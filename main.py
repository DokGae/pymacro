from __future__ import annotations

import copy
import ctypes
import html
import io
import itertools
import math
import json
import queue
import re
import sys
import threading
import time
from pathlib import Path
from typing import Any, Callable, List

from PyQt6 import QtCore, QtGui, QtWidgets

from capture import (
    CAPTURE_INTERVAL_SECONDS,
    DEFAULT_FORMAT,
    DEFAULT_JPEG_QUALITY,
    DEFAULT_PNG_COMPRESS_LEVEL,
    MAX_QUEUE_SIZE,
    MIN_INTERVAL_SECONDS,
    SCREENSHOT_DIR,
    ScreenCaptureManager,
)
from engine import (
    Action,
    Condition,
    AppTarget,
    Macro,
    MacroCondition,
    MacroEngine,
    MacroProfile,
    MacroVariables,
    Step,
    VariableResolver,
    KeyDelayConfig,
    DEFAULT_BASE_RESOLUTION,
    DEFAULT_BASE_SCALE,
)
from lib import keyboard as kbutil
from lib.interception import Interception, KeyFilter, KeyState, MapVk, MouseFilter, MouseState, map_virtual_key
from lib.keyboard import get_keystate
from lib.processes import get_foreground_process, list_processes
from lib.pixel import RGB, Region, capture_region


def _is_admin() -> bool:
    if not sys.platform.startswith("win"):
        return True
    try:
        return bool(ctypes.windll.shell32.IsUserAnAdmin())
    except Exception:
        return False


def _relaunch_as_admin():
    params = " ".join(f'"{arg}"' for arg in sys.argv)
    ctypes.windll.shell32.ShellExecuteW(None, "runas", sys.executable, params, None, 1)


def _format_dt() -> str:
    return time.strftime("%H:%M:%S")


def _rgb_to_hex(rgb) -> str | None:
    if isinstance(rgb, (list, tuple)) and len(rgb) == 3:
        try:
            return "#" + "".join(f"{int(c):02x}" for c in rgb)
        except Exception:
            return None
    return None


def _color_chip_html(hex_color: str | None, *, size: int = 12) -> str:
    if not hex_color or not isinstance(hex_color, str) or not hex_color.startswith("#"):
        return ""
    border = "#000"
    try:
        r = int(hex_color[1:3], 16)
        g = int(hex_color[3:5], 16)
        b = int(hex_color[5:7], 16)
        luminance = 0.299 * r + 0.587 * g + 0.114 * b
        border = "#000" if luminance > 186 else "#fff"
    except Exception:
        pass
    return (
        f'<span style="display:inline-block;width:{size}px;height:{size}px;'
        f'border:1px solid {border};background:{hex_color};'
        f'vertical-align:middle;margin:0 4px 0 2px;"></span>'
    )


_VID_PID_RE = re.compile(r"VID_([0-9A-F]{4}).*PID_([0-9A-F]{4})", re.IGNORECASE)


def _short_hwid(hwid: str) -> str:
    """Extract VID/PID summary from a full hardware id."""
    if not hwid:
        return ""
    match = _VID_PID_RE.search(hwid)
    if match:
        return f"VID_{match.group(1).upper()} PID_{match.group(2).upper()}"
    return hwid


def _default_macro() -> Macro:
    # z 누르고 있는 동안 r → sleep 50 → t 반복, 픽셀 맞으면 f1, 아니면 f2
    pixel_cond = Condition(type="pixel", region=(0, 0, 100, 100), color=(255, 0, 0), tolerance=10)
    actions = [
        Action(type="press", key="r"),
        Action(type="sleep", sleep_ms=50),
        Action(type="press", key="t"),
        Action(
            type="if",
            condition=pixel_cond,
            actions=[Action(type="press", key="f1")],
            else_actions=[Action(type="press", key="f2")],
        ),
    ]
    return Macro(trigger_key="z", mode="hold", suppress_trigger=True, actions=actions)


DEFAULT_PROFILE = MacroProfile(macros=[_default_macro()], pixel_region=(0, 0, 100, 100), pixel_color=(255, 0, 0), pixel_tolerance=10)

HEX_CHARS = set("0123456789abcdefABCDEF")
ACTION_TYPE_OPTIONS = [
    ("탭 (누르고 떼기)", "press"),
    ("누르기 유지 (down)", "down"),
    ("떼기 (up)", "up"),
    ("마우스 클릭", "mouse_click"),
    ("마우스 누르기 (down)", "mouse_down"),
    ("마우스 떼기 (up)", "mouse_up"),
    ("마우스 이동", "mouse_move"),
    ("대기 (sleep)", "sleep"),
    ("타이머 설정", "timer"),
]


def _parse_delay_text(text: str) -> tuple[int, bool, int, int]:
    """`40` -> (40, False, 40, 40), `40-80` -> (40, True, 40, 80)."""
    raw = str(text or "").lower().replace("ms", "")
    raw = raw.replace(" ", "")
    if not raw:
        return 0, False, 0, 0
    for sep in ("-", "~", ","):
        if sep in raw:
            parts = [p for p in raw.split(sep) if p]
            if len(parts) >= 2:
                try:
                    lo = int(parts[0])
                    hi = int(parts[1])
                except Exception:
                    break
                lo, hi = sorted((max(0, lo), max(0, hi)))
                return lo, True, lo, hi
    try:
        val = int(raw)
    except Exception:
        val = 0
    val = max(0, val)
    return val, False, val, val


def _delay_text_from_config(cfg: KeyDelayConfig, *, press: bool = True) -> str:
    """KeyDelayConfig -> human text (min-max or single)."""
    if press:
        base = int(getattr(cfg, "press_delay_ms", 0) or 0)
        rnd = bool(getattr(cfg, "press_delay_random", False))
        lo = int(getattr(cfg, "press_delay_min_ms", 0) or 0)
        hi = int(getattr(cfg, "press_delay_max_ms", 0) or 0)
    else:
        base = int(getattr(cfg, "gap_delay_ms", 0) or 0)
        rnd = bool(getattr(cfg, "gap_delay_random", False))
        lo = int(getattr(cfg, "gap_delay_min_ms", 0) or 0)
        hi = int(getattr(cfg, "gap_delay_max_ms", 0) or 0)
    if rnd or lo != hi:
        lo = lo or base
        hi = hi or base
        lo, hi = sorted((lo, hi))
        if lo == hi:
            return f"{lo}-{hi}" if rnd else str(lo)
        return f"{lo}-{hi}"
    return str(base or lo or hi or 0)


def _parse_hex_color(text: str, *, resolver=None) -> RGB:
    raw = text.strip()
    if resolver:
        raw = resolver.resolve(raw, "color")
    raw = raw.strip().lstrip("#")
    if len(raw) != 6 or any(ch not in HEX_CHARS for ch in raw):
        raise ValueError("색상은 16진수 6자리(RRGGBB)여야 합니다.")
    return tuple(int(raw[i : i + 2], 16) for i in (0, 2, 4))  # type: ignore[return-value]


def _rgb_to_hex(color: RGB | None) -> str:
    if not color:
        return ""
    r, g, b = (max(0, min(255, int(c))) for c in color)
    return f"{r:02x}{g:02x}{b:02x}"


def _setup_hex_line_edit(edit: QtWidgets.QLineEdit):
    # 변수(/name, ${name}) 입력도 허용해야 하므로 밸리데이터는 두지 않는다.
    edit.setMaxLength(64)
    edit.setPlaceholderText("RRGGBB 또는 /colorVar")


def _normalize_hex_line(text: str) -> str:
    raw = text.strip().lstrip("#")
    if len(raw) != 6 or any(ch not in HEX_CHARS for ch in raw):
        raise ValueError("HEX 색상은 RRGGBB 여야 합니다.")
    return raw.lower()


def _parse_hex_lines(text: str, *, allow_empty: bool = False) -> list[str]:
    colors: list[str] = []
    for idx, line in enumerate(text.splitlines(), 1):
        if not line.strip():
            continue
        try:
            colors.append(_normalize_hex_line(line))
        except Exception:
            raise ValueError(f"{idx}번째 줄 색상 형식이 잘못되었습니다. #RRGGBB 형태로 입력하세요.")
    if not colors and not allow_empty:
        raise ValueError("색상을 한 개 이상 입력하세요.")
    return colors


def _try_parse_hex_lines(text: str) -> tuple[list[str], str]:
    try:
        return _parse_hex_lines(text, allow_empty=True), ""
    except ValueError as exc:
        return [], str(exc)


def _hex_to_rgb_tuple(text: str) -> RGB:
    raw = _normalize_hex_line(text)
    return tuple(int(raw[i : i + 2], 16) for i in (0, 2, 4))  # type: ignore[return-value]


def _rgb_to_hex_prefixed(color: RGB | None) -> str:
    if not color:
        return ""
    r, g, b = (max(0, min(255, int(c))) for c in color)
    return f"#{r:02x}{g:02x}{b:02x}"


def _chebyshev_distance(a: RGB, b: RGB) -> int:
    return max(abs(int(x) - int(y)) for x, y in zip(a, b))


def _luminance_from_qcolor(color: QtGui.QColor) -> float:
    r, g, b = color.red(), color.green(), color.blue()
    return 0.299 * r + 0.587 * g + 0.114 * b


def _solve_color_tolerance(allowed_hex: list[str], blocked_hex: list[str]) -> dict:
    """허용/불허 색상 리스트에서 최적 tol과 색상값을 찾는다."""
    if not allowed_hex:
        raise ValueError("허용 색상을 한 개 이상 입력하세요.")
    allowed = [_hex_to_rgb_tuple(h) for h in allowed_hex]
    blocked = [_hex_to_rgb_tuple(h) for h in blocked_hex]

    min_vals = [min(c[i] for c in allowed) for i in range(3)]
    max_vals = [max(c[i] for c in allowed) for i in range(3)]
    max_range = max(max_vals[i] - min_vals[i] for i in range(3))
    min_tol = (max_range + 1) // 2

    ranges = []
    for i in range(3):
        low = max_vals[i] - min_tol
        high = min_vals[i] + min_tol
        low = max(0, int(low))
        high = min(255, int(high))
        ranges.append(range(low, high + 1))

    candidates = [tuple(vals) for vals in itertools.product(*ranges)]
    if not candidates:
        center = tuple((min_vals[i] + max_vals[i]) // 2 for i in range(3))
        candidates = [center]  # pragma: no cover - 안전망

    best_ok: dict | None = None
    best_fail: dict | None = None

    for color in candidates:
        allowed_dist = max(_chebyshev_distance(color, a) for a in allowed)
        blocked_dists = [_chebyshev_distance(color, b) for b in blocked] if blocked else []
        min_block = min(blocked_dists) if blocked_dists else 256
        conflicts = sum(1 for d in blocked_dists if d <= allowed_dist)
        margin = min_block - allowed_dist
        closest_blocked = None
        if blocked_dists:
            idx = blocked_dists.index(min_block)
            closest_blocked = blocked[idx]
        data = {
            "color": color,
            "hex": _rgb_to_hex(color),
            "tolerance": allowed_dist,
            "min_block_distance": min_block,
            "conflicts": conflicts,
            "margin": margin,
            "closest_blocked": closest_blocked,
        }
        if margin > 0:
            if (best_ok is None) or (allowed_dist < best_ok["tolerance"]) or (
                allowed_dist == best_ok["tolerance"] and margin > best_ok["margin"]
            ):
                best_ok = data
        if (best_fail is None) or (conflicts < best_fail["conflicts"]) or (
            conflicts == best_fail["conflicts"] and margin > best_fail["margin"]
        ):
            best_fail = data

    if best_ok:
        buffer_extra = max(0, min(best_ok["min_block_distance"] - 1, 255) - best_ok["tolerance"])
        best_ok.update(
            {
                "ok": True,
                "buffer_extra": buffer_extra,
                "min_required_tolerance": min_tol,
            }
        )
        return best_ok

    # 불가능 케이스
    result = best_fail or {
        "color": allowed[0],
        "hex": _rgb_to_hex(allowed[0]),
        "tolerance": min_tol,
        "min_block_distance": 0,
        "conflicts": len(blocked),
        "margin": -min_tol,
        "closest_blocked": blocked[0] if blocked else None,
    }
    result.update({"ok": False, "buffer_extra": 0, "min_required_tolerance": min_tol})
    return result


def _parse_region(text: str, *, resolver=None) -> Region:
    raw = text.strip()
    if resolver:
        raw = resolver.resolve(raw, "region")
    base_text, offset_text = _split_region_offset(raw)
    base_parts = [int(p.strip()) for p in base_text.split(",") if p.strip()]
    if len(base_parts) not in (2, 4):
        raise ValueError("Region은 x,y(,w,h) 정수여야 합니다.")
    if len(base_parts) == 2:
        base_parts.extend([1, 1])
    offset_parts = [0, 0, 0, 0]
    if offset_text:
        offset_parts = [int(p.strip()) for p in offset_text.split(",") if p.strip()]
        if len(offset_parts) != 4:
            raise ValueError("Region 덧셈은 +dx,dy,dw,dh 형식이어야 합니다.")
    merged = tuple(base_parts[i] + offset_parts[i] for i in range(4))
    return merged  # type: ignore[return-value]


def _parse_point(text: str, *, resolver=None) -> tuple[int, int]:
    raw = text.strip()
    if resolver:
        raw = resolver.resolve(raw, "var")
    parts = [p.strip() for p in raw.split(",") if p.strip()]
    if len(parts) != 2:
        raise ValueError("좌표는 x,y 형식이어야 합니다.")
    try:
        return int(parts[0]), int(parts[1])
    except Exception as exc:
        raise ValueError("좌표는 정수여야 합니다.") from exc


def _split_region_offset(raw: str) -> tuple[str, str]:
    if "+" not in raw:
        return raw.strip(), ""
    base, offset = raw.split("+", 1)
    return base.strip(), offset.strip()


def _compose_region_raw(base_text: str, offset_text: str) -> str:
    base = (base_text or "").strip()
    offset = (offset_text or "").strip()
    if not base:
        return ""
    return f"{base} + {offset}" if offset else base


def _format_resolution(res: tuple[int, int] | None) -> str:
    if not res:
        return ""
    try:
        w, h = res
        return f"{int(w)}x{int(h)}"
    except Exception:
        return ""


def _parse_resolution_text(
    text: str, *, allow_empty: bool = False, default: tuple[int, int] | None = None
) -> tuple[int, int]:
    raw = (text or "").strip()
    if not raw:
        if allow_empty and default:
            return default
        raise ValueError("해상도를 입력하세요 (예: 1920x1080).")
    cleaned = raw.lower().replace("×", "x").replace(" ", "")
    for sep in ("x", ",", "*"):
        if sep in cleaned:
            parts = [p for p in cleaned.split(sep) if p]
            if len(parts) >= 2:
                try:
                    w, h = int(parts[0]), int(parts[1])
                    if w > 0 and h > 0:
                        return (w, h)
                except Exception:
                    pass
    try:
        nums = [int(n) for n in re.findall(r"-?\d+", cleaned)]
        if len(nums) >= 2 and nums[0] > 0 and nums[1] > 0:
            return (nums[0], nums[1])
    except Exception:
        pass
    raise ValueError("해상도 형식이 잘못되었습니다. 예: 1920x1080")


def _format_scale_percent(scale: float | int | None) -> str:
    try:
        val = float(scale)
    except Exception:
        return ""
    if val <= 0:
        return ""
    if abs(val - round(val)) < 1e-6:
        return f"{int(round(val))}%"
    return f"{val:.2f}%"


def _parse_scale_text(text: str, *, allow_empty: bool = False, default: float | None = None) -> float:
    raw = (text or "").strip()
    if not raw:
        if allow_empty and default is not None:
            return float(default)
        raise ValueError("앱 배율을 입력하세요 (예: 100 또는 125).")
    cleaned = raw.lower().replace("%", "").replace("배", "").replace("x", "")
    try:
        val = float(cleaned)
    except Exception:
        raise ValueError("앱 배율은 숫자여야 합니다 (예: 100, 125, 150).")
    if val <= 0:
        raise ValueError("앱 배율은 0보다 커야 합니다.")
    return float(val)


def _affine_value(val: int | float | None, scale: float, offset: float = 0.0) -> int | None:
    if val is None:
        return None
    return int(round(float(val) * scale + float(offset)))


def _scale_value(val: int | float | None, scale: float) -> int | None:
    return _affine_value(val, scale, 0.0)


def _affine_point_tuple(
    pt: tuple[int, int] | None, scale_x: float, offset_x: float, scale_y: float, offset_y: float
) -> tuple[int, int] | None:
    if pt is None:
        return None
    try:
        return _affine_value(pt[0], scale_x, offset_x), _affine_value(pt[1], scale_y, offset_y)
    except Exception:
        return None


def _scale_point_tuple(pt: tuple[int, int] | None, scale_x: float, scale_y: float) -> tuple[int, int] | None:
    return _affine_point_tuple(pt, scale_x, 0.0, scale_y, 0.0)


def _affine_region_tuple(
    region: Region | None, scale_x: float, offset_x: float, scale_y: float, offset_y: float
) -> Region | None:
    if region is None:
        return None
    try:
        vals = tuple(region)
    except Exception:
        return None
    if len(vals) == 2:
        vals = (vals[0], vals[1], 1, 1)
    if len(vals) != 4:
        return None
    return (
        _affine_value(vals[0], scale_x, offset_x),
        _affine_value(vals[1], scale_y, offset_y),
        _affine_value(vals[2], scale_x),
        _affine_value(vals[3], scale_y),
    )  # type: ignore[return-value]


def _scale_region_tuple(region: Region | None, scale_x: float, scale_y: float) -> Region | None:
    return _affine_region_tuple(region, scale_x, 0.0, scale_y, 0.0)


def _try_parse_region_tuple(text: str | None) -> Region | None:
    if not text or not str(text).strip():
        return None
    try:
        parsed, _ = Condition._parse_region(text, None)
        return tuple(int(v) for v in parsed) if parsed else None  # type: ignore[arg-type,return-value]
    except Exception:
        return None


def _try_parse_point_tuple(text: str | None) -> tuple[int, int] | None:
    if not text or not str(text).strip():
        return None
    try:
        return _parse_point(str(text))
    except Exception:
        return None


def _scale_region_raw_text(raw: str | None, scale_x: float, scale_y: float) -> str | None:
    return _affine_region_raw_text(raw, scale_x, 0.0, scale_y, 0.0)


def _scale_point_raw_text(raw: str | None, scale_x: float, scale_y: float) -> str | None:
    return _affine_point_raw_text(raw, scale_x, 0.0, scale_y, 0.0)


def _affine_region_raw_text(raw: str | None, scale_x: float, offset_x: float, scale_y: float, offset_y: float) -> str | None:
    parsed = _try_parse_region_tuple(raw) if isinstance(raw, str) else None
    scaled = _affine_region_tuple(parsed, scale_x, offset_x, scale_y, offset_y) if parsed else None
    if not scaled:
        return None
    return ",".join(str(int(v)) for v in scaled)


def _affine_point_raw_text(raw: str | None, scale_x: float, offset_x: float, scale_y: float, offset_y: float) -> str | None:
    parsed = _try_parse_point_tuple(raw) if isinstance(raw, str) else None
    scaled = _affine_point_tuple(parsed, scale_x, offset_x, scale_y, offset_y) if parsed else None
    if not scaled:
        return None
    return ",".join(str(int(v)) for v in scaled)


def _fmt_region(reg: Region | None) -> str:
    if reg is None:
        return "-"
    try:
        vals = tuple(int(v) for v in reg)
    except Exception:
        return str(reg)
    if len(vals) == 2:
        vals = (vals[0], vals[1], 1, 1)
    vals = vals[:4]
    return ",".join(str(int(v)) for v in vals)


def _fmt_point(pt: tuple[int, int] | None) -> str:
    if pt is None:
        return "-"
    try:
        return f"{int(pt[0])},{int(pt[1])}"
    except Exception:
        return str(pt)


def _apply_affine_transform(
    profile: MacroProfile,
    record: Callable[[str, Any, Any], None],
    *,
    scale_x: float,
    scale_y: float,
    offset_x: float = 0.0,
    offset_y: float = 0.0,
):
    def transform_region(region: Region | None) -> Region | None:
        return _affine_region_tuple(region, scale_x, offset_x, scale_y, offset_y)

    def transform_point(pt: tuple[int, int] | None) -> tuple[int, int] | None:
        return _affine_point_tuple(pt, scale_x, offset_x, scale_y, offset_y)

    def transform_region_raw(raw: str | None) -> str | None:
        return _affine_region_raw_text(raw, scale_x, offset_x, scale_y, offset_y)

    def transform_point_raw(raw: str | None) -> str | None:
        return _affine_point_raw_text(raw, scale_x, offset_x, scale_y, offset_y)

    # Profile-level pixel region
    prof_region_before = getattr(profile, "pixel_region", None)
    prof_region_after = transform_region(prof_region_before)
    prof_region_raw = getattr(profile, "pixel_region_raw", None)
    scaled_prof_region_raw = transform_region_raw(prof_region_raw) if prof_region_raw else None
    if scaled_prof_region_raw is not None:
        prof_region_raw = scaled_prof_region_raw
    if prof_region_after is not None:
        record("프로필 픽셀 리전", _fmt_region(prof_region_before), _fmt_region(prof_region_after))
        profile.pixel_region = prof_region_after
        profile.pixel_region_raw = prof_region_raw

    # Variables
    if getattr(profile, "variables", None):
        region_vars = getattr(profile.variables, "region", {}) or {}
        for name, val in list(region_vars.items()):
            scaled_text = transform_region_raw(str(val))
            if scaled_text and str(val) != str(scaled_text):
                record(f"변수 Region/{name}", val, scaled_text)
                profile.variables.region[name] = scaled_text
        value_vars = getattr(profile.variables, "var", {}) or {}
        for name, val in list(value_vars.items()):
            scaled_text = transform_region_raw(str(val))
            label = f"변수 Value/{name}"
            if scaled_text and str(val) != str(scaled_text):
                record(label, val, scaled_text)
                profile.variables.var[name] = scaled_text
                continue
            scaled_point = transform_point_raw(str(val))
            if scaled_point and str(val) != str(scaled_point):
                record(label, val, scaled_point)
                profile.variables.var[name] = scaled_point

    def transform_condition(cond: Condition, ctx: str):
        if cond.region is not None or cond.region_raw:
            parsed_region = _try_parse_region_tuple(cond.region_raw) if cond.region_raw else None
            before_region = cond.region or parsed_region
            after_region = cond.region
            if cond.region is not None:
                after_region = transform_region(cond.region)
            elif parsed_region:
                after_region = transform_region(parsed_region)
            scaled_raw = transform_region_raw(cond.region_raw) if cond.region_raw else None
            if scaled_raw is not None:
                cond.region_raw = scaled_raw
                if after_region is None:
                    after_region = _try_parse_region_tuple(scaled_raw)
            if after_region is not None:
                cond.region = after_region
                record(f"{ctx} 조건 리전", _fmt_region(before_region), _fmt_region(after_region))
        for child in getattr(cond, "conditions", []) or []:
            transform_condition(child, f"{ctx} > all")
        for child in getattr(cond, "on_true", []) or []:
            transform_condition(child, f"{ctx} > true")
        for child in getattr(cond, "on_false", []) or []:
            transform_condition(child, f"{ctx} > false")

    def transform_action(act: Action, macro_ctx: str, path_parts: list[str]):
        path_label = " > ".join(path_parts + ([act.name] if act.name else [act.type]))
        if act.mouse_pos is not None or act.mouse_pos_raw:
            before_pt = act.mouse_pos or _try_parse_point_tuple(act.mouse_pos_raw)
            after_pt = act.mouse_pos
            if act.mouse_pos is not None:
                after_pt = transform_point(act.mouse_pos)
                act.mouse_pos = after_pt
            scaled_raw = transform_point_raw(act.mouse_pos_raw) if act.mouse_pos_raw else None
            if scaled_raw is not None:
                act.mouse_pos_raw = scaled_raw
                if after_pt is None:
                    after_pt = _try_parse_point_tuple(scaled_raw)
            if before_pt and after_pt and before_pt != after_pt:
                record(f"{macro_ctx} / {path_label} - 마우스 좌표", _fmt_point(before_pt), _fmt_point(after_pt))

        if act.pixel_region is not None or act.pixel_region_raw:
            parsed_region = _try_parse_region_tuple(act.pixel_region_raw) if act.pixel_region_raw else None
            before_region = act.pixel_region or parsed_region
            after_region = act.pixel_region
            if act.pixel_region is not None:
                after_region = transform_region(act.pixel_region)
            elif parsed_region:
                after_region = transform_region(parsed_region)
            scaled_raw = transform_region_raw(act.pixel_region_raw) if act.pixel_region_raw else None
            if scaled_raw is not None:
                act.pixel_region_raw = scaled_raw
            if after_region is not None and before_region != after_region:
                act.pixel_region = after_region
                record(f"{macro_ctx} / {path_label} - 리전", _fmt_region(before_region), _fmt_region(after_region))

        if act.condition:
            transform_condition(act.condition, f"{macro_ctx} / {path_label}")
        for idx, child in enumerate(getattr(act, "actions", []) or []):
            transform_action(child, macro_ctx, path_parts + [f"{act.type}[{idx + 1}]"])
        for idx, child in enumerate(getattr(act, "else_actions", []) or []):
            transform_action(child, macro_ctx, path_parts + [f"{act.type}-else[{idx + 1}]"])
        for blk_idx, blk in enumerate(getattr(act, "elif_blocks", []) or []):
            try:
                cond, acts = blk
            except Exception:
                continue
            if cond:
                transform_condition(cond, f"{macro_ctx} / {path_label} / elif#{blk_idx + 1}")
            for idx, child in enumerate(acts or []):
                transform_action(child, macro_ctx, path_parts + [f"elif#{blk_idx + 1}[{idx + 1}]"])

    for macro_idx, macro in enumerate(getattr(profile, "macros", []) or []):
        macro_ctx = f"매크로#{macro_idx + 1}({macro.name or macro.trigger_key})"
        for idx, act in enumerate(getattr(macro, "actions", []) or []):
            transform_action(act, macro_ctx, [f"action#{idx + 1}"])


def _scale_profile(
    profile: MacroProfile,
    base_res: tuple[int, int],
    target_res: tuple[int, int],
    base_scale_percent: float | int = DEFAULT_BASE_SCALE,
    target_scale_percent: float | int | None = None,
) -> tuple[MacroProfile, list[tuple[str, str, str]], float, float]:
    if not base_res or not target_res:
        raise ValueError("해상도 정보를 확인할 수 없습니다.")
    try:
        bw, bh = int(base_res[0]), int(base_res[1])
        tw, th = int(target_res[0]), int(target_res[1])
    except Exception as exc:
        raise ValueError("해상도 값이 잘못되었습니다.") from exc
    if bw <= 0 or bh <= 0 or tw <= 0 or th <= 0:
        raise ValueError("해상도는 0보다 커야 합니다.")
    try:
        base_scale_pct = float(base_scale_percent)
    except Exception:
        base_scale_pct = DEFAULT_BASE_SCALE
    try:
        target_scale_pct = float(target_scale_percent if target_scale_percent is not None else base_scale_pct)
    except Exception:
        target_scale_pct = base_scale_pct
    base_scale_factor = max(0.01, base_scale_pct) / 100.0
    target_scale_factor = max(0.01, target_scale_pct) / 100.0
    scale_x = (tw / bw) * (target_scale_factor / base_scale_factor)
    scale_y = (th / bh) * (target_scale_factor / base_scale_factor)

    changes: list[tuple[str, str, str]] = []

    def record(label: str, before, after):
        if before == after:
            return
        changes.append((label, str(before), str(after)))

    scaled = copy.deepcopy(profile)
    record("기준 해상도", _format_resolution(base_res), _format_resolution(target_res))
    record("앱 배율", _format_scale_percent(base_scale_pct), _format_scale_percent(target_scale_pct))
    scaled.base_resolution = (tw, th)
    try:
        scaled.base_scale_percent = float(target_scale_pct)
    except Exception:
        scaled.base_scale_percent = float(base_scale_pct)
    # 좌표/리전 변환
    _apply_affine_transform(
        scaled,
        record,
        scale_x=scale_x,
        scale_y=scale_y,
        offset_x=0.0,
        offset_y=0.0,
    )
    scaled.transform_matrix = None

    return scaled, changes, scale_x, scale_y


def _transform_profile_affine(
    profile: MacroProfile, ax: float, bx: float, cy: float, dy: float
) -> tuple[MacroProfile, list[tuple[str, str, str]]]:
    changes: list[tuple[str, str, str]] = []

    def record(label: str, before, after):
        if before == after:
            return
        changes.append((label, str(before), str(after)))

    transformed = copy.deepcopy(profile)
    _apply_affine_transform(
        transformed,
        record,
        scale_x=ax,
        scale_y=cy,
        offset_x=bx,
        offset_y=dy,
    )
    try:
        transformed.transform_matrix = {"ax": float(ax), "bx": float(bx), "cy": float(cy), "dy": float(dy)}
    except Exception:
        transformed.transform_matrix = {"ax": ax, "bx": bx, "cy": cy, "dy": dy}
    return transformed, changes


def _run_dialog_non_modal(dlg: QtWidgets.QDialog) -> int:
    """Show a dialog without blocking other windows but still wait for the result."""
    dlg.setModal(False)
    dlg.setWindowModality(QtCore.Qt.WindowModality.NonModal)
    try:
        dlg.setWindowFlags(
            QtCore.Qt.WindowType.Window
            | QtCore.Qt.WindowType.WindowMinimizeButtonHint
            | QtCore.Qt.WindowType.WindowMaximizeButtonHint
            | QtCore.Qt.WindowType.WindowCloseButtonHint
        )
    except Exception:
        pass

    result: dict[str, int] = {"code": int(QtWidgets.QDialog.DialogCode.Rejected)}
    loop = QtCore.QEventLoop()

    def _on_finished(code: int):
        result["code"] = int(code)
        loop.quit()

    dlg.finished.connect(_on_finished)
    dlg.show()
    try:
        dlg.raise_()
        dlg.activateWindow()
    except Exception:
        pass
    loop.exec()
    try:
        dlg.finished.disconnect(_on_finished)
    except Exception:
        pass
    return result["code"]


class ActionTableWidget(QtWidgets.QTableWidget):
    def __init__(self, parent=None):
        super().__init__(0, 2, parent)
        self.setHorizontalHeaderLabels(["액션", "키 / Sleep(ms)"])
        self.horizontalHeader().setStretchLastSection(True)
        self.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectionBehavior.SelectRows)
        self.setSelectionMode(QtWidgets.QAbstractItemView.SelectionMode.ExtendedSelection)
        self.setDragEnabled(True)
        self.setAcceptDrops(True)
        self.setDropIndicatorShown(True)
        self.setDragDropMode(QtWidgets.QAbstractItemView.DragDropMode.InternalMove)

    def _type_combo(self, default_type: str = "press") -> QtWidgets.QComboBox:
        combo = QtWidgets.QComboBox()
        for label, value in ACTION_TYPE_OPTIONS:
            combo.addItem(label, value)
        idx = combo.findData(default_type)
        if idx >= 0:
            combo.setCurrentIndex(idx)
        return combo

    def add_action_row(self, typ: str = "press", value: str = "") -> int:
        row = self.rowCount()
        self.insertRow(row)
        self.set_action_row(row, typ, value)
        return row

    def set_action_row(self, row: int, typ: str, value: str):
        combo = self._type_combo(typ)
        self.setCellWidget(row, 0, combo)
        self.setItem(row, 1, QtWidgets.QTableWidgetItem(str(value)))

    def row_data(self, row: int) -> tuple[str, str]:
        typ = ""
        type_widget = self.cellWidget(row, 0)
        if isinstance(type_widget, QtWidgets.QComboBox):
            typ = str(type_widget.currentData() or "").strip().lower()
        else:
            item = self.item(row, 0)
            typ = item.text().strip().lower() if item else ""
        val_item = self.item(row, 1)
        val = val_item.text().strip() if val_item else ""
        return typ, val

    def dropEvent(self, event: QtGui.QDropEvent):
        # Treat drops from this table (or its viewport) as a reordering operation
        if event.source() not in (self, self.viewport()):
            return super().dropEvent(event)

        selected_rows = sorted({idx.row() for idx in self.selectionModel().selectedRows()})
        if not selected_rows:
            return

        drop_row = self.indexAt(event.position().toPoint()).row()
        indicator = self.dropIndicatorPosition()
        if indicator == QtWidgets.QAbstractItemView.DropIndicatorPosition.BelowItem:
            drop_row += 1
        elif indicator == QtWidgets.QAbstractItemView.DropIndicatorPosition.OnViewport:
            drop_row = self.rowCount()
        if drop_row < 0:
            drop_row = self.rowCount()

        # Snapshot all rows, remove the moved block, then re-insert to avoid losing cell data
        rows = [self.row_data(r) for r in range(self.rowCount())]
        moving = [rows[r] for r in selected_rows]
        for r in reversed(selected_rows):
            del rows[r]
            if r < drop_row:
                drop_row -= 1
        for offset, data in enumerate(moving):
            rows.insert(drop_row + offset, data)

        self.setRowCount(0)
        for typ, val in rows:
            self.add_action_row(typ, val)

        self.clearSelection()
        for i in range(len(moving)):
            self.selectRow(drop_row + i)
        event.acceptProposedAction()


def _create_action_table(default_rows=None):
    table = ActionTableWidget()
    add_btn = QtWidgets.QPushButton("추가")
    del_btn = QtWidgets.QPushButton("삭제")

    def add_row(default_type="press", default_val=""):
        table.add_action_row(default_type, default_val)

    def del_rows():
        rows = sorted({idx.row() for idx in table.selectionModel().selectedRows()}, reverse=True)
        if not rows and table.rowCount() > 0:
            rows = [table.rowCount() - 1]
        for r in rows:
            table.removeRow(r)

    add_btn.clicked.connect(lambda: add_row())
    del_btn.clicked.connect(del_rows)

    if default_rows:
        for t, v in default_rows:
            add_row(t, v)

    layout = QtWidgets.QVBoxLayout()
    layout.addWidget(table)
    btns = QtWidgets.QHBoxLayout()
    btns.addWidget(add_btn)
    btns.addWidget(del_btn)
    btns.addStretch()
    layout.addLayout(btns)

    return {"table": table, "add": add_row, "del": del_rows, "layout": layout}


def _read_action_row(table: QtWidgets.QTableWidget, row: int) -> tuple[str, str]:
    if isinstance(table, ActionTableWidget):
        return table.row_data(row)
    typ = table.item(row, 0).text().strip().lower() if table.item(row, 0) else ""
    val = table.item(row, 1).text().strip() if table.item(row, 1) else ""
    return typ, val


class VariableCompleterDelegate(QtWidgets.QStyledItemDelegate):
    def __init__(self, category_provider, variable_provider, parent=None):
        super().__init__(parent)
        self._category_provider = category_provider
        self._variable_provider = variable_provider

    def createEditor(self, parent, option, index):
        editor = super().createEditor(parent, option, index)
        if index.column() != 1:
            return editor
        if isinstance(editor, QtWidgets.QLineEdit):
            cat = self._category_provider(index) if self._category_provider else None
            if cat:
                names = self._variable_provider(cat) if self._variable_provider else []
                _attach_variable_completer(editor, names)
        return editor


def _attach_variable_completer(edit: QtWidgets.QLineEdit, names: List[str]):
    if not isinstance(edit, QtWidgets.QLineEdit):
        return
    entries = [f"/{n}" for n in names]
    comp = QtWidgets.QCompleter(entries or ["/"], edit)
    comp.setCaseSensitivity(QtCore.Qt.CaseSensitivity.CaseInsensitive)
    comp.setFilterMode(QtCore.Qt.MatchFlag.MatchContains)
    comp.setCompletionMode(QtWidgets.QCompleter.CompletionMode.PopupCompletion)
    comp.setModelSorting(QtWidgets.QCompleter.ModelSorting.CaseInsensitivelySortedModel)

    def _current_prefix(text: str) -> tuple[str, int]:
        pos = text.rfind("/")
        if pos < 0:
            return "", -1
        return text[pos + 1 :], pos

    def _show_popup(text: str):
        prefix, start = _current_prefix(text)
        if start < 0:
            return
        comp.setCompletionPrefix(prefix)
        comp.complete()

    def _insert_choice(val: str):
        text = edit.text()
        prefix, start = _current_prefix(text)
        insert = f"@{val}"
        if start >= 0 and text[start:].startswith("${"):
            insert = f"${{{val}}}"
        new_text = text[: start if start >= 0 else len(text)]
        new_text += insert
        edit.setText(new_text)
        edit.setCursorPosition(len(new_text))

    comp.activated[str].connect(_insert_choice)
    edit.textEdited.connect(_show_popup)
    # 첫 입력 시 바로 /를 치면 팝업이 뜸
    edit.setCompleter(comp)


def _actions_from_table(table: QtWidgets.QTableWidget, resolver=None) -> List[Step]:
    steps: List[Step] = []
    for row in range(table.rowCount()):
        typ, val = _read_action_row(table, row)
        if not typ:
            continue
        if typ == "sleep":
            try:
                resolved = resolver.resolve(val, "sleep") if resolver else val
                sleep_ms, sleep_range = Step.parse_sleep(resolved)
            except ValueError as exc:
                raise ValueError(f"sleep 값이 잘못되었습니다 (행 {row + 1}): {exc}")
            steps.append(Step(type="sleep", sleep_ms=sleep_ms, sleep_range=sleep_range, sleep_raw=val))
        else:
            if not val:
                continue
            steps.append(Step(type=typ, key=val))
    return steps


def _fill_action_table(table: QtWidgets.QTableWidget, steps: List[Step]):
    table.setRowCount(0)
    for step in steps:
        if isinstance(table, ActionTableWidget):
            value = step.sleep_value_text() if step.type == "sleep" else (step.key or "")
            table.add_action_row(step.type, value)
            continue
        row = table.rowCount()
        table.insertRow(row)
        table.setItem(row, 0, QtWidgets.QTableWidgetItem(step.type))
        if step.type == "sleep":
            table.setItem(row, 1, QtWidgets.QTableWidgetItem(step.sleep_value_text()))
        else:
            table.setItem(row, 1, QtWidgets.QTableWidgetItem(step.key or ""))


def _condition_type_label(typ: str) -> str:
    return {"all": "AND", "any": "OR", "pixel": "픽셀", "key": "키", "var": "변수", "timer": "타이머"}.get(typ, typ)


def _group_child_count(cond: Condition) -> int:
    if not isinstance(cond, Condition):
        return 0
    if cond.type not in ("all", "any"):
        return 0
    # 중첩 동일 타입 단일 래퍼는 풀어서 카운트(조건 편집 트리와 일치시키기 위함)
    current = cond
    while (
        isinstance(current, Condition)
        and current.type in ("all", "any")
        and len(getattr(current, "conditions", []) or []) == 1
        and isinstance((getattr(current, "conditions", [None])[0]), Condition)
        and getattr(current, "conditions", [None])[0].type == current.type
        and not current.on_true
        and not current.on_false
    ):
        current = getattr(current, "conditions", [current])[0]
    direct_list = getattr(current, "conditions", []) or []
    return len(direct_list) + len(getattr(current, "on_true", []) or []) + len(getattr(current, "on_false", []) or [])


def _key_bundle_info(cond: Condition) -> tuple[bool, list[str], str | None]:
    """Detect a pure key bundle group and return (is_bundle, keys, key_mode)."""
    if not isinstance(cond, Condition):
        return False, [], None
    if cond.type not in ("all", "any"):
        return False, [], None
    if getattr(cond, "on_true", []) or getattr(cond, "on_false", []):
        return False, [], None
    children = getattr(cond, "conditions", []) or []
    if not children:
        return False, [], None
    if not all(isinstance(c, Condition) and c.type == "key" for c in children):
        return False, [], None
    modes = {getattr(c, "key_mode", None) for c in children}
    mode = modes.pop() if len(modes) == 1 else None
    keys = [getattr(c, "key", "") for c in children if getattr(c, "key", "")]
    if not keys:
        return False, [], mode
    return True, keys, mode


def _condition_brief(cond: Condition) -> str:
    if not isinstance(cond, Condition):
        return "(조건 없음)"
    suffix_parts = []
    if getattr(cond, "on_true", []):
        suffix_parts.append(f"참 {len(cond.on_true)}")
    if getattr(cond, "on_false", []):
        suffix_parts.append(f"거짓 {len(cond.on_false)}")
    suffix = f" | {' / '.join(suffix_parts)}" if suffix_parts else ""
    if cond.type == "key":
        mode = cond.key_mode or "hold"
        return f"키/마우스 {cond.key} ({mode}){suffix}"
    if cond.type == "pixel":
        region = cond.region_raw or ",".join(str(v) for v in cond.region or [])
        color_hex = cond.color_raw or (_rgb_to_hex(cond.color) or "------")
        state = "있음" if getattr(cond, "pixel_exists", True) else "없음"
        return f"픽셀 {region} #{color_hex} tol={cond.tolerance} ({state}일 때 참){suffix}"
    if cond.type == "var":
        op_text = "!=" if getattr(cond, "var_operator", "eq") == "ne" else "=="
        return f"변수 {cond.var_name} {op_text} {cond.var_value_raw or cond.var_value or ''}{suffix}"
    if cond.type == "timer":
        op_map = {"ge": ">=", "gt": ">", "le": "<=", "lt": "<", "eq": "==", "ne": "!="}
        op = op_map.get(getattr(cond, "timer_operator", "ge"), ">=")
        slot = getattr(cond, "timer_index", None)
        target_val = getattr(cond, "timer_value", None)
        if isinstance(target_val, (int, float)):
            target = f"{float(target_val):.3f}".rstrip("0").rstrip(".")
        else:
            target = target_val
        slot_text = f"타이머{slot}" if slot else "타이머"
        target_text = target if target is not None else "?"
        return f"{slot_text} {op} {target_text}{suffix}"
    is_bundle, keys, mode = _key_bundle_info(cond)
    if is_bundle:
        mode_text = mode or ""
        key_list = ",".join(keys)
        return f"키 {key_list} ({mode_text}){suffix}"
    if cond.type == "all":
        if cond.name:
            return f"{cond.name}{suffix}"
        return f"AND 그룹 (하위 {_group_child_count(cond)}개){suffix}"
    if cond.type == "any":
        if cond.name:
            return f"{cond.name}{suffix}"
        return f"OR 그룹 (하위 {_group_child_count(cond)}개){suffix}"
    return f"{cond.type}{suffix}"


class ConditionNodeDialog(QtWidgets.QDialog):
    def __init__(
        self,
        parent=None,
        cond: Condition | None = None,
        *,
        allow_group: bool = True,
        variable_provider=None,
        resolver: VariableResolver | None = None,
        open_debugger=None,
    ):
        super().__init__(parent)
        self.setWindowTitle("조건 설정")
        self.setModal(False)
        self.setWindowModality(QtCore.Qt.WindowModality.NonModal)
        self.setWindowFlags(
            QtCore.Qt.WindowType.Window
            | QtCore.Qt.WindowType.WindowMinimizeButtonHint
            | QtCore.Qt.WindowType.WindowMaximizeButtonHint
            | QtCore.Qt.WindowType.WindowCloseButtonHint
        )
        self.resize(520, 360)
        self._variable_provider = variable_provider
        self._resolver = resolver
        self._open_debugger_fn = open_debugger

        self._child_conditions: List[Condition] = []

        layout = QtWidgets.QVBoxLayout(self)

        self.form = QtWidgets.QFormLayout()
        self.type_combo = QtWidgets.QComboBox()
        if allow_group:
            self.type_combo.addItem("AND 그룹 (모두 참)", "all")
            self.type_combo.addItem("OR 그룹 (하나라도 참)", "any")
        self.type_combo.addItem("픽셀", "pixel")
        self.type_combo.addItem("키/마우스", "key")
        self.type_combo.addItem("변수 값 비교", "var")
        self.type_combo.addItem("타이머", "timer")
        self.name_edit = QtWidgets.QLineEdit()
        self.key_edit = QtWidgets.QLineEdit()
        self.key_edit.setPlaceholderText("예: a, ctrl, mouse1")
        self.key_mode_combo = QtWidgets.QComboBox()
        self.key_mode_combo.addItem("press (눌리는 순간 한 번, down과 동일)", "press")
        self.key_mode_combo.addItem("down (눌리는 순간 한 번)", "down")
        self.key_mode_combo.addItem("up (뗄 때 한 번)", "up")
        self.key_mode_combo.addItem("hold (누르는 동안 계속 참)", "hold")
        self.key_mode_combo.addItem("released (안 눌릴 때 참)", "released")
        self.key_mode_combo.setToolTip("press/down=방금 눌림, up=뗄 때, hold=누르는 동안, released=안 눌릴 때")
        self.key_group_mode_combo = QtWidgets.QComboBox()
        self.key_group_mode_combo.addItem("모두 만족 (AND)", "all")
        self.key_group_mode_combo.addItem("하나라도 (OR)", "any")
        self.key_group_mode_combo.setToolTip("쉼표로 여러 키를 입력하면 이 모드로 묶어서 추가합니다.")
        self.region_edit = QtWidgets.QLineEdit("0,0,1,1")
        self.region_offset_edit = QtWidgets.QLineEdit("")
        self.region_edit.setPlaceholderText("기본 영역: x,y(,w,h) 또는 /변수")
        self.region_offset_edit.setPlaceholderText("+dx,dy,dw,dh (선택)")
        self.color_edit = QtWidgets.QLineEdit("ff0000")
        _setup_hex_line_edit(self.color_edit)
        self._install_var_completer(self.region_edit, "region")
        self._install_var_completer(self.color_edit, "color")
        self.var_name_edit = QtWidgets.QLineEdit()
        self.var_value_edit = QtWidgets.QLineEdit()
        self._install_var_completer(self.var_value_edit, "var")
        if callable(self._variable_provider):
            names = self._variable_provider("var")
            comp = QtWidgets.QCompleter(names, self.var_name_edit)
            comp.setCaseSensitivity(QtCore.Qt.CaseSensitivity.CaseInsensitive)
            comp.setFilterMode(QtCore.Qt.MatchFlag.MatchContains)
            self.var_name_edit.setCompleter(comp)
        self.var_op_combo = QtWidgets.QComboBox()
        self.var_op_combo.addItem("같을 때 참 (==)", "eq")
        self.var_op_combo.addItem("다를 때 참 (!=)", "ne")
        self.timer_slot_combo = QtWidgets.QComboBox()
        for i in range(1, 21):
            self.timer_slot_combo.addItem(f"타이머{i}", i)
        self.timer_value_spin = QtWidgets.QDoubleSpinBox()
        self.timer_value_spin.setRange(0.0, 999999.0)
        self.timer_value_spin.setDecimals(3)
        self.timer_value_spin.setSingleStep(0.1)
        self.timer_value_spin.setSuffix(" 초")
        self.timer_op_combo = QtWidgets.QComboBox()
        self.timer_op_combo.addItem("이상이면 참 (>=)", "ge")
        self.timer_op_combo.addItem("초과일 때 참 (>)", "gt")
        self.timer_op_combo.addItem("같을 때 참 (==)", "eq")
        self.timer_op_combo.addItem("이하일 때 참 (<=)", "le")
        self.timer_op_combo.addItem("미만일 때 참 (<)", "lt")
        self.timer_op_combo.addItem("다를 때 참 (!=)", "ne")
        self.tol_spin = QtWidgets.QSpinBox()
        self.tol_spin.setRange(0, 255)
        self.tol_spin.setValue(10)
        self.pixel_expect_combo = QtWidgets.QComboBox()
        self.pixel_expect_combo.addItem("색상이 있을 때 참", True)
        self.pixel_expect_combo.addItem("색상이 없을 때 참", False)
        self.group_hint = QtWidgets.QLabel("하위 조건은 트리에서 추가/삭제하세요.")
        self.group_hint.setStyleSheet("color: gray;")

        self.form.addRow("조건 타입", self.type_combo)
        self.form.addRow("이름(선택)", self.name_edit)
        self.form.addRow("키/마우스", self.key_edit)
        self.form.addRow("키 모드", self.key_mode_combo)
        self.form.addRow("여러 키 묶기", self.key_group_mode_combo)
        self.form.addRow("Region x,y,w,h", self.region_edit)
        self.form.addRow("+dx,dy,dw,dh (선택)", self.region_offset_edit)
        self.form.addRow("색상 (HEX RRGGBB)", self.color_edit)
        self.form.addRow("Tolerance", self.tol_spin)
        self.form.addRow("픽셀 상태", self.pixel_expect_combo)
        self.form.addRow("변수 이름", self.var_name_edit)
        self.form.addRow("변수 값", self.var_value_edit)
        self.form.addRow("비교 방식", self.var_op_combo)
        self.form.addRow("타이머 슬롯(1~20)", self.timer_slot_combo)
        self.form.addRow("타이머 값(초)", self.timer_value_spin)
        self.form.addRow("타이머 비교", self.timer_op_combo)
        self.form.addRow(self.group_hint)
        layout.addLayout(self.form)

        btn_row = QtWidgets.QHBoxLayout()
        btn_row.addStretch()
        self.test_btn = QtWidgets.QPushButton("테스트")
        self.ok_btn = QtWidgets.QPushButton("확인")
        self.cancel_btn = QtWidgets.QPushButton("취소")
        btn_row.addWidget(self.test_btn)
        btn_row.addWidget(self.ok_btn)
        btn_row.addWidget(self.cancel_btn)
        layout.addLayout(btn_row)

        self.test_btn.clicked.connect(self._toggle_pixel_test)
        self.ok_btn.clicked.connect(self.accept)
        self.cancel_btn.clicked.connect(self.reject)
        self.type_combo.currentIndexChanged.connect(self._sync_type_visibility)

        if cond:
            self._load(cond)
        else:
            if allow_group:
                self.type_combo.setCurrentIndex(self.type_combo.findData("all") if self.type_combo.findData("all") >= 0 else 0)
            else:
                self.type_combo.setCurrentIndex(self.type_combo.findData("pixel"))
            self.key_mode_combo.setCurrentIndex(max(0, self.key_mode_combo.findData("hold")))
            self._sync_type_visibility()

    def _current_type(self) -> str:
        return self.type_combo.currentData()

    def _sync_type_visibility(self):
        typ = self._current_type()
        is_key = typ == "key"
        is_pixel = typ == "pixel"
        is_group = typ in ("all", "any")
        is_var = typ == "var"
        is_timer = typ == "timer"
        def _toggle(widgets, *, visible: bool, enabled: bool):
            for w in widgets:
                w.setEnabled(enabled)
                w.setVisible(visible)
                label = self.form.labelForField(w)
                if label is not None:
                    label.setVisible(visible)

        _toggle((self.key_edit, self.key_mode_combo, self.key_group_mode_combo), visible=is_key, enabled=is_key)
        _toggle(
            (self.region_edit, self.region_offset_edit, self.color_edit, self.tol_spin, self.pixel_expect_combo, self.test_btn),
            visible=is_pixel,
            enabled=is_pixel,
        )
        _toggle((self.var_name_edit, self.var_value_edit, self.var_op_combo), visible=is_var, enabled=is_var)
        _toggle((self.timer_slot_combo, self.timer_value_spin, self.timer_op_combo), visible=is_timer, enabled=is_timer)
        self.group_hint.setVisible(is_group)

    def _load(self, cond: Condition):
        self.type_combo.setCurrentIndex(max(0, self.type_combo.findData(cond.type)))
        if cond.type == "key":
            self.key_edit.setText(cond.key or "")
            idx = self.key_mode_combo.findData(cond.key_mode or "hold")
            if idx >= 0:
                self.key_mode_combo.setCurrentIndex(idx)
        elif cond.type == "pixel":
            raw_region = cond.region_raw or ",".join(str(v) for v in cond.region or [])
            base_txt, offset_txt = _split_region_offset(raw_region) if raw_region else ("", "")
            self.region_edit.setText(base_txt)
            self.region_offset_edit.setText(offset_txt)
            if cond.color_raw is not None:
                self.color_edit.setText(cond.color_raw)
            else:
                self.color_edit.setText(_rgb_to_hex(cond.color))
            self.tol_spin.setValue(cond.tolerance)
            idx = self.pixel_expect_combo.findData(getattr(cond, "pixel_exists", True))
            if idx >= 0:
                self.pixel_expect_combo.setCurrentIndex(idx)
        elif cond.type in ("all", "any"):
            self._child_conditions = copy.deepcopy(cond.conditions)
        elif cond.type == "var":
            self.var_name_edit.setText(cond.var_name or "")
            self.var_value_edit.setText(cond.var_value_raw or cond.var_value or "")
            idx = self.var_op_combo.findData(getattr(cond, "var_operator", "eq"))
            if idx >= 0:
                self.var_op_combo.setCurrentIndex(idx)
        elif cond.type == "timer":
            idx = self.timer_slot_combo.findData(getattr(cond, "timer_index", 1))
            if idx >= 0:
                self.timer_slot_combo.setCurrentIndex(idx)
            self.timer_value_spin.setValue(max(0.0, float(getattr(cond, "timer_value", 0) or 0)))
            op_idx = self.timer_op_combo.findData(getattr(cond, "timer_operator", "ge"))
            if op_idx >= 0:
                self.timer_op_combo.setCurrentIndex(op_idx)
        self.name_edit.setText(cond.name or "")
        self._sync_type_visibility()

    def get_condition(self) -> Condition:
        typ = self._current_type()
        name = self.name_edit.text().strip() or None
        if typ == "key":
            raw_keys = self.key_edit.text().strip()
            keys = [k.strip() for k in raw_keys.replace(",", " ").split() if k.strip()]
            if not keys:
                raise ValueError("키를 입력하세요.")
            mode = self.key_mode_combo.currentData() or "hold"
            if len(keys) == 1:
                return Condition(type="key", name=name, key=keys[0], key_mode=mode)
            group_type = self.key_group_mode_combo.currentData() or "all"
            children = [Condition(type="key", key=k, key_mode=mode) for k in keys]
            summary = name or f"키 {','.join(keys)} ({mode})"
            return Condition(type=group_type, name=summary, conditions=children)
        if typ == "pixel":
            region_text = _compose_region_raw(self.region_edit.text(), self.region_offset_edit.text())
            color_text = self.color_edit.text()
            region = _parse_region(region_text, resolver=self._resolver)
            # 변수 참조(/, ${}, @)는 값 검증 없이 raw로 저장하고 런타임에 resolver로 해석하도록 한다.
            if any(color_text.strip().startswith(prefix) for prefix in ("/", "$", "@")):
                color = None
            else:
                color = _parse_hex_color(color_text, resolver=self._resolver)
            pixel_exists = bool(self.pixel_expect_combo.currentData()) if self.pixel_expect_combo.currentIndex() >= 0 else True
            return Condition(
                type="pixel",
                name=name,
                region=region,
                region_raw=region_text,
                color=color,
                color_raw=color_text,
                tolerance=int(self.tol_spin.value()),
                pixel_exists=pixel_exists,
            )
        if typ == "var":
            var_name = self.var_name_edit.text().strip()
            if not var_name:
                raise ValueError("변수 이름을 입력하세요.")
            value_raw = self.var_value_edit.text().strip()
            op = self.var_op_combo.currentData() or "eq"
            return Condition(type="var", name=name, var_name=var_name, var_value_raw=value_raw or None, var_operator=op)
        if typ == "timer":
            slot = int(self.timer_slot_combo.currentData() or 0)
            value = float(self.timer_value_spin.value())
            op = self.timer_op_combo.currentData() or "ge"
            if slot < 1 or slot > 20:
                raise ValueError("타이머 슬롯은 1~20 사이여야 합니다.")
            return Condition(type="timer", name=name, timer_index=slot, timer_value=value, timer_operator=op)
        group = Condition(type=typ, name=name, conditions=copy.deepcopy(self._child_conditions))
        return group

    def _toggle_pixel_test(self):
        try:
            region = _parse_region(_compose_region_raw(self.region_edit.text(), self.region_offset_edit.text()), resolver=self._resolver)
            color = _parse_hex_color(self.color_edit.text(), resolver=self._resolver)
            tolerance = int(self.tol_spin.value())
        except ValueError as exc:
            QtWidgets.QMessageBox.warning(self, "입력 오류", str(exc))
            return
        expect_exists = bool(self.pixel_expect_combo.currentData()) if self.pixel_expect_combo.currentIndex() >= 0 else True
        if not callable(self._open_debugger_fn):
            QtWidgets.QMessageBox.information(self, "지원 안 함", "픽셀 테스트를 사용할 수 없습니다.")
            return
        config = {
            "region": region,
            "region_raw": self.region_edit.text().strip(),
            "color": color,
            "color_raw": self.color_edit.text().strip(),
            "tolerance": tolerance,
            "expect_exists": expect_exists,
            "label": self.name_edit.text().strip() or "조건 테스트",
        }
        self._open_debugger_fn(config)

    def closeEvent(self, event: QtGui.QCloseEvent):
        return super().closeEvent(event)

    def _install_var_completer(self, edit: QtWidgets.QLineEdit, category: str):
        if not self._variable_provider:
            return
        names = self._variable_provider(category)
        _attach_variable_completer(edit, names)


class ConditionTreeWidget(QtWidgets.QTreeWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self._drop_callback: Callable[[], None] | None = None
        self.setDragEnabled(True)
        self.setAcceptDrops(True)
        self.setDropIndicatorShown(True)
        self.setDragDropMode(QtWidgets.QAbstractItemView.DragDropMode.InternalMove)

    def set_drop_callback(self, callback: Callable[[], None]):
        self._drop_callback = callback

    def dropEvent(self, event: QtGui.QDropEvent):
        # OnItem 드롭을 모든 조건/브랜치에 허용해 하위로 넣을 수 있게 한다.
        super().dropEvent(event)
        if self._drop_callback:
            self._drop_callback()


class ConditionDialog(QtWidgets.QDialog):
    def __init__(
        self,
        parent=None,
        cond: MacroCondition | None = None,
        *,
        variable_provider=None,
        resolver: VariableResolver | None = None,
        open_debugger=None,
        start_condition_debug=None,
        image_viewer_state: dict | None = None,
        save_image_viewer_state=None,
        open_screenshot_dialog=None,
        screenshot_hotkeys_provider=None,
        screenshot_manager=None,
    ):
        super().__init__(parent)
        self.setWindowTitle("조건 편집")
        self.setModal(False)
        self.setWindowModality(QtCore.Qt.WindowModality.NonModal)
        self.setWindowFlags(
            QtCore.Qt.WindowType.Window
            | QtCore.Qt.WindowType.WindowMinimizeButtonHint
            | QtCore.Qt.WindowType.WindowMaximizeButtonHint
            | QtCore.Qt.WindowType.WindowCloseButtonHint
        )
        self.resize(640, 520)
        self._variable_provider = variable_provider
        self._resolver = resolver
        self._open_debugger_fn = open_debugger
        self._start_condition_debug_fn = start_condition_debug
        self._image_viewer_state = image_viewer_state or {}
        self._save_image_viewer_state = save_image_viewer_state
        self._image_viewer: ImageViewerDialog | None = None
        self._open_screenshot_dialog_fn = open_screenshot_dialog
        self._screenshot_hotkeys_provider = screenshot_hotkeys_provider
        self._screenshot_manager = screenshot_manager
        self._debug_stop_cb = None

        self.root_condition: Condition | None = None

        layout = QtWidgets.QVBoxLayout(self)

        name_form = QtWidgets.QFormLayout()
        self.cond_name_edit = QtWidgets.QLineEdit()
        self.cond_name_edit.setPlaceholderText("조건 블록 이름(선택)")
        name_form.addRow("조건 이름", self.cond_name_edit)
        layout.addLayout(name_form)

        viewer_row = QtWidgets.QHBoxLayout()
        self.viewer_btn = QtWidgets.QPushButton("이미지 뷰어/피커")
        self.debug_test_btn = QtWidgets.QPushButton("디버그 테스트")
        self.viewer_status = QtWidgets.QLabel("F1=좌표, F2=색상, F5=새로고침, Delete=삭제")
        self.viewer_status.setStyleSheet("color: gray;")
        last_dir = self._image_viewer_state.get("last_dir") if isinstance(self._image_viewer_state, dict) else None
        if last_dir:
            self.viewer_status.setText(f"최근 폴더: {last_dir} | F1=좌표, F2=색상, F5=새로고침")
        viewer_row.addWidget(self.viewer_btn)
        viewer_row.addWidget(self.debug_test_btn)
        viewer_row.addWidget(self.viewer_status, 1)
        layout.addLayout(viewer_row)

        cond_group = QtWidgets.QGroupBox("조건 트리 (최상위 OR, AND로 묶기)")
        cond_group_layout = QtWidgets.QVBoxLayout(cond_group)
        self.condition_tree = ConditionTreeWidget()
        self.condition_tree.setHeaderLabels(["타입", "요약"])
        self.condition_tree.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectionBehavior.SelectRows)
        self.condition_tree.set_drop_callback(self._sync_condition_from_tree)
        cond_group_layout.addWidget(self.condition_tree)

        tree_btn_row = QtWidgets.QHBoxLayout()
        self.add_node_btn = QtWidgets.QPushButton("조건 추가")
        self.add_group_btn = QtWidgets.QPushButton("그룹 추가 (AND/OR)")
        self.add_true_child_btn = QtWidgets.QPushButton("참일 때 하위")
        self.add_false_child_btn = QtWidgets.QPushButton("거짓일 때 하위")
        self.edit_node_btn = QtWidgets.QPushButton("선택 편집")
        self.clone_node_btn = QtWidgets.QPushButton("복제")
        self.delete_node_btn = QtWidgets.QPushButton("선택 삭제")
        tree_btn_row.addWidget(self.add_node_btn)
        tree_btn_row.addWidget(self.add_group_btn)
        tree_btn_row.addWidget(self.add_true_child_btn)
        tree_btn_row.addWidget(self.add_false_child_btn)
        tree_btn_row.addWidget(self.edit_node_btn)
        tree_btn_row.addWidget(self.clone_node_btn)
        tree_btn_row.addWidget(self.delete_node_btn)
        tree_btn_row.addStretch()
        cond_group_layout.addLayout(tree_btn_row)
        layout.addWidget(cond_group)

        btn_row = QtWidgets.QHBoxLayout()
        btn_row.addStretch()
        self.ok_btn = QtWidgets.QPushButton("확인")
        self.cancel_btn = QtWidgets.QPushButton("취소")
        btn_row.addWidget(self.ok_btn)
        btn_row.addWidget(self.cancel_btn)
        layout.addLayout(btn_row)

        self.ok_btn.clicked.connect(self.accept)
        self.cancel_btn.clicked.connect(self.reject)
        self.add_node_btn.clicked.connect(self._add_condition_node)
        self.add_group_btn.clicked.connect(self._add_group_condition)
        self.add_true_child_btn.clicked.connect(lambda: self._add_child_condition("true"))
        self.add_false_child_btn.clicked.connect(lambda: self._add_child_condition("false"))
        self.edit_node_btn.clicked.connect(self._edit_condition_node)
        self.clone_node_btn.clicked.connect(self._clone_condition_node)
        self.delete_node_btn.clicked.connect(self._delete_condition_node)
        self.condition_tree.itemDoubleClicked.connect(lambda *_: self._edit_condition_node())
        self.viewer_btn.clicked.connect(self._open_image_viewer)
        self.debug_test_btn.clicked.connect(self._toggle_condition_debug)
        if cond:
            self._load(cond)
        else:
            self.root_condition = Condition(type="any", conditions=[])
            self._refresh_condition_tree()

    def _load(self, cond: MacroCondition):
        self.cond_name_edit.setText(cond.name or "")
        self.root_condition = copy.deepcopy(cond.condition)
        self._refresh_condition_tree()

    def _append_condition_item(self, cond: Condition, parent_item=None):
        item = QtWidgets.QTreeWidgetItem([_condition_type_label(cond.type), _condition_brief(cond)])
        item.setData(0, QtCore.Qt.ItemDataRole.UserRole, cond)
        flags = item.flags()
        flags |= QtCore.Qt.ItemFlag.ItemIsDragEnabled | QtCore.Qt.ItemFlag.ItemIsEnabled | QtCore.Qt.ItemFlag.ItemIsSelectable
        flags |= QtCore.Qt.ItemFlag.ItemIsDropEnabled
        item.setFlags(flags)
        if parent_item:
            parent_item.addChild(item)
        else:
            self.condition_tree.addTopLevelItem(item)
        if cond.type in ("all", "any"):
            for child in cond.conditions:
                self._append_condition_item(child, item)
        if cond.on_true:
            true_header = QtWidgets.QTreeWidgetItem(["참일 때", f"{len(cond.on_true)}개"])
            true_header.setData(0, QtCore.Qt.ItemDataRole.UserRole, "branch_true")
            true_header.setFlags(QtCore.Qt.ItemFlag.ItemIsEnabled | QtCore.Qt.ItemFlag.ItemIsDropEnabled | QtCore.Qt.ItemFlag.ItemIsSelectable)
            item.addChild(true_header)
            for child in cond.on_true:
                self._append_condition_item(child, true_header)
        if cond.on_false:
            false_header = QtWidgets.QTreeWidgetItem(["거짓일 때", f"{len(cond.on_false)}개"])
            false_header.setData(0, QtCore.Qt.ItemDataRole.UserRole, "branch_false")
            false_header.setFlags(QtCore.Qt.ItemFlag.ItemIsEnabled | QtCore.Qt.ItemFlag.ItemIsDropEnabled | QtCore.Qt.ItemFlag.ItemIsSelectable)
            item.addChild(false_header)
            for child in cond.on_false:
                self._append_condition_item(child, false_header)
        return item

    def _refresh_condition_tree(self):
        self.condition_tree.clear()
        if not self.root_condition or (self.root_condition.type == "any" and not self.root_condition.conditions):
            placeholder = QtWidgets.QTreeWidgetItem(["(조건 없음)", "추가 버튼으로 루트를 만드세요."])
            placeholder.setFlags(QtCore.Qt.ItemFlag.NoItemFlags)
            self.condition_tree.addTopLevelItem(placeholder)
            return
        if self.root_condition.type == "any":
            for child in self.root_condition.conditions:
                self._append_condition_item(child)
        else:
            self._append_condition_item(self.root_condition)
        self._expand_condition_tree()
        self._restart_condition_debug_if_running()

    def _expand_condition_tree(self):
        def walk(item: QtWidgets.QTreeWidgetItem | None):
            if not item:
                return
            data = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
            is_bundle = isinstance(data, Condition) and _key_bundle_info(data)[0]
            if not is_bundle:
                self.condition_tree.expandItem(item)
            for i in range(item.childCount()):
                walk(item.child(i))

        for i in range(self.condition_tree.topLevelItemCount()):
            walk(self.condition_tree.topLevelItem(i))

    def _condition_from_item(self, item: QtWidgets.QTreeWidgetItem) -> Condition | None:
        cond = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
        if not isinstance(cond, Condition):
            return None
        cond.conditions = []
        cond.on_true = []
        cond.on_false = []
        for idx in range(item.childCount()):
            child_item = item.child(idx)
            marker = child_item.data(0, QtCore.Qt.ItemDataRole.UserRole)
            if marker == "branch_true":
                for j in range(child_item.childCount()):
                    child_cond = self._condition_from_item(child_item.child(j))
                    if child_cond:
                        cond.on_true.append(child_cond)
                continue
            if marker == "branch_false":
                for j in range(child_item.childCount()):
                    child_cond = self._condition_from_item(child_item.child(j))
                    if child_cond:
                        cond.on_false.append(child_cond)
                continue
            child_cond = self._condition_from_item(child_item)
            if child_cond:
                if cond.type in ("all", "any"):
                    cond.conditions.append(child_cond)
                else:
                    # 비그룹 노드 아래 자식은 참일 때 분기(default)로 취급
                    cond.on_true.append(child_cond)
        return cond

    def _sync_condition_from_tree(self):
        selected_cond = self._selected_condition()
        top_conditions: List[Condition] = []
        for i in range(self.condition_tree.topLevelItemCount()):
            cond = self._condition_from_item(self.condition_tree.topLevelItem(i))
            if cond:
                top_conditions.append(cond)
        if not top_conditions:
            self.root_condition = None
        elif len(top_conditions) == 1 and self.root_condition and self.root_condition.type != "any":
            self.root_condition = top_conditions[0]
        else:
            self.root_condition = Condition(type="any", conditions=top_conditions)
        self._refresh_condition_tree()
        if selected_cond:
            item = self._find_item_for_condition(selected_cond)
            if item:
                self.condition_tree.setCurrentItem(item)
        self._expand_condition_tree()

    def _find_item_for_condition(self, target: Condition) -> QtWidgets.QTreeWidgetItem | None:
        def walk(item: QtWidgets.QTreeWidgetItem) -> QtWidgets.QTreeWidgetItem | None:
            cond = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
            if cond is target:
                return item
            for idx in range(item.childCount()):
                found = walk(item.child(idx))
                if found:
                    return found
            return None

        for i in range(self.condition_tree.topLevelItemCount()):
            found = walk(self.condition_tree.topLevelItem(i))
            if found:
                return found
        return None

    def _selected_item(self) -> QtWidgets.QTreeWidgetItem | None:
        selected = self.condition_tree.selectedItems()
        return selected[0] if selected else None

    def _selected_branch_marker(self) -> str | None:
        item = self._selected_item()
        if not item:
            return None
        data = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
        if isinstance(data, str) and data in ("branch_true", "branch_false"):
            return data
        return None

    def _selected_condition(self) -> Condition | None:
        item = self._selected_item()
        if not item:
            return None
        data = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
        if isinstance(data, Condition):
            return data
        if isinstance(data, str) and data in ("branch_true", "branch_false"):
            parent = item.parent()
            if parent:
                pdata = parent.data(0, QtCore.Qt.ItemDataRole.UserRole)
                if isinstance(pdata, Condition):
                    return pdata
        return None

    def _replace_condition(self, target: Condition, new_cond: Condition) -> bool:
        if self.root_condition is target:
            self.root_condition = new_cond
            return True
        if not self.root_condition:
            return False
        return self._replace_in_children(self.root_condition, target, new_cond)

    def _replace_in_children(self, parent: Condition, target: Condition, new_cond: Condition) -> bool:
        for child_list in (parent.conditions, parent.on_true, parent.on_false):
            for idx, child in enumerate(child_list):
                if child is target:
                    child_list[idx] = new_cond
                    return True
                if self._replace_in_children(child, target, new_cond):
                    return True
        return False

    def _remove_condition(self, parent: Condition, target: Condition) -> bool:
        for child_list in (parent.conditions, parent.on_true, parent.on_false):
            for idx, child in enumerate(child_list):
                if child is target:
                    child_list.pop(idx)
                    return True
                if self._remove_condition(child, target):
                    return True
        return False

    def _find_parent_group(self, current: Condition, target: Condition) -> Condition | None:
        for child in current.conditions:
            if child is target:
                return current if current.type in ("all", "any") else None
            if child.type in ("all", "any"):
                found = self._find_parent_group(child, target)
                if found:
                    return found
        for branch_child in current.on_true + current.on_false:
            if branch_child is target:
                return current if current.type in ("all", "any") else None
            found = self._find_parent_group(branch_child, target)
            if found:
                return found
        return None

    def _add_child_condition(self, branch: str):
        parent_cond = self._selected_condition()
        if not parent_cond:
            QtWidgets.QMessageBox.information(self, "선택 없음", "하위 조건을 추가할 상위 조건을 선택하세요.")
            return

        branch_marker = self._selected_branch_marker()
        if branch_marker == "branch_false":
            branch = "false"
        elif branch_marker == "branch_true":
            branch = "true"

        dlg = ConditionNodeDialog(
            self,
            allow_group=True,
            variable_provider=self._variable_provider,
            resolver=self._resolver,
            open_debugger=self._open_debugger_fn,
        )
        if _run_dialog_non_modal(dlg):
            try:
                new_cond = dlg.get_condition()
            except ValueError as exc:
                QtWidgets.QMessageBox.warning(self, "입력 오류", str(exc))
                return
        else:
            return

        target_list = parent_cond.on_true if branch == "true" else parent_cond.on_false
        target_list.append(new_cond)
        self._refresh_condition_tree()
        item = self._find_item_for_condition(parent_cond)
        if item:
            self.condition_tree.expandItem(item)
            self.condition_tree.setCurrentItem(item)

    def _add_condition_node(self):
        dlg = ConditionNodeDialog(
            self,
            allow_group=False,
            variable_provider=self._variable_provider,
            resolver=self._resolver,
            open_debugger=self._open_debugger_fn,
        )
        if _run_dialog_non_modal(dlg):
            try:
                new_cond = dlg.get_condition()
            except ValueError as exc:
                QtWidgets.QMessageBox.warning(self, "입력 오류", str(exc))
                return
        else:
            return

        selected_cond = self._selected_condition()
        branch_marker = self._selected_branch_marker()
        branch = "false" if branch_marker == "branch_false" else "true"

        if self.root_condition is None:
            self.root_condition = Condition(type="any", conditions=[new_cond])
            self._refresh_condition_tree()
            return

        # 비그룹 조건이 선택된 경우 기본적으로 참 분기에 자식 추가
        if selected_cond and selected_cond.type not in ("all", "any"):
            if branch == "false":
                selected_cond.on_false.append(new_cond)
            else:
                selected_cond.on_true.append(new_cond)
            self._refresh_condition_tree()
            item = self._find_item_for_condition(selected_cond)
            if item:
                self.condition_tree.expandItem(item)
                self.condition_tree.setCurrentItem(item)
            return

        target_group: Condition | None = None
        if selected_cond and selected_cond.type in ("all", "any"):
            target_group = selected_cond
        elif selected_cond and self.root_condition:
            target_group = self._find_parent_group(self.root_condition, selected_cond)
        elif self.root_condition.type in ("all", "any"):
            target_group = self.root_condition

        if not target_group:
            if self.root_condition.type == "any":
                self.root_condition.conditions.append(new_cond)
            else:
                self.root_condition = Condition(type="any", conditions=[self.root_condition, new_cond])
            self._refresh_condition_tree()
            self._expand_condition_tree()
            return

        target_group.conditions.append(new_cond)
        self._refresh_condition_tree()
        self.condition_tree.expandAll()
        item = self._find_item_for_condition(target_group)
        if item:
            self.condition_tree.setCurrentItem(item)

    def _add_group_condition(self):
        dlg = ConditionNodeDialog(
            self,
            cond=Condition(type="all"),
            allow_group=True,
            variable_provider=self._variable_provider,
            resolver=self._resolver,
            open_debugger=self._open_debugger_fn,
        )
        if _run_dialog_non_modal(dlg):
            try:
                new_cond = dlg.get_condition()
            except ValueError as exc:
                QtWidgets.QMessageBox.warning(self, "입력 오류", str(exc))
                return
        else:
            return

        selected_cond = self._selected_condition()
        branch_marker = self._selected_branch_marker()
        branch = "false" if branch_marker == "branch_false" else "true"

        if self.root_condition is None:
            self.root_condition = new_cond
            self._refresh_condition_tree()
            return

        if selected_cond and selected_cond.type not in ("all", "any"):
            if branch == "false":
                selected_cond.on_false.append(new_cond)
            else:
                selected_cond.on_true.append(new_cond)
            self._refresh_condition_tree()
            item = self._find_item_for_condition(selected_cond)
            if item:
                self.condition_tree.expandItem(item)
                self.condition_tree.setCurrentItem(item)
            return

        if selected_cond and selected_cond.type in ("all", "any"):
            selected_cond.conditions.append(new_cond)
            self._refresh_condition_tree()
            self._expand_condition_tree()
            item = self._find_item_for_condition(selected_cond)
            if item:
                self.condition_tree.setCurrentItem(item)
            return

        if selected_cond and self.root_condition:
            parent_group = self._find_parent_group(self.root_condition, selected_cond)
            if parent_group:
                parent_group.conditions.append(new_cond)
                self._refresh_condition_tree()
                self._expand_condition_tree()
                item = self._find_item_for_condition(parent_group)
                if item:
                    self.condition_tree.setCurrentItem(item)
                return

        if self.root_condition.type == "any" and selected_cond is None:
            self.root_condition.conditions.append(new_cond)
            self._refresh_condition_tree()
            self._expand_condition_tree()
            item = self._find_item_for_condition(new_cond)
            if item:
                self.condition_tree.setCurrentItem(item)
            return

        if self.root_condition.type == "any":
            self.root_condition.conditions.append(new_cond)
        else:
            self.root_condition = Condition(type="any", conditions=[self.root_condition, new_cond])
        self._refresh_condition_tree()
        self._expand_condition_tree()

    def _clone_condition_node(self):
        target = self._selected_condition()
        if not target or not self.root_condition:
            QtWidgets.QMessageBox.information(self, "선택 없음", "복제할 조건을 선택하세요.")
            return
        new_cond = copy.deepcopy(target)
        inserted = False

        if target is self.root_condition:
            if target.type in ("all", "any"):
                self.root_condition.conditions.append(new_cond)
                inserted = True
            else:
                self.root_condition = Condition(type="any", conditions=[self.root_condition, new_cond])
                inserted = True
        else:
            def walk(parent: Condition) -> bool:
                nonlocal inserted
                for child_list in (parent.conditions, parent.on_true, parent.on_false):
                    for idx, child in enumerate(child_list):
                        if child is target:
                            child_list.insert(idx + 1, new_cond)
                            inserted = True
                            return True
                        if walk(child):
                            return True
                return False

            walk(self.root_condition)

        if not inserted:
            QtWidgets.QMessageBox.information(self, "복제 실패", "복제 위치를 찾지 못했습니다.")
            return

        self._refresh_condition_tree()
        item = self._find_item_for_condition(new_cond)
        if item:
            parent = item.parent()
            if parent:
                self.condition_tree.expandItem(parent)
            self.condition_tree.setCurrentItem(item)

    def _edit_condition_node(self):
        current_cond = self._selected_condition()
        if not current_cond:
            QtWidgets.QMessageBox.information(self, "선택 없음", "편집할 조건을 선택하세요.")
            return
        dlg = ConditionNodeDialog(
            self,
            cond=current_cond,
            allow_group=current_cond.type in ("all", "any"),
            variable_provider=self._variable_provider,
            resolver=self._resolver,
            open_debugger=self._open_debugger_fn,
        )
        if _run_dialog_non_modal(dlg):
            try:
                new_cond = dlg.get_condition()
            except ValueError as exc:
                QtWidgets.QMessageBox.warning(self, "입력 오류", str(exc))
                return
            if current_cond.type in ("all", "any") and current_cond.conditions and new_cond.type not in ("all", "any"):
                res = QtWidgets.QMessageBox.question(
                    self,
                    "하위 조건 삭제",
                    "그룹을 단일 조건으로 변경하면 하위 조건이 모두 삭제됩니다. 진행할까요?",
                )
                if res != QtWidgets.QMessageBox.StandardButton.Yes:
                    return
            elif new_cond.type in ("all", "any") and current_cond.type in ("all", "any"):
                new_cond.conditions = copy.deepcopy(current_cond.conditions)
            new_cond.on_true = copy.deepcopy(getattr(current_cond, "on_true", []))
            new_cond.on_false = copy.deepcopy(getattr(current_cond, "on_false", []))
            self._replace_condition(current_cond, new_cond)
            self._refresh_condition_tree()

    def _delete_condition_node(self):
        current_cond = self._selected_condition()
        if not current_cond:
            QtWidgets.QMessageBox.information(self, "선택 없음", "삭제할 조건을 선택하세요.")
            return

        if self.root_condition is current_cond:
            self.root_condition = None
            self._refresh_condition_tree()
            return

        if self.root_condition and self._remove_condition(self.root_condition, current_cond):
            self._refresh_condition_tree()
        else:
            QtWidgets.QMessageBox.warning(self, "삭제 실패", "조건을 삭제할 수 없습니다.")

    def _validate_group_children(self, cond: Condition):
        if cond.type in ("all", "any"):
            if not cond.conditions:
                raise ValueError("AND/OR 그룹에는 최소 1개의 하위 조건이 필요합니다.")
            for child in cond.conditions:
                self._validate_group_children(child)
        for child in cond.on_true + cond.on_false:
            self._validate_group_children(child)

    def get_condition(self) -> MacroCondition:
        if not self.root_condition:
            raise ValueError("조건을 하나 이상 추가하세요.")
        root_copy = copy.deepcopy(self.root_condition)
        self._validate_group_children(root_copy)

        return MacroCondition(
            condition=root_copy,
            actions=[],
            else_actions=[],
            name=self.cond_name_edit.text().strip() or None,
        )

    def _condition_debug_payload(self) -> dict:
        macro_cond = self.get_condition()
        return {
            "macro_condition": macro_cond,
            "condition": macro_cond.condition,
            "resolver": self._resolver,
            "vars_ctx": getattr(self._resolver, "vars", None) if self._resolver else None,
            "label": macro_cond.name or "조건 디버그",
        }

    def _start_condition_debug_session_internal(self, *, silent: bool = False) -> bool:
        if not callable(self._start_condition_debug_fn):
            if not silent:
                QtWidgets.QMessageBox.information(self, "지원 안 함", "디버그 테스트를 사용할 수 없습니다.")
            return False
        try:
            self._condition_debug_payload()  # 유효성 사전 확인
            provider = lambda: self._condition_debug_payload()
        except Exception as exc:
            if not silent:
                QtWidgets.QMessageBox.warning(self, "조건 오류", str(exc))
            return False
        stop_cb = self._start_condition_debug_fn(provider, on_stop=self._on_condition_debug_finished)
        if stop_cb:
            self._debug_stop_cb = stop_cb
            self.debug_test_btn.setText("디버그 중지")
            return True
        if not silent:
            QtWidgets.QMessageBox.information(self, "시작 실패", "디버그 테스트를 시작하지 못했습니다.")
        return False

    def _restart_condition_debug_if_running(self):
        if not self._debug_stop_cb:
            return
        try:
            self._debug_stop_cb()
        except Exception:
            pass
        self._debug_stop_cb = None
        self.debug_test_btn.setText("디버그 테스트")
        self._start_condition_debug_session_internal(silent=True)

    def _toggle_condition_debug(self):
        if self._debug_stop_cb:
            try:
                self._debug_stop_cb()
            except Exception:
                pass
            return
        self._start_condition_debug_session_internal()

    def _on_condition_debug_finished(self):
        self._debug_stop_cb = None
        self.debug_test_btn.setText("디버그 테스트")

    # 이미지 뷰어 --------------------------------------------------------
    def _open_image_viewer(self):
        try:
            start_dir = Path(self._image_viewer_state.get("last_dir", SCREENSHOT_DIR))
        except Exception:
            start_dir = SCREENSHOT_DIR
        if not start_dir.exists():
            start_dir = SCREENSHOT_DIR
        if self._image_viewer is None:
            self._image_viewer = ImageViewerDialog(
                None,
                start_dir=start_dir,
                condition_window=self,
                save_state=self._persist_viewer_state,
                open_screenshot_dialog=self._open_screenshot_dialog_fn,
                screenshot_hotkeys_provider=self._screenshot_hotkeys_provider,
                state=self._image_viewer_state,
                capture_manager=self._screenshot_manager,
            )
        else:
            self._image_viewer.set_start_dir(start_dir)
        self._image_viewer._resize_to_available()
        self._image_viewer.show()
        self._image_viewer.raise_()
        self._image_viewer.activateWindow()

    def _focus_viewer_if_open(self):
        if self._image_viewer and self._image_viewer.isVisible():
            self._image_viewer.show()
            self._image_viewer.raise_()
            self._image_viewer.activateWindow()

    def _persist_viewer_state(self, data: dict):
        self._image_viewer_state = data or {}
        if callable(self._save_image_viewer_state):
            try:
                self._save_image_viewer_state(self._image_viewer_state)
            except Exception:
                pass
        last_dir = self._image_viewer_state.get("last_dir")
        if last_dir:
            self.viewer_status.setText(f"최근 폴더: {last_dir}")

    def closeEvent(self, event: QtGui.QCloseEvent):
        if self._debug_stop_cb:
            try:
                self._debug_stop_cb()
            except Exception:
                pass
            self._debug_stop_cb = None
            self.debug_test_btn.setText("디버그 테스트")
        if self._image_viewer and self._image_viewer.isVisible():
            try:
                self._image_viewer.close()
            except Exception:
                pass
        return super().closeEvent(event)


class _ImageCanvas(QtWidgets.QWidget):
    sampleChanged = QtCore.pyqtSignal(object)
    zoomChanged = QtCore.pyqtSignal(float)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setMouseTracking(True)
        self._image: QtGui.QImage | None = None
        self._pixmap: QtGui.QPixmap | None = None
        self._draw_rect = QtCore.QRectF()
        self._scale = 1.0
        self._sample = None
        self._last_mouse_pos: QtCore.QPoint | None = None
        self._user_zoom = 1.0
        self._min_zoom = 0.1
        self._max_zoom = 32.0
        self._view_center = QtCore.QPointF(0, 0)
        self._dragging = False
        self._drag_start = QtCore.QPointF()
        self._center_start = QtCore.QPointF()
        self._space_pan = False

    def clear_image(self):
        self._image = None
        self._pixmap = None
        self._sample = None
        self._draw_rect = QtCore.QRectF()
        self._last_mouse_pos = None
        self._user_zoom = 1.0
        self._view_center = QtCore.QPointF(0, 0)
        self.update()
        self.sampleChanged.emit(None)
        self.zoomChanged.emit(self._user_zoom)

    def set_image(self, path: Path | None) -> bool:
        if path is None:
            self.clear_image()
            return False
        img = QtGui.QImage(str(path))
        if img.isNull():
            self.clear_image()
            return False
        self._image = img.convertToFormat(QtGui.QImage.Format.Format_RGB32)
        self._pixmap = QtGui.QPixmap.fromImage(self._image)
        self._sample = None
        self._last_mouse_pos = None
        self._user_zoom = 1.0
        self._view_center = QtCore.QPointF(self._image.width() / 2, self._image.height() / 2)
        self.update()
        self.sampleChanged.emit(None)
        self.zoomChanged.emit(self._user_zoom)
        return True

    def _clamp_center(self):
        if not self._image:
            return
        w = max(1, self._image.width())
        h = max(1, self._image.height())
        cx = max(0, min(w, self._view_center.x()))
        cy = max(0, min(h, self._view_center.y()))
        self._view_center = QtCore.QPointF(cx, cy)

    def _update_draw_rect(self):
        if not self._pixmap:
            self._draw_rect = QtCore.QRectF()
            self._scale = 1.0
            return
        avail = self.rect()
        if avail.width() <= 0 or avail.height() <= 0:
            self._draw_rect = QtCore.QRectF()
            return
        pw = float(self._pixmap.width())
        ph = float(self._pixmap.height())
        if pw <= 0 or ph <= 0:
            self._draw_rect = QtCore.QRectF()
            return
        base_scale = min(avail.width() / pw, avail.height() / ph)
        self._scale = base_scale * self._user_zoom
        self._clamp_center()
        widget_center = QtCore.QPointF(avail.center())
        origin = widget_center - QtCore.QPointF(self._view_center.x() * self._scale, self._view_center.y() * self._scale)
        self._draw_rect = QtCore.QRectF(origin, QtCore.QSizeF(pw * self._scale, ph * self._scale))

    def _build_magnifier(self):
        if not self._image or not self._sample:
            return None
        x, y = self._sample["pos"]
        radius = 8
        size = radius * 2 + 1
        x0 = max(0, x - radius)
        y0 = max(0, y - radius)
        if x0 + size > self._image.width():
            x0 = max(0, self._image.width() - size)
        if y0 + size > self._image.height():
            y0 = max(0, self._image.height() - size)
        region = self._image.copy(x0, y0, size, size)
        zoom = 12
        scaled = region.scaled(
            region.width() * zoom,
            region.height() * zoom,
            QtCore.Qt.AspectRatioMode.IgnoreAspectRatio,
            QtCore.Qt.TransformationMode.FastTransformation,
        )
        return QtGui.QPixmap.fromImage(scaled)

    def _widget_to_image(self, pos: QtCore.QPointF) -> QtCore.QPointF | None:
        if not self._image or self._scale <= 0 or self._draw_rect.isNull():
            return None
        x = (pos.x() - self._draw_rect.left()) / self._scale
        y = (pos.y() - self._draw_rect.top()) / self._scale
        return QtCore.QPointF(x, y)

    def reset_zoom(self):
        if not self._image:
            return
        self._user_zoom = 1.0
        self._view_center = QtCore.QPointF(self._image.width() / 2, self._image.height() / 2)
        self._update_draw_rect()
        self._update_sample_from_pos()
        self.zoomChanged.emit(self._user_zoom)

    def zoom_step(self, steps: int, anchor: QtCore.QPoint | None = None):
        factor = 1.15 ** steps
        self._apply_zoom(self._user_zoom * factor, anchor=anchor)

    def _apply_zoom(self, new_zoom: float, anchor: QtCore.QPoint | None = None):
        if not self._image:
            return
        new_zoom = max(self._min_zoom, min(self._max_zoom, float(new_zoom)))
        avail = self.rect()
        if avail.width() <= 0 or avail.height() <= 0:
            return
        pw = float(self._image.width())
        ph = float(self._image.height())
        base_scale = min(avail.width() / pw, avail.height() / ph)
        new_scale = base_scale * new_zoom
        anchor_point = QtCore.QPointF(anchor) if anchor is not None else QtCore.QPointF(avail.center())
        anchor_img = self._widget_to_image(anchor_point) or self._view_center
        widget_center = QtCore.QPointF(avail.center())
        new_center = QtCore.QPointF(
            (widget_center.x() - anchor_point.x()) / new_scale + anchor_img.x(),
            (widget_center.y() - anchor_point.y()) / new_scale + anchor_img.y(),
        )
        self._user_zoom = new_zoom
        self._view_center = new_center
        self._update_draw_rect()
        self._update_sample_from_pos()
        self.zoomChanged.emit(self._user_zoom)

    def zoom_factor(self) -> float:
        return float(self._user_zoom)

    def view_state(self) -> dict:
        return {
            "center": (float(self._view_center.x()), float(self._view_center.y())),
            "zoom": float(self._user_zoom),
        }

    def apply_view_state(self, state: dict | None, *, sample_pos=None):
        if not state or not self._image:
            return
        center = state.get("center")
        zoom = state.get("zoom", self._user_zoom)
        if isinstance(center, (list, tuple)) and len(center) == 2:
            self._view_center = QtCore.QPointF(float(center[0]), float(center[1]))
        self._apply_zoom(float(zoom), anchor=None)
        if sample_pos:
            self.set_sample_from_image_pos(sample_pos)

    def set_sample_from_image_pos(self, pos):
        if not self._image or not pos:
            return
        try:
            x, y = int(pos[0]), int(pos[1])
        except Exception:
            return
        x = max(0, min(self._image.width() - 1, x))
        y = max(0, min(self._image.height() - 1, y))
        widget_x = self._draw_rect.left() + x * self._scale
        widget_y = self._draw_rect.top() + y * self._scale
        self._last_mouse_pos = QtCore.QPoint(int(widget_x), int(widget_y))
        color = self._image.pixelColor(x, y)
        hex_text = f"{color.red():02x}{color.green():02x}{color.blue():02x}"
        sample = {"pos": (x, y), "widget_pos": QtCore.QPoint(int(widget_x), int(widget_y)), "color": color, "hex": hex_text}
        self._set_sample(sample)

    def _set_sample(self, sample):
        if sample == self._sample:
            return
        self._sample = sample
        self.sampleChanged.emit(sample)
        self.update()

    def _update_sample_from_pos(self):
        if not self._image or self._draw_rect.isNull() or not self._last_mouse_pos:
            self._set_sample(None)
            return
        posf = QtCore.QPointF(self._last_mouse_pos)
        if not self._draw_rect.contains(posf):
            self._set_sample(None)
            return
        rel_x = (posf.x() - self._draw_rect.left()) / self._scale
        rel_y = (posf.y() - self._draw_rect.top()) / self._scale
        x = int(rel_x)
        y = int(rel_y)
        x = max(0, min(self._image.width() - 1, x))
        y = max(0, min(self._image.height() - 1, y))
        color = self._image.pixelColor(x, y)
        hex_text = f"{color.red():02x}{color.green():02x}{color.blue():02x}"
        sample = {"pos": (x, y), "widget_pos": QtCore.QPoint(int(posf.x()), int(posf.y())), "color": color, "hex": hex_text}
        self._set_sample(sample)

    def paintEvent(self, event: QtGui.QPaintEvent):
        painter = QtGui.QPainter(self)
        painter.fillRect(self.rect(), QtGui.QColor(10, 12, 16))
        if not self._pixmap:
            painter.setPen(QtGui.QColor("#5a657d"))
            painter.drawText(self.rect(), QtCore.Qt.AlignmentFlag.AlignCenter, "이미지를 불러오세요.")
            return
        self._update_draw_rect()
        # 픽셀 단위 표시를 위해 부드러운 스케일을 끄고 최근접으로 그린다.
        painter.setRenderHint(QtGui.QPainter.RenderHint.SmoothPixmapTransform, False)
        painter.drawPixmap(self._draw_rect, self._pixmap, QtCore.QRectF(self._pixmap.rect()))

        if not self._sample:
            return
        pos = self._sample["widget_pos"]
        color = self._sample["color"]
        hex_text = self._sample["hex"]
        painter.setRenderHint(QtGui.QPainter.RenderHint.Antialiasing, True)

        magnifier = self._build_magnifier()
        if magnifier:
            mag_size = magnifier.size()
            mag_rect = QtCore.QRect(pos + QtCore.QPoint(18, 18), mag_size)
            margin = 12
            if mag_rect.right() > self.width() - margin:
                mag_rect.moveRight(self.width() - margin)
            if mag_rect.bottom() > self.height() - margin:
                mag_rect.moveBottom(self.height() - margin)
            if mag_rect.left() < margin:
                mag_rect.moveLeft(margin)
            if mag_rect.top() < margin:
                mag_rect.moveTop(margin)
            painter.fillRect(mag_rect.adjusted(-4, -4, 4, 4), QtGui.QColor(0, 0, 0, 200))
            painter.drawPixmap(mag_rect.topLeft(), magnifier)
            painter.setPen(QtGui.QPen(QtGui.QColor("#9ad1ff")))
            painter.drawRect(mag_rect.adjusted(0, 0, -1, -1))
            center_pt = mag_rect.center()
            painter.setPen(QtGui.QPen(QtGui.QColor("#ffffff"), 1))
            painter.drawLine(mag_rect.left(), center_pt.y(), mag_rect.right(), center_pt.y())
            painter.drawLine(center_pt.x(), mag_rect.top(), center_pt.x(), mag_rect.bottom())

            color_box = QtCore.QRect(mag_rect.right() + 10, mag_rect.top(), 80, mag_rect.height())
            if color_box.right() > self.width() - margin:
                color_box.moveLeft(mag_rect.left() - color_box.width() - 10)
            painter.fillRect(color_box, color)
            painter.setPen(QtGui.QPen(QtGui.QColor("#222")))
            painter.drawRect(color_box.adjusted(0, 0, -1, -1))
            text_pos = QtCore.QPoint(color_box.right() + 8, color_box.top() + 20)
        else:
            text_pos = pos + QtCore.QPoint(18, 18)
        painter.setPen(QtGui.QColor("#e8f4ff"))
        text = f"{self._sample['pos'][0]},{self._sample['pos'][1]}  #{hex_text}"
        painter.drawText(text_pos, text)

    def mouseMoveEvent(self, event: QtGui.QMouseEvent):
        self._last_mouse_pos = event.position().toPoint() if hasattr(event, "position") else event.pos()
        if self._dragging and self._scale > 0:
            delta = QtCore.QPointF(self._last_mouse_pos) - self._drag_start
            self._view_center = self._center_start - QtCore.QPointF(delta.x() / self._scale, delta.y() / self._scale)
            self._update_draw_rect()
        self._update_sample_from_pos()
        super().mouseMoveEvent(event)

    def leaveEvent(self, event: QtCore.QEvent):
        self._set_sample(None)
        super().leaveEvent(event)

    def mousePressEvent(self, event: QtGui.QMouseEvent):
        pos = event.position().toPoint() if hasattr(event, "position") else event.pos()
        self._last_mouse_pos = pos
        self._update_sample_from_pos()
        if event.button() == QtCore.Qt.MouseButton.LeftButton:
            # 좌클릭 드래그로 이동만 수행
            self._dragging = True
            self._drag_start = QtCore.QPointF(pos)
            self._center_start = QtCore.QPointF(self._view_center)
            event.accept()
            return
        super().mousePressEvent(event)

    def mouseReleaseEvent(self, event: QtGui.QMouseEvent):
        if event.button() == QtCore.Qt.MouseButton.LeftButton:
            self._dragging = False
            if self._space_pan:
                self.setCursor(QtCore.Qt.CursorShape.OpenHandCursor)
            event.accept()
            return
        super().mouseReleaseEvent(event)

    def wheelEvent(self, event: QtGui.QWheelEvent):
        delta = event.angleDelta().y()
        if delta == 0:
            return super().wheelEvent(event)
        steps = 1 if delta > 0 else -1
        anchor = event.position().toPoint() if hasattr(event, "position") else event.pos()
        if event.modifiers() & QtCore.Qt.KeyboardModifier.AltModifier:
            self.zoom_step(steps, anchor=anchor)
        else:
            self.zoom_step(steps, anchor=anchor)
        event.accept()

    def resizeEvent(self, event: QtGui.QResizeEvent):
        self._update_draw_rect()
        super().resizeEvent(event)


class ImageViewerDialog(QtWidgets.QDialog):
    def __init__(
        self,
        parent=None,
        *,
        start_dir: Path,
        condition_window=None,
        save_state=None,
        open_screenshot_dialog=None,
        screenshot_hotkeys_provider=None,
        state: dict | None = None,
        capture_manager=None,
    ):
        super().__init__(parent)
        self.setWindowTitle("이미지 뷰어/피커")
        self.setModal(False)
        self.setWindowModality(QtCore.Qt.WindowModality.NonModal)
        self.setWindowFlags(
            QtCore.Qt.WindowType.Window
            | QtCore.Qt.WindowType.WindowMinimizeButtonHint
            | QtCore.Qt.WindowType.WindowMaximizeButtonHint
            | QtCore.Qt.WindowType.WindowCloseButtonHint
        )
        self._condition_window = condition_window
        self._save_state = save_state
        self._open_screenshot_dialog = open_screenshot_dialog
        self._screenshot_hotkeys_provider = screenshot_hotkeys_provider
        self._capture_manager = capture_manager
        self._capture_listener = None
        self._current_folder = Path(start_dir)
        self._image_files: list[Path] = []
        self._current_index = -1
        self._last_sample = None
        self._focused_on_viewer = True
        self._status_prefix = ""
        self._pending_state: dict | None = None
        self._auto_refresh_enabled = bool((state or {}).get("auto_refresh"))

        self._build_ui()
        self.set_start_dir(start_dir, refresh=True)
        self._attach_capture_listener()

    def _build_ui(self):
        layout = QtWidgets.QVBoxLayout(self)

        def _make_section(title: str, content: QtWidgets.QWidget, state_key: str, *, default_open: bool = True) -> QtWidgets.QWidget:
            btn = QtWidgets.QToolButton()
            btn.setText(title)
            btn.setCheckable(True)
            btn.setChecked(default_open)
            btn.setToolButtonStyle(QtCore.Qt.ToolButtonStyle.ToolButtonTextBesideIcon)
            btn.setArrowType(QtCore.Qt.ArrowType.DownArrow if default_open else QtCore.Qt.ArrowType.RightArrow)
            container = QtWidgets.QWidget()
            v = QtWidgets.QVBoxLayout(container)
            v.setContentsMargins(0, 0, 0, 0)
            v.addWidget(content)

            def _toggle(opened: bool):
                container.setVisible(opened)
                btn.setArrowType(QtCore.Qt.ArrowType.DownArrow if opened else QtCore.Qt.ArrowType.RightArrow)
                self._section_controls[state_key] = btn
                if self._save_state_cb:
                    try:
                        self._save_state_cb(self._collect_state())
                    except Exception:
                        pass

            btn.toggled.connect(_toggle)
            _toggle(default_open)

            wrap = QtWidgets.QWidget()
            wrap_layout = QtWidgets.QVBoxLayout(wrap)
            wrap_layout.setContentsMargins(0, 0, 0, 0)
            wrap_layout.addWidget(btn)
            wrap_layout.addWidget(container)
            self._section_controls[state_key] = btn
            return wrap
        layout.setContentsMargins(6, 6, 6, 6)

        top = QtWidgets.QHBoxLayout()
        self.folder_btn = QtWidgets.QPushButton("폴더 선택")
        self.path_label = QtWidgets.QLabel("")
        self.path_label.setTextInteractionFlags(QtCore.Qt.TextInteractionFlag.TextSelectableByMouse)
        self.image_combo = QtWidgets.QComboBox()
        self.open_folder_btn = QtWidgets.QPushButton("폴더 열기")
        self.delete_btn = QtWidgets.QPushButton("전체 삭제")
        self.delete_current_btn = QtWidgets.QPushButton("현재 삭제")
        self.refresh_btn = QtWidgets.QPushButton("새로고침")
        self.auto_refresh_chk = QtWidgets.QCheckBox("단일 캡처 후 새로고침")
        self.screenshot_btn = QtWidgets.QPushButton("스크린샷")
        self.close_btn = QtWidgets.QPushButton("종료")
        top.addWidget(self.folder_btn)
        top.addWidget(self.image_combo, 1)
        top.addWidget(self.open_folder_btn)
        top.addWidget(self.delete_btn)
        top.addWidget(self.delete_current_btn)
        top.addWidget(self.refresh_btn)
        top.addWidget(self.auto_refresh_chk)
        top.addWidget(self.screenshot_btn)
        top.addWidget(self.close_btn)
        layout.addLayout(top)

        self.hud_label = QtWidgets.QLabel("")
        self.hud_label.setStyleSheet("color: #d9e7ff; background: rgba(30,40,60,0.6); padding: 4px;")
        self.path_label.setStyleSheet("color: #9fb2cc;")
        layout.addWidget(self.path_label)
        layout.addWidget(self.hud_label)

        self.canvas = _ImageCanvas()
        self.canvas.setFocusPolicy(QtCore.Qt.FocusPolicy.StrongFocus)
        layout.addWidget(self.canvas, 1)

        self.status_label = QtWidgets.QLabel("스크린샷 폴더 이미지를 선택하세요.")
        self.status_label.setStyleSheet("color: #b5c2d6;")
        layout.addWidget(self.status_label)

        self.folder_btn.clicked.connect(self._choose_folder)
        self.image_combo.currentIndexChanged.connect(self._on_image_changed)
        self.close_btn.clicked.connect(self.close)
        self.canvas.sampleChanged.connect(self._on_sample_changed)
        self.canvas.zoomChanged.connect(self._on_zoom_changed)
        self.screenshot_btn.clicked.connect(self._open_screenshot)
        self.open_folder_btn.clicked.connect(self._open_current_folder)
        self.delete_btn.clicked.connect(self._delete_all_in_folder)
        self.delete_current_btn.clicked.connect(self._delete_current_file)
        self.refresh_btn.clicked.connect(self._refresh_folder)
        self.auto_refresh_chk.setChecked(self._auto_refresh_enabled)
        self.auto_refresh_chk.toggled.connect(self._remember_folder)
        if not callable(self._open_screenshot_dialog):
            self.screenshot_btn.setEnabled(False)
        self._update_hud_text()

    def set_start_dir(self, path: Path, *, refresh: bool = False):
        new_dir = Path(path)
        if not new_dir.exists():
            new_dir = SCREENSHOT_DIR
        if refresh or new_dir != self._current_folder:
            self._current_folder = new_dir
            self._load_folder(new_dir)
            self._remember_folder()

    def _remember_folder(self):
        data = {"last_dir": str(self._current_folder), "auto_refresh": bool(self.auto_refresh_chk.isChecked())}
        if callable(self._save_state):
            try:
                self._save_state(data)
            except Exception:
                pass

    def _attach_capture_listener(self):
        if not self._capture_manager or not hasattr(self._capture_manager, "add_capture_listener"):
            return
        if self._capture_listener:
            return

        def _listener(path):
            try:
                QtCore.QMetaObject.invokeMethod(
                    self,
                    "_on_capture_from_manager",
                    QtCore.Qt.ConnectionType.QueuedConnection,
                    QtCore.Q_ARG(str, str(path)),
                )
            except Exception:
                pass

        try:
            self._capture_manager.add_capture_listener(_listener)
            self._capture_listener = _listener
        except Exception:
            self._capture_listener = None

    def _choose_folder(self):
        path = QtWidgets.QFileDialog.getExistingDirectory(self, "스크린샷 폴더 선택", str(self._current_folder))
        if not path:
            return
        self._current_folder = Path(path)
        self._load_folder(self._current_folder)
        self._remember_folder()

    def _load_folder(self, folder: Path):
        try:
            files = []
            if folder.exists():
                for ext in ("*.png", "*.jpg", "*.jpeg", "*.bmp"):
                    files.extend(folder.glob(ext))
                files = sorted(files, key=lambda p: p.stat().st_mtime, reverse=True)
            else:
                files = []
        except Exception:
            files = []
        self._image_files = files
        self.image_combo.blockSignals(True)
        self.image_combo.clear()
        for f in files:
            self.image_combo.addItem(f.name, f)
        self.image_combo.blockSignals(False)
        self.path_label.setText(str(folder))
        if files:
            self._select_index(0)
        else:
            self._current_index = -1
            self.canvas.clear_image()
            self._status_prefix = "이미지를 찾을 수 없습니다. (png/jpg/jpeg/bmp)"
            self._render_status()

    def _on_image_changed(self, idx: int):
        self._select_index(idx)

    def _read_metadata(self, path: Path) -> dict | None:
        try:
            meta_path = path.with_suffix(path.suffix + ".json")
            if not meta_path.exists():
                return None
            return json.loads(meta_path.read_text(encoding="utf-8"))
        except Exception:
            return None

    def _select_index(self, idx: int):
        self._pending_state = self._capture_view_state()
        if not self._image_files:
            self._current_index = -1
            return
        idx = max(0, min(len(self._image_files) - 1, idx))
        if idx == self._current_index:
            return
        self._current_index = idx
        self.image_combo.blockSignals(True)
        self.image_combo.setCurrentIndex(idx)
        self.image_combo.blockSignals(False)
        path = self._image_files[idx]
        ok = self.canvas.set_image(path)
        if ok:
            img = self.canvas._image
            dims = f"{img.width()}x{img.height()}" if isinstance(img, QtGui.QImage) else "-"
            self._status_prefix = f"{path.name} | {path.stat().st_size / 1024:.1f} KB, {dims}"
            meta = self._read_metadata(path)
            if meta:
                meta_parts = []
                if meta.get("type"):
                    meta_parts.append(str(meta.get("type")))
                if meta.get("label"):
                    meta_parts.append(str(meta.get("label")))
                if meta.get("fail_path"):
                    meta_parts.append(str(meta.get("fail_path")))
                if meta.get("timestamp"):
                    try:
                        ts_txt = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(float(meta.get("timestamp"))))
                        meta_parts.append(ts_txt)
                    except Exception:
                        pass
                if meta_parts:
                    self._status_prefix += " | 메타: " + " / ".join(meta_parts)
            self._last_sample = None
            self._restore_view_state()
        else:
            self._status_prefix = "이미지를 열 수 없습니다."
            self._render_status()

    def _on_sample_changed(self, sample):
        self._last_sample = sample
        if not sample:
            self._render_status()
            return
        x, y = sample["pos"]
        hex_text = sample["hex"]
        self.status_label.setText(f"x={x}, y={y} | #{hex_text} | Zoom x{self.canvas.zoom_factor():.2f}")

    def _on_zoom_changed(self, zoom: float):
        if self._last_sample:
            self._on_sample_changed(self._last_sample)
        else:
            self._render_status()

    def _capture_view_state(self) -> dict | None:
        if not self.canvas._image:
            return None
        state = self.canvas.view_state()
        if self._last_sample:
            state["sample"] = self._last_sample.get("pos")
        return state

    def _restore_view_state(self):
        state = self._pending_state
        self._pending_state = None
        if not state:
            self._render_status()
            return
        sample = state.get("sample")
        self.canvas.apply_view_state(state, sample_pos=sample)
        if not sample:
            self._render_status()

    @QtCore.pyqtSlot(str)
    def _on_capture_from_manager(self, path_str: str):
        if not self.auto_refresh_chk.isChecked():
            return
        self._refresh_folder()

    def _nudge_sample(self, dx: int, dy: int):
        img = getattr(self.canvas, "_image", None)
        if img is None:
            return
        if self._last_sample and "pos" in self._last_sample:
            x, y = self._last_sample["pos"]
        else:
            x, y = img.width() // 2, img.height() // 2
        self.canvas.set_sample_from_image_pos((x + dx, y + dy))

    def keyPressEvent(self, event: QtGui.QKeyEvent):
        key = event.key()
        ctrl = event.modifiers() & QtCore.Qt.KeyboardModifier.ControlModifier
        if key == QtCore.Qt.Key.Key_Space:
            self.canvas._space_pan = True
            self.canvas.setCursor(QtCore.Qt.CursorShape.OpenHandCursor)
            return
        if key == QtCore.Qt.Key.Key_Escape:
            self.close()
            return
        if key == QtCore.Qt.Key.Key_F5:
            self._refresh_folder()
            return
        if key == QtCore.Qt.Key.Key_Delete:
            self._delete_current_file()
            return
        if key in (
            QtCore.Qt.Key.Key_Left,
            QtCore.Qt.Key.Key_Right,
            QtCore.Qt.Key.Key_Up,
            QtCore.Qt.Key.Key_Down,
        ):
            if ctrl and key in (QtCore.Qt.Key.Key_Left, QtCore.Qt.Key.Key_Right):
                delta = -1 if key == QtCore.Qt.Key.Key_Left else 1
                self._select_index(self._current_index + delta)
                return
            dx = -1 if key == QtCore.Qt.Key.Key_Left else 1 if key == QtCore.Qt.Key.Key_Right else 0
            dy = -1 if key == QtCore.Qt.Key.Key_Up else 1 if key == QtCore.Qt.Key.Key_Down else 0
            self._nudge_sample(dx, dy)
            return
        if key == QtCore.Qt.Key.Key_F1:
            self._copy_coords()
            return
        if key == QtCore.Qt.Key.Key_F2:
            self._copy_color()
            return
        if key in (QtCore.Qt.Key.Key_Plus, QtCore.Qt.Key.Key_Equal):
            self.canvas.zoom_step(1, anchor=self.canvas._last_mouse_pos)
            return
        if key == QtCore.Qt.Key.Key_Minus:
            self.canvas.zoom_step(-1, anchor=self.canvas._last_mouse_pos)
            return
        if key == QtCore.Qt.Key.Key_0:
            self.canvas.reset_zoom()
            return
        super().keyPressEvent(event)

    def keyReleaseEvent(self, event: QtGui.QKeyEvent):
        if event.key() == QtCore.Qt.Key.Key_Space:
            self.canvas._space_pan = False
            if not self.canvas._dragging:
                self.canvas.setCursor(QtCore.Qt.CursorShape.ArrowCursor)
            return
        super().keyReleaseEvent(event)

    def _toggle_focus(self):
        if self.isActiveWindow():
            self._focus_condition_window()
        else:
            self.showNormal()
            self.raise_()
            self.activateWindow()
            self.canvas.setFocus()
            self._focused_on_viewer = True

    def _copy_coords(self):
        if not self._last_sample:
            self.status_label.setText("좌표를 가져오려면 이미지 위에 마우스를 올리세요.")
            return
        x, y = self._last_sample["pos"]
        txt = f"{x},{y},1,1"
        QtGui.QGuiApplication.clipboard().setText(txt)
        QtWidgets.QToolTip.showText(QtGui.QCursor.pos(), f"좌표 복사: {txt}", self, QtCore.QRect(), 2000)
        self.status_label.setText(f"좌표 복사: {txt}")
        # 조건 편집창(Debugger)이 열려 있다면 region 필드를 갱신해준다.
        try:
            dbg = getattr(self._condition_window, "debugger", None) if self._condition_window else None
            if dbg and dbg.isVisible():
                dbg._set_test_inputs({"region_raw": txt})
        except Exception:
            pass
        self._fill_condition_dialog_region(txt)

    def _fill_condition_dialog_region(self, region_text: str):
        """현재 열려 있는 조건 편집/노드 창의 region 필드를 채운다."""
        try:
            for w in QtWidgets.QApplication.topLevelWidgets():
                if not w.isVisible():
                    continue
                if hasattr(w, "region_edit"):
                    try:
                        w.region_edit.setText(region_text)
                        if hasattr(w, "region_offset_edit"):
                            w.region_offset_edit.setText("")
                    except Exception:
                        pass
        except Exception:
            pass

    def _copy_color(self):
        if not self._last_sample:
            self.status_label.setText("색상을 가져오려면 이미지 위에 마우스를 올리세요.")
            return
        hex_text = self._last_sample["hex"]
        QtGui.QGuiApplication.clipboard().setText(hex_text)
        QtWidgets.QToolTip.showText(QtGui.QCursor.pos(), f"색상 복사: #{hex_text}", self, QtCore.QRect(), 2000)
        self.status_label.setText(f"색상 복사: #{hex_text}")

    def mousePressEvent(self, event: QtGui.QMouseEvent):
        if event.button() == QtCore.Qt.MouseButton.RightButton:
            self._copy_color()
            event.accept()
            return
        super().mousePressEvent(event)

    def showEvent(self, event: QtGui.QShowEvent):
        super().showEvent(event)
        self._resize_to_available()
        self._update_hud_text()
        self._attach_capture_listener()
        self.canvas.setFocus()

    def closeEvent(self, event: QtGui.QCloseEvent):
        self._remember_folder()
        if self._capture_manager and self._capture_listener and hasattr(self._capture_manager, "remove_capture_listener"):
            try:
                self._capture_manager.remove_capture_listener(self._capture_listener)
            except Exception:
                pass
            self._capture_listener = None
        return super().closeEvent(event)

    def _resize_to_available(self):
        screen = self.screen() or QtGui.QGuiApplication.primaryScreen()
        if screen:
            geo = screen.availableGeometry()
            self.setGeometry(geo)

    def _render_status(self):
        if not self._status_prefix:
            return
        self.status_label.setText(f"{self._status_prefix} | Zoom x{self.canvas.zoom_factor():.2f}")

    def _delete_all_in_folder(self):
        folder = Path(self._current_folder)
        if not folder.exists():
            QtWidgets.QMessageBox.information(self, "폴더 없음", "폴더가 없습니다.")
            return
        files = [p for p in folder.iterdir() if p.is_file()]
        if not files:
            QtWidgets.QMessageBox.information(self, "삭제 대상 없음", "삭제할 파일이 없습니다.")
            return
        res = QtWidgets.QMessageBox.question(
            self,
            "전체 삭제",
            f"{folder} 폴더의 파일 {len(files)}개를 모두 삭제할까요?",
            QtWidgets.QMessageBox.StandardButton.Yes | QtWidgets.QMessageBox.StandardButton.No,
            QtWidgets.QMessageBox.StandardButton.No,
        )
        if res != QtWidgets.QMessageBox.StandardButton.Yes:
            return
        removed = 0
        for p in files:
            try:
                p.unlink()
                removed += 1
            except Exception:
                pass
        self._load_folder(folder)
        self.status_label.setText(f"삭제 완료: {removed}개 삭제")

    def _refresh_folder(self):
        self._load_folder(self._current_folder)

    def _open_current_folder(self):
        folder = Path(self._current_folder)
        if not folder.exists():
            QtWidgets.QMessageBox.information(self, "폴더 없음", "폴더가 없습니다.")
            return
        url = QtCore.QUrl.fromLocalFile(str(folder))
        QtGui.QDesktopServices.openUrl(url)

    def _delete_current_file(self):
        if not self._image_files or self._current_index < 0 or self._current_index >= len(self._image_files):
            QtWidgets.QMessageBox.information(self, "삭제 대상 없음", "삭제할 이미지가 없습니다.")
            return
        target = self._image_files[self._current_index]
        res = QtWidgets.QMessageBox.question(
            self,
            "현재 이미지 삭제",
            f"{target.name} 파일을 삭제할까요?",
            QtWidgets.QMessageBox.StandardButton.Yes | QtWidgets.QMessageBox.StandardButton.No,
            QtWidgets.QMessageBox.StandardButton.No,
        )
        if res != QtWidgets.QMessageBox.StandardButton.Yes:
            return
        try:
            target.unlink()
        except Exception as exc:
            QtWidgets.QMessageBox.warning(self, "삭제 실패", str(exc))
            return
        next_idx = min(self._current_index, len(self._image_files) - 2)
        self._load_folder(self._current_folder)
        if self._image_files:
            self._select_index(max(0, next_idx))
        else:
            self.status_label.setText("이미지를 삭제했습니다. (폴더 비어 있음)")

    def _current_hotkey_info(self) -> dict:
        if callable(self._screenshot_hotkeys_provider):
            try:
                return self._screenshot_hotkeys_provider() or {}
            except Exception:
                return {}
        return {}

    def _update_hud_text(self):
        hk = self._current_hotkey_info()
        hk_start = hk.get("start") or "-"
        hk_stop = hk.get("stop") or "-"
        hk_cap = hk.get("capture") or "-"
        self.hud_label.setText(
            f"핫키: 좌클릭 드래그 이동, Alt+휠/± 확대, 0 리셋, F1 좌표 복사, F2 색상 복사(우클릭 가능), "
            f"F5 새로고침, Delete 현재 삭제, ←/→ 이미지 이동, ESC 닫기 | 스크린샷: 시작={hk_start}, 정지={hk_stop}, 단일={hk_cap}"
        )

    def _open_screenshot(self):
        if callable(self._open_screenshot_dialog):
            try:
                self._open_screenshot_dialog()
            except Exception:
                pass

    def _focus_condition_window(self):
        if self._condition_window:
            try:
                self._condition_window.showNormal()
            except Exception:
                try:
                    self._condition_window.show()
                except Exception:
                    pass
            try:
                self._condition_window.raise_()
                self._condition_window.activateWindow()
            except Exception:
                pass
        try:
            self.lower()
        except Exception:
            pass
        self._focused_on_viewer = False


class _NoHoverDelegate(QtWidgets.QStyledItemDelegate):
    def paint(self, painter: QtGui.QPainter, option: QtWidgets.QStyleOptionViewItem, index: QtCore.QModelIndex):
        opt = QtWidgets.QStyleOptionViewItem(option)
        try:
            hover_flag = QtWidgets.QStyle.StateFlag.State_MouseOver  # Qt6
            focus_flag = QtWidgets.QStyle.StateFlag.State_HasFocus
        except AttributeError:
            hover_flag = QtWidgets.QStyle.State_MouseOver  # Qt5 fallback
            focus_flag = QtWidgets.QStyle.State_HasFocus
        opt.state &= ~hover_flag
        opt.state &= ~focus_flag
        super().paint(painter, opt, index)


class _TypeIndentDelegate(QtWidgets.QStyledItemDelegate):
    def __init__(self, tree: QtWidgets.QTreeWidget):
        super().__init__(tree)
        self.tree = tree

    def _level(self, index: QtCore.QModelIndex) -> int:
        if hasattr(self.tree, "_item_level"):
            return self.tree._item_level(index)
        level = 0
        parent = index.parent()
        while parent.isValid():
            level += 1
            parent = parent.parent()
        return level

    def paint(self, painter: QtGui.QPainter, option: QtWidgets.QStyleOptionViewItem, index: QtCore.QModelIndex):
        opt = QtWidgets.QStyleOptionViewItem(option)
        self.initStyleOption(opt, index)
        try:
            hover_flag = QtWidgets.QStyle.StateFlag.State_MouseOver
            focus_flag = QtWidgets.QStyle.StateFlag.State_HasFocus
        except AttributeError:
            hover_flag = QtWidgets.QStyle.State_MouseOver
            focus_flag = QtWidgets.QStyle.State_HasFocus
        opt.state &= ~hover_flag
        opt.state &= ~focus_flag
        if opt.state & QtWidgets.QStyle.StateFlag.State_Selected:
            highlight = QtGui.QColor("#e8f2ff")
            painter.save()
            painter.fillRect(option.rect, highlight)
            painter.restore()
        level = self._level(index)
        indent = getattr(self.tree, "_type_indent", max(12, self.tree.indentation()))
        opt.rect = opt.rect.adjusted(indent * level, 0, 0, 0)
        style = opt.widget.style() if opt.widget else QtWidgets.QApplication.style()
        style.drawControl(QtWidgets.QStyle.ControlElement.CE_ItemViewItem, opt, painter, opt.widget)

    def sizeHint(self, option: QtWidgets.QStyleOptionViewItem, index: QtCore.QModelIndex) -> QtCore.QSize:
        opt = QtWidgets.QStyleOptionViewItem(option)
        self.initStyleOption(opt, index)
        size = super().sizeHint(opt, index)
        level = self._level(index)
        indent = getattr(self.tree, "_type_indent", max(12, self.tree.indentation()))
        size.setWidth(size.width() + indent * level)
        return size


class _DepthCheckDelegate(QtWidgets.QStyledItemDelegate):
    def __init__(self, tree: QtWidgets.QTreeWidget):
        super().__init__(tree)
        self.tree = tree

    def _level(self, index: QtCore.QModelIndex) -> int:
        if hasattr(self.tree, "_item_level"):
            return self.tree._item_level(index)
        level = 0
        parent = index.parent()
        while parent.isValid():
            level += 1
            parent = parent.parent()
        return level

    def paint(self, painter: QtGui.QPainter, option: QtWidgets.QStyleOptionViewItem, index: QtCore.QModelIndex):
        opt = QtWidgets.QStyleOptionViewItem(option)
        self.initStyleOption(opt, index)
        # hover/포커스 제거하여 체크 렌더링 깜빡임 방지
        try:
            hover_flag = QtWidgets.QStyle.StateFlag.State_MouseOver
            focus_flag = QtWidgets.QStyle.StateFlag.State_HasFocus
        except AttributeError:
            hover_flag = QtWidgets.QStyle.State_MouseOver  # Qt5 fallback
            focus_flag = QtWidgets.QStyle.State_HasFocus
        opt.state &= ~hover_flag
        opt.state &= ~focus_flag
        if opt.state & QtWidgets.QStyle.StateFlag.State_Selected:
            highlight = QtGui.QColor("#e8f2ff")
            painter.save()
            painter.fillRect(option.rect, highlight)
            painter.restore()
        level = self._level(index)
        indent = getattr(self.tree, "_type_indent", max(12, self.tree.indentation()))
        opt.rect = opt.rect.adjusted(indent * level, 0, 0, 0)
        style = opt.widget.style() if opt.widget else QtWidgets.QApplication.style()
        style.drawControl(QtWidgets.QStyle.ControlElement.CE_ItemViewItem, opt, painter, opt.widget)

    def sizeHint(self, option: QtWidgets.QStyleOptionViewItem, index: QtCore.QModelIndex) -> QtCore.QSize:
        opt = QtWidgets.QStyleOptionViewItem(option)
        self.initStyleOption(opt, index)
        size = super().sizeHint(opt, index)
        level = self._level(index)
        indent = getattr(self.tree, "_type_indent", max(12, self.tree.indentation()))
        size.setWidth(size.width() + indent * level)
        return size


class _VariableSeparatorDelegate(QtWidgets.QStyledItemDelegate):
    """Draw a thicker vertical line after each (이름, 값) 쌍."""

    def paint(self, painter: QtGui.QPainter, option: QtWidgets.QStyleOptionViewItem, index: QtCore.QModelIndex):
        super().paint(painter, option, index)
        model = index.model()
        if not model:
            return
        is_pair_boundary = (index.column() % 2 == 1) and (index.column() != model.columnCount() - 1)
        if not is_pair_boundary:
            return
        painter.save()
        pen = QtGui.QPen(QtGui.QColor("#5a5a5a"), 2)
        pen.setCosmetic(True)
        painter.setPen(pen)
        rect = option.rect
        painter.drawLine(rect.right(), rect.top(), rect.right(), rect.bottom())
        painter.restore()


class _VariableHeader(QtWidgets.QHeaderView):
    """Header with a bold separator after each 값 열."""

    def paintSection(self, painter: QtGui.QPainter, rect: QtCore.QRect, logicalIndex: int):
        super().paintSection(painter, rect, logicalIndex)
        model = self.model()
        if not model:
            return
        if (logicalIndex % 2 == 1) and (logicalIndex != model.columnCount() - 1):
            painter.save()
            pen = QtGui.QPen(QtGui.QColor("#5a5a5a"), 2)
            pen.setCosmetic(True)
            painter.setPen(pen)
            painter.drawLine(rect.right(), rect.top(), rect.right(), rect.bottom())
            painter.restore()


class ActionTreeWidget(QtWidgets.QTreeWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setHeaderLabels(["순번", "타입", "이름", "값", "설명", "활성"])
        self.header().setSectionResizeMode(QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        self.header().setSectionResizeMode(2, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        self.header().setSectionResizeMode(3, QtWidgets.QHeaderView.ResizeMode.Stretch)
        self.header().setSectionResizeMode(4, QtWidgets.QHeaderView.ResizeMode.Stretch)
        self.header().setSectionResizeMode(5, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        self.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectionBehavior.SelectRows)
        self.setSelectionMode(QtWidgets.QAbstractItemView.SelectionMode.ExtendedSelection)
        self.setDragEnabled(True)
        self.setAcceptDrops(True)
        self.setDropIndicatorShown(True)
        self.setDragDropMode(QtWidgets.QAbstractItemView.DragDropMode.InternalMove)
        self.setDefaultDropAction(QtCore.Qt.DropAction.MoveAction)
        self.setExpandsOnDoubleClick(False)
        self.setAlternatingRowColors(False)
        self.setUniformRowHeights(True)
        self._expander_size = 16
        self._expander_margin = 8
        self._expander_fill = QtGui.QColor("#f6f8fc")
        self._expander_stroke = QtGui.QColor("#d5dbe7")
        self._expander_arrow = QtGui.QColor("#4a5d82")
        self._type_indent = 18
        self.setIndentation(0)
        self.setItemDelegateForColumn(1, _TypeIndentDelegate(self))
        self.setItemDelegateForColumn(5, _DepthCheckDelegate(self))
        self.setMouseTracking(False)
        # 호버 시 기본 블루 하이라이트가 뜨지 않도록 hover 이벤트를 막는다.
        self.viewport().setAttribute(QtCore.Qt.WidgetAttribute.WA_Hover, False)
        # 기본 핸들은 숨기고 오른쪽에 커스텀 화살표를 그린다.
        self.setRootIsDecorated(False)
        self.setViewportMargins(0, 0, 0, 0)
        # 소프트한 선택색, 호버 제거 + 기본 화살표 제거
        self.setStyleSheet(
            "QTreeView::item:hover { background: transparent; }"
            "QTreeView::item:selected { background: #e8f2ff; color: palette(text); }"
            "QTreeView::item:selected:active { background: #e8f2ff; color: palette(text); }"
            "QTreeView::item:selected:!active { background: #e8f2ff; color: palette(text); }"
            "QTreeView::item:focus { outline: none; }"
            "QTreeView::item:selected:focus { outline: none; }"
            "QTreeView::branch:hover { background: transparent; }"
            "QTreeView::branch:selected { background: transparent; }"
            "QTreeView::branch { background: transparent; image: none; }"
        )
        # 호버 이벤트를 완전히 억제
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_Hover, False)
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_NoSystemBackground, False)
        self.setStyleSheet(
            self.styleSheet()
            + "QTreeView::item { background-clip: padding; }"
            + "QTreeView::item:selected:active { background: #e8f2ff; }"
            + "QTreeView::item:selected:!active { background: #e8f2ff; }"
            + "QTreeView::drop-indicator { height: 0px; border: 0px solid transparent; background: transparent; }"
        )
        pal = self.palette()
        pal.setColor(QtGui.QPalette.ColorRole.Highlight, QtGui.QColor("#e8f2ff"))
        pal.setColor(QtGui.QPalette.ColorRole.HighlightedText, pal.color(QtGui.QPalette.ColorRole.Text))
        self.setPalette(pal)
        self.setItemDelegate(_NoHoverDelegate(self))
        self._disabled_base_color = QtGui.QColor("#ffe8e8")
        self._disabled_text_color = QtGui.QColor("#9c5c5c")
        self._disabled_icon = self.style().standardIcon(QtWidgets.QStyle.StandardPixmap.SP_MessageBoxCritical)
        self._drop_feedback: dict | None = None
        self._drag_pixmap_mode: str | None = None
        self._drag_pixmap_cache: dict[str, QtGui.QPixmap] = {}
        self._active_drag: QtGui.QDrag | None = None
        self._child_hint_key: tuple[int, str] | None = None
        self._child_hint_time: float = 0.0
        self.itemChanged.connect(self._handle_item_changed)

    def _first_column_rect(self, index: QtCore.QModelIndex) -> QtCore.QRect:
        idx = index.sibling(index.row(), 1)
        return self.visualRect(idx)

    def _item_level(self, index: QtCore.QModelIndex) -> int:
        item = self.itemFromIndex(index)
        if not item:
            return 0
        data = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
        if data == "__else__" or (isinstance(data, dict) and data.get("marker") == "__elif__"):
            parent = item.parent()
            if parent:
                return self._item_level(self.indexFromItem(parent))
            return 0
        level = 0
        current = item
        while current:
            parent = current.parent()
            if not parent:
                break
            level += 1
            current = parent
        return level

    def _is_block_marker(self, data) -> bool:
        if isinstance(data, Action) and data.type in ("if", "group"):
            return True
        if data == "__else__":
            return True
        if isinstance(data, dict) and data.get("marker") == "__elif__":
            return True
        return False

    def _can_have_children_data(self, data) -> bool:
        if isinstance(data, Action) and data.type in ("if", "group"):
            return True
        if data == "__else__":
            return True
        if isinstance(data, dict) and data.get("marker") == "__elif__":
            return True
        return False

    def _can_have_children_item(self, item: QtWidgets.QTreeWidgetItem | None) -> bool:
        if not item:
            return False
        data = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
        return self._can_have_children_data(data)

    def _orig_text(self, item: QtWidgets.QTreeWidgetItem, col: int) -> str:
        """Cache original text so we can append markers without losing indentation alignment."""
        key = QtCore.Qt.ItemDataRole.UserRole + 5
        cached = item.data(col, key)
        if cached is None:
            cached = item.text(col)
            item.setData(col, key, cached)
        return str(cached)

    def _set_drop_enabled(self, item: QtWidgets.QTreeWidgetItem, enabled: bool):
        flags = item.flags()
        if enabled:
            flags |= QtCore.Qt.ItemFlag.ItemIsDropEnabled
        else:
            flags &= ~QtCore.Qt.ItemFlag.ItemIsDropEnabled
        item.setFlags(flags)

    def _block_root_index(self, index: QtCore.QModelIndex) -> QtCore.QModelIndex | None:
        current = index
        while current.isValid():
            item = self.itemFromIndex(current)
            if item and self._is_block_marker(item.data(0, QtCore.Qt.ItemDataRole.UserRole)):
                return current
            current = current.parent()
        return None

    def _expander_rect(self, rect: QtCore.QRect) -> QtCore.QRect:
        size = self._expander_size
        margin = self._expander_margin
        right = rect.right() - margin
        return QtCore.QRect(right - size, rect.center().y() - size // 2, size, size)

    def _draw_block_background(self, painter: QtGui.QPainter, option: QtWidgets.QStyleOptionViewItem, index: QtCore.QModelIndex):
        block_index = self._block_root_index(index)
        if not block_index:
            return
        is_header = block_index == index
        color = QtGui.QColor("#e9f2ff" if is_header else "#f7faff")
        color.setAlpha(150 if is_header else 110)
        painter.fillRect(option.rect, color)

    def _draw_indent_guides(self, painter: QtGui.QPainter, option: QtWidgets.QStyleOptionViewItem, index: QtCore.QModelIndex):
        level = self._item_level(index)
        if level <= 0:
            return
        type_rect = self.visualRect(index.sibling(index.row(), 1))
        indent = self._type_indent
        guide_color = QtGui.QColor("#c7d7f2")
        guide_color.setAlpha(180)
        pen = QtGui.QPen(guide_color, 1)
        painter.setPen(pen)
        for depth in range(1, level + 1):
            x = type_rect.left() + depth * indent - indent // 2
            painter.drawLine(x, option.rect.top(), x, option.rect.bottom())

    def _draw_expander(self, painter: QtGui.QPainter, option: QtWidgets.QStyleOptionViewItem, index: QtCore.QModelIndex):
        item = self.itemFromIndex(index)
        if not item or item.childCount() == 0:
            return
        rect = self._expander_rect(self._first_column_rect(index))
        painter.save()
        painter.setRenderHint(QtGui.QPainter.RenderHint.Antialiasing, True)
        fill = QtGui.QColor(self._expander_fill)
        fill.setAlpha(235)
        painter.setBrush(fill)
        stroke = QtGui.QPen(self._expander_stroke, 1.1)
        stroke.setCosmetic(True)
        painter.setPen(stroke)
        painter.drawRoundedRect(rect, 5, 5)
        arrow_pen = QtGui.QPen(self._expander_arrow, 2)
        arrow_pen.setCapStyle(QtCore.Qt.PenCapStyle.RoundCap)
        arrow_pen.setJoinStyle(QtCore.Qt.PenJoinStyle.RoundJoin)
        painter.setPen(arrow_pen)
        painter.setBrush(QtCore.Qt.BrushStyle.NoBrush)
        cx, cy = rect.center().x(), rect.center().y()
        if self.isExpanded(index):
            pts = [
                QtCore.QPointF(rect.left() + 4, cy - 1),
                QtCore.QPointF(cx, cy + 4),
                QtCore.QPointF(rect.right() - 4, cy - 1),
            ]
        else:
            pts = [
                QtCore.QPointF(rect.left() + 4, cy - 4),
                QtCore.QPointF(rect.right() - 5, cy),
                QtCore.QPointF(rect.left() + 4, cy + 4),
            ]
        painter.drawPolyline(QtGui.QPolygonF(pts))
        painter.restore()

    def _drag_pixmap_for_mode(self, mode: str) -> QtGui.QPixmap:
        if mode in self._drag_pixmap_cache:
            return self._drag_pixmap_cache[mode]
        color_map = {
            "sibling": "#2f7fff",
            "child": "#5aa5ff",
            "blocked": "#d64545",
        }
        base = QtGui.QColor(color_map.get(mode, "#2f7fff"))
        pm = QtGui.QPixmap(90, 26)
        pm.fill(QtCore.Qt.GlobalColor.transparent)
        painter = QtGui.QPainter(pm)
        painter.setRenderHint(QtGui.QPainter.RenderHint.Antialiasing, True)
        fill = QtGui.QColor(base)
        fill.setAlpha(90 if mode != "blocked" else 130)
        painter.setBrush(fill)
        pen = QtGui.QPen(base, 3)
        pen.setStyle(QtCore.Qt.PenStyle.DashLine if mode == "blocked" else QtCore.Qt.PenStyle.SolidLine)
        painter.setPen(pen)
        painter.drawRoundedRect(pm.rect().adjusted(1, 1, -1, -1), 7, 7)
        painter.end()
        self._drag_pixmap_cache[mode] = pm
        return pm

    def _update_drag_pixmap_mode(self, mode: str):
        if self._drag_pixmap_mode == mode:
            return
        self._drag_pixmap_mode = mode
        if self._active_drag:
            self._active_drag.setPixmap(self._drag_pixmap_for_mode(mode))

    def _clear_drop_feedback(self):
        if self._drop_feedback is not None:
            self._drop_feedback = None
            self.viewport().update()

    def _maybe_show_child_hint(self, item: QtWidgets.QTreeWidgetItem | None, mode: str):
        # 힌트 툴팁은 사용하지 않는다(시각 노이즈 제거).
        return

    def _is_drop_allowed(self, indicator: QtWidgets.QAbstractItemView.DropIndicatorPosition, target_item: QtWidgets.QTreeWidgetItem | None) -> bool:
        if indicator == QtWidgets.QAbstractItemView.DropIndicatorPosition.OnItem:
            return bool(target_item) and bool(target_item.flags() & QtCore.Qt.ItemFlag.ItemIsDropEnabled) and self._can_have_children_item(target_item)
        return True

    def _normalized_indicator(
        self,
        pos: QtCore.QPoint,
        indicator: QtWidgets.QAbstractItemView.DropIndicatorPosition,
        target_item: QtWidgets.QTreeWidgetItem | None,
    ) -> tuple[QtWidgets.QAbstractItemView.DropIndicatorPosition, bool]:
        """Return adjusted indicator and whether child drop is allowed."""
        allowed_child = self._is_drop_allowed(indicator, target_item)
        if indicator == QtWidgets.QAbstractItemView.DropIndicatorPosition.OnItem and not allowed_child:
            # fallback: treat as above/below depending on cursor position
            idx = self.indexAt(pos)
            row_rect = self.visualRect(idx) if idx.isValid() else QtCore.QRect()
            mid_y = row_rect.center().y() if not row_rect.isNull() else pos.y()
            indicator = (
                QtWidgets.QAbstractItemView.DropIndicatorPosition.AboveItem
                if pos.y() < mid_y
                else QtWidgets.QAbstractItemView.DropIndicatorPosition.BelowItem
            )
        return indicator, allowed_child

    def _update_drop_feedback(self, event: QtGui.QDragMoveEvent | QtGui.QDropEvent | QtGui.QDragEnterEvent | None):
        if event is None:
            self._clear_drop_feedback()
            return
        pos = event.position().toPoint() if hasattr(event, "position") else event.pos()
        indicator = self.dropIndicatorPosition()
        index = self.indexAt(pos)
        target_item = self.itemFromIndex(index) if index.isValid() else None
        indicator, allowed_child = self._normalized_indicator(pos, indicator, target_item)
        mode = "blocked"
        if indicator in (
            QtWidgets.QAbstractItemView.DropIndicatorPosition.AboveItem,
            QtWidgets.QAbstractItemView.DropIndicatorPosition.BelowItem,
        ):
            mode = "sibling"
        elif indicator == QtWidgets.QAbstractItemView.DropIndicatorPosition.OnItem:
            mode = "child"
        elif indicator == QtWidgets.QAbstractItemView.DropIndicatorPosition.OnViewport:
            mode = "sibling"
        self._drop_feedback = {
            "mode": mode,
            "indicator": indicator,
            "index": index if index.isValid() else None,
            "pos": pos,
            "level": self._item_level(index) if index.isValid() else 0,
        }
        self._update_drag_pixmap_mode(mode)
        self._maybe_show_child_hint(target_item, mode)
        self.viewport().update()

    def _paint_drop_feedback(self):
        if not self._drop_feedback:
            return
        painter = QtGui.QPainter(self.viewport())
        painter.setRenderHint(QtGui.QPainter.RenderHint.Antialiasing, True)
        info = self._drop_feedback
        mode = info.get("mode")
        indicator = info.get("indicator")
        pos: QtCore.QPoint = info.get("pos") or QtCore.QPoint()
        target_idx: QtCore.QModelIndex | None = info.get("index")
        view_rect = self.viewport().rect()
        if mode == "sibling" and isinstance(target_idx, QtCore.QModelIndex) and target_idx.isValid():
            row_rect = self.visualRect(target_idx)
            y = row_rect.top() if indicator == QtWidgets.QAbstractItemView.DropIndicatorPosition.AboveItem else row_rect.bottom()
            base_color = QtGui.QColor("#1f6bff")
            pen = QtGui.QPen(base_color, 8, QtCore.Qt.PenStyle.SolidLine, QtCore.Qt.PenCapStyle.RoundCap)
            painter.setPen(pen)
            left = row_rect.left() + 6
            right = row_rect.right() - 6
            painter.drawLine(left, y, right, y)
        elif mode == "child" and isinstance(target_idx, QtCore.QModelIndex) and target_idx.isValid():
            row_rect = self.visualRect(target_idx)
            type_idx = target_idx.sibling(target_idx.row(), 1)
            type_rect = self.visualRect(type_idx) if type_idx.isValid() else row_rect
            level = int(info.get("level", 0)) + 1
            indent = self._type_indent
            left_x = type_rect.left() + indent * level - indent // 2
            right_x = left_x + indent - 4
            left_x = max(view_rect.left() + 6, left_x)
            right_x = min(view_rect.right() - 6, right_x)
            top_y = row_rect.top() + 2
            bottom_y = row_rect.bottom() - 2
            pen = QtGui.QPen(QtGui.QColor("#2f7fff"), 4, QtCore.Qt.PenStyle.SolidLine, QtCore.Qt.PenCapStyle.RoundCap)
            painter.setPen(pen)
            painter.drawLine(left_x, top_y, left_x, bottom_y)
            painter.drawLine(right_x, top_y, right_x, bottom_y)
        else:
            y = pos.y()
            y = max(view_rect.top() + 4, min(view_rect.bottom() - 4, y))
            base_color = QtGui.QColor("#d64545")
            pen = QtGui.QPen(base_color, 3, QtCore.Qt.PenStyle.DashLine, QtCore.Qt.PenCapStyle.RoundCap)
            painter.setPen(pen)
            if isinstance(target_idx, QtCore.QModelIndex) and target_idx.isValid():
                row_rect = self.visualRect(target_idx)
                left = row_rect.left() + 6
                right = row_rect.right() - 6
            else:
                left = view_rect.left() + 6
                right = view_rect.right() - 6
            painter.drawLine(left, y, right, y)
        painter.end()

    def _disabled_depth(self, item: QtWidgets.QTreeWidgetItem) -> int | None:
        if not item:
            return None
        level = self._item_level(self.indexFromItem(item))
        current = item
        while current:
            data = current.data(0, QtCore.Qt.ItemDataRole.UserRole)
            is_disabled_holder = False
            if isinstance(data, Action) and current.checkState(5) != QtCore.Qt.CheckState.Checked:
                is_disabled_holder = True
            elif isinstance(data, dict) and data.get("marker") == "__elif__":
                is_disabled_holder = current.checkState(5) != QtCore.Qt.CheckState.Checked or data.get("enabled") is False
            if is_disabled_holder:
                ancestor_level = self._item_level(self.indexFromItem(current))
                return max(0, level - ancestor_level)
            current = current.parent()
        return None

    def _disabled_overlay_color(self, depth: int) -> QtGui.QColor:
        color = QtGui.QColor(self._disabled_base_color)
        alpha = max(70, 200 - min(depth, 6) * 18)
        color.setAlpha(alpha)
        return color

    def _disabled_text_brush(self, depth: int) -> QtGui.QBrush:
        color = QtGui.QColor(self._disabled_text_color)
        color = color.lighter(100 + min(depth, 6) * 8)
        return QtGui.QBrush(color)

    def _apply_enabled_styles(self):
        default_brush = QtGui.QBrush(self.palette().color(QtGui.QPalette.ColorRole.Text))
        stack: list[QtWidgets.QTreeWidgetItem | None] = [self.topLevelItem(i) for i in range(self.topLevelItemCount())]
        while stack:
            item = stack.pop()
            if item is None:
                continue
            data = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
            disabled_depth = self._disabled_depth(item)
            if disabled_depth is not None:
                brush = self._disabled_text_brush(disabled_depth)
                for col in range(item.columnCount()):
                    item.setForeground(col, brush)
                base_type = self._orig_text(item, 1)
                if base_type:
                    item.setText(1, f"{base_type} ✕")
                item.setIcon(1, QtGui.QIcon())
            else:
                base_type = self._orig_text(item, 1)
                item.setText(1, base_type)
                if isinstance(data, Action):
                    self._apply_once_style(item, data)
                else:
                    for col in range(item.columnCount()):
                        item.setForeground(col, default_brush)
                item.setIcon(1, QtGui.QIcon())
            for i in range(item.childCount()):
                stack.append(item.child(i))

    def _collapse_branch(self, item: QtWidgets.QTreeWidgetItem | None):
        if not item:
            return
        idx = self.indexFromItem(item)
        if idx.isValid():
            self.setExpanded(idx, False)
        for i in range(item.childCount()):
            self._collapse_branch(item.child(i))

    def _handle_item_changed(self, item: QtWidgets.QTreeWidgetItem, column: int):
        if column != 5:
            return
        data = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
        is_checked = item.checkState(5) == QtCore.Qt.CheckState.Checked
        if not is_checked:
            # 비활성화 시에는 해당 노드를 접어서 시각적으로 숨긴다.
            self._collapse_branch(item)
        if isinstance(data, Action):
            data.enabled = is_checked
        elif isinstance(data, dict) and data.get("marker") == "__elif__":
            data["enabled"] = is_checked
            cond = data.get("condition")
            try:
                setattr(cond, "enabled", is_checked)
            except Exception:
                pass
        if is_checked:
            self.expandItem(item)
        self._apply_enabled_styles()
        self.viewport().update()

    def _draw_disabled_overlay(self, painter: QtGui.QPainter, option: QtWidgets.QStyleOptionViewItem, index: QtCore.QModelIndex):
        item = self.itemFromIndex(index)
        if not item:
            return
        depth = self._disabled_depth(item)
        if depth is None:
            return
        painter.fillRect(option.rect, self._disabled_overlay_color(depth))

    def drawRow(self, painter: QtGui.QPainter, option: QtWidgets.QStyleOptionViewItem, index: QtCore.QModelIndex):
        painter.save()
        self._draw_block_background(painter, option, index)
        painter.restore()

        opt = QtWidgets.QStyleOptionViewItem(option)
        # 마우스 호버/포커스가 체크박스 영역을 덮지 않도록 제거 (Qt6 호환)
        try:
            hover_flag = QtWidgets.QStyle.StateFlag.State_MouseOver  # Qt6
            focus_flag = QtWidgets.QStyle.StateFlag.State_HasFocus
        except AttributeError:
            hover_flag = QtWidgets.QStyle.State_MouseOver  # Qt5 fallback
            focus_flag = QtWidgets.QStyle.State_HasFocus
        opt.state &= ~hover_flag
        opt.state &= ~focus_flag
        super().drawRow(painter, opt, index)

        painter.save()
        self._draw_disabled_overlay(painter, option, index)
        self._draw_indent_guides(painter, option, index)
        self._draw_expander(painter, option, index)
        painter.restore()

    def paintEvent(self, event: QtGui.QPaintEvent):
        super().paintEvent(event)
        self._paint_drop_feedback()

    def _drag_default_action(self) -> QtCore.Qt.DropAction:
        modifiers = QtWidgets.QApplication.keyboardModifiers()
        return QtCore.Qt.DropAction.CopyAction if modifiers & QtCore.Qt.KeyboardModifier.AltModifier else QtCore.Qt.DropAction.MoveAction

    def dragEnterEvent(self, event: QtGui.QDragEnterEvent):
        event.setDropAction(self._drag_default_action())
        super().dragEnterEvent(event)
        self._update_drop_feedback(event)

    def startDrag(self, supported_actions: QtCore.Qt.DropActions):
        indexes = self.selectedIndexes()
        if not indexes:
            return
        drag = QtGui.QDrag(self)
        self._active_drag = drag
        drag.setPixmap(self._drag_pixmap_for_mode("sibling"))
        drag.setMimeData(self.model().mimeData(indexes))
        drag.exec(QtCore.Qt.DropAction.CopyAction | QtCore.Qt.DropAction.MoveAction, self._drag_default_action())
        self._active_drag = None
        self._drag_pixmap_mode = None
        self._clear_drop_feedback()

    def dragMoveEvent(self, event: QtGui.QDragMoveEvent):
        event.setDropAction(self._drag_default_action())
        super().dragMoveEvent(event)
        self._update_drop_feedback(event)

    def dragLeaveEvent(self, event: QtGui.QDragLeaveEvent):
        super().dragLeaveEvent(event)
        self._clear_drop_feedback()

    def mousePressEvent(self, event: QtGui.QMouseEvent):
        pos = event.position().toPoint() if hasattr(event, "position") else event.pos()
        index = self.indexAt(pos)
        if index.isValid():
            base_idx = self.model().index(index.row(), 0, index.parent())
            first_idx = index.sibling(index.row(), 1) if index.sibling(index.row(), 1).isValid() else index
            first_rect = self.visualRect(first_idx)
            hit_rect = self._expander_rect(first_rect).adjusted(-5, -4, 5, 4)
            row_rect = self.visualRect(first_idx)
            side_hit = QtCore.QRect(first_rect.left() - self._type_indent, row_rect.top(), self._type_indent * 2, row_rect.height())
            item = self.itemFromIndex(index)
            if item and item.childCount() > 0:
                if hit_rect.contains(pos) or side_hit.contains(pos):
                    self.setExpanded(base_idx, not self.isExpanded(base_idx))
                    event.accept()
                    return
            # 체크박스 클릭 지원: 체크 컬럼 영역을 클릭하면 토글
            check_idx = index.sibling(index.row(), 5)
            if check_idx.isValid():
                check_rect = self.visualRect(check_idx)
                margin = 6
                check_hit = check_rect.adjusted(-margin, -margin, margin, margin)
                if check_hit.contains(pos):
                    current_state = item.checkState(5)
                    new_state = QtCore.Qt.CheckState.Unchecked if current_state == QtCore.Qt.CheckState.Checked else QtCore.Qt.CheckState.Checked
                    item.setCheckState(5, new_state)
                    act = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
                    if isinstance(act, Action):
                        act.enabled = new_state == QtCore.Qt.CheckState.Checked
                        self._apply_once_style(item, act)
                    self.renumber()
                    event.accept()
                    return
        super().mousePressEvent(event)

    def _format_value(self, act: Action) -> str:
        suffix = " (1회)" if getattr(act, "once_per_macro", False) else ""
        if act.type in ("press", "down", "up"):
            rep = max(1, int(getattr(act, "repeat", 1) or 1))
            rep_txt = f" ({rep}회)" if rep > 1 else ""
            key_text = getattr(act, "key_raw", None) or act.key or ""
            return key_text + rep_txt + suffix
        if act.type in ("mouse_click", "mouse_down", "mouse_up", "mouse_move"):
            rep = max(1, int(getattr(act, "repeat", 1) or 1))
            rep_txt = f" ({rep}회)" if rep > 1 else ""
            btn = getattr(act, "mouse_button", None) or getattr(act, "key", "") or "mouse1"
            pos_txt = ""
            if getattr(act, "mouse_pos_raw", None):
                pos_txt = f" @{act.mouse_pos_raw}"
            elif getattr(act, "mouse_pos", None):
                x, y = act.mouse_pos
                pos_txt = f" @{x},{y}"
            prefix = "move" if act.type == "mouse_move" else btn
            value = prefix + rep_txt
            if pos_txt:
                value += pos_txt
            return value + suffix
        if act.type == "sleep":
            return act.sleep_value_text() + suffix
        if act.type == "if":
            base = ""
            if getattr(act, "elif_blocks", []):
                base = f"+{len(act.elif_blocks)} ELIF"
            return (base + suffix).strip()
        if act.type == "set_var":
            val = act.var_value_raw or act.var_value or ""
            name = act.var_name or ""
            return f"{name}={val}".strip() + suffix
        if act.type == "goto":
            return (act.goto_label or act.label or "") + suffix
        if act.type == "label":
            return (act.label or "") + suffix
        if act.type == "pixel_get":
            region_text = act.pixel_region_raw or (
                ",".join(str(v) for v in act.pixel_region) if act.pixel_region else ""
            )
            return f"{region_text} -> {act.pixel_target or ''}".strip() + suffix
        if act.type == "group":
            mode = act.group_mode or "all"
            if mode == "repeat_n":
                rep = getattr(act, "group_repeat", None)
                rep_txt = f" ({rep}회)" if rep else ""
                return mode + rep_txt + suffix
            return mode + suffix
        if act.type == "timer":
            slot = act.timer_index or "?"
            value = act.timer_value if act.timer_value is not None else "?"
            if isinstance(value, (int, float)):
                val_text = f"{float(value):.3f}".rstrip("0").rstrip(".")
            else:
                val_text = str(value)
            return f"타이머{slot}={val_text}초" + suffix
        return suffix.strip()

    def _format_desc(self, act: Action) -> str:
        return getattr(act, "description", "") or ""

    def _apply_once_style(self, item: QtWidgets.QTreeWidgetItem, act: Action):
        """색상으로 1회 실행 액션을 표시."""
        default_brush = QtGui.QBrush(self.palette().color(QtGui.QPalette.ColorRole.Text))
        once_brush = QtGui.QBrush(QtGui.QColor("#1f6feb"))
        brush = once_brush if getattr(act, "once_per_macro", False) else default_brush
        for col in range(item.columnCount()):
            item.setForeground(col, brush)

    def _append_action_item(self, act: Action, parent_item=None, insert_row: int | None = None):
        label = act.type
        item = QtWidgets.QTreeWidgetItem(
            ["", label, getattr(act, "name", "") or "", self._format_value(act), self._format_desc(act), ""]
        )
        item.setData(0, QtCore.Qt.ItemDataRole.UserRole, act)
        flags = (
            QtCore.Qt.ItemFlag.ItemIsDragEnabled
            | QtCore.Qt.ItemFlag.ItemIsEnabled
            | QtCore.Qt.ItemFlag.ItemIsSelectable
            | QtCore.Qt.ItemFlag.ItemIsUserCheckable
        )
        item.setFlags(flags)
        self._set_drop_enabled(item, self._can_have_children_data(act))
        state = QtCore.Qt.CheckState.Checked if getattr(act, "enabled", True) else QtCore.Qt.CheckState.Unchecked
        item.setCheckState(5, state)
        self._apply_once_style(item, act)
        if parent_item is None:
            if insert_row is None or insert_row < 0 or insert_row > self.topLevelItemCount():
                self.addTopLevelItem(item)
            else:
                self.insertTopLevelItem(insert_row, item)
        else:
            if insert_row is None or insert_row < 0 or insert_row > parent_item.childCount():
                parent_item.addChild(item)
            else:
                parent_item.insertChild(insert_row, item)

        if act.type == "if":
            for child in act.actions:
                self._append_action_item(child, item)
            for econd, eacts in getattr(act, "elif_blocks", []):
                elif_header = self._create_elif_header(item, econd)
                for child in eacts:
                    self._append_action_item(child, elif_header)
            if act.else_actions:
                else_header = self._ensure_else_header(item, create_if_missing=True)
                for child in act.else_actions:
                    self._append_action_item(child, else_header)
        elif act.type == "group":
            for child in act.actions:
                self._append_action_item(child, item)
        return item

    def _insert_after(self, act: Action, after_item: QtWidgets.QTreeWidgetItem) -> QtWidgets.QTreeWidgetItem:
        parent = after_item.parent()
        if parent:
            row = parent.indexOfChild(after_item) + 1
            return self._append_action_item(act, parent, row)
        row = self.indexOfTopLevelItem(after_item) + 1
        return self._append_action_item(act, None, row)

    def _find_else_header(self, item: QtWidgets.QTreeWidgetItem) -> QtWidgets.QTreeWidgetItem | None:
        for i in range(item.childCount()):
            child = item.child(i)
            if child.data(0, QtCore.Qt.ItemDataRole.UserRole) == "__else__":
                return child
        return None

    def _ensure_else_header(self, item: QtWidgets.QTreeWidgetItem, *, create_if_missing: bool) -> QtWidgets.QTreeWidgetItem | None:
        found = self._find_else_header(item)
        if found or not create_if_missing:
            return found
        else_header = QtWidgets.QTreeWidgetItem(["", "ELSE", "", "", "", ""])
        else_header.setData(0, QtCore.Qt.ItemDataRole.UserRole, "__else__")
        else_header.setFlags(
            QtCore.Qt.ItemFlag.ItemIsEnabled | QtCore.Qt.ItemFlag.ItemIsSelectable | QtCore.Qt.ItemFlag.ItemIsDragEnabled
        )
        self._set_drop_enabled(else_header, True)
        item.addChild(else_header)
        return else_header

    def _create_elif_header(self, parent: QtWidgets.QTreeWidgetItem, cond: Condition, desc: str | None = None) -> QtWidgets.QTreeWidgetItem:
        enabled_flag = getattr(cond, "enabled", True)
        try:
            setattr(cond, "enabled", enabled_flag)
        except Exception:
            pass
        header = QtWidgets.QTreeWidgetItem(["", "ELIF", "", _condition_brief(cond), desc or "", ""])
        header.setData(0, QtCore.Qt.ItemDataRole.UserRole, {"marker": "__elif__", "condition": cond, "enabled": enabled_flag})
        header.setFlags(
            QtCore.Qt.ItemFlag.ItemIsEnabled
            | QtCore.Qt.ItemFlag.ItemIsSelectable
            | QtCore.Qt.ItemFlag.ItemIsDragEnabled
            | QtCore.Qt.ItemFlag.ItemIsUserCheckable
        )
        self._set_drop_enabled(header, True)
        header.setCheckState(5, QtCore.Qt.CheckState.Checked if enabled_flag else QtCore.Qt.CheckState.Unchecked)
        else_header = self._find_else_header(parent)
        if else_header:
            idx = parent.indexOfChild(else_header)
            parent.insertChild(idx, header)
        else:
            parent.addChild(header)
        return header

    def remove_else_header(self, item: QtWidgets.QTreeWidgetItem):
        header = self._find_else_header(item)
        if header:
            idx = item.indexOfChild(header)
            item.takeChild(idx)
        self.renumber()

    def load_actions(self, actions: List[Action]):
        # Block signals/repaints during bulk load to avoid per-item itemChanged churn.
        prev_block = self.blockSignals(True)
        self.setUpdatesEnabled(False)
        try:
            self.clear()
            for act in actions:
                self._append_action_item(act)
            self.expandAll()
            self.renumber()
        finally:
            self.setUpdatesEnabled(True)
            self.blockSignals(prev_block)
            self.viewport().update()

    def collapse_all(self, checked: bool = False):
        """모든 노드를 접는다(버튼에서 bool 시그널을 받아도 허용)."""
        self.setUpdatesEnabled(False)
        super().collapseAll()
        self.setUpdatesEnabled(True)
        self.viewport().update()

    def renumber(self):
        counter = 1
        stack: list[QtWidgets.QTreeWidgetItem | None] = [
            self.topLevelItem(i) for i in reversed(range(self.topLevelItemCount()))
        ]
        while stack:
            item = stack.pop()
            if item is None:
                continue
            item.setText(0, str(counter))
            counter += 1
            for i in reversed(range(item.childCount())):
                stack.append(item.child(i))
        self._apply_enabled_styles()

    def _is_descendant(self, item: QtWidgets.QTreeWidgetItem, ancestor: QtWidgets.QTreeWidgetItem) -> bool:
        parent = item.parent()
        while parent:
            if parent is ancestor:
                return True
            parent = parent.parent()
        return False

    def _item_path_key(self, item: QtWidgets.QTreeWidgetItem) -> tuple[int, ...]:
        path: list[int] = []
        current = item
        while current:
            parent = current.parent()
            row = parent.indexOfChild(current) if parent else self.indexOfTopLevelItem(current)
            path.append(row)
            current = parent
        return tuple(reversed(path))

    def _top_level_selected(self, items: List[QtWidgets.QTreeWidgetItem]) -> List[QtWidgets.QTreeWidgetItem]:
        result: List[QtWidgets.QTreeWidgetItem] = []
        for it in items:
            if any(self._is_descendant(it, other) for other in items if other is not it):
                continue
            result.append(it)
        return sorted(result, key=self._item_path_key)

    def _expanded_keys(self) -> set[tuple[int, ...]]:
        keys: set[tuple[int, ...]] = set()

        def walk(item: QtWidgets.QTreeWidgetItem):
            key = self._item_path_key(item)
            idx = self.indexFromItem(item)
            if idx.isValid() and self.isExpanded(idx):
                keys.add(key)
            for i in range(item.childCount()):
                walk(item.child(i))

        for i in range(self.topLevelItemCount()):
            walk(self.topLevelItem(i))
        return keys

    def _restore_expanded(self, keys: set[tuple[int, ...]]):
        def walk(item: QtWidgets.QTreeWidgetItem):
            key = self._item_path_key(item)
            idx = self.indexFromItem(item)
            if idx.isValid():
                self.setExpanded(idx, key in keys)
            for i in range(item.childCount()):
                walk(item.child(i))

        for i in range(self.topLevelItemCount()):
            walk(self.topLevelItem(i))

    def move_selected_within_parent(self, offset: int) -> tuple[bool, str | None, QtWidgets.QTreeWidgetItem | None]:
        items = self._top_level_selected(self.selectedItems())
        if not items:
            return False, "이동할 항목을 선택하세요.", None
        primary = items[0]
        parent = primary.parent()
        if any(it.parent() is not parent for it in items):
            return False, "같은 부모를 가진 항목만 이동합니다.", primary
        current_row = parent.indexOfChild(primary) if parent else self.indexOfTopLevelItem(primary)
        sibling_count = parent.childCount() if parent else self.topLevelItemCount()
        target_row = current_row + offset
        if target_row < 0 or target_row >= sibling_count:
            return False, "같은 부모 안에서만 한 칸 이동할 수 있습니다.", primary
        expanded = self._expanded_keys()
        if parent:
            parent.takeChild(current_row)
            parent.insertChild(target_row, primary)
            if primary.parent() is not parent:
                # 안전장치: 잘못 부모가 바뀌면 원래 부모로 되돌림
                try:
                    current_parent = primary.parent()
                    if current_parent:
                        current_parent.takeChild(current_parent.indexOfChild(primary))
                except Exception:
                    pass
                parent.insertChild(target_row, primary)
        else:
            self.takeTopLevelItem(current_row)
            self.insertTopLevelItem(target_row, primary)
            if primary.parent() is not None:
                # 부모가 생겨버렸다면 떼어내고 다시 최상위에 삽입
                p = primary.parent()
                if p:
                    p.takeChild(p.indexOfChild(primary))
                self.insertTopLevelItem(target_row, primary)
        self._restore_expanded(expanded)
        primary.setSelected(True)
        self.setCurrentItem(primary)
        self.scrollToItem(primary)
        self.renumber()
        return True, None, primary

    def _clone_tree_item(self, item: QtWidgets.QTreeWidgetItem) -> QtWidgets.QTreeWidgetItem:
        clone = QtWidgets.QTreeWidgetItem([item.text(col) for col in range(item.columnCount())])
        clone_data = copy.deepcopy(item.data(0, QtCore.Qt.ItemDataRole.UserRole))
        clone.setData(0, QtCore.Qt.ItemDataRole.UserRole, clone_data)
        clone.setFlags(item.flags())
        self._set_drop_enabled(clone, self._can_have_children_data(clone_data))
        clone.setCheckState(5, item.checkState(5))
        for col in range(item.columnCount()):
            clone.setForeground(col, item.foreground(col))
        for idx in range(item.childCount()):
            clone.addChild(self._clone_tree_item(item.child(idx)))
        return clone

    def dropEvent(self, event: QtGui.QDropEvent):
        modifiers = QtWidgets.QApplication.keyboardModifiers()
        pos = event.position().toPoint() if hasattr(event, "position") else event.pos()
        target = self.itemAt(pos)
        indicator = self.dropIndicatorPosition()
        indicator, allowed_child = self._normalized_indicator(pos, indicator, target)
        if modifiers & QtCore.Qt.KeyboardModifier.AltModifier and event.source() in (self, self.viewport()):
            selected = self._top_level_selected(self.selectedItems())
            if not selected:
                event.ignore()
                return
            if target is None and indicator != QtWidgets.QAbstractItemView.DropIndicatorPosition.OnViewport:
                indicator = QtWidgets.QAbstractItemView.DropIndicatorPosition.OnViewport
            parent = None
            insert_row = -1
            if indicator == QtWidgets.QAbstractItemView.DropIndicatorPosition.BelowItem:
                parent = target.parent()
                insert_row = (parent.indexOfChild(target) + 1) if parent else (self.indexOfTopLevelItem(target) + 1)
            elif indicator == QtWidgets.QAbstractItemView.DropIndicatorPosition.AboveItem:
                parent = target.parent()
                insert_row = parent.indexOfChild(target) if parent else self.indexOfTopLevelItem(target)
            elif indicator == QtWidgets.QAbstractItemView.DropIndicatorPosition.OnItem:
                parent = target
                insert_row = parent.childCount()
            else:  # OnViewport
                parent = None
                insert_row = self.topLevelItemCount()

            new_items: list[QtWidgets.QTreeWidgetItem] = []
            for item in selected:
                clone = self._clone_tree_item(item)
                if parent:
                    parent.insertChild(insert_row, clone)
                else:
                    self.insertTopLevelItem(insert_row, clone)
                insert_row += 1
                new_items.append(clone)
                self.expandItem(clone)
            event.setDropAction(QtCore.Qt.DropAction.CopyAction)
            event.accept()
            self.clearSelection()
            for clone in new_items:
                clone.setSelected(True)
            if parent:
                self.expandItem(parent)
            self._clear_drop_feedback()
            return
        else:
            items = self._top_level_selected(self.selectedItems())
            if not items:
                self._clear_drop_feedback()
                return
            if target in items:
                self._clear_drop_feedback()
                return
            if indicator == QtWidgets.QAbstractItemView.DropIndicatorPosition.OnViewport:
                parent = None
                insert_row = self.topLevelItemCount()
            elif indicator == QtWidgets.QAbstractItemView.DropIndicatorPosition.OnItem and allowed_child:
                parent = target
                insert_row = parent.childCount()
            else:
                parent = target.parent() if target else None
                base_row = parent.indexOfChild(target) if parent and target else self.indexOfTopLevelItem(target) if target else -1
                insert_row = base_row
                if indicator == QtWidgets.QAbstractItemView.DropIndicatorPosition.BelowItem:
                    insert_row += 1
                if insert_row < 0:
                    insert_row = self.topLevelItemCount()
            expanded = self._expanded_keys()
            # detach selected items (reverse order to keep indices valid)
            for item in reversed(items):
                p = item.parent()
                if p:
                    p.takeChild(p.indexOfChild(item))
                else:
                    idx = self.indexOfTopLevelItem(item)
                    if idx >= 0:
                        self.takeTopLevelItem(idx)
            # insert in order
            for item in items:
                if parent:
                    parent.insertChild(insert_row, item)
                else:
                    self.insertTopLevelItem(insert_row, item)
                insert_row += 1
            self._restore_expanded(expanded)
            for item in items:
                item.setSelected(True)
            if items:
                self.setCurrentItem(items[0])
            self.renumber()
        self._clear_drop_feedback()

    def _action_from_item(self, item: QtWidgets.QTreeWidgetItem) -> Action | None:
        data = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
        if not isinstance(data, Action):
            return None
        act = copy.deepcopy(data)
        act.enabled = item.checkState(5) == QtCore.Qt.CheckState.Checked
        if act.type == "if" and isinstance(act.condition, Condition):
            try:
                act.condition.enabled = act.enabled
            except Exception:
                pass
        act.actions = []
        act.else_actions = []
        act.elif_blocks = []
        for idx in range(item.childCount()):
            child = item.child(idx)
            marker = child.data(0, QtCore.Qt.ItemDataRole.UserRole)
            if marker == "__else__":
                for j in range(child.childCount()):
                    child_action = self._action_from_item(child.child(j))
                    if child_action:
                        act.else_actions.append(child_action)
                continue
            if isinstance(marker, dict) and marker.get("marker") == "__elif__":
                cond = marker.get("condition")
                cond_enabled = child.checkState(5) == QtCore.Qt.CheckState.Checked
                if isinstance(cond, Condition):
                    try:
                        cond.enabled = cond_enabled
                    except Exception:
                        pass
                if isinstance(cond, Condition):
                    branch_actions: List[Action] = []
                    for j in range(child.childCount()):
                        child_action = self._action_from_item(child.child(j))
                        if child_action:
                            branch_actions.append(child_action)
                    act.elif_blocks.append((copy.deepcopy(cond), branch_actions))
                continue
            child_action = self._action_from_item(child)
            if child_action:
                act.actions.append(child_action)
        return act

    def collect_actions(self) -> List[Action]:
        actions: List[Action] = []
        for i in range(self.topLevelItemCount()):
            act = self._action_from_item(self.topLevelItem(i))
            if act:
                actions.append(act)
        return actions

    def selected_item(self) -> QtWidgets.QTreeWidgetItem | None:
        selected = self.selectionModel().selectedRows()
        if not selected:
            return None
        return self.itemFromIndex(selected[0])

    def selected_action(self) -> Action | None:
        item = self.selected_item()
        if not item:
            return None
        data = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
        return data if isinstance(data, Action) else None


class ActionEditDialog(QtWidgets.QDialog):
    def __init__(
        self,
        parent=None,
        action: Action | None = None,
        *,
        variable_provider=None,
        add_variable=None,
        label_provider=None,
        resolver: VariableResolver | None = None,
        start_pixel_test=None,
        start_condition_debug=None,
        stop_pixel_test=None,
        image_viewer_state: dict | None = None,
        save_image_viewer_state=None,
        open_screenshot_dialog=None,
        screenshot_hotkeys_provider=None,
        screenshot_manager=None,
    ):
        super().__init__(parent)
        self.setWindowTitle("액션 설정")
        self.setModal(False)
        self.setWindowModality(QtCore.Qt.WindowModality.NonModal)
        self.setWindowFlags(
            QtCore.Qt.WindowType.Window
            | QtCore.Qt.WindowType.WindowMinimizeButtonHint
            | QtCore.Qt.WindowType.WindowMaximizeButtonHint
            | QtCore.Qt.WindowType.WindowCloseButtonHint
        )
        self.resize(420, 360)
        self._variable_provider = variable_provider
        self._add_variable = add_variable
        self._label_provider = label_provider
        self._resolver = resolver
        self._start_pixel_test_fn = start_pixel_test
        self._start_condition_debug_fn = start_condition_debug
        self._stop_pixel_test_fn = stop_pixel_test
        self._image_viewer_state = image_viewer_state or {}
        self._save_image_viewer_state = save_image_viewer_state
        self._open_screenshot_dialog_fn = open_screenshot_dialog
        self._screenshot_hotkeys_provider = screenshot_hotkeys_provider
        self._screenshot_manager = screenshot_manager
        self._condition: Condition | None = None
        self._existing_children: List[Action] = []
        self._existing_else: List[Action] = []
        self._existing_elifs: List[tuple[Condition, List[Action]]] = []

        layout = QtWidgets.QVBoxLayout(self)

        form = QtWidgets.QFormLayout()
        self.type_combo = QtWidgets.QComboBox()
        for label, val in [
            ("탭 (press)", "press"),
            ("누르고 유지 (down)", "down"),
            ("떼기 (up)", "up"),
            ("마우스 클릭", "mouse_click"),
            ("마우스 누르기 (down)", "mouse_down"),
            ("마우스 떼기 (up)", "mouse_up"),
            ("마우스 이동", "mouse_move"),
            ("대기 (sleep)", "sleep"),
            ("변수 설정 (set_var)", "set_var"),
            ("타이머 설정 (timer)", "timer"),
            ("조건(if)", "if"),
            ("조건(elif)", "elif"),
            ("라벨(label)", "label"),
            ("점프(goto)", "goto"),
            ("반복/계속(continue)", "continue"),
            ("종료(return)", "return"),
            ("블록 탈출(break)", "break"),
            ("픽셀겟(pixel_get)", "pixel_get"),
            ("그룹(group)", "group"),
            ("Noop", "noop"),
        ]:
            self.type_combo.addItem(label, val)
        self.name_edit = QtWidgets.QLineEdit()
        self.enabled_check = QtWidgets.QCheckBox("활성")
        self.enabled_check.setChecked(True)
        self.enabled_check.setChecked(getattr(action, "enabled", True) if action else True)
        self.once_check = QtWidgets.QCheckBox("첫 사이클만 실행")
        self.key_edit = QtWidgets.QLineEdit()
        self.key_edit.setPlaceholderText("예: r / space / ctrl+shift+t")
        self.mouse_button_combo = QtWidgets.QComboBox()
        for label, val in [
            ("왼쪽 버튼 (mouse1)", "mouse1"),
            ("오른쪽 버튼 (mouse2)", "mouse2"),
            ("휠 버튼 (mouse3)", "mouse3"),
            ("X1 (mouse4)", "mouse4"),
            ("X2 (mouse5)", "mouse5"),
        ]:
            self.mouse_button_combo.addItem(label, val)
        self.mouse_pos_edit = QtWidgets.QLineEdit()
        self.mouse_pos_edit.setPlaceholderText("x,y (비우면 현재 위치)")
        self.sleep_edit = QtWidgets.QLineEdit("0")
        self.label_edit = QtWidgets.QLineEdit()
        self.goto_combo = QtWidgets.QComboBox()
        self.goto_combo.setEditable(False)
        self.goto_combo.setInsertPolicy(QtWidgets.QComboBox.InsertPolicy.NoInsert)
        self.goto_combo.setSizeAdjustPolicy(QtWidgets.QComboBox.SizeAdjustPolicy.AdjustToContents)
        self._refresh_goto_targets()
        _orig_show_popup = self.goto_combo.showPopup

        def _show_popup():
            self._refresh_goto_targets()
            _orig_show_popup()

        self.goto_combo.showPopup = _show_popup
        self.var_name_edit = QtWidgets.QLineEdit()
        self.var_value_edit = QtWidgets.QLineEdit()
        self.desc_edit = QtWidgets.QLineEdit()
        self.desc_edit.setPlaceholderText("액션 설명(선택)")
        self.region_edit = QtWidgets.QLineEdit("0,0,1,1")
        self.region_offset_edit = QtWidgets.QLineEdit("")
        self.region_edit.setPlaceholderText("기본 좌표: x,y(,w,h) 또는 /변수")
        self.region_offset_edit.setPlaceholderText("+dx,dy,dw,dh (선택)")
        self.repeat_edit = QtWidgets.QLineEdit("1")
        self.repeat_edit.setPlaceholderText("1 또는 1-3 (무작위)")
        self.repeat_edit.setToolTip("1 이상 반복 횟수 또는 범위(예: 1-3). 프레스/다운/업/마우스 입력에 적용.")
        self.pixel_target_edit = QtWidgets.QLineEdit("momo")
        self.group_mode_combo = QtWidgets.QComboBox()
        self.group_mode_combo.addItem("모두 실행", "all")
        self.group_mode_combo.addItem("첫 참만 실행", "first_true")
        self.group_mode_combo.addItem("첫 참 -> 다음 사이클", "first_true_continue")
        self.group_mode_combo.addItem("첫 참 -> 종료", "first_true_return")
        self.group_mode_combo.addItem("무한 반복 (break까지)", "while")
        self.group_mode_combo.addItem("N회 실행", "repeat_n")
        self.group_repeat_spin = QtWidgets.QSpinBox()
        self.group_repeat_spin.setRange(1, 999999)
        self.group_repeat_spin.setValue(1)
        self.group_repeat_spin.setSuffix(" 회")
        self.group_repeat_spin.setToolTip("그룹 children을 지정된 횟수만큼 실행합니다.")
        self.if_confirm_spin = QtWidgets.QSpinBox()
        self.if_confirm_spin.setRange(1, 10)
        self.if_confirm_spin.setValue(1)
        # 액션별 딜레이 오버라이드
        self.delay_override_group = QtWidgets.QGroupBox("키/마우스 입력 딜레이 오버라이드")
        delay_layout = QtWidgets.QGridLayout(self.delay_override_group)
        self.delay_override_check = QtWidgets.QCheckBox("이 액션만 다른 딜레이 사용")
        delay_layout.addWidget(self.delay_override_check, 0, 0, 1, 4)
        override_tip = "예: 40(고정) 또는 40-80(랜덤). ms 단위."
        self.override_press_edit = QtWidgets.QLineEdit("")
        self.override_press_edit.setPlaceholderText("기본 0ms(즉시) / 40 또는 40-80")
        self.override_press_edit.setToolTip(override_tip)
        self.override_gap_edit = QtWidgets.QLineEdit("")
        self.override_gap_edit.setPlaceholderText("기본 0ms(즉시) / 40 또는 40-80")
        self.override_gap_edit.setToolTip(override_tip)
        self.override_preset_btn = QtWidgets.QPushButton("휴먼 프리셋")
        self.override_preset_btn.setToolTip("누름 70-120ms, 키 사이 80-150ms")
        self.override_preset_btn.clicked.connect(self._set_override_preset)
        self.delay_override_check.toggled.connect(self._toggle_override_enabled)

        delay_layout.addWidget(QtWidgets.QLabel("누름→뗌 지연"), 1, 0)
        delay_layout.addWidget(self.override_press_edit, 1, 1)
        delay_layout.addWidget(QtWidgets.QLabel("키 사이 지연"), 2, 0)
        delay_layout.addWidget(self.override_gap_edit, 2, 1)
        delay_layout.addWidget(self.override_preset_btn, 1, 2, 2, 1)

        self._install_var_completer(self.sleep_edit, "sleep")
        self._install_var_completer(self.region_edit, "region")
        self._install_var_completer(self.var_value_edit, "var")
        self._install_var_completer(self.key_edit, "key")
        self._install_var_completer(self.mouse_pos_edit, "var")
        if callable(self._variable_provider):
            names = self._variable_provider("var")
            comp = QtWidgets.QCompleter(names, self.var_name_edit)
            comp.setCaseSensitivity(QtCore.Qt.CaseSensitivity.CaseInsensitive)
            comp.setFilterMode(QtCore.Qt.MatchFlag.MatchContains)
            self.var_name_edit.setCompleter(comp)
        self.cond_label = QtWidgets.QLabel("(조건 없음)")
        self.edit_cond_btn = QtWidgets.QPushButton("조건 편집")

        form.addRow("타입", self.type_combo)
        form.addRow("이름(선택)", self.name_edit)
        form.addRow("설명", self.desc_edit)
        form.addRow(self.enabled_check)
        form.addRow(self.once_check)
        form.addRow("키", self.key_edit)
        form.addRow("마우스 버튼", self.mouse_button_combo)
        form.addRow("마우스 좌표 x,y (선택)", self.mouse_pos_edit)
        form.addRow("반복 횟수", self.repeat_edit)
        form.addRow("Sleep(ms 또는 범위)", self.sleep_edit)
        form.addRow("라벨 이름", self.label_edit)
        form.addRow("점프 대상 라벨", self.goto_combo)
        form.addRow("변수 이름", self.var_name_edit)
        form.addRow("변수 값", self.var_value_edit)
        self.timer_slot_combo = QtWidgets.QComboBox()
        for i in range(1, 21):
            self.timer_slot_combo.addItem(f"타이머{i}", i)
        self.timer_value_spin = QtWidgets.QDoubleSpinBox()
        self.timer_value_spin.setRange(0.0, 999999.0)
        self.timer_value_spin.setDecimals(3)
        self.timer_value_spin.setSingleStep(0.1)
        self.timer_value_spin.setSuffix(" 초")
        form.addRow("타이머 슬롯(1~20)", self.timer_slot_combo)
        form.addRow("타이머 값(초)", self.timer_value_spin)
        form.addRow("픽셀 좌표 x,y,w,h", self.region_edit)
        form.addRow("추가 +dx,dy,dw,dh (선택)", self.region_offset_edit)
        form.addRow("픽셀 변수명", self.pixel_target_edit)
        form.addRow("그룹 모드", self.group_mode_combo)
        form.addRow("그룹 반복 횟수", self.group_repeat_spin)
        form.addRow("연속 실패(횟수)", self.if_confirm_spin)
        form.addRow("조건", self.cond_label)
        form.addRow(self.delay_override_group)
        layout.addLayout(form)
        self._form_layout = form

        btn_row = QtWidgets.QHBoxLayout()
        btn_row.addStretch()
        self.ok_btn = QtWidgets.QPushButton("확인")
        self.cancel_btn = QtWidgets.QPushButton("취소")
        btn_row.addWidget(self.edit_cond_btn)
        btn_row.addStretch()
        btn_row.addWidget(self.ok_btn)
        btn_row.addWidget(self.cancel_btn)
        layout.addLayout(btn_row)

        self.ok_btn.clicked.connect(self.accept)
        self.cancel_btn.clicked.connect(self.reject)
        self.edit_cond_btn.clicked.connect(self._edit_condition)
        self.type_combo.currentIndexChanged.connect(self._sync_fields)
        self.group_mode_combo.currentIndexChanged.connect(self._sync_fields)
        self._toggle_override_enabled()

        if action:
            self._load(action)
        else:
            self._sync_fields()

    def showEvent(self, event: QtGui.QShowEvent):
        super().showEvent(event)
        if self._current_type() == "goto":
            self._refresh_goto_targets()

    def _set_field_visible(self, widget: QtWidgets.QWidget, visible: bool):
        label = self._form_layout.labelForField(widget) if hasattr(self, "_form_layout") else None
        if label:
            label.setVisible(visible)
        widget.setVisible(visible)

    def _toggle_override_enabled(self):
        enabled = self.delay_override_check.isChecked()
        for w in (self.override_press_edit, self.override_gap_edit, self.override_preset_btn):
            w.setEnabled(enabled)

    def _set_override_preset(self):
        self.override_press_edit.setText("70-120")
        self.override_gap_edit.setText("80-150")

    def _install_var_completer(self, edit: QtWidgets.QLineEdit, category: str):
        if not self._variable_provider:
            return
        names = self._variable_provider(category) if callable(self._variable_provider) else []
        _attach_variable_completer(edit, names)

    def _refresh_goto_targets(self, preserve: str | None = None):
        current = preserve if preserve is not None else self.goto_combo.currentData()
        self.goto_combo.blockSignals(True)
        self.goto_combo.clear()
        self.goto_combo.addItem("라벨을 선택하세요", "")
        if not callable(self._label_provider):
            self.goto_combo.setCurrentIndex(0)
            self.goto_combo.blockSignals(False)
            return
        try:
            labels = self._label_provider() or []
        except Exception:
            labels = []
        uniq: list[str] = []
        for name in labels:
            if name and name not in uniq:
                uniq.append(name)
        current_idx = 0
        for name in uniq:
            self.goto_combo.addItem(name, name)
            if current and name == current:
                current_idx = self.goto_combo.count() - 1
        if current and current_idx == 0 and current not in uniq:
            self.goto_combo.addItem(f"{current} (삭제됨)", current)
            current_idx = self.goto_combo.count() - 1
        self.goto_combo.setCurrentIndex(current_idx)
        self.goto_combo.blockSignals(False)

    def _current_type(self) -> str:
        return self.type_combo.currentData()

    def _sync_fields(self):
        typ = self._current_type()
        mouse_types = ("mouse_click", "mouse_down", "mouse_up", "mouse_move")
        show_key = typ in ("press", "down", "up")
        show_mouse_btn = typ in ("mouse_click", "mouse_down", "mouse_up")
        show_mouse_pos = typ in mouse_types
        show_sleep = typ == "sleep"
        show_label = typ == "label"
        show_goto = typ == "goto"
        show_var = typ == "set_var"
        show_timer = typ == "timer"
        show_pixel_get = typ == "pixel_get"
        show_group = typ == "group"
        show_if = typ in ("if", "elif")
        show_override = typ in ("press", "down", "up") or typ in mouse_types
        show_repeat = typ in ("press", "down", "up") or typ in mouse_types
        show_group_repeat = show_group and self.group_mode_combo.currentData() == "repeat_n"

        self._set_field_visible(self.key_edit, show_key)
        self.key_edit.setEnabled(show_key)
        self._set_field_visible(self.mouse_button_combo, show_mouse_btn)
        self.mouse_button_combo.setEnabled(show_mouse_btn)
        self._set_field_visible(self.mouse_pos_edit, show_mouse_pos)
        self.mouse_pos_edit.setEnabled(show_mouse_pos)
        self._set_field_visible(self.repeat_edit, show_repeat)
        self.repeat_edit.setEnabled(show_repeat)
        self._set_field_visible(self.sleep_edit, show_sleep)
        self.sleep_edit.setEnabled(show_sleep)
        self._set_field_visible(self.label_edit, show_label)
        self.label_edit.setEnabled(show_label)
        if show_goto:
            self._refresh_goto_targets()
        self._set_field_visible(self.goto_combo, show_goto)
        self.goto_combo.setEnabled(show_goto)

        self._set_field_visible(self.var_name_edit, show_var)
        self._set_field_visible(self.var_value_edit, show_var)
        for w in (self.var_name_edit, self.var_value_edit):
            w.setEnabled(show_var)

        self._set_field_visible(self.timer_slot_combo, show_timer)
        self._set_field_visible(self.timer_value_spin, show_timer)
        for w in (self.timer_slot_combo, self.timer_value_spin):
            w.setEnabled(show_timer)

        self._set_field_visible(self.region_edit, show_pixel_get)
        self._set_field_visible(self.region_offset_edit, show_pixel_get)
        self._set_field_visible(self.pixel_target_edit, show_pixel_get)
        self.region_edit.setEnabled(show_pixel_get)
        self.region_offset_edit.setEnabled(show_pixel_get)
        self.pixel_target_edit.setEnabled(show_pixel_get)

        self._set_field_visible(self.group_mode_combo, show_group)
        self.group_mode_combo.setEnabled(show_group)
        self._set_field_visible(self.group_repeat_spin, show_group_repeat)
        self.group_repeat_spin.setEnabled(show_group_repeat)

        self._set_field_visible(self.if_confirm_spin, show_if)
        self.if_confirm_spin.setEnabled(show_if)
        self._set_field_visible(self.cond_label, show_if)
        self.cond_label.setEnabled(show_if)
        self.edit_cond_btn.setVisible(show_if)
        self.edit_cond_btn.setEnabled(show_if)
        self._set_field_visible(self.delay_override_group, show_override)
        self.delay_override_group.setEnabled(show_override)
        self._toggle_override_enabled()

    def _edit_condition(self):
        seed_cond = self._condition or Condition(type="pixel", region=(0, 0, 1, 1), color=(255, 0, 0), tolerance=0)
        macro_cond = MacroCondition(condition=copy.deepcopy(seed_cond), actions=[], else_actions=[])
        dlg = ConditionDialog(
            self,
            cond=macro_cond,
            variable_provider=self._variable_provider,
            resolver=self._resolver,
            open_debugger=self._start_pixel_test_fn,
            start_condition_debug=self._start_condition_debug_fn,
            image_viewer_state=self._image_viewer_state,
            save_image_viewer_state=self._save_image_viewer_state,
            open_screenshot_dialog=self._open_screenshot_dialog_fn,
            screenshot_hotkeys_provider=self._screenshot_hotkeys_provider,
            screenshot_manager=self._screenshot_manager,
        )
        if not _run_dialog_non_modal(dlg):
            return
        try:
            result = dlg.get_condition()
            self._condition = result.condition
            self.cond_label.setText(_condition_brief(self._condition))
        except Exception as exc:
            QtWidgets.QMessageBox.warning(self, "조건 오류", str(exc))

    def _load(self, act: Action):
        self.type_combo.setCurrentIndex(max(0, self.type_combo.findData(act.type)))
        self.name_edit.setText(act.name or "")
        self.desc_edit.setText(getattr(act, "description", "") or "")
        self.enabled_check.setChecked(getattr(act, "enabled", True))
        self.once_check.setChecked(getattr(act, "once_per_macro", False))
        self.key_edit.setText(getattr(act, "key_raw", None) or act.key or "")
        if getattr(act, "repeat_raw", None):
            self.repeat_edit.setText(str(act.repeat_raw))
        else:
            try:
                self.repeat_edit.setText(str(max(1, int(getattr(act, "repeat", 1) or 1))))
            except Exception:
                self.repeat_edit.setText("1")
        if act.type in ("mouse_click", "mouse_down", "mouse_up", "mouse_move"):
            btn_val = getattr(act, "mouse_button", None) or getattr(act, "key", None) or "mouse1"
            idx = self.mouse_button_combo.findData(btn_val)
            if idx >= 0:
                self.mouse_button_combo.setCurrentIndex(idx)
            pos_raw = getattr(act, "mouse_pos_raw", None)
            if pos_raw:
                self.mouse_pos_edit.setText(pos_raw)
            elif getattr(act, "mouse_pos", None):
                x, y = act.mouse_pos
                self.mouse_pos_edit.setText(f"{x},{y}")
            else:
                self.mouse_pos_edit.clear()
        self.sleep_edit.setText(act.sleep_value_text() if hasattr(act, "sleep_value_text") else "")
        self.label_edit.setText(act.label or "")
        self._refresh_goto_targets(act.goto_label or "")
        raw_region = act.pixel_region_raw or ",".join(str(v) for v in (act.pixel_region or []))
        base_txt, offset_txt = _split_region_offset(raw_region) if raw_region else ("", "")
        self.region_edit.setText(base_txt)
        self.region_offset_edit.setText(offset_txt)
        self.pixel_target_edit.setText(act.pixel_target or "")
        if act.group_mode:
            idx = self.group_mode_combo.findData(act.group_mode)
            if idx >= 0:
                self.group_mode_combo.setCurrentIndex(idx)
        try:
            self.group_repeat_spin.setValue(max(1, int(getattr(act, "group_repeat", 1) or 1)))
        except Exception:
            self.group_repeat_spin.setValue(1)
        if act.type in ("if", "elif"):
            try:
                self.if_confirm_spin.setValue(max(1, int(getattr(act, "confirm_fails", 1) or 1)))
            except Exception:
                self.if_confirm_spin.setValue(1)
            self._condition = copy.deepcopy(act.condition)
            self.cond_label.setText(_condition_brief(self._condition))
            self._existing_elifs = copy.deepcopy(getattr(act, "elif_blocks", []))
        else:
            self._existing_elifs = []
        if act.type == "set_var":
            self.var_name_edit.setText(act.var_name or "")
            self.var_value_edit.setText(act.var_value_raw or act.var_value or "")
        elif act.type == "timer":
            idx = self.timer_slot_combo.findData(getattr(act, "timer_index", 1))
            if idx >= 0:
                self.timer_slot_combo.setCurrentIndex(idx)
            self.timer_value_spin.setValue(max(0.0, float(getattr(act, "timer_value", 0) or 0)))
        self.delay_override_check.setChecked(getattr(act, "key_delay_override_enabled", False))
        override_cfg = getattr(act, "key_delay_override", None)
        if isinstance(override_cfg, KeyDelayConfig):
            press_txt = _delay_text_from_config(override_cfg, press=True)
            gap_txt = _delay_text_from_config(override_cfg, press=False)
            self.override_press_edit.setText("" if press_txt in ("0", "0-0") else press_txt)
            self.override_gap_edit.setText("" if gap_txt in ("0", "0-0") else gap_txt)
        self._toggle_override_enabled()
        self._existing_children = copy.deepcopy(getattr(act, "actions", []))
        self._existing_else = copy.deepcopy(getattr(act, "else_actions", []))
        self._sync_fields()

    def get_action(self) -> Action:
        typ = self._current_type()
        name = self.name_edit.text().strip() or None
        description = self.desc_edit.text().strip() or None
        enabled = self.enabled_check.isChecked()
        is_elif = typ == "elif"
        typ_for_build = "if" if is_elif else typ
        act = Action(type=typ_for_build, name=name, description=description, enabled=enabled, once_per_macro=self.once_check.isChecked())
        act.actions = copy.deepcopy(self._existing_children)
        act.else_actions = copy.deepcopy(self._existing_else)
        act.elif_blocks = copy.deepcopy(self._existing_elifs) if typ_for_build == "if" else []
        if typ in ("press", "down", "up"):
            key = self.key_edit.text().strip()
            if not key:
                raise ValueError("키를 입력하세요.")
            act.key = key
            act.key_raw = key
            repeat_txt = self.repeat_edit.text().strip() or "1"
            try:
                repeat_val, repeat_range, repeat_raw = Action.parse_repeat(repeat_txt)
            except Exception:
                raise ValueError("반복 횟수는 1 이상의 정수 또는 1-3 형식의 범위여야 합니다.")
            act.repeat = repeat_val
            act.repeat_range = repeat_range
            act.repeat_raw = repeat_raw
            act.key_delay_override_enabled = self.delay_override_check.isChecked()
            if act.key_delay_override_enabled:
                press_val, press_rand, press_min, press_max = _parse_delay_text(self.override_press_edit.text())
                gap_val, gap_rand, gap_min, gap_max = _parse_delay_text(self.override_gap_edit.text())
                act.key_delay_override = KeyDelayConfig(
                    press_delay_ms=press_val,
                    press_delay_random=press_rand,
                    press_delay_min_ms=press_min,
                    press_delay_max_ms=press_max,
                    gap_delay_ms=gap_val,
                    gap_delay_random=gap_rand,
                    gap_delay_min_ms=gap_min,
                    gap_delay_max_ms=gap_max,
                )
            else:
                act.key_delay_override = None
        elif typ in ("mouse_click", "mouse_down", "mouse_up", "mouse_move"):
            btn = self.mouse_button_combo.currentData() or "mouse1"
            act.mouse_button = btn
            pos_text = self.mouse_pos_edit.text().strip()
            if typ == "mouse_move" and not pos_text:
                raise ValueError("마우스 이동 좌표를 입력하세요.")
            if pos_text:
                act.mouse_pos_raw = pos_text
                act.mouse_pos = _parse_point(pos_text, resolver=self._resolver)
            repeat_txt = self.repeat_edit.text().strip() or "1"
            try:
                repeat_val, repeat_range, repeat_raw = Action.parse_repeat(repeat_txt)
            except Exception:
                raise ValueError("반복 횟수는 1 이상의 정수 또는 1-3 형식의 범위여야 합니다.")
            act.repeat = repeat_val
            act.repeat_range = repeat_range
            act.repeat_raw = repeat_raw
            act.key_delay_override_enabled = self.delay_override_check.isChecked()
            if act.key_delay_override_enabled:
                press_val, press_rand, press_min, press_max = _parse_delay_text(self.override_press_edit.text())
                gap_val, gap_rand, gap_min, gap_max = _parse_delay_text(self.override_gap_edit.text())
                act.key_delay_override = KeyDelayConfig(
                    press_delay_ms=press_val,
                    press_delay_random=press_rand,
                    press_delay_min_ms=press_min,
                    press_delay_max_ms=press_max,
                    gap_delay_ms=gap_val,
                    gap_delay_random=gap_rand,
                    gap_delay_min_ms=gap_min,
                    gap_delay_max_ms=gap_max,
                )
            else:
                act.key_delay_override = None
        elif typ == "sleep":
            act.sleep_raw = self.sleep_edit.text().strip()
            act.sleep_ms, act.sleep_range = Action.parse_sleep(
                self._resolver.resolve(act.sleep_raw, "sleep") if self._resolver and act.sleep_raw else act.sleep_raw
            )
        elif typ == "label":
            act.label = self.label_edit.text().strip() or None
        elif typ == "goto":
            goto_val = self.goto_combo.currentData() or None
            if not goto_val:
                raise ValueError("점프할 라벨을 선택하세요.")
            act.goto_label = str(goto_val).strip()
        elif typ == "set_var":
            var_name = self.var_name_edit.text().strip()
            if not var_name:
                raise ValueError("변수 이름을 입력하세요.")
            act.var_name = var_name
            act.var_value_raw = self.var_value_edit.text().strip()
            if self._add_variable:
                try:
                    self._add_variable("var", var_name, act.var_value_raw or "")
                except Exception:
                    pass
        elif typ == "timer":
            slot = int(self.timer_slot_combo.currentData() or 0)
            if slot < 1 or slot > 20:
                raise ValueError("타이머 슬롯은 1~20 사이여야 합니다.")
            act.timer_index = slot
            act.timer_value = float(self.timer_value_spin.value())
        elif typ == "pixel_get":
            region_raw = _compose_region_raw(self.region_edit.text(), self.region_offset_edit.text())
            if not region_raw:
                raise ValueError("픽셀 좌표를 입력하세요.")
            act.pixel_region_raw = region_raw
            act.pixel_region = _parse_region(region_raw, resolver=self._resolver)
            act.pixel_target = self.pixel_target_edit.text().strip() or "pixel"
            existing = self._variable_provider("color") if self._variable_provider else []
            if act.pixel_target not in (existing or []):
                res = QtWidgets.QMessageBox.question(
                    self,
                    "새 색상 변수 추가",
                    f"색상 변수 '{act.pixel_target}'이 없습니다. 추가할까요?",
                )
                if res != QtWidgets.QMessageBox.StandardButton.Yes:
                    raise ValueError("색상 변수를 추가하지 않아 취소했습니다.")
                if self._add_variable and not self._add_variable("color", act.pixel_target, "000000"):
                    raise ValueError("색상 변수를 추가하지 못했습니다.")
        elif typ == "group":
            act.group_mode = self.group_mode_combo.currentData()
            if act.group_mode == "repeat_n":
                act.group_repeat = max(1, int(self.group_repeat_spin.value()))
            else:
                act.group_repeat = None
        elif typ_for_build == "if":
            if not self._condition:
                raise ValueError("조건을 설정하세요.")
            act.condition = copy.deepcopy(self._condition)
            act.confirm_fails = max(1, int(self.if_confirm_spin.value()))
            if is_elif:
                setattr(act, "_as_elif", True)
        return act


class AppScopeDialog(QtWidgets.QDialog):
    def __init__(self, parent=None, *, scope: str = "global", targets=None, apply_all_cb=None):
        super().__init__(parent)
        self.setWindowTitle("앱 동작 범위 설정")
        self.setModal(True)
        self.resize(520, 420)
        self._apply_all_cb = apply_all_cb

        layout = QtWidgets.QVBoxLayout(self)

        form = QtWidgets.QFormLayout()
        self.scope_combo = QtWidgets.QComboBox()
        self.scope_combo.addItem("전역 (어디서나)", "global")
        self.scope_combo.addItem("특정 앱에서만", "app")
        form.addRow("동작 범위", self.scope_combo)

        self.app_target_group = QtWidgets.QGroupBox("특정 앱 선택 (scope=특정 앱일 때만 적용)")
        target_layout = QtWidgets.QVBoxLayout(self.app_target_group)

        proc_row = QtWidgets.QHBoxLayout()
        self.process_combo = QtWidgets.QComboBox()
        self.process_combo.setMinimumContentsLength(25)
        self.process_combo.setSizeAdjustPolicy(QtWidgets.QComboBox.SizeAdjustPolicy.AdjustToContents)
        self.process_refresh_btn = QtWidgets.QToolButton()
        self.process_refresh_btn.setText("새로고침")
        self.process_add_btn = QtWidgets.QToolButton()
        self.process_add_btn.setText("추가")
        proc_row.addWidget(self.process_combo, stretch=1)
        proc_row.addWidget(self.process_refresh_btn)
        proc_row.addWidget(self.process_add_btn)
        target_layout.addLayout(proc_row)

        file_row = QtWidgets.QHBoxLayout()
        self.process_pick_btn = QtWidgets.QPushButton("EXE 선택...")
        self.process_active_btn = QtWidgets.QPushButton("현재 활성 창 추가")
        self.process_remove_btn = QtWidgets.QPushButton("선택 삭제")
        file_row.addWidget(self.process_pick_btn)
        file_row.addWidget(self.process_active_btn)
        file_row.addWidget(self.process_remove_btn)
        file_row.addStretch()
        target_layout.addLayout(file_row)

        self.app_target_list = QtWidgets.QListWidget()
        self.app_target_list.setSelectionMode(QtWidgets.QAbstractItemView.SelectionMode.ExtendedSelection)
        target_layout.addWidget(self.app_target_list)

        layout.addLayout(form)
        layout.addWidget(self.app_target_group)

        btn_row = QtWidgets.QHBoxLayout()
        btn_row.addStretch()
        self.apply_all_btn = QtWidgets.QPushButton("모든 매크로에 적용")
        self.ok_btn = QtWidgets.QPushButton("확인")
        self.cancel_btn = QtWidgets.QPushButton("취소")
        self.apply_all_btn.setEnabled(bool(apply_all_cb))
        btn_row.addWidget(self.apply_all_btn)
        btn_row.addWidget(self.ok_btn)
        btn_row.addWidget(self.cancel_btn)
        layout.addLayout(btn_row)

        self.ok_btn.clicked.connect(self.accept)
        self.cancel_btn.clicked.connect(self.reject)
        self.scope_combo.currentIndexChanged.connect(self._update_scope_ui)
        self.process_refresh_btn.clicked.connect(self._refresh_process_list)
        self.process_add_btn.clicked.connect(self._add_selected_process)
        self.process_pick_btn.clicked.connect(self._pick_process_file)
        self.process_active_btn.clicked.connect(self._add_active_process)
        self.process_remove_btn.clicked.connect(self._remove_selected_targets)
        self.apply_all_btn.clicked.connect(self._apply_all)

        self._set_target_list(targets or [])
        idx = self.scope_combo.findData(scope or "global")
        self.scope_combo.setCurrentIndex(idx if idx >= 0 else 0)
        self._update_scope_ui()
        self._refresh_process_list()

    def _apply_all(self):
        if not self._apply_all_cb:
            return
        self._apply_all_cb(self.selected_scope(), self.selected_targets())
        QtWidgets.QMessageBox.information(self, "적용 완료", "모든 매크로에 적용되었습니다.")

    def _target_key(self, name: str | None, path: str | None) -> str:
        if path:
            try:
                return Path(path).resolve().as_posix().lower()
            except Exception:
                return str(path).lower()
        return (name or "").strip().lower()

    def _format_process_label(self, info: dict) -> str:
        name = info.get("name") or "(알 수 없음)"
        pid = info.get("pid")
        path = info.get("path") or ""
        bits = [name]
        if pid is not None:
            bits.append(f"PID {pid}")
        if path:
            bits.append(path)
        return " | ".join(bits)

    def _refresh_process_list(self):
        self.process_combo.clear()
        try:
            infos = list_processes(max_count=200)
        except Exception:
            infos = []
        if not infos:
            self.process_combo.addItem("실행 중인 프로세스를 찾을 수 없습니다.", None)
            self.process_combo.setEnabled(False)
            return
        self.process_combo.setEnabled(True)
        for info in infos:
            self.process_combo.addItem(self._format_process_label(info), info)

    def _add_target_entry(self, name: str | None, path: str | None):
        key = self._target_key(name, path)
        if not key:
            return
        for idx in range(self.app_target_list.count()):
            item = self.app_target_list.item(idx)
            data = item.data(QtCore.Qt.ItemDataRole.UserRole) if item else None
            if isinstance(data, dict):
                existing = self._target_key(data.get("name"), data.get("path"))
                if existing == key:
                    return
        label_parts = [name or (Path(path).name if path else key)]
        if path:
            label_parts.append(path)
        item = QtWidgets.QListWidgetItem(" | ".join(part for part in label_parts if part))
        item.setData(QtCore.Qt.ItemDataRole.UserRole, {"name": name, "path": path})
        self.app_target_list.addItem(item)

    def _remove_selected_targets(self):
        for item in self.app_target_list.selectedItems():
            row = self.app_target_list.row(item)
            self.app_target_list.takeItem(row)

    def _set_target_list(self, targets):
        self.app_target_list.clear()
        for t in targets or []:
            target = AppTarget.from_any(t)
            if not target:
                continue
            self._add_target_entry(target.name, target.path)

    def _collect_targets(self) -> list[AppTarget]:
        targets: list[AppTarget] = []
        for idx in range(self.app_target_list.count()):
            item = self.app_target_list.item(idx)
            data = item.data(QtCore.Qt.ItemDataRole.UserRole) if item else None
            if isinstance(data, dict):
                target = AppTarget.from_any(data)
                if target and (target.name or target.path):
                    targets.append(target)
        return targets

    def _add_selected_process(self):
        data = self.process_combo.currentData()
        if isinstance(data, dict):
            self._add_target_entry(data.get("name"), data.get("path"))

    def _add_active_process(self):
        try:
            info = get_foreground_process()
        except Exception:
            info = None
        if not info:
            QtWidgets.QMessageBox.information(self, "추가 실패", "활성 창 정보를 가져오지 못했습니다.")
            return
        self._add_target_entry(info.get("name"), info.get("path"))

    def _pick_process_file(self):
        path, _ = QtWidgets.QFileDialog.getOpenFileName(self, "실행 파일 선택", "", "Executables (*.exe);;All Files (*.*)")
        if path:
            self._add_target_entry(Path(path).name, path)

    def _update_scope_ui(self):
        enabled = self.scope_combo.currentData() == "app"
        self.app_target_group.setEnabled(bool(enabled))

    def selected_scope(self) -> str:
        return self.scope_combo.currentData() or "global"

    def selected_targets(self) -> list[AppTarget]:
        return self._collect_targets()

class MacroDialog(QtWidgets.QDialog):
    _action_clipboard: list[Action] | None = None

    def __init__(
        self,
        parent=None,
        macro: Macro | None = None,
        *,
        variable_provider=None,
        add_variable=None,
        resolver: VariableResolver | None = None,
        start_pixel_test=None,
        start_condition_debug=None,
        stop_pixel_test=None,
        image_viewer_state: dict | None = None,
        save_image_viewer_state=None,
        open_screenshot_dialog=None,
        screenshot_hotkeys_provider=None,
        screenshot_manager=None,
        apply_scope_all=None,
    ):
        super().__init__(parent)
        self.setWindowTitle("매크로 편집")
        self.setModal(False)
        self.setWindowModality(QtCore.Qt.WindowModality.NonModal)
        self.resize(820, 760)
        self._variable_provider = variable_provider
        self._add_variable = add_variable
        self._resolver = resolver
        self._start_pixel_test_fn = start_pixel_test
        self._start_condition_debug_fn = start_condition_debug
        self._stop_pixel_test_fn = stop_pixel_test
        self._image_viewer_state = image_viewer_state or {}
        self._save_image_viewer_state = save_image_viewer_state
        self._open_screenshot_dialog_fn = open_screenshot_dialog
        self._screenshot_hotkeys_provider = screenshot_hotkeys_provider
        self._screenshot_manager = screenshot_manager
        self._apply_scope_all_cb = apply_scope_all
        self._scope: str = "global"
        self._app_targets: list[AppTarget] = []

        layout = QtWidgets.QVBoxLayout(self)

        form = QtWidgets.QFormLayout()
        self.name_edit = QtWidgets.QLineEdit()
        self.trigger_edit = QtWidgets.QLineEdit()
        self.trigger_menu_btn = QtWidgets.QToolButton()
        self.trigger_menu_btn.setText("목록")
        self.trigger_menu_btn.setPopupMode(QtWidgets.QToolButton.ToolButtonPopupMode.InstantPopup)
        self.trigger_menu = QtWidgets.QMenu(self)
        self.trigger_menu_btn.setMenu(self.trigger_menu)
        self._populate_trigger_menu()
        self.desc_edit = QtWidgets.QLineEdit()
        self.desc_edit.setPlaceholderText("이 매크로에 대한 메모/설명")
        trigger_row = QtWidgets.QWidget()
        trigger_row_layout = QtWidgets.QHBoxLayout(trigger_row)
        trigger_row_layout.setContentsMargins(0, 0, 0, 0)
        trigger_row_layout.addWidget(self.trigger_edit)
        trigger_row_layout.addWidget(self.trigger_menu_btn)
        self.mode_combo = QtWidgets.QComboBox()
        self.mode_combo.addItems(["hold", "toggle"])
        self.stop_others_check = QtWidgets.QCheckBox("이 트리거를 누르면 다른 매크로 모두 정지")
        self.suspend_others_check = QtWidgets.QCheckBox("이 매크로 동작 시 다른 매크로 잠시 대기")
        self.enabled_check = QtWidgets.QCheckBox("활성")
        self.suppress_checkbox = QtWidgets.QCheckBox("트리거 키 차단")
        self.cycle_spin = QtWidgets.QSpinBox()
        self.cycle_spin.setRange(0, 999999)
        self.cycle_spin.setSpecialValueText("무한 반복")
        self.scope_btn = QtWidgets.QPushButton("앱 동작 범위 설정...")
        self.scope_summary = QtWidgets.QLabel("전역 (어디서나)")
        self.scope_summary.setStyleSheet("color: #555;")
        scope_row = QtWidgets.QHBoxLayout()
        scope_row.addWidget(self.scope_btn)
        scope_row.addWidget(self.scope_summary, stretch=1)
        scope_row.addStretch()

        form.addRow("이름(선택)", self.name_edit)
        form.addRow("설명(선택)", self.desc_edit)
        form.addRow("트리거 키", trigger_row)
        form.addRow("모드 (hold/toggle)", self.mode_combo)
        form.addRow(self.stop_others_check)
        form.addRow(self.suspend_others_check)
        form.addRow(self.enabled_check)
        form.addRow("사이클 횟수(0=무한)", self.cycle_spin)
        form.addRow(self.suppress_checkbox)
        form.addRow(scope_row)
        layout.addLayout(form)

        self.action_tree = ActionTreeWidget()
        layout.addWidget(self.action_tree)
        move_row = QtWidgets.QHBoxLayout()
        self.move_up_btn = QtWidgets.QPushButton("위로")
        self.move_down_btn = QtWidgets.QPushButton("아래로")
        move_row.addWidget(self.move_up_btn)
        move_row.addWidget(self.move_down_btn)
        move_row.addStretch()
        layout.addLayout(move_row)
        btns = QtWidgets.QHBoxLayout()
        self.add_btn = QtWidgets.QPushButton("액션 추가")
        self.add_child_btn = QtWidgets.QPushButton("자식 액션 추가")
        self.edit_btn = QtWidgets.QPushButton("편집")
        self.copy_btn = QtWidgets.QPushButton("복사")
        self.paste_btn = QtWidgets.QPushButton("붙여넣기")
        self.del_btn = QtWidgets.QPushButton("삭제")
        self.add_else_btn = QtWidgets.QPushButton("ELSE 추가")
        self.del_else_btn = QtWidgets.QPushButton("ELSE 제거")
        self.expand_all_btn = QtWidgets.QPushButton("전체 펼치기")
        self.collapse_all_btn = QtWidgets.QPushButton("전체 접기")
        btns.addWidget(self.add_btn)
        btns.addWidget(self.add_child_btn)
        btns.addWidget(self.edit_btn)
        btns.addWidget(self.copy_btn)
        btns.addWidget(self.paste_btn)
        btns.addWidget(self.del_btn)
        btns.addWidget(self.add_else_btn)
        btns.addWidget(self.del_else_btn)
        btns.addWidget(self.expand_all_btn)
        btns.addWidget(self.collapse_all_btn)
        btns.addStretch()
        layout.addLayout(btns)

        # 중단 시 실행 액션 편집 영역
        self.stop_group = QtWidgets.QGroupBox("중단 시 실행 (토글/홀드 해제 시 1회)")
        self.stop_group.setCheckable(True)
        self.stop_group.setChecked(False)
        stop_layout = QtWidgets.QVBoxLayout(self.stop_group)
        # 내용 전체를 감싸서 접기/펼치기 가능하게 한다.
        header_row = QtWidgets.QHBoxLayout()
        self.stop_info_lbl = QtWidgets.QLabel("매크로가 중단될 때 한 번 실행됩니다. 비워두면 실행하지 않습니다.")
        self.stop_info_lbl.setStyleSheet("color: #666; font-size: 11px;")
        header_row.addWidget(self.stop_info_lbl)
        header_row.addStretch()
        self.stop_collapse_btn = QtWidgets.QToolButton()
        self.stop_collapse_btn.setText("접기")
        self.stop_collapse_btn.setCheckable(True)
        self.stop_collapse_btn.setChecked(True)
        header_row.addWidget(self.stop_collapse_btn)
        stop_layout.addLayout(header_row)

        self.stop_content = QtWidgets.QWidget()
        stop_content_layout = QtWidgets.QVBoxLayout(self.stop_content)
        self.stop_action_tree = ActionTreeWidget()
        self.stop_action_tree.setFixedHeight(180)
        stop_content_layout.addWidget(self.stop_action_tree)
        stop_btns = QtWidgets.QHBoxLayout()
        self.stop_add_btn = QtWidgets.QPushButton("추가")
        self.stop_add_child_btn = QtWidgets.QPushButton("자식")
        self.stop_edit_btn = QtWidgets.QPushButton("편집")
        self.stop_del_btn = QtWidgets.QPushButton("삭제")
        self.stop_move_up_btn = QtWidgets.QPushButton("위로")
        self.stop_move_down_btn = QtWidgets.QPushButton("아래로")
        self.stop_expand_btn = QtWidgets.QPushButton("펼치기")
        self.stop_tree_collapse_btn = QtWidgets.QPushButton("접기")
        stop_btns.addWidget(self.stop_add_btn)
        stop_btns.addWidget(self.stop_add_child_btn)
        stop_btns.addWidget(self.stop_edit_btn)
        stop_btns.addWidget(self.stop_del_btn)
        stop_btns.addWidget(self.stop_move_up_btn)
        stop_btns.addWidget(self.stop_move_down_btn)
        stop_btns.addWidget(self.stop_expand_btn)
        stop_btns.addWidget(self.stop_tree_collapse_btn)
        stop_btns.addStretch()
        stop_content_layout.addLayout(stop_btns)
        stop_layout.addWidget(self.stop_content)
        layout.addWidget(self.stop_group)

        btn_row = QtWidgets.QHBoxLayout()
        btn_row.addStretch()
        self.ok_btn = QtWidgets.QPushButton("확인")
        self.cancel_btn = QtWidgets.QPushButton("취소")
        btn_row.addWidget(self.ok_btn)
        btn_row.addWidget(self.cancel_btn)
        layout.addLayout(btn_row)

        self.ok_btn.clicked.connect(self.accept)
        self.cancel_btn.clicked.connect(self.reject)
        self.scope_btn.clicked.connect(self._open_scope_dialog)
        self.add_btn.clicked.connect(self._add_action)
        self.add_child_btn.clicked.connect(lambda: self._add_action(as_child=True))
        self.edit_btn.clicked.connect(self._edit_action)
        self.copy_btn.clicked.connect(self._copy_action)
        self.paste_btn.clicked.connect(self._paste_action)
        self.del_btn.clicked.connect(self._delete_action)
        self.add_else_btn.clicked.connect(self._add_else_branch)
        self.del_else_btn.clicked.connect(self._delete_else_branch)
        self.expand_all_btn.clicked.connect(self.action_tree.expandAll)
        self.collapse_all_btn.clicked.connect(self.action_tree.collapse_all)
        self.move_up_btn.clicked.connect(lambda: self._move_selected(-1, self.move_up_btn))
        self.move_down_btn.clicked.connect(lambda: self._move_selected(1, self.move_down_btn))
        self.action_tree.itemDoubleClicked.connect(lambda *_: self._edit_action())
        self.stop_group.toggled.connect(self._set_stop_group_enabled)
        self.stop_collapse_btn.toggled.connect(self._update_stop_collapsed)
        self.stop_tree_collapse_btn.clicked.connect(self.stop_action_tree.collapse_all)
        self._set_stop_group_enabled(False)
        self._update_stop_collapsed()
        self.stop_add_btn.clicked.connect(lambda: self._with_action_tree(self.stop_action_tree, lambda: self._add_action()))
        self.stop_add_child_btn.clicked.connect(lambda: self._with_action_tree(self.stop_action_tree, lambda: self._add_action(as_child=True)))
        self.stop_edit_btn.clicked.connect(lambda: self._with_action_tree(self.stop_action_tree, self._edit_action))
        self.stop_del_btn.clicked.connect(lambda: self._with_action_tree(self.stop_action_tree, self._delete_action))
        self.stop_move_up_btn.clicked.connect(lambda: self._with_action_tree(self.stop_action_tree, lambda: self._move_selected(-1, self.stop_move_up_btn)))
        self.stop_move_down_btn.clicked.connect(lambda: self._with_action_tree(self.stop_action_tree, lambda: self._move_selected(1, self.stop_move_down_btn)))
        self.stop_expand_btn.clicked.connect(self.stop_action_tree.expandAll)
        self.stop_tree_collapse_btn.clicked.connect(self.stop_action_tree.collapse_all)

        if macro:
            self._load_macro(macro)
        else:
            self.suppress_checkbox.setChecked(True)
            self.action_tree.load_actions(
                [
                    Action(type="press", key="r"),
                    Action(type="sleep", sleep_ms=50),
                    Action(type="press", key="t"),
                ]
            )
            self.stop_group.setChecked(False)
            self._set_stop_group_enabled(False)
            self.stop_action_tree.load_actions([])
            self.stop_collapse_btn.setChecked(True)
            self._update_stop_collapsed()
            self._scope = "global"
            self._app_targets = []
            self._set_scope_label()

    def _populate_trigger_menu(self):
        menu = self.trigger_menu
        menu.clear()

        def add(label: str, value: str):
            act = menu.addAction(label)
            act.triggered.connect(lambda _, v=value: self.trigger_edit.setText(v))

        add("마우스 왼쪽 (mouse1)", "mouse1")
        add("마우스 오른쪽 (mouse2)", "mouse2")
        add("마우스 휠 클릭 (mouse3)", "mouse3")
        add("마우스 X1 (mouse4)", "mouse4")
        add("마우스 X2 (mouse5)", "mouse5")
        menu.addSeparator()
        add("CapsLock (capslock)", "capslock")
        for key in ["z", "x", "c", "r", "t", "space", "tab", "shift", "ctrl", "alt"]:
            add(key, key)
        menu.addSeparator()
        for i in range(1, 13):
            add(f"F{i}", f"f{i}")

    def _scope_summary_text(self) -> str:
        if self._scope != "app":
            return "전역 (어디서나)"
        labels: list[str] = []
        for t in self._app_targets or []:
            target = AppTarget.from_any(t)
            if not target:
                continue
            label = target.name or (Path(target.path).name if target.path else "")
            if label:
                labels.append(label)
        if not labels:
            return "특정 앱 (지정 필요)"
        if len(labels) > 3:
            labels = labels[:3] + ["..."]
        return f"특정 앱: {', '.join(labels)}"

    def _set_scope_label(self):
        self.scope_summary.setText(self._scope_summary_text())

    def _open_scope_dialog(self):
        dlg = AppScopeDialog(self, scope=self._scope, targets=self._app_targets, apply_all_cb=self._apply_scope_all_cb)
        if _run_dialog_non_modal(dlg):
            self._scope = dlg.selected_scope()
            self._app_targets = dlg.selected_targets()
            self._set_scope_label()

    def _collect_app_targets(self) -> list[AppTarget]:
        targets: list[AppTarget] = []
        for t in self._app_targets or []:
            target = AppTarget.from_any(t)
            if target:
                targets.append(target)
        return targets

    def _selected_item(self, tree: ActionTreeWidget | None = None) -> QtWidgets.QTreeWidgetItem | None:
        tree = tree or self.action_tree
        return tree.selected_item() if tree else None

    def _selected_if_item(self, tree: ActionTreeWidget | None = None) -> QtWidgets.QTreeWidgetItem | None:
        item = self._selected_item(tree)
        while item:
            data = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
            if isinstance(data, Action) and data.type == "if":
                return item
            item = item.parent()
        return None

    def _available_labels(self, tree: ActionTreeWidget | None = None) -> list[str]:
        labels: list[str] = []

        def walk(actions: list[Action]):
            for act in actions or []:
                if getattr(act, "type", None) == "label" and getattr(act, "label", None):
                    labels.append(act.label)
                walk(getattr(act, "actions", []) or [])
                walk(getattr(act, "else_actions", []) or [])
                for _, branch in getattr(act, "elif_blocks", []) or []:
                    walk(branch or [])

        target_tree = tree or self.action_tree
        walk(target_tree.collect_actions() if target_tree else [])
        uniq: list[str] = []
        for name in labels:
            if name and name not in uniq:
                uniq.append(name)
        return uniq

    def _with_action_tree(self, tree: ActionTreeWidget | None, fn):
        if not tree:
            return
        prev = self.action_tree
        try:
            self.action_tree = tree
            fn()
        finally:
            self.action_tree = prev

    def _set_stop_group_enabled(self, enabled: bool):
        widgets = [
            self.stop_action_tree,
            self.stop_add_btn,
            self.stop_add_child_btn,
            self.stop_edit_btn,
            self.stop_del_btn,
            self.stop_move_up_btn,
            self.stop_move_down_btn,
            self.stop_expand_btn,
            self.stop_tree_collapse_btn,
            self.stop_collapse_btn,
            self.stop_info_lbl,
        ]
        for w in widgets:
            if w:
                w.setEnabled(enabled)
        self._update_stop_collapsed()

    def _update_stop_collapsed(self):
        collapsed = self.stop_collapse_btn.isChecked() if self.stop_collapse_btn else False
        if self.stop_content:
            self.stop_content.setVisible(not collapsed)
        if self.stop_collapse_btn:
            self.stop_collapse_btn.setText("펼치기" if collapsed else "접기")

    def _move_selected(self, offset: int, btn: QtWidgets.QPushButton, tree: ActionTreeWidget | None = None):
        target_tree = tree or self.action_tree
        moved, reason, _ = target_tree.move_selected_within_parent(offset)
        if not moved and reason:
            QtWidgets.QToolTip.showText(btn.mapToGlobal(btn.rect().center()), reason, btn, btn.rect(), 1200)

    def _add_action(self, *, as_child: bool = False, tree: ActionTreeWidget | None = None):
        target_tree = tree or self.action_tree
        dlg = ActionEditDialog(
            self,
            variable_provider=self._variable_provider,
            add_variable=self._add_variable,
            label_provider=lambda: self._available_labels(target_tree),
            resolver=self._resolver,
            start_pixel_test=self._start_pixel_test_fn,
            start_condition_debug=self._start_condition_debug_fn,
            stop_pixel_test=self._stop_pixel_test_fn,
            image_viewer_state=self._image_viewer_state,
            save_image_viewer_state=self._save_image_viewer_state,
            open_screenshot_dialog=self._open_screenshot_dialog_fn,
            screenshot_hotkeys_provider=self._screenshot_hotkeys_provider,
            screenshot_manager=self._screenshot_manager,
        )
        if _run_dialog_non_modal(dlg):
            try:
                act = dlg.get_action()
            except ValueError as exc:
                QtWidgets.QMessageBox.warning(self, "입력 오류", str(exc))
                return
            target = self._selected_item(target_tree)
            if getattr(act, "_as_elif", False):
                if self._insert_elif_from_action(act, target, tree=target_tree):
                    return
                return
            parent = None
            new_item = None
            if as_child:
                parent = target
                if parent and not target_tree._can_have_children_item(parent):
                    QtWidgets.QMessageBox.information(self, "추가 불가", "if/group/elif/else 아래에만 자식을 둘 수 있습니다.")
                    return
                new_item = target_tree._append_action_item(act, parent)
            else:
                if target:
                    new_item = target_tree._insert_after(act, target)
                    parent = target.parent()
                else:
                    new_item = target_tree._append_action_item(act, None)
            if parent:
                target_tree.expandItem(parent)
            elif new_item:
                target_tree.expandItem(new_item)
            if new_item:
                target_tree.setCurrentItem(new_item)
            target_tree.renumber()

    def _find_elif_target(self, reference: QtWidgets.QTreeWidgetItem | None, *, tree: ActionTreeWidget | None = None) -> QtWidgets.QTreeWidgetItem | None:
        tgt = tree or self.action_tree
        if reference and tgt:
            data = reference.data(0, QtCore.Qt.ItemDataRole.UserRole)
            if isinstance(data, Action) and data.type == "if":
                return reference
            ancestor_if = self._selected_if_item(tgt)
            if ancestor_if:
                return ancestor_if
            parent = reference.parent()
            start_idx = parent.indexOfChild(reference) if parent else tgt.indexOfTopLevelItem(reference)
            for i in range(start_idx, -1, -1):
                candidate = parent.child(i) if parent else tgt.topLevelItem(i)
                cand_data = candidate.data(0, QtCore.Qt.ItemDataRole.UserRole)
                if isinstance(cand_data, Action) and cand_data.type == "if":
                    return candidate
        if not tgt:
            return None
        for i in range(tgt.topLevelItemCount() - 1, -1, -1):
            candidate = tgt.topLevelItem(i)
            cand_data = candidate.data(0, QtCore.Qt.ItemDataRole.UserRole)
            if isinstance(cand_data, Action) and cand_data.type == "if":
                return candidate
        return None

    def _merge_if_into_prev_as_elif(
        self,
        src_item: QtWidgets.QTreeWidgetItem,
        new_act: Action,
        *,
        suppress_warning: bool = False,
        tree: ActionTreeWidget | None = None,
    ) -> bool:
        tgt = tree or self.action_tree
        if tgt is None:
            return False
        parent = src_item.parent()
        idx = parent.indexOfChild(src_item) if parent else tgt.indexOfTopLevelItem(src_item)
        prev_if_item = None
        for i in range(idx - 1, -1, -1):
            candidate = parent.child(i) if parent else tgt.topLevelItem(i)
            cand_data = candidate.data(0, QtCore.Qt.ItemDataRole.UserRole)
            if isinstance(cand_data, Action) and cand_data.type == "if":
                prev_if_item = candidate
                break
        if prev_if_item is None:
            if not suppress_warning:
                QtWidgets.QMessageBox.information(self, "대상 없음", "같은 레벨 앞쪽 if가 있어야 ELIF로 변환할 수 있습니다.")
            return False
        if not new_act.condition:
            if not suppress_warning:
                QtWidgets.QMessageBox.information(self, "조건 없음", "조건이 있어야 ELIF로 변환할 수 있습니다.")
            return False
        target_act = prev_if_item.data(0, QtCore.Qt.ItemDataRole.UserRole)
        if not isinstance(target_act, Action) or target_act.type != "if":
            if not suppress_warning:
                QtWidgets.QMessageBox.information(self, "대상 없음", "ELIF 대상 if를 찾지 못했습니다.")
            return False

        base_cond = copy.deepcopy(new_act.condition)
        if hasattr(base_cond, "name") and not getattr(base_cond, "name", None):
            base_cond.name = new_act.name or new_act.description
        src_enabled = new_act.enabled if isinstance(new_act.enabled, bool) else True
        try:
            setattr(base_cond, "enabled", src_enabled)
        except Exception:
            pass

        new_blocks: list[tuple[Condition, list[Action], str, bool]] = [
            (base_cond, copy.deepcopy(new_act.actions), new_act.description or new_act.name or "", src_enabled)
        ]
        inherit_enabled = src_enabled
        for c, a in getattr(new_act, "elif_blocks", []) or []:
            try:
                setattr(c, "enabled", inherit_enabled)
            except Exception:
                pass
            new_blocks.append((copy.deepcopy(c), copy.deepcopy(a), "", inherit_enabled))

        target_act.elif_blocks = (target_act.elif_blocks or []) + new_blocks
        if new_act.else_actions:
            if target_act.else_actions:
                target_act.else_actions.extend(copy.deepcopy(new_act.else_actions))
            else:
                target_act.else_actions = copy.deepcopy(new_act.else_actions)

        expanded = tgt._expanded_keys()
        for cond, acts, desc_text, enabled_flag in new_blocks:
            header = tgt._create_elif_header(prev_if_item, cond, desc_text)
            if not enabled_flag:
                header.setCheckState(5, QtCore.Qt.CheckState.Unchecked)
                data = header.data(0, QtCore.Qt.ItemDataRole.UserRole)
                if isinstance(data, dict):
                    data["enabled"] = False
            for child in acts:
                tgt._append_action_item(copy.deepcopy(child), header)
        if new_act.else_actions:
            else_header = tgt._ensure_else_header(prev_if_item, create_if_missing=True)
            for child in new_act.else_actions:
                tgt._append_action_item(copy.deepcopy(child), else_header)

        # remove original item
        if parent:
            parent.takeChild(idx)
        else:
            tgt.takeTopLevelItem(idx)

        tgt._restore_expanded(expanded)
        tgt.expandItem(prev_if_item)
        tgt.renumber()
        return True

    def _insert_elif_from_action(self, act: Action, target: QtWidgets.QTreeWidgetItem | None, *, tree: ActionTreeWidget | None = None) -> bool:
        tgt = tree or self.action_tree
        target_if = self._find_elif_target(target, tree=tgt)
        if not target_if:
            QtWidgets.QMessageBox.information(self, "대상 없음", "ELIF를 추가할 if를 선택하세요.")
            return False
        cond = copy.deepcopy(act.condition)
        if cond is None:
            QtWidgets.QMessageBox.warning(self, "조건 없음", "ELIF 조건이 비어 있습니다.")
            return False
        enabled_flag = act.enabled if isinstance(act.enabled, bool) else True
        try:
            setattr(cond, "enabled", enabled_flag)
        except Exception:
            pass
        expanded = tgt._expanded_keys() if tgt else []
        header = tgt._create_elif_header(target_if, cond, act.description or act.name or "")
        header.setCheckState(5, QtCore.Qt.CheckState.Checked if enabled_flag else QtCore.Qt.CheckState.Unchecked)
        data = header.data(0, QtCore.Qt.ItemDataRole.UserRole)
        if isinstance(data, dict):
            data["enabled"] = enabled_flag
        for child_act in act.actions or []:
            tgt._append_action_item(copy.deepcopy(child_act), header)
        self._refresh_if_item(target_if, tree=tgt)
        if tgt:
            tgt._restore_expanded(expanded)
            tgt.expandItem(target_if)
            tgt.setCurrentItem(header)
            tgt.renumber()
        return True

    def _refresh_if_item(self, if_item: QtWidgets.QTreeWidgetItem | None, *, tree: ActionTreeWidget | None = None):
        if not if_item:
            return
        tgt = tree or self.action_tree
        if not tgt:
            return
        updated_if = tgt._action_from_item(if_item)
        if isinstance(updated_if, Action):
            if_item.setData(0, QtCore.Qt.ItemDataRole.UserRole, updated_if)
            if_item.setText(1, updated_if.type)
            if_item.setText(2, updated_if.name or "")
            if_item.setText(3, tgt._format_value(updated_if))
            if_item.setText(4, tgt._format_desc(updated_if))
            tgt._apply_once_style(if_item, updated_if)

    def _add_else_branch(self, *, tree: ActionTreeWidget | None = None):
        tgt = tree or self.action_tree
        if_item = self._selected_if_item(tgt)
        data = if_item.data(0, QtCore.Qt.ItemDataRole.UserRole) if if_item else None
        if not if_item or not isinstance(data, Action) or data.type != "if":
            QtWidgets.QMessageBox.information(self, "선택 없음", "ELSE를 추가할 if를 선택하세요.")
            return
        header = tgt._ensure_else_header(if_item, create_if_missing=True)
        if header:
            tgt.expandItem(if_item)
            tgt.setCurrentItem(header)
            tgt.renumber()
            tgt.renumber()

    def _delete_else_branch(self, *, tree: ActionTreeWidget | None = None):
        tgt = tree or self.action_tree
        target = self._selected_if_item(tgt)
        if not target:
            QtWidgets.QMessageBox.information(self, "선택 없음", "ELSE를 제거할 if를 선택하세요.")
            return
        tgt.remove_else_header(target)

    def _edit_action(self):
        item = self._selected_item()
        if not item:
            QtWidgets.QMessageBox.information(self, "선택 없음", "편집할 액션을 선택하세요.")
            return
        act_data = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
        if isinstance(act_data, dict) and act_data.get("marker") == "__elif__":
            cond = act_data.get("condition") if isinstance(act_data.get("condition"), Condition) else Condition(
                type="pixel", region=(0, 0, 1, 1), color=(255, 0, 0)
            )
            enabled_flag = item.checkState(5) == QtCore.Qt.CheckState.Checked
            try:
                setattr(cond, "enabled", enabled_flag)
            except Exception:
                pass
            # ELIF 편집을 IF와 동일하게 제공 (조건/설명/once_per_macro 등 포함)
            branch_actions: list[Action] = []
            else_actions: list[Action] = []
            for i in range(item.childCount()):
                child = item.child(i)
                child_data = child.data(0, QtCore.Qt.ItemDataRole.UserRole)
                if isinstance(child_data, Action):
                    branch_actions.append(self.action_tree._action_from_item(child))
                elif child_data == "__else__":
                    for j in range(child.childCount()):
                        else_actions.append(self.action_tree._action_from_item(child.child(j)))
            temp_act = Action(
                type="elif",
                name=None,
                description=item.text(3) or "",
                enabled=enabled_flag,
                condition=cond,
                actions=branch_actions,
                else_actions=else_actions,
                once_per_macro=False,
            )
            expanded_before = self.action_tree._expanded_keys()
            dlg = ActionEditDialog(
                self,
                action=temp_act,
                variable_provider=self._variable_provider,
                add_variable=self._add_variable,
                label_provider=self._available_labels,
                resolver=self._resolver,
                start_pixel_test=self._start_pixel_test_fn,
                start_condition_debug=self._start_condition_debug_fn,
                stop_pixel_test=self._stop_pixel_test_fn,
                image_viewer_state=self._image_viewer_state,
                save_image_viewer_state=self._save_image_viewer_state,
                open_screenshot_dialog=self._open_screenshot_dialog_fn,
                screenshot_hotkeys_provider=self._screenshot_hotkeys_provider,
                screenshot_manager=self._screenshot_manager,
            )
            if _run_dialog_non_modal(dlg):
                try:
                    new_act = dlg.get_action()
                except ValueError as exc:
                    QtWidgets.QMessageBox.warning(self, "입력 오류", str(exc))
                    return
                if new_act.type not in ("if", "elif"):
                    QtWidgets.QMessageBox.warning(self, "타입 제한", "ELIF는 조건 타입만 허용됩니다.")
                    return
                if new_act.type == "if":
                    parent_if = item.parent()
                    parent_container = parent_if.parent() if parent_if else None
                    insert_after = parent_if
                    if parent_if:
                        parent_if.takeChild(parent_if.indexOfChild(item))
                    new_item = self.action_tree._insert_after(new_act, insert_after)
                    if parent_if:
                        self._refresh_if_item(parent_if)
                    self.action_tree._restore_expanded(expanded_before)
                    if new_item:
                        self.action_tree.expandItem(new_item)
                        self.action_tree.setCurrentItem(new_item)
                    self.action_tree.renumber()
                    return
                setattr(new_act, "_as_elif", True)
                enabled_flag = new_act.enabled
                new_cond = new_act.condition or cond
                try:
                    setattr(new_cond, "enabled", enabled_flag)
                except Exception:
                    pass
                item.setData(0, QtCore.Qt.ItemDataRole.UserRole, {"marker": "__elif__", "condition": new_cond, "enabled": enabled_flag})
                item.setText(1, "ELIF")
                item.setText(2, new_act.name or "")
                item.setText(3, _condition_brief(new_cond))
                item.setText(4, new_act.description or "")
                item.setCheckState(5, QtCore.Qt.CheckState.Checked if enabled_flag else QtCore.Qt.CheckState.Unchecked)
                self.action_tree._set_drop_enabled(item, True)
                while item.childCount() > 0:
                    item.takeChild(0)
                for child_act in new_act.actions or []:
                    self.action_tree._append_action_item(copy.deepcopy(child_act), item)
                if new_act.else_actions:
                    else_header = self.action_tree._ensure_else_header(item, create_if_missing=True)
                    for child_act in new_act.else_actions:
                        self.action_tree._append_action_item(copy.deepcopy(child_act), else_header)
                parent_if = item.parent()
                if parent_if:
                    self._refresh_if_item(parent_if)
                self.action_tree._apply_enabled_styles()
                self.action_tree.renumber()
            return
        if not isinstance(act_data, Action):
            return
        act = self.action_tree._action_from_item(item)
        if not isinstance(act, Action):
            return
        expanded_before = self.action_tree._expanded_keys()
        dlg = ActionEditDialog(
            self,
            action=act,
            variable_provider=self._variable_provider,
            add_variable=self._add_variable,
            label_provider=self._available_labels,
            resolver=self._resolver,
            start_pixel_test=self._start_pixel_test_fn,
            start_condition_debug=self._start_condition_debug_fn,
            stop_pixel_test=self._stop_pixel_test_fn,
            image_viewer_state=self._image_viewer_state,
            save_image_viewer_state=self._save_image_viewer_state,
            open_screenshot_dialog=self._open_screenshot_dialog_fn,
            screenshot_hotkeys_provider=self._screenshot_hotkeys_provider,
            screenshot_manager=self._screenshot_manager,
        )
        if _run_dialog_non_modal(dlg):
            try:
                new_act = dlg.get_action()
            except ValueError as exc:
                QtWidgets.QMessageBox.warning(self, "입력 오류", str(exc))
                return
            if isinstance(act_data, Action) and act_data.type == "if" and getattr(new_act, "_as_elif", False):
                if self._merge_if_into_prev_as_elif(item, new_act):
                    return
            if new_act.type not in ("if", "group"):
                new_act.actions = []
                new_act.else_actions = []
                new_act.elif_blocks = []
            item.setData(0, QtCore.Qt.ItemDataRole.UserRole, new_act)
            item.setText(1, new_act.type)
            item.setText(2, new_act.name or "")
            item.setText(3, self.action_tree._format_value(new_act))
            item.setText(4, self.action_tree._format_desc(new_act))
            item.setCheckState(5, QtCore.Qt.CheckState.Checked if new_act.enabled else QtCore.Qt.CheckState.Unchecked)
            self.action_tree._set_drop_enabled(item, self.action_tree._can_have_children_data(new_act))
            self.action_tree._apply_once_style(item, new_act)
            item.takeChildren()
            if new_act.type == "if":
                for child in new_act.actions:
                    self.action_tree._append_action_item(child, item)
                for econd, eacts in getattr(new_act, "elif_blocks", []):
                    elif_header = self.action_tree._create_elif_header(item, econd)
                    for child in eacts:
                        self.action_tree._append_action_item(child, elif_header)
                else_header = self.action_tree._ensure_else_header(item, create_if_missing=bool(new_act.else_actions))
                if else_header:
                    for child in new_act.else_actions:
                        self.action_tree._append_action_item(child, else_header)
            elif new_act.type == "group":
                for child in new_act.actions:
                    self.action_tree._append_action_item(child, item)
            # 편집 전 펼침 상태만 복원하고 추가 확장은 하지 않는다.
            self.action_tree._restore_expanded(expanded_before)
            self.action_tree.renumber()

    def _copy_action(self, tree: ActionTreeWidget | None = None):
        target_tree = tree or self.action_tree
        if not target_tree:
            return
        items = target_tree._top_level_selected(target_tree.selectedItems())
        if not items:
            QtWidgets.QMessageBox.information(self, "선택 없음", "복사할 액션을 선택하세요.")
            return
        copied: list[Action] = []
        for item in items:
            act = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
            if isinstance(act, Action):
                copied.append(copy.deepcopy(act))
        if not copied:
            QtWidgets.QMessageBox.information(self, "선택 없음", "액션을 선택하세요.")
            return
        MacroDialog._action_clipboard = copied

    def _paste_action(self, tree: ActionTreeWidget | None = None):
        target_tree = tree or self.action_tree
        if not target_tree:
            return
        if not MacroDialog._action_clipboard:
            QtWidgets.QMessageBox.information(self, "복사본 없음", "먼저 복사할 액션을 선택해 복사하세요.")
            return
        target_item = self._selected_item(target_tree)
        if target_tree.topLevelItemCount() > 0 and target_item is None:
            QtWidgets.QMessageBox.information(self, "선택 없음", "붙여넣을 위치를 선택하세요.")
            return
        clipboard = MacroDialog._action_clipboard
        actions_to_paste: list[Action]
        if isinstance(clipboard, list):
            actions_to_paste = [copy.deepcopy(act) for act in clipboard]
        else:
            actions_to_paste = [copy.deepcopy(clipboard)]

        new_items: list[QtWidgets.QTreeWidgetItem] = []
        expand_item = None
        parent = None
        insert_row: int | None = None
        if target_item is None:
            parent = None
            insert_row = target_tree.topLevelItemCount()
        else:
            data = target_item.data(0, QtCore.Qt.ItemDataRole.UserRole)
            if data == "__else__" or (isinstance(data, dict) and data.get("marker") == "__elif__"):
                parent = target_item
                insert_row = parent.childCount()
                expand_item = target_item
            else:
                parent = target_item.parent()
                base_row = (
                    parent.indexOfChild(target_item)
                    if parent
                    else target_tree.indexOfTopLevelItem(target_item)
                )
                insert_row = (base_row + 1) if base_row >= 0 else None
                expand_item = parent

        for act in actions_to_paste:
            item = target_tree._append_action_item(act, parent, insert_row)
            new_items.append(item)
            if parent:
                insert_row = parent.indexOfChild(item) + 1
            else:
                insert_row = target_tree.indexOfTopLevelItem(item) + 1

        if expand_item is None and new_items:
            expand_item = new_items[0]
        if expand_item:
            target_tree.expandItem(expand_item)
        if new_items:
            target_tree.clearSelection()
            for item in new_items:
                item.setSelected(True)
            target_tree.setCurrentItem(new_items[0])
        target_tree.renumber()

    def _delete_action(self):
        selected = self.action_tree._top_level_selected(self.action_tree.selectedItems())
        if not selected:
            QtWidgets.QMessageBox.information(self, "선택 없음", "삭제할 액션을 선택하세요.")
            return
        for item in reversed(selected):
            data = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
            parent = item.parent()
            if isinstance(data, dict) and data.get("marker") == "__elif__":
                if parent:
                    parent.removeChild(item)
                continue
            if parent:
                parent.removeChild(item)
            else:
                idx = self.action_tree.indexOfTopLevelItem(item)
                if idx >= 0:
                    self.action_tree.takeTopLevelItem(idx)
        self.action_tree.renumber()

    def _load_macro(self, macro: Macro):
        self.name_edit.setText(macro.name or "")
        self.desc_edit.setText(getattr(macro, "description", "") or "")
        self.trigger_edit.setText(macro.trigger_key)
        self.mode_combo.setCurrentText(macro.mode)
        self.enabled_check.setChecked(getattr(macro, "enabled", True))
        self.suppress_checkbox.setChecked(bool(macro.suppress_trigger))
        self.stop_others_check.setChecked(bool(getattr(macro, "stop_others_on_trigger", False)))
        self.suspend_others_check.setChecked(bool(getattr(macro, "suspend_others_while_running", False)))
        self.cycle_spin.setValue(int(macro.cycle_count or 0))
        self._scope = getattr(macro, "scope", "global") or "global"
        self._app_targets = []
        if self._scope == "app":
            for t in getattr(macro, "app_targets", []) or []:
                target = AppTarget.from_any(t)
                if target:
                    self._app_targets.append(copy.deepcopy(target))
        self._set_scope_label()
        self.action_tree.load_actions(copy.deepcopy(macro.actions))
        stop_actions = copy.deepcopy(getattr(macro, "stop_actions", []) or [])
        self.stop_action_tree.load_actions(stop_actions)
        self.stop_group.setChecked(bool(stop_actions))
        self._set_stop_group_enabled(bool(stop_actions))
        self.stop_collapse_btn.setChecked(True)  # 기본은 접힌 상태
        self._update_stop_collapsed()

    def get_macro(self) -> Macro:
        trigger = self.trigger_edit.text().strip()
        if not trigger:
            raise ValueError("트리거 키를 입력하세요.")
        name = self.name_edit.text().strip() or None
        description = self.desc_edit.text().strip() or None
        mode = self.mode_combo.currentText() or "hold"
        suppress = self.suppress_checkbox.isChecked()
        stop_others = self.stop_others_check.isChecked()
        suspend_others = self.suspend_others_check.isChecked()
        enabled = self.enabled_check.isChecked()
        scope = self._scope or "global"
        app_targets: list[AppTarget] = []
        if scope == "app":
            app_targets = [copy.deepcopy(t) for t in self._collect_app_targets()]
        actions = self.action_tree.collect_actions()
        stop_enabled = self.stop_group.isChecked()
        stop_actions = self.stop_action_tree.collect_actions() if stop_enabled else []
        cycle_val = self.cycle_spin.value()
        cycle_count = cycle_val if cycle_val > 0 else None
        return Macro(
            trigger_key=trigger,
            mode=mode,
            actions=actions,
            stop_actions=stop_actions,
            suppress_trigger=suppress,
            stop_others_on_trigger=stop_others,
            suspend_others_while_running=suspend_others,
            enabled=enabled,
            name=name,
            description=description,
            cycle_count=cycle_count,
            scope=scope,
            app_targets=app_targets,
        )


class ScreenshotDialog(QtWidgets.QDialog):
    def __init__(self, manager: ScreenCaptureManager, parent=None, *, save_state_cb=None):
        super().__init__(parent)
        self.manager = manager
        self._save_state_cb = save_state_cb
        self.setWindowTitle("스크린샷")
        self.setModal(False)
        self.setWindowModality(QtCore.Qt.WindowModality.NonModal)
        self.setWindowFlags(
            QtCore.Qt.WindowType.Window
            | QtCore.Qt.WindowType.WindowMinimizeButtonHint
            | QtCore.Qt.WindowType.WindowMaximizeButtonHint
            | QtCore.Qt.WindowType.WindowCloseButtonHint
        )
        self.resize(420, 240)
        self._presets = {
            "사용자 설정": None,
            "원본(무압축 PNG)": {"format": "png", "jpeg_quality": 95, "png_level": 0},
            "고품질": {"format": "png", "jpeg_quality": 90, "png_level": 2},
            "중간": {"format": "jpeg", "jpeg_quality": 80, "png_level": 4},
            "저용량": {"format": "jpeg", "jpeg_quality": 50, "png_level": 6},
        }

        layout = QtWidgets.QVBoxLayout(self)

        form = QtWidgets.QFormLayout()
        self.interval_spin = QtWidgets.QDoubleSpinBox()
        self.interval_spin.setRange(MIN_INTERVAL_SECONDS, 60.0)
        self.interval_spin.setDecimals(6)
        self.interval_spin.setSingleStep(0.001)
        self.interval_spin.setValue(self.manager.interval)
        form.addRow("캡처 주기(초)", self.interval_spin)

        self.start_hotkey_edit = QtWidgets.QLineEdit(self.manager.hotkeys.start or "")
        self.start_hotkey_edit.setPlaceholderText("예: f9")
        self.stop_hotkey_edit = QtWidgets.QLineEdit(self.manager.hotkeys.stop or "")
        self.stop_hotkey_edit.setPlaceholderText("예: f10")
        self.capture_hotkey_edit = QtWidgets.QLineEdit(self.manager.hotkeys.capture or "")
        self.capture_hotkey_edit.setPlaceholderText("예: f11 (한 장 캡처)")
        form.addRow("시작 단축키", self.start_hotkey_edit)
        form.addRow("정지 단축키", self.stop_hotkey_edit)
        form.addRow("단일 캡처 단축키", self.capture_hotkey_edit)

        self.hotkey_checkbox = QtWidgets.QCheckBox("단축키 활성화")
        self.hotkey_checkbox.setChecked(self.manager.hotkeys.enabled)
        form.addRow(self.hotkey_checkbox)
        self.preset_combo = QtWidgets.QComboBox()
        for name in self._presets:
            self.preset_combo.addItem(name)
        form.addRow("품질 프리셋", self.preset_combo)

        self.format_combo = QtWidgets.QComboBox()
        self.format_combo.addItems(["jpeg", "png"])
        fmt_idx = self.format_combo.findText(self.manager.image_format)
        if fmt_idx >= 0:
            self.format_combo.setCurrentIndex(fmt_idx)
        self.jpeg_quality_spin = QtWidgets.QSpinBox()
        self.jpeg_quality_spin.setRange(1, 95)
        self.jpeg_quality_spin.setValue(self.manager.jpeg_quality)
        self.png_level_spin = QtWidgets.QSpinBox()
        self.png_level_spin.setRange(0, 9)
        self.png_level_spin.setValue(self.manager.png_compress_level)
        form.addRow("포맷", self.format_combo)
        form.addRow("JPEG 품질 (낮음=작음)", self.jpeg_quality_spin)
        form.addRow("PNG 압축(0~9)", self.png_level_spin)

        self.queue_spin = QtWidgets.QSpinBox()
        self.queue_spin.setRange(1, 2000)
        self.queue_spin.setValue(self.manager.max_queue_size)
        form.addRow("버퍼 크기(프레임)", self.queue_spin)

        self.output_label = QtWidgets.QLabel(str(self.manager.output_dir))
        self.output_label.setTextInteractionFlags(QtCore.Qt.TextInteractionFlag.TextSelectableByMouse)
        form.addRow("저장 위치", self.output_label)

        layout.addLayout(form)
        layout.addWidget(QtWidgets.QLabel("단축키는 단일 키 이름(f9, home 등)만 지원합니다."))

        self.status_label = QtWidgets.QLabel(self._status_text())
        layout.addWidget(self.status_label)

        btn_row = QtWidgets.QHBoxLayout()
        self.start_btn = QtWidgets.QPushButton("캡처 시작")
        self.stop_btn = QtWidgets.QPushButton("캡처 정지")
        self.open_dir_btn = QtWidgets.QPushButton("폴더 열기")
        self.close_btn = QtWidgets.QPushButton("닫기")
        for btn in (self.start_btn, self.stop_btn, self.close_btn):
            btn_row.addWidget(btn)
        btn_row.addWidget(self.open_dir_btn)
        layout.addLayout(btn_row)

        self.start_btn.clicked.connect(self._start_capture)
        self.stop_btn.clicked.connect(self._stop_capture)
        self.close_btn.clicked.connect(self.close)
        self.format_combo.currentTextChanged.connect(self._toggle_format_fields)
        self.preset_combo.currentTextChanged.connect(self._apply_preset_selection)
        self.format_combo.currentTextChanged.connect(self._on_custom_changed)
        self.jpeg_quality_spin.valueChanged.connect(self._on_custom_changed)
        self.png_level_spin.valueChanged.connect(self._on_custom_changed)
        self.open_dir_btn.clicked.connect(self._open_dir)
        self.hotkey_checkbox.toggled.connect(self._apply_only)
        self._toggle_format_fields(self.format_combo.currentText())
        self._sync_preset_from_manager(force=True)

    def _status_text(self) -> str:
        state = "동작 중" if self.manager.is_running else "중지"
        hotkey_state = (
            "ON"
            if self.manager.hotkeys.enabled
            and (self.manager.hotkeys.start or self.manager.hotkeys.stop or self.manager.hotkeys.capture)
            else "OFF"
        )
        hk_start = self.manager.hotkeys.start or "-"
        hk_stop = self.manager.hotkeys.stop or "-"
        hk_cap = self.manager.hotkeys.capture or "-"
        return (
            f"상태: {state} | 주기: {self.manager.interval}초 | 핫키: {hotkey_state} "
            f"(시작={hk_start}, 정지={hk_stop}, 단일={hk_cap}) | 포맷: {self.manager.image_format} | 버퍼: {self.manager.max_queue_size}"
        )

    def _apply_only(self):
        interval = float(self.interval_spin.value())
        start_key = self.start_hotkey_edit.text().strip() or None
        stop_key = self.stop_hotkey_edit.text().strip() or None
        capture_key = self.capture_hotkey_edit.text().strip() or None
        has_hotkeys = bool(start_key or stop_key or capture_key)
        effective_enabled = bool(self.hotkey_checkbox.isChecked() and has_hotkeys)
        if self.hotkey_checkbox.isChecked() and not has_hotkeys:
            # 키가 비어 있으면 단축키 활성화를 강제로 끈다.
            self.hotkey_checkbox.setChecked(False)
        self.manager.interval = max(interval, MIN_INTERVAL_SECONDS)
        self.manager.image_format = self.format_combo.currentText()
        self.manager.jpeg_quality = int(self.jpeg_quality_spin.value())
        self.manager.png_compress_level = int(self.png_level_spin.value())
        self.manager.max_queue_size = int(self.queue_spin.value())
        self.manager.configure_hotkeys(start_key, stop_key, capture_key, enabled=effective_enabled)
        self._sync_preset_from_manager(force=True)
        self._update_status()
        if self._save_state_cb:
            self._save_state_cb(self._collect_state())

    def _start_capture(self):
        self._apply_only()
        self.manager.start(reset_counter=True)
        self._update_status()

    def _stop_capture(self):
        self.manager.stop()
        self._update_status()

    def _update_status(self):
        self.status_label.setText(self._status_text())

    def _toggle_format_fields(self, fmt: str):
        is_jpeg = fmt.lower() == "jpeg"
        self.jpeg_quality_spin.setEnabled(is_jpeg)
        self.png_level_spin.setEnabled(not is_jpeg)

    def _mark_preset_custom(self):
        idx = self.preset_combo.findText("사용자 설정")
        if idx >= 0 and self.preset_combo.currentIndex() != idx:
            self.preset_combo.blockSignals(True)
            self.preset_combo.setCurrentIndex(idx)
            self.preset_combo.blockSignals(False)

    def _on_custom_changed(self, *args):
        # 사용자가 품질 값을 직접 수정하면 사용자 설정으로 전환
        self._mark_preset_custom()
        self._update_status()

    def _apply_preset_selection(self, name: str):
        preset = self._presets.get(name)
        if preset is None:
            return
        fmt = preset.get("format", self.format_combo.currentText())
        self.format_combo.blockSignals(True)
        self.format_combo.setCurrentText(fmt)
        self.format_combo.blockSignals(False)
        if fmt == "jpeg":
            self.jpeg_quality_spin.blockSignals(True)
            self.jpeg_quality_spin.setValue(int(preset.get("jpeg_quality", self.jpeg_quality_spin.value())))
            self.jpeg_quality_spin.blockSignals(False)
        else:
            self.png_level_spin.blockSignals(True)
            self.png_level_spin.setValue(int(preset.get("png_level", self.png_level_spin.value())))
            self.png_level_spin.blockSignals(False)
        self._toggle_format_fields(fmt)
        self._update_status()

    def _current_preset_name(self) -> str:
        fmt = self.manager.image_format
        jq = self.manager.jpeg_quality
        pl = self.manager.png_compress_level
        for name, preset in self._presets.items():
            if preset is None:
                continue
            if preset.get("format") != fmt:
                continue
            if fmt == "jpeg" and int(preset.get("jpeg_quality", -1)) == int(jq):
                return name
            if fmt == "png" and int(preset.get("png_level", -1)) == int(pl):
                return name
        return "사용자 설정"

    def _sync_preset_from_manager(self, force: bool = False):
        name = self._current_preset_name()
        idx = self.preset_combo.findText(name)
        if idx >= 0 and (force or self.preset_combo.currentIndex() != idx):
            self.preset_combo.blockSignals(True)
            self.preset_combo.setCurrentIndex(idx)
            self.preset_combo.blockSignals(False)

    def _open_dir(self):
        url = QtCore.QUrl.fromLocalFile(str(self.manager.output_dir))
        QtGui.QDesktopServices.openUrl(url)

    def closeEvent(self, event: QtGui.QCloseEvent):
        # 창을 닫을 때도 현재 설정을 적용/저장해두어 추가 클릭 없이 유지되도록 한다.
        try:
            self._apply_only()
        except Exception:
            pass
        return super().closeEvent(event)

    def _collect_state(self) -> dict:
        return {
            "interval": self.manager.interval,
            "format": self.manager.image_format,
            "jpeg_quality": self.manager.jpeg_quality,
            "png_compress_level": self.manager.png_compress_level,
            "queue_size": self.manager.max_queue_size,
            "hotkey_start": self.manager.hotkeys.start,
            "hotkey_stop": self.manager.hotkeys.stop,
            "hotkey_capture": self.manager.hotkeys.capture,
            "hotkey_enabled": self.manager.hotkeys.enabled,
        }


class DebuggerDialog(QtWidgets.QDialog):
    def _make_section(self, title: str, content: QtWidgets.QWidget, state_key: str, *, default_open: bool = True) -> QtWidgets.QWidget:
        btn = QtWidgets.QToolButton()
        btn.setText(title)
        btn.setCheckable(True)
        btn.setChecked(default_open)
        btn.setToolButtonStyle(QtCore.Qt.ToolButtonStyle.ToolButtonTextBesideIcon)
        btn.setArrowType(QtCore.Qt.ArrowType.DownArrow if default_open else QtCore.Qt.ArrowType.RightArrow)
        container = QtWidgets.QWidget()
        v = QtWidgets.QVBoxLayout(container)
        v.setContentsMargins(0, 0, 0, 0)
        v.addWidget(content)

        def _toggle(opened: bool):
            container.setVisible(opened)
            btn.setArrowType(QtCore.Qt.ArrowType.DownArrow if opened else QtCore.Qt.ArrowType.RightArrow)
            self._section_controls[state_key] = btn
            if self._save_state_cb:
                try:
                    self._save_state_cb(self._collect_state())
                except Exception:
                    pass

        btn.toggled.connect(_toggle)
        _toggle(default_open)

        wrap = QtWidgets.QWidget()
        wrap_layout = QtWidgets.QVBoxLayout(wrap)
        wrap_layout.setContentsMargins(0, 0, 0, 0)
        wrap_layout.addWidget(btn)
        wrap_layout.addWidget(container)
        self._section_controls[state_key] = btn
        return wrap
    def __init__(
        self,
        parent=None,
        *,
        state: dict | None = None,
        save_state_cb=None,
        interval_changed_cb=None,
        tolerance_changed_cb=None,
        close_cb=None,
        start_test_cb=None,
        stop_test_cb=None,
        fail_capture_cb=None,
        focus_viewer_cb=None,
    ):
        super().__init__(parent)
        self.setWindowTitle("디버거 (항상 위)")
        self.setModal(False)
        self.setWindowFlag(QtCore.Qt.WindowType.WindowStaysOnTopHint, True)
        self._save_state_cb = save_state_cb
        self._interval_changed_cb = interval_changed_cb
        self._tolerance_changed_cb = tolerance_changed_cb
        self._close_cb = close_cb
        self._start_test_cb = start_test_cb
        self._stop_test_cb = stop_test_cb
        self._max_steps = 80
        self._max_logs = 400
        self._var_rows: dict[str, int] = {}
        self._log_buffer: list[tuple[str, bool]] = []
        self._interval_ms = 200
        self._tolerance = 10
        self._testing = False
        self._pending_label: str | None = None
        self._log_seq = 0
        self._condition_eval_fn = None
        self._condition_stop_cb = None
        self._condition_timer = QtCore.QTimer(self)
        self._condition_timer.setSingleShot(False)
        self._condition_timer.timeout.connect(self._tick_condition_debug)
        self._condition_label = "조건 디버그"
        self._fail_capture_cb = fail_capture_cb
        self._focus_viewer_cb = focus_viewer_cb
        self._fail_capture_enabled = False
        self._fail_capture_cooldown = 1.0
        self._last_condition_result: bool | None = None
        self._last_capture_ts: float = 0.0
        self._fail_capture_limit: int | None = None
        self._fail_capture_count: int = 0
        self._fail_capture_armed: bool = False
        self._fail_capture_confirmations: int = 1
        self._fail_capture_false_streak: int = 0
        self._last_condition_tree: dict | None = None
        self._compare_color_override: tuple[int, int, int] | None = None
        self._section_controls: dict[str, QtWidgets.QToolButton] = {}

        self._build_ui()
        self._restore_state(state or {})

    def _build_ui(self):
        layout = QtWidgets.QVBoxLayout(self)

        status_row = QtWidgets.QHBoxLayout()
        self.state_label = QtWidgets.QLabel("엔진 상태: -")
        self.pause_label = QtWidgets.QLabel("일시정지: -")
        for lbl in (self.state_label, self.pause_label):
            lbl.setFrameShape(QtWidgets.QFrame.Shape.Panel)
            lbl.setFrameShadow(QtWidgets.QFrame.Shadow.Sunken)
            lbl.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)
            lbl.setMinimumWidth(140)
        status_row.addWidget(self.state_label)
        status_row.addWidget(self.pause_label)
        status_row.addWidget(QtWidgets.QLabel("테스트 주기(ms):"))
        self.interval_spin = QtWidgets.QSpinBox()
        self.interval_spin.setRange(50, 5000)
        self.interval_spin.setSingleStep(50)
        self.interval_spin.setValue(self._interval_ms)
        self.interval_spin.valueChanged.connect(self._on_interval_changed)
        status_row.addWidget(self.interval_spin)
        self.clear_btn = QtWidgets.QPushButton("디버거 초기화")
        self.clear_btn.clicked.connect(self._clear_all)
        status_row.addWidget(self.clear_btn)
        self.view_image_btn = QtWidgets.QPushButton("이미지 뷰어 보기")
        self.view_image_btn.clicked.connect(lambda: self._focus_viewer_cb() if callable(self._focus_viewer_cb) else None)
        status_row.addWidget(self.view_image_btn)
        status_row.addStretch()
        layout.addLayout(status_row)

        cond_group = QtWidgets.QGroupBox("조건 디버그")
        cond_layout = QtWidgets.QVBoxLayout(cond_group)
        cond_header = QtWidgets.QHBoxLayout()
        self.condition_state_label = QtWidgets.QLabel("전체 결과: -")
        self.condition_state_label.setFrameShape(QtWidgets.QFrame.Shape.Panel)
        self.condition_state_label.setFrameShadow(QtWidgets.QFrame.Shadow.Sunken)
        self.condition_state_label.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)
        self.condition_fail_label = QtWidgets.QLabel("실패 경로: -")
        self.condition_fail_label.setWordWrap(True)
        self.condition_fail_label.setFrameShape(QtWidgets.QFrame.Shape.Panel)
        self.condition_fail_label.setFrameShadow(QtWidgets.QFrame.Shadow.Sunken)
        self.condition_fail_label.setAlignment(QtCore.Qt.AlignmentFlag.AlignLeft | QtCore.Qt.AlignmentFlag.AlignVCenter)
        self.condition_stop_btn = QtWidgets.QPushButton("조건 디버그 중지")
        self.condition_stop_btn.setEnabled(False)
        self.condition_stop_btn.clicked.connect(self._on_condition_stop_clicked)
        cond_header.addWidget(self.condition_state_label)
        cond_header.addWidget(self.condition_fail_label, 1)
        cond_header.addStretch()
        cond_header.addWidget(self.condition_stop_btn)
        cond_layout.addLayout(cond_header)
        capture_row = QtWidgets.QHBoxLayout()
        self.capture_toggle_btn = QtWidgets.QToolButton()
        self.capture_toggle_btn.setCheckable(True)
        self.capture_toggle_btn.setText("실패 시 캡처 OFF")
        self.capture_toggle_btn.setToolButtonStyle(QtCore.Qt.ToolButtonStyle.ToolButtonTextBesideIcon)
        self.capture_toggle_btn.setIcon(QtGui.QIcon.fromTheme("camera"))
        self.capture_toggle_btn.toggled.connect(self._on_capture_toggle)
        capture_row.addWidget(self.capture_toggle_btn)
        capture_row.addWidget(QtWidgets.QLabel("쿨다운(초):"))
        self.capture_cooldown_spin = QtWidgets.QDoubleSpinBox()
        self.capture_cooldown_spin.setRange(0.1, 5.0)
        self.capture_cooldown_spin.setSingleStep(0.1)
        self.capture_cooldown_spin.setDecimals(1)
        self.capture_cooldown_spin.setValue(self._fail_capture_cooldown)
        self.capture_cooldown_spin.valueChanged.connect(self._on_capture_cooldown_changed)
        capture_row.addWidget(self.capture_cooldown_spin)
        capture_row.addWidget(QtWidgets.QLabel("연속 실패:"))
        self.capture_confirm_spin = QtWidgets.QSpinBox()
        self.capture_confirm_spin.setRange(1, 10)
        self.capture_confirm_spin.setValue(self._fail_capture_confirmations)
        self.capture_confirm_spin.valueChanged.connect(self._on_capture_confirm_changed)
        capture_row.addWidget(self.capture_confirm_spin)
        capture_row.addWidget(QtWidgets.QLabel("캡처 제한(장):"))
        self.capture_limit_edit = QtWidgets.QLineEdit()
        self.capture_limit_edit.setPlaceholderText("제한 없음")
        self.capture_limit_edit.setFixedWidth(70)
        int_validator = QtGui.QIntValidator(1, 9999, self.capture_limit_edit)
        self.capture_limit_edit.setValidator(int_validator)
        self.capture_limit_edit.textChanged.connect(self._on_capture_limit_changed)
        capture_row.addWidget(self.capture_limit_edit)
        self.capture_hotkey_label = QtWidgets.QLabel("Hotkey: Ctrl+F12")
        self.capture_hotkey_label.setStyleSheet("color: gray;")
        capture_row.addWidget(self.capture_hotkey_label)
        capture_row.addStretch()
        cond_layout.addLayout(capture_row)
        compare_row = QtWidgets.QHBoxLayout()
        compare_row.addWidget(QtWidgets.QLabel("색상 대조 (HEX):"))
        self.condition_color_compare_edit = QtWidgets.QLineEdit()
        self.condition_color_compare_edit.setPlaceholderText("예: ff00aa")
        _setup_hex_line_edit(self.condition_color_compare_edit)
        compare_row.addWidget(self.condition_color_compare_edit)
        self.condition_color_compare_btn = QtWidgets.QPushButton("조건과 대조")
        self.condition_color_compare_btn.clicked.connect(self._on_condition_compare_color)
        compare_row.addWidget(self.condition_color_compare_btn)
        self.condition_compare_reset_btn = QtWidgets.QPushButton("초기화")
        self.condition_compare_reset_btn.clicked.connect(self._on_condition_compare_reset)
        compare_row.addWidget(self.condition_compare_reset_btn)
        compare_row.addStretch()
        cond_layout.addLayout(compare_row)
        self.condition_tree = QtWidgets.QTreeWidget()
        self.condition_tree.setHeaderLabels(["노드", "결과", "세부"])
        self.condition_tree.setRootIsDecorated(True)
        self.condition_tree.setIndentation(18)
        self.condition_tree.setColumnWidth(0, 260)
        self.condition_tree.setColumnWidth(1, 100)
        self.condition_tree.header().setStretchLastSection(True)
        cond_layout.addWidget(self.condition_tree, 1)
        layout.addWidget(self._make_section("조건 디버그", cond_group, "section_condition", default_open=True))

        self.pixel_status = QtWidgets.QLabel("픽셀 테스트: -")
        self.pixel_status.setWordWrap(True)
        self.pixel_status.setFrameShape(QtWidgets.QFrame.Shape.Panel)
        self.pixel_status.setFrameShadow(QtWidgets.QFrame.Shadow.Sunken)
        self.pixel_status.setAlignment(QtCore.Qt.AlignmentFlag.AlignLeft | QtCore.Qt.AlignmentFlag.AlignVCenter)

        test_group = QtWidgets.QGroupBox("픽셀 테스트 입력")
        test_layout = QtWidgets.QGridLayout(test_group)
        self.region_input = QtWidgets.QLineEdit("0,0,100,100")
        self.color_input = QtWidgets.QLineEdit("ff0000")
        _setup_hex_line_edit(self.color_input)
        self.tol_spin = QtWidgets.QSpinBox()
        self.tol_spin.setRange(0, 255)
        self.tol_spin.setValue(self._tolerance)
        self.tol_spin.valueChanged.connect(self._on_tolerance_changed)
        self.expect_combo = QtWidgets.QComboBox()
        self.expect_combo.addItem("색상이 있을 때 참", True)
        self.expect_combo.addItem("색상이 없을 때 참", False)
        self.start_btn = QtWidgets.QPushButton("테스트 시작")
        self.stop_btn = QtWidgets.QPushButton("테스트 중지")
        self.stop_btn.setEnabled(False)
        test_layout.addWidget(QtWidgets.QLabel("Region x,y,w,h"), 0, 0)
        test_layout.addWidget(self.region_input, 0, 1)
        test_layout.addWidget(QtWidgets.QLabel("색상 (HEX RRGGBB)"), 1, 0)
        test_layout.addWidget(self.color_input, 1, 1)
        test_layout.addWidget(QtWidgets.QLabel("Tolerance"), 2, 0)
        test_layout.addWidget(self.tol_spin, 2, 1)
        test_layout.addWidget(QtWidgets.QLabel("기대 상태"), 3, 0)
        test_layout.addWidget(self.expect_combo, 3, 1)
        test_layout.addWidget(QtWidgets.QLabel("색상 대조 (HEX)"), 4, 0)
        btn_row = QtWidgets.QHBoxLayout()
        btn_row.addStretch()
        btn_row.addWidget(self.start_btn)
        btn_row.addWidget(self.stop_btn)
        test_layout.addLayout(btn_row, 4, 0, 1, 2)
        test_wrap = QtWidgets.QWidget()
        tw_layout = QtWidgets.QVBoxLayout(test_wrap)
        tw_layout.setContentsMargins(0, 0, 0, 0)
        tw_layout.addWidget(self.pixel_status)
        tw_layout.addWidget(test_group)
        layout.addWidget(self._make_section("픽셀 테스트", test_wrap, "section_pixel", default_open=True))

        self.start_btn.clicked.connect(self._start_test)
        self.stop_btn.clicked.connect(self._stop_test)

        var_group = QtWidgets.QGroupBox("실시간 변수")
        var_group_layout = QtWidgets.QVBoxLayout(var_group)
        self.var_table = QtWidgets.QTableWidget(0, 3)
        self.var_table.setHorizontalHeaderLabels(["이름", "값", "업데이트"])
        self.var_table.horizontalHeader().setStretchLastSection(True)
        self.var_table.verticalHeader().setVisible(False)
        self.var_table.setEditTriggers(QtWidgets.QAbstractItemView.EditTrigger.NoEditTriggers)
        var_group_layout.addWidget(self.var_table)
        layout.addWidget(self._make_section("실시간 변수", var_group, "section_vars", default_open=True))

        layout.addWidget(QtWidgets.QLabel("최근 로그/이벤트"))
        self.log_view = QtWidgets.QTextEdit()
        self.log_view.setReadOnly(True)
        self.log_view.setAcceptRichText(True)
        self.log_view.setFont(QtGui.QFontDatabase.systemFont(QtGui.QFontDatabase.SystemFont.FixedFont))
        layout.addWidget(self.log_view, 1)

        self.resize(900, 600)

    def show_and_raise(self):
        self.show()
        self.raise_()
        self.activateWindow()

    def _restore_state(self, state: dict):
        if not isinstance(state, dict):
            return
        geo = state.get("geometry")
        if isinstance(geo, (list, tuple)) and len(geo) == 4:
            try:
                x, y, w, h = [int(v) for v in geo]
                self.setGeometry(x, y, w, h)
            except Exception:
                pass
        try:
            self._interval_ms = int(state.get("interval", self._interval_ms))
            self.interval_spin.setValue(self._interval_ms)
        except Exception:
            pass
        try:
            self._fail_capture_cooldown = float(state.get("fail_capture_cooldown", self._fail_capture_cooldown))
            self.capture_cooldown_spin.setValue(self._fail_capture_cooldown)
        except Exception:
            pass
        try:
            self._fail_capture_confirmations = int(state.get("fail_capture_confirmations", self._fail_capture_confirmations))
            self.capture_confirm_spin.setValue(self._fail_capture_confirmations)
        except Exception:
            pass
        self._fail_capture_enabled = bool(state.get("fail_capture_enabled", False))
        limit = state.get("fail_capture_limit")
        try:
            self._fail_capture_limit = int(limit) if limit not in (None, "", False) else None
        except Exception:
            self._fail_capture_limit = None
        self.capture_limit_edit.setText("" if self._fail_capture_limit is None else str(self._fail_capture_limit))
        self._refresh_capture_ui()
        try:
            self._tolerance = int(state.get("tolerance", self._tolerance))
            self.tol_spin.setValue(self._tolerance)
        except Exception:
            pass
        if isinstance(state.get("test_region"), str):
            self.region_input.setText(state.get("test_region"))
        if isinstance(state.get("test_color"), str):
            self.color_input.setText(state.get("test_color"))
        if state.get("test_expect") is not None:
            idx = self.expect_combo.findData(bool(state.get("test_expect")))
            if idx >= 0:
                self.expect_combo.setCurrentIndex(idx)
        sections = state.get("sections") or {}
        for key, btn in self._section_controls.items():
            opened = bool(sections.get(key, True))
            btn.blockSignals(True)
            btn.setChecked(opened)
            btn.blockSignals(False)
            try:
                btn.toggled.emit(opened)
            except Exception:
                pass
        if state.get("visible"):
            QtCore.QTimer.singleShot(0, self.show_and_raise)

    def _collect_state(self) -> dict:
        g = self.geometry()
        return {
            "geometry": [g.x(), g.y(), g.width(), g.height()],
            "visible": self.isVisible(),
            "interval": int(self.interval_spin.value()),
            "tolerance": int(self.tol_spin.value()),
            "test_region": self.region_input.text().strip(),
            "test_color": self.color_input.text().strip(),
            "test_expect": bool(self.expect_combo.currentData()) if self.expect_combo.currentIndex() >= 0 else True,
            "fail_capture_enabled": self._fail_capture_enabled,
            "fail_capture_cooldown": float(self.capture_cooldown_spin.value()),
            "fail_capture_confirmations": int(self.capture_confirm_spin.value()),
            "fail_capture_limit": self._fail_capture_limit,
            "sections": {k: btn.isChecked() for k, btn in self._section_controls.items()},
        }

    def closeEvent(self, event: QtGui.QCloseEvent):
        self.stop_condition_debug()
        if callable(self._close_cb):
            try:
                self._close_cb()
            except Exception:
                pass
        if self._save_state_cb:
            state = self._collect_state()
            state["visible"] = False  # 닫을 때는 다음 시작 시 자동 표시하지 않도록 저장
            self._save_state_cb(state)
        self.hide()
        event.accept()
        return super().closeEvent(event)

    def _set_state_labels(self, state: dict):
        running = state.get("running", False)
        active = state.get("active", False)
        paused = state.get("paused", False)
        self.state_label.setText(f"엔진: {'실행' if running else '정지'} | {'활성' if active else '비활성'}")
        self.state_label.setStyleSheet(f"color: {'limegreen' if active else 'gray'}; font-weight: bold;")
        self.pause_label.setText(f"일시정지: {'ON' if paused else 'OFF'}")
        self.pause_label.setStyleSheet(f"color: {'orange' if paused else 'skyblue'}; font-weight: bold;")

    def _set_current_path(self, text: str):
        # 표시하지 않음(요청으로 숨김)
        return

    def _extract_seq_path(self, event: dict) -> str | None:
        seq_chain = event.get("seq_chain")
        if isinstance(seq_chain, (list, tuple)) and seq_chain:
            return "-".join(str(int(n)) for n in seq_chain if isinstance(n, (int, float)))
        path_list = event.get("path") or []
        nums: list[int] = []
        for seg in path_list:
            if not isinstance(seg, str):
                continue
            if ":" in seg:
                head = seg.split(":", 1)[0]
                if head.isdigit():
                    try:
                        nums.append(int(head) + 1)
                        continue
                    except Exception:
                        pass
            if "[" in seg and "]" in seg:
                try:
                    inner = seg.split("[", 1)[1].split("]", 1)[0]
                    if inner.isdigit():
                        nums.append(int(inner) + 1)
                        continue
                except Exception:
                    pass
        if nums:
            # 중복 연속 숫자는 한번만
            dedup: list[int] = []
            for n in nums:
                if not dedup or dedup[-1] != n:
                    dedup.append(n)
            return "-".join(str(n) for n in dedup)
        return None

    def _append_log_line(self, text: str, seq: int | None = None, *, rich: bool = False):
        ts = _format_dt()
        self._log_seq += 1
        prefix = f"[{self._log_seq} {ts}]"
        entry = f"{prefix} {text}"
        self._log_buffer.append((entry, rich))
        if len(self._log_buffer) > self._max_logs:
            self._log_buffer = self._log_buffer[-self._max_logs :]

        def _to_html(item: tuple[str, bool]) -> str:
            content, is_rich = item
            return content if is_rich else html.escape(content).replace("\n", "<br>")

        html_text = "<br>".join(_to_html(item) for item in self._log_buffer)
        self.log_view.setHtml(html_text)
        # 즉시, 그리고 이벤트 루프 이후 한 번 더 스크롤을 맨 아래로 이동시켜 항상 최신 로그를 표시
        sb = self.log_view.verticalScrollBar()
        sb.setValue(sb.maximum())
        try:
            cursor = self.log_view.textCursor()
            cursor.movePosition(QtGui.QTextCursor.MoveOperation.End)
            self.log_view.setTextCursor(cursor)
        except Exception:
            pass
        QtCore.QTimer.singleShot(0, lambda: self.log_view.verticalScrollBar().setValue(self.log_view.verticalScrollBar().maximum()))

    def _collect_pixel_samples(self, tree: dict | None, *, only_failed: bool = False, dedup_by_coord: bool = False) -> list[str]:
        if not tree:
            return []
        samples: list[str] = []
        seen: set[tuple[int, int]] = set()

        def _norm_coord(coord):
            if isinstance(coord, (list, tuple)) and len(coord) == 2:
                try:
                    return (int(coord[0]), int(coord[1]))
                except Exception:
                    return None
            return None

        def _walk(node):
            if not isinstance(node, dict):
                return
            if node.get("type") == "pixel":
                if only_failed and node.get("result") is True:
                    pass
                else:
                    detail = node.get("detail", {}).get("pixel") or {}
                    coord = _norm_coord(detail.get("sample_coord") or detail.get("coord"))
                    if dedup_by_coord and coord and coord in seen:
                        return
                    sample = detail.get("sample_color")
                    if isinstance(sample, (list, tuple)) and len(sample) == 3:
                        hex_txt = "#" + "".join(f"{int(c):02x}" for c in sample)
                        if coord:
                            samples.append(f"{coord[0]},{coord[1]} [{hex_txt}]")
                        else:
                            samples.append(hex_txt)
                        if dedup_by_coord and coord:
                            seen.add(coord)
            for child in node.get("children") or []:
                _walk(child)
            for child in node.get("on_true") or []:
                _walk(child)
            for child in node.get("on_false") or []:
                _walk(child)

        _walk(tree)
        return samples

    def _failed_pixel_details(self, tree: dict | None, *, dedup_by_coord: bool = False) -> list[dict]:
        if not tree:
            return []
        items: list[dict] = []
        seen: set[tuple[int, int]] = set()

        def _norm_coord(coord):
            if isinstance(coord, (list, tuple)) and len(coord) == 2:
                try:
                    return (int(coord[0]), int(coord[1]))
                except Exception:
                    return None
            return None

        def _walk(node: dict):
            if not isinstance(node, dict):
                return
            if node.get("type") == "pixel":
                if only_failed and node.get("result") is True:
                    pass
                else:
                    detail = node.get("detail", {}).get("pixel") or {}
                    coord = _norm_coord(detail.get("sample_coord") or detail.get("coord"))
                    if dedup_by_coord and coord and coord in seen:
                        return
                    target = detail.get("color")
                    sample = detail.get("sample_color")
                    tol = int(detail.get("tolerance", 0))
                    expect_exists = bool(detail.get("expect_exists", True))
                    if isinstance(sample, (list, tuple)) and len(sample) == 3 and isinstance(target, (list, tuple)) and len(target) == 3:
                        diff = max(abs(int(sample[i]) - int(target[i])) for i in range(3))
                    else:
                        diff = None
                    need = None
                    if diff is not None:
                        need = f"tol>={diff}" if expect_exists else f"tol<{diff}"
                    items.append(
                        {
                            "name": node.get("name") or _condition_type_label("pixel"),
                            "coord": coord,
                            "target": target,
                            "sample": sample,
                            "tolerance": tol,
                            "diff": diff,
                            "expect_exists": expect_exists,
                            "need": need,
                        }
                    )
                    if dedup_by_coord and coord:
                        seen.add(coord)
            for child in node.get("children") or []:
                _walk(child)
            for child in node.get("on_true") or []:
                _walk(child)
            for child in node.get("on_false") or []:
                _walk(child)

        _walk(tree)
        return items

    def _failed_pixel_details(self, tree: dict | None, *, dedup_by_coord: bool = False) -> list[dict]:
        if not tree:
            return []
        items: list[dict] = []
        seen: set[tuple[int, int]] = set()

        def _norm_coord(coord):
            if isinstance(coord, (list, tuple)) and len(coord) == 2:
                try:
                    return (int(coord[0]), int(coord[1]))
                except Exception:
                    return None
            return None

        def _walk(node: dict):
            if not isinstance(node, dict):
                return
            if node.get("type") == "pixel":
                if node.get("result") is True:
                    pass
                else:
                    detail = node.get("detail", {}).get("pixel") or {}
                    coord = _norm_coord(detail.get("sample_coord") or detail.get("coord"))
                    if dedup_by_coord and coord and coord in seen:
                        return
                    target = detail.get("color")
                    sample = detail.get("sample_color")
                    tol = int(detail.get("tolerance", 0))
                    expect_exists = bool(detail.get("expect_exists", True))
                    if isinstance(sample, (list, tuple)) and len(sample) == 3 and isinstance(target, (list, tuple)) and len(target) == 3:
                        diff = max(abs(int(sample[i]) - int(target[i])) for i in range(3))
                    else:
                        diff = None
                    items.append(
                        {
                            "name": node.get("name") or _condition_type_label("pixel"),
                            "coord": coord,
                            "target": target,
                            "sample": sample,
                            "tolerance": tol,
                            "diff": diff,
                            "expect_exists": expect_exists,
                        }
                    )
                    if dedup_by_coord and coord:
                        seen.add(coord)
            for child in node.get("children") or []:
                _walk(child)
            for child in node.get("on_true") or []:
                _walk(child)
            for child in node.get("on_false") or []:
                _walk(child)

        _walk(tree)
        return items

    def _failed_pixel_details(self, tree: dict | None, *, dedup_by_coord: bool = False) -> list[dict]:
        if not tree:
            return []
        items: list[dict] = []
        seen: set[tuple[int, int]] = set()

        def _norm_coord(coord):
            if isinstance(coord, (list, tuple)) and len(coord) == 2:
                try:
                    return (int(coord[0]), int(coord[1]))
                except Exception:
                    return None
            return None

        def _walk(node: dict):
            if not isinstance(node, dict):
                return
            if node.get("type") == "pixel":
                if node.get("result") is True:
                    pass
                else:
                    detail = node.get("detail", {}).get("pixel") or {}
                    coord = _norm_coord(detail.get("sample_coord") or detail.get("coord"))
                    if dedup_by_coord and coord and coord in seen:
                        return
                    target = detail.get("color")
                    sample = detail.get("sample_color")
                    tol = int(detail.get("tolerance", 0))
                    expect_exists = bool(detail.get("expect_exists", True))
                    if isinstance(sample, (list, tuple)) and len(sample) == 3 and isinstance(target, (list, tuple)) and len(target) == 3:
                        diff = max(abs(int(sample[i]) - int(target[i])) for i in range(3))
                    else:
                        diff = None
                    items.append(
                        {
                            "name": node.get("name") or _condition_type_label("pixel"),
                            "coord": coord,
                            "target": target,
                            "sample": sample,
                            "tolerance": tol,
                            "diff": diff,
                            "expect_exists": expect_exists,
                        }
                    )
                    if dedup_by_coord and coord:
                        seen.add(coord)
            for child in node.get("children") or []:
                _walk(child)
            for child in node.get("on_true") or []:
                _walk(child)
            for child in node.get("on_false") or []:
                _walk(child)

        _walk(tree)
        return items

    def _collect_pixel_coords(self, tree: dict | None, *, only_failed: bool = False, dedup_by_coord: bool = False) -> list[tuple[int, int]]:
        if not tree:
            return []
        coords: list[tuple[int, int]] = []
        seen: set[tuple[int, int]] = set()

        def _norm_coord(coord):
            if isinstance(coord, (list, tuple)) and len(coord) == 2:
                try:
                    return (int(coord[0]), int(coord[1]))
                except Exception:
                    return None
            return None

        def _walk(node: dict):
            if not isinstance(node, dict):
                return
            if node.get("type") == "pixel":
                if only_failed and node.get("result") is True:
                    pass
                else:
                    detail = node.get("detail", {}).get("pixel") or {}
                    coord = _norm_coord(detail.get("sample_coord") or detail.get("coord"))
                    if coord:
                        if dedup_by_coord and coord in seen:
                            return
                        coords.append(coord)
                        if dedup_by_coord:
                            seen.add(coord)
            for child in node.get("children") or []:
                _walk(child)
            for child in node.get("on_true") or []:
                _walk(child)
            for child in node.get("on_false") or []:
                _walk(child)

        _walk(tree)
        return coords

    def _failed_pixel_details(self, tree: dict | None, *, dedup_by_coord: bool = False) -> list[dict]:
        if not tree:
            return []
        items: list[dict] = []
        seen: set[tuple[int, int]] = set()

        def _norm_coord(coord):
            if isinstance(coord, (list, tuple)) and len(coord) == 2:
                try:
                    return (int(coord[0]), int(coord[1]))
                except Exception:
                    return None
            return None

        def _walk(node: dict):
            if not isinstance(node, dict):
                return
            if node.get("type") == "pixel":
                if node.get("result") is True:
                    pass
                else:
                    detail = node.get("detail", {}).get("pixel") or {}
                    coord = _norm_coord(detail.get("sample_coord") or detail.get("coord"))
                    if dedup_by_coord and coord and coord in seen:
                        return
                    target = detail.get("color")
                    sample = detail.get("sample_color")
                    tol = int(detail.get("tolerance", 0))
                    expect_exists = bool(detail.get("expect_exists", True))
                    if isinstance(sample, (list, tuple)) and len(sample) == 3 and isinstance(target, (list, tuple)) and len(target) == 3:
                        diff = max(abs(int(sample[i]) - int(target[i])) for i in range(3))
                    else:
                        diff = None
                    items.append(
                        {
                            "name": node.get("name") or _condition_type_label("pixel"),
                            "coord": coord,
                            "target": target,
                            "sample": sample,
                            "tolerance": tol,
                            "diff": diff,
                            "expect_exists": expect_exists,
                        }
                    )
                    if dedup_by_coord and coord:
                        seen.add(coord)
            for child in node.get("children") or []:
                _walk(child)
            for child in node.get("on_true") or []:
                _walk(child)
            for child in node.get("on_false") or []:
                _walk(child)

        _walk(tree)
        return items

    def _collect_pixel_results(self, tree: dict | None) -> list[bool | None]:
        if not tree:
            return []
        results: list[bool | None] = []

        def _walk(node: dict):
            if not isinstance(node, dict):
                return
            if node.get("type") == "pixel":
                results.append(node.get("result"))
            for child in node.get("children") or []:
                _walk(child)
            for child in node.get("on_true") or []:
                _walk(child)
            for child in node.get("on_false") or []:
                _walk(child)

        _walk(tree)
        return results

    def _failed_pixel_bbox(self, tree: dict | None):
        if not tree:
            return None
        boxes: list[tuple[int, int, int, int]] = []

        def _walk(node: dict):
            if not isinstance(node, dict):
                return
            if node.get("type") == "pixel":
                if node.get("result") is True:
                    pass
                else:
                    detail = node.get("detail", {}).get("pixel") or {}
                    region = detail.get("region")
                    if isinstance(region, (list, tuple)) and len(region) == 4:
                        try:
                            x, y, w, h = (int(region[0]), int(region[1]), int(region[2]), int(region[3]))
                            if w > 0 and h > 0:
                                boxes.append((x, y, w, h))
                        except Exception:
                            pass
            for child in node.get("children") or []:
                _walk(child)
            for child in node.get("on_true") or []:
                _walk(child)
            for child in node.get("on_false") or []:
                _walk(child)

        _walk(tree)
        if not boxes:
            return None
        min_x = min(b[0] for b in boxes)
        min_y = min(b[1] for b in boxes)
        max_x = max(b[0] + b[2] for b in boxes)
        max_y = max(b[1] + b[3] for b in boxes)
        return (min_x, min_y, max_x - min_x, max_y - min_y)

    def _failed_pixel_details(self, tree: dict | None, *, dedup_by_coord: bool = False) -> list[dict]:
        if not tree:
            return []
        items: list[dict] = []
        seen: set[tuple[int, int]] = set()

        def _norm_coord(coord):
            if isinstance(coord, (list, tuple)) and len(coord) == 2:
                try:
                    return (int(coord[0]), int(coord[1]))
                except Exception:
                    return None
            return None

        def _walk(node: dict):
            if not isinstance(node, dict):
                return
            if node.get("type") == "pixel":
                if node.get("result") is True:
                    pass
                else:
                    detail = node.get("detail", {}).get("pixel") or {}
                    coord = _norm_coord(detail.get("sample_coord") or detail.get("coord"))
                    if dedup_by_coord and coord and coord in seen:
                        return
                    target = detail.get("color")
                    sample = detail.get("sample_color")
                    tol = int(detail.get("tolerance", 0))
                    expect_exists = bool(detail.get("expect_exists", True))
                    if isinstance(sample, (list, tuple)) and len(sample) == 3 and isinstance(target, (list, tuple)) and len(target) == 3:
                        diff = max(abs(int(sample[i]) - int(target[i])) for i in range(3))
                    else:
                        diff = None
                    items.append(
                        {
                            "name": node.get("name") or _condition_type_label("pixel"),
                            "coord": coord,
                            "target": target,
                            "sample": sample,
                            "tolerance": tol,
                            "diff": diff,
                            "expect_exists": expect_exists,
                        }
                    )
                    if dedup_by_coord and coord:
                        seen.add(coord)
            for child in node.get("children") or []:
                _walk(child)
            for child in node.get("on_true") or []:
                _walk(child)
            for child in node.get("on_false") or []:
                _walk(child)

        _walk(tree)
        return items

    def _first_failed_pixel_image(self, tree: dict | None):
        if not tree:
            return None

        def _walk(node: dict):
            if not isinstance(node, dict):
                return None
            if node.get("type") == "pixel" and node.get("result") is not True:
                detail = node.get("detail", {}).get("pixel") or {}
                data = detail.get("image_png")
                region = detail.get("region")
                if data and isinstance(data, (bytes, bytearray)) and isinstance(region, (list, tuple)) and len(region) == 4:
                    try:
                        x, y, w, h = (int(region[0]), int(region[1]), int(region[2]), int(region[3]))
                        if w > 0 and h > 0:
                            return ((x, y, w, h), bytes(data))
                    except Exception:
                        pass
            for child in node.get("children") or []:
                found = _walk(child)
                if found:
                    return found
            for child in node.get("on_true") or []:
                found = _walk(child)
                if found:
                    return found
            for child in node.get("on_false") or []:
                found = _walk(child)
                if found:
                    return found
            return None

        return _walk(tree)

    def _collect_pixel_coords(self, tree: dict | None, *, only_failed: bool = False, dedup_by_coord: bool = False) -> list[tuple[int, int]]:
        if not tree:
            return []
        coords: list[tuple[int, int]] = []
        seen: set[tuple[int, int]] = set()

        def _norm_coord(coord):
            if isinstance(coord, (list, tuple)) and len(coord) == 2:
                try:
                    return (int(coord[0]), int(coord[1]))
                except Exception:
                    return None
            return None

        def _walk(node: dict):
            if not isinstance(node, dict):
                return
            if node.get("type") == "pixel":
                if only_failed and node.get("result") is True:
                    pass
                else:
                    detail = node.get("detail", {}).get("pixel") or {}
                    coord = _norm_coord(detail.get("sample_coord") or detail.get("coord"))
                    if coord:
                        if dedup_by_coord and coord in seen:
                            return
                        coords.append(coord)
                        if dedup_by_coord:
                            seen.add(coord)
            for child in node.get("children") or []:
                _walk(child)
            for child in node.get("on_true") or []:
                _walk(child)
            for child in node.get("on_false") or []:
                _walk(child)

        _walk(tree)
        return coords

    def _failed_pixel_bbox(self, tree: dict | None):
        if not tree:
            return None
        boxes: list[tuple[int, int, int, int]] = []

        def _walk(node: dict):
            if not isinstance(node, dict):
                return
            if node.get("type") == "pixel":
                if node.get("result") is True:
                    pass
                else:
                    detail = node.get("detail", {}).get("pixel") or {}
                    region = detail.get("region")
                    if isinstance(region, (list, tuple)) and len(region) == 4:
                        try:
                            x, y, w, h = (int(region[0]), int(region[1]), int(region[2]), int(region[3]))
                            if w > 0 and h > 0:
                                boxes.append((x, y, w, h))
                        except Exception:
                            pass
            for child in node.get("children") or []:
                _walk(child)
            for child in node.get("on_true") or []:
                _walk(child)
            for child in node.get("on_false") or []:
                _walk(child)

        _walk(tree)
        if not boxes:
            return None
        min_x = min(b[0] for b in boxes)
        min_y = min(b[1] for b in boxes)
        max_x = max(b[0] + b[2] for b in boxes)
        max_y = max(b[1] + b[3] for b in boxes)
        return (min_x, min_y, max_x - min_x, max_y - min_y)

    def _first_failed_pixel_image(self, tree: dict | None):
        if not tree:
            return None

        def _walk(node: dict):
            if not isinstance(node, dict):
                return None
            if node.get("type") == "pixel" and node.get("result") is not True:
                detail = node.get("detail", {}).get("pixel") or {}
                data = detail.get("image_png")
                region = detail.get("region")
                if data and isinstance(data, (bytes, bytearray)) and isinstance(region, (list, tuple)) and len(region) == 4:
                    try:
                        x, y, w, h = (int(region[0]), int(region[1]), int(region[2]), int(region[3]))
                        if w > 0 and h > 0:
                            return ((x, y, w, h), bytes(data))
                    except Exception:
                        pass
            for child in node.get("children") or []:
                found = _walk(child)
                if found:
                    return found
            for child in node.get("on_true") or []:
                found = _walk(child)
                if found:
                    return found
            for child in node.get("on_false") or []:
                found = _walk(child)
                if found:
                    return found
            return None

        return _walk(tree)

    def _on_interval_changed(self, value: int):
        self._interval_ms = int(value)
        if callable(self._interval_changed_cb):
            try:
                self._interval_changed_cb(self._interval_ms)
            except Exception:
                pass
        if self._condition_timer.isActive():
            self._condition_timer.setInterval(self._interval_ms)
        if self._save_state_cb:
            try:
                self._save_state_cb(self._collect_state())
            except Exception:
                pass

    def _on_tolerance_changed(self, value: int):
        self._tolerance = int(value)
        if callable(self._tolerance_changed_cb):
            try:
                self._tolerance_changed_cb(self._tolerance)
            except Exception:
                pass
        if self._save_state_cb:
            try:
                self._save_state_cb(self._collect_state())
            except Exception:
                pass

    def _clear_all(self):
        self.var_table.setRowCount(0)
        self._var_rows.clear()
        self._log_buffer.clear()
        self._log_seq = 0
        self.log_view.clear()
        self.pixel_status.setText("픽셀 테스트: -")
        self._reset_condition_debug_ui()

    def _reset_condition_debug_ui(self):
        self.condition_tree.clear()
        self.condition_state_label.setText("전체 결과: -")
        self.condition_state_label.setStyleSheet("color: gray;")
        self.condition_fail_label.setText("실패 경로: -")
        self.condition_stop_btn.setEnabled(bool(self._condition_eval_fn))
        self._last_condition_result = None
        self._last_capture_ts = 0.0
        self._refresh_capture_ui()

    def _refresh_capture_ui(self):
        on = self._fail_capture_enabled
        self.capture_toggle_btn.blockSignals(True)
        self.capture_toggle_btn.setChecked(on)
        self.capture_toggle_btn.blockSignals(False)
        self.capture_toggle_btn.setText(f"실패 시 캡처 {'ON' if on else 'OFF'}")
        color = "limegreen" if on else "gray"
        self.capture_toggle_btn.setStyleSheet(f"color: {color}; font-weight: bold;")
        # OFF에서도 설정을 바꿀 수 있도록 항상 활성화
        self.capture_cooldown_spin.setEnabled(True)
        self.capture_confirm_spin.setEnabled(True)
        self.capture_limit_edit.setEnabled(True)

    def _on_capture_toggle(self, checked: bool):
        self._fail_capture_enabled = bool(checked)
        self._last_condition_result = None
        self._last_capture_ts = 0.0
        self._fail_capture_count = 0
        self._fail_capture_armed = False
        self._fail_capture_false_streak = 0
        if checked:
            self._set_condition_pending(label=self._condition_label)
        self._refresh_capture_ui()
        self._append_log_line(f"[캡처] 조건 실패 캡처 {'ON (참 대기중)' if checked else 'OFF'}")
        if self._save_state_cb:
            try:
                self._save_state_cb(self._collect_state())
            except Exception:
                pass

    def _on_capture_cooldown_changed(self, value: float):
        self._fail_capture_cooldown = float(value)
        if self._save_state_cb:
            try:
                self._save_state_cb(self._collect_state())
            except Exception:
                pass

    def _on_capture_confirm_changed(self, value: int):
        self._fail_capture_confirmations = max(1, int(value))
        self._fail_capture_false_streak = 0
        if self._save_state_cb:
            try:
                self._save_state_cb(self._collect_state())
            except Exception:
                pass

    def _on_capture_limit_changed(self, text: str):
        txt = text.strip()
        if not txt:
            self._fail_capture_limit = None
        else:
            try:
                self._fail_capture_limit = max(1, int(txt))
            except Exception:
                self._fail_capture_limit = None
        if self._save_state_cb:
            try:
                self._save_state_cb(self._collect_state())
            except Exception:
                pass

    def toggle_fail_capture_from_hotkey(self):
        self._on_capture_toggle(not self._fail_capture_enabled)

    def _set_test_inputs(self, config: dict):
        if not isinstance(config, dict):
            return
        if config.get("region_raw"):
            self.region_input.setText(str(config.get("region_raw")))
        elif config.get("region"):
            self.region_input.setText(",".join(str(v) for v in config.get("region")))
        if config.get("color_raw"):
            self.color_input.setText(str(config.get("color_raw")))
        elif config.get("color"):
            try:
                self.color_input.setText(_rgb_to_hex(tuple(int(c) for c in config.get("color"))))
            except Exception:
                pass
        if config.get("expect_exists") is not None:
            idx = self.expect_combo.findData(bool(config.get("expect_exists")))
            if idx >= 0:
                self.expect_combo.setCurrentIndex(idx)
        if config.get("tolerance") is not None:
            try:
                self.tol_spin.setValue(int(config.get("tolerance")))
            except Exception:
                pass
        if config.get("interval") is not None:
            try:
                self.interval_spin.setValue(int(config.get("interval")))
            except Exception:
                pass
        self._pending_label = config.get("label") or self._pending_label

    def start_condition_debug(self, eval_fn, *, label: str | None = None, stop_cb=None):
        self._condition_eval_fn = eval_fn
        self._condition_stop_cb = stop_cb
        self._condition_label = label or "조건 디버그"
        self._reset_condition_debug_ui()
        self._condition_timer.setInterval(self._interval_ms)
        self._condition_timer.start()
        self.condition_stop_btn.setEnabled(True)

    def stop_condition_debug(self, *, notify: bool = True):
        if self._condition_timer.isActive():
            self._condition_timer.stop()
        cb = self._condition_stop_cb if notify else None
        self._condition_eval_fn = None
        self._condition_stop_cb = None
        self._condition_label = "조건 디버그"
        self._reset_condition_debug_ui()
        if callable(cb):
            try:
                cb()
            except Exception:
                pass

    def _on_condition_stop_clicked(self):
        self.stop_condition_debug()

    def _tick_condition_debug(self):
        if not callable(self._condition_eval_fn):
            self.stop_condition_debug(notify=False)
            return
        try:
            payload = self._condition_eval_fn()
        except Exception as exc:
            self.condition_tree.clear()
            self._update_condition_status(None, error=str(exc))
            return
        if not isinstance(payload, dict):
            self.condition_tree.clear()
            self._update_condition_status(None, error="평가 결과를 읽을 수 없습니다.")
            return
        if payload.get("error"):
            self.condition_tree.clear()
            self._update_condition_status(None, error=str(payload.get("error")))
            return
        result_tree = payload.get("result")
        if not isinstance(result_tree, dict):
            self.condition_tree.clear()
            self._update_condition_status(None, error="조건 결과가 비어 있습니다.")
            return
        label = payload.get("label") or self._condition_label
        self._condition_label = label
        self._render_condition_tree(result_tree, label=label)
        self._maybe_capture_failure(result_tree, label=label)

    def _update_condition_status(self, result: bool | None, *, error: str | None = None, fail_text: str | None = None, label: str | None = None):
        lbl = label or self._condition_label
        if error:
            text = f"{lbl}: 오류"
            color = "orange"
        elif result is None:
            text = f"{lbl}: 대기"
            color = "gray"
        else:
            text = f"{lbl}: {'참' if result else '거짓'}"
            color = "limegreen" if result else "red"
        self.condition_state_label.setText(text)
        self.condition_state_label.setStyleSheet(f"color: {color}; font-weight: bold;")
        if error:
            self.condition_fail_label.setText(f"실패/오류: {error}")
        elif fail_text is not None:
            self.condition_fail_label.setText(f"실패 경로: {fail_text}" if fail_text else "실패 경로: -")

    def _render_condition_tree(self, tree: dict, *, label: str, compare_color: tuple[int, int, int] | None = None):
        self.condition_tree.clear()
        self._last_condition_tree = tree
        if compare_color is None:
            compare_color = self._compare_color_override
        root_item = self._build_condition_item(tree, compare_color=compare_color)
        if root_item:
            self.condition_tree.addTopLevelItem(root_item)
            self.condition_tree.expandAll()
        fail_path = self._find_first_failure_path(tree, [])
        fail_text = " > ".join(fail_path) if fail_path else "-"
        self._update_condition_status(tree.get("result"), fail_text=fail_text, label=label)

    def _set_condition_pending(self, label: str | None = None):
        """조건 디버그 영역을 '참 대기중' 상태로 초기화."""
        self._last_condition_tree = None
        self.condition_tree.clear()
        lbl = label or self._condition_label
        self.condition_state_label.setText(f"{lbl}: 참 대기중")
        self.condition_state_label.setStyleSheet("color: darkorange; font-weight: bold;")
        self.condition_fail_label.setText("실패 경로: -")
        self._last_condition_result = None

    def _maybe_capture_failure(self, tree: dict, *, label: str):
        if not self._fail_capture_enabled:
            self._last_condition_result = tree.get("result")
            return
        if not callable(self._fail_capture_cb):
            self._last_condition_result = tree.get("result")
            return
        result_now = bool(tree.get("result"))
        now = time.monotonic()
        if result_now:
            # 참을 본 이후부터만 거짓을 캡처
            self._fail_capture_armed = True
            self._fail_capture_false_streak = 0
            self._last_condition_result = result_now
            return
        # result_now is False
        if not self._fail_capture_armed:
            self._last_condition_result = result_now
            return
        pixel_results = self._collect_pixel_results(tree)
        all_pixels_failed = bool(pixel_results) and all(res is not True for res in pixel_results)
        if not all_pixels_failed:
            self._fail_capture_false_streak = 0
            self._last_condition_result = result_now
            return
        self._fail_capture_false_streak += 1
        should_capture = False
        reason = ""
        if self._last_condition_result:
            should_capture = self._fail_capture_false_streak >= self._fail_capture_confirmations
            reason = "transition"
        elif now - self._last_capture_ts >= max(0.0, self._fail_capture_cooldown):
            should_capture = self._fail_capture_false_streak >= self._fail_capture_confirmations
            reason = "cooldown"
        self._last_condition_result = result_now
        if not should_capture:
            return
        if self._fail_capture_limit is not None and self._fail_capture_count >= self._fail_capture_limit:
            if self._fail_capture_count == self._fail_capture_limit:
                self._append_log_line(f"[캡처] 제한 {self._fail_capture_limit}장에 도달하여 추가 캡처 중단")
                self._fail_capture_count += 1  # 한 번만 알림
            return
        self._fail_capture_false_streak += 1
        if self._fail_capture_false_streak < self._fail_capture_confirmations:
            self._last_condition_result = result_now
            return

        # 연속 실패 조건을 만족한 경우에만 캡처 실행
        self._last_capture_ts = now
        self._fail_capture_count += 1
        fail_path = " > ".join(self._find_first_failure_path(tree, []))
        try:
            self.condition_tree.viewport().repaint()
            self.repaint()
            QtWidgets.QApplication.processEvents(QtCore.QEventLoop.AllEvents, 50)
        except Exception:
            pass
        try:
            self._fail_capture_cb(
                {
                    "label": label,
                    "fail_path": fail_path,
                    "timestamp": time.time(),
                    "cooldown_reason": reason,
                    "result": False,
                    "tree": tree,
                }
            )
            self._append_log_line(f"[캡처] 조건 실패 캡처 실행 ({fail_path or '경로 없음'})")
        except Exception as exc:
            self._append_log_line(f"[캡처 오류] {exc}")
        self._fail_capture_false_streak = 0
        if self._fail_capture_limit is not None and self._fail_capture_count >= self._fail_capture_limit:
            self._append_log_line(f"[캡처] 제한 {self._fail_capture_limit}장에 도달하여 캡처 OFF")
            self._on_capture_toggle(False)
            return

    def _on_condition_compare_color(self):
        text = self.condition_color_compare_edit.text().strip()
        if not text:
            self._append_log_line("색상 대조: 색상을 입력하세요.")
            return
        try:
            color = _parse_hex_color(text)
        except Exception as exc:
            self._append_log_line(f"색상 대조 오류: {exc}")
            return
        self._compare_color_override = tuple(int(c) for c in color)
        compare_hex = _rgb_to_hex(self._compare_color_override) or "-"
        compare_chip = _color_chip_html(compare_hex if compare_hex != "-" else None)
        tree = self._last_condition_tree or {}
        if not tree:
            self._append_log_line("색상 대조: 조건 결과가 없습니다.")
            return

        def _walk(node):
            results = []
            if node.get("type") == "pixel":
                detail = node.get("detail", {}).get("pixel") or {}
                target = detail.get("color")
                tol = detail.get("tolerance", 0)
                expect_exists = detail.get("expect_exists", True)
                label = node.get("name") or _condition_type_label("pixel")
                if isinstance(target, (list, tuple)) and len(target) == 3:
                    diff = max(abs(int(target[i]) - int(color[i])) for i in range(3))
                    match = diff <= int(tol)
                    final = match if expect_exists else (not match)
                    need = None
                    if not final:
                        if expect_exists:
                            # 목표 색상이 있어야 하는데 diff가 tol을 초과한 경우
                            need = f"tol>={diff}"
                        else:
                            # 목표 색상이 없어야 하는데 tol이 너무 커서 match로 판정된 경우
                            need = f"tol<{diff}"
                    results.append((label, final, target, tol, diff, expect_exists, need))
            for child in node.get("children") or []:
                results.extend(_walk(child))
            for child in node.get("on_true") or []:
                results.extend(_walk(child))
            for child in node.get("on_false") or []:
                results.extend(_walk(child))
            return results

        results = _walk(tree)
        if not results:
            self._append_log_line("색상 대조: 픽셀 조건이 없습니다.")
            return
        all_failed = all(not final for final, *_rest in results)
        parts = []
        for label, final, target, tol, diff, expect_exists, need in results:
            tgt_hex = _rgb_to_hex(target) or "-"
            tgt_chip = _color_chip_html(tgt_hex if tgt_hex != "-" else None)
            expect_txt = "있음" if expect_exists else "없음"
            need_txt = f" 필요={need}" if need else ""
            parts.append(
                f"{label}: {'참' if final else '거짓'} (목표={tgt_hex} {tgt_chip} 기준={compare_hex} {compare_chip} tol={tol} 기대={expect_txt}{need_txt})"
            )
        summary = "; ".join(parts)
        prefix = "[전체=거짓]" if all_failed else "[전체=부분참]"
        self._append_log_line(f"색상 대조: {prefix} {summary}", rich=True)
        try:
            self._render_condition_tree(tree, label=self._condition_label, compare_color=self._compare_color_override)
        except Exception:
            pass

    def _on_condition_compare_reset(self):
        self._compare_color_override = None
        self.condition_color_compare_edit.clear()
        tree = self._last_condition_tree
        if tree:
            try:
                self._render_condition_tree(tree, label=self._condition_label, compare_color=None)
            except Exception:
                pass

    def _build_condition_item(self, node: dict, *, compare_color: tuple[int, int, int] | None = None) -> QtWidgets.QTreeWidgetItem:
        cond = node.get("cond")
        cond_type = node.get("type") or getattr(cond, "type", "")
        name = getattr(cond, "name", None) or node.get("name") or ""
        label = _condition_brief(cond) if isinstance(cond, Condition) else _condition_type_label(cond_type) if cond_type else "(조건)"
        result_bool = bool(node.get("result"))
        base_result = node.get("base_result")
        result_text = "참" if result_bool else "거짓"
        if base_result is not None and base_result != result_bool:
            result_text += f" / base={'참' if base_result else '거짓'}"
        # 비교 색상 결과 추가
        if compare_color and cond_type == "pixel":
            detail = node.get("detail", {}).get("pixel") or {}
            target = detail.get("color")
            tol = int(detail.get("tolerance", 0))
            expect_exists = detail.get("expect_exists", True)
            if isinstance(target, (list, tuple)) and len(target) == 3:
                diff = max(abs(int(target[i]) - int(compare_color[i])) for i in range(3))
                match = diff <= tol
                final = match if expect_exists else (not match)
                result_text = f"{result_text} / 대조={'참' if final else '거짓'} diff={diff}"
        detail_text = self._format_condition_detail(cond_type, node.get("detail") or {}, cond)
        item = QtWidgets.QTreeWidgetItem([label, result_text, detail_text])
        self._apply_condition_color(item, node.get("detail") or {}, result_bool)
        for child in node.get("children") or []:
            item.addChild(self._build_condition_item(child, compare_color=compare_color))
        if node.get("on_true"):
            true_header = QtWidgets.QTreeWidgetItem(["[참 분기]", "", ""])
            true_header.setForeground(0, QtGui.QBrush(QtGui.QColor("dodgerblue")))
            for child in node.get("on_true"):
                true_header.addChild(self._build_condition_item(child, compare_color=compare_color))
            item.addChild(true_header)
        if node.get("on_false"):
            false_header = QtWidgets.QTreeWidgetItem(["[거짓 분기]", "", ""])
            false_header.setForeground(0, QtGui.QBrush(QtGui.QColor("orange")))
            for child in node.get("on_false"):
                false_header.addChild(self._build_condition_item(child, compare_color=compare_color))
            item.addChild(false_header)
        if compare_color and cond_type in ("all", "any"):
            child_compare_results: list[bool] = []
            for idx in range(item.childCount()):
                child_item = item.child(idx)
                txt = child_item.text(1)
                if "[참 분기]" in child_item.text(0) or "[거짓 분기]" in child_item.text(0):
                    # 분기 헤더는 스킵
                    continue
                child_compare_results.append("대조=참" in (txt or ""))
            if child_compare_results:
                if cond_type == "all":
                    compare_ok = all(child_compare_results)
                else:
                    compare_ok = any(child_compare_results)
                item.setText(1, f"{item.text(1)} / 대조={'참' if compare_ok else '거짓'}")
        return item

    def _apply_condition_color(self, item: QtWidgets.QTreeWidgetItem, detail: dict, result: bool):
        # 색상 대조 여부와 관계없이 실제 결과(result)로 색상을 결정한다.
        if detail.get("error"):
            color = "orange"
        else:
            color = "limegreen" if result else "red"
        brush = QtGui.QBrush(QtGui.QColor(color))
        for col in range(item.columnCount()):
            item.setForeground(col, brush)

    def _format_condition_detail(self, cond_type: str, detail: dict, cond: Condition | None) -> str:
        if not detail:
            return ""
        if detail.get("error"):
            return f"오류: {detail.get('error')}"
        if cond_type == "pixel":
            pix = detail.get("pixel") or {}
            region = pix.get("region")
            color = pix.get("color")
            region_txt = ",".join(str(v) for v in region) if region else "-"
            color_txt = "#" + "".join(f"{c:02x}" for c in color) if isinstance(color, (list, tuple)) else "-"
            expect = "있음" if pix.get("expect_exists", True) else "없음"
            found = "있음" if pix.get("found") else "없음"
            tol = pix.get("tolerance")
            return f"영역={region_txt} 색상={color_txt} tol={tol} 기대={expect}/발견={found}"
        if cond_type == "var":
            var_info = detail.get("var") or {}
            op_txt = "!=" if var_info.get("operator") == "ne" else "=="
            return f"{var_info.get('name', '')} {op_txt} {var_info.get('expected', '')} (실제={var_info.get('actual')})"
        if cond_type == "timer":
            t = detail.get("timer") or {}
            op_txt = t.get("operator") or "ge"
            return f"타이머{t.get('slot')} {op_txt} {t.get('expected')} (현재={t.get('actual')})"
        if cond_type in ("all", "any"):
            grp = detail.get("group") or {}
            return f"{grp.get('mode', cond_type)} {grp.get('count', 0)}개"
        if detail.get("key"):
            key_info = detail.get("key")
            return f"{key_info.get('key')} ({key_info.get('mode')}) pressed={key_info.get('pressed')} prev={key_info.get('prev')}"
        return ""

    def _find_first_failure_path(self, node: dict, prefix: list[str]) -> list[str]:
        label = node.get("name") or _condition_type_label(node.get("type", "") or "") or "(조건)"
        current_path = prefix + [label]
        if not node.get("result", False):
            return current_path
        for child in (node.get("children") or []):
            fail = self._find_first_failure_path(child, current_path)
            if fail:
                return fail
        for child in (node.get("on_true") or []):
            fail = self._find_first_failure_path(child, current_path + ["[참 분기]"])
            if fail:
                return fail
        for child in (node.get("on_false") or []):
            fail = self._find_first_failure_path(child, current_path + ["[거짓 분기]"])
            if fail:
                return fail
        return []

    def _current_test_config(self) -> dict:
        expect_exists = bool(self.expect_combo.currentData()) if self.expect_combo.currentIndex() >= 0 else True
        return {
            "region_raw": self.region_input.text().strip(),
            "color_raw": self.color_input.text().strip(),
            "tolerance": int(self.tol_spin.value()),
            "expect_exists": expect_exists,
            "interval": int(self.interval_spin.value()),
            "label": self._pending_label or "디버거 테스트",
        }

    def _start_test(self):
        if self._testing:
            return
        # 시작 전에 이전 로그/스텝/변수 상태를 정리
        self._clear_all()
        config = self._current_test_config()
        try:
            region = _parse_region(config["region_raw"])
            color = _parse_hex_color(config["color_raw"])
        except Exception as exc:
            QtWidgets.QMessageBox.warning(self, "입력 오류", str(exc))
            return
        config["region"] = region
        config["color"] = color
        if not callable(self._start_test_cb):
            QtWidgets.QMessageBox.information(self, "지원 안 함", "테스트 콜백이 없습니다.")
            return
        self._testing = True
        self.start_btn.setEnabled(False)
        self.stop_btn.setEnabled(True)
        self._start_test_cb(config, self._on_test_stopped)

    def _stop_test(self):
        if callable(self._stop_test_cb):
            self._stop_test_cb()
        self._on_test_stopped()

    def _on_test_stopped(self):
        self._testing = False
        self.start_btn.setEnabled(True)
        self.stop_btn.setEnabled(False)

    def _update_variable(self, event: dict):
        cat = event.get("category", "")
        name = event.get("name") or ""
        key = f"{cat}:{name}"
        value = event.get("value", "")
        ts = _format_dt()
        row = self._var_rows.get(key, -1)
        if row < 0:
            row = self.var_table.rowCount()
            self.var_table.insertRow(row)
            self._var_rows[key] = row
            self.var_table.setItem(row, 0, QtWidgets.QTableWidgetItem(f"{cat}:{name}"))
            self.var_table.setItem(row, 1, QtWidgets.QTableWidgetItem(str(value)))
            self.var_table.setItem(row, 2, QtWidgets.QTableWidgetItem(ts))
        else:
            self.var_table.item(row, 1).setText(str(value))
            self.var_table.item(row, 2).setText(ts)

    def _update_pixel_status(self, event: dict):
        source = event.get("source") or "test"
        label = event.get("label") or "-"
        res = event.get("result")
        expect = event.get("expect_exists", True)
        found = event.get("found")
        tol = event.get("tolerance")
        region = event.get("region")
        color = event.get("color")
        region_txt = ",".join(str(v) for v in region) if region else "-"
        color_txt = "#" + "".join(f"{c:02x}" for c in color) if isinstance(color, (list, tuple)) else "-"
        tol_txt = f"tol={tol}" if tol is not None else f"tol={self._tolerance}"
        msg = (
            f"{source} / {label}: {'성공' if res else '실패'} "
            f"(기대={'있음' if expect else '없음'}, 발견={'있음' if found else '없음'}, {tol_txt}, 영역={region_txt}, 색상={color_txt})"
        )
        self.pixel_status.setText(f"픽셀 테스트: {msg}")

    def _is_enabled_event(self, event: dict) -> bool:
        if event.get("enabled") is False:
            return False
        detail = event.get("detail") or {}
        if detail.get("enabled") is False:
            return False
        return True

    def handle_event(self, event: dict):
        etype = event.get("type")
        if etype in {"action_start", "action_end", "action", "condition_result"} and not self._is_enabled_event(event):
            return
        if etype == "state":
            self._set_state_labels(event)
        elif etype == "action_start":
            act_type = event.get("action_type") or "-"
            seq = self._extract_seq_path(event)
            extra = ""
            detail = event.get("detail") or {}
            desc = event.get("description") or ""
            pg = detail.get("pixel_get") or event.get("pixel_get")
            if act_type == "pixel_get" and isinstance(pg, dict):
                region = pg.get("region")
                target = pg.get("target") or "-"
                region_txt = ",".join(str(v) for v in region) if region else "-"
                extra = f"(영역={region_txt}, 대상={target})"
            msg = f"순번 {seq if seq is not None else '-'} - 액션 {act_type}"
            if extra:
                msg += f" {extra}"
            msg += " 시작"
            if desc:
                msg += f" | {desc}"
            self._append_log_line(msg, seq=seq)
        elif etype == "action_end":
            act_type = event.get("action_type") or "-"
            status = event.get("status", "ok")
            seq = self._extract_seq_path(event)
            extra = ""
            detail = event.get("detail") or {}
            desc = event.get("description") or ""
            pg = detail.get("pixel_get") or event.get("pixel_get")
            if act_type == "pixel_get" and isinstance(pg, dict):
                region = pg.get("region")
                target = pg.get("target") or "-"
                region_txt = ",".join(str(v) for v in region) if region else "-"
                extra = f"(영역={region_txt}, 대상={target})"
            msg = f"순번 {seq if seq is not None else '-'} - 액션 {act_type}"
            if extra:
                msg += f" {extra}"
            msg += f" 종료 ({status})"
            if desc:
                msg += f" | {desc}"
            self._append_log_line(msg, seq=seq)
        elif etype == "condition_result":
            name = event.get("name") or event.get("condition_type") or "조건"
            result = "참" if event.get("result") else "거짓"
            seq = self._extract_seq_path(event)
            detail = event.get("detail") or {}
            desc = event.get("description") or ""
            info = ""
            pix = detail.get("pixel") or event.get("pixel")
            key_detail = detail.get("key") or event.get("key")
            if isinstance(pix, dict):
                region = pix.get("region")
                color = pix.get("color")
                tol = pix.get("tolerance")
                expect = pix.get("expect_exists", True)
                found = pix.get("found")
                region_txt = ",".join(str(v) for v in region) if region else "-"
                color_txt = "#" + "".join(f"{c:02x}" for c in color) if isinstance(color, (list, tuple)) else "-"
                info = (
                    f"(픽셀 영역={region_txt}, 색상={color_txt}, tol={tol}, "
                    f"기대={'있음' if expect else '없음'}, 발견={'있음' if found else '없음'})"
                )
            elif isinstance(key_detail, dict):
                info = f"(키={key_detail.get('key')} 모드={key_detail.get('mode')})"
            msg = f"순번 {seq if seq is not None else '-'} - 조건 {name}: {result}"
            if info:
                msg += f" {info}"
            if desc:
                msg += f" | {desc}"
            self._append_log_line(msg, seq=seq)
        elif etype == "variable_update":
            self._update_variable(event)
            name = event.get("name") or ""
            cat = event.get("category") or ""
            self._append_log_line(f"변수 {cat}:{name} -> {event.get('value')}")
        elif etype == "action":
            act = event.get("action") or event.get("action_type") or "action"
            key = event.get("key")
            dur = event.get("duration")
            if act == "sleep" and dur is not None:
                self._append_log_line(f"액션 sleep {dur}ms")
            elif key:
                self._append_log_line(f"액션 {act} key={key}")
            else:
                self._append_log_line(f"액션 {act}")
        elif etype == "pixel_test":
            self._update_pixel_status(event)
        elif etype == "macro_start":
            label = event.get("macro", {}).get("name") or event.get("macro", {}).get("trigger_key") or "매크로"
            self._append_log_line(f"[매크로 시작] {label}")
        elif etype == "macro_stop":
            label = event.get("macro", {}).get("name") or event.get("macro", {}).get("trigger_key") or "매크로"
            self._append_log_line(f"[매크로 종료] {label} ({event.get('reason') or ''})")
        elif etype == "log":
            self._append_log_line(event.get("message", ""))


class ColorToleranceDialog(QtWidgets.QDialog):
    def __init__(self, parent=None, *, state: dict | None = None, save_state_cb=None):
        super().__init__(parent)
        self.setWindowTitle("색상값 계산")
        # 다른 창을 함께 볼 수 있도록 비모달로 동작시킨다.
        self.setModal(False)
        self.setWindowModality(QtCore.Qt.WindowModality.NonModal)
        try:
            self.setWindowFlags(
                QtCore.Qt.WindowType.Window
                | QtCore.Qt.WindowType.WindowMinimizeButtonHint
                | QtCore.Qt.WindowType.WindowCloseButtonHint
            )
        except Exception:
            pass
        self._save_state_cb = save_state_cb
        self._history: list[dict] = []
        self._max_history = 15
        self._current_result: dict | None = None
        self._build_ui()
        self._load_state(state or {})
        self._refresh_previews()

    def _build_ui(self):
        layout = QtWidgets.QVBoxLayout(self)
        layout.addLayout(self._build_input_row())
        layout.addWidget(self._build_result_group())
        layout.addWidget(self._build_history_group())

        btn_row = QtWidgets.QHBoxLayout()
        btn_row.addStretch()
        self.calc_btn = QtWidgets.QPushButton("추출")
        self.save_btn = QtWidgets.QPushButton("저장")
        self.reset_btn = QtWidgets.QPushButton("입력 초기화")
        self.close_btn = QtWidgets.QPushButton("닫기")
        btn_row.addWidget(self.calc_btn)
        btn_row.addWidget(self.save_btn)
        btn_row.addWidget(self.reset_btn)
        btn_row.addWidget(self.close_btn)
        layout.addLayout(btn_row)

        self.calc_btn.clicked.connect(self._compute)
        self.save_btn.clicked.connect(self._save_named_entry)
        self.reset_btn.clicked.connect(self._reset_inputs)
        self.close_btn.clicked.connect(self.reject)

        self.resize(800, 620)

    def _build_input_row(self):
        row = QtWidgets.QHBoxLayout()
        row.addWidget(self._build_input_group(True))
        row.addWidget(self._build_input_group(False))
        return row

    def _build_input_group(self, allowed: bool):
        title = "허용 색상 (HEX, 개행)" if allowed else "불허 색상 (HEX, 개행)"
        group = QtWidgets.QGroupBox(title)
        vbox = QtWidgets.QVBoxLayout(group)
        edit = QtWidgets.QPlainTextEdit()
        edit.setPlaceholderText("예) ff0000\n00ff00")
        edit.setFixedHeight(130)
        preview = QtWidgets.QListWidget()
        preview.setFixedHeight(140)
        preview.setSelectionMode(QtWidgets.QAbstractItemView.SelectionMode.NoSelection)
        hint = QtWidgets.QLabel("")
        hint.setStyleSheet("color: red;")

        if allowed:
            self.allowed_edit = edit
            self.allowed_preview = preview
            self.allowed_hint = hint
        else:
            self.blocked_edit = edit
            self.blocked_preview = preview
            self.blocked_hint = hint

        edit.textChanged.connect(self._refresh_previews)
        vbox.addWidget(edit)
        vbox.addWidget(QtWidgets.QLabel("미리보기"))
        vbox.addWidget(preview)
        vbox.addWidget(hint)
        return group

    def _build_result_group(self):
        group = QtWidgets.QGroupBox("결과")
        grid = QtWidgets.QGridLayout(group)
        self.name_edit = QtWidgets.QLineEdit()
        self.name_edit.setPlaceholderText("계산 이름 (저장 시 사용)")
        self.result_hex_label = QtWidgets.QLabel("-")
        self.result_hex_label.setTextFormat(QtCore.Qt.TextFormat.RichText)
        self.result_tol_label = QtWidgets.QLabel("-")
        self.buffer_slider = QtWidgets.QSlider(QtCore.Qt.Orientation.Horizontal)
        self.buffer_slider.setRange(0, 0)
        self.buffer_slider.setEnabled(False)
        self.buffer_info = QtWidgets.QLabel("여유 버퍼: -")
        self.buffer_info.setWordWrap(True)
        self.status_label = QtWidgets.QLabel("허용/불허 색상을 입력하고 추출을 눌러주세요.")
        self.status_label.setWordWrap(True)
        self.copy_btn = QtWidgets.QPushButton("HEX 복사")
        self.copy_btn.setEnabled(False)

        self.buffer_slider.valueChanged.connect(self._update_buffer_display)
        self.copy_btn.clicked.connect(self._copy_hex)

        grid.addWidget(QtWidgets.QLabel("이름"), 0, 0)
        grid.addWidget(self.name_edit, 0, 1, 1, 2)

        grid.addWidget(QtWidgets.QLabel("제안 색상"), 1, 0)
        result_row = QtWidgets.QHBoxLayout()
        result_row.addWidget(self.result_hex_label, 1)
        result_row.addWidget(self.copy_btn)
        grid.addLayout(result_row, 1, 1, 1, 2)

        grid.addWidget(QtWidgets.QLabel("기본 tol"), 2, 0)
        grid.addWidget(self.result_tol_label, 2, 1, 1, 2)

        grid.addWidget(QtWidgets.QLabel("여유 버퍼"), 3, 0)
        grid.addWidget(self.buffer_slider, 3, 1)
        grid.addWidget(self.buffer_info, 3, 2)

        grid.addWidget(self.status_label, 4, 0, 1, 3)
        return group

    def _build_history_group(self):
        group = QtWidgets.QGroupBox("최근 계산 내역")
        hbox = QtWidgets.QHBoxLayout(group)
        self.history_combo = QtWidgets.QComboBox()
        self.history_combo.setSizeAdjustPolicy(QtWidgets.QComboBox.SizeAdjustPolicy.AdjustToContents)
        self.history_combo.setMinimumContentsLength(30)
        self.history_load_btn = QtWidgets.QPushButton("불러오기")
        self.history_clear_btn = QtWidgets.QPushButton("내역 비우기")

        self.history_load_btn.clicked.connect(self._load_history_entry)
        self.history_clear_btn.clicked.connect(self._clear_history)

        hbox.addWidget(self.history_combo, 1)
        hbox.addWidget(self.history_load_btn)
        hbox.addWidget(self.history_clear_btn)
        return group

    def _refresh_previews(self):
        allowed_colors, allowed_error = _try_parse_hex_lines(self.allowed_edit.toPlainText())
        blocked_colors, blocked_error = _try_parse_hex_lines(self.blocked_edit.toPlainText())
        self._fill_preview(self.allowed_preview, allowed_colors)
        self._fill_preview(self.blocked_preview, blocked_colors)
        self.allowed_hint.setText(allowed_error)
        self.blocked_hint.setText(blocked_error)

    def _fill_preview(self, widget: QtWidgets.QListWidget, colors: list[str]):
        widget.clear()
        for hex_txt in colors:
            item = QtWidgets.QListWidgetItem(f"#{hex_txt.upper()}")
            qcolor = QtGui.QColor(f"#{hex_txt}")
            item.setBackground(qcolor)
            # 밝기에 따라 글자색 조정
            luminance = 0.299 * qcolor.red() + 0.587 * qcolor.green() + 0.114 * qcolor.blue()
            fg = QtCore.Qt.GlobalColor.black if luminance > 150 else QtCore.Qt.GlobalColor.white
            item.setForeground(QtGui.QBrush(fg))
            widget.addItem(item)

    def _set_status(self, text: str, *, error: bool = False):
        self.status_label.setText(text)
        if error:
            self.status_label.setStyleSheet("color: red;")
        else:
            self.status_label.setStyleSheet("")

    def _compute(self, add_history: bool = True):
        allowed_text = self.allowed_edit.toPlainText()
        blocked_text = self.blocked_edit.toPlainText()
        try:
            allowed_hex = _parse_hex_lines(allowed_text)
            blocked_hex = _parse_hex_lines(blocked_text, allow_empty=True)
        except ValueError as exc:
            self._set_status(str(exc), error=True)
            return

        try:
            result = _solve_color_tolerance(allowed_hex, blocked_hex)
        except Exception as exc:
            self._set_status(f"계산 중 오류: {exc}", error=True)
            return

        self._render_result(result)
        if add_history:
            self._append_history(allowed_text, blocked_text, result, name=self.name_edit.text().strip())
        self._save_state()

    def _render_result(self, result: dict):
        self._current_result = result
        hex_txt = result.get("hex") or ""
        display_hex = f"#{hex_txt.upper()}" if hex_txt else "-"
        chip = _color_chip_html(display_hex if display_hex != "-" else None)
        self.result_hex_label.setText(f"{chip}<b>{html.escape(display_hex)}</b>")
        self.copy_btn.setEnabled(bool(hex_txt))

        base_tol = int(result.get("tolerance", 0))
        min_req = int(result.get("min_required_tolerance", base_tol))
        self.result_tol_label.setText(f"{base_tol} (최소 요구 {min_req})")
        buffer_extra = int(result.get("buffer_extra", 0))
        self.buffer_slider.blockSignals(True)
        self.buffer_slider.setRange(0, buffer_extra)
        self.buffer_slider.setValue(0)
        self.buffer_slider.setEnabled(buffer_extra > 0)
        self.buffer_slider.blockSignals(False)

        ok = bool(result.get("ok"))
        min_block = result.get("min_block_distance")
        margin = result.get("margin")
        conflicts = result.get("conflicts", 0)
        self._update_buffer_display()
        if ok:
            if isinstance(min_block, int) and min_block < 256:
                msg = f"허용 색상 모두 통과, 불허 최소 거리 {min_block}."
            else:
                msg = "불허 목록이 없거나 모두 통과."
            self._set_status(msg, error=False)
        else:
            msg = "모든 허용을 만족하면서 불허를 모두 피할 수 없습니다."
            margin_txt = margin if isinstance(margin, (int, float)) else 0
            msg += f" (최소 충돌 {conflicts}개, tol {base_tol}, 여유 {margin_txt})"
            self._set_status(msg, error=True)

    def _save_named_entry(self):
        if not self._current_result:
            self._set_status("먼저 추출을 실행하세요.", error=True)
            return
        name = self.name_edit.text().strip()
        if not name:
            self._set_status("저장할 이름을 입력하세요.", error=True)
            return
        allowed_text = self.allowed_edit.toPlainText()
        blocked_text = self.blocked_edit.toPlainText()
        self._append_history(allowed_text, blocked_text, self._current_result, name=name)
        self._save_state()
        self._set_status(f"'{name}'으로 저장했습니다.", error=False)

    def _update_buffer_display(self):
        if not self._current_result:
            self.buffer_info.setText("여유 버퍼: -")
            return
        base_tol = int(self._current_result.get("tolerance", 0))
        extra = int(self.buffer_slider.value()) if self.buffer_slider.isEnabled() else 0
        max_extra = int(self._current_result.get("buffer_extra", 0))
        current_tol = base_tol + extra
        max_tol = base_tol + max_extra
        if max_extra > 0:
            self.buffer_info.setText(f"+{extra} → 현재 tol {current_tol} (최대 {max_tol})")
        else:
            self.buffer_info.setText("불허 색상까지 여유가 없습니다.")

    def _copy_hex(self):
        if not self._current_result:
            return
        hex_txt = self._current_result.get("hex")
        if not hex_txt:
            return
        clean_hex = hex_txt.upper()
        QtGui.QGuiApplication.clipboard().setText(clean_hex)
        QtWidgets.QToolTip.showText(QtGui.QCursor.pos(), f"복사됨: {clean_hex}", self, QtCore.QRect(), 1200)

    def _reset_inputs(self):
        self.allowed_edit.clear()
        self.blocked_edit.clear()
        self.result_hex_label.setText("-")
        self.result_tol_label.setText("-")
        self.buffer_info.setText("여유 버퍼: -")
        self.buffer_slider.setRange(0, 0)
        self.buffer_slider.setEnabled(False)
        self.copy_btn.setEnabled(False)
        self._current_result = None
        self._set_status("입력을 초기화했습니다.")
        self._refresh_previews()
        self._save_state()

    def _append_history(self, allowed_text: str, blocked_text: str, result: dict, *, name: str = ""):
        entry = {
            "ts": _format_dt(),
            "allowed": allowed_text.strip(),
            "blocked": blocked_text.strip(),
            "hex": result.get("hex") or "",
            "tolerance": int(result.get("tolerance", 0)),
            "ok": bool(result.get("ok")),
            "buffer_extra": int(result.get("buffer_extra", 0)),
            "name": name.strip(),
        }
        if entry["name"]:
            # 동일 이름은 최신으로 교체
            self._history = [e for e in self._history if e.get("name") != entry["name"]]
        self._history.insert(0, entry)
        self._history = self._history[: self._max_history]
        self._refresh_history_combo()

    def _refresh_history_combo(self):
        self.history_combo.blockSignals(True)
        self.history_combo.clear()
        for entry in self._history:
            ok_txt = "성공" if entry.get("ok") else "부분 실패"
            hex_txt = entry.get("hex")
            tol_txt = entry.get("tolerance")
            ts = entry.get("ts")
            name = entry.get("name")
            label = name if name else f"#{str(hex_txt).upper()} tol {tol_txt}"
            summary = f"[{ok_txt}] {label} ({ts})"
            self.history_combo.addItem(summary)
        self.history_combo.blockSignals(False)

    def _load_history_entry(self):
        idx = self.history_combo.currentIndex()
        if idx < 0 or idx >= len(self._history):
            return
        entry = self._history[idx]
        self.allowed_edit.setPlainText(entry.get("allowed", ""))
        self.blocked_edit.setPlainText(entry.get("blocked", ""))
        self.name_edit.setText(entry.get("name", ""))
        self._refresh_previews()
        self._compute(add_history=False)

    def _clear_history(self):
        self._history = []
        self._refresh_history_combo()
        self._save_state()
        self._set_status("최근 계산 내역을 비웠습니다.")

    def _load_state(self, state: dict):
        if not isinstance(state, dict):
            return
        self.allowed_edit.setPlainText(state.get("allowed_text", ""))
        self.blocked_edit.setPlainText(state.get("blocked_text", ""))
        self.name_edit.setText(state.get("name_text", ""))
        history = state.get("history")
        if isinstance(history, list):
            self._history = history[: self._max_history]
            self._refresh_history_combo()

    def _save_state(self):
        if not callable(self._save_state_cb):
            return
        data = {
            "allowed_text": self.allowed_edit.toPlainText(),
            "blocked_text": self.blocked_edit.toPlainText(),
            "history": self._history,
            "name_text": self.name_edit.text(),
        }
        self._save_state_cb(data)

    def closeEvent(self, event: QtGui.QCloseEvent):
        self._save_state()
        return super().closeEvent(event)


class PixelTestDialog(QtWidgets.QDialog):
    def __init__(
        self,
        parent=None,
        *,
        resolver_provider=None,
        start_test=None,
        stop_test=None,
        state: dict | None = None,
        save_state_cb=None,
    ):
        super().__init__(parent)
        self.setWindowTitle("픽셀 테스트")
        self.setModal(True)
        self.setWindowModality(QtCore.Qt.WindowModality.WindowModal)
        self._resolver_provider = resolver_provider
        self._start_test = start_test
        self._stop_test = stop_test
        self._save_state_cb = save_state_cb
        self._testing = False
        self._build_ui()
        self._load_state(state or {})

    def _build_ui(self):
        layout = QtWidgets.QVBoxLayout(self)
        form = QtWidgets.QFormLayout()
        self.region_edit = QtWidgets.QLineEdit("0,0,100,100")
        _attach_variable_completer(self.region_edit, [])
        self.color_edit = QtWidgets.QLineEdit("ff0000")
        _setup_hex_line_edit(self.color_edit)
        _attach_variable_completer(self.color_edit, [])
        self.tol_spin = QtWidgets.QSpinBox()
        self.tol_spin.setRange(0, 255)
        self.tol_spin.setValue(10)
        self.expect_combo = QtWidgets.QComboBox()
        self.expect_combo.addItem("색상이 있을 때 참", True)
        self.expect_combo.addItem("색상이 없을 때 참", False)
        self.interval_spin = QtWidgets.QSpinBox()
        self.interval_spin.setRange(50, 5000)
        self.interval_spin.setSuffix(" ms")
        self.interval_spin.setValue(200)

        form.addRow("Region x,y,w,h", self.region_edit)
        form.addRow("색상 (HEX RRGGBB)", self.color_edit)
        form.addRow("Tolerance", self.tol_spin)
        form.addRow("기대 상태", self.expect_combo)
        form.addRow("테스트 주기", self.interval_spin)
        layout.addLayout(form)

        btn_row = QtWidgets.QHBoxLayout()
        btn_row.addStretch()
        self.start_btn = QtWidgets.QPushButton("테스트 시작")
        self.close_btn = QtWidgets.QPushButton("닫기")
        btn_row.addWidget(self.start_btn)
        btn_row.addWidget(self.close_btn)
        layout.addLayout(btn_row)

        self.start_btn.clicked.connect(self._toggle_test)
        self.close_btn.clicked.connect(self.reject)

        self.resize(420, 260)

    def _current_resolver(self):
        if callable(self._resolver_provider):
            try:
                return self._resolver_provider()
            except Exception:
                return None
        return None

    def _parse_inputs(self):
        resolver = self._current_resolver()
        region = _parse_region(self.region_edit.text(), resolver=resolver)
        color = _parse_hex_color(self.color_edit.text(), resolver=resolver)
        tolerance = int(self.tol_spin.value())
        expect_exists = bool(self.expect_combo.currentData()) if self.expect_combo.currentIndex() >= 0 else True
        return region, color, tolerance, expect_exists

    def _toggle_test(self):
        if self._testing:
            self._stop_testing()
            return
        try:
            region, color, tol, expect = self._parse_inputs()
        except ValueError as exc:
            QtWidgets.QMessageBox.warning(self, "입력 오류", str(exc))
            return
        if not callable(self._start_test):
            QtWidgets.QMessageBox.information(self, "지원 안 함", "테스트 기능을 사용할 수 없습니다.")
            return
        config = {
            "region": region,
            "region_raw": self.region_edit.text().strip(),
            "color": color,
            "color_raw": self.color_edit.text().strip(),
            "tolerance": tol,
            "expect_exists": expect,
            "interval": int(self.interval_spin.value()),
            "label": "픽셀 테스트",
            "persist": True,
        }
        self._start_test(config, self._on_test_stopped)
        self._testing = True
        self.start_btn.setText("테스트 중지")
        self._save_state()

    def _stop_testing(self):
        if callable(self._stop_test):
            self._stop_test()
        self._on_test_stopped()

    def _on_test_stopped(self):
        self._testing = False
        self.start_btn.setText("테스트 시작")

    def _load_state(self, state: dict):
        if not isinstance(state, dict):
            return
        if state.get("region"):
            self.region_edit.setText(str(state.get("region")))
        if state.get("color"):
            self.color_edit.setText(str(state.get("color")))
        try:
            tol = int(state.get("tolerance", 10))
            self.tol_spin.setValue(tol)
        except Exception:
            pass
        expect = state.get("expect_exists")
        if expect is not None:
            idx = self.expect_combo.findData(bool(expect))
            if idx >= 0:
                self.expect_combo.setCurrentIndex(idx)
        try:
            interval = int(state.get("interval", 200))
            self.interval_spin.setValue(interval)
        except Exception:
            pass

    def _save_state(self):
        if not self._save_state_cb:
            return
        data = {
            "region": self.region_edit.text().strip(),
            "color": self.color_edit.text().strip(),
            "tolerance": int(self.tol_spin.value()),
            "expect_exists": bool(self.expect_combo.currentData()) if self.expect_combo.currentIndex() >= 0 else True,
            "interval": int(self.interval_spin.value()),
        }
        self._save_state_cb(data)

    def closeEvent(self, event: QtGui.QCloseEvent):
        self._stop_testing()
        self._save_state()
        return super().closeEvent(event)


class PresetTransferDialog(QtWidgets.QDialog):
    def __init__(
        self,
        parent=None,
        *,
        profile_provider: Callable[[], MacroProfile],
        base_res: tuple[int, int],
        base_scale: float,
        current_res: tuple[int, int] | None = None,
        current_scale: float | None = None,
        detect_resolution=None,
        detect_scale=None,
        theme: dict | None = None,
        log_cb=None,
        profile_path: str | None = None,
    ):
        super().__init__(parent)
        self.setWindowTitle("프리셋 옮기기")
        self.setModal(False)
        self.setWindowModality(QtCore.Qt.WindowModality.NonModal)
        try:
            self.setWindowFlag(QtCore.Qt.WindowType.WindowStaysOnTopHint, False)
        except Exception:
            pass
        self.profile_provider = profile_provider
        self.detect_resolution_cb = detect_resolution
        self.detect_scale_cb = detect_scale
        self._theme = theme or {}
        self._log_cb = log_cb
        self._profile_path = Path(profile_path) if profile_path else None
        self._base_res_default = base_res
        self._base_scale_default = base_scale
        self._current_res_default = current_res
        self._current_scale_default = current_scale
        self._last_sample_calc: dict | None = None
        self._build_ui()

    def _log(self, msg: str):
        if callable(self._log_cb):
            try:
                self._log_cb(msg)
            except Exception:
                pass

    def _build_ui(self):
        layout = QtWidgets.QVBoxLayout(self)
        self.tabs = QtWidgets.QTabWidget()
        self._build_sample_tab()
        self._build_scale_tab()
        self.tabs.addTab(self.sample_tab, "샘플 좌표 변환")
        self.tabs.addTab(self.scale_tab, "해상도+앱 배율")
        layout.addWidget(self.tabs)

        btn_row = QtWidgets.QHBoxLayout()
        btn_row.addStretch()
        self.save_btn = QtWidgets.QPushButton("저장")
        self.cancel_btn = QtWidgets.QPushButton("취소")
        btn_row.addWidget(self.save_btn)
        btn_row.addWidget(self.cancel_btn)
        layout.addLayout(btn_row)

        self.save_btn.clicked.connect(self._handle_save)
        self.cancel_btn.clicked.connect(self.reject)
        self.resize(780, 520)

    # 샘플 탭 ------------------------------------------------------------
    def _build_sample_tab(self):
        self.sample_tab = QtWidgets.QWidget()
        layout = QtWidgets.QVBoxLayout(self.sample_tab)
        desc = QtWidgets.QLabel("기준 좌표(x,y)와 변환 좌표(x',y')를 'x,y' 형식으로 최소 2개 이상 입력하세요. (3개 권장)")
        desc.setWordWrap(True)
        layout.addWidget(desc)

        self.sample_table = QtWidgets.QTableWidget(0, 2)
        self.sample_table.setHorizontalHeaderLabels(["기준 (x,y)", "변환 (x',y')"])
        header = self.sample_table.horizontalHeader()
        header.setStretchLastSection(True)
        layout.addWidget(self.sample_table)

        btn_row = QtWidgets.QHBoxLayout()
        self.add_sample_btn = QtWidgets.QPushButton("샘플 추가")
        self.del_sample_btn = QtWidgets.QPushButton("선택 삭제")
        self.calc_sample_btn = QtWidgets.QPushButton("보정 계산")
        btn_row.addWidget(self.add_sample_btn)
        btn_row.addWidget(self.del_sample_btn)
        btn_row.addStretch()
        btn_row.addWidget(self.calc_sample_btn)
        layout.addLayout(btn_row)

        self.sample_result_label = QtWidgets.QLabel("계수: a/b/c/d, RMS: -")
        layout.addWidget(self.sample_result_label)

        test_row = QtWidgets.QHBoxLayout()
        test_row.setSpacing(8)
        test_row.addWidget(QtWidgets.QLabel("기준 좌표 테스트"))
        self.sample_test_input = QtWidgets.QLineEdit()
        self.sample_test_input.setPlaceholderText("예: 1032,1323 (기준 x,y)")
        test_row.addWidget(self.sample_test_input, 1)
        self.sample_test_btn = QtWidgets.QPushButton("좌표 변환 테스트")
        self.sample_test_btn.setEnabled(False)
        test_row.addWidget(self.sample_test_btn)
        self.sample_test_result = QtWidgets.QLabel("결과: -")
        test_row.addWidget(self.sample_test_result)
        test_row.addStretch()
        layout.addLayout(test_row)

        self.sample_preview = QtWidgets.QPlainTextEdit()
        self.sample_preview.setReadOnly(True)
        self.sample_preview.setPlaceholderText("보정 계산을 누르면 계수, 프로필 좌표/리전 변환 요약, 예시가 표시됩니다.")
        self.sample_preview.setMinimumHeight(160)
        self.sample_preview.setFont(QtGui.QFontDatabase.systemFont(QtGui.QFontDatabase.SystemFont.FixedFont))
        layout.addWidget(self.sample_preview)

        self.add_sample_btn.clicked.connect(self._add_sample_row)
        self.del_sample_btn.clicked.connect(self._remove_sample_rows)
        self.calc_sample_btn.clicked.connect(self._on_calc_samples)
        self.sample_test_btn.clicked.connect(self._on_test_sample_point)
        self.sample_test_input.returnPressed.connect(self._on_test_sample_point)
        for _ in range(2):
            self._add_sample_row()

    def _add_sample_row(self, sample: tuple[float, float, float, float] | None = None):
        row = self.sample_table.rowCount()
        self.sample_table.insertRow(row)
        if sample:
            values = [f"{sample[0]:.2f},{sample[1]:.2f}", f"{sample[2]:.2f},{sample[3]:.2f}"]
        else:
            values = ["", ""]
        for col, val in enumerate(values):
            self.sample_table.setItem(row, col, QtWidgets.QTableWidgetItem(str(val)))

    def _remove_sample_rows(self):
        rows = sorted({idx.row() for idx in self.sample_table.selectionModel().selectedRows()}, reverse=True)
        if not rows and self.sample_table.rowCount() > 0:
            rows = [self.sample_table.rowCount() - 1]
        for r in rows:
            self.sample_table.removeRow(r)

    @staticmethod
    def _parse_sample_point_text(text: str) -> tuple[float, float]:
        cleaned = text.strip().replace("，", ",")
        parts = [p.strip() for p in cleaned.split(",") if p.strip()]
        if len(parts) != 2:
            raise ValueError("좌표는 'x,y' 형식으로 입력하세요.")
        try:
            return float(parts[0]), float(parts[1])
        except Exception as exc:
            raise ValueError("좌표는 숫자여야 합니다.") from exc

    def _collect_samples(self) -> list[tuple[float, float, float, float]]:
        samples: list[tuple[float, float, float, float]] = []
        for row in range(self.sample_table.rowCount()):
            base_item = self.sample_table.item(row, 0)
            target_item = self.sample_table.item(row, 1)
            base_text = base_item.text().strip() if base_item else ""
            target_text = target_item.text().strip() if target_item else ""
            if not base_text and not target_text:
                continue
            if not base_text or not target_text:
                raise ValueError(f"{row + 1}행의 좌표가 비어 있습니다. 기준/변환 모두 입력하세요.")
            try:
                sx, sy = self._parse_sample_point_text(base_text)
                tx, ty = self._parse_sample_point_text(target_text)
            except ValueError as exc:
                raise ValueError(f"{row + 1}행: {exc}") from exc
            samples.append((float(sx), float(sy), float(tx), float(ty)))
        if len(samples) < 2:
            raise ValueError("샘플을 최소 2개 이상 입력하세요.")
        return samples

    @staticmethod
    def _fit_axis(src: list[float], dst: list[float]) -> tuple[float, float]:
        n = len(src)
        if n == 0:
            return 1.0, 0.0
        sum_x = sum(src)
        sum_y = sum(dst)
        sum_x2 = sum(x * x for x in src)
        sum_xy = sum(x * y for x, y in zip(src, dst))
        denom = n * sum_x2 - sum_x * sum_x
        if abs(denom) < 1e-9:
            a = 1.0
            b = (sum_y - a * sum_x) / n
        else:
            a = (n * sum_xy - sum_x * sum_y) / denom
            b = (sum_y - a * sum_x) / n
        return a, b

    @staticmethod
    def _calc_rms(samples: list[tuple[float, float, float, float]], ax: float, bx: float, cy: float, dy: float) -> float:
        if not samples:
            return 0.0
        total = 0.0
        for sx, sy, tx, ty in samples:
            dx = ax * sx + bx - tx
            dy_err = cy * sy + dy - ty
            total += dx * dx + dy_err * dy_err
        return math.sqrt(total / len(samples))

    def _render_sample_preview(
        self,
        samples: list[tuple[float, float, float, float]],
        ax: float,
        bx: float,
        cy: float,
        dy: float,
        rms: float,
        changes: list[tuple[str, str, str]] | None = None,
        change_error: str | None = None,
    ):
        self.sample_result_label.setText(
            f"계수: a={ax:.5f}, b={bx:.3f}, c={cy:.5f}, d={dy:.3f} | RMS 오차: {rms:.3f}"
        )
        lines = [
            f"x' = a*x + b, y' = c*y + d",
            f"a={ax:.5f}, b={bx:.3f} | c={cy:.5f}, d={dy:.3f}",
            f"RMS 오차: {rms:.3f}",
            "",
        ]
        lines.append("프로필 좌표/리전 변환 요약 (현재 프로필 기준)")
        if change_error:
            lines.append(f"- 미리보기 실패: {change_error}")
        elif changes is None:
            lines.append("- 프로필을 불러올 수 없습니다.")
        elif not changes:
            lines.append("- 변경된 항목 없음")
        else:
            max_lines = 12
            for label, before, after in changes[:max_lines]:
                lines.append(f"- {label}: {before} -> {after}")
            if len(changes) > max_lines:
                lines.append(f"- ...외 {len(changes) - max_lines}건")
        lines.append("")
        if samples:
            lines.append("샘플 예시:")
        for idx, (sx, sy, tx, ty) in enumerate(samples[:3]):
            pred_x = ax * sx + bx
            pred_y = cy * sy + dy
            lines.append(
                f"예시 {idx + 1}: ({sx:.2f}, {sy:.2f}) → ({pred_x:.2f}, {pred_y:.2f}) "
                f"(샘플 목표: {tx:.2f}, {ty:.2f})"
            )
        self.sample_preview.setPlainText("\n".join(lines))

    def _compute_sample_transform(self) -> tuple[float, float, float, float, float, list[tuple[float, float, float, float]]]:
        samples = self._collect_samples()
        ax, bx = self._fit_axis([s[0] for s in samples], [s[2] for s in samples])
        cy, dy = self._fit_axis([s[1] for s in samples], [s[3] for s in samples])
        rms = self._calc_rms(samples, ax, bx, cy, dy)
        changes: list[tuple[str, str, str]] | None = None
        change_error: str | None = None
        if callable(getattr(self, "profile_provider", None)):
            try:
                preview_profile = self.profile_provider()
                _, changes = _transform_profile_affine(preview_profile, ax, bx, cy, dy)
            except Exception as exc:
                change_error = str(exc)
        else:
            change_error = "프로필을 불러올 수 없습니다."
        self._last_sample_calc = {
            "ax": ax,
            "bx": bx,
            "cy": cy,
            "dy": dy,
            "rms": rms,
            "samples": samples,
            "changes": changes,
            "change_error": change_error,
        }
        try:
            self.sample_test_btn.setEnabled(True)
            self.sample_test_result.setText("결과: -")
        except Exception:
            pass
        self._render_sample_preview(samples, ax, bx, cy, dy, rms, changes, change_error)
        return ax, bx, cy, dy, rms, samples

    def _on_calc_samples(self):
        try:
            ax, bx, cy, dy, rms, samples = self._compute_sample_transform()
        except ValueError as exc:
            QtWidgets.QMessageBox.warning(self, "입력 오류", str(exc))
            return
        change_count = len(self._last_sample_calc.get("changes") or []) if self._last_sample_calc else 0
        change_error = self._last_sample_calc.get("change_error") if self._last_sample_calc else None
        extra_line = ""
        if change_error:
            extra_line = f"\n프로필 변환 미리보기 실패: {change_error}"
        else:
            extra_line = f"\n예상 변경: {change_count}건 (미리보기 확인)"
        QtWidgets.QMessageBox.information(
            self,
            "보정 계산 완료",
            f"a={ax:.4f}, b={bx:.2f}, c={cy:.4f}, d={dy:.2f}\n"
            f"RMS 오차: {rms:.3f}\n샘플 {len(samples)}개{extra_line}",
        )
        self._log(f"샘플 좌표 변환 계산: a={ax:.4f}, b={bx:.2f}, c={cy:.4f}, d={dy:.2f}, RMS={rms:.3f}")

    def _on_test_sample_point(self):
        if not self._last_sample_calc:
            QtWidgets.QMessageBox.information(self, "보정 필요", "먼저 보정 계산을 실행하세요.")
            return
        text = self.sample_test_input.text().strip() if hasattr(self, "sample_test_input") else ""
        if not text:
            QtWidgets.QMessageBox.warning(self, "입력 오류", "기준 좌표를 입력하세요. 예: 1032,1323")
            return
        try:
            sx, sy = self._parse_sample_point_text(text)
        except ValueError as exc:
            QtWidgets.QMessageBox.warning(self, "입력 오류", str(exc))
            return
        ax = float(self._last_sample_calc.get("ax", 1.0))
        bx = float(self._last_sample_calc.get("bx", 0.0))
        cy = float(self._last_sample_calc.get("cy", 1.0))
        dy = float(self._last_sample_calc.get("dy", 0.0))
        pred_x = ax * sx + bx
        pred_y = cy * sy + dy
        if isinstance(getattr(self, "sample_test_result", None), QtWidgets.QLabel):
            self.sample_test_result.setText(f"→ 변환 좌표: ({pred_x:.2f}, {pred_y:.2f})")

    def _save_from_samples(self) -> bool:
        try:
            ax, bx, cy, dy, rms, samples = self._compute_sample_transform()
        except ValueError as exc:
            QtWidgets.QMessageBox.warning(self, "입력 오류", str(exc))
            return False
        try:
            profile = self.profile_provider()
        except ValueError as exc:
            QtWidgets.QMessageBox.warning(self, "프로필 오류", str(exc))
            return False

        QtWidgets.QMessageBox.information(
            self,
            "변환 성공",
            f"계수: a={ax:.4f}, b={bx:.2f}, c={cy:.4f}, d={dy:.2f}\nRMS 오차: {rms:.3f}\n저장 위치를 선택하세요.",
        )

        transformed, changes = _transform_profile_affine(profile, ax, bx, cy, dy)
        transformed.transform_matrix = {
            "ax": float(ax),
            "bx": float(bx),
            "cy": float(cy),
            "dy": float(dy),
            "rms": float(rms),
            "samples": [{"src": [sx, sy], "dst": [tx, ty]} for sx, sy, tx, ty in samples],
            "type": "linear_xy",
        }
        default_dir = self._profile_path.parent if self._profile_path else Path.cwd()
        base_name = self._profile_path.stem if self._profile_path else "profile"
        default_path = default_dir / f"{base_name}_affine.json"
        saved = self._prompt_save_profile(transformed, default_path)
        if saved:
            self._log(f"샘플 좌표 기반 변환 완료 (변경 {len(changes)}건, RMS={rms:.3f})")
        return saved

    # 해상도/배율 탭 -----------------------------------------------------
    def _build_scale_tab(self):
        self.scale_tab = QtWidgets.QWidget()
        layout = QtWidgets.QVBoxLayout(self.scale_tab)

        form = QtWidgets.QGridLayout()
        form.setHorizontalSpacing(8)
        form.setVerticalSpacing(4)
        form.setContentsMargins(0, 0, 0, 0)

        base_label = QtWidgets.QLabel("기준 해상도")
        base_row = QtWidgets.QHBoxLayout()
        base_row.setContentsMargins(0, 0, 0, 0)
        base_row.setSpacing(4)
        self.base_res_edit = QtWidgets.QLineEdit(_format_resolution(self._base_res_default))
        self.base_res_edit.setClearButtonEnabled(True)
        self.base_res_edit.setPlaceholderText("예: 3440x1440")
        base_row.addWidget(self.base_res_edit)
        form.addWidget(base_label, 0, 0)
        form.addLayout(base_row, 0, 1)

        base_scale_label = QtWidgets.QLabel("기준 앱 배율(%)")
        base_scale_row = QtWidgets.QHBoxLayout()
        base_scale_row.setContentsMargins(0, 0, 0, 0)
        base_scale_row.setSpacing(4)
        self.base_scale_edit = QtWidgets.QLineEdit(_format_scale_percent(self._base_scale_default))
        self.base_scale_edit.setClearButtonEnabled(True)
        self.base_scale_edit.setPlaceholderText("예: 100 또는 125")
        base_scale_row.addWidget(self.base_scale_edit)
        base_scale_row.addStretch()
        form.addWidget(base_scale_label, 1, 0)
        form.addLayout(base_scale_row, 1, 1)

        current_label = QtWidgets.QLabel("현재 해상도")
        current_row = QtWidgets.QHBoxLayout()
        current_row.setContentsMargins(0, 0, 0, 0)
        current_row.setSpacing(4)
        self.current_res_edit = QtWidgets.QLineEdit(
            _format_resolution(self._current_res_default) if self._current_res_default else ""
        )
        self.current_res_edit.setPlaceholderText("자동 감지 또는 직접 입력")
        self.current_res_edit.setClearButtonEnabled(True)
        self.detect_res_btn = QtWidgets.QPushButton("자동 감지")
        self.detect_res_btn.setMinimumWidth(90)
        current_row.addWidget(self.current_res_edit)
        current_row.addWidget(self.detect_res_btn)
        form.addWidget(current_label, 2, 0)
        form.addLayout(current_row, 2, 1)

        current_scale_label = QtWidgets.QLabel("현재 앱 배율(%)")
        current_scale_row = QtWidgets.QHBoxLayout()
        current_scale_row.setContentsMargins(0, 0, 0, 0)
        current_scale_row.setSpacing(4)
        self.current_scale_edit = QtWidgets.QLineEdit(
            _format_scale_percent(self._current_scale_default) if self._current_scale_default else ""
        )
        self.current_scale_edit.setPlaceholderText("자동 감지 또는 직접 입력 (예: 100)")
        self.current_scale_edit.setClearButtonEnabled(True)
        self.detect_scale_btn = QtWidgets.QPushButton("배율 감지")
        self.detect_scale_btn.setMinimumWidth(90)
        current_scale_row.addWidget(self.current_scale_edit)
        current_scale_row.addWidget(self.detect_scale_btn)
        form.addWidget(current_scale_label, 3, 0)
        form.addLayout(current_scale_row, 3, 1)

        preview_btn_row = QtWidgets.QHBoxLayout()
        preview_btn_row.addStretch()
        self.scale_preview_btn = QtWidgets.QPushButton("변환 미리보기")
        preview_btn_row.addWidget(self.scale_preview_btn)
        form.addLayout(preview_btn_row, 4, 0, 1, 2)

        layout.addLayout(form)

        preview_layout = QtWidgets.QVBoxLayout()
        preview_layout.setContentsMargins(0, 0, 0, 0)
        preview_label = QtWidgets.QLabel("변환 전/후 요약")
        preview_label.setStyleSheet("font-weight: 600;")
        self.scale_preview = QtWidgets.QPlainTextEdit()
        self.scale_preview.setReadOnly(True)
        self.scale_preview.setMinimumHeight(120)
        self.scale_preview.setPlaceholderText("해상도/배율을 입력 후 미리보기를 눌러 요약을 확인하세요.")
        self.scale_preview.setFont(QtGui.QFontDatabase.systemFont(QtGui.QFontDatabase.SystemFont.FixedFont))
        preview_layout.addWidget(preview_label)
        preview_layout.addWidget(self.scale_preview)
        layout.addLayout(preview_layout)

        self.detect_res_btn.clicked.connect(lambda: self._detect_current_resolution(silent=False))
        self.detect_scale_btn.clicked.connect(lambda: self._detect_current_scale(silent=False))
        self.scale_preview_btn.clicked.connect(self._preview_scale)

    def _detect_current_resolution(self, *, silent: bool = False) -> tuple[int, int] | None:
        if not callable(self.detect_resolution_cb):
            if not silent:
                QtWidgets.QMessageBox.information(self, "지원 안 함", "자동 감지를 사용할 수 없습니다.")
            return None
        res = self.detect_resolution_cb()
        if not res:
            if not silent:
                QtWidgets.QMessageBox.warning(self, "감지 실패", "현재 해상도를 가져오지 못했습니다.")
            return None
        text = _format_resolution(res)
        self.current_res_edit.setText(text)
        if not silent:
            self._log(f"현재 해상도 감지: {text}")
        return res

    def _detect_current_scale(self, *, silent: bool = False) -> float | None:
        if not callable(self.detect_scale_cb):
            if not silent:
                QtWidgets.QMessageBox.information(self, "지원 안 함", "배율 감지를 사용할 수 없습니다.")
            return None
        scale = self.detect_scale_cb()
        if scale is None:
            if not silent:
                QtWidgets.QMessageBox.warning(self, "감지 실패", "현재 앱 배율을 가져오지 못했습니다.")
            return None
        text = _format_scale_percent(scale)
        self.current_scale_edit.setText(text)
        if not silent:
            self._log(f"현재 앱 배율 감지: {text}")
        return scale

    def _parse_resolution_field(self, edit: QtWidgets.QLineEdit, default: tuple[int, int]) -> tuple[int, int]:
        text = edit.text().strip()
        return _parse_resolution_text(text, allow_empty=False, default=default)

    def _parse_scale_field(self, edit: QtWidgets.QLineEdit, default: float) -> float:
        text = edit.text().strip()
        return _parse_scale_text(text, allow_empty=True, default=default)

    def _render_scale_preview(
        self,
        changes: list[tuple[str, str, str]],
        scale_x: float,
        scale_y: float,
        base_res: tuple[int, int],
        target_res: tuple[int, int],
        base_scale: float,
        target_scale: float,
    ):
        if not isinstance(self.scale_preview, QtWidgets.QPlainTextEdit):
            return
        base_scale_text = _format_scale_percent(base_scale)
        target_scale_text = _format_scale_percent(target_scale)
        lines = [
            f"기준 { _format_resolution(base_res) } @ {base_scale_text or '100%'} -> 현재 { _format_resolution(target_res) } @ {target_scale_text or '100%'}",
            f"스케일 계수(해상도+앱 배율): x={scale_x:.3f}, y={scale_y:.3f}",
        ]
        filtered = [c for c in changes if c[0] != "기준 해상도"]
        max_lines = 12
        if not filtered:
            lines.append("변경된 좌표가 없습니다.")
        else:
            for label, before, after in filtered[:max_lines]:
                lines.append(f"- {label}: {before} -> {after}")
            if len(filtered) > max_lines:
                lines.append(f"- ...외 {len(filtered) - max_lines}건")
        self.scale_preview.setPlainText("\n".join(lines))

    def _run_scale_transform(self) -> tuple | None:
        try:
            profile = self.profile_provider()
        except ValueError as exc:
            QtWidgets.QMessageBox.warning(self, "입력 오류", str(exc))
            return None
        try:
            base_res = self._parse_resolution_field(self.base_res_edit, self._base_res_default)
        except ValueError as exc:
            QtWidgets.QMessageBox.warning(self, "입력 오류", f"기준 해상도를 확인하세요: {exc}")
            return None
        try:
            base_scale = self._parse_scale_field(self.base_scale_edit, self._base_scale_default)
        except ValueError as exc:
            QtWidgets.QMessageBox.warning(self, "입력 오류", f"기준 앱 배율을 확인하세요: {exc}")
            return None

        target_text = self.current_res_edit.text().strip()
        if not target_text:
            detected = self._detect_current_resolution(silent=True)
            target_text = _format_resolution(detected) if detected else ""
            if detected:
                self.current_res_edit.setText(target_text)
        try:
            target_res = _parse_resolution_text(target_text, allow_empty=False, default=None)
        except ValueError as exc:
            QtWidgets.QMessageBox.warning(self, "입력 오류", f"현재 해상도를 확인하세요: {exc}")
            return None

        target_scale_text = self.current_scale_edit.text().strip()
        if not target_scale_text:
            detected_scale = self._detect_current_scale(silent=True)
            target_scale_text = _format_scale_percent(detected_scale) if detected_scale else ""
            if detected_scale:
                self.current_scale_edit.setText(target_scale_text)
        try:
            target_scale = _parse_scale_text(target_scale_text, allow_empty=True, default=base_scale)
        except ValueError as exc:
            QtWidgets.QMessageBox.warning(self, "입력 오류", f"앱 배율을 확인하세요: {exc}")
            return None

        try:
            scaled_profile, changes, scale_x, scale_y = _scale_profile(
                profile, base_res, target_res, base_scale, target_scale
            )
        except ValueError as exc:
            QtWidgets.QMessageBox.warning(self, "스케일 실패", str(exc))
            return None
        self._render_scale_preview(changes, scale_x, scale_y, base_res, target_res, base_scale, target_scale)
        return scaled_profile, changes, scale_x, scale_y, base_res, target_res, base_scale, target_scale

    def _preview_scale(self):
        result = self._run_scale_transform()
        if not result:
            return
        _, _, scale_x, scale_y, _, _, _, _ = result
        QtWidgets.QMessageBox.information(
            self,
            "미리보기 완료",
            f"스케일 계수: x={scale_x:.4f}, y={scale_y:.4f}\n변환 요약을 확인하세요.",
        )

    def _save_from_scale(self) -> bool:
        result = self._run_scale_transform()
        if not result:
            return False
        scaled_profile, changes, scale_x, scale_y, base_res, target_res, base_scale, target_scale = result
        QtWidgets.QMessageBox.information(
            self,
            "변환 성공",
            f"{_format_resolution(base_res)} → {_format_resolution(target_res)}\n"
            f"스케일 계수: x={scale_x:.4f}, y={scale_y:.4f}\n저장 위치를 선택하세요.",
        )
        base_label = _format_resolution(base_res)
        target_label = _format_resolution(target_res)
        default_dir = self._profile_path.parent if self._profile_path else Path.cwd()
        base_name = self._profile_path.stem if self._profile_path else "profile"
        default_path = default_dir / f"{base_name}_{base_label}_to_{target_label}.json"
        saved = self._prompt_save_profile(scaled_profile, default_path)
        if saved:
            self._log(
                f"해상도/배율 변환 완료: {_format_resolution(base_res)}->{_format_resolution(target_res)}, "
                f"scale=({scale_x:.4f}, {scale_y:.4f}), 변경 {len(changes)}건"
            )
        return saved

    # 공용 ---------------------------------------------------------------
    def _prompt_save_profile(self, profile: MacroProfile, suggested_path: Path) -> bool:
        save_path, _ = QtWidgets.QFileDialog.getSaveFileName(
            self, "새 프로필 저장", str(suggested_path), "JSON Files (*.json)"
        )
        if not save_path:
            return False
        try:
            Path(save_path).write_text(json.dumps(profile.to_dict(), ensure_ascii=False, indent=2), encoding="utf-8")
        except Exception as exc:
            QtWidgets.QMessageBox.warning(self, "저장 실패", str(exc))
            return False
        QtWidgets.QMessageBox.information(self, "저장 완료", f"새 프로필을 저장했습니다.\n{save_path}")
        return True

    def _handle_save(self):
        if self.tabs.currentIndex() == 0:
            self._save_from_samples()
        else:
            self._save_from_scale()


class KeyboardSettingsDialog(QtWidgets.QDialog):
    def __init__(
        self,
        engine: MacroEngine,
        profile: MacroProfile,
        *,
        status_provider=None,
        apply_callback=None,
        install_callback=None,
        parent=None,
    ):
        super().__init__(parent)
        self.engine = engine
        self.profile = profile
        self._status_provider = status_provider
        self._apply_callback = apply_callback
        self._install_callback = install_callback
        self._status: dict | None = None
        self._kb_device_rows: dict[int, int] = {}
        self._kb_device_hwids: dict[str, int] = {}
        self._mouse_rows: dict[int, int] = {}
        self._mouse_hwids: dict[str, int] = {}
        self._friendly_map: dict[str, str] = {}
        self._activity_queue: queue.Queue = queue.Queue()
        self._activity_stop = threading.Event()
        self._activity_thread: threading.Thread | None = None
        self._activity_timer = QtCore.QTimer(self)
        self._activity_timer.setInterval(120)
        self._activity_timer.timeout.connect(self._drain_activity_queue)
        self._activity_running = False
        self._max_activity_rows = 150
        self.setWindowTitle("키보드 설정")
        self.resize(840, 680)
        self._anti_cheat_tip = "안티치트 환경에서는 하드웨어/소프트웨어 입력 모두 탐지될 수 있으며, 사용 책임은 사용자에게 있습니다."
        self._build_ui()
        self._activity_timer.start()
        self._load_from_profile(profile)
        self._refresh_status(True)
        self._start_activity_monitor(silent=True)

    def _build_ui(self):
        layout = QtWidgets.QVBoxLayout(self)

        mode_row = QtWidgets.QHBoxLayout()
        self.hardware_radio = QtWidgets.QRadioButton("하드웨어 (Interception)")
        self.software_radio = QtWidgets.QRadioButton("소프트웨어 (SendInput)")
        mode_row.addWidget(self.hardware_radio)
        mode_row.addWidget(self.software_radio)
        mode_row.addStretch()
        anti_label = QtWidgets.QLabel("안티치트 주의")
        anti_label.setStyleSheet("color: #c45656; font-weight: bold;")
        anti_label.setToolTip(self._anti_cheat_tip)
        mode_row.addWidget(anti_label)
        self.mode_status_label = QtWidgets.QLabel("")
        mode_row.addWidget(self.mode_status_label)
        layout.addLayout(mode_row)

        self.hardware_panel = QtWidgets.QGroupBox("하드웨어 입력 (Interception)")
        h_layout = QtWidgets.QVBoxLayout(self.hardware_panel)
        status_row = QtWidgets.QHBoxLayout()
        self.driver_badge = QtWidgets.QLabel("드라이버 상태")
        self.driver_badge.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)
        self.driver_badge.setMinimumWidth(140)
        self.driver_badge.setFrameShape(QtWidgets.QFrame.Shape.Panel)
        self.driver_badge.setFrameShadow(QtWidgets.QFrame.Shadow.Sunken)
        self.admin_badge = QtWidgets.QLabel("관리자 상태")
        self.admin_badge.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)
        self.admin_badge.setFrameShape(QtWidgets.QFrame.Shape.Panel)
        self.admin_badge.setFrameShadow(QtWidgets.QFrame.Shadow.Sunken)
        status_row.addWidget(self.driver_badge)
        status_row.addWidget(self.admin_badge)
        status_row.addStretch()
        self.install_btn = QtWidgets.QPushButton("Interception 설치 실행")
        self.install_btn.setToolTip("interception/install-interception.exe를 관리자 CMD로 실행합니다. 설치 후 재부팅이 필요합니다.")
        status_row.addWidget(self.install_btn)
        h_layout.addLayout(status_row)
        reboot_hint = QtWidgets.QLabel("설치/업데이트 후 재부팅이 필요할 수 있습니다.")
        reboot_hint.setStyleSheet("color: #a06000;")
        h_layout.addWidget(reboot_hint)

        device_row = QtWidgets.QHBoxLayout()
        device_row.setSpacing(12)

        kb_col = QtWidgets.QVBoxLayout()
        kb_col.addWidget(QtWidgets.QLabel("키보드 장치"))
        self.keyboard_table = QtWidgets.QTableWidget(0, 5)
        self.keyboard_table.setHorizontalHeaderLabels(["ID", "VID/PID", "하드웨어 ID", "FriendlyName", "기본"])
        kb_header = self.keyboard_table.horizontalHeader()
        kb_header.setSectionResizeMode(0, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        kb_header.setSectionResizeMode(1, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        kb_header.setSectionResizeMode(2, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        kb_header.setSectionResizeMode(3, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        kb_header.setStretchLastSection(True)
        self.keyboard_table.verticalHeader().setVisible(False)
        self.keyboard_table.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectionBehavior.SelectRows)
        self.keyboard_table.setEditTriggers(QtWidgets.QAbstractItemView.EditTrigger.NoEditTriggers)
        self.keyboard_table.setAlternatingRowColors(True)
        self.keyboard_table.setMinimumHeight(260)
        self.keyboard_table.setStyleSheet(
            "QTableWidget::item:selected { background: #c7f7c4; color: #000; }"
            "QTableWidget { selection-background-color: #c7f7c4; selection-color: #000; }"
        )
        kb_col.addWidget(self.keyboard_table)
        device_row.addLayout(kb_col)

        mouse_col = QtWidgets.QVBoxLayout()
        mouse_col.addWidget(QtWidgets.QLabel("마우스 장치"))
        self.mouse_table = QtWidgets.QTableWidget(0, 5)
        self.mouse_table.setHorizontalHeaderLabels(["ID", "VID/PID", "하드웨어 ID", "FriendlyName", "기본"])
        mouse_header = self.mouse_table.horizontalHeader()
        mouse_header.setSectionResizeMode(0, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        mouse_header.setSectionResizeMode(1, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        mouse_header.setSectionResizeMode(2, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        mouse_header.setSectionResizeMode(3, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        mouse_header.setStretchLastSection(True)
        self.mouse_table.verticalHeader().setVisible(False)
        self.mouse_table.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectionBehavior.SelectRows)
        self.mouse_table.setEditTriggers(QtWidgets.QAbstractItemView.EditTrigger.NoEditTriggers)
        self.mouse_table.setAlternatingRowColors(True)
        self.mouse_table.setMinimumHeight(260)
        self.mouse_table.setStyleSheet(
            "QTableWidget::item:selected { background: #c7f7c4; color: #000; }"
            "QTableWidget { selection-background-color: #c7f7c4; selection-color: #000; }"
        )
        mouse_col.addWidget(self.mouse_table)
        device_row.addLayout(mouse_col)

        h_layout.addLayout(device_row)

        hw_btn_row = QtWidgets.QHBoxLayout()
        self.refresh_btn = QtWidgets.QPushButton("새로고침")
        hw_btn_row.addWidget(self.refresh_btn)
        hw_btn_row.addStretch()
        h_layout.addLayout(hw_btn_row)

        self.activity_group = QtWidgets.QGroupBox("실시간 입력 감지 (키/마우스가 어느 장치에서 왔는지)")
        act_layout = QtWidgets.QVBoxLayout(self.activity_group)
        self.activity_hint = QtWidgets.QLabel("키보드/마우스를 눌러보면 장치 ID와 HWID가 아래 로그에 표시됩니다.")
        self.activity_hint.setWordWrap(True)
        act_layout.addWidget(self.activity_hint)
        self.activity_table = QtWidgets.QTableWidget(0, 5)
        self.activity_table.setHorizontalHeaderLabels(["시간", "장치", "종류", "입력", "HWID / Friendly"])
        act_header = self.activity_table.horizontalHeader()
        act_header.setSectionResizeMode(0, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        act_header.setSectionResizeMode(1, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        act_header.setSectionResizeMode(2, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        act_header.setSectionResizeMode(3, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        act_header.setStretchLastSection(True)
        self.activity_table.verticalHeader().setVisible(False)
        self.activity_table.setEditTriggers(QtWidgets.QAbstractItemView.EditTrigger.NoEditTriggers)
        self.activity_table.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectionBehavior.SelectRows)
        self.activity_table.setAlternatingRowColors(True)
        self.activity_table.setMinimumHeight(200)
        act_layout.addWidget(self.activity_table)
        act_btn_row = QtWidgets.QHBoxLayout()
        self.activity_toggle_btn = QtWidgets.QPushButton("실시간 감지 켜기")
        self.activity_clear_btn = QtWidgets.QPushButton("로그 지우기")
        act_btn_row.addWidget(self.activity_toggle_btn)
        act_btn_row.addWidget(self.activity_clear_btn)
        act_btn_row.addStretch()
        act_layout.addLayout(act_btn_row)
        h_layout.addWidget(self.activity_group)

        self.software_panel = QtWidgets.QGroupBox("소프트웨어 입력 (SendInput)")
        sw_layout = QtWidgets.QVBoxLayout(self.software_panel)
        sw_label = QtWidgets.QLabel("SendInput 기반으로 키를 전송합니다. 장치 선택은 없습니다.")
        sw_label.setWordWrap(True)
        sw_label.setToolTip(self._anti_cheat_tip)
        sw_layout.addWidget(sw_label)

        layout.addWidget(self.hardware_panel)
        layout.addWidget(self.software_panel)
        warn_label = QtWidgets.QLabel(self._anti_cheat_tip)
        warn_label.setWordWrap(True)
        warn_label.setStyleSheet("color: #c45656;")
        reboot_hint = QtWidgets.QLabel("Interception 설치/업데이트 후 재부팅이 필요할 수 있습니다.")
        reboot_hint.setStyleSheet("color: #a06000;")
        layout.addWidget(warn_label)
        layout.addWidget(reboot_hint)

        layout.addWidget(self._build_delay_group())

        test_row = QtWidgets.QHBoxLayout()
        test_row.addWidget(QtWidgets.QLabel("테스트 키"))
        self.test_key_combo = QtWidgets.QComboBox()
        for i in range(13, 25):
            key_name = f"F{i}"
            self.test_key_combo.addItem(key_name, key_name.lower())
        test_row.addWidget(self.test_key_combo)
        self.test_btn = QtWidgets.QPushButton("테스트 보내기")
        test_row.addWidget(self.test_btn)
        test_row.addStretch()
        layout.addLayout(test_row)

        footer = QtWidgets.QHBoxLayout()
        footer.addStretch()
        self.apply_btn = QtWidgets.QPushButton("설정 적용")
        self.close_btn = QtWidgets.QPushButton("닫기")
        footer.addWidget(self.apply_btn)
        footer.addWidget(self.close_btn)
        layout.addLayout(footer)

        self.hardware_radio.toggled.connect(self._set_mode_ui)
        self.software_radio.toggled.connect(self._set_mode_ui)
        self.refresh_btn.clicked.connect(lambda: self._refresh_status(True))
        self.install_btn.clicked.connect(self._run_install)
        self.activity_toggle_btn.clicked.connect(self._toggle_activity_monitor)
        self.activity_clear_btn.clicked.connect(self._clear_activity_log)
        self.apply_btn.clicked.connect(self._apply_clicked)
        self.close_btn.clicked.connect(self.close)
        self.test_btn.clicked.connect(self._test_clicked)

    def _build_delay_group(self) -> QtWidgets.QGroupBox:
        group = QtWidgets.QGroupBox("딜레이 설정 (글로벌 기본)")
        layout = QtWidgets.QGridLayout(group)

        delay_tip = "예: 40(고정) 또는 40-80(랜덤). ms 단위."
        self.press_delay_edit = QtWidgets.QLineEdit("")
        self.press_delay_edit.setPlaceholderText("기본 0ms(즉시) / 40 또는 40-80")
        self.press_delay_edit.setToolTip(delay_tip + " 비우면 0ms(즉시).")
        self.gap_delay_edit = QtWidgets.QLineEdit("")
        self.gap_delay_edit.setPlaceholderText("기본 0ms(즉시) / 40 또는 40-80")
        self.gap_delay_edit.setToolTip(delay_tip + " 비우면 0ms(즉시).")
        self.delay_preset_btn = QtWidgets.QPushButton("휴먼 프리셋")
        self.delay_preset_btn.setToolTip("누름 70-120ms, 키 사이 80-150ms")
        self.delay_preset_btn.clicked.connect(self._set_human_delay_preset)
        self.mouse_press_delay_edit = QtWidgets.QLineEdit("")
        self.mouse_press_delay_edit.setPlaceholderText("기본 0ms(즉시) / 40 또는 40-80")
        self.mouse_press_delay_edit.setToolTip(delay_tip + " 비우면 0ms(즉시).")
        self.mouse_gap_delay_edit = QtWidgets.QLineEdit("")
        self.mouse_gap_delay_edit.setPlaceholderText("기본 0ms(즉시) / 40 또는 40-80")
        self.mouse_gap_delay_edit.setToolTip(delay_tip + " 비우면 0ms(즉시).")
        self.mouse_delay_preset_btn = QtWidgets.QPushButton("휴먼 프리셋(마우스)")
        self.mouse_delay_preset_btn.setToolTip("누름 70-120ms, 클릭 사이 80-150ms")
        self.mouse_delay_preset_btn.clicked.connect(self._set_mouse_delay_preset)

        layout.addWidget(QtWidgets.QLabel("키 누름→뗌 지연"), 0, 0)
        layout.addWidget(self.press_delay_edit, 0, 1)
        layout.addWidget(QtWidgets.QLabel("키 사이 지연"), 1, 0)
        layout.addWidget(self.gap_delay_edit, 1, 1)
        layout.addWidget(self.delay_preset_btn, 0, 2, 2, 1)
        layout.addWidget(QtWidgets.QLabel("마우스 누름→뗌 지연"), 2, 0)
        layout.addWidget(self.mouse_press_delay_edit, 2, 1)
        layout.addWidget(QtWidgets.QLabel("마우스 입력 사이 지연"), 3, 0)
        layout.addWidget(self.mouse_gap_delay_edit, 3, 1)
        layout.addWidget(self.mouse_delay_preset_btn, 2, 2, 2, 1)
        hint = QtWidgets.QLabel("입력 값 그대로 적용(추가 지연 아님). 비우면 0ms로 처리됩니다.")
        hint.setStyleSheet("color: gray;")
        layout.addWidget(hint, 4, 0, 1, 3)

        return group

    def _load_from_profile(self, profile: MacroProfile):
        mode = getattr(profile, "input_mode", "hardware")
        if mode == "hardware":
            self.hardware_radio.setChecked(True)
        else:
            self.software_radio.setChecked(True)
        delay: KeyDelayConfig = getattr(profile, "key_delay", KeyDelayConfig())
        press_txt = _delay_text_from_config(delay, press=True)
        gap_txt = _delay_text_from_config(delay, press=False)
        self.press_delay_edit.setText("" if press_txt in ("0", "0-0") else press_txt)
        self.gap_delay_edit.setText("" if gap_txt in ("0", "0-0") else gap_txt)
        mouse_delay: KeyDelayConfig = getattr(profile, "mouse_delay", KeyDelayConfig())
        mouse_press_txt = _delay_text_from_config(mouse_delay, press=True)
        mouse_gap_txt = _delay_text_from_config(mouse_delay, press=False)
        self.mouse_press_delay_edit.setText("" if mouse_press_txt in ("0", "0-0") else mouse_press_txt)
        self.mouse_gap_delay_edit.setText("" if mouse_gap_txt in ("0", "0-0") else mouse_gap_txt)
        self.test_key_combo.setCurrentIndex(max(0, self.test_key_combo.findData(getattr(profile, "keyboard_test_key", "f24"))))

    def _delay_config_from_ui(self) -> tuple[KeyDelayConfig, KeyDelayConfig]:
        press_val, press_rand, press_min, press_max = _parse_delay_text(self.press_delay_edit.text())
        gap_val, gap_rand, gap_min, gap_max = _parse_delay_text(self.gap_delay_edit.text())
        key_cfg = KeyDelayConfig(
            press_delay_ms=press_val,
            press_delay_random=press_rand,
            press_delay_min_ms=press_min,
            press_delay_max_ms=press_max,
            gap_delay_ms=gap_val,
            gap_delay_random=gap_rand,
            gap_delay_min_ms=gap_min,
            gap_delay_max_ms=gap_max,
        )
        m_press_val, m_press_rand, m_press_min, m_press_max = _parse_delay_text(self.mouse_press_delay_edit.text())
        m_gap_val, m_gap_rand, m_gap_min, m_gap_max = _parse_delay_text(self.mouse_gap_delay_edit.text())
        mouse_cfg = KeyDelayConfig(
            press_delay_ms=m_press_val,
            press_delay_random=m_press_rand,
            press_delay_min_ms=m_press_min,
            press_delay_max_ms=m_press_max,
            gap_delay_ms=m_gap_val,
            gap_delay_random=m_gap_rand,
            gap_delay_min_ms=m_gap_min,
            gap_delay_max_ms=m_gap_max,
        )
        return key_cfg, mouse_cfg

    def _set_human_delay_preset(self):
        self.press_delay_edit.setText("70-120")
        self.gap_delay_edit.setText("80-150")
        self._set_mouse_delay_preset()

    def _set_mouse_delay_preset(self):
        self.mouse_press_delay_edit.setText("70-120")
        self.mouse_gap_delay_edit.setText("80-150")

    def _refresh_status(self, force: bool = False):
        provider = self._status_provider or (lambda refresh=True: {})
        try:
            self._status = provider(refresh=force) or {}
        except Exception:
            self._status = {}
        backend = self._status or {}
        hardware = backend.get("hardware") or {}
        active_mode = backend.get("active_mode") or backend.get("requested_mode") or "-"
        self.mode_status_label.setText(f"현재 동작: {active_mode}")
        installed = hardware.get("installed")
        admin_ok = hardware.get("admin")
        msg = hardware.get("message") or ""
        self.driver_badge.setText("설치됨" if installed else "미설치")
        self.driver_badge.setStyleSheet(f"background: {'#d1f2d1' if installed else '#ffe1e1'};")
        admin_txt = "관리자" if admin_ok is not False else "관리자 아님"
        self.admin_badge.setText(admin_txt)
        self.admin_badge.setStyleSheet(f"background: {'#d1f2d1' if admin_ok is not False else '#ffe1e1'};")
        if msg:
            self.driver_badge.setToolTip(msg)
            self.admin_badge.setToolTip(msg)
        devices = hardware.get("devices") or []
        kb_devices = hardware.get("keyboard_devices") or [d for d in devices if d.get("is_keyboard")]
        mouse_devices = hardware.get("mouse_devices") or [d for d in devices if d.get("is_mouse")]
        self._kb_device_rows = {}
        self._kb_device_hwids = {}
        self._mouse_rows = {}
        self._mouse_hwids = {}
        self._friendly_map = {}
        kb_target = hardware.get("current_device") or {}
        kb_target_id = kb_target.get("id") or self.profile.keyboard_device_id
        kb_target_hwid = (kb_target.get("hardware_id") or self.profile.keyboard_hardware_id or "").lower()
        mouse_target = hardware.get("current_mouse") or {}
        mouse_target_id = mouse_target.get("id") or getattr(self.profile, "mouse_device_id", None)
        mouse_target_hwid = (mouse_target.get("hardware_id") or getattr(self.profile, "mouse_hardware_id", "") or "").lower()
        kb_target_row = 0
        mouse_target_row = 0

        self.keyboard_table.setRowCount(len(kb_devices))
        for idx, dev in enumerate(kb_devices):
            hwid = dev.get("hardware_id") or ""
            friendly = dev.get("friendly_name") or ""
            is_default = dev.get("is_default") or False
            dev_id = None
            try:
                dev_id = int(dev.get("id")) if dev.get("id") is not None else None
            except Exception:
                dev_id = None
            vidpid = _short_hwid(hwid)
            if dev_id:
                self._kb_device_rows[dev_id] = idx
            if hwid:
                self._kb_device_hwids[hwid.lower()] = idx
                self._friendly_map[hwid.lower()] = friendly
            item0 = QtWidgets.QTableWidgetItem(str(dev_id) if dev_id is not None else "")
            try:
                item0.setData(QtCore.Qt.ItemDataRole.UserRole, dev_id)  # type: ignore[arg-type]
            except Exception:
                pass
            self.keyboard_table.setItem(idx, 0, item0)
            self.keyboard_table.setItem(idx, 1, QtWidgets.QTableWidgetItem(vidpid))
            self.keyboard_table.setItem(idx, 2, QtWidgets.QTableWidgetItem(hwid))
            self.keyboard_table.setItem(idx, 3, QtWidgets.QTableWidgetItem(friendly))
            self.keyboard_table.setItem(idx, 4, QtWidgets.QTableWidgetItem("기본" if is_default else ""))
            if dev.get("id") == kb_target_id or (hwid and hwid.lower() == kb_target_hwid):
                kb_target_row = idx
        if kb_devices:
            self.keyboard_table.selectRow(kb_target_row)

        self.mouse_table.setRowCount(len(mouse_devices))
        for idx, dev in enumerate(mouse_devices):
            hwid = dev.get("hardware_id") or ""
            friendly = dev.get("friendly_name") or ""
            is_default = dev.get("is_default") or False
            dev_id = None
            try:
                dev_id = int(dev.get("id")) if dev.get("id") is not None else None
            except Exception:
                dev_id = None
            vidpid = _short_hwid(hwid)
            if dev_id:
                self._mouse_rows[dev_id] = idx
            if hwid:
                self._mouse_hwids[hwid.lower()] = idx
                self._friendly_map[hwid.lower()] = friendly
            item0 = QtWidgets.QTableWidgetItem(str(dev_id) if dev_id is not None else "")
            try:
                item0.setData(QtCore.Qt.ItemDataRole.UserRole, dev_id)  # type: ignore[arg-type]
            except Exception:
                pass
            self.mouse_table.setItem(idx, 0, item0)
            self.mouse_table.setItem(idx, 1, QtWidgets.QTableWidgetItem(vidpid))
            self.mouse_table.setItem(idx, 2, QtWidgets.QTableWidgetItem(hwid))
            self.mouse_table.setItem(idx, 3, QtWidgets.QTableWidgetItem(friendly))
            self.mouse_table.setItem(idx, 4, QtWidgets.QTableWidgetItem("기본" if is_default else ""))
            if dev.get("id") == mouse_target_id or (hwid and hwid.lower() == mouse_target_hwid):
                mouse_target_row = idx
        if mouse_devices:
            self.mouse_table.selectRow(mouse_target_row)

        self._update_activity_hint(installed=installed, admin_ok=admin_ok, has_device=bool(kb_devices or mouse_devices))
        self._set_mode_ui()

    def _set_mode_ui(self):
        hw = self.hardware_radio.isChecked()
        self.hardware_panel.setVisible(hw)
        self.software_panel.setVisible(not hw)

    def _selected_keyboard(self) -> dict | None:
        row = self.keyboard_table.currentRow()
        if row < 0:
            return None
        id_item = self.keyboard_table.item(row, 0)
        hwid_item = self.keyboard_table.item(row, 2)
        friendly_item = self.keyboard_table.item(row, 3)
        hwid = hwid_item.text() if hwid_item else ""
        friendly = friendly_item.text() if friendly_item else ""
        dev_id = None
        try:
            dev_id = int(id_item.data(QtCore.Qt.ItemDataRole.UserRole)) if id_item else None
        except Exception:
            dev_id = None
        return {"id": dev_id, "hardware_id": hwid, "friendly_name": friendly}

    def _selected_mouse(self) -> dict | None:
        row = self.mouse_table.currentRow()
        if row < 0:
            return None
        id_item = self.mouse_table.item(row, 0)
        hwid_item = self.mouse_table.item(row, 2)
        friendly_item = self.mouse_table.item(row, 3)
        hwid = hwid_item.text() if hwid_item else ""
        friendly = friendly_item.text() if friendly_item else ""
        dev_id = None
        try:
            dev_id = int(id_item.data(QtCore.Qt.ItemDataRole.UserRole)) if id_item else None
        except Exception:
            dev_id = None
        return {"id": dev_id, "hardware_id": hwid, "friendly_name": friendly}

    def _apply_clicked(self):
        if not callable(self._apply_callback):
            return
        mode = "hardware" if self.hardware_radio.isChecked() else "software"
        selected = self._selected_keyboard() if mode == "hardware" else None
        mouse_selected = self._selected_mouse() if mode == "hardware" else None
        device_id = selected.get("id") if isinstance(selected, dict) else None
        hwid = selected.get("hardware_id") if isinstance(selected, dict) else None
        mouse_device_id = mouse_selected.get("id") if isinstance(mouse_selected, dict) else None
        mouse_hwid = mouse_selected.get("hardware_id") if isinstance(mouse_selected, dict) else None
        key_delay_cfg, mouse_delay_cfg = self._delay_config_from_ui()
        test_key = self.test_key_combo.currentData() or "f24"
        try:
            status = self._apply_callback(
                mode=mode,
                device_id=device_id,
                hardware_id=hwid,
                mouse_device_id=mouse_device_id,
                mouse_hardware_id=mouse_hwid,
                key_delay=key_delay_cfg,
                mouse_delay=mouse_delay_cfg,
                test_key=test_key,
            )
            if status:
                self._status = status
        except Exception as exc:
            QtWidgets.QMessageBox.warning(self, "설정 적용 실패", str(exc))
        self._refresh_status(False)

    def _run_install(self):
        if callable(self._install_callback):
            self._install_callback()

    def _test_clicked(self):
        key = self.test_key_combo.currentData() or "f24"
        ok, msg = self.engine.test_keyboard(key)
        QtWidgets.QMessageBox.information(self, "테스트", msg if ok else f"실패: {msg}")

    # 실시간 입력 감지 ---------------------------------------------------------
    def _update_activity_hint(self, *, installed: bool, admin_ok: bool, has_device: bool):
        if not hasattr(self, "activity_hint"):
            return
        if not installed:
            self.activity_hint.setText("Interception 미설치: 설치/재부팅 후 사용 가능합니다.")
            self.activity_toggle_btn.setEnabled(False)
            return
        if admin_ok is False:
            self.activity_hint.setText("관리자 권한 필요: 관리자 실행 후 사용 가능합니다.")
            self.activity_toggle_btn.setEnabled(False)
            return
        if not has_device:
            self.activity_hint.setText("Interception 키보드/마우스가 보이지 않습니다.")
            self.activity_toggle_btn.setEnabled(False)
            return
        self.activity_hint.setText("키보드/마우스를 눌러보면 장치 ID와 HWID가 아래 로그에 표시됩니다.")
        self.activity_toggle_btn.setEnabled(True)

    def _toggle_activity_monitor(self):
        if self._activity_running:
            self._stop_activity_monitor()
        else:
            self._start_activity_monitor()

    def _start_activity_monitor(self, *, silent: bool = False):
        if self._activity_running:
            return
        hardware = (self._status or {}).get("hardware") or {}
        installed = bool(hardware.get("installed"))
        admin_ok = hardware.get("admin")
        devices_list = hardware.get("devices") or hardware.get("keyboard_devices") or hardware.get("mouse_devices") or []
        has_device = bool(devices_list)
        if not installed:
            if not silent:
                QtWidgets.QMessageBox.information(self, "Interception 필요", "Interception 설치 후 재부팅이 필요합니다.")
            return
        if admin_ok is False:
            if not silent:
                QtWidgets.QMessageBox.information(self, "관리자 권한 필요", "관리자 권한으로 실행해야 입력을 감지할 수 있습니다.")
            return
        if not has_device:
            if not silent:
                QtWidgets.QMessageBox.information(self, "장치 없음", "Interception이 키보드/마우스 장치를 찾지 못했습니다.")
            return
        self._activity_stop.clear()
        self._activity_thread = threading.Thread(target=self._activity_loop, name="ActivityMonitor", daemon=True)
        self._activity_thread.start()
        self._activity_running = True
        if hasattr(self, "activity_toggle_btn"):
            self.activity_toggle_btn.setText("실시간 감지 끄기")
        if hasattr(self, "activity_hint"):
            self.activity_hint.setText("감지 중: 키/마우스를 눌러 장치를 확인하세요.")

    def _stop_activity_monitor(self):
        self._activity_stop.set()
        t = self._activity_thread
        if t and t.is_alive():
            t.join(timeout=1.0)
        self._activity_thread = None
        self._activity_running = False
        if hasattr(self, "activity_toggle_btn"):
            self.activity_toggle_btn.setText("실시간 감지 켜기")

    def _clear_activity_log(self):
        if hasattr(self, "activity_table"):
            self.activity_table.setRowCount(0)

    def _activity_loop(self):
        try:
            inter = Interception()
            inter.set_keyboard_filter(KeyFilter.All)
            inter.set_mouse_filter(MouseFilter.All)
            ctx = getattr(inter, "_context", [])
            # 장치 ID -> HWID 매핑 (활동 로그 보완용)
            devices_info = kbutil.list_interception_devices(friendly=False)
            self._activity_hwid_map = {info.get("id"): info.get("hardware_id") or "" for info in devices_info}
            self._activity_hwid_map_by_idx = {idx + 1: info.get("hardware_id") or "" for idx, info in enumerate(devices_info)}
        except Exception as exc:
            self._activity_queue.put({"type": "error", "message": str(exc)})
            return
        while not self._activity_stop.is_set():
            device = inter.wait_receive(200)
            if not device:
                continue
            try:
                entry = self._build_activity_entry(device, ctx)
                if entry:
                    self._activity_queue.put(entry)
            except Exception as exc:
                self._activity_queue.put({"type": "error", "message": str(exc)})
                break
            try:
                device.send()
            except Exception:
                pass

    def _is_mouse_move(self, stroke) -> bool:
        ms = MouseState if "MouseState" in globals() else None
        if not ms:
            return False
        try:
            return ms(stroke.state) == getattr(ms, "Move", None)
        except Exception:
            return False

    def _build_activity_entry(self, device, ctx) -> dict | None:
        hwid = ""
        try:
            hwid = device.get_hardware_id() or ""
        except Exception:
            hwid = ""
        device_id = None
        try:
            device_id = ctx.index(device) + 1 if ctx else None
        except ValueError:
            device_id = None
        entry: dict = {
            "type": "keyboard" if getattr(device, "is_keyboard", False) else "mouse",
            "ts": time.time(),
            "device_id": device_id,
            "hwid": hwid
            or (self._activity_hwid_map.get(device_id) if hasattr(self, "_activity_hwid_map") else "")
            or (self._activity_hwid_map_by_idx.get(device_id) if hasattr(self, "_activity_hwid_map_by_idx") else ""),
        }
        stroke = getattr(device, "stroke", None)
        if stroke and getattr(device, "is_keyboard", False):
            entry["detail"] = self._format_key_detail(stroke)
        elif stroke:
            if self._is_mouse_move(stroke):
                return None  # 마우스 이동은 로그에서 제외
            entry["detail"] = self._format_mouse_detail(stroke)
        else:
            entry["detail"] = "입력"
        return entry

    def _friendly_from_hwid(self, hwid: str) -> str:
        if not hwid:
            return ""
        return self._friendly_map.get(hwid.lower()) or self._friendly_map.get(hwid.upper(), "")

    def _format_key_detail(self, stroke) -> str:
        try:
            state = KeyState(stroke.state)
        except Exception:
            state = None
        state_txt = {
            KeyState.Down: "Down",
            KeyState.Up: "Up",
            KeyState.E0Down: "E0 Down",
            KeyState.E0Up: "E0 Up",
            KeyState.E1Down: "E1 Down",
            KeyState.E1Up: "E1 Up",
        }.get(state, f"state={getattr(stroke, 'state', '-')}")
        vk_txt = ""
        try:
            vk = map_virtual_key(int(stroke.code), MapVk.ScToVk)
            if vk:
                ch = chr(vk)
                vk_txt = f"{ch} (VK {vk})" if ch.isprintable() and len(ch) == 1 else f"VK {vk}"
        except Exception:
            vk_txt = ""
        base = f"SC {getattr(stroke, 'code', '-')}"
        if vk_txt:
            base = f"{vk_txt} / {base}"
        return f"{base} [{state_txt}]"

    def _format_mouse_detail(self, stroke) -> str:
        ms = MouseState if "MouseState" in globals() else None
        try:
            state = ms(stroke.state) if ms else None
        except Exception:
            state = None
        mapping = {
            getattr(ms, "LeftButtonDown", None): "Left Down" if ms else None,
            getattr(ms, "LeftButtonUp", None): "Left Up" if ms else None,
            getattr(ms, "RightButtonDown", None): "Right Down" if ms else None,
            getattr(ms, "RightButtonUp", None): "Right Up" if ms else None,
            getattr(ms, "MiddleButtonDown", None): "Middle Down" if ms else None,
            getattr(ms, "MiddleButtonUp", None): "Middle Up" if ms else None,
            getattr(ms, "XButton1Down", None): "X1 Down" if ms else None,
            getattr(ms, "XButton1Up", None): "X1 Up" if ms else None,
            getattr(ms, "XButton2Down", None): "X2 Down" if ms else None,
            getattr(ms, "XButton2Up", None): "X2 Up" if ms else None,
            getattr(ms, "VerticalWheel", None): "Wheel V" if ms else None,
            getattr(ms, "HorizontalWheel", None): "Wheel H" if ms else None,
            getattr(ms, "Move", None): "Move" if ms else None,
        } if ms else {}
        label = mapping.get(state, f"state={getattr(stroke, 'state', '-')}")
        rolling = getattr(stroke, "rolling", 0)
        if state in (getattr(ms, "VerticalWheel", None), getattr(ms, "HorizontalWheel", None)):
            label += f" ({rolling})"
        x = getattr(stroke, "x", 0)
        y = getattr(stroke, "y", 0)
        if x or y:
            label += f" x={x} y={y}"
        return label

    def _drain_activity_queue(self):
        if not hasattr(self, "activity_table"):
            return
        changed = False
        while True:
            try:
                entry = self._activity_queue.get_nowait()
            except queue.Empty:
                break
            changed = True
            if entry.get("type") == "error":
                if hasattr(self, "activity_hint"):
                    self.activity_hint.setText(f"실시간 감지 오류: {entry.get('message')}")
                self._stop_activity_monitor()
                continue
            self._add_activity_entry(entry)
        if changed and getattr(self, "activity_table", None):
            self.activity_table.resizeRowsToContents()

    def _add_activity_entry(self, entry: dict):
        if not hasattr(self, "activity_table"):
            return
        row = 0
        self.activity_table.insertRow(row)
        ts = float(entry.get("ts", time.time()))
        base = time.strftime("%H:%M:%S", time.localtime(ts))
        ms = int((ts - int(ts)) * 1000)
        ts_txt = f"{base}.{ms:03d}"
        dev_id = entry.get("device_id")
        device_txt = f"#{dev_id}" if dev_id else "-"
        kind_txt = "키보드" if entry.get("type") == "keyboard" else "마우스"
        detail = entry.get("detail") or ""
        hwid = entry.get("hwid") or ""
        vidpid = _short_hwid(hwid)
        friendly = self._friendly_from_hwid(hwid)
        hwid_cell = vidpid
        if friendly and vidpid:
            hwid_cell = f"{vidpid} ({friendly})"
        elif friendly:
            hwid_cell = friendly
        elif hwid:
            hwid_cell = hwid
        self.activity_table.setItem(row, 0, QtWidgets.QTableWidgetItem(ts_txt))
        self.activity_table.setItem(row, 1, QtWidgets.QTableWidgetItem(device_txt))
        self.activity_table.setItem(row, 2, QtWidgets.QTableWidgetItem(kind_txt))
        self.activity_table.setItem(row, 3, QtWidgets.QTableWidgetItem(detail))
        self.activity_table.setItem(row, 4, QtWidgets.QTableWidgetItem(hwid_cell))
        if self.activity_table.rowCount() > self._max_activity_rows:
            self.activity_table.removeRow(self.activity_table.rowCount() - 1)
        self._highlight_device_row(dev_id, hwid, entry.get("type"))

    def _highlight_device_row(self, dev_id=None, hwid: str | None = None, kind: str | None = None):
        table = None
        rows = {}
        hwids = {}
        if kind == "mouse":
            table = getattr(self, "mouse_table", None)
            rows = self._mouse_rows or {}
            hwids = self._mouse_hwids or {}
        else:
            table = getattr(self, "keyboard_table", None)
            rows = self._kb_device_rows or {}
            hwids = self._kb_device_hwids or {}
        if table is None:
            return
        row = None
        if hwid:
            row = hwids.get(hwid.lower())
        if row is None and dev_id and dev_id in rows:
            row = rows.get(dev_id)
        if row is None or row < 0:
            return
        try:
            table.selectRow(row)
            item = table.item(row, 0)
            if item:
                table.scrollToItem(item)
            self._flash_device_row(table, row)
        except Exception:
            pass

    def _flash_device_row(self, table, row: int, *, duration_ms: int = 600):
        if table is None or row < 0:
            return
        cols = table.columnCount()
        for c in range(cols):
            item = table.item(row, c)
            if item is None:
                item = QtWidgets.QTableWidgetItem("")
                table.setItem(row, c, item)
            item.setBackground(QtGui.QBrush(QtGui.QColor("#c7f7c4")))
        QtCore.QTimer.singleShot(duration_ms, lambda r=row, t=table: self._reset_device_row_color(t, r))

    def _reset_device_row_color(self, table, row: int):
        if table is None or row < 0 or row >= table.rowCount():
            return
        cols = table.columnCount()
        for c in range(cols):
            item = table.item(row, c)
            if item:
                item.setBackground(QtGui.QBrush())

    def closeEvent(self, event: QtGui.QCloseEvent):
        self._stop_activity_monitor()
        return super().closeEvent(event)

class MacroWindow(QtWidgets.QMainWindow):
    def __init__(self, engine: MacroEngine, profile: MacroProfile | None = None):
        super().__init__()
        self.engine = engine
        self.is_admin = _is_admin()
        self.profile = copy.deepcopy(profile or DEFAULT_PROFILE)
        self.current_profile_path: str | None = None
        self.base_title = "Interception Macro GUI"
        self.dirty: bool = False
        self._loading_profile = False
        self._state_path = Path.home() / ".interception_macro_gui.json"
        self._state: dict = self._load_state()
        self._debugger_state = self._state.get("debugger", {}) if isinstance(self._state, dict) else {}
        self._image_viewer_state = self._state.get("image_viewer", {}) if isinstance(self._state, dict) else {}
        self._color_calc_state = self._state.get("color_calc", {}) if isinstance(self._state, dict) else {}
        self._log_enabled = bool(self._state.get("log_enabled", True)) if isinstance(self._state, dict) else True
        self.debugger: DebuggerDialog | None = None
        self._image_viewer_dialog: ImageViewerDialog | None = None
        self._color_calc_dialog: ColorToleranceDialog | None = None
        self._keyboard_settings_dialog: KeyboardSettingsDialog | None = None
        self._last_backend_state: dict | None = None
        pixel_state = self._state.get("pixel_test", {}) if isinstance(self._state, dict) else {}
        self._pixel_test_defaults = {
            "region_raw": pixel_state.get("region"),
            "color_raw": pixel_state.get("color"),
            "tolerance": pixel_state.get("tolerance"),
            "expect_exists": pixel_state.get("expect_exists"),
            "interval": pixel_state.get("interval", 200),
        }
        self._updating_resolution_fields = False
        self._pixel_test_timer = QtCore.QTimer(self)
        self._pixel_test_timer.setSingleShot(False)
        self._pixel_test_timer.timeout.connect(self._tick_pixel_test)
        self._pixel_test_config: dict | None = None
        self._pixel_test_dialog: QtWidgets.QDialog | None = None
        self._condition_debug_key_states: dict[str, bool] = {}
        self._condition_debug_on_stop = None
        self._condition_debug_active = False
        self._last_condition_tree: dict | None = None
        self._fail_capture_hotkey_prev = False
        self._fail_capture_hotkey_key = "f12"
        self._last_capture_running: bool = False
        screenshot_state = self._state.get("screenshot", {}) if isinstance(self._state, dict) else {}
        self.screenshot_manager = ScreenCaptureManager(
            interval_seconds=screenshot_state.get("interval", CAPTURE_INTERVAL_SECONDS),
            image_format=screenshot_state.get("format", DEFAULT_FORMAT),
            jpeg_quality=screenshot_state.get("jpeg_quality", DEFAULT_JPEG_QUALITY),
            png_compress_level=screenshot_state.get("png_compress_level", DEFAULT_PNG_COMPRESS_LEVEL),
            max_queue_size=screenshot_state.get("queue_size", MAX_QUEUE_SIZE),
        )
        self._theme = self._compute_theme_colors()
        self.screenshot_manager.configure_hotkeys(
            screenshot_state.get("hotkey_start"),
            screenshot_state.get("hotkey_stop"),
            screenshot_state.get("hotkey_capture"),
            enabled=bool(screenshot_state.get("hotkey_enabled")),
        )
        self._screenshot_dialog: ScreenshotDialog | None = None
        self.setWindowTitle(self.base_title)
        self.resize(1100, 820)
        self.setMinimumWidth(780)

        self._build_ui()
        self._build_menu()
        self._install_shortcuts()
        loaded = self._load_last_session()
        if not loaded:
            self._refresh_macros()
            self._set_variable_fields(self.profile.variables)
            self._refresh_pixel_defaults(self.profile)
            self._mark_dirty(False)
        self._connect_signals()
        self._log_admin_status()

        self.engine.update_profile(self.profile)
        self._refresh_pixel_defaults(self.profile)
        try:
            backend_state = self.engine.keyboard_status(refresh=True)
        except Exception:
            backend_state = {}
        self._update_keyboard_summary(backend_state)
        self._last_backend_state = backend_state
        self.profile.input_mode = backend_state.get("requested_mode", self.profile.input_mode)
        self.engine.start()

        self.poll_timer = QtCore.QTimer(self)
        self.poll_timer.setInterval(100)
        self.poll_timer.timeout.connect(self._poll_engine)
        self.poll_timer.start()

        self._status_hint = "Home=활성, Insert=일시정지, End=종료, 기능 메뉴=디버거/픽셀 테스트"
        self.statusBar().showMessage(self._status_hint)
        self._set_capture_status(self.screenshot_manager.is_running)

    def _show_apply_feedback(self, ok: bool):
        """적용 버튼에 짧은 색상 피드백 표시."""
        if not getattr(self, "_apply_flash_timer", None):
            return
        if self._apply_flash_timer.isActive():
            self._apply_flash_timer.stop()
        if ok:
            style = (
                self._apply_btn_default_style
                + " background: #2ecc71; color: #ffffff; border-color: #2ecc71;"
            )
        else:
            style = (
                self._apply_btn_default_style
                + " background: #d64545; color: #ffffff; border-color: #d64545;"
            )
        self.apply_btn.setStyleSheet(style)
        self._apply_flash_timer.start(700)

    def _handle_apply_click(self):
        if getattr(self, "_apply_btn_working_style", None):
            self.apply_btn.setStyleSheet(self._apply_btn_working_style)
            try:
                QtWidgets.QApplication.processEvents(QtCore.QEventLoop.ProcessEventsFlag.AllEvents, 50)
            except Exception:
                pass
        ok = bool(self._apply_profile())
        self._show_apply_feedback(ok)

    def _install_shortcuts(self):
        """설정 적용 단축키 등 공용 단축키 등록."""
        self.apply_shortcut = QtGui.QShortcut(QtGui.QKeySequence("Ctrl+Shift+P"), self)
        self.apply_shortcut.setContext(QtCore.Qt.ShortcutContext.ApplicationShortcut)
        self.apply_shortcut.activated.connect(self._handle_apply_click)

    # UI ------------------------------------------------------------------
    def _build_ui(self):
        central = QtWidgets.QWidget()
        self.setCentralWidget(central)

        layout = QtWidgets.QVBoxLayout(central)
        layout.setContentsMargins(10, 6, 10, 6)
        layout.setSpacing(6)

        header = QtWidgets.QWidget()
        header_layout = QtWidgets.QVBoxLayout(header)
        header_layout.setContentsMargins(0, 0, 0, 0)
        header_layout.setSpacing(6)
        header_layout.addWidget(self._build_status_row())
        header_layout.addWidget(self._build_device_group())
        layout.addWidget(header)

        macro_group = self._build_macro_group()
        variable_group = self._build_variable_group()
        log_group = self._build_log_group()

        layout.addWidget(macro_group, stretch=3)
        layout.addWidget(variable_group, stretch=2)
        layout.addWidget(log_group, stretch=2)
        layout.setStretch(0, 0)  # header
        layout.setStretch(1, 3)  # macro
        layout.setStretch(2, 2)  # variable
        layout.setStretch(3, 2)  # log

    def _build_menu(self):
        menu_bar = self.menuBar()
        file_menu = menu_bar.addMenu("파일(&F)")

        new_action = QtGui.QAction("새로 만들기", self)
        new_action.setShortcut("Ctrl+N")
        new_action.triggered.connect(self._new_profile)

        load_action = QtGui.QAction("불러오기", self)
        load_action.setShortcut("Ctrl+O")
        load_action.triggered.connect(self._load_profile)

        save_action = QtGui.QAction("저장", self)
        save_action.setShortcut("Ctrl+S")
        save_action.triggered.connect(self._save_profile)

        save_as_action = QtGui.QAction("다른 이름으로 저장", self)
        save_as_action.setShortcut("Ctrl+Shift+S")
        save_as_action.triggered.connect(self._save_profile_as)

        for act in (new_action, load_action, save_action, save_as_action):
            file_menu.addAction(act)

        feature_menu = menu_bar.addMenu("기능(&G)")
        screenshot_action = QtGui.QAction("스크린샷", self)
        screenshot_action.triggered.connect(self._open_screenshot_dialog)
        feature_menu.addAction(screenshot_action)
        debugger_action = QtGui.QAction("디버거", self)
        debugger_action.triggered.connect(self._open_debugger)
        feature_menu.addAction(debugger_action)
        pixel_test_action = QtGui.QAction("픽셀 테스트", self)
        pixel_test_action.triggered.connect(self._open_pixel_test_dialog)
        feature_menu.addAction(pixel_test_action)
        preset_transfer_action = QtGui.QAction("프리셋 옮기기...", self)
        preset_transfer_action.triggered.connect(self._open_preset_transfer_dialog)
        feature_menu.addAction(preset_transfer_action)
        color_calc_action = QtGui.QAction("색상값 계산", self)
        color_calc_action.triggered.connect(self._open_color_calc_dialog)
        feature_menu.addAction(color_calc_action)
        image_viewer_action = QtGui.QAction("이미지 뷰어/피커", self)
        image_viewer_action.triggered.connect(self._open_image_viewer_dialog)
        feature_menu.addAction(image_viewer_action)

        settings_menu = menu_bar.addMenu("설정(&S)")
        keyboard_settings_action = QtGui.QAction("키보드 설정", self)
        keyboard_settings_action.triggered.connect(self._open_keyboard_settings)
        settings_menu.addAction(keyboard_settings_action)

    def _open_screenshot_dialog(self):
        if self._screenshot_dialog is None:
            self._screenshot_dialog = ScreenshotDialog(
                self.screenshot_manager,
                self,
                save_state_cb=self._persist_screenshot_state,
            )
        self._screenshot_dialog._update_status()
        self._screenshot_dialog.show()
        self._screenshot_dialog.raise_()
        self._screenshot_dialog.activateWindow()

    def _open_keyboard_settings(self):
        if self._keyboard_settings_dialog is None:
            self._keyboard_settings_dialog = KeyboardSettingsDialog(
                self.engine,
                self.profile,
                status_provider=lambda refresh=True: self.engine.keyboard_status(refresh=refresh),
                apply_callback=self._apply_keyboard_settings,
                install_callback=self._run_interception_installer,
                parent=self,
            )
        else:
            self._keyboard_settings_dialog.profile = self.profile
            self._keyboard_settings_dialog._load_from_profile(self.profile)
        try:
            status = self.engine.keyboard_status(refresh=True)
        except Exception:
            status = self._last_backend_state or {}
        self._keyboard_settings_dialog._status = status
        self._keyboard_settings_dialog._refresh_status(False)
        self._keyboard_settings_dialog.show()
        self._keyboard_settings_dialog.raise_()
        self._keyboard_settings_dialog.activateWindow()

    def _apply_keyboard_settings(
        self,
        *,
        mode: str,
        device_id=None,
        hardware_id=None,
        mouse_device_id=None,
        mouse_hardware_id=None,
        key_delay=None,
        mouse_delay=None,
        test_key: str | None = None,
    ):
        delay_cfg = key_delay if isinstance(key_delay, KeyDelayConfig) else KeyDelayConfig()
        mouse_delay_cfg = mouse_delay if isinstance(mouse_delay, KeyDelayConfig) else KeyDelayConfig()
        self.profile.input_mode = mode
        self.profile.key_delay = delay_cfg
        self.profile.mouse_delay = mouse_delay_cfg
        self.profile.keyboard_device_id = device_id
        self.profile.keyboard_hardware_id = hardware_id
        self.profile.mouse_device_id = mouse_device_id
        self.profile.mouse_hardware_id = mouse_hardware_id
        if test_key:
            self.profile.keyboard_test_key = test_key
        status = self.engine.apply_keyboard_settings(
            mode=mode,
            device_id=self.profile.keyboard_device_id,
            hardware_id=self.profile.keyboard_hardware_id,
            mouse_device_id=self.profile.mouse_device_id,
            mouse_hardware_id=self.profile.mouse_hardware_id,
            key_delay=delay_cfg,
            mouse_delay=mouse_delay_cfg,
            test_key=self.profile.keyboard_test_key,
        )
        self._last_backend_state = status
        self._update_keyboard_summary(status)
        if not self._loading_profile:
            self._mark_dirty()
        return status

    def _run_keyboard_test_main(self):
        key = getattr(self.profile, "keyboard_test_key", "f24") or "f24"
        ok_key, msg_key = self.engine.test_keyboard(key)
        ok_mouse, msg_mouse = self.engine.test_mouse("mouse1")
        self._append_log(msg_key)
        self._append_log(msg_mouse)
        ok = ok_key and ok_mouse
        combined = f"키보드: {msg_key}\n마우스: {msg_mouse}"
        if ok:
            QtWidgets.QMessageBox.information(self, "테스트", combined)
        else:
            QtWidgets.QMessageBox.warning(self, "테스트 실패", combined)
        try:
            self._update_keyboard_summary(self.engine.keyboard_status(refresh=False))
        except Exception:
            pass

    def _run_interception_installer(self):
        installer = Path(__file__).resolve().parent / "interception" / "install-interception.exe"
        if not installer.exists():
            QtWidgets.QMessageBox.warning(self, "설치 파일 없음", f"{installer} 를 찾을 수 없습니다.")
            return
        try:
            ctypes.windll.shell32.ShellExecuteW(None, "runas", "cmd.exe", f'/c \"{installer}\"', None, 1)
            self._append_log("Interception 설치 프로그램을 실행했습니다. 설치 후 재부팅이 필요합니다.")
        except Exception as exc:
            QtWidgets.QMessageBox.warning(self, "설치 실행 실패", str(exc))

    def _ensure_debugger(self) -> DebuggerDialog:
        if self.debugger is None:
            self.debugger = DebuggerDialog(
                None,
                state=self._debugger_state,
                save_state_cb=self._persist_debugger_state,
                interval_changed_cb=self._debugger_interval_changed,
                tolerance_changed_cb=self._debugger_tolerance_changed,
                close_cb=self._on_debugger_closed,
                start_test_cb=self._start_debugger_pixel_test,
                stop_test_cb=self._stop_pixel_test_loop,
                fail_capture_cb=self._capture_condition_failure,
                focus_viewer_cb=self._focus_image_viewer,
            )
            # 디버거에서 복원된 주기를 현재 기본값에도 반영
            try:
                self._debugger_interval_changed(self.debugger._interval_ms)
            except Exception:
                pass
            try:
                self._debugger_tolerance_changed(self.debugger._tolerance)
            except Exception:
                pass
        return self.debugger

    def _open_debugger(self):
        dbg = self._ensure_debugger()
        dbg.show_and_raise()

    def _open_debugger_with_config(self, config: dict):
        dbg = self._ensure_debugger()
        dbg._set_test_inputs(config or {})
        if isinstance(config, dict):
            if config.get("region_raw"):
                self._pixel_test_defaults["region_raw"] = config.get("region_raw")
            if config.get("color_raw"):
                self._pixel_test_defaults["color_raw"] = config.get("color_raw")
            if config.get("tolerance") is not None:
                self._pixel_test_defaults["tolerance"] = int(config.get("tolerance"))
            if config.get("interval") is not None:
                self._pixel_test_defaults["interval"] = int(config.get("interval"))
        dbg.show_and_raise()

    def _open_color_calc_dialog(self):
        state = self._color_calc_state if isinstance(self._color_calc_state, dict) else {}
        if self._color_calc_dialog is None:
            self._color_calc_dialog = ColorToleranceDialog(self, state=state, save_state_cb=self._persist_color_calc_state)
        else:
            self._color_calc_dialog._load_state(state)
        self._color_calc_dialog.show()
        self._color_calc_dialog.raise_()
        self._color_calc_dialog.activateWindow()

    def _open_pixel_test_dialog(self):
        defaults = self._current_pixel_defaults()
        state = self._state.get("pixel_test", {}) if isinstance(self._state, dict) else {}
        dialog_state = {
            "region": state.get("region", defaults["region"]),
            "color": state.get("color", defaults["color"]),
            "tolerance": state.get("tolerance", defaults["tolerance"]),
            "expect_exists": state.get("expect_exists", defaults["expect_exists"]),
            "interval": state.get("interval", defaults["interval"]),
        }
        if self._pixel_test_dialog is None:
            self._pixel_test_dialog = PixelTestDialog(
                self,
                resolver_provider=self._build_variable_resolver,
                start_test=self._start_modal_pixel_test,
                stop_test=self._stop_pixel_test_loop,
                state=dialog_state,
                save_state_cb=self._persist_pixel_test_state,
            )
        else:
            self._pixel_test_dialog._load_state(dialog_state)
        self._pixel_test_dialog.show()
        self._pixel_test_dialog.raise_()
        self._pixel_test_dialog.activateWindow()

    def _open_preset_transfer_dialog(self):
        try:
            base_res = self._current_base_resolution()
        except Exception:
            base_res = getattr(self.profile, "base_resolution", DEFAULT_BASE_RESOLUTION) or DEFAULT_BASE_RESOLUTION
        try:
            base_scale = self._current_base_scale()
        except Exception:
            base_scale = float(getattr(self.profile, "base_scale_percent", DEFAULT_BASE_SCALE) or DEFAULT_BASE_SCALE)

        current_res = None
        try:
            if isinstance(getattr(self, "current_res_edit", None), QtWidgets.QLineEdit):
                text = self.current_res_edit.text().strip()
                if text:
                    current_res = _parse_resolution_text(text, allow_empty=False, default=None)
        except Exception:
            current_res = None

        current_scale = None
        try:
            if isinstance(getattr(self, "current_scale_edit", None), QtWidgets.QLineEdit):
                scale_text = self.current_scale_edit.text().strip()
                if scale_text:
                    current_scale = _parse_scale_text(scale_text, allow_empty=True, default=None)
        except Exception:
            current_scale = None

        dlg = PresetTransferDialog(
            self,
            profile_provider=self._build_profile_from_inputs,
            base_res=base_res,
            base_scale=base_scale,
            current_res=current_res,
            current_scale=current_scale,
            detect_resolution=self._detect_screen_resolution,
            detect_scale=self._detect_app_scale,
            theme=self._theme,
            log_cb=self._append_log,
            profile_path=self.current_profile_path,
        )
        dlg.show()
        dlg.raise_()
        dlg.activateWindow()
        self._preset_transfer_dialog = dlg

    def _open_image_viewer_dialog(self):
        try:
            start_dir = Path(self._image_viewer_state.get("last_dir", SCREENSHOT_DIR))
        except Exception:
            start_dir = SCREENSHOT_DIR
        if not start_dir.exists():
            start_dir = SCREENSHOT_DIR
        if self._image_viewer_dialog is None:
            self._image_viewer_dialog = ImageViewerDialog(
                None,
                start_dir=start_dir,
                condition_window=self,
                save_state=self._persist_image_viewer_state,
                open_screenshot_dialog=self._open_screenshot_dialog,
                screenshot_hotkeys_provider=self._screenshot_hotkeys_info,
                state=self._image_viewer_state,
                capture_manager=self.screenshot_manager,
            )
        else:
            self._image_viewer_dialog.set_start_dir(start_dir)
        self._image_viewer_dialog._resize_to_available()
        self._image_viewer_dialog.show()
        self._image_viewer_dialog.raise_()
        self._image_viewer_dialog.activateWindow()

    def _focus_image_viewer(self, path: Path | None = None):
        self._open_image_viewer_dialog()
        if self._image_viewer_dialog:
            self._image_viewer_dialog.show()
            self._image_viewer_dialog.raise_()
            self._image_viewer_dialog.activateWindow()
            if path and path.exists():
                try:
                    self._image_viewer_dialog.set_start_dir(path.parent, refresh=True)
                    files = list(self._image_viewer_dialog._image_files)
                    for idx, f in enumerate(files):
                        if f == path:
                            self._image_viewer_dialog._select_index(idx)
                            break
                except Exception:
                    pass

    def _build_status_row(self):
        container = QtWidgets.QFrame()
        container.setObjectName("statusStrip")
        container.setFrameShape(QtWidgets.QFrame.Shape.StyledPanel)
        container.setFrameShadow(QtWidgets.QFrame.Shadow.Plain)
        container.setSizePolicy(QtWidgets.QSizePolicy.Policy.Expanding, QtWidgets.QSizePolicy.Policy.Maximum)

        row = QtWidgets.QHBoxLayout(container)
        row.setContentsMargins(10, 6, 10, 6)
        row.setSpacing(8)

        self.running_label = QtWidgets.QLabel("정지")
        self.active_label = QtWidgets.QLabel("비활성")
        self.paused_label = QtWidgets.QLabel("정상")
        self.admin_label = QtWidgets.QLabel("관리자(?)")
        self.capture_label = QtWidgets.QLabel("")
        self.log_toggle_btn = QtWidgets.QToolButton()
        self.log_toggle_btn.setCheckable(True)
        self.log_toggle_btn.setChecked(self._log_enabled)
        self.log_toggle_btn.setText("로그")
        self.log_toggle_btn.setAutoRaise(True)
        self.log_toggle_btn.setToolButtonStyle(QtCore.Qt.ToolButtonStyle.ToolButtonTextOnly)
        self.log_toggle_btn.toggled.connect(self._toggle_log_enabled)

        badge_style = "padding: 3px 6px; border: 1px solid #e3e8f0; border-radius: 6px; background: #f5f7fb;"
        theme = self._theme
        badge_style = (
            f"padding: 3px 6px; border: 1px solid {theme['panel_border']}; "
            f"border-radius: 6px; background: {theme['badge_bg']}; color: {theme['text']};"
        )
        self._status_badge_style = badge_style
        for lbl in (self.running_label, self.active_label, self.paused_label, self.admin_label, self.capture_label):
            lbl.setMinimumWidth(60)
            lbl.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)
            lbl.setStyleSheet(badge_style)
        self.capture_label.setVisible(False)

        status_label = QtWidgets.QLabel("상태")
        status_label.setStyleSheet("font-weight: 600;")
        badge_grid = QtWidgets.QGridLayout()
        badge_grid.setContentsMargins(0, 0, 0, 0)
        badge_grid.setHorizontalSpacing(6)
        badge_grid.setVerticalSpacing(4)
        badge_grid.addWidget(self.running_label, 0, 0)
        badge_grid.addWidget(self.active_label, 0, 1)
        badge_grid.addWidget(self.paused_label, 0, 2)
        badge_grid.addWidget(self.admin_label, 1, 0)
        badge_grid.addWidget(self.capture_label, 1, 1)
        badge_grid.addWidget(self.log_toggle_btn, 1, 2)

        badge_block = QtWidgets.QVBoxLayout()
        badge_block.setContentsMargins(0, 0, 0, 0)
        badge_block.setSpacing(2)
        badge_block.addWidget(status_label)
        badge_block.addLayout(badge_grid)

        row.addLayout(badge_block, stretch=2)
        row.addStretch(1)

        def _flat_btn(text: str, tooltip: str | None = None):
            btn = QtWidgets.QPushButton(text)
            btn.setMinimumSize(68, 26)
            btn.setStyleSheet(
                f"padding: 3px 8px; border: 1px solid {theme['button_border']}; "
                f"border-radius: 6px; background: {theme['button_bg']}; color: {theme['button_text']};"
            )
            if tooltip:
                btn.setToolTip(tooltip)
            return btn

        self.start_btn = _flat_btn("시작", "엔진 시작")
        self.stop_btn = _flat_btn("정지", "엔진 정지")
        self.pause_btn = _flat_btn("일시정지", "일시정지/재개")
        self.activate_btn = _flat_btn("활성화", "엔진 활성화")
        self.deactivate_btn = _flat_btn("비활성", "엔진 비활성화")
        self.apply_btn = _flat_btn("적용", "프로필 적용")
        self._apply_btn_default_style = self.apply_btn.styleSheet()
        self._apply_btn_working_style = (
            self._apply_btn_default_style
            + (" background: #2c4a7a; color: #ffffff; border-color: #5b82d7;" if theme["is_dark"] else " background: #dce7ff; color: #1f3f73; border-color: #5b82d7;")
        )
        self._apply_flash_timer = QtCore.QTimer(self)
        self._apply_flash_timer.setSingleShot(True)
        self._apply_flash_timer.timeout.connect(lambda: self.apply_btn.setStyleSheet(self._apply_btn_default_style))

        control_grid = QtWidgets.QGridLayout()
        control_grid.setContentsMargins(0, 0, 0, 0)
        control_grid.setHorizontalSpacing(4)
        control_grid.setVerticalSpacing(2)
        control_grid.addWidget(self.start_btn, 0, 0)
        control_grid.addWidget(self.stop_btn, 0, 1)
        control_grid.addWidget(self.pause_btn, 0, 2)
        control_grid.addWidget(self.activate_btn, 1, 0)
        control_grid.addWidget(self.deactivate_btn, 1, 1)
        control_grid.addWidget(self.apply_btn, 1, 2)
        row.addLayout(control_grid, stretch=3)

        container.setStyleSheet(
            f"#statusStrip {{ border: 1px solid {theme['panel_border']}; border-radius: 8px; background: {theme['panel_bg']}; color: {theme['text']}; }}"
        )
        return container

    def _build_device_group(self):
        group = QtWidgets.QFrame()
        group.setObjectName("inputStrip")
        group.setFrameShape(QtWidgets.QFrame.Shape.StyledPanel)
        group.setFrameShadow(QtWidgets.QFrame.Shadow.Plain)
        group.setSizePolicy(QtWidgets.QSizePolicy.Policy.Expanding, QtWidgets.QSizePolicy.Policy.Maximum)

        layout = QtWidgets.QHBoxLayout(group)
        layout.setContentsMargins(8, 4, 8, 4)
        layout.setSpacing(6)

        self.keyboard_mode_label = QtWidgets.QLabel("-")
        self.keyboard_device_label = QtWidgets.QLabel("-")
        self.mouse_device_label = QtWidgets.QLabel("-")
        for lbl in (self.keyboard_mode_label, self.keyboard_device_label, self.mouse_device_label):
            lbl.setStyleSheet("font-weight: 600;")
            lbl.setSizePolicy(QtWidgets.QSizePolicy.Policy.Preferred, QtWidgets.QSizePolicy.Policy.Maximum)

        info_grid = QtWidgets.QGridLayout()
        info_grid.setContentsMargins(0, 0, 0, 0)
        info_grid.setHorizontalSpacing(6)
        info_grid.setVerticalSpacing(2)
        info_grid.addWidget(QtWidgets.QLabel("입력"), 0, 0)
        info_grid.addWidget(self.keyboard_mode_label, 0, 1)
        info_grid.addWidget(QtWidgets.QLabel("키보드"), 1, 0)
        info_grid.addWidget(self.keyboard_device_label, 1, 1)
        info_grid.addWidget(QtWidgets.QLabel("마우스"), 2, 0)
        info_grid.addWidget(self.mouse_device_label, 2, 1)

        layout.addLayout(info_grid, stretch=2)
        layout.addStretch(1)

        btn_row = QtWidgets.QHBoxLayout()
        btn_row.setContentsMargins(0, 0, 0, 0)
        btn_row.setSpacing(4)
        self.keyboard_settings_btn = QtWidgets.QPushButton("설정")
        self.keyboard_test_btn = QtWidgets.QPushButton("테스트")
        self.keyboard_install_btn = QtWidgets.QPushButton("설치")
        self.keyboard_install_btn.setToolTip("interception/install-interception.exe를 관리자 CMD로 실행합니다. 설치 후 재부팅이 필요합니다.")
        for btn in (self.keyboard_settings_btn, self.keyboard_test_btn, self.keyboard_install_btn):
            btn.setMinimumHeight(26)
            btn.setStyleSheet(
                f"padding: 3px 8px; border: 1px solid {self._theme['button_border']}; "
                f"border-radius: 6px; background: {self._theme['button_bg']}; color: {self._theme['button_text']};"
            )
            btn_row.addWidget(btn)
        btn_row.addStretch()
        layout.addLayout(btn_row, stretch=3)

        group.setStyleSheet(
            f"#inputStrip {{ border: 1px solid {self._theme['panel_border']}; border-radius: 8px; background: {self._theme['panel_alt_bg']}; color: {self._theme['text']}; }}"
        )
        return group

    def _build_resolution_group(self):
        group = QtWidgets.QFrame()
        group.setObjectName("resolutionStrip")
        group.setFrameShape(QtWidgets.QFrame.Shape.StyledPanel)
        group.setFrameShadow(QtWidgets.QFrame.Shadow.Plain)
        group.setSizePolicy(QtWidgets.QSizePolicy.Policy.Expanding, QtWidgets.QSizePolicy.Policy.Maximum)

        layout = QtWidgets.QHBoxLayout(group)
        layout.setContentsMargins(8, 4, 8, 4)
        layout.setSpacing(8)

        form = QtWidgets.QGridLayout()
        form.setContentsMargins(0, 0, 0, 0)
        form.setHorizontalSpacing(8)
        form.setVerticalSpacing(4)

        base_label = QtWidgets.QLabel("기준 해상도")
        base_row = QtWidgets.QHBoxLayout()
        base_row.setContentsMargins(0, 0, 0, 0)
        base_row.setSpacing(4)
        self.base_res_edit = QtWidgets.QLineEdit(_format_resolution(getattr(self.profile, "base_resolution", DEFAULT_BASE_RESOLUTION)))
        self.base_res_edit.setPlaceholderText("예: 3440x1440 (기준)")
        self.base_res_edit.setClearButtonEnabled(True)
        self.base_res_edit.setMaximumWidth(200)
        self.set_base_btn = QtWidgets.QPushButton("기준=현재")
        self.set_base_btn.setMinimumWidth(90)
        base_row.addWidget(self.base_res_edit)
        base_row.addWidget(self.set_base_btn)
        form.addWidget(base_label, 0, 0)
        form.addLayout(base_row, 0, 1)

        base_scale_label = QtWidgets.QLabel("기준 앱 배율(%)")
        base_scale_row = QtWidgets.QHBoxLayout()
        base_scale_row.setContentsMargins(0, 0, 0, 0)
        base_scale_row.setSpacing(4)
        self.base_scale_edit = QtWidgets.QLineEdit(_format_scale_percent(getattr(self.profile, "base_scale_percent", DEFAULT_BASE_SCALE)))
        self.base_scale_edit.setPlaceholderText("예: 100 또는 125")
        self.base_scale_edit.setClearButtonEnabled(True)
        self.base_scale_edit.setMaximumWidth(140)
        base_scale_row.addWidget(self.base_scale_edit)
        base_scale_row.addStretch()
        form.addWidget(base_scale_label, 1, 0)
        form.addLayout(base_scale_row, 1, 1)

        current_label = QtWidgets.QLabel("현재 해상도")
        current_row = QtWidgets.QHBoxLayout()
        current_row.setContentsMargins(0, 0, 0, 0)
        current_row.setSpacing(4)
        self.current_res_edit = QtWidgets.QLineEdit()
        self.current_res_edit.setPlaceholderText("자동 감지 또는 직접 입력")
        self.current_res_edit.setClearButtonEnabled(True)
        self.current_res_edit.setMaximumWidth(220)
        self.detect_res_btn = QtWidgets.QPushButton("자동 감지")
        self.detect_res_btn.setMinimumWidth(90)
        current_row.addWidget(self.current_res_edit)
        current_row.addWidget(self.detect_res_btn)
        form.addWidget(current_label, 2, 0)
        form.addLayout(current_row, 2, 1)

        current_scale_label = QtWidgets.QLabel("현재 앱 배율(%)")
        current_scale_row = QtWidgets.QHBoxLayout()
        current_scale_row.setContentsMargins(0, 0, 0, 0)
        current_scale_row.setSpacing(4)
        self.current_scale_edit = QtWidgets.QLineEdit()
        self.current_scale_edit.setPlaceholderText("자동 감지 또는 직접 입력 (예: 100)")
        self.current_scale_edit.setClearButtonEnabled(True)
        self.current_scale_edit.setMaximumWidth(140)
        self.detect_scale_btn = QtWidgets.QPushButton("배율 감지")
        self.detect_scale_btn.setMinimumWidth(90)
        current_scale_row.addWidget(self.current_scale_edit)
        current_scale_row.addWidget(self.detect_scale_btn)
        form.addWidget(current_scale_label, 3, 0)
        form.addLayout(current_scale_row, 3, 1)

        self.preset_transfer_btn = QtWidgets.QPushButton("프리셋 옮기기...")
        self.preset_transfer_btn.setMinimumHeight(30)
        self.preset_transfer_btn.setStyleSheet(
            f"font-weight: 600; border: 1px solid {self._theme['button_border']}; "
            f"border-radius: 6px; background: {self._theme['button_bg']}; color: {self._theme['button_text']}; padding: 4px 10px;"
        )
        form.addWidget(self.preset_transfer_btn, 4, 0, 1, 2)

        layout.addLayout(form)

        group.setStyleSheet(
            f"#resolutionStrip {{ border: 1px solid {self._theme['panel_border']}; border-radius: 8px; background: {self._theme['panel_bg']}; color: {self._theme['text']}; }}"
        )
        return group

    def _build_macro_group(self):
        group = QtWidgets.QGroupBox("매크로 목록 (기본 액션 + 조건)")
        layout = QtWidgets.QVBoxLayout(group)

        self.macro_table = QtWidgets.QTableWidget(0, 8)
        self.macro_table.setHorizontalHeaderLabels(["순번", "이름", "트리거", "모드", "활성", "차단", "범위", "설명"])
        header = self.macro_table.horizontalHeader()
        header.setDefaultSectionSize(90)
        header.setMinimumSectionSize(60)
        header.setStretchLastSection(True)
        self.macro_table.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectionBehavior.SelectRows)
        self.macro_table.setEditTriggers(QtWidgets.QAbstractItemView.EditTrigger.NoEditTriggers)
        self.macro_table.verticalHeader().setVisible(False)
        self.macro_table.setContextMenuPolicy(QtCore.Qt.ContextMenuPolicy.CustomContextMenu)
        layout.addWidget(self.macro_table)

        btn_row = QtWidgets.QHBoxLayout()
        self.add_macro_btn = QtWidgets.QPushButton("매크로 추가")
        self.edit_macro_btn = QtWidgets.QPushButton("편집")
        self.clone_macro_btn = QtWidgets.QPushButton("복제")
        self.del_macro_btn = QtWidgets.QPushButton("삭제")
        btn_row.addWidget(self.add_macro_btn)
        btn_row.addWidget(self.edit_macro_btn)
        btn_row.addWidget(self.clone_macro_btn)
        btn_row.addWidget(self.del_macro_btn)
        btn_row.addStretch()
        layout.addLayout(btn_row)

        return group

    def _build_variable_group(self):
        group = QtWidgets.QGroupBox("전역 변수/프리셋 (모든 매크로에서 사용)")
        layout = QtWidgets.QVBoxLayout(group)

        self.variable_tabs = QtWidgets.QTabWidget()
        self.variable_tables: dict[str, QtWidgets.QTableWidget] = {}
        self._updating_variables = False

        def make_tab(label: str, key: str) -> QtWidgets.QWidget:
            tab = QtWidgets.QWidget()
            tab_layout = QtWidgets.QVBoxLayout(tab)
            table = QtWidgets.QTableWidget(0, 0)
            self._configure_variable_table(table)
            table.itemChanged.connect(self._on_variable_item_changed)
            self.variable_tables[key] = table

            btn_row = QtWidgets.QHBoxLayout()
            add_btn = QtWidgets.QPushButton("추가")
            del_btn = QtWidgets.QPushButton("삭제")
            btn_row.addWidget(add_btn)
            btn_row.addWidget(del_btn)
            btn_row.addStretch()

            def add_row():
                self._append_variable_pair(table, "", "")

            def del_rows():
                if not self._delete_selected_variable_pairs(table):
                    self._pop_last_variable_pair(table)

            add_btn.clicked.connect(add_row)
            del_btn.clicked.connect(del_rows)

            tab_layout.addWidget(table)
            tab_layout.addLayout(btn_row)
            return tab

        self.variable_tabs.addTab(make_tab("Sleep", "sleep"), "Sleep")
        self.variable_tabs.addTab(make_tab("Region", "region"), "Region")
        self.variable_tabs.addTab(make_tab("Color", "color"), "Color")
        self.variable_tabs.addTab(make_tab("Key", "key"), "Key")
        self.variable_tabs.addTab(make_tab("Value", "var"), "Value")

        layout.addWidget(
            QtWidgets.QLabel(
                "이름에 영문/숫자/_ 사용, 값은 해당 타입 포맷 (예: sleep은 100~200, region은 x,y,w,h, color는 RRGGBB, key는 키 이름 또는 스캔코드, value는 자유 문자열)."
            )
        )
        layout.addWidget(self.variable_tabs)
        return group

    def _build_log_group(self):
        group = QtWidgets.QGroupBox("로그")
        self.log_group = group
        layout = QtWidgets.QVBoxLayout(group)
        toggle_row = QtWidgets.QHBoxLayout()
        self.log_enable_checkbox = QtWidgets.QCheckBox("로그 표시")
        self.log_enable_checkbox.setChecked(self._log_enabled)
        self.log_enable_checkbox.toggled.connect(self._toggle_log_enabled)
        toggle_row.addWidget(self.log_enable_checkbox)
        toggle_row.addStretch()
        layout.addLayout(toggle_row)
        self.log_view = QtWidgets.QTextEdit()
        self.log_view.setReadOnly(True)
        self.log_view.setAcceptRichText(True)
        self.log_view.setFont(QtGui.QFontDatabase.systemFont(QtGui.QFontDatabase.SystemFont.FixedFont))
        layout.addWidget(self.log_view)
        self.log_view.setVisible(self._log_enabled)
        group.setVisible(self._log_enabled)
        return group

    def _connect_signals(self):
        self.start_btn.clicked.connect(self.engine.start)
        self.stop_btn.clicked.connect(self.engine.stop)
        self.activate_btn.clicked.connect(self.engine.activate)
        self.deactivate_btn.clicked.connect(self.engine.deactivate)
        self.pause_btn.clicked.connect(self.engine.toggle_pause)
        self.apply_btn.clicked.connect(self._handle_apply_click)
        if hasattr(self, "detect_res_btn"):
            self.detect_res_btn.clicked.connect(lambda: self._fill_current_resolution(silent=False))
        if hasattr(self, "detect_scale_btn"):
            self.detect_scale_btn.clicked.connect(lambda: self._fill_current_scale(silent=False))
        if hasattr(self, "preset_transfer_btn"):
            self.preset_transfer_btn.clicked.connect(self._open_preset_transfer_dialog)
        if hasattr(self, "base_res_edit"):
            self.base_res_edit.textChanged.connect(self._on_base_resolution_changed)
        if hasattr(self, "base_scale_edit"):
            self.base_scale_edit.textChanged.connect(self._on_base_resolution_changed)
        if hasattr(self, "set_base_btn"):
            self.set_base_btn.clicked.connect(self._set_base_from_current_resolution)
        self.keyboard_settings_btn.clicked.connect(self._open_keyboard_settings)
        self.keyboard_test_btn.clicked.connect(self._run_keyboard_test_main)
        self.keyboard_install_btn.clicked.connect(self._run_interception_installer)

        self.add_macro_btn.clicked.connect(self._add_macro)
        self.edit_macro_btn.clicked.connect(self._edit_macro)
        self.clone_macro_btn.clicked.connect(self._clone_macro)
        self.del_macro_btn.clicked.connect(self._delete_macro)
        self.macro_table.doubleClicked.connect(lambda _: self._edit_macro())
        self.macro_table.customContextMenuRequested.connect(self._macro_context_menu)

    # Variable helpers ---------------------------------------------------
    def _on_variable_item_changed(self, _item):
        if getattr(self, "_updating_variables", False):
            return
        self._mark_dirty()
        self._refresh_variable_completers()

    def _configure_variable_table(self, table: QtWidgets.QTableWidget, *, pairs_per_row: int = 4):
        table.setProperty("pairs_per_row", max(1, pairs_per_row))
        table.setColumnCount(pairs_per_row * 2)
        headers: list[str] = []
        for idx in range(pairs_per_row):
            headers.extend([f"이름{idx + 1}", f"값{idx + 1}"])
        table.setHorizontalHeaderLabels(headers)
        header = _VariableHeader(QtCore.Qt.Orientation.Horizontal, table)
        table.setHorizontalHeader(header)
        header.setDefaultSectionSize(90)
        header.setMinimumSectionSize(70)
        header.setStretchLastSection(False)
        table.verticalHeader().setVisible(False)
        table.setSelectionMode(QtWidgets.QAbstractItemView.SelectionMode.ExtendedSelection)
        table.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectionBehavior.SelectItems)
        table.setObjectName("variableTable")
        table.setShowGrid(True)
        table.setGridStyle(QtCore.Qt.PenStyle.SolidLine)
        table.setStyleSheet(
            "QTableWidget#variableTable { gridline-color: #a0a0a0; }"
            "QTableWidget#variableTable::item { padding: 4px; }"
            "QTableWidget#variableTable QHeaderView::section { padding: 4px; }"
        )
        table.setItemDelegate(_VariableSeparatorDelegate(table))

    def _variable_pairs_per_row(self, table: QtWidgets.QTableWidget) -> int:
        return max(1, int(table.property("pairs_per_row") or 4))

    def _variable_pairs_from_table(self, table: QtWidgets.QTableWidget) -> list[tuple[str, str]]:
        pairs: list[tuple[str, str]] = []
        per_row = self._variable_pairs_per_row(table)
        for row in range(table.rowCount()):
            for pidx in range(per_row):
                name_item = table.item(row, pidx * 2)
                val_item = table.item(row, pidx * 2 + 1)
                name = name_item.text().strip() if name_item else ""
                val = val_item.text().strip() if val_item else ""
                if not name and not val:
                    continue
                pairs.append((name, val))
        return pairs

    def _set_variable_pairs(self, table: QtWidgets.QTableWidget, pairs: list[tuple[str, str]]):
        per_row = self._variable_pairs_per_row(table)
        cols = per_row * 2
        rows = math.ceil(len(pairs) / per_row) if pairs else 0
        prev_updating = getattr(self, "_updating_variables", False)
        self._updating_variables = True
        try:
            table.setColumnCount(cols)
            headers: list[str] = []
            for idx in range(per_row):
                headers.extend([f"이름{idx + 1}", f"값{idx + 1}"])
            table.setHorizontalHeaderLabels(headers)
            table.setRowCount(rows)
            for idx, (name, val) in enumerate(pairs):
                r = idx // per_row
                c = (idx % per_row) * 2
                table.setItem(r, c, QtWidgets.QTableWidgetItem(name))
                table.setItem(r, c + 1, QtWidgets.QTableWidgetItem(val))
        finally:
            self._updating_variables = prev_updating
        if not prev_updating:
            self._mark_dirty()
            self._refresh_variable_completers()

    def _append_variable_pair(self, table: QtWidgets.QTableWidget, name: str, value: str):
        pairs = self._variable_pairs_from_table(table)
        pairs.append((name, value))
        self._set_variable_pairs(table, pairs)

    def _delete_selected_variable_pairs(self, table: QtWidgets.QTableWidget) -> bool:
        indexes = table.selectionModel().selectedIndexes()
        if not indexes:
            return False
        per_row = self._variable_pairs_per_row(table)
        to_remove = sorted(
            {idx.row() * per_row + (idx.column() // 2) for idx in indexes},
            reverse=True,
        )
        pairs = self._variable_pairs_from_table(table)
        for pidx in to_remove:
            if 0 <= pidx < len(pairs):
                pairs.pop(pidx)
        self._set_variable_pairs(table, pairs)
        return True

    def _pop_last_variable_pair(self, table: QtWidgets.QTableWidget):
        pairs = self._variable_pairs_from_table(table)
        if not pairs:
            return
        pairs.pop()
        self._set_variable_pairs(table, pairs)

    def _variable_names(self, category: str) -> List[str]:
        table = self.variable_tables.get(category)
        if not table:
            return []
        names: List[str] = []
        for name, _ in self._variable_pairs_from_table(table):
            if name:
                names.append(name)
        return names

    def _ensure_variable(self, category: str, name: str, default_value: str = "") -> bool:
        table = self.variable_tables.get(category)
        if not table or not name:
            return False
        if category == "color" and not default_value:
            default_value = "000000"
        # 이미 있으면 스킵
        for row in range(table.rowCount()):
            item = table.item(row, 0)
            if item and item.text().strip() == name:
                return True
        self._append_variable_pair(table, name, default_value)
        return True

    def _collect_variables(self) -> MacroVariables:
        buckets = {cat: {} for cat in ("sleep", "region", "color", "key", "var")}
        for cat, table in self.variable_tables.items():
            bucket = buckets.setdefault(cat, {})
            for idx, (name, val) in enumerate(self._variable_pairs_from_table(table)):
                if not name and not val:
                    continue
                if not name:
                    raise ValueError(f"{cat} 변수 이름이 비어 있습니다. (순번 {idx + 1})")
                if name in bucket:
                    raise ValueError(f"{cat} 변수 '{name}'가 중복되었습니다.")
                bucket[name] = val
        return MacroVariables(**buckets)

    def _set_variable_fields(self, variables: MacroVariables):
        self._updating_variables = True
        try:
            for cat, table in self.variable_tables.items():
                data = getattr(variables, cat, {}) or {}
                pairs = list(data.items())
                table.clearContents()
                table.setRowCount(0)
                self._set_variable_pairs(table, pairs)
        finally:
            self._updating_variables = False
            self._refresh_variable_completers()

    def _refresh_variable_completers(self):
        names = {cat: self._variable_names(cat) for cat in ("region", "color", "key", "var")}
        dlg = self._pixel_test_dialog
        if isinstance(dlg, PixelTestDialog):
            _attach_variable_completer(dlg.region_edit, names.get("region", []))
            _attach_variable_completer(dlg.color_edit, names.get("color", []))
        # 액션/조건 편집기에서 사용할 수 있도록 기본 변수 목록을 업데이트
        self._variable_provider = lambda category: names.get(category, [])

    def _build_variable_resolver(self) -> VariableResolver:
        vars = self._collect_variables()
        return VariableResolver(vars)

    def _compute_theme_colors(self) -> dict:
        pal = QtWidgets.QApplication.palette()
        win = pal.color(QtGui.QPalette.ColorRole.Window)
        text = pal.color(QtGui.QPalette.ColorRole.WindowText)
        is_dark = _luminance_from_qcolor(win) < 128
        return {
            "is_dark": is_dark,
            "panel_bg": "#1f1f1f" if is_dark else "#f7f9fc",
            "panel_alt_bg": "#20242a" if is_dark else "#fbfcfe",
            "panel_border": "#3a3f46" if is_dark else "#e3e8f0",
            "badge_bg": "#2b2f35" if is_dark else "#f5f7fb",
            "button_bg": "#2d3036" if is_dark else "#ffffff",
            "button_border": "#4a5058" if is_dark else "#d5dae3",
            "button_text": text.name(),
            "text": text.name(),
        }

    def _current_base_resolution(self) -> tuple[int, int]:
        default = getattr(self.profile, "base_resolution", DEFAULT_BASE_RESOLUTION) or DEFAULT_BASE_RESOLUTION
        text = ""
        try:
            if isinstance(getattr(self, "base_res_edit", None), QtWidgets.QLineEdit):
                text = self.base_res_edit.text()
        except Exception:
            text = ""
        if text.strip():
            return _parse_resolution_text(text, allow_empty=False, default=None)
        return tuple(int(v) for v in default)

    def _current_base_scale(self) -> float:
        default = float(getattr(self.profile, "base_scale_percent", DEFAULT_BASE_SCALE) or DEFAULT_BASE_SCALE)
        text = ""
        try:
            if isinstance(getattr(self, "base_scale_edit", None), QtWidgets.QLineEdit):
                text = self.base_scale_edit.text()
        except Exception:
            text = ""
        if text.strip():
            return _parse_scale_text(text, allow_empty=False, default=None)
        return float(default)

    def _build_profile_from_inputs(self) -> MacroProfile:
        resolver = self._build_variable_resolver()
        macros = self._collect_macros(resolver)
        variables = self._collect_variables()
        region_raw = self.profile.pixel_region_raw or ",".join(str(v) for v in self.profile.pixel_region or [])
        color_raw = self.profile.pixel_color_raw or _rgb_to_hex(self.profile.pixel_color or (255, 0, 0))
        pixel_region = _parse_region(region_raw, resolver=resolver)
        pixel_color = _parse_hex_color(color_raw, resolver=resolver)
        tolerance = int(self.profile.pixel_tolerance if self.profile.pixel_tolerance is not None else 10)
        expect_exists = getattr(self.profile, "pixel_expect_exists", True)
        input_mode = getattr(self.profile, "input_mode", "hardware") or "hardware"
        key_delay = getattr(self.profile, "key_delay", KeyDelayConfig())
        mouse_delay = getattr(self.profile, "mouse_delay", KeyDelayConfig())
        test_key = getattr(self.profile, "keyboard_test_key", "f24")
        base_resolution = self._current_base_resolution()
        base_scale = self._current_base_scale()
        return MacroProfile(
            macros=macros,
            pixel_region=pixel_region,
            pixel_region_raw=region_raw,
            pixel_color=pixel_color,
            pixel_color_raw=color_raw,
            pixel_tolerance=tolerance,
            pixel_expect_exists=expect_exists,
            keyboard_device_id=self.profile.keyboard_device_id if input_mode == "hardware" else None,
            keyboard_hardware_id=self.profile.keyboard_hardware_id if input_mode == "hardware" else None,
            mouse_device_id=self.profile.mouse_device_id if input_mode == "hardware" else None,
            mouse_hardware_id=self.profile.mouse_hardware_id if input_mode == "hardware" else None,
            keyboard_test_key=test_key,
            input_mode=input_mode,
            key_delay=key_delay if isinstance(key_delay, KeyDelayConfig) else KeyDelayConfig.from_dict(key_delay),
            mouse_delay=mouse_delay if isinstance(mouse_delay, KeyDelayConfig) else KeyDelayConfig.from_dict(mouse_delay),
            variables=variables,
            base_resolution=base_resolution,
            base_scale_percent=base_scale,
            transform_matrix=getattr(self.profile, "transform_matrix", None),
        )

    # App state ----------------------------------------------------------
    def _load_state(self) -> dict:
        if not self._state_path.exists():
            return {}
        try:
            data = json.loads(self._state_path.read_text(encoding="utf-8"))
            return data if isinstance(data, dict) else {}
        except Exception as exc:
            self._append_log(f"상태 파일 로드 오류: {exc}")
            return {}

    def _write_state(self, state: dict):
        try:
            self._state_path.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")
        except Exception as exc:
            self._append_log(f"상태 파일 저장 오류: {exc}")

    def _update_state(self, key: str, value):
        state = dict(self._state) if isinstance(self._state, dict) else {}
        state[key] = value
        self._state = state
        self._write_state(state)

    def _persist_screenshot_state(self, data: dict):
        self._update_state("screenshot", data)

    def _persist_debugger_state(self, data: dict):
        self._update_state("debugger", data)

    def _persist_color_calc_state(self, data: dict):
        self._color_calc_state = data or {}
        self._update_state("color_calc", self._color_calc_state)

    def _persist_pixel_test_state(self, data: dict):
        self._update_state("pixel_test", data)

    def _persist_image_viewer_state(self, data: dict):
        self._image_viewer_state = data or {}
        self._update_state("image_viewer", self._image_viewer_state)

    def _screenshot_hotkeys_info(self) -> dict:
        hk = self.screenshot_manager.hotkeys
        return {"start": hk.start, "stop": hk.stop, "capture": hk.capture}

    def _debugger_interval_changed(self, interval_ms: int):
        ms = max(50, int(interval_ms))
        self._pixel_test_defaults["interval"] = ms
        if self._pixel_test_config:
            self._pixel_test_config["interval"] = ms
        if self._pixel_test_timer.isActive():
            self._pixel_test_timer.setInterval(ms)

    def _debugger_tolerance_changed(self, tolerance: int):
        tol = max(0, min(255, int(tolerance)))
        self._pixel_test_defaults["tolerance"] = tol
        if self._pixel_test_config:
            self._pixel_test_config["tolerance"] = tol
        try:
            cfg = self._pixel_test_config or {}
            region = cfg.get("region") or self.profile.pixel_region or (0, 0, 100, 100)
            color = cfg.get("color") or self.profile.pixel_color or (255, 0, 0)
            expect = bool(cfg.get("expect_exists")) if cfg else getattr(self.profile, "pixel_expect_exists", True)
            region = tuple(int(v) for v in region)
            color = tuple(int(c) for c in color)
            self.engine.update_pixel_test(region, color, tol, expect)
        except Exception:
            pass

    def _on_debugger_closed(self):
        # 디버거를 닫을 때 테스트 루프도 안전하게 종료
        self._stop_pixel_test_loop()

    def _update_title(self):
        name = Path(self.current_profile_path).name if self.current_profile_path else "새 프로필"
        dirty_mark = "*" if self.dirty else ""
        self.setWindowTitle(f"{self.base_title} - {name}{dirty_mark}")

    def _mark_dirty(self, dirty: bool = True):
        self.dirty = dirty
        self._update_title()

    def _persist_last_profile_path(self, path: str | None):
        self._update_state("last_profile_path", path)

    def _load_last_session(self) -> bool:
        data = self._state if isinstance(self._state, dict) else {}
        path = data.get("last_profile_path")
        if not path or not Path(path).exists():
            return False
        loaded = self._load_profile_from_path(path, show_error_dialog=False, add_log=False)
        if loaded:
            self._append_log(f"이전 세션에서 자동 불러오기: {path}")
        return loaded

    def _confirm_save_if_dirty(self) -> bool:
        if not self.dirty:
            return True
        res = QtWidgets.QMessageBox.question(
            self,
            "변경 사항 저장",
            "변경 사항이 저장되지 않았습니다. 저장하시겠습니까?",
            QtWidgets.QMessageBox.StandardButton.Yes
            | QtWidgets.QMessageBox.StandardButton.No
            | QtWidgets.QMessageBox.StandardButton.Cancel,
            QtWidgets.QMessageBox.StandardButton.Yes,
        )
        if res == QtWidgets.QMessageBox.StandardButton.Cancel:
            return False
        if res == QtWidgets.QMessageBox.StandardButton.Yes:
            return self._save_profile()
        return True

    # Profile helpers -----------------------------------------------------
    def _macro_scope_text(self, macro: Macro) -> str:
        scope = getattr(macro, "scope", "global") or "global"
        if scope != "app":
            return "전역"
        targets = getattr(macro, "app_targets", []) or []
        names: list[str] = []
        for t in targets:
            target = AppTarget.from_any(t)
            if not target:
                continue
            label = target.name or (Path(target.path).name if target.path else "")
            if label:
                names.append(label)
        if not names:
            return "앱 지정"
        if len(names) > 3:
            names = names[:3] + ["..."]
        return f"앱: {', '.join(names)}"

    def _set_macro_row(self, row: int, macro: Macro):
        scope_text = self._macro_scope_text(macro)
        values = [
            str(row + 1),
            macro.name or "",
            macro.trigger_key,
            macro.mode,
            "ON" if getattr(macro, "enabled", True) else "OFF",
            "ON" if macro.suppress_trigger else "OFF",
            scope_text,
            getattr(macro, "description", "") or "",
        ]
        for col, val in enumerate(values):
            item = QtWidgets.QTableWidgetItem(val)
            item.setData(QtCore.Qt.ItemDataRole.UserRole, macro)
            self.macro_table.setItem(row, col, item)

    def _refresh_macros(self):
        self._loading_profile = True
        self.macro_table.setRowCount(0)
        for macro in self.profile.macros:
            self._append_macro_row(macro)
        self._renumber_macro_rows()
        self._loading_profile = False

    def _append_macro_row(self, macro: Macro):
        row = self.macro_table.rowCount()
        self.macro_table.insertRow(row)
        self._set_macro_row(row, macro)
        if not self._loading_profile:
            self._mark_dirty()

    def _apply_scope_to_all_macros(self, scope: str, targets: list[AppTarget]):
        scope_val = scope or "global"
        cleaned: list[AppTarget] = []
        if scope_val == "app":
            for t in targets or []:
                target = AppTarget.from_any(t)
                if target:
                    cleaned.append(copy.deepcopy(target))
        updated = False
        for row in range(self.macro_table.rowCount()):
            macro = self._macro_from_row(row)
            if not macro:
                continue
            macro.scope = scope_val
            macro.app_targets = [copy.deepcopy(t) for t in cleaned] if scope_val == "app" else []
            self._set_macro_row(row, macro)
            updated = True
        if updated and not self._loading_profile:
            self._mark_dirty()

    def _macro_summary(self, macro: Macro) -> str:
        cycles = f", {macro.cycle_count}회" if macro.cycle_count else ", 무한"
        return f"액션 {len(macro.actions)}{cycles}"

    def _macro_copy_name(self, macro: Macro | None) -> str:
        base = (macro.name if macro else "") or (macro.trigger_key if macro else "") or ""
        base = base.strip() or "매크로"
        existing = {m.name for m in self._collect_macros() if isinstance(m, Macro) and m.name}
        candidate = f"{base} 복사본"
        if candidate not in existing:
            return candidate
        suffix = 2
        while f"{candidate} {suffix}" in existing:
            suffix += 1
        return f"{candidate} {suffix}"

    def _get_selected_row(self) -> int:
        selected = self.macro_table.selectionModel().selectedRows()
        return selected[0].row() if selected else -1

    def _macro_from_row(self, row: int) -> Macro:
        item = self.macro_table.item(row, 0)
        stored = item.data(QtCore.Qt.ItemDataRole.UserRole) if item else None
        return stored if isinstance(stored, Macro) else None

    def _renumber_macro_rows(self):
        for row in range(self.macro_table.rowCount()):
            item = self.macro_table.item(row, 0)
            if item:
                item.setText(str(row + 1))

    def _macro_context_menu(self, pos: QtCore.QPoint):
        index = self.macro_table.indexAt(pos)
        if index.isValid():
            self.macro_table.selectRow(index.row())
        menu = QtWidgets.QMenu(self)
        add_act = menu.addAction("매크로 추가")
        edit_act = menu.addAction("편집")
        clone_act = menu.addAction("복제")
        del_act = menu.addAction("삭제")
        action = menu.exec(self.macro_table.viewport().mapToGlobal(pos))
        if action == add_act:
            self._add_macro()
        elif action == edit_act:
            self._edit_macro()
        elif action == clone_act:
            self._clone_macro()
        elif action == del_act:
            self._delete_macro()

    def _collect_macros(self, resolver: VariableResolver | None = None) -> List[Macro]:
        macros: List[Macro] = []
        for row in range(self.macro_table.rowCount()):
            macro = self._macro_from_row(row)
            if macro:
                if resolver:
                    macros.append(Macro.from_dict(macro.to_dict(), resolver))
                else:
                    macros.append(macro)
        return macros

    def _add_macro(self):
        resolver = None
        try:
            resolver = self._build_variable_resolver()
        except Exception:
            resolver = None
        dlg = MacroDialog(
            self,
            variable_provider=self._variable_names,
            add_variable=self._ensure_variable,
            resolver=resolver,
            start_pixel_test=self._start_condition_pixel_test,
            start_condition_debug=self._start_condition_debug_session,
            stop_pixel_test=self._stop_pixel_test_loop,
            image_viewer_state=self._image_viewer_state,
            save_image_viewer_state=self._persist_image_viewer_state,
            open_screenshot_dialog=self._open_screenshot_dialog,
            screenshot_hotkeys_provider=self._screenshot_hotkeys_info,
            screenshot_manager=self.screenshot_manager,
            apply_scope_all=self._apply_scope_to_all_macros,
        )
        if _run_dialog_non_modal(dlg):
            try:
                macro = dlg.get_macro()
            except ValueError as exc:
                QtWidgets.QMessageBox.warning(self, "입력 오류", str(exc))
                return
            self._append_macro_row(macro)
            self._renumber_macro_rows()

    def _edit_macro(self):
        row = self._get_selected_row()
        if row < 0:
            QtWidgets.QMessageBox.information(self, "선택 없음", "편집할 매크로를 선택하세요.")
            return
        macro = self._macro_from_row(row)
        resolver = None
        try:
            resolver = self._build_variable_resolver()
        except Exception:
            resolver = None
        dlg = MacroDialog(
            self,
            macro=macro,
            variable_provider=self._variable_names,
            add_variable=self._ensure_variable,
            resolver=resolver,
            start_pixel_test=self._start_condition_pixel_test,
            start_condition_debug=self._start_condition_debug_session,
            stop_pixel_test=self._stop_pixel_test_loop,
            image_viewer_state=self._image_viewer_state,
            save_image_viewer_state=self._persist_image_viewer_state,
            open_screenshot_dialog=self._open_screenshot_dialog,
            screenshot_hotkeys_provider=self._screenshot_hotkeys_info,
            screenshot_manager=self.screenshot_manager,
            apply_scope_all=self._apply_scope_to_all_macros,
        )
        if _run_dialog_non_modal(dlg):
            try:
                new_macro = dlg.get_macro()
            except ValueError as exc:
                QtWidgets.QMessageBox.warning(self, "입력 오류", str(exc))
                return
            old_snapshot = macro.to_dict() if macro else None
            new_snapshot = new_macro.to_dict()
            self._set_macro_row(row, new_macro)
            if not self._loading_profile and old_snapshot != new_snapshot:
                self._mark_dirty()

    def _clone_macro(self):
        row = self._get_selected_row()
        if row < 0:
            QtWidgets.QMessageBox.information(self, "선택 없음", "복제할 매크로를 선택하세요.")
            return
        macro = self._macro_from_row(row)
        if not macro:
            QtWidgets.QMessageBox.information(self, "대상 없음", "복제할 매크로를 찾지 못했습니다.")
            return
        cloned = copy.deepcopy(macro)
        cloned.name = self._macro_copy_name(macro)
        insert_row = row + 1
        self.macro_table.insertRow(insert_row)
        self._set_macro_row(insert_row, cloned)
        self._renumber_macro_rows()
        self.macro_table.selectRow(insert_row)
        if not self._loading_profile:
            self._mark_dirty()

    def _delete_macro(self):
        row = self._get_selected_row()
        if row < 0:
            QtWidgets.QMessageBox.information(self, "선택 없음", "삭제할 매크로를 선택하세요.")
            return
        self.macro_table.removeRow(row)
        self._renumber_macro_rows()
        if not self._loading_profile:
            self._mark_dirty()

    def _apply_profile(self, *, silent: bool = False) -> bool:
        try:
            profile = self._build_profile_from_inputs()
        except ValueError as exc:
            if not silent:
                QtWidgets.QMessageBox.warning(self, "입력 오류", str(exc))
            return False
        self.profile = profile
        runtime_profile = MacroProfile.from_dict(profile.to_dict())
        self.engine.update_profile(runtime_profile)
        self._refresh_pixel_defaults(self.profile)
        try:
            backend_state = self.engine.keyboard_status(refresh=True)
        except Exception:
            backend_state = None
        if backend_state:
            self._last_backend_state = backend_state
        try:
            self._update_keyboard_summary(backend_state)
        except Exception:
            pass
        if not silent:
            self._append_log("프로필 적용 완료")
        return True

    def _new_profile(self):
        if not self._confirm_save_if_dirty():
            return
        self.profile = copy.deepcopy(DEFAULT_PROFILE)
        self.current_profile_path = None
        self._persist_last_profile_path(None)
        self._loading_profile = True
        self._refresh_macros()
        self._set_variable_fields(self.profile.variables)
        self._refresh_pixel_defaults(self.profile)
        self.engine.update_profile(self.profile)
        try:
            backend_state = self.engine.keyboard_status(refresh=True)
        except Exception:
            backend_state = None
        if backend_state:
            self._last_backend_state = backend_state
        try:
            self._update_keyboard_summary(backend_state)
        except Exception:
            pass
        self._loading_profile = False
        self._mark_dirty(True)
        self._append_log("새 프로필 생성")

    def _load_profile_from_path(self, path: str, *, show_error_dialog: bool = True, add_log: bool = True) -> bool:
        try:
            data = json.loads(Path(path).read_text(encoding="utf-8"))
            profile = MacroProfile.from_dict(data)
        except Exception as exc:
            if show_error_dialog:
                QtWidgets.QMessageBox.warning(self, "불러오기 실패", str(exc))
            self._append_log(f"프로필 불러오기 실패: {exc}")
            return False
        self.profile = profile
        self.current_profile_path = path
        self._persist_last_profile_path(path)
        self._loading_profile = True
        self._refresh_macros()
        self._set_variable_fields(self.profile.variables)
        self._refresh_pixel_defaults(self.profile)
        self.engine.update_profile(self.profile)
        try:
            backend_state = self.engine.keyboard_status(refresh=True)
        except Exception:
            backend_state = None
        if backend_state:
            self._last_backend_state = backend_state
        try:
            self._update_keyboard_summary(backend_state)
        except Exception:
            pass
        self._loading_profile = False
        self._mark_dirty(False)
        if add_log:
            self._append_log(f"프로필 불러옴: {path}")
        return True

    def _load_profile(self):
        if not self._confirm_save_if_dirty():
            return
        path, _ = QtWidgets.QFileDialog.getOpenFileName(self, "프로필 불러오기", "", "JSON Files (*.json)")
        if not path:
            return
        self._load_profile_from_path(path)

    def _save_profile(self):
        path = self.current_profile_path
        if not path:
            return self._save_profile_as()
        return self._write_profile(path)

    def _save_profile_as(self):
        path, _ = QtWidgets.QFileDialog.getSaveFileName(
            self, "다른 이름으로 저장", self.current_profile_path or "", "JSON Files (*.json)"
        )
        if not path:
            return False
        self.current_profile_path = path
        return self._write_profile(path)

    def _write_profile(self, path: str) -> bool:
        try:
            profile = self._build_profile_from_inputs()
        except ValueError as exc:
            QtWidgets.QMessageBox.warning(self, "입력 오류", str(exc))
            return False
        try:
            Path(path).write_text(json.dumps(profile.to_dict(), indent=2, ensure_ascii=False), encoding="utf-8")
        except Exception as exc:
            QtWidgets.QMessageBox.warning(self, "저장 실패", str(exc))
            return False
        self.profile = profile
        runtime_profile = MacroProfile.from_dict(profile.to_dict())
        self.engine.update_profile(runtime_profile)
        self._refresh_pixel_defaults(self.profile)
        try:
            backend_state = self.engine.keyboard_status(refresh=True)
        except Exception:
            backend_state = None
        if backend_state:
            self._last_backend_state = backend_state
        try:
            self._update_keyboard_summary(backend_state)
        except Exception:
            pass
        self.current_profile_path = path
        self._persist_last_profile_path(path)
        self._mark_dirty(False)
        self._append_log(f"프로필 저장: {path}")
        return True

    def _refresh_resolution_fields(self, profile: MacroProfile | None = None):
        prof = profile or self.profile
        base_res = getattr(prof, "base_resolution", DEFAULT_BASE_RESOLUTION) or DEFAULT_BASE_RESOLUTION
        base_scale = float(getattr(prof, "base_scale_percent", DEFAULT_BASE_SCALE) or DEFAULT_BASE_SCALE)
        try:
            self._updating_resolution_fields = True
            if isinstance(getattr(self, "base_res_edit", None), QtWidgets.QLineEdit):
                self.base_res_edit.setText(_format_resolution(base_res))
            if isinstance(getattr(self, "base_scale_edit", None), QtWidgets.QLineEdit):
                self.base_scale_edit.setText(_format_scale_percent(base_scale))
            if isinstance(getattr(self, "current_res_edit", None), QtWidgets.QLineEdit) and not self.current_res_edit.text().strip():
                self._fill_current_resolution(silent=True)
            if isinstance(getattr(self, "current_scale_edit", None), QtWidgets.QLineEdit) and not self.current_scale_edit.text().strip():
                self._fill_current_scale(silent=True)
        finally:
            self._updating_resolution_fields = False
        if isinstance(getattr(self, "scale_preview", None), QtWidgets.QPlainTextEdit):
            if not self.scale_preview.toPlainText().strip():
                self.scale_preview.setPlainText(
                    "기준/현재 해상도와 앱 배율을 입력한 후 '프리셋 옮기기…' 버튼에서 변환을 실행하세요."
                )

    def _refresh_pixel_defaults(self, profile: MacroProfile | None = None):
        prof = profile or self.profile
        self._refresh_resolution_fields(prof)
        region = prof.pixel_region or (0, 0, 100, 100)
        color = prof.pixel_color or (255, 0, 0)
        tol = prof.pixel_tolerance if prof.pixel_tolerance is not None else 10
        expect = getattr(prof, "pixel_expect_exists", True)
        region_text = prof.pixel_region_raw or ",".join(str(v) for v in region)
        color_text = prof.pixel_color_raw or _rgb_to_hex(color)
        self._pixel_test_defaults.update(
            {
                "region_raw": region_text,
                "color_raw": color_text,
                "tolerance": tol,
                "expect_exists": expect,
            }
        )

    def _detect_app_scale(self) -> float | None:
        try:
            screen = None
            try:
                screen = self.windowHandle().screen() if self.windowHandle() else None
            except Exception:
                screen = None
            if not screen:
                screen = QtGui.QGuiApplication.primaryScreen()
            if not screen:
                screens = QtGui.QGuiApplication.screens()
                screen = screens[0] if screens else None
            if not screen:
                return None
            candidates: list[float] = []
            try:
                dpr = float(screen.devicePixelRatio())
                if dpr > 0:
                    candidates.append(dpr * 100.0)
            except Exception:
                pass
            try:
                dpi = float(screen.logicalDotsPerInch())
                if dpi > 0:
                    candidates.append(dpi / 96.0 * 100.0)
            except Exception:
                pass
            if not candidates:
                return None
            return round(max(candidates), 2)
        except Exception:
            return None

    def _detect_screen_resolution(self) -> tuple[int, int] | None:
        try:
            screen = None
            try:
                screen = self.windowHandle().screen() if self.windowHandle() else None
            except Exception:
                screen = None
            if not screen:
                screen = QtGui.QGuiApplication.primaryScreen()
            if not screen:
                screens = QtGui.QGuiApplication.screens()
                screen = screens[0] if screens else None
            if not screen:
                return None
            size = screen.geometry().size()
            dpr = 1.0
            try:
                dpr = float(screen.devicePixelRatio())
            except Exception:
                dpr = 1.0
            dpr = max(dpr, 1.0)
            width = int(round(size.width() * dpr))
            height = int(round(size.height() * dpr))
            return (width, height)
        except Exception:
            return None

    def _fill_current_scale(self, *, silent: bool = False) -> float | None:
        scale = self._detect_app_scale()
        if scale is None:
            if not silent:
                QtWidgets.QMessageBox.warning(self, "감지 실패", "현재 앱 배율을 자동으로 가져오지 못했습니다.")
            return None
        if isinstance(getattr(self, "current_scale_edit", None), QtWidgets.QLineEdit):
            prev = self.current_scale_edit.text().strip()
            text = _format_scale_percent(scale)
            self.current_scale_edit.setText(text)
            if not silent and prev != text:
                self._append_log(f"현재 앱 배율 감지: {text}")
        return scale

    def _fill_current_resolution(self, *, silent: bool = False) -> tuple[int, int] | None:
        res = self._detect_screen_resolution()
        if not res:
            if not silent:
                QtWidgets.QMessageBox.warning(self, "감지 실패", "현재 해상도를 자동으로 가져오지 못했습니다.")
            return None
        self._fill_current_scale(silent=silent)
        if isinstance(getattr(self, "current_res_edit", None), QtWidgets.QLineEdit):
            prev = self.current_res_edit.text().strip()
            text = _format_resolution(res)
            self.current_res_edit.setText(text)
            if not silent and prev != text:
                self._append_log(f"현재 해상도 감지: {text}")
        return res

    def _on_base_resolution_changed(self):
        if getattr(self, "_updating_resolution_fields", False):
            return
        self._mark_dirty()

    def _set_base_from_current_resolution(self):
        text = ""
        if isinstance(getattr(self, "current_res_edit", None), QtWidgets.QLineEdit):
            text = self.current_res_edit.text().strip()
        if text:
            try:
                parsed = _parse_resolution_text(text, allow_empty=False, default=None)
            except ValueError as exc:
                QtWidgets.QMessageBox.warning(self, "입력 오류", f"현재 해상도 입력을 확인하세요: {exc}")
                parsed = None
        else:
            parsed = None
        if not parsed:
            detected = self._fill_current_resolution(silent=True)
            if not detected:
                QtWidgets.QMessageBox.warning(self, "감지 실패", "현재 해상도를 자동으로 가져오지 못했습니다.")
                return
            parsed = detected
        scale_val = None
        scale_text = ""
        if isinstance(getattr(self, "current_scale_edit", None), QtWidgets.QLineEdit):
            scale_text = self.current_scale_edit.text().strip()
        if scale_text:
            try:
                scale_val = _parse_scale_text(scale_text, allow_empty=False, default=None)
            except ValueError:
                scale_val = None
        if scale_val is None:
            scale_val = self._fill_current_scale(silent=True)
        try:
            if isinstance(getattr(self, "base_res_edit", None), QtWidgets.QLineEdit):
                self.base_res_edit.setText(_format_resolution(parsed))
            if scale_val and isinstance(getattr(self, "base_scale_edit", None), QtWidgets.QLineEdit):
                self.base_scale_edit.setText(_format_scale_percent(scale_val))
            self._append_log(f"기준 해상도를 현재 해상도로 설정: {_format_resolution(parsed)}")
        except Exception:
            pass
        self._mark_dirty()

    def _update_scale_preview(
        self,
        changes: list[tuple[str, str, str]],
        scale_x: float,
        scale_y: float,
        base_res: tuple[int, int],
        target_res: tuple[int, int],
        base_scale: float,
        target_scale: float,
    ):
        if not isinstance(getattr(self, "scale_preview", None), QtWidgets.QPlainTextEdit):
            return
        base_scale_text = _format_scale_percent(base_scale)
        target_scale_text = _format_scale_percent(target_scale)
        lines = [
            f"기준 { _format_resolution(base_res) } @ {base_scale_text or '100%'} -> 현재 { _format_resolution(target_res) } @ {target_scale_text or '100%'}",
            f"스케일 계수(해상도+앱 배율): x={scale_x:.3f}, y={scale_y:.3f}",
        ]
        filtered = [c for c in changes if c[0] != "기준 해상도"]
        max_lines = 12
        if not filtered:
            lines.append("변경된 좌표가 없습니다.")
        else:
            for label, before, after in filtered[:max_lines]:
                lines.append(f"- {label}: {before} -> {after}")
            if len(filtered) > max_lines:
                lines.append(f"- ...외 {len(filtered) - max_lines}건")
        self.scale_preview.setPlainText("\n".join(lines))

    def _scale_and_save_profile(self):
        try:
            profile = self._build_profile_from_inputs()
        except ValueError as exc:
            QtWidgets.QMessageBox.warning(self, "입력 오류", str(exc))
            return
        base_res = getattr(profile, "base_resolution", DEFAULT_BASE_RESOLUTION) or DEFAULT_BASE_RESOLUTION
        base_scale = float(getattr(profile, "base_scale_percent", DEFAULT_BASE_SCALE) or DEFAULT_BASE_SCALE)
        target_text = ""
        try:
            if isinstance(getattr(self, "current_res_edit", None), QtWidgets.QLineEdit):
                target_text = self.current_res_edit.text()
        except Exception:
            target_text = ""
        if not target_text.strip():
            detected = self._fill_current_resolution(silent=True)
            target_text = _format_resolution(detected) if detected else ""
        try:
            target_res = _parse_resolution_text(target_text, allow_empty=False, default=None)
        except ValueError as exc:
            QtWidgets.QMessageBox.warning(self, "입력 오류", f"현재 해상도를 확인하세요: {exc}")
            return
        target_scale_text = ""
        try:
            if isinstance(getattr(self, "current_scale_edit", None), QtWidgets.QLineEdit):
                target_scale_text = self.current_scale_edit.text()
        except Exception:
            target_scale_text = ""
        if not target_scale_text.strip():
            detected_scale = self._fill_current_scale(silent=True)
            target_scale_text = _format_scale_percent(detected_scale) if detected_scale else ""
        try:
            target_scale = _parse_scale_text(target_scale_text, allow_empty=True, default=base_scale)
        except ValueError as exc:
            QtWidgets.QMessageBox.warning(self, "입력 오류", f"앱 배율을 확인하세요: {exc}")
            return
        try:
            scaled_profile, changes, scale_x, scale_y = _scale_profile(
                profile, base_res, target_res, base_scale, target_scale
            )
        except ValueError as exc:
            QtWidgets.QMessageBox.warning(self, "스케일 실패", str(exc))
            return
        self._update_scale_preview(changes, scale_x, scale_y, base_res, target_res, base_scale, target_scale)

        base_label = _format_resolution(base_res)
        target_label = _format_resolution(target_res)
        default_dir = Path(self.current_profile_path).parent if self.current_profile_path else Path.cwd()
        default_name = f"{Path(self.current_profile_path).stem if self.current_profile_path else 'profile'}_{base_label}_to_{target_label}.json"
        suggested_path = default_dir / default_name
        save_path, _ = QtWidgets.QFileDialog.getSaveFileName(
            self, "스케일된 새 프로필 저장", str(suggested_path), "JSON Files (*.json)"
        )
        if not save_path:
            return
        try:
            Path(save_path).write_text(json.dumps(scaled_profile.to_dict(), ensure_ascii=False, indent=2), encoding="utf-8")
        except Exception as exc:
            QtWidgets.QMessageBox.warning(self, "저장 실패", str(exc))
            return
        self._append_log(f"스케일된 프로필 저장: {save_path}")
        QtWidgets.QMessageBox.information(self, "저장 완료", f"스케일된 프로필을 저장했습니다.\n{save_path}")
        try:
            self.engine.update_pixel_test(region, color, tol, expect)
        except Exception:
            pass

    def _update_pixel_profile(
        self,
        region: Region,
        color: RGB,
        tolerance: int,
        expect_exists: bool,
        *,
        region_raw: str | None = None,
        color_raw: str | None = None,
        mark_dirty: bool = True,
    ):
        region_raw = region_raw if region_raw is not None else ",".join(str(v) for v in region)
        color_raw = color_raw if color_raw is not None else _rgb_to_hex(color)
        self.profile.pixel_region = tuple(int(v) for v in region)
        self.profile.pixel_region_raw = region_raw
        self.profile.pixel_color = tuple(int(c) for c in color)
        self.profile.pixel_color_raw = color_raw
        self.profile.pixel_tolerance = int(tolerance)
        if hasattr(self.profile, "pixel_expect_exists"):
            self.profile.pixel_expect_exists = bool(expect_exists)
        self._refresh_pixel_defaults(self.profile)
        self.engine.update_pixel_test(region, color, tolerance, expect_exists)
        if mark_dirty and not self._loading_profile:
            self._mark_dirty()

    def _current_pixel_defaults(self) -> dict:
        region_txt = self._pixel_test_defaults.get("region_raw") or ",".join(
            str(v) for v in (self.profile.pixel_region or (0, 0, 100, 100))
        )
        color_txt = self._pixel_test_defaults.get("color_raw") or _rgb_to_hex(self.profile.pixel_color or (255, 0, 0))
        tol = self._pixel_test_defaults.get("tolerance")
        tol_val = int(tol if tol is not None else (self.profile.pixel_tolerance or 10))
        expect = self._pixel_test_defaults.get("expect_exists")
        expect_val = bool(self.profile.pixel_expect_exists) if expect is None else bool(expect)
        interval = int(self._pixel_test_defaults.get("interval", 200) or 200)
        return {
            "region": region_txt,
            "color": color_txt,
            "tolerance": tol_val,
            "expect_exists": expect_val,
            "interval": interval,
        }

    def _tick_pixel_test(self):
        cfg = self._pixel_test_config
        if not cfg:
            return
        try:
            self.engine.run_pixel_check(
                region=cfg["region"],
                color=cfg["color"],
                tolerance=cfg["tolerance"],
                expect_exists=cfg.get("expect_exists", True),
                source=cfg.get("source"),
                label=cfg.get("label"),
            )
        except Exception as exc:
            self._append_log(f"픽셀 테스트 오류: {exc}")
            self._stop_pixel_test_loop()

    def _stop_pixel_test_loop(self):
        if self._pixel_test_timer.isActive():
            self._pixel_test_timer.stop()
        if self._pixel_test_config:
            callback = self._pixel_test_config.get("on_stop")
            self._pixel_test_config = None
            if callable(callback):
                try:
                    callback()
                except Exception:
                    pass

    def _start_pixel_test_loop(self, config: dict, *, source: str, on_stop=None, persist: bool = False):
        self._stop_pixel_test_loop()
        try:
            region = tuple(int(v) for v in config.get("region", (0, 0, 1, 1)))
            color = tuple(int(c) for c in config.get("color", (0, 0, 0)))
            tolerance = int(config.get("tolerance", 0))
            expect_exists = bool(config.get("expect_exists", True))
            interval = max(50, int(config.get("interval", 200) or 200))
        except Exception as exc:
            self._append_log(f"픽셀 테스트 시작 실패: {exc}")
            return
        self._pixel_test_defaults["interval"] = interval
        self._pixel_test_defaults["tolerance"] = tolerance
        label = config.get("label")
        self._pixel_test_config = {
            "region": region,
            "color": color,
            "tolerance": tolerance,
            "expect_exists": expect_exists,
            "source": source,
            "label": label,
            "on_stop": on_stop,
        }
        if persist:
            self._update_pixel_profile(
                region,
                color,
                tolerance,
                expect_exists,
                region_raw=config.get("region_raw"),
                color_raw=config.get("color_raw"),
                mark_dirty=not self._loading_profile,
            )
            self._persist_pixel_test_state(
                {
                    "region": config.get("region_raw") or ",".join(str(v) for v in region),
                    "color": config.get("color_raw") or _rgb_to_hex(color),
                    "tolerance": tolerance,
                    "expect_exists": expect_exists,
                    "interval": interval,
                }
            )
        self._pixel_test_timer.setInterval(interval)
        self._pixel_test_timer.start()
        self.engine.run_pixel_check(
            region=region,
            color=color,
            tolerance=tolerance,
            expect_exists=expect_exists,
            source=source,
            label=label,
        )
        self._open_debugger()

    def _start_condition_pixel_test(self, config: dict, on_stop=None):
        self._open_debugger_with_config(config)
        if self.debugger:
            self.debugger.raise_()
            self.debugger.activateWindow()

    def _start_condition_debug_session(self, provider, *, on_stop=None):
        # 기존 세션이 있다면 정리
        self._stop_condition_debug_session()
        self._condition_debug_on_stop = on_stop
        self._condition_debug_key_states = {}
        self._condition_debug_active = False
        self._last_condition_tree = None

        def eval_fn():
            try:
                payload = provider()
            except Exception as exc:
                return {"error": str(exc)}
            if not payload:
                return {"error": "조건이 없습니다."}
            cond_obj = None
            label = payload.get("label")
            resolver = payload.get("resolver")
            vars_ctx = payload.get("vars_ctx")
            macro_cond = payload.get("macro_condition")
            if macro_cond and getattr(macro_cond, "condition", None):
                cond_obj = getattr(macro_cond, "condition", None)
                label = label or getattr(macro_cond, "name", None)
            cond_obj = payload.get("condition", cond_obj)
            if cond_obj is None:
                return {"error": "조건이 없습니다."}
            if vars_ctx is None and resolver is not None:
                vars_ctx = getattr(resolver, "vars", None)
            if vars_ctx is None:
                vars_ctx = getattr(self.engine, "_vars", None)
            try:
                result = self.engine.debug_condition_tree(
                    cond_obj,
                    key_states=self._condition_debug_key_states,
                    resolver=resolver,
                    vars_ctx=vars_ctx,
                )
            except Exception as exc:
                return {"error": str(exc)}
            if isinstance(result, dict):
                self._last_condition_tree = result
            node_label = label or getattr(cond_obj, "name", None) or "조건 디버그"
            return {"result": result, "label": node_label}

        try:
            dbg = self._ensure_debugger()
            dbg.start_condition_debug(eval_fn, label="조건 디버그", stop_cb=self._on_condition_debug_stopped)
            dbg.show_and_raise()
        except Exception:
            self._finish_condition_debug(notify=False)
            return None
        self._condition_debug_active = True
        return lambda: self._stop_condition_debug_session()

    def _stop_condition_debug_session(self, notify: bool = True):
        if self.debugger:
            try:
                self.debugger.stop_condition_debug(notify=False)
            except Exception:
                pass
        self._finish_condition_debug(notify=notify)

    def _on_condition_debug_stopped(self):
        self._finish_condition_debug(notify=True)

    def _finish_condition_debug(self, *, notify: bool):
        if not self._condition_debug_active:
            return
        self._condition_debug_active = False
        self._condition_debug_key_states = {}
        self._last_condition_tree = None
        cb = self._condition_debug_on_stop
        self._condition_debug_on_stop = None
        if notify and callable(cb):
            try:
                cb()
            except Exception:
                pass

    def _capture_condition_failure(self, payload: dict):
        label = (payload or {}).get("label") or "condition"
        fail_path = (payload or {}).get("fail_path") or ""
        tree = (payload or {}).get("tree") or getattr(self, "_last_condition_tree", None)
        details = self._failed_pixel_details(tree, dedup_by_coord=True)
        if not details:
            return None

        def _pixel_pass(item: dict) -> bool:
            target = item.get("target")
            sample = item.get("sample")
            tol = int(item.get("tolerance", 0))
            expect_exists = bool(item.get("expect_exists", True))
            if not (isinstance(target, (list, tuple)) and len(target) == 3 and isinstance(sample, (list, tuple)) and len(sample) == 3):
                return False if expect_exists else True
            diff_val = max(abs(int(sample[i]) - int(target[i])) for i in range(3))
            if expect_exists:
                return diff_val <= tol
            return diff_val > tol

        any_pass = any(_pixel_pass(item) for item in details)
        if any_pass:
            return None

        parts = []
        for item in details:
            coord = item.get("coord")
            coord_txt = f"{coord[0]},{coord[1]}" if coord else "-"
            tgt = item.get("target")
            sample = item.get("sample")
            tol = item.get("tolerance")
            diff = item.get("diff")
            expect = item.get("expect_exists")
            need = item.get("need")
            tgt_hex = _rgb_to_hex(tgt) or "-"
            samp_hex = _rgb_to_hex(sample) or "-"
            tgt_chip = _color_chip_html(tgt_hex if tgt_hex != "-" else None)
            samp_chip = _color_chip_html(samp_hex if samp_hex != "-" else None)
            expect_txt = "있음" if expect else "없음"
            need_txt = f" 필요={need}" if need else ""
            parts.append(
                f"{coord_txt} [목표={tgt_hex} {tgt_chip} 샘플={samp_hex} {samp_chip} tol={tol} 기대={expect_txt}{need_txt}]"
            )
        sample_msg = f"[캡처] 조건 실패 캡처 실행 : {', '.join(parts)}"
        self._append_log(sample_msg, rich=True)
        if self.debugger:
            try:
                self.debugger._append_log_line(sample_msg, rich=True)
            except Exception:
                pass
        return None

    def _failed_pixel_details(self, tree: dict | None, *, dedup_by_coord: bool = False) -> list[dict]:
        if not tree:
            return []
        items: list[dict] = []
        seen: set[tuple[int, int]] = set()

        def _norm_coord(coord):
            if isinstance(coord, (list, tuple)) and len(coord) == 2:
                try:
                    return (int(coord[0]), int(coord[1]))
                except Exception:
                    return None
            return None

        def _walk(node: dict):
            if not isinstance(node, dict):
                return
            if node.get("type") == "pixel":
                if node.get("result") is True:
                    pass
                else:
                    detail = node.get("detail", {}).get("pixel") or {}
                    coord = _norm_coord(detail.get("sample_coord") or detail.get("coord"))
                    if dedup_by_coord and coord and coord in seen:
                        return
                    target = detail.get("color")
                    sample = detail.get("sample_color")
                    tol = int(detail.get("tolerance", 0))
                    expect_exists = bool(detail.get("expect_exists", True))
                    if isinstance(sample, (list, tuple)) and len(sample) == 3 and isinstance(target, (list, tuple)) and len(target) == 3:
                        diff = max(abs(int(sample[i]) - int(target[i])) for i in range(3))
                    else:
                        diff = None
                    items.append(
                        {
                            "name": node.get("name") or _condition_type_label("pixel"),
                            "coord": coord,
                            "target": target,
                            "sample": sample,
                            "tolerance": tol,
                            "diff": diff,
                            "expect_exists": expect_exists,
                        }
                    )
                    if dedup_by_coord and coord:
                        seen.add(coord)
            for child in node.get("children") or []:
                _walk(child)
            for child in node.get("on_true") or []:
                _walk(child)
            for child in node.get("on_false") or []:
                _walk(child)

        _walk(tree)
        return items

    def _collect_pixel_results(self, tree: dict | None) -> list[bool | None]:
        if not tree:
            return []
        results: list[bool | None] = []

        def _walk(node: dict):
            if not isinstance(node, dict):
                return
            if node.get("type") == "pixel":
                results.append(node.get("result"))
            for child in node.get("children") or []:
                _walk(child)
            for child in node.get("on_true") or []:
                _walk(child)
            for child in node.get("on_false") or []:
                _walk(child)

        _walk(tree)
        return results

    def _start_modal_pixel_test(self, config: dict, on_stop=None):
        cfg = dict(config)
        cfg.setdefault("interval", self._current_pixel_defaults().get("interval", 200))
        self._start_pixel_test_loop(
            cfg,
            source="modal",
            on_stop=on_stop,
            persist=bool(cfg.get("persist")),
        )

    def _start_debugger_pixel_test(self, config: dict, on_stop=None):
        cfg = dict(config)
        cfg.setdefault("interval", self._current_pixel_defaults().get("interval", 200))
        cfg.setdefault("tolerance", self._current_pixel_defaults().get("tolerance", 10))
        self._start_pixel_test_loop(cfg, source="debugger", on_stop=on_stop, persist=False)

    # Event handling ------------------------------------------------------
    def _tick_fail_capture_hotkey(self):
        pressed = False
        try:
            pressed = bool(get_keystate("ctrl", async_=True)) and bool(get_keystate(self._fail_capture_hotkey_key, async_=True))
        except Exception:
            pressed = False
        if pressed and not self._fail_capture_hotkey_prev:
            try:
                if self.debugger is None:
                    self._ensure_debugger()
                if self.debugger:
                    self.debugger.toggle_fail_capture_from_hotkey()
            except Exception:
                pass
        self._fail_capture_hotkey_prev = pressed

    def _poll_engine(self):
        self._tick_fail_capture_hotkey()
        cap_running = self.screenshot_manager.is_running
        if cap_running != getattr(self, "_last_capture_running", False):
            self._set_capture_status(cap_running)
        dbg_visible = bool(self.debugger and self.debugger.isVisible())
        drop_types: set[str] = set()
        if not dbg_visible:
            drop_types.update({"action_start", "action_end", "action", "condition_result", "variable_update"})
            if not getattr(self, "_log_enabled", True):
                drop_types.add("log")
        events = self.engine.drain_events(
            drop_types=drop_types or None,
            max_events=800 if dbg_visible else 400,
            max_time=0.02,
        )
        if not self.engine.events.empty():
            # 백로그가 남아 있으면 이벤트 루프를 블로킹하지 않도록 다음 틱에 이어서 처리
            QtCore.QTimer.singleShot(0, self._poll_engine)

        for event in events:
            etype = event.get("type")
            if self.debugger:
                try:
                    self.debugger.handle_event(event)
                except Exception:
                    pass
            if dbg_visible:
                # 디버거가 열려 있으면 로그는 디버거에만 표시
                continue
            # 디버그 전용 이벤트는 메인 로그에 노출하지 않는다.
            if etype in {"action_start", "action_end", "action", "condition_result", "variable_update"}:
                continue
            if etype == "log":
                self._append_log(event.get("message", ""))
            elif etype == "state":
                self._update_engine_state(event)
            elif etype == "macro_start":
                macro = event.get("macro", {}) or {}
                name = macro.get("name") or macro.get("trigger_key") or ""
                self._append_log(f"매크로 시작: {name}")
            elif etype == "macro_stop":
                macro = event.get("macro", {}) or {}
                name = macro.get("name") or macro.get("trigger_key") or ""
                self._append_log(f"매크로 종료: {name}")
            elif etype == "action_start":
                path_txt = event.get("path_text") or event.get("action_type")
                self._append_log(f"액션 시작: {path_txt}")
            elif etype == "action_end":
                path_txt = event.get("path_text") or event.get("action_type")
                self._append_log(f"액션 종료: {path_txt} ({event.get('status', 'ok')})")
            elif etype == "action":
                btn_or_key = event.get("button") or event.get("key")
                pos = event.get("pos")
                pos_txt = f" pos={pos}" if pos else ""
                self._append_log(f"액션: {event.get('action')} target={btn_or_key}{pos_txt}")

    def _update_engine_state(self, state: dict):
        running = state.get("running", False)
        active = state.get("active", False)
        paused = state.get("paused", False)
        self._set_label(self.running_label, "실행중" if running else "정지", running)
        self._set_label(self.active_label, "활성" if active else "비활성", active)
        self._set_label(self.paused_label, "일시정지" if paused else "정상", paused)
        backend = state.get("backend") or {}
        prev = self._last_backend_state or {}
        self._last_backend_state = backend
        self._update_keyboard_summary(backend, prev)

    def _set_label(self, label: QtWidgets.QLabel, text: str, on: bool):
        label.setText(text)
        base = getattr(self, "_status_badge_style", "")
        if hasattr(self, "paused_label") and label is self.paused_label:
            color = "#d98c3b" if on else "limegreen"
        else:
            color = "limegreen" if on else "gray"
        label.setStyleSheet(f"{base} color: {color}; font-weight: bold;")

    def _set_capture_status(self, running: bool):
        self._last_capture_running = bool(running)
        if hasattr(self, "capture_label"):
            base = getattr(self, "_status_badge_style", "")
            if running:
                self.capture_label.setVisible(True)
                self.capture_label.setText("녹화중")
                self.capture_label.setStyleSheet(f"{base} color: #e53935; font-weight: bold;")
            else:
                self.capture_label.setVisible(False)
                self.capture_label.setText("")

    def _update_keyboard_summary(self, backend: dict | None, prev_backend: dict | None = None):
        backend = backend or {}
        requested = backend.get("requested_mode") or getattr(self.profile, "input_mode", "hardware")
        active = backend.get("active_mode") or requested
        hardware = backend.get("hardware") or {}
        installed = bool(hardware.get("installed"))
        available = hardware.get("available")
        admin_ok = hardware.get("admin")
        device = hardware.get("current_device") or {}
        mouse_device = hardware.get("current_mouse") or {}

        if active == "hardware":
            if installed and (available is True or available is None) and admin_ok is not False:
                mode_txt = "하드웨어 (정상)"
                color = "limegreen"
            elif not installed:
                mode_txt = "하드웨어 (미설치)"
                color = "#d9534f"
            elif admin_ok is False:
                mode_txt = "하드웨어 (관리자 아님)"
                color = "#d9534f"
            else:
                mode_txt = "하드웨어 (장치 미검출)"
                color = "#d98c3b"
        else:
            mode_txt = "소프트웨어"
            color = "#5fa7f7" if requested == "software" else "#d98c3b"
            if requested == "hardware":
                mode_txt += " (폴백)"

        dev_txt = "-"
        if device:
            friendly = device.get("friendly_name") or device.get("hardware_id") or "알 수 없음"
            dev_txt = friendly
            if device.get("id"):
                dev_txt += f" #{device.get('id')}"
        mouse_txt = "-"
        if mouse_device:
            friendly_mouse = mouse_device.get("friendly_name") or mouse_device.get("hardware_id") or "알 수 없음"
            mouse_txt = friendly_mouse
            if mouse_device.get("id"):
                mouse_txt += f" #{mouse_device.get('id')}"

        self.keyboard_mode_label.setText(mode_txt)
        self.keyboard_mode_label.setStyleSheet(f"color: {color}; font-weight: bold;")
        self.keyboard_device_label.setText(dev_txt)
        self.keyboard_device_label.setStyleSheet("color: #333;")
        self.mouse_device_label.setText(mouse_txt)
        self.mouse_device_label.setStyleSheet("color: #333;")

        test_key = backend.get("keyboard_test_key") or getattr(self.profile, "keyboard_test_key", "f24")
        self.keyboard_test_btn.setText(f"테스트 ({str(test_key).upper()})")
        self.profile.input_mode = requested
        self.profile.keyboard_test_key = test_key
        if device:
            self.profile.keyboard_device_id = device.get("id")
            self.profile.keyboard_hardware_id = device.get("hardware_id")
        if mouse_device:
            self.profile.mouse_device_id = mouse_device.get("id")
            self.profile.mouse_hardware_id = mouse_device.get("hardware_id")
        hint = getattr(self, "_status_hint", "")
        if hint:
            self.statusBar().showMessage(f"{hint} | 입력 {mode_txt} (키보드 {dev_txt}, 마우스 {mouse_txt})")
        prev_active = (prev_backend or {}).get("active_mode")
        if prev_active == "hardware" and active != "hardware":
            self._append_log("Interception 불가 또는 장치 미검출로 소프트웨어 입력으로 전환되었습니다.")

    def _toggle_log_enabled(self, enabled: bool):
        self._log_enabled = bool(enabled)
        if hasattr(self, "_state"):
            try:
                self._update_state("log_enabled", self._log_enabled)
            except Exception:
                pass
        # 동기화: 두 토글이 서로 상태를 맞추도록 한다.
        if hasattr(self, "log_enable_checkbox") and self.log_enable_checkbox and self.log_enable_checkbox.isChecked() != self._log_enabled:
            self.log_enable_checkbox.blockSignals(True)
            self.log_enable_checkbox.setChecked(self._log_enabled)
            self.log_enable_checkbox.blockSignals(False)
        if hasattr(self, "log_toggle_btn") and self.log_toggle_btn and self.log_toggle_btn.isChecked() != self._log_enabled:
            self.log_toggle_btn.blockSignals(True)
            self.log_toggle_btn.setChecked(self._log_enabled)
            self.log_toggle_btn.blockSignals(False)
        if hasattr(self, "log_view") and self.log_view:
            self.log_view.setVisible(self._log_enabled)
            if not self._log_enabled:
                self.log_view.clear()
        if hasattr(self, "log_group") and self.log_group:
            self.log_group.setVisible(self._log_enabled)

    def _append_log(self, message: str, *, rich: bool = False):
        if not getattr(self, "_log_enabled", True):
            return
        ts = _format_dt()
        entry = f"[{ts}] {message}"
        if not rich:
            entry = html.escape(entry).replace("\n", "<br>")
        self.log_view.append(entry)
        self.log_view.moveCursor(QtGui.QTextCursor.MoveOperation.End)

    def _collect_pixel_samples(self, tree: dict | None, *, only_failed: bool = False, dedup_by_coord: bool = False) -> list[str]:
        if not tree:
            return []
        samples: list[str] = []
        seen: set[tuple[int, int]] = set()

        def _norm_coord(coord):
            if isinstance(coord, (list, tuple)) and len(coord) == 2:
                try:
                    return (int(coord[0]), int(coord[1]))
                except Exception:
                    return None
            return None

        def _walk(node: dict):
            if not isinstance(node, dict):
                return
            if node.get("type") == "pixel":
                if only_failed and node.get("result") is True:
                    pass
                else:
                    detail = node.get("detail", {}).get("pixel") or {}
                    coord = _norm_coord(detail.get("sample_coord") or detail.get("coord"))
                    if dedup_by_coord and coord and coord in seen:
                        return
                    sample = detail.get("sample_color")
                    if isinstance(sample, (list, tuple)) and len(sample) == 3:
                        hex_txt = "#" + "".join(f"{int(c):02x}" for c in sample)
                        if coord:
                            samples.append(f"{coord[0]},{coord[1]} [{hex_txt}]")
                        else:
                            samples.append(hex_txt)
                        if dedup_by_coord and coord:
                            seen.add(coord)
            for child in node.get("children") or []:
                _walk(child)
            for child in node.get("on_true") or []:
                _walk(child)
            for child in node.get("on_false") or []:
                _walk(child)

        _walk(tree)
        return samples

    def _collect_pixel_coords(self, tree: dict | None, *, only_failed: bool = False, dedup_by_coord: bool = False) -> list[tuple[int, int]]:
        if not tree:
            return []
        coords: list[tuple[int, int]] = []
        seen: set[tuple[int, int]] = set()

        def _norm_coord(coord):
            if isinstance(coord, (list, tuple)) and len(coord) == 2:
                try:
                    return (int(coord[0]), int(coord[1]))
                except Exception:
                    return None
            return None

        def _walk(node: dict):
            if not isinstance(node, dict):
                return
            if node.get("type") == "pixel":
                if only_failed and node.get("result") is True:
                    pass
                else:
                    detail = node.get("detail", {}).get("pixel") or {}
                    coord = _norm_coord(detail.get("sample_coord") or detail.get("coord"))
                    if coord:
                        if dedup_by_coord and coord in seen:
                            return
                        coords.append(coord)
                        if dedup_by_coord:
                            seen.add(coord)
            for child in node.get("children") or []:
                _walk(child)
            for child in node.get("on_true") or []:
                _walk(child)
            for child in node.get("on_false") or []:
                _walk(child)

        _walk(tree)
        return coords

    def _failed_pixel_bbox(self, tree: dict | None):
        if not tree:
            return None
        boxes: list[tuple[int, int, int, int]] = []

        def _walk(node: dict):
            if not isinstance(node, dict):
                return
            if node.get("type") == "pixel":
                if node.get("result") is True:
                    pass
                else:
                    detail = node.get("detail", {}).get("pixel") or {}
                    region = detail.get("region")
                    if isinstance(region, (list, tuple)) and len(region) == 4:
                        try:
                            x, y, w, h = (int(region[0]), int(region[1]), int(region[2]), int(region[3]))
                            if w > 0 and h > 0:
                                boxes.append((x, y, w, h))
                        except Exception:
                            pass
            for child in node.get("children") or []:
                _walk(child)
            for child in node.get("on_true") or []:
                _walk(child)
            for child in node.get("on_false") or []:
                _walk(child)

        _walk(tree)
        if not boxes:
            return None
        min_x = min(b[0] for b in boxes)
        min_y = min(b[1] for b in boxes)
        max_x = max(b[0] + b[2] for b in boxes)
        max_y = max(b[1] + b[3] for b in boxes)
        return (min_x, min_y, max_x - min_x, max_y - min_y)

    def _first_failed_pixel_image(self, tree: dict | None):
        if not tree:
            return None

        def _walk(node: dict):
            if not isinstance(node, dict):
                return None
            if node.get("type") == "pixel" and node.get("result") is not True:
                detail = node.get("detail", {}).get("pixel") or {}
                data = detail.get("image_png")
                region = detail.get("region")
                if data and isinstance(data, (bytes, bytearray)) and isinstance(region, (list, tuple)) and len(region) == 4:
                    try:
                        x, y, w, h = (int(region[0]), int(region[1]), int(region[2]), int(region[3]))
                        if w > 0 and h > 0:
                            return ((x, y, w, h), bytes(data))
                    except Exception:
                        pass
            for child in node.get("children") or []:
                found = _walk(child)
                if found:
                    return found
            for child in node.get("on_true") or []:
                found = _walk(child)
                if found:
                    return found
            for child in node.get("on_false") or []:
                found = _walk(child)
                if found:
                    return found
            return None

        return _walk(tree)

    def _log_admin_status(self):
        if self.is_admin:
            self.admin_label.setText("관리자(O)")
            base = getattr(self, "_status_badge_style", "")
            self.admin_label.setStyleSheet(f"{base} color: limegreen; font-weight: bold;")
            self._append_log("관리자 모드: O")
        else:
            self.admin_label.setText("관리자(X)")
            base = getattr(self, "_status_badge_style", "")
            self.admin_label.setStyleSheet(f"{base} color: red; font-weight: bold;")
            self._append_log("관리자 모드: X (관리자 권한 필요)")

    def closeEvent(self, event: QtGui.QCloseEvent):
        if not self._confirm_save_if_dirty():
            event.ignore()
            return
        # 최신 스크린샷 설정을 저장
        self._persist_screenshot_state(self._current_screenshot_state())
        self._stop_condition_debug_session(notify=False)
        self._stop_pixel_test_loop()
        if self.debugger:
            try:
                self._persist_debugger_state(self.debugger._collect_state())
            except Exception:
                pass
        if self._image_viewer_dialog:
            try:
                self._persist_image_viewer_state(self._image_viewer_state)
            except Exception:
                pass
        if self._color_calc_dialog:
            try:
                self._color_calc_dialog._save_state()
            except Exception:
                pass
        self._fail_capture_hotkey_prev = False
        self.screenshot_manager.shutdown()
        self.engine.stop()
        return super().closeEvent(event)

    def _current_screenshot_state(self) -> dict:
        return {
            "interval": self.screenshot_manager.interval,
            "format": self.screenshot_manager.image_format,
            "jpeg_quality": self.screenshot_manager.jpeg_quality,
            "png_compress_level": self.screenshot_manager.png_compress_level,
            "queue_size": self.screenshot_manager.max_queue_size,
            "hotkey_start": self.screenshot_manager.hotkeys.start,
            "hotkey_stop": self.screenshot_manager.hotkeys.stop,
            "hotkey_capture": self.screenshot_manager.hotkeys.capture,
            "hotkey_enabled": self.screenshot_manager.hotkeys.enabled,
        }


def main():
    if not _is_admin():
        _relaunch_as_admin()
        return
    try:
        app = QtWidgets.QApplication(sys.argv)
        engine = MacroEngine()
        window = MacroWindow(engine)
        window.show()
        sys.exit(app.exec())
    except Exception as exc:
        # GUI가 바로 종료될 때 콘솔에 오류를 보여 디버깅할 수 있도록 한다.
        import traceback

        traceback.print_exc()
        QtWidgets.QMessageBox.critical(None, "오류", str(exc))
        sys.exit(1)


if __name__ == "__main__":
    main()
