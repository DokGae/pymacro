from __future__ import annotations
import copy
import ctypes
import html
import io
import itertools
import math
import json
import shutil
import queue
import re
import sys
import threading
import time
import unicodedata
from pathlib import Path
from typing import Any, Callable, List, Optional
from PyQt6 import QtCore, QtGui, QtWidgets
import numpy as np
from PIL import Image
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
    MacroTrigger,
    MacroCondition,
    MacroEngine,
    MacroProfile,
    MacroVariables,
    Step,
    VariableResolver,
    KeyDelayConfig,
    DEFAULT_BASE_RESOLUTION,
    DEFAULT_BASE_SCALE,
    normalize_trigger_key,
    parse_trigger_keys,
)
from lib import keyboard as kbutil
from lib.interception import Interception, KeyFilter, KeyState, MapVk, MouseFilter, MouseState, map_virtual_key
from lib.keyboard import get_keystate
from lib.processes import get_foreground_process, list_processes
from lib.pixel import RGB, Region, PixelPattern, PixelPatternPoint, capture_region
PATTERN_DIR = Path(__file__).parent / "pattern"
PATTERN_FILE = PATTERN_DIR / "patterns.json"
def _load_shared_patterns() -> dict[str, PixelPattern]:
    """pattern 폴더의 각 패턴 파일(*.json)을 개별로 읽어 공용 패턴을 만든다."""
    result: dict[str, PixelPattern] = {}
    try:
        if not PATTERN_DIR.exists():
            return {}
        # 1) 개별 파일 로드
        for path in PATTERN_DIR.glob("*.json"):
            if path.name == "patterns.json":  # 구버전 파일은 무시
                continue
            try:
                data = json.loads(path.read_text(encoding="utf-8"))
            except Exception:
                continue
            if not isinstance(data, dict):
                continue
            merged = dict(data)
            merged.setdefault("name", merged.get("name") or path.stem)
            pat = PixelPattern.from_dict(merged)
            pat.tolerance = 0
            for pt in pat.points:
                pt.tolerance = None
            result[pat.name] = pat
        # 2) 레거시 patterns.json 병합(존재하면, 이름이 겹치지 않을 때만)
        if PATTERN_FILE.exists():
            try:
                legacy = json.loads(PATTERN_FILE.read_text(encoding="utf-8"))
                if isinstance(legacy, dict):
                    for name, item in legacy.items():
                        if name in result or not isinstance(item, dict):
                            continue
                        merged = dict(item)
                        merged.setdefault("name", name)
                        pat = PixelPattern.from_dict(merged)
                        pat.tolerance = 0
                        for pt in pat.points:
                            pt.tolerance = None
                        result[pat.name] = pat
            except Exception:
                pass
    except Exception:
        return result
    return result
def _save_shared_patterns(patterns: dict[str, PixelPattern]):
    """공용 패턴을 pattern/<name>.json 파일 단위로 즉시 저장한다."""
    try:
        PATTERN_DIR.mkdir(parents=True, exist_ok=True)
        # 기존 파일 목록(레거시 patterns.json 제외)
        existing = {
            p.stem: p
            for p in PATTERN_DIR.glob("*.json")
            if p.is_file() and p.name != "patterns.json"
        }
        for name, pat in (patterns or {}).items():
            path = PATTERN_DIR / f"{name}.json"
            payload = pat.to_dict()
            path.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
            existing.pop(name, None)
        # 남은 파일은 삭제(패턴이 제거된 경우)
        for _stem, path in existing.items():
            try:
                path.unlink(missing_ok=True)
            except Exception:
                pass
        # 레거시 patterns.json 은 더 이상 사용하지 않으므로 삭제
        try:
            if PATTERN_FILE.exists():
                PATTERN_FILE.unlink()
        except Exception:
            pass
    except Exception:
        # 저장 실패는 치명적이지 않으므로 조용히 무시
        pass
def _merge_profile_patterns_to_shared(profile_patterns: dict[str, PixelPattern] | None) -> dict[str, PixelPattern]:
    """프로필에 남아 있는 패턴을 공용 저장소(pattern/patterns.json)로 옮겨 한 곳에서만 관리한다."""
    shared = _load_shared_patterns()
    # 이미 공용 패턴 파일이 존재한다면(비어 있어도) 사용자 의도를 존중해 프로필 패턴을 재주입하지 않는다.
    if any(PATTERN_DIR.glob("*.json")):
        return shared
    incoming = profile_patterns or {}
    if not incoming:
        return shared
    merged = copy.deepcopy(shared)
    changed = False
    for name, pat in incoming.items():
        if name not in merged:
            merged[name] = copy.deepcopy(pat)
            changed = True
    if changed:
        _save_shared_patterns(merged)
    return merged
MAX_RECENT_PROFILES = 15
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
def _parse_name_list(text: str) -> list[str]:
    raw = str(text or "")
    parts = re.split(r"[;,]", raw)
    return [p.strip() for p in parts if p and p.strip()]
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
def _normalize_profile_path(path: str) -> str:
    try:
        return str(Path(path).expanduser().resolve())
    except Exception:
        try:
            return str(Path(path))
        except Exception:
            return str(path)
def _elide_middle(text: str, max_len: int = 60) -> str:
    if not text or len(text) <= max_len:
        return text
    head = max(3, max_len // 2 - 2)
    tail = max(3, max_len - head - 3)
    return f"{text[:head]}...{text[-tail:]}"
def _default_macro() -> Macro:
    # z 누르고 있는 동안 r → sleep 50 → t 반복, 픽셀 맞으면 f1, 아니면 f2
    pixel_cond = Condition(type="pixel", region=(0, 0, 100, 100), color=(255, 0, 0), tolerance=0)
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
    return Macro(
        trigger_key="z",
        mode="hold",
        triggers=[MacroTrigger(key="z", mode="hold")],
        suppress_trigger=False,
        actions=actions,
    )
DEFAULT_PROFILE = MacroProfile(
    macros=[_default_macro()],
    pixel_region=(0, 0, 100, 100),
    pixel_color=(255, 0, 0),
    pixel_tolerance=0,
)
HEX_CHARS = set("0123456789abcdefABCDEF")
_RECORDER_RESERVED_KEYS = {"pgup", "pageup", "pgdown", "pagedown"}


def _normalize_hotkey_name(raw: Any) -> str | None:
    text = str(raw or "").strip().lower()
    if not text:
        return None
    if text == "pageup":
        return "pgup"
    if text == "pagedown":
        return "pgdown"
    return text


def _sanitize_screenshot_hotkey(raw: Any, *, allow_reserved: bool = True) -> str | None:
    key = _normalize_hotkey_name(raw)
    if not key:
        return None
    if not allow_reserved and key in _RECORDER_RESERVED_KEYS:
        return None
    return key


ACTION_TYPE_OPTIONS = [
    ("탭 (누르고 떼기)", "press"),
    ("누르기 유지 (down)", "down"),
    ("떼기 (up)", "up"),
    ("마우스 클릭", "mouse_click"),
    ("마우스 누르기 (down)", "mouse_down"),
    ("마우스 떼기 (up)", "mouse_up"),
    ("마우스 이동", "mouse_move"),
    ("대기 (sleep)", "sleep"),
    ("소리 알림", "sound_alert"),
    ("타이머 설정", "timer"),
]
_VK_TO_MACRO_KEY: dict[int, str] = {
    8: "backspace",
    9: "tab",
    13: "enter",
    16: "shift",
    17: "ctrl",
    18: "alt",
    19: "pause",
    20: "capslock",
    27: "esc",
    32: "space",
    33: "pageup",
    34: "pagedown",
    35: "end",
    36: "home",
    37: "left",
    38: "up",
    39: "right",
    40: "down",
    45: "insert",
    46: "delete",
    91: "win",
    92: "win",
    93: "apps",
    144: "numlock",
    145: "scrolllock",
    186: ";",
    187: "=",
    188: ",",
    189: "-",
    190: ".",
    191: "/",
    192: "`",
    219: "[",
    220: "\\",
    221: "]",
    222: "'",
}
def _vk_to_macro_key(vk: int) -> str | None:
    try:
        code = int(vk)
    except Exception:
        return None
    key: str | None = None
    if 65 <= code <= 90:
        key = chr(code).lower()
    elif 48 <= code <= 57:
        key = chr(code)
    elif 112 <= code <= 135:
        key = f"f{code - 111}"
    elif 96 <= code <= 105:
        # 넘패드 숫자는 매크로에서 일반 숫자 키로 취급해도 동일하게 동작한다.
        key = str(code - 96)
    elif code in (106, 107, 109, 110, 111):
        key = {106: "*", 107: "+", 109: "-", 110: ".", 111: "/"}[code]
    else:
        key = _VK_TO_MACRO_KEY.get(code)
    if not key:
        return None
    try:
        kbutil.vk_from_key(key)
    except Exception:
        return None
    return key
def _macro_key_from_stroke(stroke) -> str | None:
    if stroke is None:
        return None
    try:
        sc = int(getattr(stroke, "code", 0))
    except Exception:
        return None
    if sc <= 0:
        return None
    try:
        vk = int(map_virtual_key(sc, MapVk.ScToVk) or 0)
    except Exception:
        vk = 0
    if vk <= 0:
        return None
    return _vk_to_macro_key(vk)
def _stroke_key_label(stroke, key_name: str | None = None) -> str:
    try:
        sc = int(getattr(stroke, "code", 0))
    except Exception:
        sc = 0
    try:
        vk = int(map_virtual_key(sc, MapVk.ScToVk) or 0)
    except Exception:
        vk = 0
    label = key_name or ""
    parts: list[str] = []
    if label:
        parts.append(label)
    if vk > 0:
        parts.append(f"VK {vk}")
    if sc > 0:
        parts.append(f"SC {sc}")
    return " / ".join(parts) if parts else "알 수 없는 키"
class _WinPoint(ctypes.Structure):
    _fields_ = [("x", ctypes.c_long), ("y", ctypes.c_long)]
def _current_cursor_pos() -> tuple[int, int] | None:
    try:
        user32 = ctypes.windll.user32
    except Exception:
        return None
    try:
        pt = _WinPoint()
        ok = bool(user32.GetCursorPos(ctypes.byref(pt)))
        if not ok:
            return None
        return int(pt.x), int(pt.y)
    except Exception:
        return None
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
def _attach_hex_preview_chip(edit: QtWidgets.QLineEdit) -> QtGui.QAction:
    """텍스트 입력 옆에 HEX 색상 미리보기 칩을 붙인다."""
    action = edit.addAction(QtGui.QIcon(), QtWidgets.QLineEdit.ActionPosition.TrailingPosition)
    action.setVisible(False)
    action.setToolTip("입력 색상 미리보기")
    def _update(text: str | None):
        raw = (text or "").strip()
        icon = QtGui.QIcon()
        show = False
        if raw:
            try:
                normalized = _normalize_hex_line(raw)
                color = QtGui.QColor(f"#{normalized}")
                if color.isValid():
                    pix = QtGui.QPixmap(12, 12)
                    pix.fill(color)
                    icon = QtGui.QIcon(pix)
                    show = True
            except Exception:
                show = False
        action.setIcon(icon)
        action.setVisible(show)
    edit.textChanged.connect(_update)
    _update(edit.text())
    return action
def _make_hex_preview_label(*, size: int = 14) -> QtWidgets.QLabel:
    """라벨 옆에 붙이는 작은 색상 칩 레이블을 생성한다."""
    lbl = QtWidgets.QLabel()
    lbl.setFixedSize(size, size)
    lbl.setFrameShape(QtWidgets.QFrame.Shape.NoFrame)
    lbl.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)
    lbl.setContentsMargins(0, 0, 0, 0)
    lbl.setStyleSheet("padding:0;margin:0;")
    lbl.setToolTip("입력 색상 미리보기")
    return lbl
def _update_hex_preview_label(label: QtWidgets.QLabel | None, text: str | None, *, size: int | None = None):
    if not label:
        return
    effective_size = size or max(1, min(label.width(), label.height()))
    raw = (text or "").strip()
    if raw:
        try:
            normalized = _normalize_hex_line(raw)
            color = QtGui.QColor(f"#{normalized}")
            if color.isValid():
                pix = QtGui.QPixmap(effective_size, effective_size)
                pix.fill(color)
                label.setPixmap(pix)
                label.setVisible(True)
                return
        except Exception:
            pass
    label.clear()
    label.setVisible(False)
def _make_hex_chip_icon(text: str | None, *, size: int = 12) -> QtGui.QIcon:
    raw = (text or "").strip().lstrip("#")
    if len(raw) != 6 or any(ch not in HEX_CHARS for ch in raw):
        return QtGui.QIcon()
    color = QtGui.QColor(f"#{raw}")
    if not color.isValid():
        return QtGui.QIcon()
    pix = QtGui.QPixmap(size, size)
    pix.fill(QtCore.Qt.GlobalColor.transparent)
    painter = QtGui.QPainter(pix)
    painter.fillRect(0, 0, size, size, color)
    luminance = 0.299 * color.red() + 0.587 * color.green() + 0.114 * color.blue()
    border = QtGui.QColor("#000" if luminance > 186 else "#fff")
    pen = QtGui.QPen(border)
    pen.setWidth(1)
    painter.setPen(pen)
    painter.drawRect(0, 0, size - 1, size - 1)
    painter.end()
    return QtGui.QIcon(pix)
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
            cond, acts, _, _ = _split_elif_block(blk)
            if cond:
                transform_condition(cond, f"{macro_ctx} / {path_label} / elif#{blk_idx + 1}")
            for idx, child in enumerate(acts or []):
                transform_action(child, macro_ctx, path_parts + [f"elif#{blk_idx + 1}[{idx + 1}]"])
    for macro_idx, macro in enumerate(getattr(profile, "macros", []) or []):
        try:
            trigger_label = macro.trigger_label(include_mode=False)
        except Exception:
            trigger_label = getattr(macro, "trigger_key", "") or ""
        macro_ctx = f"매크로#{macro_idx + 1}({macro.name or trigger_label})"
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
class InteractionDialog(QtWidgets.QDialog):
    def __init__(
        self,
        *,
        mode: str = "none",
        targets: list[str] | None = None,
        excludes: list[str] | None = None,
        allow: list[str] | None = None,
        block: list[str] | None = None,
        macro_list_provider=None,
        parent=None,
    ):
        super().__init__(parent)
        self.setWindowTitle("상호작용 설정")
        self.setModal(False)
        self.setWindowModality(QtCore.Qt.WindowModality.NonModal)
        self.resize(520, 260)
        self._macro_list_provider = macro_list_provider
        layout = QtWidgets.QVBoxLayout(self)
        form = QtWidgets.QFormLayout()
        self.mode_combo = QtWidgets.QComboBox()
        self.mode_combo.addItem("상호작용 없음", "none")
        self.mode_combo.addItem("다른 매크로 중지", "stop")
        self.mode_combo.addItem("다른 매크로 대기/일시정지", "suspend")
        form.addRow("기본 동작", self.mode_combo)
        self.targets_edit, tgt_btn = self._line_with_picker("적용 대상 (비우면 전체)")
        self.exclude_edit, exc_btn = self._line_with_picker("영향 제외")
        self.allow_edit, allow_btn = self._line_with_picker("나를 중단 허용")
        self.block_edit, block_btn = self._line_with_picker("나를 중단 차단")
        form.addRow("영향 대상", self._hline(self.targets_edit, tgt_btn))
        form.addRow("영향 제외", self._hline(self.exclude_edit, exc_btn))
        form.addRow("나를 중단 허용", self._hline(self.allow_edit, allow_btn))
        form.addRow("나를 중단 차단", self._hline(self.block_edit, block_btn))
        layout.addLayout(form)
        btn_row = QtWidgets.QHBoxLayout()
        btn_row.addStretch()
        ok_btn = QtWidgets.QPushButton("확인")
        cancel_btn = QtWidgets.QPushButton("취소")
        btn_row.addWidget(ok_btn)
        btn_row.addWidget(cancel_btn)
        layout.addLayout(btn_row)
        ok_btn.clicked.connect(self.accept)
        cancel_btn.clicked.connect(self.reject)
        self.mode_combo.setCurrentIndex({"none": 0, "stop": 1, "suspend": 2}.get((mode or "none").lower(), 0))
        self.targets_edit.setText(", ".join(targets or []))
        self.exclude_edit.setText(", ".join(excludes or []))
        self.allow_edit.setText(", ".join(allow or []))
        self.block_edit.setText(", ".join(block or []))
    def _hline(self, edit: QtWidgets.QLineEdit, btn: QtWidgets.QToolButton) -> QtWidgets.QWidget:
        w = QtWidgets.QWidget()
        lay = QtWidgets.QHBoxLayout(w)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.addWidget(edit, stretch=1)
        lay.addWidget(btn)
        return w
    def _line_with_picker(self, placeholder: str) -> tuple[QtWidgets.QLineEdit, QtWidgets.QToolButton]:
        edit = QtWidgets.QLineEdit()
        edit.setPlaceholderText(placeholder)
        btn = QtWidgets.QToolButton()
        btn.setText("목록")
        btn.setPopupMode(QtWidgets.QToolButton.ToolButtonPopupMode.InstantPopup)
        menu = QtWidgets.QMenu(btn)
        btn.setMenu(menu)
        menu.aboutToShow.connect(lambda m=menu, e=edit: self._populate_macro_menu(m, e))
        return edit, btn
    def _populate_macro_menu(self, menu: QtWidgets.QMenu, target_edit: QtWidgets.QLineEdit):
        menu.clear()
        items: list[str] = []
        try:
            if callable(self._macro_list_provider):
                items = self._macro_list_provider() or []
        except Exception:
            items = []
        if not items:
            menu.addAction("목록 없음").setEnabled(False)
            return
        seen = set()
        for name in items:
            key = name.strip()
            if not key or key in seen:
                continue
            seen.add(key)
            act = menu.addAction(key)
            act.triggered.connect(lambda _=False, v=key: self._append_value(target_edit, v))
    def _append_value(self, edit: QtWidgets.QLineEdit, value: str):
        items = _parse_name_list(edit.text())
        if value not in items:
            items.append(value)
        edit.setText(", ".join(items))
    def result_values(self) -> tuple[str, list[str], list[str], list[str], list[str]]:
        return (
            self.mode_combo.currentData() or "none",
            _parse_name_list(self.targets_edit.text()),
            _parse_name_list(self.exclude_edit.text()),
            _parse_name_list(self.allow_edit.text()),
            _parse_name_list(self.block_edit.text()),
        )
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
def _condition_hex_color(cond: Condition) -> str | None:
    if not isinstance(cond, Condition):
        return None
    if cond.type != "pixel" or getattr(cond, "pixel_pattern", None):
        return None
    raw = getattr(cond, "color_raw", "") or ""
    if raw:
        try:
            return f"#{_normalize_hex_line(raw)}"
        except Exception:
            pass
    return _rgb_to_hex(cond.color)
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
        min_cnt = max(1, int(getattr(cond, "pixel_min_count", 1) or 1))
        exists = getattr(cond, "pixel_exists", True)
        state = f">={min_cnt}픽셀 있을 때 참" if exists else "일치 픽셀이 없을 때 참"
        if getattr(cond, "pixel_pattern", None):
            pat = getattr(cond, "pixel_pattern", "")
            return f"픽셀패턴 {pat} @ {region} tol={cond.tolerance} ({state}일 때 참){suffix}"
        color_hex = cond.color_raw or (_rgb_to_hex(cond.color) or "------")
        return f"픽셀 {region} #{color_hex} tol={cond.tolerance} ({state}){suffix}"
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
def _split_elif_block(blk):
    cond = None
    acts = []
    desc = ""
    enabled_override = None
    if isinstance(blk, (list, tuple)):
        if len(blk) >= 2:
            cond, acts = blk[0], blk[1]
        if len(blk) >= 3:
            desc_val = blk[2]
            desc = desc_val if isinstance(desc_val, str) else str(desc_val) if desc_val is not None else ""
        if len(blk) >= 4 and isinstance(blk[3], bool):
            enabled_override = blk[3]
    if isinstance(enabled_override, bool) and isinstance(cond, Condition):
        try:
            cond.enabled = enabled_override
        except Exception:
            pass
    return cond if isinstance(cond, Condition) else None, list(acts or []), desc or "", enabled_override
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
        pattern_provider=None,
        open_pattern_manager=None,
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
        self._pattern_provider = pattern_provider
        self._open_pattern_manager = open_pattern_manager
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
        self.color_preview = _make_hex_preview_label()
        self.color_edit.textChanged.connect(lambda txt: _update_hex_preview_label(self.color_preview, txt))
        _update_hex_preview_label(self.color_preview, self.color_edit.text())
        self._install_var_completer(self.region_edit, "region")
        self._install_var_completer(self.color_edit, "color")
        self.pattern_check = QtWidgets.QCheckBox("패턴 사용")
        self.pattern_combo = QtWidgets.QComboBox()
        self.pattern_manage_btn = QtWidgets.QPushButton("패턴 관리")
        self.pattern_manage_btn.clicked.connect(self._open_pattern_manager_cb)
        self.pattern_check.stateChanged.connect(self._sync_type_visibility)
        self._reload_patterns()
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
        self.pixel_min_spin = QtWidgets.QSpinBox()
        self.pixel_min_spin.setRange(1, 100000)
        self.pixel_min_spin.setValue(1)
        self.pixel_min_spin.setToolTip("범위 안에서 허용오차를 만족해야 하는 픽셀의 최소 개수입니다.")
        self.pixel_expect_combo = QtWidgets.QComboBox()
        self.pixel_expect_combo.addItem("색상이 있을 때 참", True)
        self.pixel_expect_combo.addItem("색상이 없을 때 참", False)
        self.pixel_expect_combo.currentIndexChanged.connect(self._sync_type_visibility)
        self.group_hint = QtWidgets.QLabel("하위 조건은 트리에서 추가/삭제하세요.")
        self.group_hint.setStyleSheet("color: gray;")
        self.form.addRow("조건 타입", self.type_combo)
        self.form.addRow("이름(선택)", self.name_edit)
        self.form.addRow("키/마우스", self.key_edit)
        self.form.addRow("키 모드", self.key_mode_combo)
        self.form.addRow("여러 키 묶기", self.key_group_mode_combo)
        self.form.addRow("Region x,y,w,h", self.region_edit)
        self.form.addRow("+dx,dy,dw,dh (선택)", self.region_offset_edit)
        color_row = QtWidgets.QHBoxLayout()
        color_row.setContentsMargins(0, 0, 0, 0)
        color_row.setSpacing(6)
        color_row.addWidget(self.color_edit, 1)
        color_row.addWidget(self.color_preview)
        color_wrap = QtWidgets.QWidget()
        color_wrap.setLayout(color_row)
        self.color_wrap = color_wrap
        self.form.addRow("색상", color_wrap)
        pattern_row = QtWidgets.QHBoxLayout()
        pattern_row.setContentsMargins(0, 0, 0, 0)
        pattern_row.setSpacing(6)
        pattern_row.addWidget(self.pattern_check)
        pattern_row.addWidget(self.pattern_combo, 1)
        pattern_row.addWidget(self.pattern_manage_btn)
        pattern_wrap = QtWidgets.QWidget()
        pattern_wrap.setLayout(pattern_row)
        self.form.addRow("패턴", pattern_wrap)
        self.form.addRow("Tolerance", self.tol_spin)
        self.form.addRow("최소 일치 픽셀 수", self.pixel_min_spin)
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
            (
                self.region_edit,
                self.region_offset_edit,
                self.color_edit,
                self.tol_spin,
                self.pixel_min_spin,
                self.pixel_expect_combo,
                self.test_btn,
                self.pattern_check,
                self.pattern_combo,
                self.pattern_manage_btn,
            ),
            visible=is_pixel,
            enabled=is_pixel,
        )
        if is_pixel:
            use_pat = self.pattern_check.isChecked()
            # 색상 입력 필드는 패턴 사용 시 숨김
            self.color_wrap.setVisible(not use_pat)
            if self.form.labelForField(self.color_wrap):
                self.form.labelForField(self.color_wrap).setVisible(not use_pat)
            min_visible = not use_pat and bool(self.pixel_expect_combo.currentData())
            for w in (self.pixel_min_spin,):
                w.setVisible(min_visible)
                w.setEnabled(min_visible)
                label = self.form.labelForField(w)
                if label is not None:
                    label.setVisible(min_visible)
        else:
            self.color_wrap.setVisible(False)
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
            if getattr(cond, "pixel_pattern", None):
                self.pattern_check.setChecked(True)
                idx_pat = self.pattern_combo.findData(cond.pixel_pattern)
                if idx_pat >= 0:
                    self.pattern_combo.setCurrentIndex(idx_pat)
            else:
                self.pattern_check.setChecked(False)
            if cond.color_raw is not None:
                self.color_edit.setText(cond.color_raw)
            else:
                self.color_edit.setText(_rgb_to_hex(cond.color))
            self.tol_spin.setValue(cond.tolerance)
            try:
                self.pixel_min_spin.setValue(max(1, int(getattr(cond, "pixel_min_count", 1) or 1)))
            except Exception:
                self.pixel_min_spin.setValue(1)
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
            region = _parse_region(region_text, resolver=self._resolver)
            color_text = self.color_edit.text()
            use_pattern = self.pattern_check.isChecked()
            pattern_name = self.pattern_combo.currentData() if use_pattern else None
            if use_pattern and not pattern_name:
                raise ValueError("사용할 픽셀 패턴을 선택하세요.")
            if use_pattern:
                color = None
            else:
                # 변수 참조(/, ${}, @)는 값 검증 없이 raw로 저장하고 런타임에 resolver로 해석하도록 한다.
                if any(color_text.strip().startswith(prefix) for prefix in ("/", "$", "@")):
                    color = None
                else:
                    color = _parse_hex_color(color_text, resolver=self._resolver)
            pixel_exists = bool(self.pixel_expect_combo.currentData()) if self.pixel_expect_combo.currentIndex() >= 0 else True
            min_count = max(1, int(self.pixel_min_spin.value()))
            return Condition(
                type="pixel",
                name=name,
                region=region,
                region_raw=region_text,
                color=color,
                color_raw=color_text if not use_pattern else None,
                pixel_pattern=str(pattern_name) if use_pattern else None,
                tolerance=int(self.tol_spin.value()),
                pixel_min_count=min_count if not use_pattern else 1,
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
            use_pattern = self.pattern_check.isChecked()
            color = None if use_pattern else _parse_hex_color(self.color_edit.text(), resolver=self._resolver)
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
            "pattern": self.pattern_combo.currentData() if use_pattern else None,
            "tolerance": tolerance,
            "expect_exists": expect_exists,
            "min_count": 1 if use_pattern else max(1, int(self.pixel_min_spin.value())),
            "label": self.name_edit.text().strip() or "조건 테스트",
        }
        self._open_debugger_fn(config)
    def closeEvent(self, event: QtGui.QCloseEvent):
        try:
            cur = self.list_widget.currentItem()
            if cur:
                self._current_name = cur.text()
            self._save_current_pattern(name_hint=self._current_name)
        except Exception:
            pass
        return super().closeEvent(event)
    def _install_var_completer(self, edit: QtWidgets.QLineEdit, category: str):
        if not self._variable_provider:
            return
        names = self._variable_provider(category)
        _attach_variable_completer(edit, names)
    def _reload_patterns(self):
        self.pattern_combo.clear()
        self.pattern_combo.addItem("선택 안 함", None)
        names = []
        if callable(self._pattern_provider):
            try:
                names = self._pattern_provider() or []
            except Exception:
                names = []
        for name in names:
            self.pattern_combo.addItem(str(name), str(name))
    def _open_pattern_manager_cb(self):
        if callable(self._open_pattern_manager):
            try:
                self._open_pattern_manager(parent=self)
            except Exception:
                pass
        self._reload_patterns()
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
        # 다중 선택 이동: Qt 기본 InternalMove 는 현재 아이템만 옮기므로 직접 처리
        selected = self._top_level_selected(self.selectedItems())
        if event.source() is self and event.dropAction() == QtCore.Qt.DropAction.MoveAction and len(selected) > 1:
            pos = event.position().toPoint() if hasattr(event, "position") else event.pos()
            target = self.itemAt(pos)
            indicator = self.dropIndicatorPosition()

            # 선택 항목 내부나 자식으로 드롭하려면 무시
            if target and any(target is it or self._is_descendant(target, it) for it in selected):
                event.ignore()
                return

            # 드롭 위치(parent, row) 계산
            if indicator == QtWidgets.QAbstractItemView.DropIndicatorPosition.OnItem and target:
                parent = target
                row = target.childCount()
            elif indicator == QtWidgets.QAbstractItemView.DropIndicatorPosition.AboveItem and target:
                parent = target.parent()
                row = parent.indexOfChild(target) if parent else self.indexOfTopLevelItem(target)
            elif indicator == QtWidgets.QAbstractItemView.DropIndicatorPosition.BelowItem and target:
                parent = target.parent()
                row = (parent.indexOfChild(target) if parent else self.indexOfTopLevelItem(target)) + 1
            else:  # OnViewport 또는 대상 없음 -> 최상위 마지막
                parent = None
                row = self.topLevelItemCount()

            # 원래 위치 기록 후 분리
            orig_info = []
            for it in selected:
                p = it.parent()
                idx = p.indexOfChild(it) if p else self.indexOfTopLevelItem(it)
                orig_info.append((it, p, idx))
            # 삽입 위치 보정: 같은 부모에서 위쪽 아이템을 들어내면 row 가 앞으로 당겨진다.
            removed_above = sum(1 for _, p, idx in orig_info if p is parent and idx < row)
            row -= removed_above

            for it, p, _ in orig_info:
                if p:
                    p.takeChild(p.indexOfChild(it))
                else:
                    self.takeTopLevelItem(self.indexOfTopLevelItem(it))

            for offset, (it, p, _) in enumerate(orig_info):
                if parent:
                    parent.insertChild(row + offset, it)
                else:
                    self.insertTopLevelItem(row + offset, it)

            event.accept()
            if self._drop_callback:
                self._drop_callback()
            return

            # 기본 동작 (단일 항목 이동 등)
        # OnItem 드롭을 모든 조건/브랜치에 허용해 하위로 넣을 수 있게 한다.
        super().dropEvent(event)
        if self._drop_callback:
            self._drop_callback()
    def _item_path_key(self, item: QtWidgets.QTreeWidgetItem) -> tuple[int, ...]:
        path: list[int] = []
        current = item
        while current:
            parent = current.parent()
            row = parent.indexOfChild(current) if parent else self.indexOfTopLevelItem(current)
            path.append(row)
            current = parent
        return tuple(reversed(path))
    def _is_descendant(self, item: QtWidgets.QTreeWidgetItem, ancestor: QtWidgets.QTreeWidgetItem) -> bool:
        parent = item.parent()
        while parent:
            if parent is ancestor:
                return True
            parent = parent.parent()
        return False
    def _top_level_selected(self, items: List[QtWidgets.QTreeWidgetItem]) -> List[QtWidgets.QTreeWidgetItem]:
        """Return selected items without their descendants (ordered by tree path)."""
        result: List[QtWidgets.QTreeWidgetItem] = []
        for it in items:
            if any(self._is_descendant(it, other) for other in items if other is not it):
                continue
            result.append(it)
        return sorted(result, key=self._item_path_key)
class ConditionDialog(QtWidgets.QDialog):
    _condition_clipboard: list[Condition] | None = None
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
        pattern_provider=None,
        open_pattern_manager=None,
        trigger_keys_provider=None,
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
        self._viewer_image_provider = None
        self._pattern_provider = pattern_provider
        self._open_pattern_manager = open_pattern_manager
        self._trigger_keys_provider = trigger_keys_provider
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
        self._viewer_status_hint = "F1=좌표, Ctrl+F1=범위, F2=색상, F3=패턴포인트, F5=새로고침, Delete=삭제"
        self.viewer_status = QtWidgets.QLabel(self._viewer_status_hint)
        self.viewer_status.setStyleSheet("color: gray;")
        last_dir = self._image_viewer_state.get("last_dir") if isinstance(self._image_viewer_state, dict) else None
        self._refresh_viewer_status_label(last_dir)
        viewer_row.addWidget(self.viewer_btn)
        viewer_row.addWidget(self.debug_test_btn)
        viewer_row.addWidget(self.viewer_status, 1)
        layout.addLayout(viewer_row)
        cond_group = QtWidgets.QGroupBox("조건 트리 (최상위 OR, AND로 묶기)")
        cond_group_layout = QtWidgets.QVBoxLayout(cond_group)
        self.condition_tree = ConditionTreeWidget()
        self.condition_tree.setHeaderLabels(["타입", "이름", "요약", "활성"])
        self.condition_tree.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectionBehavior.SelectRows)
        # PyQt6 이름 변경: ExtendedSelection 이 올바른 상수
        self.condition_tree.setSelectionMode(QtWidgets.QAbstractItemView.SelectionMode.ExtendedSelection)
        self.condition_tree.set_drop_callback(self._sync_condition_from_tree)
        self.condition_tree.itemChanged.connect(self._on_item_changed)
        self.condition_tree.setColumnWidth(1, 140)
        header = self.condition_tree.header()
        header.setStretchLastSection(False)
        header.setSectionResizeMode(0, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(2, QtWidgets.QHeaderView.ResizeMode.Stretch)
        checkbox_w = self.style().pixelMetric(QtWidgets.QStyle.PixelMetric.PM_IndicatorWidth)
        self.condition_tree.setColumnWidth(3, max(checkbox_w + 10, 28))
        header.setSectionResizeMode(3, QtWidgets.QHeaderView.ResizeMode.Interactive)
        cond_group_layout.addWidget(self.condition_tree)
        tree_btn_row = QtWidgets.QHBoxLayout()
        self.add_node_btn = QtWidgets.QPushButton("조건 추가")
        self.add_group_btn = QtWidgets.QPushButton("그룹 추가 (AND/OR)")
        self.add_true_child_btn = QtWidgets.QPushButton("참일 때 하위")
        self.add_false_child_btn = QtWidgets.QPushButton("거짓일 때 하위")
        self.edit_node_btn = QtWidgets.QPushButton("선택 편집")
        self.copy_node_btn = QtWidgets.QPushButton("복사")
        self.paste_node_btn = QtWidgets.QPushButton("붙여넣기")
        self.clone_node_btn = QtWidgets.QPushButton("복제")
        self.delete_node_btn = QtWidgets.QPushButton("선택 삭제")
        tree_btn_row.addWidget(self.add_node_btn)
        tree_btn_row.addWidget(self.add_group_btn)
        tree_btn_row.addWidget(self.add_true_child_btn)
        tree_btn_row.addWidget(self.add_false_child_btn)
        tree_btn_row.addWidget(self.edit_node_btn)
        tree_btn_row.addWidget(self.copy_node_btn)
        tree_btn_row.addWidget(self.paste_node_btn)
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
        self.copy_node_btn.clicked.connect(self._copy_condition_nodes)
        self.paste_node_btn.clicked.connect(self._paste_condition_nodes)
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
    def _pattern_names(self) -> list[str]:
        if callable(self._pattern_provider):
            try:
                return self._pattern_provider() or []
            except Exception:
                return []
        return []
    def _load(self, cond: MacroCondition):
        self.cond_name_edit.setText(cond.name or "")
        self.root_condition = copy.deepcopy(cond.condition)
        self._refresh_condition_tree()
    def _append_condition_item(self, cond: Condition, parent_item=None):
        enabled_flag = getattr(cond, "enabled", True)
        try:
            setattr(cond, "enabled", enabled_flag)
        except Exception:
            pass
        item = QtWidgets.QTreeWidgetItem([_condition_type_label(cond.type), cond.name or "", _condition_brief(cond), ""])
        item.setData(0, QtCore.Qt.ItemDataRole.UserRole, cond)
        color_hex = _condition_hex_color(cond)
        if color_hex:
            item.setIcon(2, _make_hex_chip_icon(color_hex))
        flags = item.flags()
        flags |= (
            QtCore.Qt.ItemFlag.ItemIsDragEnabled
            | QtCore.Qt.ItemFlag.ItemIsEnabled
            | QtCore.Qt.ItemFlag.ItemIsSelectable
            | QtCore.Qt.ItemFlag.ItemIsUserCheckable
        )
        flags |= QtCore.Qt.ItemFlag.ItemIsDropEnabled
        item.setFlags(flags)
        item.setCheckState(3, QtCore.Qt.CheckState.Checked if enabled_flag else QtCore.Qt.CheckState.Unchecked)
        if parent_item:
            parent_item.addChild(item)
        else:
            self.condition_tree.addTopLevelItem(item)
        if cond.type in ("all", "any"):
            for child in cond.conditions:
                self._append_condition_item(child, item)
        if cond.on_true:
            true_header = QtWidgets.QTreeWidgetItem(["참일 때", "", f"{len(cond.on_true)}개", ""])
            true_header.setData(0, QtCore.Qt.ItemDataRole.UserRole, "branch_true")
            true_header.setFlags(QtCore.Qt.ItemFlag.ItemIsEnabled | QtCore.Qt.ItemFlag.ItemIsDropEnabled | QtCore.Qt.ItemFlag.ItemIsSelectable)
            item.addChild(true_header)
            for child in cond.on_true:
                self._append_condition_item(child, true_header)
        if cond.on_false:
            false_header = QtWidgets.QTreeWidgetItem(["거짓일 때", "", f"{len(cond.on_false)}개", ""])
            false_header.setData(0, QtCore.Qt.ItemDataRole.UserRole, "branch_false")
            false_header.setFlags(QtCore.Qt.ItemFlag.ItemIsEnabled | QtCore.Qt.ItemFlag.ItemIsDropEnabled | QtCore.Qt.ItemFlag.ItemIsSelectable)
            item.addChild(false_header)
            for child in cond.on_false:
                self._append_condition_item(child, false_header)
        return item
    def _refresh_condition_tree(self):
        prev_block = self.condition_tree.blockSignals(True)
        try:
            self.condition_tree.clear()
            if not self.root_condition or (self.root_condition.type == "any" and not self.root_condition.conditions):
                placeholder = QtWidgets.QTreeWidgetItem(["(조건 없음)", "", "추가 버튼으로 루트를 만드세요.", ""])
                placeholder.setFlags(QtCore.Qt.ItemFlag.NoItemFlags)
                self.condition_tree.addTopLevelItem(placeholder)
            else:
                if self.root_condition.type == "any":
                    for child in self.root_condition.conditions:
                        self._append_condition_item(child)
                else:
                    self._append_condition_item(self.root_condition)
                self._expand_condition_tree()
                self._restart_condition_debug_if_running()
        finally:
            self.condition_tree.blockSignals(prev_block)
        self._apply_enabled_styles()
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
    def _item_enabled_state(self, item: QtWidgets.QTreeWidgetItem | None) -> bool:
        if not item:
            return True
        if item.flags() & QtCore.Qt.ItemFlag.ItemIsUserCheckable:
            return item.checkState(3) == QtCore.Qt.CheckState.Checked
        return True
    def _apply_enabled_styles(self):
        default_brush = QtGui.QBrush(self.condition_tree.palette().color(QtGui.QPalette.ColorRole.Text))
        disabled_brush = QtGui.QBrush(QtGui.QColor("#9aa0a6"))
        def walk(item: QtWidgets.QTreeWidgetItem | None, parent_disabled: bool = False):
            if not item:
                return
            data = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
            is_disabled = parent_disabled
            if isinstance(data, Condition):
                is_disabled = is_disabled or (not self._item_enabled_state(item))
            brush = disabled_brush if is_disabled else default_brush
            for col in range(item.columnCount()):
                item.setForeground(col, brush)
            for idx in range(item.childCount()):
                walk(item.child(idx), is_disabled)
        for i in range(self.condition_tree.topLevelItemCount()):
            walk(self.condition_tree.topLevelItem(i), False)
    def _on_item_changed(self, item: QtWidgets.QTreeWidgetItem, column: int):
        if column != 3:
            return
        data = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
        if isinstance(data, Condition):
            data.enabled = self._item_enabled_state(item)
        self._apply_enabled_styles()
    def _condition_from_item(self, item: QtWidgets.QTreeWidgetItem) -> Condition | None:
        cond = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
        if not isinstance(cond, Condition):
            return None
        cond.conditions = []
        cond.on_true = []
        cond.on_false = []
        try:
            cond.enabled = self._item_enabled_state(item)
        except Exception:
            pass
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

    def _find_container_info(self, target: Condition) -> tuple[list[Condition], int, Condition | None] | None:
        if not self.root_condition or target is self.root_condition:
            return None

        def walk(parent: Condition) -> tuple[list[Condition], int, Condition] | None:
            for child_list in (parent.conditions, parent.on_true, parent.on_false):
                for idx, child in enumerate(child_list):
                    if child is target:
                        return child_list, idx, parent
                    found = walk(child)
                    if found:
                        return found
            return None

        return walk(self.root_condition)
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
            pattern_provider=self._pattern_names,
            open_pattern_manager=self._open_pattern_manager,
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
            pattern_provider=self._pattern_names,
            open_pattern_manager=self._open_pattern_manager,
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
            pattern_provider=self._pattern_names,
            open_pattern_manager=self._open_pattern_manager,
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
    def _insert_conditions_into_list(self, lst: list[Condition], start_index: int, new_conds: list[Condition]) -> list[Condition]:
        idx = max(0, start_index)
        inserted: list[Condition] = []
        for cond in new_conds:
            lst.insert(idx, cond)
            inserted.append(cond)
            idx += 1
        return inserted

    def _select_conditions_in_tree(self, conds: list[Condition]):
        self.condition_tree.clearSelection()
        first_item = None
        for cond in conds:
            item = self._find_item_for_condition(cond)
            if item:
                item.setSelected(True)
                if first_item is None:
                    first_item = item
        if first_item:
            self.condition_tree.setCurrentItem(first_item)

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
    def _copy_condition_nodes(self):
        items = self.condition_tree._top_level_selected(self.condition_tree.selectedItems())
        if not items:
            QtWidgets.QMessageBox.information(self, "선택 없음", "복사할 조건을 선택하세요.")
            return
        copied: list[Condition] = []
        for item in items:
            cond = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
            if isinstance(cond, Condition):
                copied.append(copy.deepcopy(cond))
        if not copied:
            QtWidgets.QMessageBox.information(self, "선택 없음", "조건을 선택하세요.")
            return
        ConditionDialog._condition_clipboard = copied

    def _paste_condition_nodes(self):
        if not ConditionDialog._condition_clipboard:
            QtWidgets.QMessageBox.information(self, "복사본 없음", "먼저 조건을 복사하세요.")
            return
        new_conds = [copy.deepcopy(cond) for cond in ConditionDialog._condition_clipboard]
        branch_marker = self._selected_branch_marker()
        target_cond = self._selected_condition()
        inserted: list[Condition] = []
        if not self.root_condition:
            if len(new_conds) == 1:
                self.root_condition = new_conds[0]
            else:
                self.root_condition = Condition(type="any", conditions=new_conds)
            inserted = new_conds
        elif branch_marker and target_cond:
            dest = target_cond.on_true if branch_marker == "branch_true" else target_cond.on_false
            inserted = self._insert_conditions_into_list(dest, len(dest), new_conds)
        elif target_cond:
            container = self._find_container_info(target_cond)
            if container:
                lst, idx, _parent = container
                inserted = self._insert_conditions_into_list(lst, idx + 1, new_conds)
            elif target_cond.type in ("all", "any"):
                inserted = self._insert_conditions_into_list(target_cond.conditions, len(target_cond.conditions), new_conds)
            else:
                self.root_condition = Condition(type="any", conditions=[self.root_condition] + new_conds)
                inserted = new_conds
        else:
            if self.root_condition.type == "any":
                inserted = self._insert_conditions_into_list(self.root_condition.conditions, len(self.root_condition.conditions), new_conds)
            else:
                self.root_condition = Condition(type="any", conditions=[self.root_condition] + new_conds)
                inserted = new_conds
        self._refresh_condition_tree()
        self._expand_condition_tree()
        self._select_conditions_in_tree(inserted)

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
            pattern_provider=self._pattern_names,
            open_pattern_manager=self._open_pattern_manager,
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
            new_cond.enabled = getattr(current_cond, "enabled", True)
            new_cond.on_true = copy.deepcopy(getattr(current_cond, "on_true", []))
            new_cond.on_false = copy.deepcopy(getattr(current_cond, "on_false", []))
            self._replace_condition(current_cond, new_cond)
            self._refresh_condition_tree()
    def _delete_condition_node(self):
        items = self.condition_tree._top_level_selected(self.condition_tree.selectedItems())
        if not items:
            QtWidgets.QMessageBox.information(self, "선택 없음", "삭제할 조건을 선택하세요.")
            return

        count = len(items)
        reply = QtWidgets.QMessageBox.question(
            self,
            "삭제 확인",
            f"선택한 조건 {count}개를 삭제할까요?",
            QtWidgets.QMessageBox.StandardButton.Yes | QtWidgets.QMessageBox.StandardButton.No,
        )
        if reply != QtWidgets.QMessageBox.StandardButton.Yes:
            return

        for item in reversed(items):
            cond = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
            if cond is self.root_condition:
                self.root_condition = None
                continue
            info = self._find_container_info(cond)
            if not info:
                continue
            lst, idx, _parent = info
            if 0 <= idx < len(lst):
                lst.pop(idx)

        self._refresh_condition_tree()
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
        name = self.cond_name_edit.text().strip() or None
        try:
            setattr(root_copy, "name", name)
        except Exception:
            pass
        return MacroCondition(
            condition=root_copy,
            actions=[],
            else_actions=[],
            name=name,
        )
    def _condition_debug_payload(self) -> dict:
        macro_cond = self.get_condition()
        return {
            "macro_condition": macro_cond,
            "condition": macro_cond.condition,
            "resolver": self._resolver,
            "vars_ctx": getattr(self._resolver, "vars", None) if self._resolver else None,
            "label": macro_cond.name or "조건 디버그",
            "image_provider": self._viewer_image_provider if callable(self._viewer_image_provider) else None,
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
    def _refresh_viewer_status_label(self, last_dir: str | None = None):
        base_dir = last_dir or self._image_viewer_state.get("last_dir")
        text = f"최근 폴더: {base_dir}" if base_dir else self._viewer_status_hint
        self.viewer_status.setText(text)
    def set_viewer_debug_source(self, *, enabled: bool, provider=None):
        self._viewer_image_provider = provider if callable(provider) else None
        self._refresh_viewer_status_label()
        self._restart_condition_debug_if_running()
    def notify_viewer_image_changed(self):
        self._restart_condition_debug_if_running()
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
        self._refresh_viewer_status_label(self._image_viewer_state.get("last_dir"))
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
    imageChanged = QtCore.pyqtSignal()
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
        self._overlays: list[tuple[int, int, int, int]] = []
        self._region_select_active = False
        self._region_select_start: QtCore.QPoint | None = None
        self._region_select_rect: tuple[int, int, int, int] | None = None
        self._region_select_cb = None
    def clear_image(self):
        self._image = None
        self._pixmap = None
        self._sample = None
        self._region_select_active = False
        self._region_select_start = None
        self._region_select_rect = None
        self._region_select_cb = None
        self._draw_rect = QtCore.QRectF()
        self._last_mouse_pos = None
        self._user_zoom = 1.0
        self._view_center = QtCore.QPointF(0, 0)
        self.update()
        self.sampleChanged.emit(None)
        self.zoomChanged.emit(self._user_zoom)
        self.imageChanged.emit()
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
        self.imageChanged.emit()
        return True
    def set_overlays(self, rects: list[tuple[int, int, int, int] | tuple[int, int, int, int, object]] | None):
        # rect: (x, y, w, h[, color])
        self._overlays = rects or []
        self.update()
    def begin_region_selection(self, callback=None) -> bool:
        if not self._image:
            return False
        self._region_select_active = True
        self._region_select_start = None
        self._region_select_rect = None
        self._region_select_cb = callback
        self.update()
        return True
    def cancel_region_selection(self):
        if not self._region_select_active:
            return
        self._region_select_active = False
        self._region_select_start = None
        self._region_select_rect = None
        self._region_select_cb = None
        self.update()
    def is_region_selecting(self) -> bool:
        return bool(self._region_select_active)
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
    def _event_image_pos(self, event: QtGui.QMouseEvent) -> tuple[int, int] | None:
        if not self._image:
            return None
        pos = event.position().toPoint() if hasattr(event, "position") else event.pos()
        self._last_mouse_pos = pos
        img_pt = self._widget_to_image(QtCore.QPointF(pos))
        if img_pt is None:
            return None
        x = int(img_pt.x())
        y = int(img_pt.y())
        x = max(0, min(self._image.width() - 1, x))
        y = max(0, min(self._image.height() - 1, y))
        return x, y
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
        # overlays in image coordinates -> convert to widget coords
        if self._overlays and self._image and not self._draw_rect.isNull() and self._scale > 0:
            painter.setBrush(QtCore.Qt.BrushStyle.NoBrush)
            for rect in self._overlays:
                if len(rect) >= 5:
                    ox, oy, ow, oh, color = rect[:5]
                else:
                    ox, oy, ow, oh = rect
                    color = QtGui.QColor(255, 80, 80)
                try:
                    qcolor = color if isinstance(color, QtGui.QColor) else QtGui.QColor(*color) if isinstance(color, (list, tuple)) else QtGui.QColor(str(color))
                    if not qcolor.isValid():
                        qcolor = QtGui.QColor(255, 80, 80)
                except Exception:
                    qcolor = QtGui.QColor(255, 80, 80)
                pen = QtGui.QPen(qcolor, 2)
                pen.setCosmetic(True)
                painter.setPen(pen)
                wx = self._draw_rect.left() + ox * self._scale
                wy = self._draw_rect.top() + oy * self._scale
                painter.drawRect(QtCore.QRectF(wx, wy, ow * self._scale, oh * self._scale))
        if self._region_select_rect and self._image and not self._draw_rect.isNull() and self._scale > 0:
            x, y, w, h = self._region_select_rect
            pen = QtGui.QPen(QtGui.QColor(90, 200, 255), 2, QtCore.Qt.PenStyle.DashLine)
            pen.setCosmetic(True)
            painter.setPen(pen)
            painter.setBrush(QtGui.QColor(90, 200, 255, 40))
            wx = self._draw_rect.left() + x * self._scale
            wy = self._draw_rect.top() + y * self._scale
            painter.drawRect(QtCore.QRectF(wx, wy, w * self._scale, h * self._scale))
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
        if self._region_select_active and self._region_select_start is not None:
            img_pos = self._event_image_pos(event)
            if img_pos:
                sx, sy = self._region_select_start.x(), self._region_select_start.y()
                ex, ey = img_pos
                x0, y0 = min(sx, ex), min(sy, ey)
                w = abs(ex - sx) + 1
                h = abs(ey - sy) + 1
                self._region_select_rect = (x0, y0, w, h)
                self.update()
        self._update_sample_from_pos()
        super().mouseMoveEvent(event)
    def leaveEvent(self, event: QtCore.QEvent):
        self._set_sample(None)
        super().leaveEvent(event)
    def mousePressEvent(self, event: QtGui.QMouseEvent):
        if self._region_select_active:
            if event.button() == QtCore.Qt.MouseButton.LeftButton:
                img_pos = self._event_image_pos(event)
                if img_pos:
                    self._region_select_start = QtCore.QPoint(*img_pos)
                    self._region_select_rect = (img_pos[0], img_pos[1], 1, 1)
                    self._update_sample_from_pos()
                    self.update()
                event.accept()
                return
            if event.button() == QtCore.Qt.MouseButton.RightButton:
                cb = self._region_select_cb
                self.cancel_region_selection()
                if cb:
                    try:
                        cb(None)
                    except Exception:
                        pass
                event.accept()
                return
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
        if event.button() == QtCore.Qt.MouseButton.RightButton:
            # 우클릭 무시 구간 (색상 복사/텍스트 없음)
            event.accept()
            return
        super().mousePressEvent(event)
    def mouseReleaseEvent(self, event: QtGui.QMouseEvent):
        if self._region_select_active and event.button() == QtCore.Qt.MouseButton.LeftButton:
            img_pos = self._event_image_pos(event)
            if img_pos and self._region_select_start is not None:
                sx, sy = self._region_select_start.x(), self._region_select_start.y()
                ex, ey = img_pos
                x0, y0 = min(sx, ex), min(sy, ey)
                w = abs(ex - sx) + 1
                h = abs(ey - sy) + 1
                self._region_select_rect = (x0, y0, w, h)
            region = self._region_select_rect
            cb = self._region_select_cb
            self.cancel_region_selection()
            if cb and region:
                try:
                    cb(region)
                except Exception:
                    pass
            event.accept()
            return
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
class _ImageFilterProxyModel(QtCore.QSortFilterProxyModel):
    def __init__(self, *, allow_exts: tuple[str, ...], parent=None):
        super().__init__(parent)
        self._allow_exts = tuple(e.lower() for e in allow_exts)
    def headerData(self, section: int, orientation: QtCore.Qt.Orientation, role: int = QtCore.Qt.ItemDataRole.DisplayRole):
        if role == QtCore.Qt.ItemDataRole.DisplayRole and orientation == QtCore.Qt.Orientation.Horizontal:
            if section == 2:
                return "형식"
        return super().headerData(section, orientation, role)
    def data(self, index: QtCore.QModelIndex, role: int = QtCore.Qt.ItemDataRole.DisplayRole):
        if role == QtCore.Qt.ItemDataRole.DisplayRole and index.column() == 2:
            try:
                src_idx = self.mapToSource(index)
                name = self.sourceModel().fileName(src_idx)
                ext = Path(name).suffix.upper().lstrip(".")
                return ext or "파일"
            except Exception:
                pass
        return super().data(index, role)
    def filterAcceptsRow(self, source_row: int, source_parent: QtCore.QModelIndex) -> bool:
        model = self.sourceModel()
        if model is None:
            return False
        idx = model.index(source_row, 0, source_parent)
        if not idx.isValid():
            return False
        if getattr(model, "isDir", lambda x: False)(idx):
            return True
        name = getattr(model, "fileName", lambda x: "")(idx).lower()
        return any(name.endswith(ext) for ext in self._allow_exts)
class _FileTreeView(QtWidgets.QTreeView):
    dropRequested = QtCore.pyqtSignal(list, Path, QtCore.Qt.DropAction)
    ctrlArrow = QtCore.pyqtSignal(int)
    deleteRequested = QtCore.pyqtSignal()
    refreshRequested = QtCore.pyqtSignal()
    def __init__(self, parent=None):
        super().__init__(parent)
        self._root_path = Path.cwd()
        self._path_resolver = None
        self.setUniformRowHeights(True)
        self.setHeaderHidden(False)
        self.setSelectionMode(QtWidgets.QAbstractItemView.SelectionMode.ExtendedSelection)
        self.setDragEnabled(True)
        self.setAcceptDrops(True)
        self.setDropIndicatorShown(True)
        self.setDragDropMode(QtWidgets.QAbstractItemView.DragDropMode.DragDrop)
        self.setDefaultDropAction(QtCore.Qt.DropAction.MoveAction)
        self.setIndentation(16)
        self.setExpandsOnDoubleClick(True)
    def set_root_path(self, root: Path):
        self._root_path = Path(root)
    def set_path_resolver(self, fn: Callable[[QtCore.QModelIndex], Path | None]):
        self._path_resolver = fn
    def keyPressEvent(self, event: QtGui.QKeyEvent):
        key = event.key()
        modifiers = event.modifiers()
        if key in (QtCore.Qt.Key.Key_Left, QtCore.Qt.Key.Key_Right) and (
            modifiers & QtCore.Qt.KeyboardModifier.ControlModifier
        ):
            delta = -1 if key == QtCore.Qt.Key.Key_Left else 1
            self.ctrlArrow.emit(delta)
            event.accept()
            return
        if key == QtCore.Qt.Key.Key_Delete:
            self.deleteRequested.emit()
            event.accept()
            return
        if key == QtCore.Qt.Key.Key_F5:
            self.refreshRequested.emit()
            event.accept()
            return
        super().keyPressEvent(event)
    def dragEnterEvent(self, event: QtGui.QDragEnterEvent):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()
            return
        super().dragEnterEvent(event)
    def dragMoveEvent(self, event: QtGui.QDragMoveEvent):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()
            return
        super().dragMoveEvent(event)
    def dropEvent(self, event: QtGui.QDropEvent):
        if not event.mimeData().hasUrls():
            return super().dropEvent(event)
        idx = self.indexAt(event.position().toPoint()) if hasattr(event, "position") else self.indexAt(event.pos())
        target_path = self._resolve_path(idx)
        urls = event.mimeData().urls()
        paths = [Path(u.toLocalFile()) for u in urls if u.isLocalFile()]
        if not paths:
            event.ignore()
            return
        copy_action = bool(event.keyboardModifiers() & QtCore.Qt.KeyboardModifier.ControlModifier)
        action = QtCore.Qt.DropAction.CopyAction if copy_action else QtCore.Qt.DropAction.MoveAction
        self.dropRequested.emit(paths, target_path, action)
        event.acceptProposedAction()
    def _resolve_path(self, idx: QtCore.QModelIndex) -> Path:
        if idx and idx.isValid() and callable(self._path_resolver):
            p = self._path_resolver(idx)
        else:
            p = None
        if p is None:
            return self._root_path
        return p if p.is_dir() else p.parent
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
        state = state or {}
        self._root_dir = self._validate_dir(Path(state.get("root_dir", start_dir)))
        self._current_folder = self._validate_dir(Path(state.get("last_dir", self._root_dir)))
        self._image_files: list[Path] = []
        self._current_index = -1
        self._last_sample = None
        self._focused_on_viewer = True
        self._status_prefix = ""
        self._pending_state: dict | None = None
        self._block_tree_selection = False
        self._auto_refresh_enabled = bool(state.get("auto_refresh"))
        self._debug_frame_cache_path: Path | None = None
        self._debug_frame_cache_mtime: float | None = None
        self._debug_frame_cache_frame: np.ndarray | None = None
        self._favorites = state.get("favorites") if isinstance(state, dict) else {}
        if not isinstance(self._favorites, dict):
            self._favorites = {}
        if not self._favorites:
            self._favorites = {"기본": []}
        self._current_fav_group = state.get("fav_group") if isinstance(state, dict) else None
        if not self._current_fav_group or self._current_fav_group not in self._favorites:
            self._current_fav_group = next(iter(self._favorites))
        self._last_file_in_state = state.get("last_file") if isinstance(state, dict) else None
        self._sort_column = int(state.get("sort_col", 3)) if isinstance(state, dict) else 3
        self._sort_order = (
            QtCore.Qt.SortOrder.DescendingOrder
            if state.get("sort_order", "desc") == "desc"
            else QtCore.Qt.SortOrder.AscendingOrder
            if isinstance(state, dict)
            else QtCore.Qt.SortOrder.DescendingOrder
        )
        self._build_ui()
        self.set_start_dir(self._current_folder, refresh=True)
        self._attach_capture_listener()
        self._notify_condition_window()
    def _build_ui(self):
        layout = QtWidgets.QVBoxLayout(self)
        layout.setContentsMargins(8, 8, 8, 8)
        layout.setSpacing(6)
        top = QtWidgets.QHBoxLayout()
        self.root_btn = QtWidgets.QPushButton("루트 변경")
        self.open_folder_btn = QtWidgets.QPushButton("탐색기에서 열기")
        self.refresh_btn = QtWidgets.QPushButton("새로고침")
        self.delete_btn = QtWidgets.QPushButton("선택 삭제")
        self.delete_all_btn = QtWidgets.QPushButton("폴더 비우기")
        self.auto_refresh_chk = QtWidgets.QCheckBox("단일 캡처 후 새로고침")
        self.region_select_btn = QtWidgets.QPushButton("범위 선택")
        self.screenshot_btn = QtWidgets.QPushButton("스크린샷")
        self.close_btn = QtWidgets.QPushButton("종료")
        top.addWidget(self.root_btn)
        top.addWidget(self.open_folder_btn)
        top.addWidget(self.refresh_btn)
        top.addWidget(self.delete_btn)
        top.addWidget(self.delete_all_btn)
        top.addWidget(self.auto_refresh_chk)
        top.addStretch(1)
        top.addWidget(self.region_select_btn)
        top.addWidget(self.screenshot_btn)
        top.addWidget(self.close_btn)
        layout.addLayout(top)
        splitter = QtWidgets.QSplitter(QtCore.Qt.Orientation.Horizontal)
        layout.addWidget(splitter, 1)
        # 좌측: 즐겨찾기 + 파일 트리
        sidebar = QtWidgets.QWidget()
        side_layout = QtWidgets.QVBoxLayout(sidebar)
        side_layout.setContentsMargins(0, 0, 0, 0)
        side_layout.setSpacing(6)
        root_row = QtWidgets.QHBoxLayout()
        root_row.setContentsMargins(0, 0, 0, 0)
        root_row.setSpacing(6)
        root_row.addWidget(QtWidgets.QLabel("루트"))
        self.root_label = QtWidgets.QLabel(str(self._root_dir))
        self.root_label.setTextInteractionFlags(QtCore.Qt.TextInteractionFlag.TextSelectableByMouse)
        root_row.addWidget(self.root_label, 1)
        side_layout.addLayout(root_row)
        fav_box = QtWidgets.QGroupBox("즐겨찾기")
        fav_layout = QtWidgets.QVBoxLayout(fav_box)
        fav_layout.setContentsMargins(6, 6, 6, 6)
        fav_layout.setSpacing(6)
        fav_btns = QtWidgets.QHBoxLayout()
        fav_btns.setSpacing(4)
        self.add_group_btn = QtWidgets.QPushButton("그룹 추가")
        self.remove_group_btn = QtWidgets.QPushButton("그룹 삭제")
        self.add_fav_btn = QtWidgets.QPushButton("현재 추가")
        self.remove_fav_btn = QtWidgets.QPushButton("삭제")
        fav_btns.addWidget(self.add_group_btn)
        fav_btns.addWidget(self.remove_group_btn)
        fav_btns.addWidget(self.add_fav_btn)
        fav_btns.addWidget(self.remove_fav_btn)
        fav_layout.addLayout(fav_btns)
        self.fav_tree = QtWidgets.QTreeWidget()
        self.fav_tree.setHeaderHidden(True)
        self.fav_tree.setIndentation(14)
        self.fav_tree.setUniformRowHeights(True)
        self.fav_tree.setSelectionMode(QtWidgets.QAbstractItemView.SelectionMode.SingleSelection)
        fav_layout.addWidget(self.fav_tree, 1)
        side_layout.addWidget(fav_box)
        self.file_tree = _FileTreeView()
        side_layout.addWidget(self.file_tree, 1)
        splitter.addWidget(sidebar)
        # 우측: 뷰어
        right = QtWidgets.QWidget()
        right_layout = QtWidgets.QVBoxLayout(right)
        right_layout.setContentsMargins(0, 0, 0, 0)
        right_layout.setSpacing(6)
        self.path_label = QtWidgets.QLabel("")
        self.path_label.setTextInteractionFlags(QtCore.Qt.TextInteractionFlag.TextSelectableByMouse)
        self.hud_label = QtWidgets.QLabel("")
        self.hud_label.setStyleSheet("color: #d9e7ff; background: rgba(30,40,60,0.6); padding: 4px;")
        self.path_label.setStyleSheet("color: #9fb2cc;")
        right_layout.addWidget(self.path_label)
        right_layout.addWidget(self.hud_label)
        self.canvas = _ImageCanvas()
        self.canvas.setFocusPolicy(QtCore.Qt.FocusPolicy.StrongFocus)
        right_layout.addWidget(self.canvas, 1)
        self.status_label = QtWidgets.QLabel("스크린샷 폴더 이미지를 선택하세요.")
        self.status_label.setStyleSheet("color: #b5c2d6;")
        right_layout.addWidget(self.status_label)
        splitter.addWidget(right)
        splitter.setStretchFactor(0, 0)
        splitter.setStretchFactor(1, 1)
        splitter.setSizes([320, 900])
        # 파일 모델/트리 연결
        self._fs_model = QtGui.QFileSystemModel(self)
        self._fs_model.setReadOnly(False)
        self._fs_model.setNameFilterDisables(False)
        self._fs_model.setFilter(
            QtCore.QDir.Filter.AllDirs | QtCore.QDir.Filter.NoDotAndDotDot | QtCore.QDir.Filter.Files
        )
        self._fs_model.setHeaderData(0, QtCore.Qt.Orientation.Horizontal, "이름")
        self._fs_model.setHeaderData(1, QtCore.Qt.Orientation.Horizontal, "크기")
        self._fs_model.setHeaderData(2, QtCore.Qt.Orientation.Horizontal, "형식")
        self._fs_model.setHeaderData(3, QtCore.Qt.Orientation.Horizontal, "수정 시각")
        self._proxy_model = _ImageFilterProxyModel(allow_exts=(".png", ".jpg", ".jpeg", ".bmp"), parent=self)
        self._proxy_model.setSourceModel(self._fs_model)
        self.file_tree.setModel(self._proxy_model)
        self.file_tree.set_path_resolver(self._path_from_index)
        self.file_tree.set_root_path(self._root_dir)
        header = self.file_tree.header()
        header.setSectionsClickable(True)
        header.setStretchLastSection(False)
        header.setSectionResizeMode(0, QtWidgets.QHeaderView.ResizeMode.Stretch)
        header.setSectionResizeMode(2, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(3, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        self.file_tree.hideColumn(1)  # 크기 숨김
        self.file_tree.setSortingEnabled(True)
        # 시그널 연결
        self.root_btn.clicked.connect(self._choose_root)
        self.open_folder_btn.clicked.connect(self._open_current_folder)
        self.refresh_btn.clicked.connect(self._refresh_folder)
        self.delete_btn.clicked.connect(self._delete_selection)
        self.delete_all_btn.clicked.connect(self._delete_all_in_folder)
        self.auto_refresh_chk.setChecked(self._auto_refresh_enabled)
        self.auto_refresh_chk.toggled.connect(self._persist_state)
        self.region_select_btn.clicked.connect(self._start_region_selection)
        self.screenshot_btn.clicked.connect(self._open_screenshot)
        self.close_btn.clicked.connect(self.close)
        self.canvas.sampleChanged.connect(self._on_sample_changed)
        self.canvas.zoomChanged.connect(self._on_zoom_changed)
        self.add_group_btn.clicked.connect(self._add_favorite_group)
        self.remove_group_btn.clicked.connect(self._remove_favorite_group)
        self.add_fav_btn.clicked.connect(self._add_current_to_favorites)
        self.remove_fav_btn.clicked.connect(self._remove_selected_favorite)
        self.fav_tree.itemDoubleClicked.connect(self._on_favorite_double_clicked)
        self.file_tree.dropRequested.connect(self._handle_drop)
        self.file_tree.ctrlArrow.connect(self._on_tree_ctrl_arrow)
        self.file_tree.deleteRequested.connect(self._delete_selection)
        self.file_tree.refreshRequested.connect(self._refresh_folder)
        self.file_tree.doubleClicked.connect(self._on_tree_double_clicked)
        self.file_tree.selectionModel().selectionChanged.connect(self._on_tree_selection_changed)
        header.sortIndicatorChanged.connect(self._on_sort_indicator_changed)
        self._set_tree_root(self._root_dir)
        self._apply_sort()
        self._refresh_favorites_tree()
        if not callable(self._open_screenshot_dialog):
            self.screenshot_btn.setEnabled(False)
        self._update_hud_text()
        QtGui.QShortcut(
            QtGui.QKeySequence("Ctrl+F1"),
            self,
            self._start_region_selection,
            context=QtCore.Qt.ShortcutContext.ApplicationShortcut,
        )
    def _validate_dir(self, path: Path) -> Path:
        try:
            p = Path(path)
        except Exception:
            p = SCREENSHOT_DIR
        if p.is_file():
            p = p.parent
        if not p.exists():
            p = SCREENSHOT_DIR
        return p
    def _is_under_root(self, path: Path) -> bool:
        try:
            return Path(path).resolve().is_relative_to(self._root_dir.resolve())
        except Exception:
            try:
                return str(Path(path).resolve()).lower().startswith(str(self._root_dir.resolve()).lower())
            except Exception:
                return False
    def _is_image_file(self, path: Path) -> bool:
        return path.is_file() and path.suffix.lower() in {".png", ".jpg", ".jpeg", ".bmp"}
    def _set_tree_root(self, path: Path):
        root = self._validate_dir(path)
        self._root_dir = root
        self.root_label.setText(str(root))
        try:
            src_root = self._fs_model.setRootPath(str(root))
            proxy_root = self._proxy_model.mapFromSource(src_root)
            self.file_tree.set_root_path(root)
            self.file_tree.setRootIndex(proxy_root)
        except Exception:
            pass
        self._apply_sort()
    def _path_from_index(self, proxy_idx: QtCore.QModelIndex) -> Path | None:
        if not proxy_idx or not proxy_idx.isValid():
            return None
        try:
            src_idx = self._proxy_model.mapToSource(proxy_idx)
            return Path(self._fs_model.filePath(src_idx))
        except Exception:
            return None
    def _index_for_path(self, path: Path) -> QtCore.QModelIndex:
        try:
            src_idx = self._fs_model.index(str(path))
            if not src_idx.isValid():
                return QtCore.QModelIndex()
            return self._proxy_model.mapFromSource(src_idx)
        except Exception:
            return QtCore.QModelIndex()
    def _select_tree_path(self, path: Path):
        idx = self._index_for_path(path)
        if not idx.isValid() or not self.file_tree.selectionModel():
            return
        self._block_tree_selection = True
        try:
            sel = QtCore.QItemSelection(idx, idx)
            self.file_tree.selectionModel().select(
                sel,
                QtCore.QItemSelectionModel.SelectionFlag.ClearAndSelect
                | QtCore.QItemSelectionModel.SelectionFlag.Rows,
            )
            self.file_tree.selectionModel().setCurrentIndex(
                idx,
                QtCore.QItemSelectionModel.SelectionFlag.ClearAndSelect
                | QtCore.QItemSelectionModel.SelectionFlag.Rows,
            )
            self.file_tree.scrollTo(idx, QtWidgets.QAbstractItemView.ScrollHint.PositionAtCenter)
        except Exception:
            pass
        self._block_tree_selection = False
    def _set_current_folder(self, folder: Path, *, refresh: bool = False, auto_select_first: bool = False):
        folder = self._validate_dir(folder)
        need_refresh = refresh or folder != self._current_folder
        self._current_folder = folder
        self._update_path_label()
        self._load_folder(folder, auto_select_first=auto_select_first or need_refresh)
        self._select_tree_path(folder)
        self._persist_state()
    def _select_file(self, path: Path):
        if not path or not path.exists() or not self._is_image_file(path):
            return
        parent = path.parent
        if parent != self._current_folder:
            self._set_current_folder(parent, refresh=True)
        try:
            idx = self._image_files.index(path)
        except ValueError:
            self._load_folder(parent, auto_select_first=False)
            try:
                idx = self._image_files.index(path)
            except ValueError:
                return
        self._select_index(idx)
    def _current_file(self) -> Path | None:
        if 0 <= self._current_index < len(self._image_files):
            return self._image_files[self._current_index]
        return None
    def _persist_state(self):
        data = {
            "last_dir": str(self._current_folder),
            "root_dir": str(self._root_dir),
            "auto_refresh": bool(self.auto_refresh_chk.isChecked()),
            "favorites": self._favorites,
            "fav_group": self._current_fav_group,
            "last_file": str(self._current_file()) if self._current_file() else None,
            "sort_col": self._sort_column,
            "sort_order": "desc" if self._sort_order == QtCore.Qt.SortOrder.DescendingOrder else "asc",
        }
        if callable(self._save_state):
            try:
                self._save_state(data)
            except Exception:
                pass
    def _update_path_label(self):
        if self._current_folder == self._root_dir:
            self.path_label.hide()
        else:
            self.path_label.setText(str(self._current_folder))
            self.path_label.show()
    def _remember_folder(self):
        self._persist_state()
    def _collect_state(self):
        return {
            "last_dir": str(self._current_folder),
            "root_dir": str(self._root_dir),
            "auto_refresh": bool(self.auto_refresh_chk.isChecked()),
            "favorites": self._favorites,
            "fav_group": self._current_fav_group,
            "last_file": str(self._current_file()) if self._current_file() else None,
        }
    def set_start_dir(self, path: Path, *, refresh: bool = False):
        new_dir = self._validate_dir(path)
        if not self._is_under_root(new_dir):
            self._set_tree_root(new_dir)
        self._set_current_folder(new_dir, refresh=refresh, auto_select_first=True)
        if self._last_file_in_state:
            try:
                remembered = Path(self._last_file_in_state)
                if remembered.exists() and self._is_image_file(remembered):
                    self._select_file(remembered)
            except Exception:
                pass
            self._last_file_in_state = None
    def _on_tree_selection_changed(self, selected: QtCore.QItemSelection, deselected: QtCore.QItemSelection):
        if self._block_tree_selection:
            return
        try:
            idxs = self.file_tree.selectionModel().selectedRows()
        except Exception:
            idxs = []
        if not idxs:
            return
        path = self._path_from_index(idxs[0])
        if not path:
            return
        if path.is_dir():
            self._set_current_folder(path, refresh=True, auto_select_first=False)
            return
        if self._is_image_file(path):
            self._select_file(path)
        else:
            self._set_current_folder(path.parent, refresh=False, auto_select_first=False)
    def _on_tree_double_clicked(self, idx: QtCore.QModelIndex):
        path = self._path_from_index(idx)
        if not path:
            return
        if path.is_dir():
            if self.file_tree.isExpanded(idx):
                self.file_tree.collapse(idx)
            else:
                self.file_tree.expand(idx)
            self._set_current_folder(path, refresh=False, auto_select_first=False)
            return
        if self._is_image_file(path):
            self._select_file(path)
    def _next_available_path(self, path: Path) -> Path:
        if not path.exists():
            return path
        stem, suffix = path.stem, path.suffix
        parent = path.parent
        for i in range(1, 1000):
            candidate = parent / f"{stem} ({i}){suffix}"
            if not candidate.exists():
                return candidate
        return path
    def _handle_drop(self, sources: list[Path], target_dir: Path, action: QtCore.Qt.DropAction):
        target_dir = self._validate_dir(target_dir)
        try:
            target_dir.mkdir(parents=True, exist_ok=True)
        except Exception:
            pass
        copy = action == QtCore.Qt.DropAction.CopyAction
        moved = copied = skipped = 0
        errors: list[str] = []
        for src in sources:
            try:
                src_path = Path(src)
            except Exception:
                skipped += 1
                continue
            if not src_path.exists():
                skipped += 1
                continue
            if target_dir == src_path or target_dir in src_path.parents:
                skipped += 1
                continue
            dest = self._next_available_path(target_dir / src_path.name)
            try:
                if copy:
                    if src_path.is_dir():
                        shutil.copytree(src_path, dest)
                    else:
                        shutil.copy2(src_path, dest)
                    copied += 1
                else:
                    shutil.move(str(src_path), str(dest))
                    moved += 1
            except Exception as exc:
                errors.append(f"{src_path.name}: {exc}")
        self._set_current_folder(target_dir, refresh=True)
        parts = []
        if moved:
            parts.append(f"이동 {moved}개")
        if copied:
            parts.append(f"복사 {copied}개")
        if skipped:
            parts.append(f"건너뜀 {skipped}개")
        if parts:
            self.status_label.setText(" / ".join(parts))
        if errors:
            QtWidgets.QMessageBox.warning(self, "이동/복사 실패", "\n".join(errors[:5]))
    def _delete_selection(self):
        paths: list[Path] = []
        try:
            sel = self.file_tree.selectionModel().selectedRows()
            for idx in sel:
                p = self._path_from_index(idx)
                if p and p not in paths:
                    paths.append(p)
        except Exception:
            paths = []
        if not paths and self._current_file():
            self._delete_current_file()
            return
        if not paths:
            QtWidgets.QMessageBox.information(self, "삭제 대상 없음", "삭제할 항목이 없습니다.")
            return
        files = sum(1 for p in paths if p.is_file())
        folders = sum(1 for p in paths if p.is_dir())
        msg = []
        if folders:
            msg.append(f"폴더 {folders}개")
        if files:
            msg.append(f"파일 {files}개")
        res = QtWidgets.QMessageBox.question(
            self,
            "선택 삭제",
            f"{', '.join(msg)}를 삭제할까요?",
            QtWidgets.QMessageBox.StandardButton.Yes | QtWidgets.QMessageBox.StandardButton.No,
            QtWidgets.QMessageBox.StandardButton.No,
        )
        if res != QtWidgets.QMessageBox.StandardButton.Yes:
            return
        removed = 0
        failed: list[str] = []
        for p in paths:
            try:
                if p.is_dir():
                    shutil.rmtree(p)
                else:
                    p.unlink()
                removed += 1
            except Exception as exc:
                failed.append(f"{p.name}: {exc}")
        self._refresh_folder()
        self.status_label.setText(f"삭제 완료: {removed}건")
        if failed:
            QtWidgets.QMessageBox.warning(self, "삭제 실패", "\n".join(failed[:5]))
    def _refresh_favorites_tree(self):
        if not hasattr(self, "fav_tree"):
            return
        self.fav_tree.blockSignals(True)
        self.fav_tree.clear()
        for group, items in self._favorites.items():
            g_item = QtWidgets.QTreeWidgetItem([group])
            g_item.setData(0, QtCore.Qt.ItemDataRole.UserRole, {"type": "group", "name": group})
            for path_str in items:
                path = Path(path_str)
                label = path.name or str(path)
                child = QtWidgets.QTreeWidgetItem([label])
                child.setToolTip(0, str(path))
                child.setData(
                    0,
                    QtCore.Qt.ItemDataRole.UserRole,
                    {"type": "fav", "group": group, "path": str(path)},
                )
                g_item.addChild(child)
            g_item.setExpanded(group == self._current_fav_group)
            self.fav_tree.addTopLevelItem(g_item)
            if group == self._current_fav_group:
                self.fav_tree.setCurrentItem(g_item)
        self.fav_tree.blockSignals(False)
    def _add_favorite_group(self):
        name, ok = QtWidgets.QInputDialog.getText(self, "즐겨찾기 그룹 추가", "그룹 이름을 입력하세요.")
        if not ok or not name.strip():
            return
        name = name.strip()
        if name in self._favorites:
            QtWidgets.QMessageBox.information(self, "중복", "이미 존재하는 그룹입니다.")
            return
        self._favorites[name] = []
        self._current_fav_group = name
        self._refresh_favorites_tree()
        self._persist_state()
    def _remove_favorite_group(self):
        item = self.fav_tree.currentItem()
        data = item.data(0, QtCore.Qt.ItemDataRole.UserRole) if item else None
        group = data.get("name") if isinstance(data, dict) and data.get("type") == "group" else None
        if not group:
            QtWidgets.QMessageBox.information(self, "선택 없음", "삭제할 그룹을 선택하세요.")
            return
        if len(self._favorites) <= 1:
            QtWidgets.QMessageBox.information(self, "삭제 불가", "최소 한 개의 그룹이 필요합니다.")
            return
        res = QtWidgets.QMessageBox.question(
            self,
            "그룹 삭제",
            f"'{group}' 그룹과 포함된 즐겨찾기를 삭제할까요?",
            QtWidgets.QMessageBox.StandardButton.Yes | QtWidgets.QMessageBox.StandardButton.No,
            QtWidgets.QMessageBox.StandardButton.No,
        )
        if res != QtWidgets.QMessageBox.StandardButton.Yes:
            return
        self._favorites.pop(group, None)
        self._current_fav_group = next(iter(self._favorites))
        self._refresh_favorites_tree()
        self._persist_state()
    def _rename_current_file(self):
        target = self._current_file()
        if not target or not target.exists():
            QtWidgets.QMessageBox.information(self, "이름 변경", "선택된 이미지가 없습니다.")
            return
        base_name = target.name
        new_name, ok = QtWidgets.QInputDialog.getText(self, "이름 변경", "새 파일 이름을 입력하세요.", text=base_name)
        if not ok:
            return
        new_name = new_name.strip()
        if not new_name:
            QtWidgets.QMessageBox.information(self, "이름 변경", "파일 이름이 비어 있습니다.")
            return
        if "." not in new_name:
            new_name += target.suffix
        new_path = target.parent / new_name
        if new_path == target:
            return
        if new_path.exists():
            QtWidgets.QMessageBox.warning(self, "이름 변경", "동일한 이름의 파일이 이미 있습니다.")
            return
        try:
            target.rename(new_path)
        except Exception as exc:
            QtWidgets.QMessageBox.warning(self, "이름 변경 실패", str(exc))
            return
        self._set_current_folder(new_path.parent, refresh=True, auto_select_first=False)
        self._select_file(new_path)
        self.status_label.setText(f"이름 변경: {base_name} → {new_path.name}")
    def _add_current_to_favorites(self):
        target = self._current_file() or self._current_folder
        if not target:
            QtWidgets.QMessageBox.information(self, "추가할 항목 없음", "현재 선택된 파일이나 폴더가 없습니다.")
            return
        group = self._current_fav_group or next(iter(self._favorites))
        favs = self._favorites.setdefault(group, [])
        path_str = str(target)
        if path_str not in favs:
            favs.append(path_str)
            self._refresh_favorites_tree()
            self._persist_state()
            self.status_label.setText(f"즐겨찾기 추가: {target}")
        else:
            self.status_label.setText("이미 즐겨찾기에 있습니다.")
    def _remove_selected_favorite(self):
        item = self.fav_tree.currentItem()
        data = item.data(0, QtCore.Qt.ItemDataRole.UserRole) if item else None
        if not isinstance(data, dict) or data.get("type") != "fav":
            QtWidgets.QMessageBox.information(self, "선택 없음", "삭제할 즐겨찾기를 선택하세요.")
            return
        group = data.get("group")
        path_str = data.get("path")
        favs = self._favorites.get(group, [])
        if path_str in favs:
            favs.remove(path_str)
        self._refresh_favorites_tree()
        self._persist_state()
    def _on_favorite_double_clicked(self, item: QtWidgets.QTreeWidgetItem, column: int):
        data = item.data(0, QtCore.Qt.ItemDataRole.UserRole) if item else None
        if not isinstance(data, dict):
            return
        if data.get("type") == "group":
            self._current_fav_group = data.get("name") or self._current_fav_group
            self._persist_state()
            return
        if data.get("type") == "fav":
            path = Path(data.get("path"))
            if not path.exists():
                QtWidgets.QMessageBox.information(self, "경로 없음", f"{path} 가 존재하지 않습니다.")
                return
            if path.is_dir():
                if not self._is_under_root(path):
                    self._set_tree_root(path)
                self._set_current_folder(path, refresh=True, auto_select_first=True)
                return
            if self._is_image_file(path):
                parent = path.parent
                if not self._is_under_root(parent):
                    self._set_tree_root(parent)
                self._select_file(path)
    def _on_tree_ctrl_arrow(self, delta: int):
        """Ctrl+좌/우: 트리에서 현재 선택 기준 다음/이전 이미지로 이동."""
        sel_model = self.file_tree.selectionModel()
        idx = sel_model.currentIndex() if sel_model else QtCore.QModelIndex()
        if (not idx.isValid()) and self._current_file():
            idx = self._index_for_path(self._current_file())
        if not idx.isValid():
            # 더 이상 기준이 없으면 이미지 리스트 기준으로만 이동
            self._select_index(max(0, min(len(self._image_files) - 1, self._current_index + delta)))
            return
        next_idx = self._next_image_index(idx, delta)
        if next_idx.isValid():
            path = self._path_from_index(next_idx)
            if path:
                self._select_file(path)
                return
        # 못 찾으면 현 폴더 내 리스트 기준 이동
        self._select_index(max(0, min(len(self._image_files) - 1, self._current_index + delta)))
    def _next_image_index(self, start_idx: QtCore.QModelIndex, delta: int) -> QtCore.QModelIndex:
        model = self.file_tree.model()
        if not model or not start_idx.isValid() or delta == 0:
            return QtCore.QModelIndex()
        parent = start_idx.parent()
        rows = model.rowCount(parent)
        row = start_idx.row() + delta
        while 0 <= row < rows:
            idx = model.index(row, 0, parent)
            path = self._path_from_index(idx)
            if path and path.is_file() and self._is_image_file(path):
                return idx
            row += delta
        return QtCore.QModelIndex()
    def _apply_sort(self):
        try:
            self._proxy_model.sort(self._sort_column, self._sort_order)
            self.file_tree.header().setSortIndicator(self._sort_column, self._sort_order)
        except Exception:
            pass
    def _on_sort_indicator_changed(self, section: int, order: QtCore.Qt.SortOrder):
        self._sort_column = section
        self._sort_order = order
        self._apply_sort()
        self._persist_state()
    def _emit_debug_image_changed(self):
        try:
            if self._condition_window and hasattr(self._condition_window, "notify_viewer_image_changed"):
                self._condition_window.notify_viewer_image_changed()
        except Exception:
            pass
    def _notify_condition_window(self):
        if not self._condition_window or not hasattr(self._condition_window, "set_viewer_debug_source"):
            return
        try:
            self._condition_window.set_viewer_debug_source(
                enabled=True,
                provider=self._debug_image_payload,
            )
        except Exception:
            pass
    def _debug_image_payload(self):
        if not self._image_files or self._current_index < 0:
            return None
        try:
            path = self._image_files[self._current_index]
        except Exception:
            return None
        frame = self._load_debug_frame(path)
        if frame is None:
            return None
        return {"frame": frame, "label": path.name}
    def _load_debug_frame(self, path: Path):
        try:
            mtime = path.stat().st_mtime
        except Exception:
            mtime = None
        if (
            self._debug_frame_cache_path == path
            and self._debug_frame_cache_frame is not None
            and self._debug_frame_cache_mtime == mtime
        ):
            return self._debug_frame_cache_frame
        try:
            img = Image.open(path).convert("RGB")
            frame = np.asarray(img, dtype=np.uint8)
        except Exception:
            return None
        self._debug_frame_cache_path = path
        self._debug_frame_cache_frame = frame
        self._debug_frame_cache_mtime = mtime
        return frame
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
    def _choose_root(self):
        path = QtWidgets.QFileDialog.getExistingDirectory(self, "루트 선택", str(self._root_dir))
        if not path:
            return
        root = self._validate_dir(path)
        self._set_tree_root(root)
        self._set_current_folder(root, refresh=True, auto_select_first=True)
    def _choose_folder(self):
        # 호환용: 기존 호출이 있다면 루트 선택으로 동작
        self._choose_root()
    def _load_folder(self, folder: Path, *, auto_select_first: bool = False):
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
        prev_path = self._current_file()
        self._image_files = files
        self._debug_frame_cache_path = None
        self._debug_frame_cache_mtime = None
        self._debug_frame_cache_frame = None
        self.path_label.setText(str(folder))
        if files:
            try:
                if prev_path and prev_path in files:
                    self._select_index(files.index(prev_path), update_tree=False)
                elif auto_select_first or self._current_index >= len(files) or self._current_index < 0:
                    self._select_index(0, update_tree=False)
            except Exception:
                pass
        else:
            self._current_index = -1
            self.canvas.clear_image()
            self._status_prefix = "이미지를 찾을 수 없습니다. (png/jpg/jpeg/bmp)"
            self._render_status()
    def _select_index(self, idx: int, *, update_tree: bool = True):
        self._pending_state = self._capture_view_state()
        if not self._image_files:
            self._current_index = -1
            return
        self._debug_frame_cache_path = None
        self._debug_frame_cache_mtime = None
        self._debug_frame_cache_frame = None
        idx = max(0, min(len(self._image_files) - 1, idx))
        self._current_index = idx
        path = self._image_files[idx]
        if update_tree:
            self._select_tree_path(path)
        ok = self.canvas.set_image(path)
        if ok:
            img = self.canvas._image
            dims = f"{img.width()}x{img.height()}" if isinstance(img, QtGui.QImage) else "-"
            self._status_prefix = f"{path.name} | {path.stat().st_size / 1024:.1f} KB, {dims}"
            self._last_sample = None
            self._restore_view_state()
            self._notify_condition_window()
            self._emit_debug_image_changed()
            self._persist_state()
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
        if key == QtCore.Qt.Key.Key_F1 and ctrl:
            self._start_region_selection()
            return
        if key == QtCore.Qt.Key.Key_Space:
            self.canvas._space_pan = True
            self.canvas.setCursor(QtCore.Qt.CursorShape.OpenHandCursor)
            return
        if key == QtCore.Qt.Key.Key_Escape:
            if getattr(self.canvas, "is_region_selecting", lambda: False)():
                try:
                    self.canvas.cancel_region_selection()
                except Exception:
                    pass
                self._on_region_selected(None)
                return
            self.close()
            return
        if key == QtCore.Qt.Key.Key_F5:
            self._refresh_folder()
            return
        if key == QtCore.Qt.Key.Key_Delete:
            self._delete_selection()
            return
        if ctrl and key in (QtCore.Qt.Key.Key_Return, QtCore.Qt.Key.Key_Enter):
            self._rename_current_file()
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
    def _fill_condition_dialog_color(self, color_text: str):
        """현재 열려 있는 조건 편집/노드 창의 color 필드를 채운다."""
        try:
            for w in QtWidgets.QApplication.topLevelWidgets():
                if not w.isVisible():
                    continue
                if hasattr(w, "color_edit"):
                    try:
                        w.color_edit.setText(color_text)
                    except Exception:
                        pass
        except Exception:
            pass
    def _start_region_selection(self):
        if not getattr(self.canvas, "_image", None):
            self.status_label.setText("범위 선택: 이미지가 없습니다.")
            return
        begin = getattr(self.canvas, "begin_region_selection", None)
        if not callable(begin):
            self.status_label.setText("범위 선택 기능을 사용할 수 없습니다.")
            return
        ok = begin(self._on_region_selected)
        if not ok:
            self.status_label.setText("범위 선택을 시작할 수 없습니다.")
            return
        if hasattr(self, "region_select_btn"):
            try:
                self.region_select_btn.setEnabled(False)
            except Exception:
                pass
        tip = "범위 선택: 시작점과 끝점을 순서대로 클릭하세요. 드래그도 가능합니다."
        QtWidgets.QToolTip.showText(QtGui.QCursor.pos(), tip, self, QtCore.QRect(), 2500)
        self.status_label.setText("범위 선택: 시작점과 끝점을 클릭하세요. (Ctrl+F1)")
    def _on_region_selected(self, region: tuple[int, int, int, int] | None):
        if hasattr(self, "region_select_btn"):
            try:
                self.region_select_btn.setEnabled(True)
            except Exception:
                pass
        if not region:
            self.status_label.setText("범위 선택이 취소되었습니다.")
            return
        try:
            x, y, w, h = (int(v) for v in region)
        except Exception:
            self.status_label.setText("범위 가져오기 오류.")
            return
        txt = f"{x},{y},{w},{h}"
        QtGui.QGuiApplication.clipboard().setText(txt)
        QtWidgets.QToolTip.showText(QtGui.QCursor.pos(), f"범위 복사: {txt}", self, QtCore.QRect(), 2000)
        self.status_label.setText(f"범위 복사: {txt}")
        try:
            dbg = getattr(self._condition_window, "debugger", None) if self._condition_window else None
            if dbg and dbg.isVisible():
                dbg._set_test_inputs({"region_raw": txt})
        except Exception:
            pass
        self._fill_condition_dialog_region(txt)
    def _copy_color(self):
        if not self._last_sample:
            self.status_label.setText("색상을 가져오려면 이미지 위에 마우스를 올리세요.")
            return
        hex_text = self._last_sample["hex"]
        QtGui.QGuiApplication.clipboard().setText(hex_text)
        QtWidgets.QToolTip.showText(QtGui.QCursor.pos(), f"색상 복사: #{hex_text}", self, QtCore.QRect(), 2000)
        self.status_label.setText(f"색상 복사: #{hex_text}")
        try:
            dbg = getattr(self._condition_window, "debugger", None) if self._condition_window else None
            if dbg and dbg.isVisible():
                dbg._set_test_inputs({"color_raw": hex_text})
        except Exception:
            pass
        self._fill_condition_dialog_color(hex_text)
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
        self._set_current_folder(folder, refresh=True, auto_select_first=False)
        self.status_label.setText(f"삭제 완료: {removed}개 삭제")
    def _refresh_folder(self):
        self._set_current_folder(self._current_folder, refresh=True, auto_select_first=False)
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
        self._set_current_folder(self._current_folder, refresh=True, auto_select_first=False)
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
            f"핫키: 좌클릭 드래그 이동, Alt+휠/± 확대, 0 리셋, F1 좌표 복사, Ctrl+F1 범위 복사, F2 색상 복사(우클릭), "
            f"F5 새로고침, Delete 선택 삭제, Ctrl+←/→ 이미지 이동, ESC 닫기 | 트리: 더블클릭 열기/접기, 드래그앤드롭 이동(CTRL=복사) "
            f"| 스크린샷: 시작={hk_start}, 정지={hk_stop}, 단일={hk_cap}"
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
class _ProfileListDelegate(QtWidgets.QStyledItemDelegate):
    def _to_brush(self, value):
        if isinstance(value, QtGui.QBrush):
            return value
        if isinstance(value, QtGui.QColor):
            return QtGui.QBrush(value)
        if isinstance(value, str):
            return QtGui.QBrush(QtGui.QColor(value))
        return None
    def paint(
        self,
        painter: QtGui.QPainter,
        option: QtWidgets.QStyleOptionViewItem,
        index: QtCore.QModelIndex,
    ):
        opt = QtWidgets.QStyleOptionViewItem(option)
        self.initStyleOption(opt, index)
        bg_brush = self._to_brush(index.data(QtCore.Qt.ItemDataRole.BackgroundRole))
        fg_brush = self._to_brush(index.data(QtCore.Qt.ItemDataRole.ForegroundRole))
        if bg_brush:
            try:
                hover_flag = QtWidgets.QStyle.StateFlag.State_MouseOver  # Qt6
            except AttributeError:
                hover_flag = QtWidgets.QStyle.State_MouseOver  # Qt5 fallback
            opt.state &= ~hover_flag
        if bg_brush:
            painter.save()
            painter.fillRect(opt.rect, bg_brush)
            painter.restore()
            opt.backgroundBrush = bg_brush
            opt.palette.setBrush(QtGui.QPalette.ColorRole.Base, bg_brush)
            opt.palette.setBrush(QtGui.QPalette.ColorRole.Highlight, bg_brush)
        if fg_brush:
            for role in (
                QtGui.QPalette.ColorRole.Text,
                QtGui.QPalette.ColorRole.WindowText,
                QtGui.QPalette.ColorRole.HighlightedText,
            ):
                opt.palette.setBrush(role, fg_brush)
        super().paint(painter, opt, index)
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
    def _set_type_text(self, item: QtWidgets.QTreeWidgetItem, text: str):
        key = QtCore.Qt.ItemDataRole.UserRole + 5
        item.setText(1, text)
        item.setData(1, key, text)
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
    def _is_seq_column_area(self, pos: QtCore.QPoint) -> bool:
        """Return True if the drop position is within the 순번(column 0) area."""
        col = self.columnAt(pos.x())
        if col == 0:
            return True
        # columnAt can return -1 when near the left edge; treat that as 순번 영역 too.
        if col == -1 and pos.x() <= self.columnWidth(0) + 4:
            return True
        return False
    def _normalized_indicator(
        self,
        pos: QtCore.QPoint,
        indicator: QtWidgets.QAbstractItemView.DropIndicatorPosition,
        target_item: QtWidgets.QTreeWidgetItem | None,
        *,
        force_sibling: bool = False,
    ) -> tuple[QtWidgets.QAbstractItemView.DropIndicatorPosition, bool]:
        """Return adjusted indicator and whether child drop is allowed."""
        allowed_child = False if force_sibling else self._is_drop_allowed(indicator, target_item)
        if indicator == QtWidgets.QAbstractItemView.DropIndicatorPosition.OnItem and (force_sibling or not allowed_child):
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
        force_top_level = self._is_seq_column_area(pos)
        indicator, _ = self._normalized_indicator(pos, indicator, target_item, force_sibling=force_top_level)
        display_index = index
        display_level = self._item_level(index) if index.isValid() else 0
        if force_top_level and target_item:
            top_target = self._top_level_ancestor(target_item)
            if top_target:
                display_index = self.indexFromItem(top_target)
                display_level = 0
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
            "index": display_index if display_index and display_index.isValid() else None,
            "pos": pos,
            "level": display_level,
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
        suffix_bits = []
        if getattr(act, "once_per_macro", False):
            suffix_bits.append("1회")
        if getattr(act, "force_first_run", False):
            suffix_bits.append("첫입력")
        suffix = f" ({', '.join(suffix_bits)})" if suffix_bits else ""
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
        if act.type == "macro_stop":
            return "현재 매크로 중지" + suffix
        if act.type == "sound_alert":
            return "시스템 알림음" + suffix
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
        """색상으로 1회 실행/첫 입력 보장 액션을 표시."""
        default_brush = QtGui.QBrush(self.palette().color(QtGui.QPalette.ColorRole.Text))
        once_brush = QtGui.QBrush(QtGui.QColor("#1f6feb"))
        has_flag = getattr(act, "once_per_macro", False) or getattr(act, "force_first_run", False)
        brush = once_brush if has_flag else default_brush
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
            for blk in getattr(act, "elif_blocks", []):
                econd, eacts, edesc, _ = _split_elif_block(blk)
                if not econd:
                    continue
                elif_header = self._create_elif_header(item, econd, edesc)
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
        header.setData(
            0,
            QtCore.Qt.ItemDataRole.UserRole,
            {"marker": "__elif__", "condition": cond, "enabled": enabled_flag, "description": desc or ""},
        )
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
    def _top_level_ancestor(self, item: QtWidgets.QTreeWidgetItem | None) -> QtWidgets.QTreeWidgetItem | None:
        """Return the highest ancestor (or self) for the given item."""
        current = item
        while current and current.parent():
            current = current.parent()
        return current
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
        force_top_level = self._is_seq_column_area(pos)
        indicator, allowed_child = self._normalized_indicator(pos, indicator, target, force_sibling=force_top_level)
        target_for_insert = self._top_level_ancestor(target) if force_top_level else target
        def compute_parent_and_row(
            indicator_value: QtWidgets.QAbstractItemView.DropIndicatorPosition,
            target_item: QtWidgets.QTreeWidgetItem | None,
            allow_child: bool,
        ) -> tuple[QtWidgets.QTreeWidgetItem | None, int]:
            if force_top_level:
                parent_item = None
                base_row = self.indexOfTopLevelItem(target_item) if target_item else self.topLevelItemCount()
                if base_row < 0:
                    base_row = self.topLevelItemCount()
                insert_at = base_row
                if indicator_value == QtWidgets.QAbstractItemView.DropIndicatorPosition.BelowItem:
                    insert_at = base_row + 1
                elif indicator_value == QtWidgets.QAbstractItemView.DropIndicatorPosition.OnViewport:
                    insert_at = self.topLevelItemCount()
                return parent_item, insert_at
            if indicator_value == QtWidgets.QAbstractItemView.DropIndicatorPosition.OnViewport:
                return None, self.topLevelItemCount()
            if indicator_value == QtWidgets.QAbstractItemView.DropIndicatorPosition.OnItem and allow_child and target_item:
                return target_item, target_item.childCount()
            parent_item = target_item.parent() if target_item else None
            base_row = (
                parent_item.indexOfChild(target_item)
                if parent_item and target_item
                else self.indexOfTopLevelItem(target_item)
                if target_item
                else -1
            )
            insert_at = base_row
            if indicator_value == QtWidgets.QAbstractItemView.DropIndicatorPosition.BelowItem:
                insert_at += 1
            if insert_at < 0:
                insert_at = self.topLevelItemCount()
            return parent_item, insert_at
        if modifiers & QtCore.Qt.KeyboardModifier.AltModifier and event.source() in (self, self.viewport()):
            selected = self._top_level_selected(self.selectedItems())
            if not selected:
                event.ignore()
                return
            if target_for_insert is None and indicator != QtWidgets.QAbstractItemView.DropIndicatorPosition.OnViewport:
                indicator = QtWidgets.QAbstractItemView.DropIndicatorPosition.OnViewport
            parent, insert_row = compute_parent_and_row(indicator, target_for_insert, allowed_child)
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
            if target in items or target_for_insert in items:
                self._clear_drop_feedback()
                return
            parent, insert_row = compute_parent_and_row(indicator, target_for_insert, allowed_child)
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
                desc_text = marker.get("description") or child.text(4) or ""
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
                    act.elif_blocks.append((copy.deepcopy(cond), branch_actions, desc_text))
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
        pattern_provider=None,
        open_pattern_manager=None,
        trigger_keys_provider=None,
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
        self._pattern_provider = pattern_provider
        self._open_pattern_manager = open_pattern_manager
        self._trigger_keys_provider = trigger_keys_provider
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
            ("소리 알림", "sound_alert"),
            ("현재 매크로 중지 (macro_stop)", "macro_stop"),
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
        self.force_first_check = QtWidgets.QCheckBox("첫 입력 1회 무조건 실행(트리거 상태 무시)")
        self.force_first_check.setToolTip("트리거가 풀려도 첫 사이클을 한 번은 끝까지 실행")
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
        self.mouse_pos_edit.setToolTip("F1: 현재 마우스 좌표 입력")
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
        self.repeat_edit.setPlaceholderText("예: 1 (1회), 5 (5회), 3~10 또는 3-10 (랜덤 반복)")
        self.repeat_edit.setToolTip("반복 횟수 입력: 1=1회, 5=5회, 3~10/3-10=3~10 사이 랜덤 반복. 프레스/다운/업/마우스 입력에 적용.")
        self.pause_keep_check = QtWidgets.QCheckBox("일시중지 중에도 눌림 유지")
        self.pause_keep_check.setToolTip("끄면 일시중지/대기 시 자동으로 뗐다가 재개 시 다시 눌러줍니다. 켜면 일시중지 중에도 계속 누른 상태로 유지합니다.")
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
        self.key_warn_label = QtWidgets.QLabel("")
        self.key_warn_label.setStyleSheet("color:#c00;font-weight:bold;")
        self.key_warn_label.setVisible(False)
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
        form.addRow(self.force_first_check)
        form.addRow("키", self.key_edit)
        form.addRow("", self.key_warn_label)
        form.addRow("마우스 버튼", self.mouse_button_combo)
        form.addRow("마우스 좌표 x,y (선택)", self.mouse_pos_edit)
        form.addRow("반복 횟수", self.repeat_edit)
        form.addRow("일시중지 시 유지", self.pause_keep_check)
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
        self.key_edit.textEdited.connect(self._update_trigger_warning)
        self.mouse_button_combo.currentIndexChanged.connect(self._update_trigger_warning)
        self.type_combo.currentIndexChanged.connect(self._update_trigger_warning)
        self.capture_mouse_pos_shortcut = QtGui.QShortcut(QtGui.QKeySequence("F1"), self)
        self.capture_mouse_pos_shortcut.setContext(QtCore.Qt.ShortcutContext.WidgetWithChildrenShortcut)
        self.capture_mouse_pos_shortcut.activated.connect(self._capture_mouse_position)
        self._toggle_override_enabled()
        if action:
            self._load(action)
        else:
            self._sync_fields()
            self._update_trigger_warning()
    def showEvent(self, event: QtGui.QShowEvent):
        super().showEvent(event)
        if self._current_type() == "goto":
            self._refresh_goto_targets()
    def _capture_mouse_position(self):
        mouse_types = {"mouse_click", "mouse_down", "mouse_up", "mouse_move"}
        if self._current_type() not in mouse_types:
            return
        pos = _current_cursor_pos()
        if pos is None:
            qpos = QtGui.QCursor.pos()
            pos = (int(qpos.x()), int(qpos.y()))
        x, y = pos
        txt = f"{x},{y}"
        self.mouse_pos_edit.setText(txt)
        self.mouse_pos_edit.setFocus(QtCore.Qt.FocusReason.ShortcutFocusReason)
        self.mouse_pos_edit.selectAll()
        QtWidgets.QToolTip.showText(QtGui.QCursor.pos(), f"마우스 좌표 입력: {txt}", self, QtCore.QRect(), 1500)
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
    def _parse_repeat_input(self) -> tuple[int, Optional[tuple[int, int]], Optional[str]]:
        raw_repeat = self.repeat_edit.text() or ""
        normalized = self._normalize_repeat_text(raw_repeat)
        if not normalized:
            if not raw_repeat.strip():
                normalized = "1"
            else:
                raise ValueError("반복 횟수는 정수 또는 A~B 형식(정수 범위)로 입력하세요. 예: 1 또는 1~4")
        range_match = re.fullmatch(r"(\d+)~(\d+)", normalized)
        if range_match:
            start, end = (int(range_match.group(1)), int(range_match.group(2)))
            if start < 1 or end < 1:
                raise ValueError("반복 횟수는 1 이상의 정수만 허용됩니다.")
            if start > end:
                raise ValueError("반복 범위는 시작값이 끝값보다 작거나 같아야 합니다.")
            repeat_raw = f"{start}~{end}"
            self.repeat_edit.setText(repeat_raw)
            repeat_range = None if start == end else (start, end)
            return start, repeat_range, repeat_raw
        single_match = re.fullmatch(r"\d+", normalized)
        if single_match:
            val = int(single_match.group(0))
            if val < 1:
                raise ValueError("반복 횟수는 1 이상의 정수만 허용됩니다.")
            self.repeat_edit.setText(str(val))
            return val, None, None
        raise ValueError("반복 횟수는 정수 또는 A~B 형식(정수 범위)로 입력하세요. 예: 1 또는 1~4")
    @staticmethod
    def _normalize_repeat_text(text: str) -> str:
        raw = unicodedata.normalize("NFKC", str(text or ""))
        if not raw:
            return ""
        # Map common range separators and strip zero-width whitespace.
        translate_map = {
            0xFF5E: "~",
            0x301C: "~",
            0x223C: "~",
            0x2013: "~",
            0x2014: "~",
            0x2212: "~",
            0x2010: "~",
            0x2011: "~",
            0x2012: "~",
            0x2015: "~",
            0xFE63: "~",
            0xFF0D: "~",
            0x200B: None,
            0xFEFF: None,
        }
        raw = raw.translate(translate_map)
        raw = raw.replace("-", "~")
        raw = raw.replace("\uD68C", "").replace("\uBC88", "")
        raw = re.sub(r"\s+", "", raw)
        return raw
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
        show_pause_keep = typ in ("down", "mouse_down")
        self._set_field_visible(self.key_edit, show_key)
        self.key_edit.setEnabled(show_key)
        self._set_field_visible(self.mouse_button_combo, show_mouse_btn)
        self.mouse_button_combo.setEnabled(show_mouse_btn)
        self._set_field_visible(self.mouse_pos_edit, show_mouse_pos)
        self.mouse_pos_edit.setEnabled(show_mouse_pos)
        self._set_field_visible(self.repeat_edit, show_repeat)
        self.repeat_edit.setEnabled(show_repeat)
        self._set_field_visible(self.pause_keep_check, show_pause_keep)
        self.pause_keep_check.setEnabled(show_pause_keep)
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
        seed_name = getattr(seed_cond, "name", None)
        macro_cond = MacroCondition(condition=copy.deepcopy(seed_cond), actions=[], else_actions=[], name=seed_name)
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
            pattern_provider=self._pattern_provider if hasattr(self, "_pattern_provider") else None,
            open_pattern_manager=self._open_pattern_manager if hasattr(self, "_open_pattern_manager") else None,
            trigger_keys_provider=self._trigger_keys_provider,
        )
        if not _run_dialog_non_modal(dlg):
            return
        try:
            result = dlg.get_condition()
            self._condition = result.condition
            try:
                setattr(self._condition, "name", result.name)
            except Exception:
                pass
            self.cond_label.setText(_condition_brief(self._condition))
        except Exception as exc:
            QtWidgets.QMessageBox.warning(self, "조건 오류", str(exc))
    def _load(self, act: Action):
        self.type_combo.setCurrentIndex(max(0, self.type_combo.findData(act.type)))
        self.name_edit.setText(act.name or "")
        self.desc_edit.setText(getattr(act, "description", "") or "")
        self.enabled_check.setChecked(getattr(act, "enabled", True))
        self.once_check.setChecked(getattr(act, "once_per_macro", False))
        self.force_first_check.setChecked(getattr(act, "force_first_run", False))
        self.key_edit.setText(getattr(act, "key_raw", None) or act.key or "")
        if getattr(act, "repeat_raw", None):
            repeat_raw_txt = str(act.repeat_raw).strip()
            if "~" not in repeat_raw_txt and "-" in repeat_raw_txt:
                repeat_raw_txt = repeat_raw_txt.replace("-", "~")
            self.repeat_edit.setText(repeat_raw_txt)
        else:
            try:
                self.repeat_edit.setText(str(max(1, int(getattr(act, "repeat", 1) or 1))))
            except Exception:
                self.repeat_edit.setText("1")
        try:
            self.pause_keep_check.setChecked(bool(getattr(act, "hold_keep_on_pause", False)))
        except Exception:
            self.pause_keep_check.setChecked(False)
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
        self._update_trigger_warning()
    def _update_trigger_warning(self):
        if not hasattr(self, "key_warn_label"):
            return
        typ = self._current_type()
        act_key: str | None = None
        if typ in ("press", "down", "up"):
            act_key = (self.key_edit.text() or "").strip().lower()
        elif typ in ("mouse_click", "mouse_down", "mouse_up", "mouse_move"):
            act_key = (self.mouse_button_combo.currentData() or "").strip().lower()
        warn = ""
        if act_key and callable(self._trigger_keys_provider):
            try:
                trig_keys = self._trigger_keys_provider() or []
            except Exception:
                trig_keys = []
            for trig in trig_keys:
                try:
                    toks = set(parse_trigger_keys(trig))
                except Exception:
                    toks = {trig.lower()}
                if act_key in toks:
                    warn = "트리거 키에 포함된 키입니다. 실행 시 트리거가 풀릴 수 있습니다."
                    break
        self.key_warn_label.setText(warn)
        self.key_warn_label.setVisible(bool(warn))
    def get_action(self) -> Action:
        typ = self._current_type()
        name = self.name_edit.text().strip() or None
        description = self.desc_edit.text().strip() or None
        enabled = self.enabled_check.isChecked()
        is_elif = typ == "elif"
        typ_for_build = "if" if is_elif else typ
        act = Action(
            type=typ_for_build,
            name=name,
            description=description,
            enabled=enabled,
            once_per_macro=self.once_check.isChecked(),
            force_first_run=self.force_first_check.isChecked(),
        )
        act.actions = copy.deepcopy(self._existing_children)
        act.else_actions = copy.deepcopy(self._existing_else)
        act.elif_blocks = copy.deepcopy(self._existing_elifs) if typ_for_build == "if" else []
        if typ in ("press", "down", "up"):
            key = self.key_edit.text().strip()
            if not key:
                raise ValueError("키를 입력하세요.")
            act.key = key
            act.key_raw = key
            repeat_val, repeat_range, repeat_raw = self._parse_repeat_input()
            act.repeat = repeat_val
            act.repeat_range = repeat_range
            act.repeat_raw = repeat_raw
            act.hold_keep_on_pause = self.pause_keep_check.isChecked() if typ == "down" else False
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
            repeat_val, repeat_range, repeat_raw = self._parse_repeat_input()
            act.repeat = repeat_val
            act.repeat_range = repeat_range
            act.repeat_raw = repeat_raw
            act.hold_keep_on_pause = self.pause_keep_check.isChecked() if typ == "mouse_down" else False
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
        macro_list_provider=None,
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
        parent_for_patterns = parent if parent is not None else getattr(self, "parent", lambda: None)()
        self._pattern_names = getattr(parent_for_patterns, "_pattern_names", None)
        if not callable(self._pattern_names):
            self._pattern_names = lambda: []
        self._open_pattern_manager = getattr(parent_for_patterns, "_open_pattern_manager", None)
        self._apply_scope_all_cb = apply_scope_all
        self._macro_list_provider = macro_list_provider
        self._scope: str = "global"
        self._app_targets: list[AppTarget] = []
        self._updating_trigger_builder = False
        self._interaction_mode = "none"
        self._interaction_targets: list[str] = []
        self._interaction_excludes: list[str] = []
        self._interaction_allow: list[str] = []
        self._interaction_block: list[str] = []
        self._stop_others_on_trigger = False
        self._suspend_others_while_running = False
        layout = QtWidgets.QVBoxLayout(self)
        form = QtWidgets.QFormLayout()
        self.name_edit = QtWidgets.QLineEdit()
        self.trigger_edit = QtWidgets.QLineEdit()
        self.trigger_edit.setPlaceholderText("예: w 또는 mouse4 (조합은 아래 체크박스로 설정 후 추가)")
        self.trigger_menu_btn = QtWidgets.QToolButton()
        self.trigger_menu_btn.setText("목록")
        self.trigger_menu_btn.setPopupMode(QtWidgets.QToolButton.ToolButtonPopupMode.InstantPopup)
        self.trigger_menu = QtWidgets.QMenu(self)
        self.trigger_menu_btn.setMenu(self.trigger_menu)
        self._populate_trigger_menu()
        self.trigger_mod_ctrl = QtWidgets.QCheckBox("Ctrl")
        self.trigger_mod_shift = QtWidgets.QCheckBox("Shift")
        self.trigger_mod_alt = QtWidgets.QCheckBox("Alt")
        self.trigger_mod_win = QtWidgets.QCheckBox("Win")
        self.trigger_main_edit = QtWidgets.QLineEdit()
        self.trigger_main_edit.setPlaceholderText("주 키 (예: w, f1, mouse1)")
        self.trigger_main_edit.setClearButtonEnabled(True)
        self.trigger_mode_combo = QtWidgets.QComboBox()
        self.trigger_mode_combo.addItem("hold", "hold")
        self.trigger_mode_combo.addItem("toggle", "toggle")
        self.trigger_mode_combo.addItem("1회 실행", "once")
        self.trigger_hold_spin = QtWidgets.QDoubleSpinBox()
        self.trigger_hold_spin.setRange(0.0, 60.0)
        self.trigger_hold_spin.setDecimals(2)
        self.trigger_hold_spin.setSingleStep(0.1)
        self.trigger_hold_spin.setSuffix(" 초 이상 누름")
        self.trigger_hold_spin.setSpecialValueText("즉시 발동")
        self.trigger_hold_spin.setToolTip("hold 모드일 때, 이 시간 이상 누르고 있어야 발동. 0이면 바로 발동.")
        self.trigger_add_btn = QtWidgets.QPushButton("추가")
        self.trigger_save_btn = QtWidgets.QPushButton("선택 저장")
        self.trigger_delete_btn = QtWidgets.QPushButton("선택 삭제")
        self.trigger_up_btn = QtWidgets.QToolButton()
        self.trigger_up_btn.setText("▲")
        self.trigger_down_btn = QtWidgets.QToolButton()
        self.trigger_down_btn.setText("▼")
        self.trigger_table = QtWidgets.QTableWidget(0, 3)
        self.trigger_table.setHorizontalHeaderLabels(["트리거", "모드", "홀드 최소"])
        self.trigger_table.horizontalHeader().setStretchLastSection(True)
        self.trigger_table.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectionBehavior.SelectRows)
        self.trigger_table.setSelectionMode(QtWidgets.QAbstractItemView.SelectionMode.SingleSelection)
        self.trigger_table.setEditTriggers(QtWidgets.QAbstractItemView.EditTrigger.NoEditTriggers)
        self.trigger_table.verticalHeader().setVisible(False)
        trigger_builder_row = QtWidgets.QWidget()
        trigger_builder_layout = QtWidgets.QHBoxLayout(trigger_builder_row)
        trigger_builder_layout.setContentsMargins(0, 0, 0, 0)
        for chk in (
            self.trigger_mod_ctrl,
            self.trigger_mod_shift,
            self.trigger_mod_alt,
            self.trigger_mod_win,
        ):
            trigger_builder_layout.addWidget(chk)
        trigger_builder_layout.addWidget(self.trigger_main_edit, stretch=1)
        self.desc_edit = QtWidgets.QLineEdit()
        self.desc_edit.setPlaceholderText("이 매크로에 대한 메모/설명")
        trigger_input_row = QtWidgets.QWidget()
        trigger_input_layout = QtWidgets.QHBoxLayout(trigger_input_row)
        trigger_input_layout.setContentsMargins(0, 0, 0, 0)
        trigger_input_layout.addWidget(self.trigger_edit, stretch=1)
        trigger_input_layout.addWidget(self.trigger_menu_btn)
        trigger_input_layout.addWidget(self.trigger_mode_combo)
        trigger_input_layout.addWidget(self.trigger_hold_spin)
        trigger_input_layout.addWidget(self.trigger_add_btn)
        trigger_input_layout.addWidget(self.trigger_save_btn)
        trigger_table_box = QtWidgets.QWidget()
        trigger_table_layout = QtWidgets.QVBoxLayout(trigger_table_box)
        trigger_table_layout.setContentsMargins(0, 0, 0, 0)
        trigger_table_layout.addWidget(self.trigger_table)
        trigger_btn_row = QtWidgets.QHBoxLayout()
        trigger_btn_row.addWidget(self.trigger_delete_btn)
        trigger_btn_row.addWidget(self.trigger_up_btn)
        trigger_btn_row.addWidget(self.trigger_down_btn)
        trigger_btn_row.addStretch()
        trigger_table_layout.addLayout(trigger_btn_row)
        self.enabled_check = QtWidgets.QCheckBox("활성")
        self.suppress_checkbox = QtWidgets.QCheckBox("트리거 키 차단")
        self.cycle_spin = QtWidgets.QSpinBox()
        self.cycle_spin.setRange(0, 999999)
        self.cycle_spin.setSpecialValueText("무한 반복")
        self.scope_btn = QtWidgets.QPushButton("앱 동작 범위 설정...")
        self.scope_summary = QtWidgets.QLabel("전역 (어디서나)")
        self.scope_summary.setStyleSheet("color: #555;")
        self.interaction_btn = QtWidgets.QPushButton("상호작용 설정...")
        self.interaction_summary = QtWidgets.QLabel("")
        self.interaction_summary.setStyleSheet("color: #555;")
        scope_row = QtWidgets.QHBoxLayout()
        scope_row.addWidget(self.scope_btn)
        scope_row.addWidget(self.scope_summary, stretch=1)
        scope_row.addStretch()
        inter_row = QtWidgets.QHBoxLayout()
        inter_row.addWidget(self.interaction_btn)
        inter_row.addWidget(self.interaction_summary, stretch=1)
        inter_row.addStretch()
        form.addRow("이름(선택)", self.name_edit)
        form.addRow("설명(선택)", self.desc_edit)
        form.addRow("트리거 입력/모드", trigger_input_row)
        form.addRow("조합 구성", trigger_builder_row)
        form.addRow("트리거 목록", trigger_table_box)
        form.addRow(self.enabled_check)
        form.addRow("사이클 횟수(0=무한)", self.cycle_spin)
        form.addRow(self.suppress_checkbox)
        form.addRow(scope_row)
        # 상호작용 라벨을 생략해 공간을 확보하고 바로 버튼/요약을 배치
        form.addRow(inter_row)
        layout.addLayout(form)
        for chk in (
            self.trigger_mod_ctrl,
            self.trigger_mod_shift,
            self.trigger_mod_alt,
            self.trigger_mod_win,
        ):
            chk.toggled.connect(self._sync_trigger_from_builder)
        self.trigger_main_edit.textChanged.connect(self._sync_trigger_from_builder)
        self.trigger_edit.textChanged.connect(self._sync_builder_from_trigger_text)
        self.trigger_mode_combo.currentIndexChanged.connect(self._sync_trigger_hold_visibility)
        self.trigger_table.itemSelectionChanged.connect(self._on_trigger_selection_changed)
        self.trigger_add_btn.clicked.connect(lambda: self._add_or_update_trigger(force_new=True))
        self.trigger_save_btn.clicked.connect(lambda: self._add_or_update_trigger(require_selection=True))
        self.trigger_delete_btn.clicked.connect(self._delete_selected_trigger)
        self.trigger_up_btn.clicked.connect(lambda: self._move_trigger_row(-1))
        self.trigger_down_btn.clicked.connect(lambda: self._move_trigger_row(1))
        self._sync_builder_from_trigger_text()
        self._sync_trigger_hold_visibility()
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
        self.keyboard_record_btn = QtWidgets.QPushButton("키보드 녹화")
        self.mouse_record_btn = QtWidgets.QPushButton("마우스 녹화")
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
        btns.addWidget(self.keyboard_record_btn)
        btns.addWidget(self.mouse_record_btn)
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
        self.interaction_btn.clicked.connect(self._open_interaction_dialog)
        self.add_btn.clicked.connect(self._add_action)
        self.add_child_btn.clicked.connect(lambda: self._add_action(as_child=True))
        self.keyboard_record_btn.clicked.connect(self._record_keyboard_actions)
        self.mouse_record_btn.clicked.connect(self._record_mouse_actions)
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
        self._update_interaction_summary()
        if macro:
            self._load_macro(macro)
        else:
            self.suppress_checkbox.setChecked(False)
            self._load_triggers([MacroTrigger(key="z", mode="hold")])
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
            self.trigger_hold_spin.setValue(0.0)
            self._sync_trigger_hold_visibility()
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
        for key in [
            "z",
            "x",
            "c",
            "r",
            "t",
            "space",
            "tab",
            "shift",
            "ctrl",
            "alt",
            "left",
            "right",
            "up",
            "down",
        ]:
            add(key, key)
        menu.addSeparator()
        for i in range(1, 13):
            add(f"F{i}", f"f{i}")
    def _sync_trigger_from_builder(self):
        if self._updating_trigger_builder:
            return
        parts: list[str] = []
        if self.trigger_mod_ctrl.isChecked():
            parts.append("ctrl")
        if self.trigger_mod_shift.isChecked():
            parts.append("shift")
        if self.trigger_mod_alt.isChecked():
            parts.append("alt")
        if self.trigger_mod_win.isChecked():
            parts.append("win")
        main = self.trigger_main_edit.text().strip()
        if main:
            parts.append(main)
        combined = normalize_trigger_key("+".join(parts))
        self._updating_trigger_builder = True
        try:
            self.trigger_edit.setText(combined)
        finally:
            self._updating_trigger_builder = False
    def _sync_builder_from_trigger_text(self):
        if self._updating_trigger_builder:
            return
        text = self.trigger_edit.text().strip()
        keys = parse_trigger_keys(text)
        mods = {k for k in keys if k in ("ctrl", "shift", "alt", "win")}
        main_key = next((k for k in keys if k not in mods), "")
        self._updating_trigger_builder = True
        try:
            self.trigger_mod_ctrl.setChecked("ctrl" in mods)
            self.trigger_mod_shift.setChecked("shift" in mods)
            self.trigger_mod_alt.setChecked("alt" in mods)
            self.trigger_mod_win.setChecked("win" in mods)
            self.trigger_main_edit.setText(main_key)
            self.trigger_edit.setText(normalize_trigger_key(text))
        finally:
            self._updating_trigger_builder = False
    def _current_trigger_mode(self) -> str:
        mode_data = self.trigger_mode_combo.currentData()
        if isinstance(mode_data, str):
            mode = mode_data.strip().lower()
            if mode in ("hold", "toggle", "once"):
                return mode
        mode_text = (self.trigger_mode_combo.currentText() or "hold").strip().lower()
        if mode_text in ("1회", "1회 실행", "1회실행", "once", "single", "oneshot", "one-shot"):
            return "once"
        if mode_text in ("hold", "toggle", "once"):
            return mode_text
        return "hold"
    def _set_trigger_mode(self, mode: str):
        normalized = str(mode or "hold").strip().lower()
        if normalized in ("1회", "1회 실행", "1회실행", "single", "oneshot", "one-shot"):
            normalized = "once"
        if normalized not in ("hold", "toggle", "once"):
            normalized = "hold"
        idx = self.trigger_mode_combo.findData(normalized)
        if idx < 0:
            idx = self.trigger_mode_combo.findText(normalized)
        if idx < 0:
            idx = 0
        self.trigger_mode_combo.setCurrentIndex(idx)
    def _sync_trigger_hold_visibility(self):
        is_hold = self._current_trigger_mode() == "hold"
        self.trigger_hold_spin.setVisible(is_hold)
    def _format_hold_value(self, hold: float | None) -> str:
        if hold in (None, "", False):
            return "즉시"
        try:
            val = float(hold)
        except Exception:
            return "즉시"
        if abs(val - round(val)) < 1e-6:
            return f"{int(round(val))}s" if val > 0 else "즉시"
        return f"{val:.2f}s"
    def _resize_trigger_table_height(self):
        table = getattr(self, "trigger_table", None)
        if not table:
            return
        header = table.horizontalHeader()
        header_h = header.height() if header else 0
        frame_h = table.frameWidth() * 2
        rows = table.rowCount()
        body_h = sum(table.rowHeight(r) for r in range(rows)) if rows > 0 else 0
        if body_h <= 0:
            row_h = table.verticalHeader().defaultSectionSize() if table.verticalHeader() else 24
            body_h = row_h * rows
        # keep height tight: only as tall as the rows we have (no phantom empty rows)
        height = int(header_h + body_h + frame_h)
        min_height = max(1, height if rows > 0 else header_h + frame_h)
        table.setMinimumHeight(min_height)
        table.setMaximumHeight(min_height)
    def _set_trigger_row(self, row: int, *, key: str, mode: str, hold: float | None):
        if row < 0:
            return
        if row >= self.trigger_table.rowCount():
            self.trigger_table.insertRow(row)
        key_item = QtWidgets.QTableWidgetItem(key)
        mode_key = str(mode or "hold").strip().lower()
        mode_text = "1회 실행" if mode_key == "once" else mode_key
        mode_item = QtWidgets.QTableWidgetItem(mode_text)
        hold_item = QtWidgets.QTableWidgetItem(self._format_hold_value(hold))
        hold_item.setData(QtCore.Qt.ItemDataRole.UserRole, hold)
        self.trigger_table.setItem(row, 0, key_item)
        self.trigger_table.setItem(row, 1, mode_item)
        self.trigger_table.setItem(row, 2, hold_item)
        self._resize_trigger_table_height()
    def _selected_trigger_row(self) -> int:
        sel = self.trigger_table.selectionModel().selectedRows()
        return sel[0].row() if sel else -1
    def _find_trigger_row(self, key: str) -> int:
        target = key.strip().lower()
        for r in range(self.trigger_table.rowCount()):
            item = self.trigger_table.item(r, 0)
            if item and item.text().strip().lower() == target:
                return r
        return -1
    def _collect_triggers(self) -> list[MacroTrigger]:
        triggers: list[MacroTrigger] = []
        for row in range(self.trigger_table.rowCount()):
            key_item = self.trigger_table.item(row, 0)
            mode_item = self.trigger_table.item(row, 1)
            hold_item = self.trigger_table.item(row, 2)
            key = normalize_trigger_key(key_item.text().strip() if key_item else "")
            mode = ((mode_item.text() if mode_item else "hold") or "hold").strip().lower()
            if mode in ("1회", "1회 실행", "1회실행", "single", "oneshot", "one-shot"):
                mode = "once"
            if mode not in ("hold", "toggle", "once"):
                mode = "hold"
            hold_val = hold_item.data(QtCore.Qt.ItemDataRole.UserRole) if hold_item else None
            try:
                hold = float(hold_val) if hold_val not in (None, "", False) else None
            except Exception:
                hold = None
            if mode != "hold":
                hold = None
            if key:
                triggers.append(MacroTrigger(key=key, mode=mode, hold_press_seconds=hold))
        return triggers
    def _current_trigger_keys(self) -> list[str]:
        try:
            return [t.key for t in self._collect_triggers()]
        except Exception:
            return []
    def _load_triggers(self, triggers: list[MacroTrigger]):
        self.trigger_table.setRowCount(0)
        for idx, trig in enumerate(triggers or []):
            self._set_trigger_row(idx, key=trig.key, mode=trig.mode, hold=trig.hold_press_seconds)
        self.trigger_table.resizeRowsToContents()
        self._resize_trigger_table_height()
        if triggers:
            self.trigger_table.selectRow(0)
            self._on_trigger_selection_changed()
    def _on_trigger_selection_changed(self):
        row = self._selected_trigger_row()
        if row < 0:
            return
        key_item = self.trigger_table.item(row, 0)
        mode_item = self.trigger_table.item(row, 1)
        hold_item = self.trigger_table.item(row, 2)
        if key_item:
            self.trigger_edit.setText(key_item.text())
            self._sync_builder_from_trigger_text()
        if mode_item:
            self._set_trigger_mode(mode_item.text())
        hold_val = hold_item.data(QtCore.Qt.ItemDataRole.UserRole) if hold_item else None
        try:
            self.trigger_hold_spin.setValue(float(hold_val) if hold_val not in (None, "", False) else 0.0)
        except Exception:
            self.trigger_hold_spin.setValue(0.0)
        self._sync_trigger_hold_visibility()
    def _move_trigger_row(self, offset: int):
        if offset == 0:
            return
        row = self._selected_trigger_row()
        if row < 0:
            return
        target = row + offset
        if target < 0 or target >= self.trigger_table.rowCount():
            return
        data = []
        for col in range(self.trigger_table.columnCount()):
            item = self.trigger_table.takeItem(row, col)
            data.append(item)
        self.trigger_table.removeRow(row)
        self.trigger_table.insertRow(target)
        for col, item in enumerate(data):
            self.trigger_table.setItem(target, col, item)
        self.trigger_table.selectRow(target)
    def _delete_selected_trigger(self):
        rows = sorted({idx.row() for idx in self.trigger_table.selectionModel().selectedRows()}, reverse=True)
        if not rows and self.trigger_table.rowCount() > 0:
            rows = [self.trigger_table.rowCount() - 1]
        for r in rows:
            self.trigger_table.removeRow(r)
        if self.trigger_table.rowCount() > 0:
            self.trigger_table.selectRow(min(rows[0], self.trigger_table.rowCount() - 1))
        self._resize_trigger_table_height()
    def _add_or_update_trigger(self, *, force_new: bool = False, require_selection: bool = False):
        key = normalize_trigger_key(self.trigger_edit.text().strip())
        if not key:
            QtWidgets.QMessageBox.information(self, "입력 없음", "추가할 트리거 키를 입력하세요.")
            return
        mode = self._current_trigger_mode()
        hold_val = None
        if mode == "hold":
            try:
                hold_val = max(0.0, float(self.trigger_hold_spin.value()))
            except Exception:
                hold_val = None
            if hold_val == 0:
                hold_val = None
        target_row = self._selected_trigger_row()
        if require_selection and target_row < 0:
            QtWidgets.QMessageBox.information(self, "선택 없음", "수정할 트리거를 먼저 선택하세요.")
            return
        if force_new:
            target_row = self.trigger_table.rowCount()
        else:
            existing_row = self._find_trigger_row(key)
            if target_row < 0 and existing_row >= 0:
                target_row = existing_row
            if target_row < 0:
                target_row = self.trigger_table.rowCount()
        self._set_trigger_row(target_row, key=key, mode=mode, hold=hold_val)
        self.trigger_table.selectRow(target_row)
        self.trigger_table.resizeRowsToContents()
        self._resize_trigger_table_height()
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
                for blk in getattr(act, "elif_blocks", []) or []:
                    _, branch, _, _ = _split_elif_block(blk)
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
    def _update_interaction_summary(self):
        mode_label = {"none": "없음", "stop": "중지", "suspend": "대기"}.get((self._interaction_mode or "none").lower(), "없음")
        def _short(items: list[str], default: str = "전체") -> str:
            if not items:
                return default
            txt = ", ".join(items[:3])
            return txt + ("..." if len(items) > 3 else "")
        parts = [mode_label]
        parts.append(f"대상: {_short(self._interaction_targets)}")
        if self._interaction_excludes:
            parts.append(f"제외: {_short(self._interaction_excludes, default='없음')}")
        if self._interaction_allow:
            parts.append(f"허용: {_short(self._interaction_allow, default='없음')}")
        if self._interaction_block:
            parts.append(f"차단: {_short(self._interaction_block, default='없음')}")
        self.interaction_summary.setText(" | ".join(parts))
    def _open_interaction_dialog(self):
        dlg = InteractionDialog(
            mode=self._interaction_mode,
            targets=self._interaction_targets,
            excludes=self._interaction_excludes,
            allow=self._interaction_allow,
            block=self._interaction_block,
            macro_list_provider=self._macro_list_provider,
            parent=self,
        )
        if _run_dialog_non_modal(dlg) == int(QtWidgets.QDialog.DialogCode.Accepted):
            mode, targets, excludes, allow, block = dlg.result_values()
            self._interaction_mode = (mode or "none").lower()
            if self._interaction_mode not in ("none", "stop", "suspend"):
                self._interaction_mode = "none"
            self._interaction_targets = targets
            self._interaction_excludes = excludes
            self._interaction_allow = allow
            self._interaction_block = block
            self._stop_others_on_trigger = self._interaction_mode == "stop"
            self._suspend_others_while_running = self._interaction_mode == "suspend"
            self._update_interaction_summary()
    def _move_selected(self, offset: int, btn: QtWidgets.QPushButton, tree: ActionTreeWidget | None = None):
        target_tree = tree or self.action_tree
        moved, reason, _ = target_tree.move_selected_within_parent(offset)
        if not moved and reason:
            QtWidgets.QToolTip.showText(btn.mapToGlobal(btn.rect().center()), reason, btn, btn.rect(), 1200)
    def _record_keyboard_actions(self):
        dlg = KeyboardRecordDialog(self)
        if _run_dialog_non_modal(dlg):
            recorded = dlg.recorded_actions()
            if not recorded:
                QtWidgets.QMessageBox.information(self, "녹화 없음", "추가할 키보드 녹화 액션이 없습니다.")
                return
            ts_text = time.strftime("%H:%M:%S")
            group_act = Action(
                type="group",
                name=f"키보드 녹화 {ts_text}",
                description=f"키보드 이벤트 {len(recorded)}개",
                group_mode="all",
                actions=recorded,
            )
            target = self._selected_item(self.action_tree)
            if target:
                new_item = self.action_tree._insert_after(group_act, target)
                parent = target.parent()
            else:
                new_item = self.action_tree._append_action_item(group_act, None)
                parent = None
            if parent:
                self.action_tree.expandItem(parent)
            if new_item:
                self.action_tree.expandItem(new_item)
                self.action_tree.setCurrentItem(new_item)
            self.action_tree.renumber()
            skipped = dlg.skipped_unknown_count()
            if skipped > 0:
                QtWidgets.QMessageBox.information(
                    self,
                    "일부 키 제외",
                    f"미지원 키 이벤트 {skipped}개는 제외하고 그룹에 추가했습니다.",
                )
    def _record_mouse_actions(self):
        dlg = MouseRecordDialog(self)
        if _run_dialog_non_modal(dlg):
            recorded = dlg.recorded_actions()
            if not recorded:
                QtWidgets.QMessageBox.information(self, "녹화 없음", "추가할 마우스 녹화 액션이 없습니다.")
                return
            ts_text = time.strftime("%H:%M:%S")
            group_act = Action(
                type="group",
                name=f"마우스 녹화 {ts_text}",
                description=f"마우스 이벤트 {len(recorded)}개",
                group_mode="all",
                actions=recorded,
            )
            target = self._selected_item(self.action_tree)
            if target:
                new_item = self.action_tree._insert_after(group_act, target)
                parent = target.parent()
            else:
                new_item = self.action_tree._append_action_item(group_act, None)
                parent = None
            if parent:
                self.action_tree.expandItem(parent)
            if new_item:
                self.action_tree.expandItem(new_item)
                self.action_tree.setCurrentItem(new_item)
            self.action_tree.renumber()
            skipped = dlg.skipped_unknown_count()
            if skipped > 0:
                QtWidgets.QMessageBox.information(
                    self,
                    "일부 이벤트 제외",
                    f"미지원 마우스 이벤트 {skipped}개는 제외하고 그룹에 추가했습니다.",
                )
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
            pattern_provider=self._pattern_names,
            open_pattern_manager=self._open_pattern_manager,
            trigger_keys_provider=self._current_trigger_keys,
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
        new_blocks: list[tuple[Condition, list[Action], str, bool | None]] = [
            (base_cond, copy.deepcopy(new_act.actions), new_act.description or new_act.name or "", src_enabled)
        ]
        inherit_enabled = src_enabled
        for blk in getattr(new_act, "elif_blocks", []) or []:
            c, a, desc_text, enabled_override = _split_elif_block(blk)
            if not c:
                continue
            enabled_val = enabled_override if isinstance(enabled_override, bool) else inherit_enabled
            try:
                setattr(c, "enabled", enabled_val)
            except Exception:
                pass
            new_blocks.append((copy.deepcopy(c), copy.deepcopy(a), desc_text or "", enabled_val))
        normalized_blocks = [(cond, acts, desc) for cond, acts, desc, _ in new_blocks]
        target_act.elif_blocks = (target_act.elif_blocks or []) + normalized_blocks
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
            tgt._set_type_text(if_item, updated_if.type)
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
            cond_src = act_data.get("condition") if isinstance(act_data.get("condition"), Condition) else Condition(
                type="pixel", region=(0, 0, 1, 1), color=(255, 0, 0)
            )
            cond = copy.deepcopy(cond_src)
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
                name=item.text(2) or None,
                description=item.text(4) or "",
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
            pattern_provider=self._pattern_names,
            open_pattern_manager=self._open_pattern_manager,
            trigger_keys_provider=self._current_trigger_keys,
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
                convert_to_if = new_act.type == "if" and not getattr(new_act, "_as_elif", False)
                if convert_to_if:
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
                # 조건 이름을 유지
                if hasattr(cond, "name") and not getattr(new_cond, "name", None):
                    try:
                        setattr(new_cond, "name", getattr(cond, "name", None))
                    except Exception:
                        pass
                item.setData(
                    0,
                    QtCore.Qt.ItemDataRole.UserRole,
                    {"marker": "__elif__", "condition": new_cond, "enabled": enabled_flag, "description": new_act.description or ""},
                )
                self.action_tree._set_type_text(item, "ELIF")
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
            pattern_provider=self._pattern_names,
            open_pattern_manager=self._open_pattern_manager,
            trigger_keys_provider=self._current_trigger_keys,
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
            self.action_tree._set_type_text(item, new_act.type)
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
                for blk in getattr(new_act, "elif_blocks", []):
                    econd, eacts, edesc, _ = _split_elif_block(blk)
                    if not econd:
                        continue
                    elif_header = self.action_tree._create_elif_header(item, econd, edesc)
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
            data = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
            if isinstance(data, Action):
                copied.append(copy.deepcopy(data))
                continue
            if isinstance(data, dict) and data.get("marker") == "__elif__":
                cond_src = data.get("condition")
                cond = copy.deepcopy(cond_src) if isinstance(cond_src, Condition) else Condition(
                    type="pixel", region=(0, 0, 1, 1), color=(255, 0, 0), tolerance=0
                )
                enabled_flag = item.checkState(5) == QtCore.Qt.CheckState.Checked
                desc_text = data.get("description") or item.text(4) or ""
                try:
                    setattr(cond, "enabled", enabled_flag)
                except Exception:
                    pass
                branch_actions: list[Action] = []
                else_actions: list[Action] = []
                for idx in range(item.childCount()):
                    child = item.child(idx)
                    marker = child.data(0, QtCore.Qt.ItemDataRole.UserRole)
                    if marker == "__else__":
                        for j in range(child.childCount()):
                            child_act = self.action_tree._action_from_item(child.child(j))
                            if child_act:
                                else_actions.append(child_act)
                        continue
                    child_act = self.action_tree._action_from_item(child)
                    if child_act:
                        branch_actions.append(child_act)
                copied.append(
                    Action(
                        type="if",
                        condition=cond,
                        actions=branch_actions,
                        else_actions=else_actions,
                        name=item.text(2) or "",
                        description=desc_text,
                        enabled=enabled_flag,
                    )
                )
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
        triggers = macro.trigger_list()
        self._load_triggers(triggers)
        if triggers:
            primary = triggers[0]
            self.trigger_edit.setText(primary.key)
            self._set_trigger_mode(primary.mode)
            try:
                self.trigger_hold_spin.setValue(max(0.0, float(primary.hold_press_seconds or 0.0)))
            except Exception:
                self.trigger_hold_spin.setValue(0.0)
        else:
            self.trigger_edit.clear()
            self._set_trigger_mode("hold")
            self.trigger_hold_spin.setValue(0.0)
        self._sync_builder_from_trigger_text()
        self._sync_trigger_hold_visibility()
        self.enabled_check.setChecked(getattr(macro, "enabled", True))
        self.suppress_checkbox.setChecked(bool(macro.suppress_trigger))
        self._stop_others_on_trigger = bool(getattr(macro, "stop_others_on_trigger", False))
        self._suspend_others_while_running = bool(getattr(macro, "suspend_others_while_running", False))
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
        mode_raw = str(getattr(macro, "interaction_outgoing_mode", "none") or "none").lower()
        self._interaction_mode = mode_raw if mode_raw in ("none", "stop", "suspend") else "none"
        self._interaction_targets = list(getattr(macro, "interaction_targets", []) or [])
        self._interaction_excludes = list(getattr(macro, "interaction_exclude_targets", []) or [])
        self._interaction_allow = list(getattr(macro, "interaction_incoming_allow", []) or [])
        self._interaction_block = list(getattr(macro, "interaction_incoming_block", []) or [])
        if self._interaction_mode == "none":
            if self._stop_others_on_trigger:
                self._interaction_mode = "stop"
            elif self._suspend_others_while_running:
                self._interaction_mode = "suspend"
        else:
            self._stop_others_on_trigger = self._interaction_mode == "stop"
            self._suspend_others_while_running = self._interaction_mode == "suspend"
        self._update_interaction_summary()
    def get_macro(self) -> Macro:
        # 빌더 체크박스/입력값을 우선 반영해 텍스트를 최신 상태로 맞춘다.
        self._sync_trigger_from_builder()
        triggers = self._collect_triggers()
        if not triggers:
            raise ValueError("트리거 키를 하나 이상 입력하세요.")
        primary = triggers[0]
        name = self.name_edit.text().strip() or None
        description = self.desc_edit.text().strip() or None
        suppress = self.suppress_checkbox.isChecked()
        interaction_mode = (self._interaction_mode or "none").lower()
        if interaction_mode not in ("none", "stop", "suspend"):
            interaction_mode = "none"
        self._stop_others_on_trigger = interaction_mode == "stop"
        self._suspend_others_while_running = interaction_mode == "suspend"
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
            trigger_key=primary.key,
            mode=primary.mode,
            hold_press_seconds=primary.hold_press_seconds,
            triggers=triggers,
            actions=actions,
            stop_actions=stop_actions,
            suppress_trigger=suppress,
            stop_others_on_trigger=self._stop_others_on_trigger,
            suspend_others_while_running=self._suspend_others_while_running,
            interaction_outgoing_mode=interaction_mode,
            interaction_targets=list(self._interaction_targets),
            interaction_exclude_targets=list(self._interaction_excludes),
            interaction_incoming_allow=list(self._interaction_allow),
            interaction_incoming_block=list(self._interaction_block),
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
        self.start_hotkey_edit.setPlaceholderText("예: home")
        self.stop_hotkey_edit = QtWidgets.QLineEdit(self.manager.hotkeys.stop or "")
        self.stop_hotkey_edit.setPlaceholderText("예: end")
        self.capture_hotkey_edit = QtWidgets.QLineEdit(self.manager.hotkeys.capture or "")
        self.capture_hotkey_edit.setPlaceholderText("예: f11 (한 장 캡처)")
        form.addRow("시작 단축키", self.start_hotkey_edit)
        form.addRow("정지 단축키", self.stop_hotkey_edit)
        form.addRow("단일 캡처 단축키", self.capture_hotkey_edit)
        self.hotkey_checkbox = QtWidgets.QCheckBox("단축키 활성화")
        self.hotkey_checkbox.setChecked(self.manager.hotkeys.enabled)
        form.addRow(self.hotkey_checkbox)
        self.preset_combo = QtWidgets.QComboBox()
        for name in self._sorted_preset_names():
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
        layout.addWidget(QtWidgets.QLabel("단축키는 단일 키 이름(f8, home 등)만 지원합니다."))
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
    def _name_sort_key(self, name: str):
        def _bucket(ch: str) -> int:
            if ch.isascii() and ch.isalpha():
                return 0
            if "가" <= ch <= "힣":
                return 1
            if ch.isdigit():
                return 2
            return 3
        if not name:
            return ((3, ""),)
        key_parts = [(_bucket(ch), ch.casefold()) for ch in name]
        key_parts.append((4, len(name)))
        return tuple(key_parts)
    def _sorted_preset_names(self) -> list[str]:
        names = list(self._presets.keys())
        return sorted(
            names,
            key=lambda n: (-1, "") if n == "사용자 설정" else (0, self._name_sort_key(n)),
        )
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
        start_raw = self.start_hotkey_edit.text()
        stop_raw = self.stop_hotkey_edit.text()
        capture_raw = self.capture_hotkey_edit.text()
        start_key = _sanitize_screenshot_hotkey(start_raw, allow_reserved=False)
        stop_key = _sanitize_screenshot_hotkey(stop_raw, allow_reserved=False)
        capture_key = _sanitize_screenshot_hotkey(capture_raw)
        start_text = (start_raw or "").strip()
        stop_text = (stop_raw or "").strip()
        capture_text = (capture_raw or "").strip()
        if start_text and start_key is None:
            self.start_hotkey_edit.setText("")
        elif start_key and start_key != start_text.lower():
            self.start_hotkey_edit.setText(start_key)
        if stop_text and stop_key is None:
            self.stop_hotkey_edit.setText("")
        elif stop_key and stop_key != stop_text.lower():
            self.stop_hotkey_edit.setText(stop_key)
        if capture_key and capture_key != capture_text.lower():
            self.capture_hotkey_edit.setText(capture_key)
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
        get_viewer_cb=None,
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
        self._get_viewer_cb = get_viewer_cb
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
        self._use_viewer_image: bool = False
        self._selection_highlight: bool = False
        self._log_visible: bool = True
        self._viewer_shortcuts: list[QtGui.QShortcut] = []
        self._selected_item_path: list[str] | None = None
        self._build_ui()
        self._install_viewer_shortcuts()
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
        self.viewer_image_chk = QtWidgets.QCheckBox("뷰어 이미지 사용")
        self.viewer_image_chk.toggled.connect(self._on_use_viewer_toggled)
        status_row.addWidget(self.viewer_image_chk)
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
        self.highlight_btn = QtWidgets.QToolButton()
        self.highlight_btn.setText("선택 노드 표시")
        self.highlight_btn.setToolButtonStyle(QtCore.Qt.ToolButtonStyle.ToolButtonTextBesideIcon)
        self.highlight_btn.setCheckable(True)
        self.highlight_btn.setChecked(False)
        self.highlight_btn.toggled.connect(self._on_highlight_toggle)
        self.condition_stop_btn = QtWidgets.QPushButton("조건 디버그 중지")
        self.condition_stop_btn.setEnabled(False)
        self.condition_stop_btn.clicked.connect(self._on_condition_stop_clicked)
        cond_header.addWidget(self.condition_state_label)
        cond_header.addWidget(self.condition_fail_label, 1)
        cond_header.addStretch()
        cond_header.addWidget(self.highlight_btn)
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
        self.condition_compare_chip = _attach_hex_preview_chip(self.condition_color_compare_edit)
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
        self.condition_tree.itemSelectionChanged.connect(self._on_condition_selection_changed)
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
        self.color_input_chip = _attach_hex_preview_chip(self.color_input)
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
        log_head = QtWidgets.QHBoxLayout()
        log_head.addWidget(QtWidgets.QLabel("최근 로그/이벤트"))
        self.log_visible_chk = QtWidgets.QCheckBox("로그 표시")
        self.log_visible_chk.setChecked(True)
        self.log_visible_chk.toggled.connect(self._set_log_visible)
        log_head.addStretch()
        log_head.addWidget(self.log_visible_chk)
        layout.addLayout(log_head)
        self.log_view = QtWidgets.QTextEdit()
        self.log_view.setReadOnly(True)
        self.log_view.setAcceptRichText(True)
        self.log_view.setFont(QtGui.QFontDatabase.systemFont(QtGui.QFontDatabase.SystemFont.FixedFont))
        layout.addWidget(self.log_view, 1)
        self.resize(900, 600)
    def _install_viewer_shortcuts(self):
        shortcuts = {
            "Ctrl+Left": QtCore.Qt.Key.Key_Left,
            "Ctrl+Right": QtCore.Qt.Key.Key_Right,
            "Ctrl+Up": QtCore.Qt.Key.Key_Up,
            "Ctrl+Down": QtCore.Qt.Key.Key_Down,
        }
        for seq, key in shortcuts.items():
            sc = QtGui.QShortcut(QtGui.QKeySequence(seq), self)
            sc.setContext(QtCore.Qt.ShortcutContext.WidgetWithChildrenShortcut)
            sc.activated.connect(lambda key=key: self._forward_viewer_key(key, QtCore.Qt.KeyboardModifier.ControlModifier))
            self._viewer_shortcuts.append(sc)
    def show_and_raise(self):
        self.show()
        self.raise_()
        self.activateWindow()
    @property
    def use_viewer_image(self) -> bool:
        return bool(self._use_viewer_image)
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
        self._use_viewer_image = bool(state.get("use_viewer_image", False))
        try:
            self.viewer_image_chk.setChecked(self._use_viewer_image)
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
        self._selection_highlight = bool(state.get("highlight_selection", False))
        try:
            self.highlight_btn.setChecked(self._selection_highlight)
        except Exception:
            pass
        try:
            self._set_log_visible(bool(state.get("log_visible", True)))
        except Exception:
            pass
        try:
            if hasattr(self, "log_visible_chk"):
                blocker = QtCore.QSignalBlocker(self.log_visible_chk)
                self.log_visible_chk.setChecked(self._log_visible)
                del blocker
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
            # 자동 복원 시에는 포커스를 빼앗지 않는다.
            QtCore.QTimer.singleShot(0, self.show)
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
            "use_viewer_image": bool(self.viewer_image_chk.isChecked()) if hasattr(self, "viewer_image_chk") else False,
            "sections": {k: btn.isChecked() for k, btn in self._section_controls.items()},
            "highlight_selection": bool(getattr(self, "highlight_btn", None).isChecked()) if hasattr(self, "highlight_btn") else False,
            "log_visible": bool(self._log_visible),
        }
    def closeEvent(self, event: QtGui.QCloseEvent):
        self.stop_condition_debug()
        # 창을 닫을 때 뷰어에 남은 오버레이를 정리
        self._clear_viewer_overlay()
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
        if not self._log_visible:
            return
        self._refresh_log_view()
    def _refresh_log_view(self):
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
    def _set_log_visible(self, visible: bool):
        self._log_visible = bool(visible)
        self.log_view.setVisible(self._log_visible)
        if self._log_visible:
            self._refresh_log_view()
        if callable(self._save_state_cb):
            try:
                self._save_state_cb(self._collect_state())
            except Exception:
                pass
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
    def _on_use_viewer_toggled(self, checked: bool):
        self._use_viewer_image = bool(checked)
        # 디버거 사용 중이면 뷰어와 오버레이 상태를 즉시 동기화
        if not self._use_viewer_image:
            self._clear_viewer_overlay()
        elif self._selection_highlight:
            self._apply_selection_overlay()
        if callable(self._save_state_cb):
            try:
                self._save_state_cb(self._collect_state())
            except Exception:
                pass
        if self._condition_timer.isActive():
            self._tick_condition_debug()
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
        restored = self._restore_selection_path()
        if not restored and self._selection_highlight and not self.condition_tree.selectedItems():
            first = self._first_pixel_item(only_true=True)
            if first:
                self._set_tree_selection(first, keep_focus=True)
        fail_path = self._find_first_failure_path(tree, [])
        fail_text = " > ".join(fail_path) if fail_path else "-"
        self._update_condition_status(tree.get("result"), fail_text=fail_text, label=label)
        if self._selection_highlight:
            self._apply_selection_overlay()
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
    def _get_viewer(self):
        return self._get_viewer_cb() if callable(self._get_viewer_cb) else None
    def _clear_viewer_overlay(self):
        viewer = self._get_viewer()
        if viewer and hasattr(viewer, "canvas"):
            try:
                viewer.canvas.set_overlays([])
            except Exception:
                pass
    def _apply_selection_overlay(self):
        if not self._use_viewer_image:
            return
        viewer = self._get_viewer()
        if viewer is None or not hasattr(viewer, "canvas"):
            return
        qimg = getattr(viewer.canvas, "_image", None)
        if qimg is None or qimg.isNull():
            return
        rects: list[tuple[int, int, int, int, object]] = []
        items = self.condition_tree.selectedItems()
        if not items:
            fallback = self._first_pixel_item(only_true=True)
            if fallback:
                if self._selection_highlight:
                    self._set_tree_selection(fallback, keep_focus=True)
                items = [fallback]
        for item in items:
            node = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
            if not isinstance(node, dict):
                continue
            if node.get("type") != "pixel":
                continue
            detail = (node.get("detail") or {}).get("pixel") or {}
            # 전체 영역은 초록색으로 표시
            region = detail.get("region")
            if isinstance(region, (list, tuple)) and len(region) == 4:
                try:
                    rx, ry, rw, rh = (int(region[0]), int(region[1]), int(region[2]), int(region[3]))
                    rects.append((rx, ry, rw, rh, QtGui.QColor(0, 200, 0)))
                except Exception:
                    pass
            coord = detail.get("coord")
            if not isinstance(coord, (list, tuple)) or len(coord) != 2:
                continue
            try:
                bx, by = int(coord[0]), int(coord[1])
            except Exception:
                continue
            pts = detail.get("pattern_points") or []
            size = detail.get("pattern_size")
            max_dx = max((int(p[0]) for p in pts), default=0)
            max_dy = max((int(p[1]) for p in pts), default=0)
            if not pts and isinstance(size, (list, tuple)) and len(size) == 2:
                try:
                    max_dx = int(size[0]) - 1
                    max_dy = int(size[1]) - 1
                except Exception:
                    pass
            # 발견(참)일 때만 붉은색 테두리
            if node.get("result"):
                highlight_color = QtGui.QColor(255, 215, 0)
                rects.append((bx, by, max_dx + 1, max_dy + 1, highlight_color))
                for dx, dy in pts:
                    rects.append((bx + int(dx), by + int(dy), 1, 1, highlight_color))
                match_coords = detail.get("matched_coords") or []
                for mx, my in match_coords:
                    try:
                        rects.append((int(mx), int(my), 1, 1, highlight_color))
                    except Exception:
                        continue
        try:
            viewer.canvas.set_overlays(rects)
            viewer.canvas.update()
        except Exception:
            pass
    def _on_highlight_toggle(self, checked: bool):
        self._selection_highlight = bool(checked)
        if checked:
            if not self.condition_tree.selectedItems():
                first = self._first_pixel_item(only_true=True)
                if first:
                    self._set_tree_selection(first, keep_focus=True)
            self._apply_selection_overlay()
        else:
            self._clear_viewer_overlay()
        if callable(self._save_state_cb):
            try:
                self._save_state_cb(self._collect_state())
            except Exception:
                pass
    def _on_condition_selection_changed(self):
        items = self.condition_tree.selectedItems()
        if items:
            self._selected_item_path = self._current_selection_path()
        if self._selection_highlight:
            self._apply_selection_overlay()
    def _forward_viewer_key(self, key: int, modifiers: QtCore.Qt.KeyboardModifier = QtCore.Qt.KeyboardModifier.NoModifier):
        viewer = self._get_viewer()
        if viewer is None and callable(self._focus_viewer_cb):
            try:
                self._focus_viewer_cb()
            except Exception:
                pass
            viewer = self._get_viewer()
        if viewer is None:
            return
        # 우선 실제 키 이벤트를 전달해 viewer의 기본 처리 로직을 이용
        try:
            evt = QtGui.QKeyEvent(QtCore.QEvent.Type.KeyPress, key, modifiers)
            QtWidgets.QApplication.sendEvent(viewer, evt)
        except Exception:
            pass
        # 필요한 경우 포커스와 창 활성화도 함께 시도
        try:
            viewer.raise_()
            viewer.activateWindow()
        except Exception:
            pass
    def _first_pixel_item(self, *, only_true: bool = True) -> QtWidgets.QTreeWidgetItem | None:
        def match(item: QtWidgets.QTreeWidgetItem) -> bool:
            node = item.data(0, QtCore.Qt.ItemDataRole.UserRole)
            if not isinstance(node, dict):
                return False
            if node.get("type") != "pixel":
                return False
            if only_true and not node.get("result"):
                return False
            return True
        def walk(item: QtWidgets.QTreeWidgetItem) -> QtWidgets.QTreeWidgetItem | None:
            if match(item):
                return item
            for i in range(item.childCount()):
                found = walk(item.child(i))
                if found:
                    return found
            return None
        for i in range(self.condition_tree.topLevelItemCount()):
            found = walk(self.condition_tree.topLevelItem(i))
            if found:
                return found
        return None
    def _current_selection_path(self) -> list[str] | None:
        items = self.condition_tree.selectedItems()
        if not items:
            return None
        item = items[0]
        path: list[str] = []
        while item:
            path.append(item.text(0))
            item = item.parent()
        return list(reversed(path))
    def _restore_selection_path(self) -> bool:
        if not self._selected_item_path:
            return False
        target = self._find_item_by_path(self._selected_item_path)
        if target:
            return self._set_tree_selection(target, keep_focus=True)
        return False
    def _find_item_by_path(self, path: list[str]) -> QtWidgets.QTreeWidgetItem | None:
        if not path:
            return None
        def walk(item: QtWidgets.QTreeWidgetItem, depth: int) -> QtWidgets.QTreeWidgetItem | None:
            if item.text(0) != path[depth]:
                return None
            if depth == len(path) - 1:
                return item
            for i in range(item.childCount()):
                found = walk(item.child(i), depth + 1)
                if found:
                    return found
            return None
        for i in range(self.condition_tree.topLevelItemCount()):
            top = self.condition_tree.topLevelItem(i)
            found = walk(top, 0)
            if found:
                return found
        return None
    def _set_tree_selection(self, item: QtWidgets.QTreeWidgetItem | None, *, keep_focus: bool = False) -> bool:
        if item is None:
            return False
        prev_focus = QtWidgets.QApplication.focusWidget() if keep_focus else None
        blocker = QtCore.QSignalBlocker(self.condition_tree)
        try:
            self.condition_tree.setCurrentItem(item)
            item.setSelected(True)
        except Exception:
            return False
        finally:
            del blocker
        self._selected_item_path = self._current_selection_path()
        if keep_focus and prev_focus and prev_focus not in (self.condition_tree, self.condition_tree.viewport()):
            try:
                prev_focus.setFocus(QtCore.Qt.FocusReason.OtherFocusReason)
            except Exception:
                pass
        return True
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
        color_chip_html = ""
        tgt_hex = None
        tooltip_parts: list[str] = []
        # 비교 색상 결과 추가 + 색상 칩 준비
        if cond_type == "pixel":
            detail = node.get("detail", {}).get("pixel") or {}
            target = detail.get("color")
            tol = int(detail.get("tolerance", 0))
            expect_exists = detail.get("expect_exists", True)
            tgt_hex = _rgb_to_hex(target) if isinstance(target, (list, tuple)) and len(target) == 3 else None
            if tgt_hex:
                tooltip_parts.append(f"목표 색상: {tgt_hex}")
            if compare_color and isinstance(target, (list, tuple)) and len(target) == 3:
                diff = max(abs(int(target[i]) - int(compare_color[i])) for i in range(3))
                match = diff <= tol
                final = match if expect_exists else (not match)
                need = None
                if not final:
                    need = f"tol>={diff}" if expect_exists else f"tol<{diff}"
                result_text = f"{result_text} / 대조={'참' if final else '거짓'} diff={diff}"
                tooltip_parts.append(f"대조 색상: {_rgb_to_hex(compare_color)} / diff={diff} tol={tol}")
                if need:
                    tooltip_parts.append(f"대조 필요: {need}")
            sample = detail.get("sample_color")
            if isinstance(sample, (list, tuple)) and len(sample) == 3:
                sample_hex = _rgb_to_hex(sample)
                if sample_hex:
                    tooltip_parts.append(f"샘플: {sample_hex}")
        detail_text = self._format_condition_detail(cond_type, node.get("detail") or {}, cond)
        item = QtWidgets.QTreeWidgetItem([label, result_text, detail_text])
        if tgt_hex:
            try:
                color_str = tgt_hex if tgt_hex.startswith("#") else f"#{tgt_hex}"
                color = QtGui.QColor(color_str)
                if color.isValid():
                    pix = QtGui.QPixmap(12, 12)
                    pix.fill(color)
                    item.setIcon(2, QtGui.QIcon(pix))
            except Exception:
                pass
        if tooltip_parts:
            item.setToolTip(2, "\n".join(tooltip_parts))
        self._apply_condition_color(item, node.get("detail") or {}, result_bool)
        item.setData(0, QtCore.Qt.ItemDataRole.UserRole, node)
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
            color_txt = _rgb_to_hex(color) or "-"
            expect_exists = bool(pix.get("expect_exists", True))
            expect = "있음" if expect_exists else "없음"
            found = "있음" if pix.get("found") else "없음"
            tol = pix.get("tolerance")
            match_cnt = pix.get("match_count")
            min_cnt = pix.get("min_count")
            count_txt = ""
            if expect_exists and match_cnt is not None and min_cnt is not None:
                count_txt = f" (일치 {match_cnt}/{min_cnt})"
            return f"영역={region_txt} 색상={color_txt} tol={tol} 기대={expect}/발견={found}{count_txt}"
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
        match_cnt = event.get("match_count")
        min_cnt = event.get("min_count", 1)
        region_txt = ",".join(str(v) for v in region) if region else "-"
        color_txt = "#" + "".join(f"{c:02x}" for c in color) if isinstance(color, (list, tuple)) else "-"
        tol_txt = f"tol={tol}" if tol is not None else f"tol={self._tolerance}"
        count_txt = ""
        if expect and match_cnt is not None and min_cnt is not None:
            count_txt = f", 일치 {match_cnt}/{min_cnt}"
        msg = (
            f"{source} / {label}: {'성공' if res else '실패'} "
            f"(기대={'있음' if expect else '없음'}, 발견={'있음' if found else '없음'}{count_txt}, {tol_txt}, 영역={region_txt}, 색상={color_txt})"
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
            macro_info = event.get("macro", {}) or {}
            label = macro_info.get("name") or macro_info.get("trigger_key")
            if not label:
                trig_list = macro_info.get("triggers") or []
                if trig_list and isinstance(trig_list, list):
                    first = trig_list[0] if trig_list else {}
                    if isinstance(first, dict):
                        label = first.get("key")
            label = label or "매크로"
            self._append_log_line(f"[매크로 시작] {label}")
        elif etype == "macro_stop":
            macro_info = event.get("macro", {}) or {}
            label = macro_info.get("name") or macro_info.get("trigger_key")
            if not label:
                trig_list = macro_info.get("triggers") or []
                if trig_list and isinstance(trig_list, list):
                    first = trig_list[0] if trig_list else {}
                    if isinstance(first, dict):
                        label = first.get("key")
            label = label or "매크로"
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
class PixelPatternManagerDialog(QtWidgets.QDialog):
    def __init__(self, parent=None, *, patterns: dict | None = None, open_image_viewer=None, sample_provider=None):
        super().__init__(parent)
        self._owner = parent
        # 부모와 포커스 연동을 끊어 메인 창이 앞에 뜨는 것을 막는다.
        self.setParent(None)
        self.setWindowTitle("픽셀 패턴 관리자")
        self.setModal(False)
        self.setWindowModality(QtCore.Qt.WindowModality.NonModal)
        # 원본을 바로 다루어 저장 누락을 줄인다.
        shared = _load_shared_patterns()
        incoming = patterns or {}
        merged: dict[str, PixelPattern] = copy.deepcopy(shared)
        for name, pat in incoming.items():
            if name not in merged:
                merged[name] = copy.deepcopy(pat)
        self.patterns = merged
        self._sanitize_all_patterns()
        self._current_name: Optional[str] = None
        self._anchor_pos: Optional[tuple[int, int]] = None
        self._anchor_image_pos: Optional[tuple[int, int]] = None
        self._loading_patterns = False
        self._loading_points = False
        self._open_image_viewer = open_image_viewer
        self._sample_provider = sample_provider
        self._overlay_visible = False
        self._viewer_connected = False
        self._highlight_dx_dy: Optional[tuple[int, int]] = None
        self._keep_name_on_next_save = False
        self._build_ui()
        self._load_patterns()
        self._attach_viewer_change_listener()
    def _sanitize_pattern(self, pat: PixelPattern) -> PixelPattern:
        pat.tolerance = 0
        for pt in pat.points:
            pt.tolerance = None
        return pat
    def _sanitize_all_patterns(self):
        for name, pat in list(self.patterns.items()):
            self.patterns[name] = self._sanitize_pattern(pat)
    def _attach_viewer_change_listener(self):
        self._ensure_viewer_listener()
    def _ensure_viewer_listener(self):
        if self._viewer_connected:
            return
        viewer = getattr(self._owner, "_image_viewer_dialog", None)
        if not viewer or not hasattr(viewer, "canvas"):
            return
        canvas = viewer.canvas
        try:
            if hasattr(canvas, "imageChanged"):
                canvas.imageChanged.connect(self._on_viewer_changed)
            self._viewer_connected = True
        except Exception:
            self._viewer_connected = False
    def _build_ui(self):
        layout = QtWidgets.QVBoxLayout(self)
        # 이름/설명 입력을 상단에 배치해 선택/입력 흐름을 명확히 한다.
        info_widget = QtWidgets.QWidget()
        info_form = QtWidgets.QFormLayout(info_widget)
        self.name_edit = QtWidgets.QLineEdit()
        self.desc_edit = QtWidgets.QLineEdit()
        self.name_edit.setReadOnly(True)
        self.desc_edit.setReadOnly(True)
        self.tol_spin = QtWidgets.QSpinBox()
        self.tol_spin.setRange(0, 255)
        self.tol_spin.setValue(0)
        # 패턴 관리 화면에서는 tol을 사용하지 않으므로 UI에서 숨긴다.
        self.tol_spin.setEnabled(False)
        self.tol_spin.hide()
        info_form.addRow("이름", self.name_edit)
        info_form.addRow("설명", self.desc_edit)
        layout.addWidget(info_widget)
        info_widget.hide()  # 이름/설명 입력란은 모달 편집만 사용하므로 UI에서 숨김
        top_row = QtWidgets.QHBoxLayout()
        # 패턴 목록: 이름/설명 2열 테이블
        self.list_widget = QtWidgets.QTableWidget(0, 2)
        self.list_widget.setHorizontalHeaderLabels(["이름", "설명"])
        self.list_widget.horizontalHeader().setSectionResizeMode(QtWidgets.QHeaderView.ResizeMode.Stretch)
        self.list_widget.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectionBehavior.SelectRows)
        self.list_widget.setSelectionMode(QtWidgets.QAbstractItemView.SelectionMode.SingleSelection)
        self.list_widget.setEditTriggers(QtWidgets.QAbstractItemView.EditTrigger.NoEditTriggers)
        self.list_widget.setContextMenuPolicy(QtCore.Qt.ContextMenuPolicy.PreventContextMenu)
        self.list_widget.currentCellChanged.connect(self._on_select_pattern_cell)
        self.list_widget.cellDoubleClicked.connect(self._edit_pattern_meta_dialog)
        list_btns = QtWidgets.QVBoxLayout()
        self.add_btn = QtWidgets.QPushButton("새 패턴")
        self.stay_on_top_check = QtWidgets.QCheckBox("항상 위")
        self.stay_on_top_check.toggled.connect(self._toggle_stay_on_top)
        self.dup_btn = QtWidgets.QPushButton("복제")
        self.del_btn = QtWidgets.QPushButton("삭제")
        self.open_viewer_btn = QtWidgets.QPushButton("이미지 뷰어")
        self.open_viewer_btn.clicked.connect(self._open_viewer)
        for b in (self.add_btn, self.stay_on_top_check, self.dup_btn, self.del_btn):
            list_btns.addWidget(b)
        list_btns.addWidget(self.open_viewer_btn)
        list_btns.addStretch()
        top_row.addWidget(self.list_widget, 2)
        list_btn_wrap = QtWidgets.QWidget()
        list_btn_wrap.setLayout(list_btns)
        top_row.addWidget(list_btn_wrap)
        layout.addLayout(top_row)
        point_btn_row = QtWidgets.QHBoxLayout()
        self.add_point_btn = QtWidgets.QPushButton("커서 픽셀 추가 (F3)")
        self.del_point_btn = QtWidgets.QPushButton("포인트 삭제")
        self.clear_point_btn = QtWidgets.QPushButton("모두 지우기")
        point_btn_row.addWidget(self.add_point_btn)
        point_btn_row.addWidget(self.del_point_btn)
        point_btn_row.addWidget(self.clear_point_btn)
        self.table = QtWidgets.QTableWidget(0, 4)
        self.table.setHorizontalHeaderLabels(["x", "y", "color", ""])
        self.table.horizontalHeader().setSectionResizeMode(QtWidgets.QHeaderView.ResizeMode.Stretch)
        self.table.horizontalHeader().setSectionResizeMode(3, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        self.table.setContextMenuPolicy(QtCore.Qt.ContextMenuPolicy.PreventContextMenu)
        self.table.itemChanged.connect(lambda *_: self._update_preview())
        self.table.itemSelectionChanged.connect(self._highlight_selected_point)
        preview_wrap = QtWidgets.QVBoxLayout()
        self.preview_label = QtWidgets.QLabel("미리보기")
        self.preview_label.setAlignment(QtCore.Qt.AlignmentFlag.AlignCenter)
        self.preview_label.setStyleSheet("background: transparent;")
        self.preview_label.setContextMenuPolicy(QtCore.Qt.ContextMenuPolicy.PreventContextMenu)
        self.preview_scroll = QtWidgets.QScrollArea()
        self.preview_scroll.setWidget(self.preview_label)
        self.preview_scroll.setWidgetResizable(True)
        self.preview_scroll.setFrameShape(QtWidgets.QFrame.Shape.Box)
        self.preview_scroll.setMinimumHeight(220)
        self.preview_scroll.setHorizontalScrollBarPolicy(QtCore.Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.preview_scroll.setVerticalScrollBarPolicy(QtCore.Qt.ScrollBarPolicy.ScrollBarAsNeeded)
        self.size_label = QtWidgets.QLabel("")
        preview_wrap.addWidget(self.preview_scroll)
        preview_wrap.addWidget(self.size_label)
        # 배경 선택 & 오버레이 토글
        bg_row = QtWidgets.QHBoxLayout()
        bg_row.addWidget(QtWidgets.QLabel("배경"))
        self.preview_bg_combo = QtWidgets.QComboBox()
        self.preview_bg_combo.addItems(["체커보드", "검정", "흰색", "주황"])
        self.preview_bg_combo.currentIndexChanged.connect(lambda *_: self._update_preview())
        bg_row.addWidget(self.preview_bg_combo, 1)
        self.overlay_btn = QtWidgets.QPushButton("패턴 표시(뷰어)")
        self.overlay_btn.setCheckable(True)
        self.overlay_btn.toggled.connect(self._show_pattern_on_viewer)
        bg_row.addWidget(self.overlay_btn)
        self.overlay_status = QtWidgets.QLabel("")
        self.overlay_status.setStyleSheet("color: gray;")
        bg_row.addWidget(self.overlay_status, 2)
        preview_wrap.addLayout(bg_row)
        layout.addLayout(point_btn_row)
        layout.addWidget(self.table)
        layout.addLayout(preview_wrap)
        btn_row = QtWidgets.QHBoxLayout()
        btn_row.addStretch()
        self.save_btn = QtWidgets.QPushButton("저장")
        self.close_btn = QtWidgets.QPushButton("닫기")
        btn_row.addWidget(self.save_btn)
        btn_row.addWidget(self.close_btn)
        layout.addLayout(btn_row)
        # Signals
        self.add_btn.clicked.connect(self._add_pattern)
        self.dup_btn.clicked.connect(self._dup_pattern)
        self.del_btn.clicked.connect(self._del_pattern)
        self.add_point_btn.clicked.connect(self._add_point_from_cursor)
        self.del_point_btn.clicked.connect(self._del_points)
        self.clear_point_btn.clicked.connect(self._clear_points)
        self.save_btn.clicked.connect(self._save_and_mark_dirty)
        self.close_btn.clicked.connect(self.accept)
        QtGui.QShortcut(
            QtGui.QKeySequence("F3"),
            self,
            self._add_point_from_cursor,
            context=QtCore.Qt.ShortcutContext.ApplicationShortcut,
        )
        self.resize(520, 640)
    def _load_patterns(self):
        self._loading_patterns = True
        self.list_widget.setRowCount(0)
        self._anchor_image_pos = None
        self._overlay_visible = False
        self.overlay_btn.setChecked(False)
        self.overlay_status.setText("")
        for row, name in enumerate(sorted(self.patterns.keys())):
            pat = self.patterns.get(name)
            self.list_widget.insertRow(row)
            self.list_widget.setItem(row, 0, QtWidgets.QTableWidgetItem(name))
            self.list_widget.setItem(row, 1, QtWidgets.QTableWidgetItem(pat.description or "" if pat else ""))
        self._loading_patterns = False
        if self.list_widget.rowCount() > 0:
            self.list_widget.setCurrentCell(0, 0)
            # 초기 로드시에도 상세정보를 채워 넣는다.
            self._on_select_pattern_cell(0, 0, -1, -1)
        else:
            # 아무 패턴도 없을 때 UI를 깨끗이 비워 두어 저장 버튼이 패턴을 재생성하지 않도록 한다.
            self._current_name = None
            self.name_edit.clear()
            self.desc_edit.clear()
            self.table.setRowCount(0)
            self._highlight_dx_dy = None
            self.preview_label.setPixmap(QtGui.QPixmap())
            self.preview_label.setText("포인트 없음")
            self.size_label.setText("")
    def _current_pattern(self) -> PixelPattern:
        if not self._current_name or self._current_name not in self.patterns:
            cur_row = self.list_widget.currentRow()
            self._current_name = self.list_widget.item(cur_row, 0).text() if cur_row >= 0 else None
        if self._current_name and self._current_name in self.patterns:
            return copy.deepcopy(self._sanitize_pattern(self.patterns[self._current_name]))
        pat = PixelPattern(name="pattern1", points=[], tolerance=0)
        pat = self._sanitize_pattern(pat)
        self.patterns[pat.name] = copy.deepcopy(pat)
        self._current_name = pat.name
        # 리스트가 비어 있을 때 최초 패턴을 UI에도 반영해 사용자가 바로 볼 수 있게 한다.
        if self.list_widget.rowCount() == 0:
            self.list_widget.insertRow(0)
            self.list_widget.setItem(0, 0, QtWidgets.QTableWidgetItem(pat.name))
            self.list_widget.setItem(0, 1, QtWidgets.QTableWidgetItem(pat.description or ""))
            self.list_widget.setCurrentCell(0, 0)
        return pat
    def _save_current_pattern(self, *, name_hint: str | None = None, keep_name: bool = False):
        # name_hint: 저장 대상 패턴명(이전 선택 항목). 없으면 현재 이름을 사용.
        if not self.patterns and self.list_widget.rowCount() == 0 and not (self._current_name or name_hint):
            return
        old_name = name_hint or self._current_name
        if not old_name:
            return
        pat = copy.deepcopy(self.patterns.get(old_name) or self._current_pattern())
        new_name = pat.name  # 이름/설명은 목록 더블클릭 모달에서만 변경
        if new_name != old_name and new_name in self.patterns:
            # 이름 충돌 시 접미사 부여
            base = new_name
            i = 2
            while f"{base}_{i}" in self.patterns:
                i += 1
            new_name = f"{base}_{i}"
        pat.name = new_name
        # 설명은 모달에서만 수정
        pat.tolerance = 0
        anchor_x, anchor_y = self._anchor_image_pos or (0, 0)
        new_points: list[PixelPatternPoint] = []
        for row in range(self.table.rowCount()):
            item_x = self.table.item(row, 0)
            item_y = self.table.item(row, 1)
            item_c = self.table.item(row, 2)
            if not item_x or not item_y or not item_c:
                continue
            try:
                x_val = int(item_x.text())
                y_val = int(item_y.text())
                color_txt = item_c.text().strip().lstrip("#")
                if len(color_txt) != 6:
                    continue
                color = tuple(int(color_txt[i : i + 2], 16) for i in (0, 2, 4))
            except Exception:
                continue
            dx = x_val - anchor_x
            dy = y_val - anchor_y
            new_points.append(PixelPatternPoint(dx=dx, dy=dy, color=color, tolerance=None))
        if new_points:
            pat.points = new_points
        pat = copy.deepcopy(pat.normalized())
        self.patterns.pop(old_name, None)
        self.patterns[pat.name] = pat
        # 리스트 항목 텍스트 갱신
        for i in range(self.list_widget.rowCount()):
            item = self.list_widget.item(i, 0)
            if item and item.text() == old_name:
                item.setText(pat.name)
                desc_item = self.list_widget.item(i, 1)
                if desc_item:
                    desc_item.setText(pat.description or "")
                break
        self._current_name = pat.name
        if self.list_widget.currentRow() < 0:
            self._select_by_name(pat.name)
        # 엔진과 공용 패턴 저장소에 즉시 반영해 다른 창에서도 곧바로 보이게 한다.
        self._push_patterns_to_owner()
    def _select_by_name(self, name: str):
        for i in range(self.list_widget.rowCount()):
            item = self.list_widget.item(i, 0)
            if item and item.text() == name:
                prev = self.list_widget.blockSignals(True)
                self.list_widget.setCurrentCell(i, 0)
                self.list_widget.blockSignals(prev)
                break
    def _row_name(self, row: int) -> str | None:
        if row < 0:
            return None
        item = self.list_widget.item(row, 0)
        return item.text() if item else None
    def _display_pattern(self, pat: PixelPattern):
        pat = self._sanitize_pattern(pat)
        self._current_name = pat.name
        self._anchor_pos = None
        self._anchor_image_pos = (0, 0)
        self._highlight_dx_dy = None
        self.table.setRowCount(0)
        for pt in pat.points:
            self._append_point_row(pt.dx, pt.dy, pt.color, pt.tolerance)
        self._update_preview()
    def _on_select_pattern_cell(self, cur_row: int, _cur_col: int, prev_row: int, _prev_col: int):
        if self._loading_patterns:
            return
        if cur_row < 0:
            return
        if prev_row >= 0:
            try:
                prev_name = self._row_name(prev_row)
                keep_name = getattr(self, "_keep_name_on_next_save", False)
                self._keep_name_on_next_save = False
                self._save_current_pattern(name_hint=prev_name, keep_name=keep_name)
            except Exception:
                pass
        else:
            self._keep_name_on_next_save = False
        name = self._row_name(cur_row)
        if not name:
            return
        if name not in self.patterns:
            self.patterns[name] = PixelPattern(name=name, points=[], tolerance=0)
        self._current_name = name
        pat = copy.deepcopy(self._sanitize_pattern(self.patterns[name]))
        self.name_edit.setText(pat.name)
        self.desc_edit.setText(pat.description or "")
        self.tol_spin.setValue(0)
        self._display_pattern(pat)
    def _append_point_row(self, dx: int, dy: int, color: RGB, tol: Optional[int] = None):
        self._loading_points = True
        row = self.table.rowCount()
        self.table.insertRow(row)
        anchor_x, anchor_y = self._anchor_image_pos or (0, 0)
        display_x = anchor_x + dx
        display_y = anchor_y + dy
        for col, val in enumerate(
            [display_x, display_y, f"{color[0]:02x}{color[1]:02x}{color[2]:02x}"]
        ):
            item = QtWidgets.QTableWidgetItem(str(val))
            self.table.setItem(row, col, item)
        # 삭제 버튼
        del_btn = QtWidgets.QPushButton("X")
        del_btn.setFixedWidth(24)
        del_btn.clicked.connect(lambda _, b=del_btn: self._delete_point_row(b))
        self.table.setCellWidget(row, 3, del_btn)
        self._loading_points = False
        self.table.resizeRowsToContents()
    def _prompt_new_pattern(self) -> tuple[str, str | None] | None:
        dlg = QtWidgets.QDialog(self)
        dlg.setWindowTitle("새 패턴")
        dlg.setModal(True)
        vbox = QtWidgets.QVBoxLayout(dlg)
        form = QtWidgets.QFormLayout()
        name_edit = QtWidgets.QLineEdit()
        name_edit.setText(self._next_default_name())
        desc_edit = QtWidgets.QLineEdit()
        form.addRow("이름", name_edit)
        form.addRow("설명", desc_edit)
        vbox.addLayout(form)
        btns = QtWidgets.QDialogButtonBox(QtWidgets.QDialogButtonBox.StandardButton.Ok | QtWidgets.QDialogButtonBox.StandardButton.Cancel)
        vbox.addWidget(btns)
        btns.accepted.connect(dlg.accept)
        btns.rejected.connect(dlg.reject)
        while True:
            if dlg.exec() != QtWidgets.QDialog.DialogCode.Accepted:
                return None
            name = name_edit.text().strip()
            if not name:
                QtWidgets.QMessageBox.warning(self, "이름 필요", "패턴 이름을 입력하세요.")
                continue
            return name, (desc_edit.text().strip() or None)
    def _next_default_name(self) -> str:
        base = "pattern"
        idx = 1
        while f"{base}{idx}" in self.patterns:
            idx += 1
        return f"{base}{idx}"
    def _add_pattern(self):
        # 현재 선택 패턴은 이름을 보존한 채 먼저 저장
        try:
            self._save_current_pattern(name_hint=self._current_name, keep_name=True)
        except Exception:
            pass
        self._keep_name_on_next_save = False
        result = self._prompt_new_pattern()
        if result is None:
            return
        desired, desc = result
        name = desired
        if name in self.patterns:
            base = name
            i = 2
            while f"{base}_{i}" in self.patterns:
                i += 1
            name = f"{base}_{i}"
        pat = PixelPattern(name=name, points=[], tolerance=0, description=desc)
        pat = self._sanitize_pattern(pat)
        self.patterns[name] = pat
        row = self.list_widget.rowCount()
        self.list_widget.insertRow(row)
        self.list_widget.setItem(row, 0, QtWidgets.QTableWidgetItem(name))
        self.list_widget.setItem(row, 1, QtWidgets.QTableWidgetItem(desc or ""))
        # 선택 전 신호를 일시 차단해 이전 패턴 데이터를 새 패턴에 섞지 않는다.
        prev = self.list_widget.blockSignals(True)
        self.list_widget.setCurrentCell(row, 0)
        self.list_widget.blockSignals(prev)
        self.name_edit.setText(name)
        self.desc_edit.setText(desc or "")
        self._display_pattern(pat)
        # 즉시 저장해 다른 창/세션에서도 바로 보이도록 한다.
        self._push_patterns_to_owner()
    def _edit_pattern_meta_dialog(self, row: int, _col: int):
        name = self._row_name(row)
        if not name or name not in self.patterns:
            return
        pat = self.patterns[name]
        dlg = QtWidgets.QDialog(self)
        dlg.setWindowTitle("패턴 정보 수정")
        dlg.setModal(True)
        vbox = QtWidgets.QVBoxLayout(dlg)
        form = QtWidgets.QFormLayout()
        name_edit = QtWidgets.QLineEdit()
        name_edit.setText(name)
        desc_edit = QtWidgets.QLineEdit()
        desc_edit.setText(pat.description or "")
        form.addRow("이름", name_edit)
        form.addRow("설명", desc_edit)
        vbox.addLayout(form)
        btns = QtWidgets.QDialogButtonBox(QtWidgets.QDialogButtonBox.StandardButton.Ok | QtWidgets.QDialogButtonBox.StandardButton.Cancel)
        vbox.addWidget(btns)
        btns.accepted.connect(dlg.accept)
        btns.rejected.connect(dlg.reject)
        if dlg.exec() != QtWidgets.QDialog.DialogCode.Accepted:
            return
        new_name = name_edit.text().strip() or name
        if new_name != name and new_name in self.patterns:
            base = new_name
            i = 2
            while f"{base}_{i}" in self.patterns:
                i += 1
            new_name = f"{base}_{i}"
        new_desc = desc_edit.text().strip() or None
        if new_name != name:
            self.patterns.pop(name, None)
        pat.name = new_name
        pat.description = new_desc
        self.patterns[new_name] = pat
        self._current_name = new_name
        self._load_patterns()
        self._select_by_name(new_name)
        self._push_patterns_to_owner()
    def _dup_pattern(self):
        pat = self._current_pattern()
        new_name = pat.name + "_copy"
        i = 1
        while new_name in self.patterns:
            new_name = f"{pat.name}_copy{i}"
            i += 1
        self.patterns[new_name] = PixelPattern(
            name=new_name,
            points=copy.deepcopy(pat.points),
            tolerance=0,
            description=pat.description,
        )
        self._load_patterns()
        self._select_by_name(new_name)
        self._push_patterns_to_owner()
    def _del_pattern(self):
        if self._current_name and self._current_name in self.patterns:
            self.patterns.pop(self._current_name, None)
        self._load_patterns()
        self._push_patterns_to_owner()
    def _add_point_from_cursor(self):
        if self.list_widget.rowCount() == 0:
            self._load_patterns()
        if self.list_widget.currentRow() < 0 and self.list_widget.rowCount() > 0:
            self.list_widget.setCurrentCell(0, 0)
        sample = None
        if callable(self._sample_provider):
            try:
                sample = self._sample_provider()
            except Exception:
                sample = None
        if sample and isinstance(sample, dict) and sample.get("pos") is not None:
            x, y = sample.get("pos")
            qcolor = sample.get("color")
            if isinstance(qcolor, QtGui.QColor):
                color = (qcolor.red(), qcolor.green(), qcolor.blue())
            else:
                color = tuple(int(c) for c in sample.get("color", (0, 0, 0)))[:3]
        else:
            pos = QtGui.QCursor.pos()
            x, y = pos.x(), pos.y()
            try:
                img = capture_region((x, y, 1, 1)).convert("RGB")
                color = img.getpixel((0, 0))
            except Exception:
                QtWidgets.QMessageBox.warning(self, "캡처 실패", "현재 커서 위치 픽셀을 읽지 못했습니다.")
                return
        pat = self._current_pattern()
        if self._anchor_image_pos is None or not pat.points:
            self._anchor_image_pos = (int(x), int(y))
        anchor_x, anchor_y = self._anchor_image_pos
        dx = int(x) - anchor_x
        dy = int(y) - anchor_y
        self._append_point_row(int(dx), int(dy), color)
        # 새로 추가된 행을 선택해 즉시 눈에 보이도록
        row = self.table.rowCount() - 1
        if row >= 0:
            self.table.selectRow(row)
            self.table.scrollToItem(self.table.item(row, 0), QtWidgets.QAbstractItemView.ScrollHint.PositionAtCenter)
        self._update_preview()
        QtWidgets.QToolTip.showText(
            QtGui.QCursor.pos(),
            f"추가: x={x}, y={y}, #{color[0]:02x}{color[1]:02x}{color[2]:02x}",
            self,
        )
    def _del_points(self):
        rows = sorted({idx.row() for idx in self.table.selectedIndexes()}, reverse=True)
        for r in rows:
            self.table.removeRow(r)
        self._update_preview()
    def _clear_points(self):
        self.table.setRowCount(0)
        self._anchor_pos = None
        self._anchor_image_pos = None
        self._highlight_dx_dy = None
        self._update_preview()
    def _delete_point_row(self, button: QtWidgets.QPushButton):
        for r in range(self.table.rowCount()):
            if self.table.cellWidget(r, 3) is button:
                self.table.removeRow(r)
                break
        self._highlight_dx_dy = None
        self._update_preview()
    def _highlight_selected_point(self):
        if self._loading_points:
            return
        sel = self.table.selectedIndexes()
        if not sel:
            self._highlight_dx_dy = None
            self._update_preview()
            return
        row = sel[0].row()
        try:
            pat = self._current_pattern()
            norm = pat.normalized()
            if 0 <= row < len(norm.points):
                pt = norm.points[row]
                self._highlight_dx_dy = (int(pt.dx), int(pt.dy))
            else:
                self._highlight_dx_dy = None
        except Exception:
            self._highlight_dx_dy = None
        self._update_preview()
    def _update_preview(self):
        if self._loading_points:
            return
        try:
            self._save_current_pattern()
        except Exception:
            pass
        pat = self._current_pattern()
        norm = pat.normalized()
        if not norm.points:
            self.preview_label.setText("포인트 없음")
            self.size_label.setText("")
            # 오버레이도 제거
            viewer = getattr(self._owner, "_image_viewer_dialog", None)
            if viewer and hasattr(viewer, "canvas"):
                try:
                    viewer.canvas.set_overlays([])
                except Exception:
                    pass
            self.overlay_status.setText("")
            self._overlay_visible = False
            return
        max_dx = max(p.dx for p in norm.points)
        max_dy = max(p.dy for p in norm.points)
        w = max_dx + 1
        h = max_dy + 1
        margin = 2  # preview padding in pixels (pre-scale)
        scale = max(4, min(16, 160 // max(1, max(w, h))))
        img_w = (w + margin * 2) * scale
        img_h = (h + margin * 2) * scale
        img = QtGui.QImage(img_w, img_h, QtGui.QImage.Format.Format_ARGB32)
        img.fill(QtCore.Qt.GlobalColor.transparent)
        painter = QtGui.QPainter(img)
        bg_mode = self.preview_bg_combo.currentText()
        if bg_mode == "체커보드":
            checker = QtGui.QColor(220, 220, 220, 80)
            for y in range(0, h * scale, scale):
                for x in range(0, w * scale, scale):
                    if ((x // scale) + (y // scale)) % 2 == 0:
                        painter.fillRect((x + margin * scale), (y + margin * scale), scale, scale, checker)
        else:
            color_map = {
                "검정": QtGui.QColor(0, 0, 0),
                "흰색": QtGui.QColor(255, 255, 255),
                "주황": QtGui.QColor(255, 180, 80),
            }
            painter.fillRect(
                margin * scale,
                margin * scale,
                w * scale,
                h * scale,
                color_map.get(bg_mode, QtGui.QColor(220, 220, 220, 80)),
            )
        for pt in norm.points:
            color = QtGui.QColor(int(pt.color[0]), int(pt.color[1]), int(pt.color[2]))
            painter.fillRect((pt.dx + margin) * scale, (pt.dy + margin) * scale, scale, scale, color)
        if self._highlight_dx_dy:
            hx, hy = self._highlight_dx_dy
            pen = QtGui.QPen(QtGui.QColor(255, 64, 64, 180))
            pen.setWidth(max(1, scale // 6))
            painter.setPen(pen)
            painter.drawRect((hx + margin) * scale, (hy + margin) * scale, scale, scale)
        painter.end()
        self.preview_label.setPixmap(QtGui.QPixmap.fromImage(img))
        self.size_label.setText(f"크기: {w} x {h}, 포인트 {len(norm.points)}개")
        # 미리보기 갱신 후 오버레이도 최신으로
        if self.overlay_btn.isChecked():
            self._show_pattern_on_viewer()
    def accept(self):
        try:
            row = self.list_widget.currentRow()
            if row >= 0:
                self._current_name = self._row_name(row)
            self._save_current_pattern(name_hint=self._current_name)
        except Exception:
            pass
        return super().accept()
    def _save_and_mark_dirty(self):
        try:
            row = self.list_widget.currentRow()
            if row >= 0:
                self._current_name = self._row_name(row)
            self._save_current_pattern(name_hint=self._current_name)
            self.overlay_status.setText("패턴 저장됨")
        except Exception:
            pass
    def _toggle_stay_on_top(self, checked: bool):
        self.setWindowFlag(QtCore.Qt.WindowType.WindowStaysOnTopHint, checked)
        self.show()
    def _open_viewer(self):
        if callable(self._open_image_viewer):
            try:
                self._open_image_viewer()
            except Exception:
                pass
        elif self._owner and hasattr(self._owner, "_open_image_viewer_dialog"):
            try:
                self._owner._open_image_viewer_dialog()
            except Exception:
                pass
        # 새로 열린 뷰어에도 리스너를 연결한다.
        QtCore.QTimer.singleShot(0, self._ensure_viewer_listener)
    def _show_pattern_on_viewer(self):
        self._ensure_viewer_listener()
        self._overlay_visible = self.overlay_btn.isChecked()
        pat = self._current_pattern()
        viewer = getattr(self._owner, "_image_viewer_dialog", None)
        if viewer is None or not hasattr(viewer, "canvas"):
            self.overlay_status.setText("이미지 뷰어 없음")
            return
        if not self.overlay_btn.isChecked():
            viewer.canvas.set_overlays([])
            self.overlay_status.setText("패턴 표시 꺼짐")
            return
        if not pat.points:
            self.overlay_status.setText("패턴 없음")
            viewer.canvas.set_overlays([])
            return
        # 매칭: 현재 뷰어 이미지에서 패턴 존재 위치를 찾는다.
        qimg = getattr(viewer.canvas, "_image", None)
        if qimg is None or qimg.isNull():
            self.overlay_status.setText("이미지가 없습니다")
            viewer.canvas.set_overlays([])
            return
        matches = self._find_pattern_in_qimage(qimg, pat)
        if not matches:
            self.overlay_status.setText("패턴을 찾지 못했습니다")
            viewer.canvas.set_overlays([])
            return
        rects: list[tuple[int, int, int, int]] = []
        for mx, my in matches:
            for pt in pat.points:
                rects.append((mx + int(pt.dx), my + int(pt.dy), 1, 1))
        viewer.canvas.set_overlays(rects)
        viewer.canvas.update()
        self.overlay_status.setText(f"패턴 {len(matches)}곳 표시")
    @staticmethod
    def _find_pattern_in_qimage(qimg: QtGui.QImage, pattern: PixelPattern) -> list[tuple[int, int]]:
        """Return list of (x,y) top-left matches within the image."""
        if qimg.isNull() or not pattern.points:
            return []
        norm = pattern.normalized()
        w = qimg.width()
        h = qimg.height()
        max_dx = max(p.dx for p in norm.points)
        max_dy = max(p.dy for p in norm.points)
        if w - max_dx <= 0 or h - max_dy <= 0:
            return []
        # Convert qimage to numpy uint8 HxWx4 then to RGB
        fmt = qimg.format()
        if fmt != QtGui.QImage.Format.Format_RGBA8888:
            qimg = qimg.convertToFormat(QtGui.QImage.Format.Format_RGBA8888)
        ptr = qimg.bits()
        ptr.setsize(qimg.sizeInBytes())
        import numpy as np
        arr = np.frombuffer(ptr, np.uint8).reshape((h, qimg.bytesPerLine() // 4, 4))
        arr = arr[:, : w, :3]
        matches: list[tuple[int, int]] = []
        tol_default = 0
        pts = norm.points
        # vectorized search for speed: precompute per-point tolerance mask
        arr_i16 = arr.astype(np.int16)
        for y in range(0, h - max_dy):
            window = arr_i16[y : y + max_dy + 1, 0 : w - max_dx, :]
            # Start with all columns valid
            valid = np.ones(window.shape[:2], dtype=bool)
            for pt in pts:
                tol = tol_default
                sub = window[pt.dy, pt.dx : pt.dx + window.shape[1], :]
                diff = np.abs(sub - np.array(pt.color, dtype=np.int16))
                cond = (diff <= tol).all(axis=1)
                valid[: cond.shape[0], : cond.shape[0]] &= cond  # align lengths
            ys, xs = np.where(valid)
            for xv in xs:
                matches.append((int(xv), int(y)))
        return matches
    def _on_viewer_changed(self, *_):
        # 이미지가 바뀌거나 샘플이 변하면 자동으로 오버레이를 끈다.
        self.overlay_btn.setChecked(False)
        viewer = getattr(self._owner, "_image_viewer_dialog", None)
        if viewer and hasattr(viewer, "canvas"):
            try:
                viewer.canvas.set_overlays([])
            except Exception:
                pass
        self.overlay_status.setText("이미지 변경: 패턴 표시 꺼짐")
    def _push_patterns_to_owner(self):
        """엔진과 공용 패턴 파일에 현재 패턴을 즉시 반영해 재열 때 사라지지 않도록 한다."""
        try:
            if self._owner and hasattr(self._owner, "engine"):
                self._owner.engine._pixel_patterns = copy.deepcopy(self.patterns)
            _save_shared_patterns(self.patterns)
        except Exception:
            pass
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
        pattern_provider=None,
        open_pattern_manager=None,
    ):
        super().__init__(parent)
        self.setWindowTitle("픽셀 테스트")
        self.setModal(True)
        self.setWindowModality(QtCore.Qt.WindowModality.WindowModal)
        self._resolver_provider = resolver_provider
        self._start_test = start_test
        self._stop_test = stop_test
        self._save_state_cb = save_state_cb
        self._pattern_provider = pattern_provider
        self._open_pattern_manager = open_pattern_manager
        self._testing = False
        self._build_ui()
        self._load_state(state or {})
    def _build_ui(self):
        layout = QtWidgets.QVBoxLayout(self)
        form = QtWidgets.QFormLayout()
        self._form = form
        self.region_edit = QtWidgets.QLineEdit("0,0,100,100")
        _attach_variable_completer(self.region_edit, [])
        self.color_edit = QtWidgets.QLineEdit("ff0000")
        _setup_hex_line_edit(self.color_edit)
        self.color_preview = _make_hex_preview_label()
        self.color_edit.textChanged.connect(lambda txt: _update_hex_preview_label(self.color_preview, txt))
        _update_hex_preview_label(self.color_preview, self.color_edit.text())
        _attach_variable_completer(self.color_edit, [])
        self.pattern_check = QtWidgets.QCheckBox("패턴 사용")
        self.pattern_combo = QtWidgets.QComboBox()
        self.pattern_manage_btn = QtWidgets.QPushButton("패턴 관리")
        self.pattern_manage_btn.clicked.connect(self._open_pattern_manager_cb)
        self.pattern_check.stateChanged.connect(self._sync_pattern_visibility)
        self._reload_patterns()
        self.tol_spin = QtWidgets.QSpinBox()
        self.tol_spin.setRange(0, 255)
        self.tol_spin.setValue(10)
        self.min_count_spin = QtWidgets.QSpinBox()
        self.min_count_spin.setRange(1, 100000)
        self.min_count_spin.setValue(1)
        self.min_count_spin.setToolTip("허용오차를 만족해야 하는 최소 픽셀 개수입니다.")
        self.expect_combo = QtWidgets.QComboBox()
        self.expect_combo.addItem("색상이 있을 때 참", True)
        self.expect_combo.addItem("색상이 없을 때 참", False)
        self.expect_combo.currentIndexChanged.connect(self._sync_expect_visibility)
        self.interval_spin = QtWidgets.QSpinBox()
        self.interval_spin.setRange(50, 5000)
        self.interval_spin.setSuffix(" ms")
        self.interval_spin.setValue(200)
        form.addRow("Region x,y,w,h", self.region_edit)
        color_row = QtWidgets.QHBoxLayout()
        color_row.setContentsMargins(0, 0, 0, 0)
        color_row.setSpacing(6)
        color_row.addWidget(self.color_edit, 1)
        color_row.addWidget(self.color_preview)
        color_wrap = QtWidgets.QWidget()
        color_wrap.setLayout(color_row)
        self.color_wrap = color_wrap
        form.addRow("색상", color_wrap)
        pattern_row = QtWidgets.QHBoxLayout()
        pattern_row.setContentsMargins(0, 0, 0, 0)
        pattern_row.setSpacing(6)
        pattern_row.addWidget(self.pattern_check)
        pattern_row.addWidget(self.pattern_combo, 1)
        pattern_row.addWidget(self.pattern_manage_btn)
        pattern_wrap = QtWidgets.QWidget()
        pattern_wrap.setLayout(pattern_row)
        form.addRow("패턴", pattern_wrap)
        form.addRow("Tolerance", self.tol_spin)
        form.addRow("최소 일치 픽셀 수", self.min_count_spin)
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
        self._sync_expect_visibility()
    def _reload_patterns(self):
        self.pattern_combo.clear()
        self.pattern_combo.addItem("선택 안 함", None)
        names = []
        if callable(self._pattern_provider):
            try:
                names = self._pattern_provider() or []
            except Exception:
                names = []
        for name in names:
            self.pattern_combo.addItem(str(name), str(name))
        self._sync_pattern_visibility()
    def _open_pattern_manager_cb(self):
        if callable(self._open_pattern_manager):
            try:
                self._open_pattern_manager(parent=self)
            except Exception:
                pass
        self._reload_patterns()
    def _sync_pattern_visibility(self):
        use_pat = self.pattern_check.isChecked()
        self.color_wrap.setVisible(not use_pat)
        form = getattr(self, "_form", None)
        if form is not None:
            lbl_color = form.labelForField(self.color_wrap)
            if lbl_color is not None:
                lbl_color.setVisible(not use_pat)
            lbl_min = form.labelForField(getattr(self, "min_count_spin", None))
            if lbl_min is not None:
                lbl_min.setVisible(not use_pat)
        self.color_edit.setEnabled(not use_pat)
        self.color_preview.setEnabled(not use_pat)
        if hasattr(self, "min_count_spin"):
            self.min_count_spin.setVisible(not use_pat)
            self.min_count_spin.setEnabled(not use_pat)
            lbl = self._form.labelForField(self.min_count_spin) if hasattr(self, "_form") else None
            if lbl is not None:
                lbl.setVisible(not use_pat)
    def _sync_expect_visibility(self):
        allow_min = bool(self.expect_combo.currentData()) if self.expect_combo.currentIndex() >= 0 else True
        self.min_count_spin.setEnabled(allow_min)
        lbl = self._form.labelForField(self.min_count_spin) if hasattr(self, "_form") else None
        if lbl is not None:
            lbl.setEnabled(allow_min)
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
        use_pattern = self.pattern_check.isChecked()
        pattern_name = self.pattern_combo.currentData() if use_pattern else None
        color = None if use_pattern else _parse_hex_color(self.color_edit.text(), resolver=resolver)
        tolerance = int(self.tol_spin.value())
        expect_exists = bool(self.expect_combo.currentData()) if self.expect_combo.currentIndex() >= 0 else True
        min_count = max(1, int(self.min_count_spin.value())) if expect_exists else 1
        return region, color, pattern_name, tolerance, expect_exists, min_count
    def _toggle_test(self):
        if self._testing:
            self._stop_testing()
            return
        try:
            region, color, pattern_name, tol, expect, min_count = self._parse_inputs()
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
            "pattern": pattern_name,
            "tolerance": tol,
            "expect_exists": expect,
            "min_count": min_count,
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
        try:
            min_cnt = int(state.get("min_count", 1))
            self.min_count_spin.setValue(max(1, min_cnt))
        except Exception:
            pass
        expect = state.get("expect_exists")
        if expect is not None:
            idx = self.expect_combo.findData(bool(expect))
            if idx >= 0:
                self.expect_combo.setCurrentIndex(idx)
        pat = state.get("pattern")
        if pat is not None:
            idxp = self.pattern_combo.findData(pat)
            if idxp >= 0:
                self.pattern_combo.setCurrentIndex(idxp)
                self.pattern_check.setChecked(True)
        self._sync_pattern_visibility()
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
            "min_count": int(self.min_count_spin.value()),
            "interval": int(self.interval_spin.value()),
            "pattern": self.pattern_combo.currentData() if self.pattern_check.isChecked() else None,
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
        sample_preset_state: dict | None = None,
        save_sample_preset_state=None,
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
        self._sample_preset_state = sample_preset_state or {}
        self._save_sample_preset_state_cb = save_sample_preset_state
        self._sample_preset_path: str | None = None
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
        preset_row = QtWidgets.QHBoxLayout()
        self.sample_preset_label = QtWidgets.QLabel("불러온 좌표 프리셋: (없음)")
        self.sample_preset_label.setStyleSheet("color: gray;")
        preset_row.addWidget(self.sample_preset_label, 1)
        self.sample_preset_load_btn = QtWidgets.QPushButton("좌표 프리셋 불러오기")
        self.sample_preset_save_btn = QtWidgets.QPushButton("좌표 프리셋 저장")
        preset_row.addWidget(self.sample_preset_load_btn)
        preset_row.addWidget(self.sample_preset_save_btn)
        layout.addLayout(preset_row)
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
        self.sample_preset_load_btn.clicked.connect(self._on_load_sample_preset)
        self.sample_preset_save_btn.clicked.connect(self._on_save_sample_preset)
        self.add_sample_btn.clicked.connect(self._add_sample_row)
        self.del_sample_btn.clicked.connect(self._remove_sample_rows)
        self.calc_sample_btn.clicked.connect(self._on_calc_samples)
        self.sample_test_btn.clicked.connect(self._on_test_sample_point)
        self.sample_test_input.returnPressed.connect(self._on_test_sample_point)
        self._apply_initial_samples()
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
    def _apply_initial_samples(self):
        preset_state = self._sample_preset_state if isinstance(self._sample_preset_state, dict) else {}
        preset_path = preset_state.get("path")
        preset_samples = self._normalize_sample_list(preset_state.get("samples"))
        if preset_path and Path(preset_path).exists():
            if self._load_sample_preset_from_path(preset_path, silent=True, remember=False):
                return
        if preset_samples:
            self._sample_preset_path = str(preset_path) if preset_path else None
            self._set_sample_rows(preset_samples)
            self._update_sample_preset_label(self._sample_preset_path, True)
            return
        self._set_sample_rows([])
        self._update_sample_preset_label(None, False)
    def _set_sample_rows(self, samples: list[tuple[float, float, float, float]]):
        self.sample_table.setRowCount(0)
        for sample in samples:
            self._add_sample_row(sample)
        if not samples:
            for _ in range(2):
                self._add_sample_row()
        try:
            self.sample_test_btn.setEnabled(False)
            self.sample_test_result.setText("결과: -")
        except Exception:
            pass
        self._last_sample_calc = None
        try:
            self.sample_result_label.setText("계수: a/b/c/d, RMS: -")
            self.sample_preview.setPlainText("")
        except Exception:
            pass
    def _update_sample_preset_label(self, path: str | None, has_samples: bool):
        if not isinstance(getattr(self, "sample_preset_label", None), QtWidgets.QLabel):
            return
        if path:
            name = Path(path).name
            self.sample_preset_label.setText(f"불러온 좌표 프리셋: {name}")
            self.sample_preset_label.setToolTip(str(path))
            self.sample_preset_label.setStyleSheet("")
        elif has_samples:
            self.sample_preset_label.setText("불러온 좌표 프리셋: (파일 없음)")
            self.sample_preset_label.setToolTip("")
            self.sample_preset_label.setStyleSheet("color: gray;")
        else:
            self.sample_preset_label.setText("불러온 좌표 프리셋: (없음)")
            self.sample_preset_label.setToolTip("")
            self.sample_preset_label.setStyleSheet("color: gray;")
    def _sample_preset_dir(self) -> Path:
        if self._sample_preset_path:
            try:
                return Path(self._sample_preset_path).parent
            except Exception:
                pass
        if self._profile_path:
            try:
                return self._profile_path.parent
            except Exception:
                pass
        return Path.cwd()
    @staticmethod
    def _normalize_sample_list(raw) -> list[tuple[float, float, float, float]]:
        items = None
        if isinstance(raw, dict):
            if isinstance(raw.get("samples"), list):
                items = raw.get("samples")
            elif isinstance(raw.get("transform_matrix"), dict):
                tm = raw.get("transform_matrix") or {}
                if isinstance(tm.get("samples"), list):
                    items = tm.get("samples")
        elif isinstance(raw, list):
            items = raw
        result: list[tuple[float, float, float, float]] = []
        if not isinstance(items, list):
            return result
        for item in items:
            try:
                src = None
                dst = None
                if isinstance(item, dict):
                    src = item.get("src") or item.get("source") or item.get("base") or item.get("from")
                    dst = item.get("dst") or item.get("target") or item.get("to")
                elif isinstance(item, (list, tuple)):
                    if len(item) == 2 and all(isinstance(p, (list, tuple)) for p in item):
                        src, dst = item[0], item[1]
                    elif len(item) == 4:
                        src, dst = item[:2], item[2:]
                if not (isinstance(src, (list, tuple)) and isinstance(dst, (list, tuple))):
                    continue
                if len(src) < 2 or len(dst) < 2:
                    continue
                sx, sy = float(src[0]), float(src[1])
                tx, ty = float(dst[0]), float(dst[1])
                result.append((sx, sy, tx, ty))
            except Exception:
                continue
        return result
    def _load_sample_preset_from_path(self, path: str, *, silent: bool = False, remember: bool = True) -> bool:
        try:
            data = json.loads(Path(path).read_text(encoding="utf-8"))
        except Exception as exc:
            if not silent:
                QtWidgets.QMessageBox.warning(self, "불러오기 실패", f"파일을 열 수 없습니다.\n{exc}")
            else:
                self._log(f"좌표 프리셋 로드 실패({path}): {exc}")
            return False
        samples = self._normalize_sample_list(data)
        if not samples:
            if not silent:
                QtWidgets.QMessageBox.warning(self, "불러오기 실패", "유효한 좌표 샘플을 찾을 수 없습니다.")
            else:
                self._log(f"좌표 프리셋 로드 실패({path}): 샘플 없음")
            return False
        self._sample_preset_path = str(path)
        self._set_sample_rows(samples)
        self._update_sample_preset_label(self._sample_preset_path, True)
        if remember:
            self._persist_sample_preset_state(samples)
        if not silent:
            self._log(f"좌표 프리셋 불러오기: {path} (샘플 {len(samples)}개)")
        return True
    def _on_load_sample_preset(self):
        start_dir = self._sample_preset_dir()
        path, _ = QtWidgets.QFileDialog.getOpenFileName(
            self, "좌표 프리셋 불러오기", str(start_dir), "Text Preset (*.txt);;JSON Files (*.json);;All Files (*.*)"
        )
        if not path:
            return
        self._load_sample_preset_from_path(path)
    def _on_save_sample_preset(self):
        try:
            samples = self._collect_samples()
        except ValueError as exc:
            QtWidgets.QMessageBox.warning(self, "입력 오류", str(exc))
            return
        default_dir = self._sample_preset_dir()
        default_name = (
            Path(self._sample_preset_path).name
            if self._sample_preset_path
            else (f"{self._profile_path.stem}_samples.txt" if self._profile_path else "sample_preset.txt")
        )
        default_path = default_dir / default_name
        path, _ = QtWidgets.QFileDialog.getSaveFileName(
            self, "좌표 프리셋 저장", str(default_path), "Text Preset (*.txt);;JSON Files (*.json);;All Files (*.*)"
        )
        if not path:
            return
        if not Path(path).suffix:
            path = f"{path}.txt"
        payload = {
            "type": "preset_transfer_samples",
            "version": 1,
            "samples": [{"src": [sx, sy], "dst": [tx, ty]} for sx, sy, tx, ty in samples],
            "meta": {
                "base_resolution": list(self._base_res_default) if self._base_res_default else None,
                "base_scale_percent": self._base_scale_default,
            },
        }
        try:
            Path(path).write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
        except Exception as exc:
            QtWidgets.QMessageBox.warning(self, "저장 실패", str(exc))
            return
        self._sample_preset_path = str(path)
        self._update_sample_preset_label(self._sample_preset_path, True)
        self._persist_sample_preset_state(samples)
        QtWidgets.QMessageBox.information(self, "저장 완료", f"좌표 프리셋을 저장했습니다.\n{path}")
        self._log(f"좌표 프리셋 저장: {path} (샘플 {len(samples)}개)")
    def _persist_sample_preset_state(self, samples: list[tuple[float, float, float, float]] | None):
        if not callable(self._save_sample_preset_state_cb):
            return
        payload = {
            "path": self._sample_preset_path,
            "samples": [{"src": [sx, sy], "dst": [tx, ty]} for sx, sy, tx, ty in (samples or [])],
        }
        self._sample_preset_state = payload
        try:
            self._save_sample_preset_state_cb(payload)
        except Exception:
            pass
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
class KeyboardRecordDialog(QtWidgets.QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("키보드 녹화")
        self.setModal(False)
        self.setWindowModality(QtCore.Qt.WindowModality.NonModal)
        self.resize(760, 460)
        self._queue: queue.Queue = queue.Queue()
        self._stop_event = threading.Event()
        self._listener_thread: threading.Thread | None = None
        self._timer = QtCore.QTimer(self)
        self._timer.setInterval(100)
        self._timer.timeout.connect(self._drain_queue)
        self._events: list[dict[str, Any]] = []
        self._prev_event_ts: float | None = None
        self._recordable_event_count: int = 0
        self._skipped_unknown_count: int = 0
        self._accepted_actions: list[Action] | None = None
        self._status_prefix: str = "키보드 녹화 대기중"
        self._hotkey_start: str = "pgup"
        self._hotkey_stop: str = "pgdown"
        self._hotkey_start_label: str = "PageUp"
        self._hotkey_stop_label: str = "PageDown"
        self._hotkey_start_prev = False
        self._hotkey_stop_prev = False
        self._hotkey_ready = False
        self._hotkey_release_polls = 0
        self._hotkey_release_polls_required = 2
        self._hotkey_start_streak = 0
        self._hotkey_stop_streak = 0
        self._hotkey_start_polls_required = 2
        self._hotkey_stop_polls_required = 1
        self._hotkey_initial_guard_until = time.monotonic() + 0.35
        self._build_ui()
        self._timer.start()
        self._hotkey_start_prev = self._safe_pressed(self._hotkey_start)
        self._hotkey_stop_prev = self._safe_pressed(self._hotkey_stop)
        self._hotkey_ready = False
        self._hotkey_release_polls = 0
        self._hotkey_timer = QtCore.QTimer(self)
        self._hotkey_timer.setInterval(35)
        self._hotkey_timer.timeout.connect(self._poll_hotkeys)
        self._hotkey_timer.start()
    def _build_ui(self):
        layout = QtWidgets.QVBoxLayout(self)
        self.status_label = QtWidgets.QLabel("")
        self.status_label.setWordWrap(True)
        layout.addWidget(self.status_label)
        hint = QtWidgets.QLabel(
            "다운/업 입력을 그대로 기록합니다. 적용 시 액션은 sleep + down/up 형태로 생성됩니다."
        )
        hint.setStyleSheet("color: #666;")
        hint.setWordWrap(True)
        layout.addWidget(hint)
        hotkey_hint = QtWidgets.QLabel(
            f"단축키: {self._hotkey_start_label}=녹화 시작, {self._hotkey_stop_label}=녹화 중지"
        )
        hotkey_hint.setStyleSheet("color: #666;")
        layout.addWidget(hotkey_hint)
        ctrl_row = QtWidgets.QHBoxLayout()
        self.toggle_btn = QtWidgets.QPushButton(self._toggle_btn_text(running=False))
        self.clear_btn = QtWidgets.QPushButton("초기화")
        ctrl_row.addWidget(self.toggle_btn)
        ctrl_row.addWidget(self.clear_btn)
        ctrl_row.addStretch()
        layout.addLayout(ctrl_row)
        self.table = QtWidgets.QTableWidget(0, 5)
        self.table.setHorizontalHeaderLabels(["시간", "키", "이벤트", "이전과 간격(ms)", "상세"])
        header = self.table.horizontalHeader()
        header.setSectionResizeMode(0, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(1, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(2, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(3, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        header.setStretchLastSection(True)
        self.table.verticalHeader().setVisible(False)
        self.table.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectionBehavior.SelectRows)
        self.table.setEditTriggers(QtWidgets.QAbstractItemView.EditTrigger.NoEditTriggers)
        self.table.setAlternatingRowColors(True)
        layout.addWidget(self.table, stretch=1)
        btn_row = QtWidgets.QHBoxLayout()
        btn_row.addStretch()
        self.apply_btn = QtWidgets.QPushButton("기록 적용")
        self.cancel_btn = QtWidgets.QPushButton("취소")
        btn_row.addWidget(self.apply_btn)
        btn_row.addWidget(self.cancel_btn)
        layout.addLayout(btn_row)
        self.toggle_btn.clicked.connect(self._toggle_listener)
        self.clear_btn.clicked.connect(self._clear_events)
        self.apply_btn.clicked.connect(self._accept_if_valid)
        self.cancel_btn.clicked.connect(self.reject)
        self._refresh_status()
    def _toggle_btn_text(self, *, running: bool) -> str:
        if running:
            return f"녹화 중지 ({self._hotkey_stop_label})"
        return f"녹화 시작 ({self._hotkey_start_label})"
    def _is_start_hotkey_key(self, key_name: str | None) -> bool:
        key = str(key_name or "").strip().lower()
        if not key:
            return False
        return key in {str(self._hotkey_start or "").strip().lower(), "pgup", "pageup"}
    def _is_stop_hotkey_key(self, key_name: str | None) -> bool:
        key = str(key_name or "").strip().lower()
        if not key:
            return False
        return key in {str(self._hotkey_stop or "").strip().lower(), "pgdown", "pagedown"}
    def _refresh_status(self, prefix: str | None = None):
        if prefix is not None:
            self._status_prefix = prefix
        txt = f"{self._status_prefix}: 총 {len(self._events)}개, 적용 가능 {self._recordable_event_count}개"
        if self._skipped_unknown_count > 0:
            txt += f", 미지원 {self._skipped_unknown_count}개 제외"
        self.status_label.setText(txt)
    def _toggle_listener(self):
        if self._listener_thread and self._listener_thread.is_alive():
            self._stop_listener()
        else:
            self._start_listener()
    def _start_listener(self):
        if self._listener_thread and self._listener_thread.is_alive():
            return
        self._stop_event.clear()
        self._listener_thread = threading.Thread(target=self._listen_loop, name="KeyboardRecordListener", daemon=True)
        self._listener_thread.start()
        self.toggle_btn.setText(self._toggle_btn_text(running=True))
        self._refresh_status("키보드 녹화중")
    def _stop_listener(self, *, message: str | None = None):
        self._stop_event.set()
        t = self._listener_thread
        if t and t.is_alive():
            t.join(timeout=1.0)
        self._listener_thread = None
        self.toggle_btn.setText(self._toggle_btn_text(running=False))
        self._refresh_status(message or "키보드 녹화 중지됨")
    def _safe_pressed(self, key_name: str) -> bool:
        try:
            return bool(get_keystate(key_name, async_=True))
        except TypeError:
            try:
                return bool(get_keystate(key_name))
            except Exception:
                return False
        except Exception:
            return False
    def _poll_hotkeys(self):
        start_pressed = self._safe_pressed(self._hotkey_start)
        stop_pressed = self._safe_pressed(self._hotkey_stop)
        if time.monotonic() < self._hotkey_initial_guard_until:
            self._hotkey_start_prev = start_pressed
            self._hotkey_stop_prev = stop_pressed
            return
        if not self._hotkey_ready:
            if not start_pressed and not stop_pressed:
                self._hotkey_release_polls += 1
                if self._hotkey_release_polls >= self._hotkey_release_polls_required:
                    self._hotkey_ready = True
                    self._hotkey_start_prev = False
                    self._hotkey_stop_prev = False
                    self._hotkey_start_streak = 0
                    self._hotkey_stop_streak = 0
            else:
                self._hotkey_release_polls = 0
                self._hotkey_start_prev = start_pressed
                self._hotkey_stop_prev = stop_pressed
            return
        if start_pressed:
            self._hotkey_start_streak += 1
        else:
            self._hotkey_start_streak = 0
        if stop_pressed:
            self._hotkey_stop_streak += 1
        else:
            self._hotkey_stop_streak = 0
        running = bool(self._listener_thread and self._listener_thread.is_alive())
        if running and self._hotkey_stop_streak == self._hotkey_stop_polls_required:
            self._stop_listener(message=f"키보드 녹화 중지됨 ({self._hotkey_stop_label})")
            running = False
            self._hotkey_ready = False
            self._hotkey_release_polls = 0
            self._hotkey_start_streak = 0
            self._hotkey_stop_streak = 0
            self._hotkey_initial_guard_until = time.monotonic() + 0.05
        if (not running) and self._hotkey_start_streak == self._hotkey_start_polls_required:
            self._start_listener()
            self._hotkey_ready = False
            self._hotkey_release_polls = 0
            self._hotkey_start_streak = 0
            self._hotkey_stop_streak = 0
            self._hotkey_initial_guard_until = time.monotonic() + 0.05
        self._hotkey_start_prev = start_pressed
        self._hotkey_stop_prev = stop_pressed
    def _listen_loop(self):
        try:
            inter = Interception()
            inter.set_keyboard_filter(KeyFilter.All)
        except Exception as exc:
            self._queue.put({"type": "error", "message": str(exc)})
            return
        down_states = {getattr(KeyState, "Down", None), getattr(KeyState, "E0Down", None), getattr(KeyState, "E1Down", None)}
        up_states = {getattr(KeyState, "Up", None), getattr(KeyState, "E0Up", None), getattr(KeyState, "E1Up", None)}
        while not self._stop_event.is_set():
            device = inter.wait_receive(200)
            if not device:
                continue
            try:
                if getattr(device, "is_keyboard", False):
                    stroke = getattr(device, "stroke", None)
                    if stroke is not None:
                        try:
                            state = KeyState(stroke.state)
                        except Exception:
                            state = None
                        if state in down_states or state in up_states:
                            action = "down" if state in down_states else "up"
                            key_name = _macro_key_from_stroke(stroke)
                            vk_code = 0
                            try:
                                sc_code = int(getattr(stroke, "code", 0))
                                vk_code = int(map_virtual_key(sc_code, MapVk.ScToVk) or 0)
                            except Exception:
                                vk_code = 0
                            is_start_hotkey = self._is_start_hotkey_key(key_name) or vk_code == 33
                            is_stop_hotkey = self._is_stop_hotkey_key(key_name) or vk_code == 34
                            if action == "down" and is_stop_hotkey:
                                self._queue.put({"type": "hotkey_stop"})
                            if not (is_start_hotkey or is_stop_hotkey):
                                self._queue.put(
                                    {
                                        "type": "event",
                                        "event": {
                                            "ts": time.time(),
                                            "action": action,
                                            "key": key_name,
                                            "label": _stroke_key_label(stroke, key_name),
                                        },
                                    }
                                )
            except Exception as exc:
                self._queue.put({"type": "error", "message": str(exc)})
                break
            try:
                device.send()
            except Exception:
                pass
    def _drain_queue(self):
        dirty = False
        while True:
            try:
                msg = self._queue.get_nowait()
            except queue.Empty:
                break
            mtype = msg.get("type")
            if mtype == "error":
                self._stop_listener(message=f"오류: {msg.get('message')}")
                continue
            if mtype == "hotkey_stop":
                self._stop_listener(message=f"키보드 녹화 중지됨 ({self._hotkey_stop_label})")
                continue
            if mtype != "event":
                continue
            event = msg.get("event")
            if not isinstance(event, dict):
                continue
            self._append_event_row(event)
            dirty = True
        if dirty:
            if self.table.rowCount() <= 500:
                self.table.resizeRowsToContents()
            self._refresh_status()
    def _append_event_row(self, event: dict[str, Any]):
        self._accepted_actions = None
        self._events.append(event)
        ts = float(event.get("ts", time.time()))
        row = self.table.rowCount()
        self.table.insertRow(row)
        base = time.strftime("%H:%M:%S", time.localtime(ts))
        ms = int((ts - int(ts)) * 1000)
        ts_txt = f"{base}.{ms:03d}"
        gap_txt = "-"
        if self._prev_event_ts is not None:
            gap_ms = max(0.0, (ts - self._prev_event_ts) * 1000.0)
            gap_txt = f"{gap_ms:.1f}"
        self._prev_event_ts = ts
        action = event.get("action")
        action_txt = "down" if action == "down" else "up"
        key_name = event.get("key")
        if key_name:
            self._recordable_event_count += 1
        else:
            self._skipped_unknown_count += 1
        key_txt = str(key_name) if key_name else "(미지원 키)"
        detail_txt = str(event.get("label") or "")
        self.table.setItem(row, 0, QtWidgets.QTableWidgetItem(ts_txt))
        self.table.setItem(row, 1, QtWidgets.QTableWidgetItem(key_txt))
        self.table.setItem(row, 2, QtWidgets.QTableWidgetItem(action_txt))
        self.table.setItem(row, 3, QtWidgets.QTableWidgetItem(gap_txt))
        self.table.setItem(row, 4, QtWidgets.QTableWidgetItem(detail_txt))
        if not key_name:
            warn_brush = QtGui.QBrush(QtGui.QColor("#b44"))
            for col in range(self.table.columnCount()):
                cell = self.table.item(row, col)
                if cell:
                    cell.setForeground(warn_brush)
    def _clear_events(self):
        self._accepted_actions = None
        self._events = []
        self._prev_event_ts = None
        self._recordable_event_count = 0
        self._skipped_unknown_count = 0
        self.table.setRowCount(0)
        self._refresh_status()
    def recorded_actions(self) -> list[Action]:
        if self._accepted_actions is not None:
            return list(self._accepted_actions)
        actions: list[Action] = []
        prev_ts: float | None = None
        for event in list(self._events):
            action_type = event.get("action")
            key_name = event.get("key")
            if action_type not in ("down", "up") or not key_name:
                continue
            ts = float(event.get("ts", 0.0) or 0.0)
            if prev_ts is not None:
                sleep_ms = int(round(max(0.0, (ts - prev_ts) * 1000.0)))
                if sleep_ms > 0:
                    actions.append(Action(type="sleep", sleep_ms=sleep_ms))
            actions.append(Action(type=action_type, key=key_name, key_raw=key_name))
            prev_ts = ts
        return actions
    def skipped_unknown_count(self) -> int:
        return int(self._skipped_unknown_count)
    def _accept_if_valid(self):
        if self._listener_thread and self._listener_thread.is_alive():
            self._stop_listener(message="키보드 녹화 중지됨")
            self._drain_queue()
        actions = self.recorded_actions()
        if not actions:
            QtWidgets.QMessageBox.information(self, "녹화 없음", "적용 가능한 키보드 이벤트가 없습니다.")
            return
        if self._skipped_unknown_count > 0:
            res = QtWidgets.QMessageBox.question(
                self,
                "일부 키 제외",
                f"미지원 키 이벤트 {self._skipped_unknown_count}개는 제외됩니다. 계속할까요?",
            )
            if res != QtWidgets.QMessageBox.StandardButton.Yes:
                return
        self._accepted_actions = list(actions)
        self.accept()
    def done(self, result: int):
        try:
            self._hotkey_timer.stop()
        except Exception:
            pass
        self._stop_listener()
        super().done(result)
    def closeEvent(self, event):
        try:
            try:
                self._hotkey_timer.stop()
            except Exception:
                pass
            self._stop_listener()
        finally:
            super().closeEvent(event)
class MouseRecordDialog(QtWidgets.QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("마우스 녹화")
        self.setModal(False)
        self.setWindowModality(QtCore.Qt.WindowModality.NonModal)
        self.resize(820, 500)
        self._queue: queue.Queue = queue.Queue()
        self._stop_event = threading.Event()
        self._listener_thread: threading.Thread | None = None
        self._timer = QtCore.QTimer(self)
        self._timer.setInterval(100)
        self._timer.timeout.connect(self._drain_queue)
        self._events: list[dict[str, Any]] = []
        self._prev_event_ts: float | None = None
        self._recordable_event_count: int = 0
        self._skipped_unknown_count: int = 0
        self._dropped_overflow_count: int = 0
        self._last_move_event_ts: float | None = None
        self._max_events: int = 6000
        self._move_sample_ms: int = 15
        self._accepted_actions: list[Action] | None = None
        self._status_prefix: str = "마우스 녹화 대기중"
        self._hotkey_start: str = "pgup"
        self._hotkey_stop: str = "pgdown"
        self._hotkey_start_label: str = "PageUp"
        self._hotkey_stop_label: str = "PageDown"
        self._hotkey_start_prev = False
        self._hotkey_stop_prev = False
        self._hotkey_ready = False
        self._hotkey_release_polls = 0
        self._hotkey_release_polls_required = 2
        self._hotkey_start_streak = 0
        self._hotkey_stop_streak = 0
        self._hotkey_start_polls_required = 2
        self._hotkey_stop_polls_required = 1
        self._hotkey_initial_guard_until = time.monotonic() + 0.35
        self._build_ui()
        self._timer.start()
        self._hotkey_start_prev = self._safe_pressed(self._hotkey_start)
        self._hotkey_stop_prev = self._safe_pressed(self._hotkey_stop)
        self._hotkey_ready = False
        self._hotkey_release_polls = 0
        self._hotkey_timer = QtCore.QTimer(self)
        self._hotkey_timer.setInterval(35)
        self._hotkey_timer.timeout.connect(self._poll_hotkeys)
        self._hotkey_timer.start()
    def _build_ui(self):
        layout = QtWidgets.QVBoxLayout(self)
        self.status_label = QtWidgets.QLabel("")
        self.status_label.setWordWrap(True)
        layout.addWidget(self.status_label)
        hint = QtWidgets.QLabel(
            "마우스 이동/누름/떼기를 그대로 기록합니다. 적용 시 액션은 sleep + mouse_move/down/up 형태로 생성됩니다."
        )
        hint.setStyleSheet("color: #666;")
        hint.setWordWrap(True)
        layout.addWidget(hint)
        hotkey_hint = QtWidgets.QLabel(
            f"단축키: {self._hotkey_start_label}=녹화 시작, {self._hotkey_stop_label}=녹화 중지"
        )
        hotkey_hint.setStyleSheet("color: #666;")
        layout.addWidget(hotkey_hint)
        ctrl_row = QtWidgets.QHBoxLayout()
        self.toggle_btn = QtWidgets.QPushButton(self._toggle_btn_text(running=False))
        self.clear_btn = QtWidgets.QPushButton("초기화")
        ctrl_row.addWidget(self.toggle_btn)
        ctrl_row.addWidget(self.clear_btn)
        ctrl_row.addStretch()
        layout.addLayout(ctrl_row)
        self.table = QtWidgets.QTableWidget(0, 6)
        self.table.setHorizontalHeaderLabels(["시간", "이벤트", "버튼", "좌표", "이전과 간격(ms)", "상세"])
        header = self.table.horizontalHeader()
        header.setSectionResizeMode(0, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(1, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(2, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(3, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(4, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        header.setStretchLastSection(True)
        self.table.verticalHeader().setVisible(False)
        self.table.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectionBehavior.SelectRows)
        self.table.setEditTriggers(QtWidgets.QAbstractItemView.EditTrigger.NoEditTriggers)
        self.table.setAlternatingRowColors(True)
        layout.addWidget(self.table, stretch=1)
        btn_row = QtWidgets.QHBoxLayout()
        btn_row.addStretch()
        self.apply_btn = QtWidgets.QPushButton("기록 적용")
        self.cancel_btn = QtWidgets.QPushButton("취소")
        btn_row.addWidget(self.apply_btn)
        btn_row.addWidget(self.cancel_btn)
        layout.addLayout(btn_row)
        self.toggle_btn.clicked.connect(self._toggle_listener)
        self.clear_btn.clicked.connect(self._clear_events)
        self.apply_btn.clicked.connect(self._accept_if_valid)
        self.cancel_btn.clicked.connect(self.reject)
        self._refresh_status()
    def _toggle_btn_text(self, *, running: bool) -> str:
        if running:
            return f"녹화 중지 ({self._hotkey_stop_label})"
        return f"녹화 시작 ({self._hotkey_start_label})"
    def _refresh_status(self, prefix: str | None = None):
        if prefix is not None:
            self._status_prefix = prefix
        txt = f"{self._status_prefix}: 총 {len(self._events)}개, 적용 가능 {self._recordable_event_count}개"
        if self._skipped_unknown_count > 0:
            txt += f", 미지원 {self._skipped_unknown_count}개 제외"
        if self._dropped_overflow_count > 0:
            txt += f", 초과 {self._dropped_overflow_count}개 생략(최대 {self._max_events}개)"
        self.status_label.setText(txt)
    def _toggle_listener(self):
        if self._listener_thread and self._listener_thread.is_alive():
            self._stop_listener()
        else:
            self._start_listener()
    def _start_listener(self):
        if self._listener_thread and self._listener_thread.is_alive():
            return
        self._stop_event.clear()
        self._listener_thread = threading.Thread(target=self._listen_loop, name="MouseRecordListener", daemon=True)
        self._listener_thread.start()
        self.toggle_btn.setText(self._toggle_btn_text(running=True))
        self._refresh_status("마우스 녹화중")
    def _stop_listener(self, *, message: str | None = None):
        self._stop_event.set()
        t = self._listener_thread
        if t and t.is_alive():
            t.join(timeout=1.0)
        self._listener_thread = None
        self.toggle_btn.setText(self._toggle_btn_text(running=False))
        self._refresh_status(message or "마우스 녹화 중지됨")
    def _safe_pressed(self, key_name: str) -> bool:
        try:
            return bool(get_keystate(key_name, async_=True))
        except TypeError:
            try:
                return bool(get_keystate(key_name))
            except Exception:
                return False
        except Exception:
            return False
    def _poll_hotkeys(self):
        start_pressed = self._safe_pressed(self._hotkey_start)
        stop_pressed = self._safe_pressed(self._hotkey_stop)
        if time.monotonic() < self._hotkey_initial_guard_until:
            self._hotkey_start_prev = start_pressed
            self._hotkey_stop_prev = stop_pressed
            return
        if not self._hotkey_ready:
            if not start_pressed and not stop_pressed:
                self._hotkey_release_polls += 1
                if self._hotkey_release_polls >= self._hotkey_release_polls_required:
                    self._hotkey_ready = True
                    self._hotkey_start_prev = False
                    self._hotkey_stop_prev = False
                    self._hotkey_start_streak = 0
                    self._hotkey_stop_streak = 0
            else:
                self._hotkey_release_polls = 0
                self._hotkey_start_prev = start_pressed
                self._hotkey_stop_prev = stop_pressed
            return
        if start_pressed:
            self._hotkey_start_streak += 1
        else:
            self._hotkey_start_streak = 0
        if stop_pressed:
            self._hotkey_stop_streak += 1
        else:
            self._hotkey_stop_streak = 0
        running = bool(self._listener_thread and self._listener_thread.is_alive())
        if running and self._hotkey_stop_streak == self._hotkey_stop_polls_required:
            self._stop_listener(message=f"마우스 녹화 중지됨 ({self._hotkey_stop_label})")
            running = False
            self._hotkey_ready = False
            self._hotkey_release_polls = 0
            self._hotkey_start_streak = 0
            self._hotkey_stop_streak = 0
            self._hotkey_initial_guard_until = time.monotonic() + 0.05
        if (not running) and self._hotkey_start_streak == self._hotkey_start_polls_required:
            self._start_listener()
            self._hotkey_ready = False
            self._hotkey_release_polls = 0
            self._hotkey_start_streak = 0
            self._hotkey_stop_streak = 0
            self._hotkey_initial_guard_until = time.monotonic() + 0.05
        self._hotkey_start_prev = start_pressed
        self._hotkey_stop_prev = stop_pressed
    def _parse_mouse_event(self, stroke) -> dict[str, Any] | None:
        ms = MouseState if "MouseState" in globals() else None
        if stroke is None or ms is None:
            return None
        try:
            state_raw = int(getattr(stroke, "state", 0))
        except Exception:
            return {
                "action": None,
                "button": None,
                "supported": False,
                "label": f"state={getattr(stroke, 'state', '-')}",
            }
        mappings = [
            (getattr(ms, "LeftButtonDown", None), "mouse_down", "mouse1", "left down"),
            (getattr(ms, "LeftButtonUp", None), "mouse_up", "mouse1", "left up"),
            (getattr(ms, "RightButtonDown", None), "mouse_down", "mouse2", "right down"),
            (getattr(ms, "RightButtonUp", None), "mouse_up", "mouse2", "right up"),
            (getattr(ms, "MiddleButtonDown", None), "mouse_down", "mouse3", "middle down"),
            (getattr(ms, "MuddleButtonDown", None), "mouse_down", "mouse3", "middle down"),
            (getattr(ms, "MiddleButtonUp", None), "mouse_up", "mouse3", "middle up"),
            (getattr(ms, "XButton1Down", None), "mouse_down", "mouse4", "x1 down"),
            (getattr(ms, "XButton1Up", None), "mouse_up", "mouse4", "x1 up"),
            (getattr(ms, "XButton2Down", None), "mouse_down", "mouse5", "x2 down"),
            (getattr(ms, "XButton2Up", None), "mouse_up", "mouse5", "x2 up"),
        ]
        for target_state, action, button, label in mappings:
            if target_state is None:
                continue
            try:
                target_bits = int(target_state)
            except Exception:
                continue
            if target_bits != 0 and (state_raw & target_bits) == target_bits:
                return {"action": action, "button": button, "supported": True, "label": label}
        move_state = getattr(ms, "Move", None)
        if move_state is not None:
            try:
                move_bits = int(move_state)
            except Exception:
                move_bits = 0
            if state_raw == move_bits or state_raw == 0x1000:
                return {"action": "mouse_move", "button": None, "supported": True, "label": "move"}
        wheel_bits = 0
        for wheel_state in (getattr(ms, "VerticalWheel", None), getattr(ms, "HorizontalWheel", None)):
            if wheel_state is None:
                continue
            try:
                wheel_bits |= int(wheel_state)
            except Exception:
                continue
        if wheel_bits and (state_raw & wheel_bits):
            return {"action": None, "button": None, "supported": False, "label": "wheel"}
        if state_raw == 0:
            return {"action": "mouse_move", "button": None, "supported": True, "label": "move"}
        return {"action": None, "button": None, "supported": False, "label": f"state={state_raw}"}
    def _evict_oldest_move_event(self) -> bool:
        for idx, old_event in enumerate(list(self._events)):
            if str(old_event.get("action") or "") != "mouse_move":
                continue
            supported = bool(old_event.get("supported"))
            if supported:
                self._recordable_event_count = max(0, self._recordable_event_count - 1)
            else:
                self._skipped_unknown_count = max(0, self._skipped_unknown_count - 1)
            del self._events[idx]
            if 0 <= idx < self.table.rowCount():
                self.table.removeRow(idx)
            return True
        return False
    def _listen_loop(self):
        try:
            inter = Interception()
            inter.set_mouse_filter(MouseFilter.All)
        except Exception as exc:
            self._queue.put({"type": "error", "message": str(exc)})
            return
        while not self._stop_event.is_set():
            device = inter.wait_receive(200)
            if not device:
                continue
            try:
                if getattr(device, "is_mouse", False):
                    stroke = getattr(device, "stroke", None)
                    event = self._parse_mouse_event(stroke)
                    if event:
                        pos = _current_cursor_pos()
                        event["ts"] = time.time()
                        event["x"] = pos[0] if pos else None
                        event["y"] = pos[1] if pos else None
                        if event.get("action") == "mouse_move" and pos is None:
                            event["supported"] = False
                            event["label"] = f"{event.get('label') or 'move'} (좌표 없음)"
                        self._queue.put({"type": "event", "event": event})
            except Exception as exc:
                self._queue.put({"type": "error", "message": str(exc)})
                break
            try:
                device.send()
            except Exception:
                pass
    def _drain_queue(self):
        dirty = False
        while True:
            try:
                msg = self._queue.get_nowait()
            except queue.Empty:
                break
            mtype = msg.get("type")
            if mtype == "error":
                self._stop_listener(message=f"오류: {msg.get('message')}")
                continue
            if mtype != "event":
                continue
            event = msg.get("event")
            if not isinstance(event, dict):
                continue
            self._append_event_row(event)
            dirty = True
        if dirty:
            if self.table.rowCount() <= 500:
                self.table.resizeRowsToContents()
            self._refresh_status()
    def _append_event_row(self, event: dict[str, Any]):
        ts = float(event.get("ts", time.time()))
        action = str(event.get("action") or "")
        if action == "mouse_move":
            if self._last_move_event_ts is not None:
                gap_ms = (ts - self._last_move_event_ts) * 1000.0
                if gap_ms < float(self._move_sample_ms):
                    return
            self._last_move_event_ts = ts
            if (
                bool(event.get("supported"))
                and self._events
                and str(self._events[-1].get("action") or "") == "mouse_move"
                and bool(self._events[-1].get("supported"))
                and self.table.rowCount() > 0
            ):
                self._accepted_actions = None
                self._events[-1] = event
                row = self.table.rowCount() - 1
                base = time.strftime("%H:%M:%S", time.localtime(ts))
                ms = int((ts - int(ts)) * 1000)
                ts_txt = f"{base}.{ms:03d}"
                x = event.get("x")
                y = event.get("y")
                pos_txt = f"{x},{y}" if isinstance(x, int) and isinstance(y, int) else "-"
                detail_txt = str(event.get("label") or "")
                self.table.setItem(row, 0, QtWidgets.QTableWidgetItem(ts_txt))
                self.table.setItem(row, 3, QtWidgets.QTableWidgetItem(pos_txt))
                self.table.setItem(row, 5, QtWidgets.QTableWidgetItem(detail_txt))
                self._prev_event_ts = ts
                return
        if len(self._events) >= int(self._max_events):
            if action == "mouse_move":
                self._dropped_overflow_count += 1
                return
            if not self._evict_oldest_move_event():
                self._dropped_overflow_count += 1
                return
        self._accepted_actions = None
        self._events.append(event)
        row = self.table.rowCount()
        self.table.insertRow(row)
        base = time.strftime("%H:%M:%S", time.localtime(ts))
        ms = int((ts - int(ts)) * 1000)
        ts_txt = f"{base}.{ms:03d}"
        gap_txt = "-"
        if self._prev_event_ts is not None:
            gap_ms = max(0.0, (ts - self._prev_event_ts) * 1000.0)
            gap_txt = f"{gap_ms:.1f}"
        self._prev_event_ts = ts
        action = str(event.get("action") or "")
        event_txt = {"mouse_down": "down", "mouse_up": "up", "mouse_move": "move"}.get(action, "-")
        button_txt = str(event.get("button") or "-")
        x = event.get("x")
        y = event.get("y")
        pos_txt = f"{x},{y}" if isinstance(x, int) and isinstance(y, int) else "-"
        detail_txt = str(event.get("label") or "")
        supported = bool(event.get("supported"))
        if supported:
            self._recordable_event_count += 1
        else:
            self._skipped_unknown_count += 1
        self.table.setItem(row, 0, QtWidgets.QTableWidgetItem(ts_txt))
        self.table.setItem(row, 1, QtWidgets.QTableWidgetItem(event_txt))
        self.table.setItem(row, 2, QtWidgets.QTableWidgetItem(button_txt))
        self.table.setItem(row, 3, QtWidgets.QTableWidgetItem(pos_txt))
        self.table.setItem(row, 4, QtWidgets.QTableWidgetItem(gap_txt))
        self.table.setItem(row, 5, QtWidgets.QTableWidgetItem(detail_txt))
        if not supported:
            warn_brush = QtGui.QBrush(QtGui.QColor("#b44"))
            for col in range(self.table.columnCount()):
                cell = self.table.item(row, col)
                if cell:
                    cell.setForeground(warn_brush)
    def _clear_events(self):
        self._accepted_actions = None
        self._events = []
        self._prev_event_ts = None
        self._last_move_event_ts = None
        self._recordable_event_count = 0
        self._skipped_unknown_count = 0
        self._dropped_overflow_count = 0
        self.table.setRowCount(0)
        self._refresh_status()
    def recorded_actions(self) -> list[Action]:
        if self._accepted_actions is not None:
            return list(self._accepted_actions)
        compressed: list[dict[str, Any]] = []
        for event in list(self._events):
            if not bool(event.get("supported")):
                continue
            action_type = str(event.get("action") or "")
            if action_type not in ("mouse_move", "mouse_down", "mouse_up"):
                continue
            if action_type == "mouse_move" and compressed and str(compressed[-1].get("action") or "") == "mouse_move":
                compressed[-1] = event
            else:
                compressed.append(event)
        actions: list[Action] = []
        prev_ts: float | None = None
        for event in compressed:
            action_type = str(event.get("action") or "")
            ts = float(event.get("ts", 0.0) or 0.0)
            if prev_ts is not None:
                sleep_ms = int(round(max(0.0, (ts - prev_ts) * 1000.0)))
                if sleep_ms > 0:
                    actions.append(Action(type="sleep", sleep_ms=sleep_ms))
            x = event.get("x")
            y = event.get("y")
            if action_type == "mouse_move":
                if not isinstance(x, int) or not isinstance(y, int):
                    continue
                raw = f"{x},{y}"
                actions.append(Action(type="mouse_move", mouse_pos=(x, y), mouse_pos_raw=raw))
            else:
                btn = str(event.get("button") or "mouse1")
                act = Action(type=action_type, mouse_button=btn)
                if isinstance(x, int) and isinstance(y, int):
                    raw = f"{x},{y}"
                    act.mouse_pos = (x, y)
                    act.mouse_pos_raw = raw
                actions.append(act)
            prev_ts = ts
        return actions
    def skipped_unknown_count(self) -> int:
        return int(self._skipped_unknown_count)
    def _accept_if_valid(self):
        if self._listener_thread and self._listener_thread.is_alive():
            self._stop_listener(message="마우스 녹화 중지됨")
            self._drain_queue()
        actions = self.recorded_actions()
        if not actions:
            QtWidgets.QMessageBox.information(self, "녹화 없음", "적용 가능한 마우스 이벤트가 없습니다.")
            return
        if self._dropped_overflow_count > 0:
            res = QtWidgets.QMessageBox.question(
                self,
                "일부 이벤트 생략",
                f"이벤트가 많아 {self._dropped_overflow_count}개를 생략했습니다(최대 {self._max_events}개 유지). 계속할까요?",
            )
            if res != QtWidgets.QMessageBox.StandardButton.Yes:
                return
        if self._skipped_unknown_count > 0:
            res = QtWidgets.QMessageBox.question(
                self,
                "일부 이벤트 제외",
                f"미지원 마우스 이벤트 {self._skipped_unknown_count}개는 제외됩니다. 계속할까요?",
            )
            if res != QtWidgets.QMessageBox.StandardButton.Yes:
                return
        self._accepted_actions = list(actions)
        self.accept()
    def done(self, result: int):
        try:
            self._hotkey_timer.stop()
        except Exception:
            pass
        self._stop_listener()
        super().done(result)
    def closeEvent(self, event):
        try:
            try:
                self._hotkey_timer.stop()
            except Exception:
                pass
            self._stop_listener()
        finally:
            super().closeEvent(event)
class InputTimingTestDialog(QtWidgets.QDialog):
    def __init__(self, parent=None, *, on_apply_keyboard=None, on_apply_mouse=None):
        super().__init__(parent)
        self.setWindowTitle("입력 속도 테스트")
        self.setModal(False)
        self.setWindowModality(QtCore.Qt.WindowModality.NonModal)
        self.resize(780, 520)
        self._apply_keyboard_cb = on_apply_keyboard
        self._apply_mouse_cb = on_apply_mouse
        self._queue: queue.Queue = queue.Queue()
        self._stop_event = threading.Event()
        self._listener_thread: threading.Thread | None = None
        self._timer = QtCore.QTimer(self)
        self._timer.setInterval(120)
        self._timer.timeout.connect(self._drain_queue)
        self._pending: dict = {}
        self._last_down_ts: float | None = None
        self._press_samples: list[float] = []
        self._gap_samples: list[float] = []
        self._max_rows = 180
        self._friendly_map: dict[str, str] = {}
        self._build_ui()
        self._update_stats()
        self._timer.start()
        self._start_listener()
    def _build_ui(self):
        layout = QtWidgets.QVBoxLayout(self)
        self.status_label = QtWidgets.QLabel("키보드나 마우스를 연타해보세요. 누름 시간과 입력 사이 지연을 측정합니다.")
        self.status_label.setWordWrap(True)
        layout.addWidget(self.status_label)
        stats = QtWidgets.QGridLayout()
        stats.addWidget(QtWidgets.QLabel("누름 시간"), 0, 0)
        self.press_stat_label = QtWidgets.QLabel("-")
        stats.addWidget(self.press_stat_label, 0, 1)
        stats.addWidget(QtWidgets.QLabel("입력 사이 지연"), 1, 0)
        self.gap_stat_label = QtWidgets.QLabel("-")
        stats.addWidget(self.gap_stat_label, 1, 1)
        layout.addLayout(stats)
        self.last_sample_label = QtWidgets.QLabel("최근: -")
        self.last_sample_label.setStyleSheet("color: gray;")
        layout.addWidget(self.last_sample_label)
        ctrl_row = QtWidgets.QHBoxLayout()
        self.toggle_btn = QtWidgets.QPushButton("측정 중지")
        self.reset_btn = QtWidgets.QPushButton("초기화")
        self.apply_keyboard_btn = QtWidgets.QPushButton("키보드 적용")
        self.apply_mouse_btn = QtWidgets.QPushButton("마우스 적용")
        ctrl_row.addWidget(self.toggle_btn)
        ctrl_row.addWidget(self.reset_btn)
        ctrl_row.addWidget(self.apply_keyboard_btn)
        ctrl_row.addWidget(self.apply_mouse_btn)
        ctrl_row.addStretch()
        layout.addLayout(ctrl_row)
        self.table = QtWidgets.QTableWidget(0, 6)
        self.table.setHorizontalHeaderLabels(["시간", "장치", "입력", "누름(ms)", "입력 사이(ms)", "HWID / Friendly"])
        header = self.table.horizontalHeader()
        header.setSectionResizeMode(0, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(1, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(2, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(3, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        header.setSectionResizeMode(4, QtWidgets.QHeaderView.ResizeMode.ResizeToContents)
        header.setStretchLastSection(True)
        self.table.verticalHeader().setVisible(False)
        self.table.setSelectionBehavior(QtWidgets.QAbstractItemView.SelectionBehavior.SelectRows)
        self.table.setEditTriggers(QtWidgets.QAbstractItemView.EditTrigger.NoEditTriggers)
        self.table.setAlternatingRowColors(True)
        layout.addWidget(self.table)
        self.toggle_btn.clicked.connect(self._toggle_listener)
        self.reset_btn.clicked.connect(self._reset)
        self.apply_keyboard_btn.clicked.connect(self._apply_to_keyboard)
        self.apply_mouse_btn.clicked.connect(self._apply_to_mouse)
    def set_apply_callbacks(self, *, keyboard=None, mouse=None):
        self._apply_keyboard_cb = keyboard
        self._apply_mouse_cb = mouse
    def _toggle_listener(self):
        if self._listener_thread and self._listener_thread.is_alive():
            self._stop_listener()
        else:
            self._start_listener()
    def _start_listener(self):
        if self._listener_thread and self._listener_thread.is_alive():
            return
        self._stop_event.clear()
        self._pending = {}
        self._last_down_ts = None
        self._listener_thread = threading.Thread(target=self._listen_loop, name="InputTimingListener", daemon=True)
        self._listener_thread.start()
        self.toggle_btn.setText("측정 중지")
        self.status_label.setText("측정 중: 키보드나 마우스를 연타해보세요.")
    def _stop_listener(self, *, message: str | None = None):
        self._stop_event.set()
        t = self._listener_thread
        if t and t.is_alive():
            t.join(timeout=1.0)
        self._listener_thread = None
        self.toggle_btn.setText("측정 시작")
        if message:
            self.status_label.setText(message)
        else:
            self.status_label.setText("중지됨: 다시 시작하려면 측정 시작을 누르세요.")
    def _listen_loop(self):
        try:
            inter = Interception()
            inter.set_keyboard_filter(KeyFilter.All)
            inter.set_mouse_filter(MouseFilter.All)
            ctx = getattr(inter, "_context", [])
            try:
                friendly_info = kbutil.list_interception_devices(friendly=True)
                friendly_map = {info.get("hardware_id", "").lower(): info.get("friendly_name", "") for info in friendly_info}
                self._queue.put({"type": "friendly_map", "map": friendly_map})
            except Exception:
                pass
        except Exception as exc:
            self._queue.put({"type": "error", "message": str(exc)})
            return
        while not self._stop_event.is_set():
            device = inter.wait_receive(200)
            if not device:
                continue
            now = time.time()
            try:
                entry = self._build_entry(device, ctx, now)
                if entry:
                    self._queue.put(entry)
            except Exception as exc:
                self._queue.put({"type": "error", "message": str(exc)})
                break
            try:
                device.send()
            except Exception:
                pass
    def _build_entry(self, device, ctx, now: float) -> dict | None:
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
        stroke = getattr(device, "stroke", None)
        if getattr(device, "is_keyboard", False):
            info = self._parse_keyboard_stroke(stroke)
            if not info:
                return None
            return self._handle_timing_event(
                key_id=("keyboard", device_id, info.get("code")),
                action=info.get("action"),
                label=info.get("label") or "키보드",
                kind="키보드",
                hwid=hwid,
                device_id=device_id,
                now=now,
            )
        info = self._parse_mouse_stroke(stroke)
        if not info:
            return None
        return self._handle_timing_event(
            key_id=("mouse", device_id, info.get("button")),
            action=info.get("action"),
            label=info.get("label") or "마우스",
            kind="마우스",
            hwid=hwid,
            device_id=device_id,
            now=now,
        )
    def _parse_keyboard_stroke(self, stroke) -> dict | None:
        if stroke is None:
            return None
        try:
            state = KeyState(stroke.state)
        except Exception:
            state = None
        down_states = {getattr(KeyState, "Down", None), getattr(KeyState, "E0Down", None), getattr(KeyState, "E1Down", None)}
        up_states = {getattr(KeyState, "Up", None), getattr(KeyState, "E0Up", None), getattr(KeyState, "E1Up", None)}
        if state in down_states:
            action = "down"
        elif state in up_states:
            action = "up"
        else:
            return None
        return {"action": action, "code": getattr(stroke, "code", None), "label": self._describe_key(stroke)}
    def _parse_mouse_stroke(self, stroke) -> dict | None:
        ms = MouseState if "MouseState" in globals() else None
        if stroke is None or ms is None:
            return None
        try:
            state = ms(stroke.state)
        except Exception:
            return None
        down_map = {
            getattr(ms, "LeftButtonDown", None): ("left", "좌클릭"),
            getattr(ms, "RightButtonDown", None): ("right", "우클릭"),
            getattr(ms, "MiddleButtonDown", None): ("middle", "휠 클릭"),
            getattr(ms, "XButton1Down", None): ("x1", "X1 클릭"),
            getattr(ms, "XButton2Down", None): ("x2", "X2 클릭"),
        }
        up_map = {
            getattr(ms, "LeftButtonUp", None): ("left", "좌클릭"),
            getattr(ms, "RightButtonUp", None): ("right", "우클릭"),
            getattr(ms, "MiddleButtonUp", None): ("middle", "휠 클릭"),
            getattr(ms, "XButton1Up", None): ("x1", "X1 클릭"),
            getattr(ms, "XButton2Up", None): ("x2", "X2 클릭"),
        }
        if state in down_map:
            button, label = down_map[state]
            return {"action": "down", "button": button, "label": label}
        if state in up_map:
            button, label = up_map[state]
            return {"action": "up", "button": button, "label": label}
        return None
    def _handle_timing_event(
        self,
        *,
        key_id,
        action: str,
        label: str,
        kind: str,
        hwid: str,
        device_id,
        now: float,
    ) -> dict | None:
        if action == "down":
            gap_ms = None
            if self._last_down_ts:
                gap_ms = (now - self._last_down_ts) * 1000.0
            self._last_down_ts = now
            self._pending[key_id] = {"ts": now, "gap_ms": gap_ms, "label": label, "kind": kind, "hwid": hwid, "device_id": device_id}
            return None
        if action != "up":
            return None
        pending = self._pending.pop(key_id, None)
        if not pending:
            return None
        hold_ms = (now - pending["ts"]) * 1000.0
        gap_ms = pending.get("gap_ms")
        return {
            "type": "sample",
            "ts": now,
            "kind": kind,
            "label": label,
            "hold_ms": hold_ms,
            "gap_ms": gap_ms,
            "hwid": hwid or pending.get("hwid"),
            "device_id": device_id or pending.get("device_id"),
        }
    def _drain_queue(self):
        dirty = False
        while True:
            try:
                msg = self._queue.get_nowait()
            except queue.Empty:
                break
            mtype = msg.get("type")
            if mtype == "error":
                self._stop_listener(message=f"오류: {msg.get('message')}")
                continue
            if mtype == "friendly_map":
                self._friendly_map = msg.get("map") or {}
                continue
            if mtype == "sample":
                hold_ms = float(msg.get("hold_ms") or 0.0)
                gap_ms = msg.get("gap_ms")
                self._press_samples.append(hold_ms)
                if len(self._press_samples) > 500:
                    self._press_samples = self._press_samples[-500:]
                if gap_ms is not None:
                    try:
                        gap_val = float(gap_ms)
                        self._gap_samples.append(gap_val)
                        if len(self._gap_samples) > 500:
                            self._gap_samples = self._gap_samples[-500:]
                    except Exception:
                        pass
                self._add_row(msg)
                self._last_sample_label(msg)
                dirty = True
        if dirty:
            self._update_stats()
    def _last_sample_label(self, msg: dict):
        label = msg.get("label") or "-"
        hold_ms = float(msg.get("hold_ms") or 0.0)
        gap_ms = msg.get("gap_ms")
        gap_txt = f", 사이 {gap_ms:.1f}ms" if isinstance(gap_ms, (int, float)) else ""
        self.last_sample_label.setText(f"최근: {label} · 누름 {hold_ms:.1f}ms{gap_txt}")
    def _add_row(self, msg: dict):
        row = 0
        self.table.insertRow(row)
        ts = float(msg.get("ts", time.time()))
        base = time.strftime("%H:%M:%S", time.localtime(ts))
        ms = int((ts - int(ts)) * 1000)
        ts_txt = f"{base}.{ms:03d}"
        device_txt = f"#{msg.get('device_id')}" if msg.get("device_id") else "-"
        hwid = msg.get("hwid") or ""
        friendly = self._friendly_from_hwid(hwid)
        vidpid = _short_hwid(hwid)
        hwid_cell = vidpid
        if friendly and vidpid:
            hwid_cell = f"{vidpid} ({friendly})"
        elif friendly:
            hwid_cell = friendly
        elif hwid:
            hwid_cell = hwid
        self.table.setItem(row, 0, QtWidgets.QTableWidgetItem(ts_txt))
        self.table.setItem(row, 1, QtWidgets.QTableWidgetItem(msg.get("kind") or "-"))
        self.table.setItem(row, 2, QtWidgets.QTableWidgetItem(msg.get("label") or "-"))
        self.table.setItem(row, 3, QtWidgets.QTableWidgetItem(f"{float(msg.get('hold_ms') or 0):.1f}"))
        gap_val = msg.get("gap_ms")
        gap_txt = f"{float(gap_val):.1f}" if isinstance(gap_val, (int, float)) else "-"
        self.table.setItem(row, 4, QtWidgets.QTableWidgetItem(gap_txt))
        self.table.setItem(row, 5, QtWidgets.QTableWidgetItem(hwid_cell))
        if self.table.rowCount() > self._max_rows:
            self.table.removeRow(self.table.rowCount() - 1)
        self.table.resizeRowsToContents()
    def _friendly_from_hwid(self, hwid: str) -> str:
        if not hwid:
            return ""
        return self._friendly_map.get(hwid.lower(), "") or self._friendly_map.get(hwid.upper(), "")
    def _describe_key(self, stroke) -> str:
        base = f"SC {getattr(stroke, 'code', '-')}"
        try:
            vk = map_virtual_key(int(getattr(stroke, "code", 0)), MapVk.ScToVk)
            if vk:
                ch = chr(vk)
                vk_txt = f"{ch.upper()} (VK {vk})" if ch.isprintable() and len(ch) == 1 else f"VK {vk}"
                base = f"{vk_txt} / {base}"
        except Exception:
            pass
        return base
    def _update_stats(self):
        self.press_stat_label.setText(self._format_stat(self._press_samples))
        self.gap_stat_label.setText(self._format_stat(self._gap_samples))
    def _format_stat(self, samples: list[float]) -> str:
        if not samples:
            return "- (샘플 0)"
        avg = sum(samples) / len(samples)
        return f"{avg:.1f} ms (샘플 {len(samples)}, 최소 {min(samples):.1f}, 최대 {max(samples):.1f})"
    def _reset(self):
        self._press_samples = []
        self._gap_samples = []
        self._pending = {}
        self._last_down_ts = None
        self.table.setRowCount(0)
        self.last_sample_label.setText("최근: -")
        self._update_stats()
    def _apply_to_keyboard(self):
        hold, gap = self._current_ms()
        if not callable(self._apply_keyboard_cb):
            self.status_label.setText("키보드 적용 콜백이 연결되지 않았습니다.")
            return
        if hold is None and gap is None:
            self.status_label.setText("샘플이 없습니다. 눌러서 측정 후 적용하세요.")
            return
        self._apply_keyboard_cb(hold, gap)
        self.status_label.setText(
            f"키보드 적용 완료: 누름 {hold if hold is not None else '-'} ms, 사이 {gap if gap is not None else '-'} ms"
        )
    def _apply_to_mouse(self):
        hold, gap = self._current_ms()
        if not callable(self._apply_mouse_cb):
            self.status_label.setText("마우스 적용 콜백이 연결되지 않았습니다.")
            return
        if hold is None and gap is None:
            self.status_label.setText("샘플이 없습니다. 눌러서 측정 후 적용하세요.")
            return
        self._apply_mouse_cb(hold, gap)
        self.status_label.setText(
            f"마우스 적용 완료: 누름 {hold if hold is not None else '-'} ms, 사이 {gap if gap is not None else '-'} ms"
        )
    def _current_ms(self) -> tuple[int | None, int | None]:
        hold = round(sum(self._press_samples) / len(self._press_samples)) if self._press_samples else None
        gap = round(sum(self._gap_samples) / len(self._gap_samples)) if self._gap_samples else None
        return hold, gap
    def set_friendly_map(self, friendly: dict[str, str] | None):
        self._friendly_map = friendly or {}
    def closeEvent(self, event):
        try:
            self._stop_listener()
        finally:
            super().closeEvent(event)
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
        self._input_rate_dialog: InputTimingTestDialog | None = None
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
        self.input_rate_btn = QtWidgets.QPushButton("입력 속도 테스트")
        test_row.addWidget(self.input_rate_btn)
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
        self.input_rate_btn.clicked.connect(self._open_input_rate_dialog)
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
        if self._input_rate_dialog:
            self._input_rate_dialog.set_friendly_map(self._friendly_map)
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
    def _open_input_rate_dialog(self):
        if self._input_rate_dialog is None:
            self._input_rate_dialog = InputTimingTestDialog(
                parent=self,
                on_apply_keyboard=self._apply_input_timing_to_keyboard,
                on_apply_mouse=self._apply_input_timing_to_mouse,
            )
            self._input_rate_dialog.set_friendly_map(self._friendly_map)
            try:
                self._input_rate_dialog.destroyed.connect(lambda: setattr(self, "_input_rate_dialog", None))
            except Exception:
                pass
        else:
            self._input_rate_dialog.set_friendly_map(self._friendly_map)
            self._input_rate_dialog.set_apply_callbacks(
                keyboard=self._apply_input_timing_to_keyboard, mouse=self._apply_input_timing_to_mouse
            )
        self._input_rate_dialog.show()
        self._input_rate_dialog.raise_()
        self._input_rate_dialog.activateWindow()
    def _apply_input_timing_to_keyboard(self, hold_ms: int | None, gap_ms: int | None):
        derived_gap = None
        if hold_ms is not None and gap_ms is not None:
            derived_gap = max(int(gap_ms) - int(hold_ms), 0)
        if hold_ms is not None:
            self.press_delay_edit.setText(str(int(hold_ms)))
        if gap_ms is not None:
            self.gap_delay_edit.setText(str(int(derived_gap if derived_gap is not None else gap_ms)))
    def _apply_input_timing_to_mouse(self, hold_ms: int | None, gap_ms: int | None):
        derived_gap = None
        if hold_ms is not None and gap_ms is not None:
            derived_gap = max(int(gap_ms) - int(hold_ms), 0)
        if hold_ms is not None:
            self.mouse_press_delay_edit.setText(str(int(hold_ms)))
        if gap_ms is not None:
            self.mouse_gap_delay_edit.setText(str(int(derived_gap if derived_gap is not None else gap_ms)))
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
        shared_patterns = _merge_profile_patterns_to_shared(getattr(self.profile, "pixel_patterns", None))
        try:
            self.engine._pixel_patterns = copy.deepcopy(shared_patterns)
        except Exception:
            pass
        self.profile.pixel_patterns = {}
        self.current_profile_path: str | None = None
        self.base_title = "Interception Macro GUI"
        self.dirty: bool = False
        self._loading_profile = False
        base_dir = Path(__file__).resolve().parent
        self._config_dir = base_dir / "config"
        try:
            self._config_dir.mkdir(parents=True, exist_ok=True)
        except Exception:
            pass
        self._state_path = self._config_dir / "global_state.json"
        self._state: dict = self._load_state()
        self._debugger_state = self._state.get("debugger", {}) if isinstance(self._state, dict) else {}
        self._image_viewer_state = self._state.get("image_viewer", {}) if isinstance(self._state, dict) else {}
        self._color_calc_state = self._state.get("color_calc", {}) if isinstance(self._state, dict) else {}
        self._preset_transfer_state = self._state.get("preset_transfer", {}) if isinstance(self._state, dict) else {}
        self._log_enabled = bool(self._state.get("log_enabled", True)) if isinstance(self._state, dict) else True
        history_state = self._state.get("profile_history", {}) if isinstance(self._state, dict) else {}
        self._recent_profiles: list[str] = self._dedupe_profile_paths(
            history_state.get("recent", []) if isinstance(history_state, dict) else []
        )
        self._favorite_profiles: list[str] = self._dedupe_profile_paths(
            history_state.get("favorites", []) if isinstance(history_state, dict) else []
        )
        self._syncing_profile_lists = False
        last_path = self._state.get("last_profile_path") if isinstance(self._state, dict) else None
        if last_path:
            self._recent_profiles = self._dedupe_profile_paths([last_path, *self._recent_profiles])
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
            "min_count": pixel_state.get("min_count", 1),
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
        self._viewer_image_provider = None
        screenshot_state = self._state.get("screenshot", {}) if isinstance(self._state, dict) else {}
        self.screenshot_manager = ScreenCaptureManager(
            interval_seconds=screenshot_state.get("interval", CAPTURE_INTERVAL_SECONDS),
            image_format=screenshot_state.get("format", DEFAULT_FORMAT),
            jpeg_quality=screenshot_state.get("jpeg_quality", DEFAULT_JPEG_QUALITY),
            png_compress_level=screenshot_state.get("png_compress_level", DEFAULT_PNG_COMPRESS_LEVEL),
            max_queue_size=screenshot_state.get("queue_size", MAX_QUEUE_SIZE),
        )
        self._theme = self._compute_theme_colors()
        hotkey_start = _sanitize_screenshot_hotkey(screenshot_state.get("hotkey_start"), allow_reserved=False)
        hotkey_stop = _sanitize_screenshot_hotkey(screenshot_state.get("hotkey_stop"), allow_reserved=False)
        hotkey_capture = _sanitize_screenshot_hotkey(screenshot_state.get("hotkey_capture"))
        self.screenshot_manager.configure_hotkeys(
            hotkey_start,
            hotkey_stop,
            hotkey_capture,
            enabled=bool(screenshot_state.get("hotkey_enabled", False)),
        )
        self._screenshot_dialog: ScreenshotDialog | None = None
        self.setWindowTitle(self.base_title)
        self.resize(1100, 820)
        self.setMinimumWidth(780)
        self._build_ui()
        self._build_menu()
        self._refresh_profile_header()
        self._refresh_profile_lists()
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
        self._status_hint = "Home=활성, Pause=일시정지, End=종료, 기능 메뉴=디버거/픽셀 테스트"
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
        header_layout.addWidget(self._build_profile_strip())
        layout.addWidget(header)
        macro_group = self._build_macro_group()
        variable_group = self._build_variable_group()
        log_group = self._build_log_group()
        splitter = QtWidgets.QSplitter(QtCore.Qt.Orientation.Vertical)
        splitter.addWidget(macro_group)
        splitter.addWidget(variable_group)
        splitter.addWidget(log_group)
        splitter.setSizes([400, 260, 200])
        self.main_splitter = splitter
        layout.addWidget(splitter, stretch=1)
        layout.setStretch(0, 0)  # header
        layout.setStretch(1, 1)  # splitter with macro/variable/log
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
        pattern_action = QtGui.QAction("픽셀 패턴 관리", self)
        pattern_action.triggered.connect(lambda: self._open_pattern_manager())
        feature_menu.addAction(pattern_action)
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
                get_viewer_cb=lambda: self._image_viewer_dialog,
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
            if config.get("min_count") is not None:
                try:
                    self._pixel_test_defaults["min_count"] = max(1, int(config.get("min_count")))
                except Exception:
                    pass
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
            "min_count": state.get("min_count", defaults["min_count"]),
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
                pattern_provider=self._pattern_names,
                open_pattern_manager=self._open_pattern_manager,
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
            sample_preset_state=self._preset_transfer_state.get("sample_preset")
            if isinstance(self._preset_transfer_state, dict)
            else {},
            save_sample_preset_state=self._persist_preset_transfer_state,
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
    def set_viewer_debug_source(self, *, enabled: bool, provider=None):
        self._viewer_image_provider = provider if callable(provider) else None
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
    def _build_profile_strip(self):
        group = QtWidgets.QFrame()
        group.setObjectName("profileStrip")
        group.setFrameShape(QtWidgets.QFrame.Shape.StyledPanel)
        group.setFrameShadow(QtWidgets.QFrame.Shadow.Plain)
        group.setSizePolicy(QtWidgets.QSizePolicy.Policy.Expanding, QtWidgets.QSizePolicy.Policy.Maximum)
        layout = QtWidgets.QVBoxLayout(group)
        layout.setContentsMargins(8, 6, 8, 6)
        layout.setSpacing(6)
        theme = self._theme
        btn_style = (
            f"padding: 4px 10px; border: 1px solid {theme['button_border']}; "
            f"border-radius: 6px; background: {theme['button_bg']}; color: {theme['button_text']};"
        )
        def _btn(text: str):
            b = QtWidgets.QPushButton(text)
            b.setMinimumHeight(26)
            b.setStyleSheet(btn_style)
            return b
        lists_row = QtWidgets.QHBoxLayout()
        lists_row.setContentsMargins(0, 0, 0, 0)
        lists_row.setSpacing(10)
        fav_col = QtWidgets.QVBoxLayout()
        fav_col.setContentsMargins(0, 0, 0, 0)
        fav_col.setSpacing(4)
        fav_head = QtWidgets.QHBoxLayout()
        fav_head.setContentsMargins(0, 0, 0, 0)
        fav_head.setSpacing(4)
        self.fav_label = QtWidgets.QLabel("즐겨찾기 (0)")
        self.fav_label.setStyleSheet("font-weight: 600;")
        self.fav_load_btn = _btn("불러오기")
        self.fav_load_btn.setMinimumHeight(24)
        self.fav_remove_btn = _btn("즐겨찾기 해제")
        self.fav_remove_btn.setMinimumHeight(24)
        fav_head.addWidget(self.fav_label)
        fav_head.addStretch()
        fav_head.addWidget(self.fav_load_btn)
        fav_head.addWidget(self.fav_remove_btn)
        fav_col.addLayout(fav_head)
        self.favorite_list = QtWidgets.QListWidget()
        self.favorite_list.setSelectionMode(QtWidgets.QAbstractItemView.SelectionMode.SingleSelection)
        self.favorite_list.setAlternatingRowColors(False)
        self.favorite_list.setTextElideMode(QtCore.Qt.TextElideMode.ElideMiddle)
        self.favorite_list.setMaximumHeight(120)
        self.favorite_list.setHorizontalScrollBarPolicy(QtCore.Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.favorite_list.setDragEnabled(True)
        self.favorite_list.setAcceptDrops(True)
        self.favorite_list.setDropIndicatorShown(True)
        self.favorite_list.setDefaultDropAction(QtCore.Qt.DropAction.MoveAction)
        self.favorite_list.setDragDropMode(QtWidgets.QAbstractItemView.DragDropMode.InternalMove)
        fav_col.addWidget(self.favorite_list)
        rec_col = QtWidgets.QVBoxLayout()
        rec_col.setContentsMargins(0, 0, 0, 0)
        rec_col.setSpacing(4)
        rec_head = QtWidgets.QHBoxLayout()
        rec_head.setContentsMargins(0, 0, 0, 0)
        rec_head.setSpacing(4)
        self.recent_label = QtWidgets.QLabel("최근 불러온 (0)")
        self.recent_label.setStyleSheet("font-weight: 600;")
        self.recent_load_btn = _btn("불러오기")
        self.recent_load_btn.setMinimumHeight(24)
        self.recent_to_fav_btn = _btn("즐겨찾기 추가")
        self.recent_to_fav_btn.setMinimumHeight(24)
        self.recent_clear_btn = _btn("비우기")
        self.recent_clear_btn.setMinimumHeight(24)
        rec_head.addWidget(self.recent_label)
        rec_head.addStretch()
        rec_head.addWidget(self.recent_load_btn)
        rec_head.addWidget(self.recent_to_fav_btn)
        rec_head.addWidget(self.recent_clear_btn)
        rec_col.addLayout(rec_head)
        self.recent_list = QtWidgets.QListWidget()
        self.recent_list.setSelectionMode(QtWidgets.QAbstractItemView.SelectionMode.SingleSelection)
        self.recent_list.setAlternatingRowColors(False)
        self.recent_list.setTextElideMode(QtCore.Qt.TextElideMode.ElideMiddle)
        self.recent_list.setMaximumHeight(120)
        self.recent_list.setHorizontalScrollBarPolicy(QtCore.Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        rec_col.addWidget(self.recent_list)
        self._fav_list_delegate = _ProfileListDelegate(self.favorite_list)
        self.favorite_list.setItemDelegate(self._fav_list_delegate)
        self._recent_list_delegate = _ProfileListDelegate(self.recent_list)
        self.recent_list.setItemDelegate(self._recent_list_delegate)
        lists_row.addLayout(fav_col, 1)
        lists_row.addLayout(rec_col, 1)
        layout.addLayout(lists_row)
        sel_bg = "#2c4a7a" if theme["is_dark"] else "#dce7ff"
        sel_fg = "#ffffff" if theme["is_dark"] else "#1f3f73"
        hover_bg = theme["panel_alt_bg"]
        base_bg = "#ffffff" if not theme["is_dark"] else "#111318"
        list_style = (
            f"QListWidget {{ border: 1px solid {theme['panel_border']}; border-radius: 0px; padding: 0px; background: {base_bg}; }}"
            f"QListWidget {{ outline: 0; }}"
            f"QListWidget::item {{ padding: 6px 10px; margin: 0; border: none; border-radius: 0px; }}"
            f"QListWidget::item:hover {{ background: {hover_bg}; color: {theme['text']}; border: none; border-radius: 0px; }}"
            f"QListWidget::item:selected {{ background: {sel_bg}; color: {sel_fg}; border: none; outline: 0; border-radius: 0px; }}"
            f"QListWidget::item:selected:active {{ background: {sel_bg}; color: {sel_fg}; border: none; outline: 0; border-radius: 0px; }}"
            f"QListWidget::item:selected:!active {{ background: {sel_bg}; color: {sel_fg}; border: none; outline: 0; border-radius: 0px; }}"
            f"QListWidget::item:selected:hover {{ background: {sel_bg}; color: {sel_fg}; border: none; outline: 0; border-radius: 0px; }}"
            f"QListWidget::item:focus {{ outline: none; border: none; border-radius: 0px; }}"
        )
        self.favorite_list.setStyleSheet(list_style)
        self.recent_list.setStyleSheet(list_style)
        group.setStyleSheet(
            f"#profileStrip {{ border: 1px solid {theme['panel_border']}; border-radius: 8px; "
            f"background: {theme['panel_bg']}; color: {theme['text']}; }}"
        )
        return group
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
        self.hardware_label = QtWidgets.QLabel("하드웨어(?)")
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
        for lbl in (self.running_label, self.active_label, self.paused_label, self.admin_label, self.hardware_label, self.capture_label):
            lbl.setMinimumWidth(66)
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
        badge_grid.addWidget(self.hardware_label, 1, 1)
        badge_grid.addWidget(self.capture_label, 1, 2)
        badge_grid.addWidget(self.log_toggle_btn, 1, 3)
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
            del_btn = QtWidgets.QPushButton("삭제")
            sort_btn = QtWidgets.QPushButton("정렬")
            btn_row.addWidget(del_btn)
            btn_row.addWidget(sort_btn)
            btn_row.addStretch()
            def del_rows():
                if table.selectionModel().selectedIndexes():
                    self._delete_selected_variable_pairs(table, key)
                else:
                    self._pop_last_variable_pair(table)
            def sort_rows():
                pairs = self._sort_pairs_by_name(self._variable_pairs_from_table(table))
                self._set_variable_pairs(table, pairs)
            del_btn.clicked.connect(del_rows)
            sort_btn.clicked.connect(sort_rows)
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
        self.log_clear_btn = QtWidgets.QToolButton()
        self.log_clear_btn.setText("초기화")
        self.log_clear_btn.setAutoRaise(True)
        self.log_clear_btn.clicked.connect(self._clear_log_view)
        toggle_row.addWidget(self.log_clear_btn)
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
        self.recent_load_btn.clicked.connect(lambda: self._load_selected_profile(self.recent_list))
        self.fav_load_btn.clicked.connect(lambda: self._load_selected_profile(self.favorite_list))
        self.recent_to_fav_btn.clicked.connect(self._favorite_selected_recent)
        self.recent_clear_btn.clicked.connect(self._clear_recent_profiles)
        self.fav_remove_btn.clicked.connect(self._remove_selected_favorite)
        self.recent_list.itemDoubleClicked.connect(self._open_profile_item)
        self.favorite_list.itemDoubleClicked.connect(self._open_profile_item)
        self.recent_list.itemSelectionChanged.connect(self._on_recent_selection_changed)
        self.favorite_list.itemSelectionChanged.connect(self._on_favorite_selection_changed)
        fav_model = self.favorite_list.model()
        if fav_model:
            fav_model.rowsMoved.connect(self._on_favorite_rows_moved)
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
        if hasattr(self, "keyboard_settings_btn"):
            self.keyboard_settings_btn.clicked.connect(self._open_keyboard_settings)
        if hasattr(self, "keyboard_test_btn"):
            self.keyboard_test_btn.clicked.connect(self._run_keyboard_test_main)
        if hasattr(self, "keyboard_install_btn"):
            self.keyboard_install_btn.clicked.connect(self._run_interception_installer)
        self.add_macro_btn.clicked.connect(self._add_macro)
        self.edit_macro_btn.clicked.connect(self._edit_macro)
        self.clone_macro_btn.clicked.connect(self._clone_macro)
        self.del_macro_btn.clicked.connect(self._delete_macro)
        self.macro_table.doubleClicked.connect(lambda _: self._edit_macro())
        self.macro_table.customContextMenuRequested.connect(self._macro_context_menu)
    # 정렬/키 헬퍼 ---------------------------------------------------------
    def _name_sort_key(self, name: str):
        """
        이름을 글자 단위로 정렬 키로 변환한다.
        우선순위: 한글(0) > 영문(1) > 숫자(2) > 기타(3), 이후 동일 순서로 다음 글자를 비교한다.
        """
        def _bucket(ch: str) -> int:
            if ch.isascii() and ch.isalpha():
                return 0  # 영문 우선
            if "가" <= ch <= "힣":
                return 1  # 한글
            if ch.isdigit():
                return 2  # 숫자
            return 3      # 기타 기호
        if not name:
            return ((3, ""),)
        key_parts = [(_bucket(ch), ch.casefold()) for ch in name]
        # 길이 차이로 끝까지 동일한 경우를 안정적으로 구분
        key_parts.append((4, len(name)))
        return tuple(key_parts)
    def _sorted_preset_names(self) -> list[str]:
        names = list(self._presets.keys())
        return sorted(
            names,
            key=lambda n: (-1, "") if n == "사용자 설정" else self._name_sort_key(n),
        )
    def _sort_pairs_by_name(self, pairs: list[tuple[str, str]]) -> list[tuple[str, str]]:
        return sorted(pairs, key=lambda pair: self._name_sort_key(pair[0]))
    # Variable helpers ---------------------------------------------------
    def _on_variable_item_changed(self, _item):
        if getattr(self, "_updating_variables", False):
            return
        self._mark_dirty()
        self._refresh_variable_completers()
        self._ensure_trailing_blank(_item.tableWidget() if hasattr(_item, "tableWidget") else None)
    def _configure_variable_table(self, table: QtWidgets.QTableWidget, *, rows_per_column: int = 12):
        table.setProperty("rows_per_column", max(1, rows_per_column))
        table.setColumnCount(2)
        table.setRowCount(rows_per_column)
        table.setHorizontalHeaderLabels(["이름1", "값1"])
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
            "QTableWidget#variableTable::item:selected { background: #ffe9b3; color: #000000; }"
            "QTableWidget#variableTable::item:focus { background: #ffe9b3; color: #000000; }"
        )
        table.setItemDelegate(_VariableSeparatorDelegate(table))
    def _rows_per_column(self, table: QtWidgets.QTableWidget) -> int:
        base = int(table.property("rows_per_column") or 12)
        vh = table.verticalHeader() if hasattr(table, "verticalHeader") else None
        row_h = vh.defaultSectionSize() if vh else (table.fontMetrics().height() + 8)
        view_h = table.viewport().height() if hasattr(table, "viewport") else 0
        auto = int(view_h / row_h) if view_h and row_h else base
        return max(1, auto or base or 12)
    def _ensure_trailing_blank(self, table: QtWidgets.QTableWidget | None):
        if table is None:
            return
        rows_per_col = self._rows_per_column(table)
        pairs = self._variable_pairs_from_table(table)
        capacity = (table.columnCount() // 2) * rows_per_col
        if len(pairs) >= capacity:
            self._set_variable_pairs(table, pairs)
    def _variable_pairs_from_table(self, table: QtWidgets.QTableWidget) -> list[tuple[str, str]]:
        pairs: list[tuple[str, str]] = []
        rows = table.rowCount()
        cols = table.columnCount()
        for c in range(0, cols, 2):
            for r in range(rows):
                name_item = table.item(r, c)
                val_item = table.item(r, c + 1) if c + 1 < cols else None
                name = name_item.text().strip() if name_item else ""
                val = val_item.text().strip() if val_item else ""
                if not name and not val:
                    continue
                pairs.append((name, val))
        return pairs
    def _set_variable_pairs(self, table: QtWidgets.QTableWidget, pairs: list[tuple[str, str]]):
        rows_per_col = self._rows_per_column(table)
        slots_needed = len(pairs) + 1  # 항상 한 칸 여유를 둔다.
        cols = max(1, math.ceil(slots_needed / rows_per_col)) * 2
        rows = rows_per_col
        prev_updating = getattr(self, "_updating_variables", False)
        table.setProperty("current_rows_per_col", rows_per_col)
        self._updating_variables = True
        try:
            table.clearContents()
            table.setColumnCount(cols)
            headers: list[str] = []
            for idx in range(cols // 2):
                headers.extend([f"이름{idx + 1}", f"값{idx + 1}"])
            table.setHorizontalHeaderLabels(headers)
            table.setRowCount(rows)
            for idx, (name, val) in enumerate(pairs):
                r = idx % rows_per_col
                c = (idx // rows_per_col) * 2
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
    def _extract_variable_refs(self, obj: object) -> set[str]:
        names: set[str] = set()
        if isinstance(obj, str):
            for m in VariableResolver._pattern.finditer(obj):
                name = m.group("name") or m.group("name2") or m.group("name3")
                if name:
                    names.add(name)
        elif isinstance(obj, dict):
            for val in obj.values():
                names.update(self._extract_variable_refs(val))
        elif isinstance(obj, (list, tuple, set)):
            for item in obj:
                names.update(self._extract_variable_refs(item))
        return names
    def _find_variable_usages(self, targets: list[tuple[str, str]]) -> dict[tuple[str, str], list[str]]:
        target_set = {(cat, name.strip()) for cat, name in targets if name and str(name).strip()}
        if not target_set:
            return {}
        usages: dict[tuple[str, str], list[str]] = {t: [] for t in target_set}
        for idx, macro in enumerate(self._collect_macros(), 1):
            try:
                macro_dict = macro.to_dict()
            except Exception:
                continue
            used_names = self._extract_variable_refs(macro_dict)
            if not used_names:
                continue
            try:
                trig_label = macro.trigger_label(include_mode=False)
            except Exception:
                trig_label = getattr(macro, "trigger_key", "")
            label = macro.name or trig_label or f"#{idx}"
            for cat, name in target_set:
                if name in used_names:
                    usages[(cat, name)].append(label)
        return {k: v for k, v in usages.items() if v}
    def _delete_selected_variable_pairs(self, table: QtWidgets.QTableWidget, category: str | None = None) -> bool:
        indexes = table.selectionModel().selectedIndexes()
        if not indexes:
            return False
        rows_per_col = int(table.property("current_rows_per_col") or table.property("rows_per_column") or table.rowCount() or 1)
        to_remove = sorted(
            {(idx.column() // 2) * rows_per_col + idx.row() for idx in indexes},
            reverse=True,
        )
        pairs = self._variable_pairs_from_table(table)
        targets: list[tuple[str, str]] = []
        for pidx in to_remove:
            if 0 <= pidx < len(pairs):
                name = pairs[pidx][0]
                if name:
                    targets.append((category or "", name))
        usages = self._find_variable_usages(targets)
        if usages:
            lines = [f"{cat or 'var'}:{name} -> {', '.join(macros)}" for (cat, name), macros in usages.items()]
            msg = "다음 변수가 매크로에서 사용 중입니다. 삭제하면 참조가 끊어집니다.\n\n" + "\n".join(lines) + "\n\n그래도 삭제하시겠습니까?"
            res = QtWidgets.QMessageBox.question(
                self,
                "변수 사용 중",
                msg,
                QtWidgets.QMessageBox.StandardButton.Yes | QtWidgets.QMessageBox.StandardButton.No,
                QtWidgets.QMessageBox.StandardButton.No,
            )
            if res != QtWidgets.QMessageBox.StandardButton.Yes:
                return False
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
        name = (name or "").strip()
        if not table or not name:
            return False
        if category == "color" and not default_value:
            default_value = "000000"
        existing_names = {n for n, _ in self._variable_pairs_from_table(table)}
        if name in existing_names:
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
                pairs = self._sort_pairs_by_name(list(data.items()))
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
            if not self._state_path.parent.exists():
                self._state_path.parent.mkdir(parents=True, exist_ok=True)
            self._state_path.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")
        except Exception as exc:
            self._append_log(f"상태 파일 저장 오류: {exc}")
    def _update_state(self, key: str, value):
        state = dict(self._state) if isinstance(self._state, dict) else {}
        state[key] = value
        self._state = state
        self._write_state(state)
    def _dedupe_profile_paths(self, items) -> list[str]:
        seen = set()
        result: list[str] = []
        for raw in items or []:
            if not isinstance(raw, str):
                continue
            norm = _normalize_profile_path(raw)
            if norm in seen:
                continue
            seen.add(norm)
            result.append(norm)
        return result[:MAX_RECENT_PROFILES]
    def _persist_profile_history(self):
        self._update_state(
            "profile_history",
            {
                "recent": self._recent_profiles,
                "favorites": self._favorite_profiles,
            },
        )
    def _profile_display_text(self, path: str) -> str:
        try:
            p = Path(path)
            name = p.stem or p.name  # 확장자(.json) 숨김
            parent = p.parent.name or str(p.parent)
            if parent.lower() == "setting":
                return name
            return f"{name} · {parent}"
        except Exception:
            return path
    def _record_recent_profile(self, path: str | None):
        if not path:
            return
        norm = _normalize_profile_path(path)
        if not norm:
            return
        self._recent_profiles = [p for p in self._recent_profiles if p != norm]
        self._recent_profiles.insert(0, norm)
        self._recent_profiles = self._recent_profiles[:MAX_RECENT_PROFILES]
        self._persist_profile_history()
        self._refresh_profile_lists()
    def _set_favorite_path(self, path: str | None, *, favorite: bool = True):
        if not path:
            return
        norm = _normalize_profile_path(path)
        if not norm:
            return
        if favorite:
            if norm not in self._favorite_profiles:
                self._favorite_profiles.insert(0, norm)
                self._favorite_profiles = self._favorite_profiles[:MAX_RECENT_PROFILES]
        else:
            self._favorite_profiles = [p for p in self._favorite_profiles if p != norm]
        self._persist_profile_history()
        self._refresh_profile_lists()
        self._refresh_profile_header()
    def _sync_favorite_order_from_list(self):
        """현재 즐겨찾기 리스트 순서를 내부 상태에 반영한다."""
        if not hasattr(self, "favorite_list"):
            return
        paths: list[str] = []
        for idx in range(self.favorite_list.count()):
            item = self.favorite_list.item(idx)
            if not item:
                continue
            raw = item.data(QtCore.Qt.ItemDataRole.UserRole)
            norm = _normalize_profile_path(str(raw)) if raw else None
            if norm:
                paths.append(norm)
        self._favorite_profiles = self._dedupe_profile_paths(paths)
        self._persist_profile_history()
        if hasattr(self, "fav_label"):
            self.fav_label.setText(f"즐겨찾기 ({len(self._favorite_profiles)})")
        self._update_profile_list_buttons()
    def _on_favorite_rows_moved(
        self,
        _parent: QtCore.QModelIndex,
        _start: int,
        _end: int,
        _dest_parent: QtCore.QModelIndex,
        _dest_row: int,
    ):
        self._sync_favorite_order_from_list()
    def _clear_recent_profiles(self):
        if not self._recent_profiles:
            return
        res = QtWidgets.QMessageBox.question(
            self,
            "최근 목록 비우기",
            "최근에 불러온 설정 목록을 모두 비울까요?",
            QtWidgets.QMessageBox.StandardButton.Yes | QtWidgets.QMessageBox.StandardButton.No,
            QtWidgets.QMessageBox.StandardButton.No,
        )
        if res != QtWidgets.QMessageBox.StandardButton.Yes:
            return
        self._recent_profiles = []
        self._persist_profile_history()
        self._refresh_profile_lists()
    def _refresh_profile_lists(self):
        if not hasattr(self, "recent_list"):
            return
        def _fill_list(widget: QtWidgets.QListWidget, paths: list[str], *, highlight_current: bool):
            widget.clear()
            for path in paths:
                item = QtWidgets.QListWidgetItem(self._profile_display_text(path))
                item.setToolTip(path)
                item.setData(QtCore.Qt.ItemDataRole.UserRole, path)
                norm = _normalize_profile_path(path)
                if highlight_current and current_norm and norm == current_norm:
                    # 현재 불러온 프로필은 배경/글자색을 강조
                    bg = QtGui.QColor(active_bg)
                    fg = QtGui.QColor(active_fg)
                    item.setData(QtCore.Qt.ItemDataRole.BackgroundRole, bg)
                    item.setData(QtCore.Qt.ItemDataRole.ForegroundRole, fg)
                    font = item.font()
                    font.setBold(True)
                    item.setFont(font)
                widget.addItem(item)
            widget.setEnabled(bool(paths))
        current_norm = _normalize_profile_path(self.current_profile_path) if self.current_profile_path else None
        # 강조 색상: 밝은 테마는 짙은 주황, 어두운 테마는 선명한 녹색
        active_bg = "#ffe08a" if not self._theme.get("is_dark") else "#2faa4f"
        active_fg = "#2d1b00" if not self._theme.get("is_dark") else "#f0fff0"
        in_favorites = current_norm in self._favorite_profiles if current_norm else False
        highlight_recent = bool(current_norm and not in_favorites)
        highlight_fav = bool(current_norm and in_favorites)
        _fill_list(self.recent_list, self._recent_profiles, highlight_current=highlight_recent)
        _fill_list(self.favorite_list, self._favorite_profiles, highlight_current=highlight_fav)
        if hasattr(self, "recent_label"):
            self.recent_label.setText(f"최근 불러온 ({len(self._recent_profiles)})")
        if hasattr(self, "fav_label"):
            self.fav_label.setText(f"즐겨찾기 ({len(self._favorite_profiles)})")
        self._update_profile_list_buttons()
    def _refresh_profile_header(self):
        path = self.current_profile_path
        self._update_title()
        if hasattr(self, "profile_path_label"):
            if path:
                self.profile_path_label.setText(_elide_middle(str(path), 72))
                self.profile_path_label.setToolTip(str(path))
            else:
                self.profile_path_label.setText("새 프로필 (미저장)")
                self.profile_path_label.setToolTip("파일로 저장하거나 불러오면 목록에 표시됩니다.")
    def _selected_profile_path(self, widget: QtWidgets.QListWidget) -> str | None:
        item = widget.currentItem()
        if not item:
            return None
        path = item.data(QtCore.Qt.ItemDataRole.UserRole)
        return str(path) if path else None
    def _open_profile_item(self, item: QtWidgets.QListWidgetItem | None):
        if item is None:
            return
        path = item.data(QtCore.Qt.ItemDataRole.UserRole)
        if path:
            self._open_profile_path(str(path))
    def _load_selected_profile(self, widget: QtWidgets.QListWidget):
        path = self._selected_profile_path(widget)
        if path:
            self._open_profile_path(path)
    def _favorite_selected_recent(self):
        path = self._selected_profile_path(self.recent_list)
        if path:
            self._set_favorite_path(path, favorite=True)
    def _on_recent_selection_changed(self):
        if getattr(self, "_syncing_profile_lists", False):
            return
        self._syncing_profile_lists = True
        try:
            self.favorite_list.clearSelection()
        finally:
            self._syncing_profile_lists = False
        self._update_profile_list_buttons()
    def _on_favorite_selection_changed(self):
        if getattr(self, "_syncing_profile_lists", False):
            return
        self._syncing_profile_lists = True
        try:
            self.recent_list.clearSelection()
        finally:
            self._syncing_profile_lists = False
        self._update_profile_list_buttons()
    def _remove_selected_favorite(self):
        path = self._selected_profile_path(self.favorite_list)
        if path:
            self._set_favorite_path(path, favorite=False)
    def _toggle_favorite_current(self):
        # 더 이상 상단 버튼에서 즐겨찾기를 토글하지 않음. 최근/즐겨찾기 리스트 버튼을 사용한다.
        pass
    def _update_profile_list_buttons(self):
        has_recent = bool(self.recent_list.selectedItems())
        has_fav = bool(self.favorite_list.selectedItems())
        for btn in (self.recent_load_btn, self.recent_to_fav_btn):
            btn.setEnabled(has_recent)
        for btn in (self.fav_load_btn, self.fav_remove_btn):
            btn.setEnabled(has_fav)
        if hasattr(self, "recent_clear_btn"):
            self.recent_clear_btn.setEnabled(bool(self._recent_profiles))
    def _open_profile_path(self, path: str):
        if not path:
            return
        if not Path(path).exists():
            QtWidgets.QMessageBox.warning(self, "불러오기 실패", "파일이 존재하지 않습니다.")
            self._recent_profiles = [p for p in self._recent_profiles if p != path]
            self._favorite_profiles = [p for p in self._favorite_profiles if p != path]
            self._persist_profile_history()
            self._refresh_profile_lists()
            return
        if not self._confirm_save_if_dirty():
            return
        self._load_profile_from_path(path)
    def _persist_screenshot_state(self, data: dict):
        self._update_state("screenshot", data)
    def _persist_debugger_state(self, data: dict):
        self._debugger_state = data or {}
        self._update_state("debugger", self._debugger_state)
    def _persist_color_calc_state(self, data: dict):
        self._color_calc_state = data or {}
        self._update_state("color_calc", self._color_calc_state)
    def _persist_pixel_test_state(self, data: dict):
        self._update_state("pixel_test", data)
    def _persist_image_viewer_state(self, data: dict):
        self._image_viewer_state = data or {}
        self._update_state("image_viewer", self._image_viewer_state)
    def _persist_preset_transfer_state(self, data: dict):
        state = dict(self._preset_transfer_state) if isinstance(self._preset_transfer_state, dict) else {}
        state["sample_preset"] = data or {}
        self._preset_transfer_state = state
        self._update_state("preset_transfer", state)
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
            min_cnt = max(1, int(cfg.get("min_count", getattr(self.profile, "pixel_min_count", 1) or 1)))
            region = tuple(int(v) for v in region)
            color = tuple(int(c) for c in color)
            self.engine.update_pixel_test(region, color, tol, expect, min_cnt)
        except Exception:
            pass
    def _on_debugger_closed(self):
        # 디버거를 닫을 때 테스트 루프도 안전하게 종료
        self._stop_pixel_test_loop()
    def _update_title(self):
        if self.current_profile_path:
            name = Path(self.current_profile_path).name
            path_txt = str(Path(self.current_profile_path))
        else:
            name = "새 프로필"
            path_txt = name
        dirty_mark = "*" if self.dirty else ""
        self.setWindowTitle(f"{self.base_title} - {path_txt}{dirty_mark}")
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
    def _macro_trigger_texts(self, macro: Macro) -> tuple[str, str]:
        try:
            triggers = macro.trigger_list()
        except Exception:
            triggers = list(getattr(macro, "triggers", []) or [])
        labels: list[str] = []
        modes: list[str] = []
        for trig in triggers:
            key = getattr(trig, "key", "") or ""
            mode = getattr(trig, "mode", "") or ""
            mode_txt = "1회 실행" if str(mode).strip().lower() == "once" else mode
            if key:
                labels.append(f"{key} ({mode_txt})" if mode_txt else key)
            if mode_txt:
                modes.append(mode_txt)
        trigger_text = ", ".join(labels[:3]) + ("..." if len(labels) > 3 else "")
        if not trigger_text:
            trigger_text = getattr(macro, "trigger_key", "") or ""
        mode_text = ", ".join(dict.fromkeys(modes)) if modes else (getattr(macro, "mode", "") or "")
        return trigger_text, mode_text
    def _set_macro_row(self, row: int, macro: Macro):
        scope_text = self._macro_scope_text(macro)
        trigger_text, mode_text = self._macro_trigger_texts(macro)
        values = [
            str(row + 1),
            macro.name or "",
            trigger_text,
            mode_text,
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
        trigger_label = ""
        if macro:
            try:
                trigger_label = macro.trigger_label(include_mode=False)
            except Exception:
                trigger_label = getattr(macro, "trigger_key", "") or ""
        base = (macro.name if macro else "") or trigger_label or ""
        base = base.strip() or "매크로"
        existing = {m.name for m in self._collect_macros() if isinstance(m, Macro) and m.name}
        candidate = f"{base} 복사본"
        if candidate not in existing:
            return candidate
        suffix = 2
        while f"{candidate} {suffix}" in existing:
            suffix += 1
        return f"{candidate} {suffix}"
    def _macro_picker_items(self, exclude: Macro | None = None) -> list[str]:
        items: list[str] = []
        for m in self._collect_macros():
            if exclude is not None and m is exclude:
                continue
            name = (m.name or "").strip()
            try:
                trigger = m.trigger_label(include_mode=False)
            except Exception:
                trigger = (m.trigger_key or "").strip()
            label = name or trigger
            if label:
                items.append(label)
        uniq: list[str] = []
        seen = set()
        for item in items:
            key = item.lower()
            if key in seen:
                continue
            seen.add(key)
            uniq.append(item)
        return uniq
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
            macro_list_provider=lambda: self._macro_picker_items(),
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
            macro_list_provider=lambda m=macro: self._macro_picker_items(exclude=m),
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
        self._refresh_profile_header()
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
        self._record_recent_profile(path)
        self._refresh_profile_header()
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
        self._record_recent_profile(path)
        self._refresh_profile_header()
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
        min_count = max(1, int(getattr(prof, "pixel_min_count", 1) or 1))
        region_text = prof.pixel_region_raw or ",".join(str(v) for v in region)
        color_text = prof.pixel_color_raw or _rgb_to_hex(color)
        self._pixel_test_defaults.update(
            {
                "region_raw": region_text,
                "color_raw": color_text,
                "tolerance": tol,
                "expect_exists": expect,
                "min_count": min_count,
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
            min_cnt = max(1, int(getattr(self.profile, "pixel_min_count", 1) or 1))
            self.engine.update_pixel_test(region, color, tol, expect, min_cnt)
        except Exception:
            pass
    def _update_pixel_profile(
        self,
        region: Region,
        color: RGB,
        tolerance: int,
        expect_exists: bool,
        min_count: int = 1,
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
        if hasattr(self.profile, "pixel_min_count"):
            self.profile.pixel_min_count = max(1, int(min_count))
        if hasattr(self.profile, "pixel_expect_exists"):
            self.profile.pixel_expect_exists = bool(expect_exists)
        self._refresh_pixel_defaults(self.profile)
        self.engine.update_pixel_test(region, color, tolerance, expect_exists, max(1, int(min_count)))
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
        min_count = self._pixel_test_defaults.get("min_count")
        min_count_val = max(1, int(min_count)) if min_count is not None else 1
        interval = int(self._pixel_test_defaults.get("interval", 200) or 200)
        return {
            "region": region_txt,
            "color": color_txt,
            "tolerance": tol_val,
            "expect_exists": expect_val,
            "min_count": min_count_val,
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
                min_count=cfg.get("min_count", 1),
                source=cfg.get("source"),
                label=cfg.get("label"),
                pattern=cfg.get("pattern"),
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
            color_raw = config.get("color", (0, 0, 0))
            color = tuple(int(c) for c in color_raw) if color_raw is not None else None
            tolerance = int(config.get("tolerance", 0))
            expect_exists = bool(config.get("expect_exists", True))
            min_count = max(1, int(config.get("min_count", 1) or 1))
            interval = max(50, int(config.get("interval", 200) or 200))
            pattern_name = config.get("pattern")
        except Exception as exc:
            self._append_log(f"픽셀 테스트 시작 실패: {exc}")
            return
        self._pixel_test_defaults["interval"] = interval
        self._pixel_test_defaults["tolerance"] = tolerance
        self._pixel_test_defaults["min_count"] = min_count
        label = config.get("label")
        self._pixel_test_config = {
            "region": region,
            "color": color,
            "pattern": pattern_name,
            "tolerance": tolerance,
            "expect_exists": expect_exists,
            "min_count": min_count,
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
                min_count=min_count,
                region_raw=config.get("region_raw"),
                color_raw=config.get("color_raw"),
                mark_dirty=not self._loading_profile,
            )
            self._persist_pixel_test_state(
                {
                    "region": config.get("region_raw") or ",".join(str(v) for v in region),
                    "color": config.get("color_raw") or _rgb_to_hex(color),
                    "pattern": pattern_name,
                    "tolerance": tolerance,
                    "expect_exists": expect_exists,
                    "min_count": min_count,
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
            min_count=min_count,
            source=source,
            label=label,
            pattern=pattern_name,
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
            image_provider = payload.get("image_provider")
            dbg = getattr(self, "debugger", None)
            use_viewer_image = bool(getattr(dbg, "use_viewer_image", False)) if dbg else False
            if image_provider is None and use_viewer_image and callable(getattr(self, "_viewer_image_provider", None)):
                image_provider = self._viewer_image_provider
            override_frame = None
            override_label = None
            if use_viewer_image and callable(image_provider):
                try:
                    img_payload = image_provider()
                    if isinstance(img_payload, dict):
                        override_frame = img_payload.get("frame")
                        override_label = img_payload.get("label")
                    elif isinstance(img_payload, tuple) and len(img_payload) == 2:
                        override_frame, override_label = img_payload
                    elif isinstance(img_payload, np.ndarray):
                        override_frame = img_payload
                except Exception:
                    override_frame = None
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
                if override_frame is not None:
                    try:
                        self.engine.set_debug_image_override(override_frame, label=override_label)
                    except Exception:
                        pass
                else:
                    try:
                        self.engine.clear_debug_image_override()
                    except Exception:
                        pass
                result = self.engine.debug_condition_tree(
                    cond_obj,
                    key_states=self._condition_debug_key_states,
                    resolver=resolver,
                    vars_ctx=vars_ctx,
                )
            except Exception as exc:
                return {"error": str(exc)}
            finally:
                try:
                    self.engine.clear_debug_image_override()
                except Exception:
                    pass
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
        try:
            self.engine.clear_debug_image_override()
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
            label.setStyleSheet(f"{base} color: {color}; font-weight: bold;")
            return
        if hasattr(self, "running_label") and label is self.running_label and on:
            label.setStyleSheet(
                f"{base} color: #ffffff; background: #2c7a3d; border-color: #1f5f2d; font-weight: bold;"
            )
            return
        else:
            color = "limegreen" if on else "gray"
        label.setStyleSheet(f"{base} color: {color}; font-weight: bold;")
    def _set_capture_status(self, running: bool):
        self._last_capture_running = bool(running)
        if hasattr(self, "capture_label"):
            base = getattr(self, "_status_badge_style", "")
            if running:
                self.capture_label.setVisible(True)
                self.capture_label.setText("스크린샷 캡처중")
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
        if hasattr(self, "hardware_label"):
            base = getattr(self, "_status_badge_style", "")
            self.hardware_label.setText(mode_txt)
            self.hardware_label.setStyleSheet(f"{base} color: {color}; font-weight: bold;")
        test_key = backend.get("keyboard_test_key") or getattr(self.profile, "keyboard_test_key", "f24")
        self.profile.input_mode = requested
        self.profile.keyboard_test_key = test_key
        hint = getattr(self, "_status_hint", "")
        if hint:
            self.statusBar().showMessage(f"{hint} | 입력 {mode_txt}")
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
    def _clear_log_view(self):
        if hasattr(self, "log_view") and self.log_view:
            self.log_view.clear()
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
        self._persist_screenshot_state(_current_screenshot_state(self))
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
def _mw_pattern_names(self) -> list[str]:
    patterns = _load_shared_patterns()
    return sorted(patterns.keys())
def _mw_open_pattern_manager(self, parent=None):
    dlg = PixelPatternManagerDialog(
        parent or self,
        patterns=_load_shared_patterns(),
        open_image_viewer=getattr(self, "_open_image_viewer_dialog", None),
        sample_provider=getattr(self, "_current_viewer_sample", None),
    )
    # Qt parent는 호출자(widget)로 두되, 실제 패턴 저장/동기화는 항상 메인 창을 기준으로 한다.
    dlg._owner = self
    def _sync_patterns_from_dlg(_code: int):
        """Close 시점에도 패턴을 한 번 더 저장/동기화해 포인트 유실을 막는다.
        프로필 저장 여부와 무관하게 pattern/patterns.json 에만 기록한다.
        """
        try:
            row = dlg.list_widget.currentRow()
            if row >= 0:
                dlg._current_name = dlg._row_name(row)
            dlg._save_current_pattern(name_hint=dlg._current_name)
        except Exception:
            pass
        try:
            if hasattr(self, "engine"):
                self.engine._pixel_patterns = copy.deepcopy(dlg.patterns)
        except Exception:
            pass
    dlg.finished.connect(_sync_patterns_from_dlg)
    _run_dialog_non_modal(dlg)
# Monkey patch helper methods onto MacroWindow without touching the large class body above.
try:
    MacroWindow._pattern_names = _mw_pattern_names  # type: ignore[attr-defined]
    MacroWindow._open_pattern_manager = _mw_open_pattern_manager  # type: ignore[attr-defined]
    def _mw_current_viewer_sample(self):
        dlg = getattr(self, "_image_viewer_dialog", None)
        sample = getattr(dlg, "_last_sample", None) if dlg else None
        if not sample or not isinstance(sample, dict):
            return None
        pos = sample.get("pos")
        if not pos or not isinstance(pos, (list, tuple)) or len(pos) != 2:
            return None
        color = sample.get("color")
        if isinstance(color, QtGui.QColor):
            color_val = color
        elif isinstance(color, (list, tuple)) and len(color) >= 3:
            color_val = QtGui.QColor(int(color[0]), int(color[1]), int(color[2]))
        else:
            return None
        return {"pos": (int(pos[0]), int(pos[1])), "color": color_val}
    MacroWindow._current_viewer_sample = _mw_current_viewer_sample  # type: ignore[attr-defined]
except Exception:
    pass
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
