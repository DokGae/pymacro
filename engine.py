from __future__ import annotations

import copy
import ctypes
import io
import os
import queue
import random
import re
import sys
import threading
import time
import json
from pathlib import Path
from dataclasses import dataclass, field
from typing import Any, Dict, Iterable, List, Literal, Optional, Set, Tuple

import numpy as np
from PIL import Image

from lib.interception import Interception, KeyFilter, KeyState
from lib.input_backend import InterceptionBackend, KeyboardBackendStatus, KeyDelayConfig, SoftwareBackend
from lib.keyboard import get_interception, get_keystate, to_scan_code
from lib.pixel import (
    RGB,
    Region,
    PixelPattern,
    capture_region,
    capture_region_np,
    find_color_in_region,
    find_pattern_in_region,
)
from lib.processes import get_foreground_process

ConditionType = Literal["key", "pixel", "all", "any", "var", "timer"]
KeyMode = Literal["press", "down", "up", "hold", "released"]
ActionType = Literal[
    "press",
    "down",
    "up",
    "mouse_click",
    "mouse_down",
    "mouse_up",
    "mouse_move",
    "sleep",
    "macro_stop",
    "if",
    "label",
    "goto",
    "return",
    "continue",
    "break",
    "pixel_get",
    "group",
    "noop",
    "set_var",
    "timer",
]
GroupMode = Literal["all", "first_true", "first_true_continue", "first_true_return", "while", "repeat_n"]
StepType = Literal["press", "down", "up", "sleep", "if", "loop_while"]  # legacy 호환용
MacroMode = Literal["hold", "toggle"]
VarCategory = Literal["sleep", "region", "color", "key", "var"]
DEFAULT_BASE_RESOLUTION: tuple[int, int] = (1920, 1080)
DEFAULT_BASE_SCALE: float = 100.0
_TRIGGER_MOD_ALIASES = {
    "ctrl": {"ctrl", "control", "lctrl", "rctrl", "leftctrl", "rightctrl"},
    "shift": {"shift", "lshift", "rshift", "leftshift", "rightshift"},
    "alt": {"alt", "lalt", "ralt", "leftalt", "rightalt", "menu"},
    "win": {"win", "lwin", "rwin", "super", "meta", "cmd", "command", "windows"},
}
_TRIGGER_MOD_KEYS = set(_TRIGGER_MOD_ALIASES.keys())

PATTERN_DIR = Path(__file__).parent / "pattern"
PATTERN_FILE = PATTERN_DIR / "patterns.json"


def _load_shared_patterns() -> Dict[str, PixelPattern]:
    """pattern 폴더의 각 패턴 파일(*.json)을 개별로 읽어 공용 패턴을 만든다."""
    result: Dict[str, PixelPattern] = {}
    try:
        if not PATTERN_DIR.exists():
            return {}
        for path in PATTERN_DIR.glob("*.json"):
            if path.name == "patterns.json":
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
        # 레거시 patterns.json 병합(존재하면 이름이 겹치지 않을 때만)
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


def _normalize_trigger_part(key: str) -> str:
    low = str(key or "").strip().lower()
    for canon, aliases in _TRIGGER_MOD_ALIASES.items():
        if low in aliases:
            return canon
    return low


def parse_trigger_keys(trigger_key: str) -> List[str]:
    """'ctrl+shift+w' -> ['ctrl', 'shift', 'w']; invalid 부분은 무시."""
    if not trigger_key:
        return []
    mouse_names = {"mouse1", "mouse2", "mouse3", "mouse4", "mouse5", "lmb", "rmb", "mmb", "mb4", "mb5", "x1", "x2", "mouse_left", "mouse_right", "mouse_middle"}
    ordered_keys: List[str] = []
    seen: Set[str] = set()
    for raw in re.split(r"[+]", str(trigger_key)):
        norm = _normalize_trigger_part(raw)
        if not norm:
            continue
        try:
            sc = to_scan_code(norm)
        except Exception:
            sc = 0
        if sc <= 0 and norm not in mouse_names:
            continue
        if norm in seen:
            continue
        seen.add(norm)
        ordered_keys.append(norm)
    mod_order = ["ctrl", "shift", "alt", "win"]
    mods = [m for m in mod_order if m in seen]
    others = [k for k in ordered_keys if k not in mod_order]
    return mods + others


def normalize_trigger_key(trigger_key: str) -> str:
    """조합키를 정규화해 저장/비교용 문자열로 만든다."""
    keys = parse_trigger_keys(trigger_key)
    return "+".join(keys)


def _is_admin() -> bool:
    if not sys.platform.startswith("win"):
        return True
    try:
        return bool(ctypes.windll.shell32.IsUserAnAdmin())
    except Exception:
        return False


def _norm_path(path: Optional[str]) -> str:
    if not path:
        return ""
    try:
        return os.path.normcase(os.path.abspath(path))
    except Exception:
        try:
            return os.path.normcase(path)
        except Exception:
            return str(path)


@dataclass
class MacroVariables:
    sleep: Dict[str, str] = field(default_factory=dict)
    region: Dict[str, str] = field(default_factory=dict)
    color: Dict[str, str] = field(default_factory=dict)
    key: Dict[str, str] = field(default_factory=dict)
    var: Dict[str, str] = field(default_factory=dict)

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "MacroVariables":
        return cls(
            sleep=dict(data.get("sleep", {}) or {}),
            region=dict(data.get("region", {}) or {}),
            color=dict(data.get("color", {}) or {}),
            key=dict(data.get("key", {}) or {}),
            var=dict(data.get("var", {}) or {}),
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "sleep": dict(self.sleep),
            "region": dict(self.region),
            "color": dict(self.color),
            "key": dict(self.key),
            "var": dict(self.var),
        }


class VariableResolver:
    """
    Resolves /name placeholders using category-specific variables.
    """

    def __init__(self, vars: MacroVariables):
        self.vars = vars

    # 변수 이름에 한글 등 유니코드 문자를 허용하고, 공백/구분자만 막는다.
    _pattern = re.compile(r"/(?P<name>[^\s/{}@$]+)|\$\{(?P<name2>[^\s/{}@$]+)\}|@(?P<name3>[^\s/{}@$]+)")

    def resolve(self, text: str, category: VarCategory, *, stack: Optional[Tuple[str, ...]] = None) -> str:
        if text is None:
            return text
        text = str(text).strip()
        if text == "":
            return text
        stack = stack or ()

        def replacer(match: re.Match[str]) -> str:
            name = match.group("name") or match.group("name2") or match.group("name3") or ""
            if name in stack:
                raise ValueError(f"변수 순환 참조: {' -> '.join(stack + (name,))}")
            value_map = getattr(self.vars, category, {}) or {}
            if name not in value_map and category not in ("var",):
                value_map = getattr(self.vars, "var", {}) or {}
            if name not in value_map:
                raise ValueError(f"{category} 변수 '{name}'를 찾을 수 없습니다.")
            raw_val = str(value_map[name])
            return self.resolve(raw_val, category, stack=stack + (name,))

        return self._pattern.sub(replacer, str(text))


def _split_region_offset(raw: str) -> tuple[str, str]:
    if "+" not in raw:
        return raw.strip(), ""
    base, offset = raw.split("+", 1)
    return base.strip(), offset.strip()


def _normalize_region_tuple(region: Any) -> Optional[Tuple[int, int, int, int]]:
    if region is None:
        return None
    try:
        reg_tuple = tuple(region)
    except Exception as exc:
        raise ValueError(f"Region 파싱 실패: {region}") from exc
    if len(reg_tuple) not in (2, 4):
        raise ValueError(f"Region 길이는 2 또는 4여야 합니다: {region}")
    try:
        reg_tuple = tuple(int(v) for v in reg_tuple)  # type: ignore[assignment]
    except Exception as exc:
        raise ValueError(f"Region 정수 변환 실패: {region}") from exc
    if len(reg_tuple) == 2:
        reg_tuple = (reg_tuple[0], reg_tuple[1], 1, 1)
    return reg_tuple  # type: ignore[return-value]


def _parse_mouse_pos(raw: Any, resolver: Optional[VariableResolver]) -> tuple[Optional[tuple[int, int]], Optional[str]]:
    """
    마우스 좌표 문자열/튜플을 (x, y), raw 텍스트 형태로 파싱한다.
    빈값/None이면 (None, None)을 반환한다.
    """
    if raw is None:
        return None, None
    if isinstance(raw, str):
        text_raw = raw.strip()
        if not text_raw:
            return None, None
        resolved = resolver.resolve(text_raw, "var") if resolver else text_raw
        parts = [p.strip() for p in str(resolved).split(",") if p.strip()]
        if len(parts) != 2:
            raise ValueError("마우스 좌표는 x,y 형식이어야 합니다.")
        try:
            x, y = (int(parts[0]), int(parts[1]))
        except Exception as exc:
            raise ValueError("마우스 좌표는 정수여야 합니다.") from exc
        return (x, y), text_raw
    try:
        tup = tuple(raw)
        if len(tup) != 2:
            raise ValueError("마우스 좌표는 x,y 형식이어야 합니다.")
        return (int(tup[0]), int(tup[1])), None
    except Exception as exc:
        raise ValueError("마우스 좌표 파싱 실패") from exc


@dataclass
class Condition:
    type: ConditionType
    enabled: bool = True
    name: Optional[str] = None
    key: Optional[str] = None
    key_mode: Optional[KeyMode] = None
    var_name: Optional[str] = None
    var_value: Optional[str] = None
    var_value_raw: Optional[str] = None
    var_operator: str = "eq"
    region: Optional[Region] = None
    region_raw: Optional[str] = None
    color: Optional[RGB] = None
    color_raw: Optional[str] = None
    pixel_pattern: Optional[str] = None  # 이름 기반으로 패턴 참조
    tolerance: int = 0
    pixel_min_count: int = 1
    pixel_exists: bool = True
    conditions: List["Condition"] = field(default_factory=list)
    on_true: List["Condition"] = field(default_factory=list)
    on_false: List["Condition"] = field(default_factory=list)
    timer_index: Optional[int] = None
    timer_value: Optional[float] = None
    timer_operator: str = "ge"

    @classmethod
    def _parse_region(cls, raw: Any, resolver: Optional[VariableResolver]) -> tuple[Region, Optional[str]]:
        if raw is None:
            return None, None  # type: ignore[return-value]
        region_raw: Optional[str] = None
        value = raw
        if isinstance(raw, str):
            region_raw = raw.strip()
            value = resolver.resolve(region_raw, "region") if resolver else region_raw
        if isinstance(value, str):
            base_text, offset_text = _split_region_offset(value)
            parts = [p.strip() for p in base_text.split(",") if p.strip()]
            if len(parts) not in (2, 4):
                raise ValueError("Region은 x,y(,w,h) 정수여야 합니다.")
            if len(parts) == 2:
                parts.extend(["1", "1"])
            base_nums = [int(p) for p in parts]
            offset_nums = [0, 0, 0, 0]
            if offset_text:
                offset_parts = [p.strip() for p in offset_text.split(",") if p.strip()]
                if len(offset_parts) != 4:
                    raise ValueError("Region 덧셈은 +dx,dy,dw,dh 형식이어야 합니다.")
                offset_nums = [int(p) for p in offset_parts]
            merged = tuple(base_nums[i] + offset_nums[i] for i in range(4))
            return merged, region_raw  # type: ignore[return-value]
        return _normalize_region_tuple(value), region_raw  # type: ignore[arg-type,return-value]

    @classmethod
    def _parse_color(cls, raw: Any, resolver: Optional[VariableResolver]) -> tuple[RGB, Optional[str]]:
        if raw is None:
            return None, None  # type: ignore[return-value]
        color_raw: Optional[str] = None
        value = raw
        if isinstance(raw, str):
            color_raw = raw.strip()
            # 변수 참조는 저장 시 즉시 검증하지 않고 런타임에 해석
            if color_raw.startswith(("/", "$", "@")):
                return None, color_raw  # type: ignore[return-value]
            value = resolver.resolve(color_raw, "color") if resolver else color_raw
        if isinstance(value, str):
            text = value.strip().lstrip("#")
            if len(text) != 6 or not all(c in "0123456789abcdefABCDEF" for c in text):
                raise ValueError("색상은 16진수 6자리(RRGGBB)여야 합니다.")
            return tuple(int(text[i : i + 2], 16) for i in (0, 2, 4)), color_raw  # type: ignore[return-value]
        try:
            return tuple(value), color_raw  # type: ignore[arg-type,return-value]
        except Exception as exc:
            raise ValueError(f"색상 파싱 실패: {raw}") from exc

    @classmethod
    def from_dict(cls, data: Dict[str, Any], resolver: Optional[VariableResolver] = None) -> "Condition":
        ctype = data.get("type", "key")
        conds = [Condition.from_dict(c, resolver) for c in data.get("conditions", [])] if ctype in ("all", "any") else []
        true_branch = [Condition.from_dict(c, resolver) for c in data.get("on_true", [])]
        false_branch = [Condition.from_dict(c, resolver) for c in data.get("on_false", [])]
        key_mode_raw = data.get("key_mode")
        key_mode = str(key_mode_raw).lower() if key_mode_raw else None
        if key_mode and key_mode not in ("press", "down", "up", "hold", "released"):
            key_mode = None
        pixel_exists_raw = data.get("pixel_exists", True)
        if isinstance(pixel_exists_raw, str):
            pixel_exists = pixel_exists_raw.strip().lower() not in ("false", "0", "no")
        else:
            pixel_exists = bool(pixel_exists_raw)
        region, region_raw = cls._parse_region(data.get("region"), resolver)
        color, color_raw = cls._parse_color(data.get("color"), resolver)
        pattern_name = data.get("pixel_pattern") or data.get("pattern_name")
        var_name = data.get("var_name")
        var_value_raw = data.get("var_value_raw", data.get("var_value"))
        var_value = None
        if var_value_raw is not None:
            try:
                var_value = resolver.resolve(str(var_value_raw), "var") if resolver else str(var_value_raw)
            except Exception:
                var_value = str(var_value_raw)
        var_operator_raw = str(data.get("var_operator", "eq")).lower()
        var_operator = "ne" if var_operator_raw == "ne" else "eq"
        timer_idx_raw = data.get("timer_index", data.get("timer_slot"))
        timer_index = None
        try:
            if timer_idx_raw not in (None, ""):
                timer_index = int(timer_idx_raw)
        except Exception:
            timer_index = None
        if timer_index is not None and (timer_index < 1 or timer_index > 20):
            timer_index = None
        min_count_raw = data.get("pixel_min_count", 1)
        try:
            pixel_min_count = max(1, int(min_count_raw))
        except Exception:
            pixel_min_count = 1
        timer_value_raw = data.get("timer_value")
        timer_value: Optional[float] = None
        if timer_value_raw not in (None, ""):
            try:
                resolved = resolver.resolve(str(timer_value_raw), "var") if resolver and isinstance(timer_value_raw, str) else timer_value_raw
                timer_value = float(resolved)
            except Exception:
                try:
                    timer_value = float(timer_value_raw)
                except Exception:
                    timer_value = None
        timer_op_raw = str(data.get("timer_operator", data.get("timer_op", "ge"))).lower()
        timer_operator = timer_op_raw if timer_op_raw in ("ge", "gt", "le", "lt", "eq", "ne") else "ge"
        enabled_raw = data.get("enabled")
        if isinstance(enabled_raw, str):
            enabled_val = enabled_raw.strip().lower() not in ("false", "0", "no")
        else:
            enabled_val = bool(enabled_raw) if enabled_raw is not None else True
        cond = cls(
            type=ctype,
            name=data.get("name"),
            key=data.get("key"),
            key_mode=key_mode,
            var_name=var_name,
            var_value=var_value,
            var_value_raw=str(var_value_raw) if var_value_raw is not None else None,
            var_operator=var_operator,
            region=region,
            region_raw=region_raw,
            color=color,
            color_raw=color_raw,
            pixel_pattern=str(pattern_name).strip() if pattern_name else None,
            tolerance=int(data.get("tolerance", 0) or 0),
            pixel_min_count=pixel_min_count,
            pixel_exists=pixel_exists,
            conditions=conds,
            on_true=true_branch,
            on_false=false_branch,
            timer_index=timer_index,
            timer_value=timer_value,
            timer_operator=timer_operator,
            enabled=enabled_val,
        )
        return cond

    def to_dict(self) -> Dict[str, Any]:
        payload: Dict[str, Any] = {
            "type": self.type,
            "name": self.name,
            "key": self.key,
            "key_mode": self.key_mode,
            "var_name": self.var_name,
            "var_value_raw": self.var_value_raw if self.var_value_raw is not None else self.var_value,
            "var_operator": self.var_operator,
            "region": self.region_raw if self.region_raw is not None else (list(self.region) if self.region else None),
            "color": self.color_raw if self.color_raw is not None else (list(self.color) if self.color else None),
            "pixel_pattern": self.pixel_pattern,
            "tolerance": self.tolerance,
            "pixel_min_count": self.pixel_min_count,
            "pixel_exists": self.pixel_exists,
            "timer_index": self.timer_index,
            "timer_value": self.timer_value,
            "timer_operator": self.timer_operator,
            "enabled": getattr(self, "enabled", True),
        }
        if self.type in ("all", "any"):
            payload["conditions"] = [c.to_dict() for c in self.conditions]
        if self.on_true:
            payload["on_true"] = [c.to_dict() for c in self.on_true]
        if self.on_false:
            payload["on_false"] = [c.to_dict() for c in self.on_false]
        return payload


def _iter_elif_blocks(blocks):
    for blk in blocks or []:
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
        if not isinstance(cond, Condition):
            continue
        if isinstance(enabled_override, bool):
            try:
                cond.enabled = enabled_override
            except Exception:
                pass
        yield cond, list(acts or []), desc or ""


@dataclass
class Action:
    type: ActionType
    name: Optional[str] = None
    description: Optional[str] = None
    enabled: bool = True
    once_per_macro: bool = False
    force_first_run: bool = False
    key: Optional[str] = None
    key_raw: Optional[str] = None
    repeat: int = 1
    repeat_raw: Optional[str] = None
    repeat_range: Optional[tuple[int, int]] = None
    var_name: Optional[str] = None
    var_value: Optional[str] = None
    var_value_raw: Optional[str] = None
    confirm_fails: int = 1
    sleep_ms: int = 0
    sleep_range: Optional[tuple[int, int]] = None
    sleep_raw: Optional[str] = None
    condition: Optional[Condition] = None
    elif_blocks: List[tuple[Condition, List["Action"], str | None]] = field(default_factory=list)
    actions: List["Action"] = field(default_factory=list)
    else_actions: List["Action"] = field(default_factory=list)
    label: Optional[str] = None
    goto_label: Optional[str] = None
    mouse_button: Optional[str] = None
    mouse_pos: Optional[tuple[int, int]] = None
    mouse_pos_raw: Optional[str] = None
    pixel_region: Optional[Region] = None
    pixel_region_raw: Optional[str] = None
    pixel_target: Optional[str] = None
    group_mode: Optional[GroupMode] = None
    group_repeat: Optional[int] = None
    hold_keep_on_pause: bool = False
    timer_index: Optional[int] = None
    timer_value: Optional[float] = None
    key_delay_override_enabled: bool = False
    key_delay_override: Optional[KeyDelayConfig] = None

    @staticmethod
    def parse_sleep(raw: Any) -> tuple[int, Optional[tuple[int, int]]]:
        text = str(raw).strip() if raw is not None else ""
        if text == "":
            return 0, None
        if "~" in text:
            parts = [p.strip() for p in text.split("~")]
            if len(parts) != 2 or any(not p for p in parts):
                raise ValueError("sleep은 정수 또는 범위(예: 1000~2000)여야 합니다.")
            try:
                first, second = (int(parts[0]), int(parts[1]))
            except Exception as exc:
                raise ValueError("sleep은 정수 또는 범위(예: 1000~2000)여야 합니다.") from exc
            low, high = sorted((first, second))
            low = max(0, low)
            high = max(0, high)
            if low == high:
                return low, None
            return low, (low, high)
        try:
            val = int(text)
        except Exception as exc:
            raise ValueError("sleep은 정수 또는 범위(예: 1000~2000)여야 합니다.") from exc
        return max(0, val), None

    @staticmethod
    def parse_repeat(raw: Any) -> tuple[int, Optional[tuple[int, int]], Optional[str]]:
        """
        반복 횟수 파서. 정수 또는 "a~b"/"a-b" 범위를 허용한다.
        returns: (repeat_value, repeat_range, repeat_raw)
        """
        text = str(raw).strip() if raw is not None else ""
        if text == "":
            return 1, None, None
        sep = "~" if "~" in text else "-"
        if sep in text:
            parts = [p.strip() for p in text.split(sep)]
            if len(parts) != 2 or any(not p for p in parts):
                raise ValueError("반복은 정수 또는 범위(예: 1~3)여야 합니다.")
            try:
                first, second = (int(parts[0]), int(parts[1]))
            except Exception as exc:
                raise ValueError("반복은 정수 또는 범위(예: 1~3)여야 합니다.") from exc
            low, high = sorted((first, second))
            if low < 1 or high < 1:
                raise ValueError("반복은 1 이상의 정수 또는 범위(예: 1~3)여야 합니다.")
            normalized = f"{low}~{high}"
            if low == high:
                return low, None, normalized
            return low, (low, high), normalized
        try:
            val = int(text)
        except Exception as exc:
            raise ValueError("반복은 정수 또는 범위(예: 1~3)여야 합니다.") from exc
        if val < 1:
            raise ValueError("반복은 1 이상의 정수 또는 범위(예: 1~3)여야 합니다.")
        return val, None, None

    def sleep_value_text(self) -> str:
        if self.sleep_range:
            low, high = self.sleep_range
            return f"{low}~{high}"
        if self.sleep_raw is not None:
            return self.sleep_raw
        return str(self.sleep_ms)

    def sleep_value_for_export(self) -> int | str:
        if self.sleep_range:
            low, high = self.sleep_range
            return f"{low}~{high}"
        if self.sleep_raw is not None:
            return self.sleep_raw
        return self.sleep_ms

    def resolve_sleep_ms(self) -> int:
        if self.sleep_range:
            low, high = self.sleep_range
            return random.randint(low, high)
        return max(0, int(self.sleep_ms or 0))

    @classmethod
    def from_dict(cls, data: Dict[str, Any], resolver: Optional[VariableResolver] = None) -> "Action":
        typ = data.get("type", "press")
        cond_data = data.get("condition")
        cond = Condition.from_dict(cond_data, resolver) if cond_data else None
        actions = [Action.from_dict(s, resolver) for s in data.get("actions", data.get("steps", []))]
        else_actions = [Action.from_dict(s, resolver) for s in data.get("else_actions", [])]
        elif_blocks: List[tuple[Condition, List["Action"], str | None]] = []
        for blk in data.get("elif_blocks", []) or []:
            try:
                econd = Condition.from_dict(blk.get("condition", {}), resolver)
                eacts = [Action.from_dict(a, resolver) for a in blk.get("actions", [])]
                desc = blk.get("description") or ""
                enabled_raw = blk.get("enabled")
                if isinstance(enabled_raw, bool):
                    try:
                        econd.enabled = enabled_raw
                    except Exception:
                        pass
                elif_blocks.append((econd, eacts, desc))
            except Exception:
                continue
        sleep_ms_raw = data.get("sleep_ms", data.get("sleep", 0))
        sleep_raw: Optional[str] = None
        sleep_value_for_parse = sleep_ms_raw
        if isinstance(sleep_ms_raw, str):
            sleep_raw = sleep_ms_raw.strip()
            sleep_value_for_parse = resolver.resolve(sleep_raw, "sleep") if resolver else sleep_raw
        sleep_ms, sleep_range = cls.parse_sleep(sleep_value_for_parse)
        region_raw = data.get("pixel_region_raw")
        region_val = data.get("pixel_region")
        region = None
        if region_raw is not None:
            region = Condition._parse_region(region_raw, resolver)[0]
        elif region_val is not None:
            region = _normalize_region_tuple(region_val)
        var_value_raw = data.get("var_value_raw", data.get("var_value"))
        var_value = None
        if var_value_raw is not None:
            try:
                var_value = resolver.resolve(str(var_value_raw), "var") if resolver else str(var_value_raw)
            except Exception:
                var_value = str(var_value_raw)
        timer_idx_raw = data.get("timer_index", data.get("timer_slot"))
        timer_index = None
        try:
            if timer_idx_raw not in (None, ""):
                timer_index = int(timer_idx_raw)
        except Exception:
            timer_index = None
        if timer_index is not None and (timer_index < 1 or timer_index > 20):
            timer_index = None
        timer_value_raw = data.get("timer_value")
        timer_value: Optional[float] = None
        if timer_value_raw not in (None, ""):
            try:
                resolved_timer_val = resolver.resolve(str(timer_value_raw), "var") if resolver and isinstance(timer_value_raw, str) else timer_value_raw
                timer_value = float(resolved_timer_val)
            except Exception:
                try:
                    timer_value = float(timer_value_raw)
                except Exception:
                    timer_value = None
        confirm_raw = data.get("confirm_fails", 1)
        try:
            confirm_fails = int(confirm_raw)
        except Exception:
            confirm_fails = 1
        confirm_fails = max(1, confirm_fails)
        override_enabled = bool(data.get("key_delay_override_enabled", False))
        key_delay_override = None
        try:
            if isinstance(data.get("key_delay_override"), dict):
                key_delay_override = KeyDelayConfig.from_dict(data.get("key_delay_override"))
        except Exception:
            key_delay_override = None
        repeat_raw_data = data.get("repeat_raw")
        if repeat_raw_data in (None, ""):
            repeat_raw_data = data.get("repeat", 1)
        try:
            repeat_val, repeat_range, repeat_raw = cls.parse_repeat(repeat_raw_data)
        except Exception:
            repeat_val, repeat_range, repeat_raw = 1, None, None
        mouse_pos_raw_val = data.get("mouse_pos_raw", data.get("mouse_pos"))
        mouse_pos: Optional[tuple[int, int]] = None
        mouse_pos_raw: Optional[str] = None
        if mouse_pos_raw_val is not None:
            try:
                mouse_pos, mouse_pos_raw = _parse_mouse_pos(mouse_pos_raw_val, resolver)
            except Exception:
                mouse_pos = None
                mouse_pos_raw = str(mouse_pos_raw_val).strip() if mouse_pos_raw_val is not None else None
        group_repeat_raw = data.get("group_repeat")
        try:
            group_repeat = max(1, int(group_repeat_raw)) if group_repeat_raw not in (None, "") else None
        except Exception:
            group_repeat = None
        key_raw = data.get("key")
        key_resolved = key_raw
        if resolver and isinstance(key_raw, str) and key_raw.strip():
            try:
                key_resolved = resolver.resolve(key_raw, "key")
            except Exception:
                key_resolved = key_raw
        return cls(
            type=typ,
            name=data.get("name"),
            description=data.get("description"),
            enabled=bool(data.get("enabled", True)),
            once_per_macro=bool(data.get("once_per_macro", False)),
            force_first_run=bool(data.get("force_first_run", False)),
            key=key_resolved,
            key_raw=str(key_raw) if key_raw is not None else None,
            repeat=repeat_val,
            repeat_range=repeat_range,
            repeat_raw=str(repeat_raw) if repeat_raw is not None else None,
            var_name=data.get("var_name"),
            var_value=var_value,
            var_value_raw=str(var_value_raw) if var_value_raw is not None else None,
            confirm_fails=confirm_fails,
            sleep_ms=sleep_ms,
            sleep_range=sleep_range,
            sleep_raw=sleep_raw,
            condition=cond,
            elif_blocks=elif_blocks,
            actions=actions,
            else_actions=else_actions,
            label=data.get("label"),
            goto_label=data.get("goto_label"),
            mouse_button=data.get("mouse_button") or data.get("button"),
            mouse_pos=mouse_pos,
            mouse_pos_raw=mouse_pos_raw,
            pixel_region=region,
            pixel_region_raw=region_raw,
            pixel_target=data.get("pixel_target"),
            group_mode=data.get("group_mode"),
            group_repeat=group_repeat,
            hold_keep_on_pause=bool(data.get("hold_keep_on_pause", False)),
            timer_index=timer_index,
            timer_value=timer_value,
            key_delay_override_enabled=override_enabled,
            key_delay_override=key_delay_override,
        )

    def to_dict(self) -> Dict[str, Any]:
        payload: Dict[str, Any] = {
            "type": self.type,
            "name": self.name,
            "description": self.description,
            "enabled": self.enabled,
            "once_per_macro": self.once_per_macro,
            "force_first_run": getattr(self, "force_first_run", False),
            "key": self.key_raw if self.key_raw is not None else self.key,
            "repeat": self.repeat,
            "repeat_raw": self.repeat_raw if self.repeat_raw is not None else None,
            "var_name": self.var_name,
            "var_value_raw": self.var_value_raw if self.var_value_raw is not None else self.var_value,
            "confirm_fails": self.confirm_fails,
            "sleep_ms": self.sleep_value_for_export(),
            "condition": self.condition.to_dict() if self.condition else None,
            "label": self.label,
            "goto_label": self.goto_label,
            "mouse_button": self.mouse_button,
            "mouse_pos": list(self.mouse_pos) if self.mouse_pos is not None else None,
            "mouse_pos_raw": self.mouse_pos_raw,
            "pixel_region": list(self.pixel_region) if self.pixel_region is not None else None,
            "pixel_region_raw": self.pixel_region_raw,
            "pixel_target": self.pixel_target,
            "group_mode": self.group_mode,
            "group_repeat": self.group_repeat,
            "hold_keep_on_pause": getattr(self, "hold_keep_on_pause", False),
            "timer_index": self.timer_index,
            "timer_value": self.timer_value,
            "key_delay_override_enabled": getattr(self, "key_delay_override_enabled", False),
            "key_delay_override": self.key_delay_override.to_dict() if getattr(self, "key_delay_override", None) else None,
        }
        if self.actions:
            payload["actions"] = [a.to_dict() for a in self.actions]
        if self.elif_blocks:
            blocks: list[dict[str, Any]] = []
            for cond, acts, desc in _iter_elif_blocks(self.elif_blocks):
                blocks.append(
                    {
                        "condition": cond.to_dict(),
                        "actions": [a.to_dict() for a in acts],
                        "description": desc or None,
                    }
                )
            if blocks:
                payload["elif_blocks"] = blocks
        if self.else_actions:
            payload["else_actions"] = [a.to_dict() for a in self.else_actions]
        return payload


@dataclass
class Step:
    type: StepType
    key: Optional[str] = None
    sleep_ms: int = 0
    sleep_range: Optional[tuple[int, int]] = None
    sleep_raw: Optional[str] = None
    condition: Optional[Condition] = None
    steps: List["Step"] = field(default_factory=list)
    else_steps: List["Step"] = field(default_factory=list)

    @staticmethod
    def parse_sleep(raw: Any) -> tuple[int, Optional[tuple[int, int]]]:
        text = str(raw).strip() if raw is not None else ""
        if text == "":
            return 0, None
        if "~" in text:
            parts = [p.strip() for p in text.split("~")]
            if len(parts) != 2 or any(not p for p in parts):
                raise ValueError("sleep은 정수 또는 범위(예: 1000~2000)여야 합니다.")
            try:
                first, second = (int(parts[0]), int(parts[1]))
            except Exception as exc:
                raise ValueError("sleep은 정수 또는 범위(예: 1000~2000)여야 합니다.") from exc
            low, high = sorted((first, second))
            low = max(0, low)
            high = max(0, high)
            if low == high:
                return low, None
            return low, (low, high)
        try:
            val = int(text)
        except Exception as exc:
            raise ValueError("sleep은 정수 또는 범위(예: 1000~2000)여야 합니다.") from exc
        return max(0, val), None

    def sleep_value_text(self) -> str:
        if self.sleep_range:
            low, high = self.sleep_range
            return f"{low}~{high}"
        if self.sleep_raw is not None:
            return self.sleep_raw
        return str(self.sleep_ms)

    def sleep_value_for_export(self) -> int | str:
        if self.sleep_range:
            low, high = self.sleep_range
            return f"{low}~{high}"
        if self.sleep_raw is not None:
            return self.sleep_raw
        return self.sleep_ms

    def resolve_sleep_ms(self) -> int:
        if self.sleep_range:
            low, high = self.sleep_range
            return random.randint(low, high)
        return max(0, int(self.sleep_ms or 0))

    @classmethod
    def from_dict(cls, data: Dict[str, Any], resolver: Optional[VariableResolver] = None) -> "Step":
        cdata = data.get("condition")
        cond = Condition.from_dict(cdata, resolver) if cdata else None
        steps = [Step.from_dict(s, resolver) for s in data.get("steps", [])]
        else_steps = [Step.from_dict(s, resolver) for s in data.get("else_steps", [])]
        sleep_ms_raw = data.get("sleep_ms", 0)
        sleep_raw: Optional[str] = None
        sleep_value_for_parse = sleep_ms_raw
        if isinstance(sleep_ms_raw, str):
            sleep_raw = sleep_ms_raw.strip()
            sleep_value_for_parse = resolver.resolve(sleep_raw, "sleep") if resolver else sleep_raw
        sleep_ms, sleep_range = cls.parse_sleep(sleep_value_for_parse)
        return cls(
            type=data.get("type", "press"),
            key=data.get("key"),
            sleep_ms=sleep_ms,
            sleep_range=sleep_range,
            sleep_raw=sleep_raw,
            condition=cond,
            steps=steps,
            else_steps=else_steps,
        )

    def to_dict(self) -> Dict[str, Any]:
        payload: Dict[str, Any] = {
            "type": self.type,
            "key": self.key,
            "sleep_ms": self.sleep_value_for_export(),
            "condition": self.condition.to_dict() if self.condition else None,
        }
        if self.steps:
            payload["steps"] = [s.to_dict() for s in self.steps]
        if self.else_steps:
            payload["else_steps"] = [s.to_dict() for s in self.else_steps]
        return payload


@dataclass
class AppTarget:
    name: Optional[str] = None
    path: Optional[str] = None

    @classmethod
    def from_any(cls, raw: Any) -> Optional["AppTarget"]:
        if isinstance(raw, cls):
            return raw
        if raw is None:
            return None
        if isinstance(raw, str):
            text = raw.strip()
            if not text:
                return None
            if os.path.sep in text or ":" in text:
                return cls(path=text, name=None)
            return cls(name=text, path=None)
        if isinstance(raw, dict):
            name = raw.get("name")
            path = raw.get("path") or raw.get("exe")
            if not name and not path:
                return None
            return cls(name=name, path=path)
        return None

    def norm_path(self) -> str:
        return _norm_path(self.path)

    def norm_name(self) -> str:
        text = (self.name or "").strip()
        if text:
            return text.lower()
        if self.path:
            try:
                return Path(self.path).name.lower()
            except Exception:
                return str(self.path).lower()
        return ""

    def to_dict(self) -> Dict[str, Any]:
        data: Dict[str, Any] = {}
        if self.name:
            data["name"] = self.name
        if self.path:
            data["path"] = self.path
        return data


@dataclass
class MacroCondition:
    condition: Condition
    actions: List[Step] = field(default_factory=list)
    else_actions: List[Step] = field(default_factory=list)
    name: Optional[str] = None
    enabled: bool = True
    confirm_fails: int = 1

    @classmethod
    def from_dict(cls, data: Dict[str, Any], resolver: Optional[VariableResolver] = None) -> "MacroCondition":
        cond = Condition.from_dict(data.get("condition", {}), resolver)
        actions = [Step.from_dict(s, resolver) for s in data.get("actions", data.get("steps", []))]
        else_actions = [Step.from_dict(s, resolver) for s in data.get("else_actions", data.get("false_actions", []))]
        enabled_raw = data.get("enabled", True)
        enabled = enabled_raw if isinstance(enabled_raw, bool) else str(enabled_raw).strip().lower() not in ("false", "0", "no")
        confirm_fails = int(data.get("confirm_fails", 1) or 1)
        if confirm_fails < 1:
            confirm_fails = 1
        return cls(
            condition=cond,
            actions=actions,
            else_actions=else_actions,
            name=data.get("name"),
            enabled=enabled,
            confirm_fails=confirm_fails,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "condition": self.condition.to_dict(),
            "actions": [s.to_dict() for s in self.actions],
            "else_actions": [s.to_dict() for s in self.else_actions],
            "name": self.name,
            "enabled": self.enabled,
            "confirm_fails": self.confirm_fails,
        }


@dataclass
class MacroTrigger:
    key: str
    mode: MacroMode = "hold"
    hold_press_seconds: Optional[float] = None

    def __post_init__(self):
        self.key = normalize_trigger_key(self.key)
        try:
            if self.hold_press_seconds in (None, "", False):
                self.hold_press_seconds = None
            else:
                self.hold_press_seconds = max(0.0, float(self.hold_press_seconds))
        except Exception:
            self.hold_press_seconds = None
        self.mode = self.mode if self.mode in ("hold", "toggle") else "hold"

    @classmethod
    def from_any(cls, raw: Any, *, default_mode: str = "hold", default_hold: Optional[float] = None) -> Optional["MacroTrigger"]:
        if raw is None:
            return None
        if isinstance(raw, cls):
            return cls(key=raw.key, mode=raw.mode, hold_press_seconds=raw.hold_press_seconds)
        if isinstance(raw, str):
            return cls(key=raw, mode=default_mode, hold_press_seconds=default_hold)
        if isinstance(raw, dict):
            key = raw.get("key") or raw.get("trigger_key") or ""
            mode = raw.get("mode", default_mode)
            hold = raw.get("hold_press_seconds", raw.get("hold_threshold", default_hold))
            return cls(key=key, mode=mode, hold_press_seconds=hold)
        return None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "key": self.key,
            "mode": self.mode,
            "hold_press_seconds": self.hold_press_seconds,
        }


@dataclass
class Macro:
    trigger_key: str
    mode: MacroMode = "hold"
    hold_press_seconds: Optional[float] = None
    triggers: List[MacroTrigger] = field(default_factory=list)
    actions: List[Action] = field(default_factory=list)
    stop_actions: List[Action] = field(default_factory=list)
    suppress_trigger: bool = False
    enabled: bool = True
    name: Optional[str] = None
    cycle_count: Optional[int] = None
    description: Optional[str] = None
    stop_others_on_trigger: bool = False
    suspend_others_while_running: bool = False
    interaction_outgoing_mode: Literal["none", "stop", "suspend"] = "none"
    interaction_targets: List[str] = field(default_factory=list)
    interaction_exclude_targets: List[str] = field(default_factory=list)
    interaction_incoming_allow: List[str] = field(default_factory=list)
    interaction_incoming_block: List[str] = field(default_factory=list)
    scope: Literal["global", "app"] = "global"
    app_targets: List[AppTarget] = field(default_factory=list)

    @classmethod
    def from_dict(cls, data: Dict[str, Any], resolver: Optional[VariableResolver] = None) -> "Macro":
        actions_data = data.get("actions")
        stop_actions_data = data.get("stop_actions")
        cycle_count_raw = data.get("cycle_count", None)
        if actions_data is None:
            actions = cls._from_legacy(data, resolver)
        else:
            actions = [Action.from_dict(a, resolver) for a in actions_data or []]
        stop_actions = [Action.from_dict(a, resolver) for a in stop_actions_data or []]
        cycle_count = None
        if cycle_count_raw not in (None, ""):
            try:
                cycle_count = int(cycle_count_raw)
                if cycle_count < 0:
                    cycle_count = None
            except Exception:
                cycle_count = None
        enabled_raw = data.get("enabled", True)
        enabled = enabled_raw if isinstance(enabled_raw, bool) else str(enabled_raw).strip().lower() not in ("false", "0", "no")
        scope_raw = str(data.get("scope", "global") or "global").lower()
        scope = scope_raw if scope_raw in ("global", "app") else "global"
        targets: List[AppTarget] = []
        targets_raw = data.get("app_targets", data.get("apps", []))
        for item in targets_raw or []:
            target = AppTarget.from_any(item)
            if target:
                targets.append(target)
        def _string_list(key: str) -> List[str]:
            raw = data.get(key, [])
            if not isinstance(raw, list):
                return []
            result: List[str] = []
            for item in raw:
                try:
                    text = str(item).strip()
                except Exception:
                    text = ""
                if text:
                    result.append(text)
            return result
        interaction_mode = str(data.get("interaction_outgoing_mode", "none") or "none").lower()
        if interaction_mode not in ("none", "stop", "suspend"):
            interaction_mode = "none"
        hold_press_seconds = data.get("hold_press_seconds", None)
        try:
            if hold_press_seconds in (None, "", False):
                hold_press_seconds = None
            else:
                hold_press_seconds = max(0.0, float(hold_press_seconds))
        except Exception:
            hold_press_seconds = None
        triggers_raw = data.get("triggers", [])
        triggers: List[MacroTrigger] = []
        if isinstance(triggers_raw, list):
            for item in triggers_raw:
                trig = MacroTrigger.from_any(item, default_mode=data.get("mode", "hold"), default_hold=hold_press_seconds)
                if trig and trig.key:
                    triggers.append(trig)
        primary_key = normalize_trigger_key(str(data.get("trigger_key") or data.get("key") or ""))
        primary_mode = data.get("mode", "hold")
        if not triggers:
            triggers.append(MacroTrigger(key=primary_key, mode=primary_mode, hold_press_seconds=hold_press_seconds))
        primary_trigger = triggers[0]
        return cls(
            trigger_key=primary_trigger.key,
            mode=primary_trigger.mode,
            hold_press_seconds=primary_trigger.hold_press_seconds,
            triggers=triggers,
            actions=actions,
            stop_actions=stop_actions,
            suppress_trigger=bool(data.get("suppress_trigger", False)),
            enabled=enabled,
            name=data.get("name"),
            cycle_count=cycle_count,
            description=data.get("description"),
            stop_others_on_trigger=bool(data.get("stop_others_on_trigger", False)),
            suspend_others_while_running=bool(data.get("suspend_others_while_running", False)),
            interaction_outgoing_mode=interaction_mode,
            interaction_targets=_string_list("interaction_targets"),
            interaction_exclude_targets=_string_list("interaction_exclude_targets"),
            interaction_incoming_allow=_string_list("interaction_incoming_allow"),
            interaction_incoming_block=_string_list("interaction_incoming_block"),
            scope=scope,
            app_targets=targets,
        )

    def __post_init__(self):
        # 정규화된 형태로 유지해 비교/차단 로직을 단순화한다.
        normalized: List[MacroTrigger] = []
        for trig in self.triggers or []:
            t = MacroTrigger.from_any(trig, default_mode=self.mode, default_hold=self.hold_press_seconds)
            if t and t.key:
                normalized.append(t)
        if not normalized:
            normalized.append(MacroTrigger(key=self.trigger_key, mode=self.mode, hold_press_seconds=self.hold_press_seconds))
        self.triggers = normalized
        primary = self.triggers[0]
        self.trigger_key = normalize_trigger_key(primary.key)
        self.mode = primary.mode if primary.mode in ("hold", "toggle") else "hold"
        try:
            if primary.hold_press_seconds in (None, "", False):
                self.hold_press_seconds = None
            else:
                self.hold_press_seconds = max(0.0, float(primary.hold_press_seconds))
        except Exception:
            self.hold_press_seconds = None

    @property
    def trigger_keys(self) -> List[str]:
        return parse_trigger_keys(self.trigger_key)

    def trigger_list(self) -> List[MacroTrigger]:
        return list(self.triggers or []) or [MacroTrigger(key=self.trigger_key, mode=self.mode, hold_press_seconds=self.hold_press_seconds)]

    def primary_trigger(self) -> MacroTrigger:
        lst = self.trigger_list()
        return lst[0] if lst else MacroTrigger(key=self.trigger_key, mode=self.mode, hold_press_seconds=self.hold_press_seconds)

    def trigger_label(self, *, include_mode: bool = False, max_items: int = 2) -> str:
        items: List[str] = []
        for trig in self.trigger_list()[: max(1, max_items)]:
            if not trig.key:
                continue
            label = trig.key
            if include_mode:
                label = f"{label} ({trig.mode})"
            items.append(label)
        if not items and self.trigger_key:
            items.append(self.trigger_key)
        if len(self.trigger_list()) > len(items):
            items.append("...")
        return ", ".join(items)

    def to_dict(self) -> Dict[str, Any]:
        targets: List[Dict[str, Any]] = []
        for t in getattr(self, "app_targets", []) or []:
            target = AppTarget.from_any(t)
            if target:
                targets.append(target.to_dict())
        primary = self.primary_trigger()
        return {
            "trigger_key": primary.key,
            "mode": primary.mode,
            "hold_press_seconds": getattr(primary, "hold_press_seconds", None),
            "triggers": [t.to_dict() for t in self.trigger_list()],
            "name": self.name,
            "description": self.description,
            "suppress_trigger": self.suppress_trigger,
            "enabled": self.enabled,
            "cycle_count": self.cycle_count,
            "actions": [a.to_dict() for a in self.actions],
            "stop_actions": [a.to_dict() for a in getattr(self, "stop_actions", [])],
            "stop_others_on_trigger": getattr(self, "stop_others_on_trigger", False),
            "suspend_others_while_running": getattr(self, "suspend_others_while_running", False),
            "interaction_outgoing_mode": getattr(self, "interaction_outgoing_mode", "none"),
            "interaction_targets": list(getattr(self, "interaction_targets", []) or []),
            "interaction_exclude_targets": list(getattr(self, "interaction_exclude_targets", []) or []),
            "interaction_incoming_allow": list(getattr(self, "interaction_incoming_allow", []) or []),
            "interaction_incoming_block": list(getattr(self, "interaction_incoming_block", []) or []),
            "scope": getattr(self, "scope", "global"),
            "app_targets": targets,
        }

    @staticmethod
    def _step_to_action(step: Step) -> Action:
        return Action.from_dict(step.to_dict())

    @classmethod
    def _conditions_to_actions(cls, conds: List[MacroCondition]) -> List[Action]:
        actions: List[Action] = []
        for cond in conds:
            actions.append(
                Action(
                    type="if",
                    condition=cond.condition,
                    actions=[cls._step_to_action(s) for s in cond.actions],
                    else_actions=[cls._step_to_action(s) for s in cond.else_actions],
                    name=cond.name,
                    enabled=getattr(cond, "enabled", True),
                    confirm_fails=getattr(cond, "confirm_fails", 1),
                )
            )
        return actions

    @classmethod
    def _from_legacy(cls, data: Dict[str, Any], resolver: Optional[VariableResolver]) -> List[Action]:
        base_actions_data = data.get("base_actions", data.get("steps", []))
        conditions_data = data.get("conditions", [])
        base_steps = [Step.from_dict(s, resolver) for s in base_actions_data or []]
        cond_blocks = [MacroCondition.from_dict(c, resolver) for c in conditions_data or []]
        actions = [cls._step_to_action(s) for s in base_steps if s.type in ("press", "down", "up", "sleep", "if")]
        actions.extend(cls._conditions_to_actions(cond_blocks))
        return actions


@dataclass
class MacroProfile:
    macros: List[Macro] = field(default_factory=list)
    pixel_region: Region = (0, 0, 100, 100)
    pixel_region_raw: Optional[str] = None
    pixel_color: RGB = (255, 0, 0)
    pixel_color_raw: Optional[str] = None
    pixel_tolerance: int = 10
    pixel_min_count: int = 1
    pixel_expect_exists: bool = True
    pixel_patterns: Dict[str, PixelPattern] = field(default_factory=dict)
    keyboard_device_id: Optional[int] = None
    keyboard_hardware_id: Optional[str] = None
    mouse_device_id: Optional[int] = None
    mouse_hardware_id: Optional[str] = None
    keyboard_test_key: str = "f24"
    input_mode: str = "hardware"
    key_delay: KeyDelayConfig = field(default_factory=KeyDelayConfig)
    mouse_delay: KeyDelayConfig = field(default_factory=KeyDelayConfig)
    variables: MacroVariables = field(default_factory=MacroVariables)
    base_resolution: tuple[int, int] = DEFAULT_BASE_RESOLUTION
    base_scale_percent: float = DEFAULT_BASE_SCALE
    transform_matrix: Optional[Dict[str, Any]] = None

    @staticmethod
    def _parse_resolution(raw: Any, default: tuple[int, int] = DEFAULT_BASE_RESOLUTION) -> tuple[int, int]:
        if isinstance(raw, (list, tuple)) and len(raw) >= 2:
            try:
                w, h = int(raw[0]), int(raw[1])
                if w > 0 and h > 0:
                    return (w, h)
            except Exception:
                pass
        if isinstance(raw, str):
            text = raw.strip().lower().replace("×", "x").replace(" ", "")
            for sep in ("x", ",", "*"):
                if sep in text:
                    parts = [p for p in text.split(sep) if p]
                    if len(parts) >= 2:
                        try:
                            w, h = int(parts[0]), int(parts[1])
                            if w > 0 and h > 0:
                                return (w, h)
                        except Exception:
                            pass
            try:
                nums = [int(n) for n in re.findall(r"\d+", text)]
                if len(nums) >= 2 and nums[0] > 0 and nums[1] > 0:
                    return (nums[0], nums[1])
            except Exception:
                pass
        return default

    @staticmethod
    def _parse_scale_percent(raw: Any, default: float = DEFAULT_BASE_SCALE) -> float:
        try:
            if isinstance(raw, str):
                text = raw.strip().lower().replace("%", "").replace("배", "").replace("x", "")
                if not text:
                    return default
                value = float(text)
            else:
                value = float(raw)
            if value <= 0:
                return default
            return float(value)
        except Exception:
            return default

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "MacroProfile":
        variables = MacroVariables.from_dict(data.get("variables", {}) or {})
        resolver = VariableResolver(variables)
        base_resolution = cls._parse_resolution(data.get("base_resolution"), DEFAULT_BASE_RESOLUTION)
        base_scale = cls._parse_scale_percent(data.get("base_scale_percent"), DEFAULT_BASE_SCALE)
        patterns_raw = data.get("pixel_patterns") or {}
        patterns: Dict[str, PixelPattern] = {}
        if isinstance(patterns_raw, list):
            for item in patterns_raw:
                if isinstance(item, dict):
                    pat = PixelPattern.from_dict(item)
                    patterns[pat.name] = pat
        elif isinstance(patterns_raw, dict):
            for name, item in patterns_raw.items():
                if not isinstance(item, dict):
                    continue
                merged = dict(item)
                merged.setdefault("name", name)
                pat = PixelPattern.from_dict(merged)
                patterns[pat.name] = pat
        for name, pat in list(patterns.items()):
            pat.tolerance = 0
            for pt in pat.points:
                pt.tolerance = None
            patterns[name] = pat

        region_raw = data.get("pixel_region")
        region_val = region_raw if region_raw is not None else (0, 0, 100, 100)
        if isinstance(region_val, str):
            resolved_region = resolver.resolve(region_val, "region")
            parts = [p.strip() for p in resolved_region.split(",") if p.strip()]
            if len(parts) != 4:
                raise ValueError("pixel_region은 x,y,w,h 네 개의 정수여야 합니다.")
            region = tuple(int(p) for p in parts)
        else:
            region = tuple(region_val)

        color_raw = data.get("pixel_color")
        color_val = color_raw if color_raw is not None else (255, 0, 0)
        if isinstance(color_val, str):
            resolved_color = resolver.resolve(color_val, "color")
            color_text = resolved_color.strip().lstrip("#")
            if len(color_text) != 6 or not all(c in "0123456789abcdefABCDEF" for c in color_text):
                raise ValueError("pixel_color는 16진수 6자리(RRGGBB)여야 합니다.")
            color = tuple(int(color_text[i : i + 2], 16) for i in (0, 2, 4))
        else:
            color = tuple(color_val)

        tol = int(data.get("pixel_tolerance", 0) or 0)
        min_count_raw = data.get("pixel_min_count", 1)
        try:
            min_count = max(1, int(min_count_raw))
        except Exception:
            min_count = 1
        expect_raw = data.get("pixel_expect_exists", True)
        if isinstance(expect_raw, str):
            expect_exists = expect_raw.strip().lower() not in ("false", "0", "no")
        else:
            expect_exists = bool(expect_raw)
        device_id_raw = data.get("keyboard_device_id")
        try:
            device_id = int(device_id_raw)
        except Exception:
            device_id = None
        hwid_raw = data.get("keyboard_hardware_id")
        hwid = str(hwid_raw) if hwid_raw else None
        mouse_device_raw = data.get("mouse_device_id")
        try:
            mouse_device_id = int(mouse_device_raw)
        except Exception:
            mouse_device_id = None
        mouse_hwid_raw = data.get("mouse_hardware_id")
        mouse_hwid = str(mouse_hwid_raw) if mouse_hwid_raw else None
        input_mode = str(data.get("input_mode", "hardware") or "hardware").lower()
        if input_mode not in ("hardware", "software"):
            input_mode = "hardware"
        test_key_raw = data.get("keyboard_test_key", "f24") or "f24"
        test_key = str(test_key_raw).lower()
        transform_meta = data.get("transform_matrix")
        if not isinstance(transform_meta, dict):
            transform_meta = None
        return cls(
            macros=[Macro.from_dict(m, resolver) for m in data.get("macros", [])],
            pixel_region=region,  # type: ignore[arg-type]
            pixel_region_raw=region_raw if isinstance(region_raw, str) else None,
            pixel_color=color,  # type: ignore[arg-type]
            pixel_color_raw=color_raw if isinstance(color_raw, str) else None,
            pixel_tolerance=tol,
            pixel_min_count=min_count,
            pixel_expect_exists=expect_exists,
            pixel_patterns=patterns,
            keyboard_device_id=device_id,
            keyboard_hardware_id=hwid,
            mouse_device_id=mouse_device_id,
            mouse_hardware_id=mouse_hwid,
            keyboard_test_key=test_key,
            input_mode=input_mode,
            key_delay=KeyDelayConfig.from_dict(data.get("key_delay", {}) if isinstance(data, dict) else {}),
            mouse_delay=KeyDelayConfig.from_dict(data.get("mouse_delay", {}) if isinstance(data, dict) else {}),
            variables=variables,
            base_resolution=base_resolution,
            base_scale_percent=base_scale,
            transform_matrix=transform_meta,
        )

    def to_dict(self) -> Dict[str, Any]:
        try:
            base_res = self._parse_resolution(self.base_resolution, DEFAULT_BASE_RESOLUTION)
        except Exception:
            base_res = DEFAULT_BASE_RESOLUTION
        try:
            base_scale = float(self._parse_scale_percent(self.base_scale_percent, DEFAULT_BASE_SCALE))
        except Exception:
            base_scale = DEFAULT_BASE_SCALE
        data: Dict[str, Any] = {
            "macros": [m.to_dict() for m in self.macros],
            "pixel_region": self.pixel_region_raw if self.pixel_region_raw is not None else list(self.pixel_region),
            "pixel_color": self.pixel_color_raw if self.pixel_color_raw is not None else list(self.pixel_color),
            "pixel_tolerance": self.pixel_tolerance,
            "pixel_min_count": self.pixel_min_count,
            "pixel_expect_exists": self.pixel_expect_exists,
            "pixel_patterns": {name: pat.to_dict() for name, pat in (getattr(self, "pixel_patterns", {}) or {}).items()},
            "keyboard_device_id": self.keyboard_device_id,
            "keyboard_hardware_id": self.keyboard_hardware_id,
            "mouse_device_id": self.mouse_device_id,
            "mouse_hardware_id": self.mouse_hardware_id,
            "keyboard_test_key": self.keyboard_test_key,
            "input_mode": self.input_mode,
            "key_delay": self.key_delay.to_dict(),
            "mouse_delay": self.mouse_delay.to_dict(),
            "variables": self.variables.to_dict(),
            "base_resolution": [int(v) for v in base_res],
            "base_scale_percent": float(base_scale),
        }
        if self.transform_matrix:
            try:
                data["transform_matrix"] = copy.deepcopy(self.transform_matrix)
            except Exception:
                data["transform_matrix"] = self.transform_matrix
        return data


class KeySwallower:
    """트리거 키를 OS에 전달하지 않도록 삼킴."""

    def __init__(self, inter: Optional[Interception] = None):
        self._stop = threading.Event()
        self._enabled = False
        self._keys: Set[int] = set()
        self._pressed: Set[int] = set()
        self._pressed_ts: Dict[int, float] = {}
        self._lock = threading.Lock()
        self._thread: Optional[threading.Thread] = None
        # 가능한 한 전역 Interception 인스턴스를 재사용해 필터 적용이 동일한 디바이스에
        # 걸리도록 한다.
        self._inter: Optional[Interception] = inter

    def set_keys(self, keys: List[str]):
        scs: Set[int] = set()
        for k in keys:
            try:
                sc = to_scan_code(k)
            except Exception:
                continue
            if sc > 0:
                scs.add(sc)
        with self._lock:
            if scs == self._keys:
                return
            self._keys = scs
            self._pressed.clear()
            self._pressed_ts.clear()

    def set_enabled(self, enabled: bool):
        with self._lock:
            self._enabled = enabled
            if not enabled:
                self._pressed.clear()
                self._pressed_ts.clear()

    def is_enabled(self) -> bool:
        with self._lock:
            return self._enabled

    def is_alive(self) -> bool:
        t = self._thread
        return bool(t and t.is_alive())

    def is_tracked(self, key: str) -> bool:
        try:
            sc = to_scan_code(key)
        except Exception:
            return False
        with self._lock:
            return sc > 0 and sc in self._keys

    def is_pressed(self, key: str, *, max_age: Optional[float] = None) -> bool:
        try:
            sc = to_scan_code(key)
        except Exception:
            return False
        with self._lock:
            if sc not in self._pressed:
                return False
            if max_age is not None:
                ts = self._pressed_ts.get(sc)
                if ts is None or (time.monotonic() - ts) > max_age:
                    # up 이벤트를 놓친 경우를 대비해 일정 시간 지나면 강제로 해제
                    self._pressed.discard(sc)
                    self._pressed_ts.pop(sc, None)
                    return False
            return True

    def last_pressed_at(self, key: str) -> Optional[float]:
        try:
            sc = to_scan_code(key)
        except Exception:
            return None
        with self._lock:
            return self._pressed_ts.get(sc)

    def start(self):
        if self._thread and self._thread.is_alive():
            return
        self._stop.clear()
        self._thread = threading.Thread(target=self._run, name="KeySwallower", daemon=True)
        self._thread.start()

    def stop(self):
        self._stop.set()
        if self._thread and threading.current_thread() is not self._thread:
            self._thread.join(timeout=1.0)
        with self._lock:
            self._pressed.clear()
            self._pressed_ts.clear()
        if self._inter:
            try:
                self._inter.set_keyboard_filter(KeyFilter(0))
            except Exception:
                pass
            self._inter = None

    def _run(self):
        try:
            inter = self._inter or Interception()
        except Exception:
            return
        self._inter = inter
        current_enabled = None
        while not self._stop.is_set():
            try:
                with self._lock:
                    enabled = self._enabled
                    codes = set(self._keys)

                if enabled != current_enabled:
                    try:
                        inter.set_keyboard_filter(KeyFilter.All if enabled else KeyFilter(0))
                    except Exception:
                        pass
                    current_enabled = enabled

                if not enabled:
                    time.sleep(0.05)
                    continue

                device = inter.wait_receive(50)
                if not device:
                    continue
                stroke = device.stroke
                tracked_key = device.is_keyboard and stroke.code in codes
                if tracked_key:
                    is_down = stroke.state in (KeyState.Down, KeyState.E0Down, KeyState.E1Down)
                    is_up = stroke.state in (KeyState.Up, KeyState.E0Up, KeyState.E1Up)
                    now = time.monotonic()
                    with self._lock:
                        if is_down:
                            self._pressed.add(stroke.code)
                            self._pressed_ts[stroke.code] = now
                        elif is_up:
                            self._pressed.discard(stroke.code)
                            self._pressed_ts.pop(stroke.code, None)

                swallow = tracked_key
                if not swallow:
                    device.send()
            except Exception:
                # 예외 발생 시 필터를 해제하고 종료
                with self._lock:
                    self._enabled = False
                    self._pressed.clear()
                    self._pressed_ts.clear()
                try:
                    inter.set_keyboard_filter(KeyFilter(0))
                except Exception:
                    pass
                break


class MacroRunner:
    def __init__(
        self,
        macro: Macro,
        engine: "MacroEngine",
        index: Optional[int] = None,
        *,
        inherit_held_keys: Optional[Iterable[str]] = None,
        inherit_held_mouse: Optional[Iterable[str]] = None,
    ):
        self.macro = macro
        self.engine = engine
        self.index = index
        self._stop_event = threading.Event()
        self._thread: Optional[threading.Thread] = None
        self._cond_key_states: Dict[str, bool] = {}
        self._vars = copy.deepcopy(getattr(engine._profile, "variables", MacroVariables()))
        self._resolver = VariableResolver(self._vars)
        self._sent_stop_event = False
        self._seq_map: Dict[tuple[int, ...], int] = {}
        self._seq_counter = 1
        self._build_seq_map(self.macro.actions, [])
        self._held_keys: Set[str] = set(inherit_held_keys or [])
        self._held_mouse: Set[str] = set(inherit_held_mouse or [])
        # inherited holds는 일시정지 시 다시 풀고 재적용해야 하므로 기본 False
        self._held_key_policy: Dict[str, bool] = {k: False for k in self._held_keys}
        self._held_mouse_policy: Dict[str, bool] = {m: False for m in self._held_mouse}
        self._held_lock = threading.Lock()
        self._if_false_streaks: Dict[tuple[int, ...], int] = {}
        self._running_stop_actions = False
        self._stop_request_after_cycle = False
        self._stop_actions_run = False
        self._stop_logged = False
        self._first_cycle_done = False
        self._force_first_cycle = self._has_force_first_action(self.macro.actions)
        self._start_cycle = 0
        self._release_inputs_on_stop = True

    def _has_force_first_action(self, actions: List[Action]) -> bool:
        for act in actions:
            if getattr(act, "force_first_run", False):
                return True
            children: List[Action] = []
            if act.type == "if":
                children.extend(act.actions)
                for _, eacts, _ in _iter_elif_blocks(getattr(act, "elif_blocks", [])):
                    children.extend(eacts)
                children.extend(getattr(act, "else_actions", []))
            elif act.type == "group":
                children.extend(act.actions)
            if children and self._has_force_first_action(children):
                return True
        return False

    def is_alive(self) -> bool:
        return bool(self._thread and self._thread.is_alive())

    class _Result:
        def __init__(self, signal: str = "none", goto_label: Optional[str] = None, condition_hit: bool = False, repeat: bool = False):
            self.signal = signal
            self.goto_label = goto_label
            self.condition_hit = condition_hit
            self.repeat = repeat

    def _macro_label(self) -> str:
        if self.macro.name:
            return self.macro.name
        base = f"{self.macro.trigger_label(include_mode=False) or self.macro.trigger_key}"
        return base if self.index is None else f"{base}#{self.index}"

    def _macro_context(self) -> Dict[str, Any]:
        primary = self.macro.primary_trigger()
        return {
            "index": self.index,
            "name": self.macro.name,
            "trigger_key": primary.key,
            "mode": primary.mode,
            "triggers": [t.to_dict() for t in self.macro.trigger_list()],
        }

    def _macro_identifier(self) -> str:
        base = (self.macro.name or "").strip().lower()
        if not base:
            base = (self.macro.primary_trigger().key or self.macro.trigger_key or "").strip().lower()
        return base or f"macro-{self.index if self.index is not None else 'unknown'}"

    def _build_seq_map(self, actions: List[Action], prefix: List[int]):
        for idx, act in enumerate(actions):
            path_key = tuple(prefix + [idx])
            self._seq_map[path_key] = self._seq_counter
            self._seq_counter += 1
            children: List[Action] = []
            if act.type == "if":
                children.extend(act.actions)
                for _, eacts, _ in _iter_elif_blocks(getattr(act, "elif_blocks", [])):
                    children.extend(eacts)
                children.extend(getattr(act, "else_actions", []))
            elif act.type == "group":
                children.extend(act.actions)
            if children:
                child_prefix = prefix + [idx]
                self._build_seq_map(children, child_prefix)

    def _seq_chain(self, idx_path: List[int]) -> List[int]:
        chain: List[int] = []
        for i in range(1, len(idx_path) + 1):
            key = tuple(idx_path[:i])
            num = self._seq_map.get(key)
            if num is not None:
                chain.append(num)
        return chain

    def _emit_macro_event(self, etype: str, **extra):
        payload = {"type": etype, "macro": self._macro_context()}
        payload.update(extra)
        self.engine._emit_event(payload)

    def _action_label(self, action: Action, idx: int) -> str:
        label = action.name or action.description or action.type
        return f"{idx}:{label}"

    def _emit_action_event(self, stage: str, action: Action, path: List[str], idx_path: List[int], **extra):
        detail: Dict[str, Any] = {}
        if action.type == "pixel_get":
            region = action.pixel_region
            if region is None and action.pixel_region_raw is not None:
                try:
                    region = Condition._parse_region(action.pixel_region_raw, self._resolver)[0]
                except Exception:
                    region = None
            if region is not None:
                try:
                    region = _normalize_region_tuple(region)
                except Exception:
                    region = None
            detail["pixel_get"] = {
                "region": tuple(region) if region else None,
                "target": action.pixel_target,
            }
        if action.type == "timer":
            detail["timer"] = {"slot": action.timer_index, "value": action.timer_value}
        payload = {
            "type": stage,
            "macro": self._macro_context(),
            "action_type": action.type,
            "action_name": action.name,
            "description": action.description,
            "path": path,
            "path_text": " > ".join(path),
            "cycle": getattr(self, "_current_cycle", 0),
            "detail": detail,
            "seq_chain": self._seq_chain(idx_path),
        }
        payload.update(extra)
        self.engine._emit_event(payload)

    def _notify_macro_stop(self, reason: str):
        if getattr(self, "_sent_stop_event", False):
            return
        self._sent_stop_event = True
        self._emit_macro_event("macro_stop", reason=reason, cycle=getattr(self, "_current_cycle", 0))

    def _release_held_keys(self, *, force: bool = False):
        if not force and not getattr(self, "_release_inputs_on_stop", True):
            return
        with self._held_lock:
            keys = list(self._held_keys)
            mouse_buttons = list(self._held_mouse)
            self._held_keys.clear()
            self._held_mouse.clear()
            self._held_key_policy.clear()
            self._held_mouse_policy.clear()
        for key in keys:
            try:
                self.engine._send_key("up", key, hold_ms=0)
            except Exception:
                pass
        for btn in mouse_buttons:
            try:
                self.engine._send_mouse("mouse_up", btn, hold_ms=0)
            except Exception:
                pass

    def snapshot_held_inputs(self) -> tuple[Set[str], Set[str]]:
        with self._held_lock:
            return set(self._held_keys), set(self._held_mouse)

    def snapshot_held_inputs_with_policy(self) -> tuple[Dict[str, bool], Dict[str, bool]]:
        with self._held_lock:
            return dict(self._held_key_policy), dict(self._held_mouse_policy)

    def start(self, *, start_cycle: int = 0):
        if self._thread and self._thread.is_alive():
            return
        try:
            self._start_cycle = max(0, int(start_cycle))
        except Exception:
            self._start_cycle = 0
        self._stop_event.clear()
        self._release_inputs_on_stop = True
        self._sent_stop_event = False
        self._stop_request_after_cycle = False
        self._stop_actions_run = False
        self._stop_logged = False
        self._first_cycle_done = bool(self._start_cycle > 0)
        self._force_first_cycle = self._has_force_first_action(self.macro.actions)
        self._current_cycle = self._start_cycle
        name = f"Macro-{self.macro.primary_trigger().key or self.macro.trigger_key}"
        self._thread = threading.Thread(target=self._run, name=name, daemon=True)
        self._thread.start()
        limit = self.macro.cycle_count
        if limit == 0:
            limit = None
        limit_text = "inf" if limit is None else str(limit)
        label = self.macro.trigger_label(include_mode=False) or self.macro.trigger_key
        self.engine._emit_log(f"매크로 시작: {label} (cycle_limit={limit_text})")
        self._emit_macro_event("macro_start", cycle=self._start_cycle)

    def stop(self, *, release_inputs: bool = True, run_stop_actions: bool = True):
        label = self.macro.trigger_label(include_mode=False) or self.macro.trigger_key
        self._stop_request_after_cycle = False
        self._stop_event.set()
        self._release_inputs_on_stop = bool(release_inputs)
        if not run_stop_actions:
            self._stop_actions_run = True
        else:
            # on_stop 액션이 있으면 먼저 실행한다.
            self._run_stop_actions()
        # 중단 요청이 들어오면 바로 입력을 풀어준다.
        if release_inputs:
            self._release_held_keys()
        if self._thread and threading.current_thread() is not self._thread:
            self._thread.join(timeout=1.0)
            if self._thread.is_alive():
                self.engine._emit_log(f"매크로 정지 대기 초과: {label}")
        # 스레드가 끝난 뒤에도 혹시 남아 있을 입력을 한 번 더 해제한다.
        if release_inputs:
            self._release_held_keys()
        self.engine._emit_log(f"매크로 정지: {label}")
        self._stop_logged = True
        self._notify_macro_stop("stopped")

    def request_stop_after_cycle(self):
        self._stop_request_after_cycle = True

    def should_finish_first_cycle(self) -> bool:
        return bool(self._force_first_cycle)

    def first_cycle_done(self) -> bool:
        return bool(self._first_cycle_done)

    def is_stop_after_cycle_requested(self) -> bool:
        return bool(self._stop_request_after_cycle)

    def current_cycle(self) -> int:
        return getattr(self, "_current_cycle", 0)

    def _run_stop_actions(self):
        if self._stop_actions_run:
            return
        actions = getattr(self.macro, "stop_actions", []) or []
        if not actions:
            self._stop_actions_run = True
            return
        labels = self._label_index(actions)
        self._running_stop_actions = True
        try:
            self._run_actions(copy.deepcopy(actions), labels, root=True, path=[f"{self._macro_label()}-on_stop"])
        finally:
            self._running_stop_actions = False
            self._stop_actions_run = True

    def _run(self):
        labels = self._label_index(self.macro.actions)
        cycle = max(0, getattr(self, "_start_cycle", 0))
        self._current_cycle = cycle
        try:
            # cycle_count가 0이면 무한 반복, None이면 제한 없음.
            max_cycles = self.macro.cycle_count
            if max_cycles == 0:
                max_cycles = None

            while not self._stop_event.is_set():
                if max_cycles is not None and cycle >= max_cycles:
                    break
                self._current_cycle = cycle
                result = self._run_actions(self.macro.actions, labels, root=True, path=[self._macro_label()])
                if self._stop_event.is_set():
                    break
                cycle += 1
                if cycle >= 1:
                    self._first_cycle_done = True
                if self._stop_request_after_cycle and self._first_cycle_done:
                    break
                if result.signal == "return":
                    break
                self._stop_event.wait(self.engine.tick)
            stopped = self._stop_event.is_set() or self._stop_request_after_cycle
            if stopped and not self._stop_actions_run:
                self._run_stop_actions()
            if stopped:
                if not self._stop_logged:
                    self.engine._emit_log(f"매크로 정지: {self.macro.trigger_label(include_mode=False) or self.macro.trigger_key}")
                    self._stop_logged = True
                self._notify_macro_stop("stopped")
            else:
                self._notify_macro_stop("finished")
        finally:
            self._release_held_keys()

    def _label_index(self, actions: List[Action]) -> Dict[str, int]:
        labels: Dict[str, int] = {}
        for idx, act in enumerate(actions):
            if act.type == "label" and act.label:
                labels[act.label] = idx
        return labels

    def _run_actions(
        self,
        actions: List[Action],
        labels: Dict[str, int],
        *,
        root: bool = False,
        path: Optional[List[str]] = None,
        idx_path: Optional[List[int]] = None,
        base_offset: int = 0,
    ) -> "MacroRunner._Result":
        idx = 0
        base_path = list(path or [])
        base_idx_path = list(idx_path or [])
        while idx < len(actions) and (self._running_stop_actions or not self._stop_event.is_set()):
            act = actions[idx]
            act_path = base_path + [self._action_label(act, idx)]
            act_idx_path = base_idx_path + [base_offset + idx]
            if not getattr(act, "enabled", True):
                self._emit_action_event("action_end", act, act_path, act_idx_path, status="disabled")
                idx += 1
                continue
            res = self._exec_action(act, labels, act_path, act_idx_path)
            if self._stop_event.is_set() and not self._running_stop_actions:
                return self._Result(signal="break")
            if getattr(res, "repeat", False):
                # 대기 없이 너무 빠르게 반복되지 않도록 tick만큼 대기
                self._stop_event.wait(self.engine.tick)
                continue
            if res.signal == "goto":
                if root and res.goto_label and res.goto_label in labels:
                    idx = labels[res.goto_label]
                    continue
                if root:
                    self.engine._emit_log(f"라벨을 찾을 수 없습니다: {res.goto_label}")
                return res
            if res.signal in ("return", "continue", "break"):
                return res
            idx += 1
        return self._Result()

    def _sleep_with_condition_poll(self, sleep_ms: int, *, allow_condition: bool):
        """sleep 동안에도 조건 평가가 돌도록 짧게 쪼개 대기."""
        if sleep_ms <= 0:
            return
        deadline = time.perf_counter() + (sleep_ms / 1000.0)
        while self._running_stop_actions or not self._stop_event.is_set():
            now = time.perf_counter()
            remaining = deadline - now
            if remaining <= 0:
                break
            slice_len = min(self.engine.tick, remaining)
            self._stop_event.wait(slice_len)
            if allow_condition and not self._stop_event.is_set():
                # allow nested condition polls if needed later
                pass

    def _exec_action(self, action: Action, labels: Dict[str, int], path: List[str], idx_path: List[int]) -> "MacroRunner._Result":
        def end_result(
            signal: str = "none",
            status: str = "ok",
            goto_label: Optional[str] = None,
            condition_hit: bool = False,
            repeat: bool = False,
            **extra,
        ):
            self._emit_action_event(
                "action_end",
                action,
                path,
                idx_path,
                status=status,
                goto_label=goto_label,
                condition_hit=condition_hit,
                **extra,
            )
            return self._Result(signal=signal, goto_label=goto_label, condition_hit=condition_hit, repeat=repeat)

        if self._stop_event.is_set() and not self._running_stop_actions:
            return self._Result(signal="break")

        # once_per_macro 액션은 첫 사이클 이후에는 바로 스킵 처리하고 로그를 남기지 않는다.
        if getattr(action, "once_per_macro", False) and getattr(self, "_current_cycle", 0) > 0:
            return end_result(status="skip_once")

        self._emit_action_event("action_start", action, path, idx_path)

        if action.type == "noop":
            return end_result(status="noop")

        if action.type == "sleep":
            sleep_ms = action.resolve_sleep_ms()
            if sleep_ms > 0:
                self._sleep_with_condition_poll(sleep_ms, allow_condition=False)
            return end_result(status="sleep", duration=sleep_ms)

        def _resolve_repeat_val(act: Action) -> int:
            if getattr(act, "repeat_range", None):
                try:
                    low, high = act.repeat_range
                    return max(1, random.randint(int(low), int(high)))
                except Exception:
                    pass
            try:
                return max(1, int(getattr(act, "repeat", 1) or 1))
            except Exception:
                return 1

        if action.type in ("press", "down", "up"):
            if not action.key:
                self.engine._emit_log(f"키 없음: {action.type} 스킵")
                return end_result(status="error", error="missing_key")
            press_delay, gap_delay = self.engine._resolve_key_delays(action)
            repeat = _resolve_repeat_val(action)
            for i in range(repeat):
                if self._stop_event.is_set() and not self._running_stop_actions:
                    return end_result(status="stopped", signal="break")
                ok = self.engine._send_key(action.type, action.key, hold_ms=press_delay if action.type == "press" else 0)
                if not ok:
                    return end_result(status="error", error="send_failed")
                if action.type == "down":
                    policy = bool(getattr(action, "hold_keep_on_pause", False))
                    with self._held_lock:
                        self._held_keys.add(action.key)
                        self._held_key_policy[action.key] = policy
                elif action.type == "up":
                    with self._held_lock:
                        self._held_keys.discard(action.key)
                        self._held_key_policy.pop(action.key, None)
                self.engine._emit_event({"type": "action", "action": action.type, "key": action.key})
                if gap_delay > 0 and i < repeat - 1:
                    self._sleep_with_condition_poll(gap_delay, allow_condition=False)
            if gap_delay > 0:
                self._sleep_with_condition_poll(gap_delay, allow_condition=False)
            return end_result()

        if action.type in ("mouse_click", "mouse_down", "mouse_up", "mouse_move"):
            button = (action.mouse_button or action.key or "mouse1").strip() if (action.mouse_button or action.key) else "mouse1"
            pos = action.mouse_pos
            if pos is None and getattr(action, "mouse_pos_raw", None):
                try:
                    pos, _ = _parse_mouse_pos(action.mouse_pos_raw, self._resolver)
                except Exception:
                    pos = None
            if action.type == "mouse_move" and pos is None:
                self.engine._emit_log("마우스 이동 좌표가 비어 있습니다.")
                return end_result(status="error", error="missing_mouse_pos")
            press_delay, gap_delay = self.engine._resolve_mouse_delays(action)
            repeat = _resolve_repeat_val(action)
            event_target = "move" if action.type == "mouse_move" else button
            for i in range(repeat):
                if self._stop_event.is_set() and not self._running_stop_actions:
                    return end_result(status="stopped", signal="break")
                ok = self.engine._send_mouse(
                    action.type,
                    button,
                    hold_ms=press_delay if action.type == "mouse_click" else 0,
                    pos=pos,
                )
                if not ok:
                    return end_result(status="error", error="send_failed")
                if action.type == "mouse_down":
                    policy = bool(getattr(action, "hold_keep_on_pause", False))
                    with self._held_lock:
                        self._held_mouse.add(button)
                        self._held_mouse_policy[button] = policy
                elif action.type in ("mouse_up",):
                    with self._held_lock:
                        self._held_mouse.discard(button)
                        self._held_mouse_policy.pop(button, None)
                self.engine._emit_event({"type": "action", "action": action.type, "button": event_target, "pos": pos})
                if gap_delay > 0 and i < repeat - 1:
                    self._sleep_with_condition_poll(gap_delay, allow_condition=False)
            if gap_delay > 0:
                self._sleep_with_condition_poll(gap_delay, allow_condition=False)
            return end_result()

        if action.type == "label":
            return end_result(status="label")

        if action.type == "goto":
            return end_result(signal="goto", status="goto", goto_label=action.goto_label or action.label)

        if action.type == "return":
            return end_result(signal="return", status="return")

        if action.type == "continue":
            return end_result(signal="continue", status="continue")

        if action.type == "break":
            return end_result(signal="break", status="break")

        if action.type == "macro_stop":
            # 현재 매크로를 즉시 중단한다.
            self.stop()
            return end_result(signal="break", status="macro_stop")

        if action.type == "pixel_get":
            region = action.pixel_region
            if action.pixel_region_raw:
                region = Condition._parse_region(action.pixel_region_raw, self._resolver)[0]
            if not region:
                self.engine._emit_log("픽셀겟 영역이 비어 있습니다.")
                return end_result(status="error", error="empty_region")
            try:
                region = _normalize_region_tuple(region)
            except Exception as exc:
                self.engine._emit_log(f"픽셀겟 영역 파싱 실패: {exc}")
                return end_result(status="error", error=str(exc))
            x, y, w, h = region
            if w <= 0 or h <= 0:
                self.engine._emit_log("픽셀겟 영역 크기가 0 이하입니다.")
                return end_result(status="error", error="invalid_region_size")
            try:
                img = capture_region(region)
                color = img.convert("RGB").getpixel((0, 0))
                var_name = (action.pixel_target or "pixel").strip() or "pixel"
                self._vars.color[var_name] = f"{color[0]:02x}{color[1]:02x}{color[2]:02x}"
                ts = time.time()
                self.engine._emit_event(
                    {
                        "type": "variable_update",
                        "category": "color",
                        "name": var_name,
                        "value": self._vars.color[var_name],
                        "macro": self._macro_context(),
                        "source": "pixel_get",
                        "timestamp": ts,
                    }
                )
                self.engine._emit_log(f"픽셀겟 ({x},{y},{w},{h}) -> {var_name}={self._vars.color[var_name]}")
            except Exception as exc:
                self.engine._emit_log(f"픽셀겟 실패: {exc}")
                return end_result(status="error", error=str(exc))
            return end_result(status="ok", updated_var=var_name)

        if action.type == "set_var":
            name = (action.var_name or "").strip()
            if not name:
                self.engine._emit_log("변수 설정 실패: 이름이 없습니다.")
                return end_result(status="error", error="missing_var_name")
            raw_val = action.var_value_raw if action.var_value_raw is not None else action.var_value
            value = "" if raw_val is None else str(raw_val)
            if self._resolver and raw_val is not None:
                try:
                    value = self._resolver.resolve(str(raw_val), "var")
                except Exception as exc:
                    self.engine._emit_log(f"변수 설정 실패: {exc}")
                    return end_result(status="error", error=str(exc))
            self._vars.var[name] = str(value)
            ts = time.time()
            self.engine._emit_event(
                {
                    "type": "variable_update",
                    "category": "var",
                    "name": name,
                    "value": self._vars.var[name],
                    "macro": self._macro_context(),
                    "source": "set_var",
                    "timestamp": ts,
                }
            )
            self.engine._emit_log(f"변수 설정: {name}={self._vars.var[name]}")
            return end_result(status="ok", updated_var=name, value=self._vars.var[name])

        if action.type == "timer":
            slot = int(action.timer_index or 0)
            value = float(action.timer_value) if action.timer_value is not None else 0.0
            if slot < 1 or slot > 20:
                self.engine._emit_log("타이머 설정 실패: 1~20 슬롯만 가능합니다.")
                return end_result(status="error", error="invalid_timer_slot")
            if value < 0:
                value = 0.0
            self.engine._set_timer(slot, value)
            self.engine._emit_log(f"타이머{slot} = {value:.3f}초로 설정")
            self.engine._emit_event(
                {"type": "timer_update", "slot": slot, "value": value, "macro": self._macro_context(), "timestamp": time.time()}
            )
            return end_result(status="timer", timer_slot=slot, timer_value=value)

        if action.type == "if":
            cond = action.condition
            if not cond:
                self.engine._emit_log("if 조건이 없습니다.")
                return end_result(status="error", error="missing_condition")
            path_key = tuple(idx_path)
            confirm_fails = max(1, getattr(action, "confirm_fails", 1))
            pixel_cache: Dict[Tuple[int, int, int, int], Any] = {}
            cond_true = self.engine._evaluate_condition(
                cond,
                key_states=self._cond_key_states,
                resolver=self._resolver,
                macro_ctx=self._macro_context(),
                path=path + ["if"],
                vars_ctx=self._vars,
                pixel_cache=pixel_cache,
            )
            if cond_true:
                self._if_false_streaks[path_key] = 0
                res = self._run_actions(action.actions, labels, path=path + ["if_true"], idx_path=idx_path)
                res.condition_hit = True
                self._emit_action_event("action_end", action, path, idx_path, status="branch_true", condition_hit=True, branch="if_true")
                return res
            offset = len(action.actions or [])
            elif_offset = offset
            elif_blocks = list(_iter_elif_blocks(getattr(action, "elif_blocks", [])))
            for idx, (elif_cond, elif_actions, _) in enumerate(elif_blocks):
                if getattr(elif_cond, "enabled", True) is False:
                    elif_offset += len(elif_actions or [])
                    continue
                if self.engine._evaluate_condition(
                    elif_cond,
                    key_states=self._cond_key_states,
                    resolver=self._resolver,
                    macro_ctx=self._macro_context(),
                    path=path + [f"elif[{idx}]"],
                    vars_ctx=self._vars,
                    pixel_cache=pixel_cache,
                ):
                    self._if_false_streaks[path_key] = 0
                    res = self._run_actions(elif_actions, labels, path=path + [f"elif[{idx}]"], idx_path=idx_path, base_offset=elif_offset)
                    res.condition_hit = True
                    self._emit_action_event(
                        "action_end", action, path, idx_path, status="branch_elif", condition_hit=True, branch=f"elif[{idx}]"
                    )
                    return res
                elif_offset += len(elif_actions or [])
            streak = self._if_false_streaks.get(path_key, 0) + 1
            self._if_false_streaks[path_key] = streak
            if streak < confirm_fails:
                # 연속 실패 횟수 도달 전에는 기다렸다가 다시 평가
                return self._Result(repeat=True)
            self._if_false_streaks[path_key] = 0
            res = self._run_actions(
                action.else_actions,
                labels,
                path=path + ["else"],
                idx_path=idx_path,
                base_offset=offset + sum(len(ea or []) for _, ea, _ in elif_blocks),
            )
            self._emit_action_event(
                "action_end", action, path, idx_path, status="branch_else", condition_hit=getattr(res, "condition_hit", False), branch="else"
            )
            return res

        if action.type == "group":
            mode = action.group_mode or "all"
            if mode == "while":
                iteration = 0
                while self._running_stop_actions or not self._stop_event.is_set():
                    res = self._run_actions(action.actions, labels, path=path + ["while"], idx_path=idx_path)
                    if res.signal == "continue":
                        iteration += 1
                        self._stop_event.wait(self.engine.tick)
                        continue
                    if res.signal == "break":
                        self._emit_action_event(
                            "action_end", action, path, idx_path, status="break", branch="while", condition_hit=res.condition_hit
                        )
                        return self._Result()
                    if res.signal in ("return", "goto"):
                        self._emit_action_event(
                            "action_end", action, path, idx_path, status=res.signal, branch="while", condition_hit=res.condition_hit
                        )
                        return res
                    iteration += 1
                    self._stop_event.wait(self.engine.tick)
                return end_result(status="stopped" if self._stop_event.is_set() else "while_done", branch="while")
            if mode == "repeat_n":
                repeat_limit_raw = getattr(action, "group_repeat", None)
                try:
                    repeat_limit = max(1, int(repeat_limit_raw)) if repeat_limit_raw not in (None, "") else 1
                except Exception:
                    repeat_limit = 1
                iteration = 0
                while iteration < repeat_limit and (self._running_stop_actions or not self._stop_event.is_set()):
                    res = self._run_actions(
                        action.actions,
                        labels,
                        path=path + [f"repeat[{iteration}]"],
                        idx_path=idx_path,
                    )
                    if res.signal == "continue":
                        iteration += 1
                        self._stop_event.wait(self.engine.tick)
                        continue
                    if res.signal == "break":
                        self._emit_action_event(
                            "action_end", action, path, idx_path, status="break", branch="repeat_n", condition_hit=res.condition_hit
                        )
                        return self._Result()
                    if res.signal in ("return", "goto"):
                        self._emit_action_event(
                            "action_end", action, path, idx_path, status=res.signal, branch="repeat_n", condition_hit=res.condition_hit
                        )
                        return res
                    iteration += 1
                    self._stop_event.wait(self.engine.tick)
                return end_result(status="stopped" if self._stop_event.is_set() else "repeat_n_done", branch="repeat_n")
            for child_idx, child in enumerate(action.actions):
                res = self._exec_action(
                    child,
                    labels,
                    path=path + [f"group[{child_idx}]", self._action_label(child, child_idx)],
                    idx_path=idx_path + [child_idx],
                )
                if res.signal in ("return", "continue", "break", "goto"):
                    self._emit_action_event(
                        "action_end", action, path, idx_path, status=res.signal, branch="group", condition_hit=res.condition_hit
                    )
                    return res
                if res.condition_hit and mode in ("first_true", "first_true_continue", "first_true_return"):
                    branch_status = "first_true"
                    if mode == "first_true_continue":
                        self._emit_action_event(
                            "action_end", action, path, idx_path, status="continue", branch=branch_status, condition_hit=True
                        )
                        return self._Result(signal="continue", condition_hit=True)
                    if mode == "first_true_return":
                        self._emit_action_event(
                            "action_end", action, path, idx_path, status="return", branch=branch_status, condition_hit=True
                        )
                        return self._Result(signal="return", condition_hit=True)
                    self._emit_action_event(
                        "action_end", action, path, idx_path, status="ok", branch=branch_status, condition_hit=True
                    )
                    return self._Result(condition_hit=True)
            return end_result(status="ok", branch="group")

        self.engine._emit_log(f"알 수 없는 액션 타입: {action.type}")
        return end_result(status="error", error="unknown_action")


class MacroEngine:
    """
    트리거 키를 누르는 동안 기본 액션을 반복 실행하고 조건별로 참/거짓 액션을 추가로 실행하는 엔진.
    글로벌 키: Home(활성), Insert(일시정지 토글), End(종료), PageUp(픽셀 테스트)
    """

    def __init__(self, profile: Optional[MacroProfile] = None, *, tick: float = 0.02):
        self.tick = tick
        self.running = False
        self.active = False
        self.paused = False

        self._profile = profile or MacroProfile()
        self._lock = threading.Lock()
        self._stop_event = threading.Event()
        self._thread: Optional[threading.Thread] = None
        self._events: "queue.Queue[Dict[str, Any]]" = queue.Queue()
        self._hotkey_states: Dict[str, bool] = {}
        self._hotkey_pressed_at: Dict[str, float] = {}
        self._cond_key_states: Dict[str, bool] = {}
        self._cond_lock = threading.Lock()
        self._macro_runners: Dict[int, MacroRunner] = {}
        self._hold_release_since: Dict[tuple[int, int], float] = {}
        self._hold_press_since: Dict[tuple[int, int], float] = {}
        self._hold_raw_state: Dict[tuple[int, int], bool] = {}
        self._active_hold_triggers: Set[tuple[int, int]] = set()
        self._toggle_states: Dict[int, bool] = {}
        self._recent_sends: Dict[str, float] = {}
        self._guard_macro_idx: Optional[int] = None
        self._suspended_toggle_indices: Set[int] = set()
        self._suspended_toggle_states: Dict[int, bool] = {}
        self._suspended_toggle_cycles: Dict[int, int] = {}
        self._suspended_hold_inputs: Dict[int, Dict[str, Set[str]]] = {}
        self._paused_hold_inputs: Dict[str, Set[str]] = {
            "release_keys": set(),
            "release_mouse": set(),
            "keep_keys": set(),
            "keep_mouse": set(),
        }
        # cycle_count가 있는 홀드 매크로는 트리거를 뗄 때까지 재시작을 막는다.
        self._hold_exhausted_indices: Set[int] = set()
        self._hold_blocked_by_extra_mods: Dict[tuple[int, int], bool] = {}
        self._app_ctx: Optional[Dict[str, Any]] = None
        self._app_ctx_ts: float = 0.0
        # 홀드 상태가 일시적으로 끊겼을 때 재시작을 막기 위해 약간 여유를 둔다.
        self._hold_release_debounce = max(self.tick * 2, 0.05)
        # 매크로가 스스로 트리거 키를 입력했을 때 토글이 바로 꺼지는 것을 막기 위한 완충 시간.
        self._edge_block_window = max(self.tick * 5, 0.1)
        # 키 눌림을 삼키는 동안 오래된 상태를 무시하기 위한 완충 시간.
        self._swallow_stale_sec = max(self.tick * 25, 1.0)
        self._swallower = KeySwallower(get_interception())
        self._swallower.set_keys(self._swallow_keys())
        self._timer_lock = threading.Lock()
        self._timers: List[Dict[str, Any]] = []
        self._reset_timers()
        self._app_ctx: Optional[Dict[str, Any]] = None
        self._app_ctx_ts: float = 0.0

        self._pixel_test_region: Region = (0, 0, 1, 1)
        self._pixel_test_color: RGB = (0, 0, 0)
        self._pixel_test_tolerance: int = 0
        self._pixel_test_expect_exists: bool = True
        self._pixel_test_min_count: int = 1
        self._pixel_test_pattern: Optional[str] = None
        base_patterns = _load_shared_patterns()
        profile_patterns = getattr(self._profile, "pixel_patterns", {}) or {}
        for name, pat in profile_patterns.items():
            if name not in base_patterns:
                base_patterns[name] = copy.deepcopy(pat)
        self._pixel_patterns: Dict[str, PixelPattern] = base_patterns
        self._debug_image_override: Optional[np.ndarray] = None
        self._debug_image_label: Optional[str] = None
        self._keyboard_device_id: Optional[int] = self._profile.keyboard_device_id
        self._keyboard_hardware_id: Optional[str] = self._profile.keyboard_hardware_id
        self._mouse_device_id: Optional[int] = getattr(self._profile, "mouse_device_id", None)
        self._mouse_hardware_id: Optional[str] = getattr(self._profile, "mouse_hardware_id", None)
        self._keyboard_test_key: str = getattr(self._profile, "keyboard_test_key", "f24") or "f24"
        self._input_mode: str = getattr(self._profile, "input_mode", "hardware") or "hardware"
        self._key_delay: KeyDelayConfig = copy.deepcopy(getattr(self._profile, "key_delay", KeyDelayConfig()))
        self._mouse_delay: KeyDelayConfig = copy.deepcopy(getattr(self._profile, "mouse_delay", KeyDelayConfig()))
        self._hardware_backend = InterceptionBackend(is_admin=_is_admin())
        self._software_backend = SoftwareBackend()
        self._backend = None
        self._active_backend_mode: Optional[str] = None
        self._backend_status: Optional[Dict[str, Any]] = None

    # ------------------------------------------------------------------ 상호작용 규칙
    def _resume_cycle_for_runner(self, runner: MacroRunner) -> int:
        try:
            cycle = max(0, int(runner.current_cycle()))
        except Exception:
            cycle = 0
        try:
            first_done = bool(runner.first_cycle_done())
        except Exception:
            first_done = False
        if first_done and cycle < 1:
            cycle = 1
        return cycle

    def _record_suspended_holds(self, idx: int, runner: MacroRunner):
        try:
            key_policy, mouse_policy = runner.snapshot_held_inputs_with_policy()
        except Exception:
            key_policy, mouse_policy = {}, {}
        release_keys = {k for k, keep in key_policy.items() if not keep}
        keep_keys = {k for k, keep in key_policy.items() if keep}
        release_mouse = {m for m, keep in mouse_policy.items() if not keep}
        keep_mouse = {m for m, keep in mouse_policy.items() if keep}
        if release_keys or release_mouse:
            self._release_hold_inputs({"keys": release_keys, "mouse": release_mouse})
        payload = {
            "release_keys": release_keys,
            "keep_keys": keep_keys,
            "release_mouse": release_mouse,
            "keep_mouse": keep_mouse,
        }
        if any(payload.values()):
            self._suspended_hold_inputs[idx] = payload
        else:
            self._suspended_hold_inputs.pop(idx, None)

    def _release_hold_inputs(self, entry: Optional[Dict[str, Set[str]]]):
        if not entry:
            return
        for key in list(entry.get("keys", set())):
            try:
                self._send_key("up", key, hold_ms=0)
            except Exception:
                pass
        for btn in list(entry.get("mouse", set())):
            try:
                self._send_mouse("mouse_up", btn, hold_ms=0)
            except Exception:
                pass

    def _release_suspended_hold_inputs(self):
        items = list(self._suspended_hold_inputs.items())
        self._suspended_hold_inputs.clear()
        for _, entry in items:
            self._release_hold_inputs(entry)

    @staticmethod
    def _normalize_targets(raw: Optional[List[str]]) -> Set[str]:
        items: Set[str] = set()
        for item in raw or []:
            try:
                text = str(item).strip().lower()
            except Exception:
                text = ""
            if text:
                items.add(text)
        return items

    def _macro_identifier(self, macro: Macro, idx: Optional[int]) -> str:
        if getattr(macro, "name", None):
            try:
                name = str(macro.name).strip()
            except Exception:
                name = ""
            if name:
                return name.lower()
        try:
            key = str(macro.primary_trigger().key if hasattr(macro, "primary_trigger") else macro.trigger_key).strip()
        except Exception:
            key = ""
        if key:
            return key.lower()
        return f"macro-{idx}" if idx is not None else "macro-unknown"

    def set_debug_image_override(self, frame: Optional[np.ndarray], *, label: str | None = None):
        self._debug_image_override = frame
        self._debug_image_label = label

    def clear_debug_image_override(self):
        self._debug_image_override = None
        self._debug_image_label = None

    def _extract_debug_region(self, region: Region) -> Optional[np.ndarray]:
        """
        현재 설정된 디버그 이미지에서 지정 영역을 잘라 반환한다.
        영역이 유효하지 않거나 이미지가 없으면 None을 반환한다.
        """
        if self._debug_image_override is None:
            return None
        try:
            x, y, w, h = region
            if w <= 0 or h <= 0:
                return None
            frame = np.asarray(self._debug_image_override, dtype=np.uint8)
            if frame.ndim != 3 or frame.shape[2] < 3:
                return None
            if y < 0 or x < 0 or (y + h) > frame.shape[0] or (x + w) > frame.shape[1]:
                return None
            return frame[y : y + h, x : x + w, :3].copy()
        except Exception:
            return None

    def _interaction_mode(self, macro: Macro) -> Optional[Literal["stop", "suspend"]]:
        mode = str(getattr(macro, "interaction_outgoing_mode", "none") or "none").lower()
        if mode not in ("none", "stop", "suspend"):
            mode = "none"
        if mode == "none":
            if getattr(macro, "stop_others_on_trigger", False):
                mode = "stop"
            elif getattr(macro, "suspend_others_while_running", False):
                mode = "suspend"
        if mode == "none":
            return None
        return mode  # type: ignore[return-value]

    def _interaction_target_allowed(
        self,
        actor_macro: Macro,
        actor_idx: int,
        target_macro: Macro,
        target_idx: int,
    ) -> bool:
        actor_id = self._macro_identifier(actor_macro, actor_idx)
        target_id = self._macro_identifier(target_macro, target_idx)

        targets = self._normalize_targets(getattr(actor_macro, "interaction_targets", []))
        excludes = self._normalize_targets(getattr(actor_macro, "interaction_exclude_targets", []))
        if targets and target_id not in targets:
            return False
        if target_id in excludes:
            return False

        allow = self._normalize_targets(getattr(target_macro, "interaction_incoming_allow", []))
        block = self._normalize_targets(getattr(target_macro, "interaction_incoming_block", []))
        if allow and actor_id not in allow:
            return False
        if actor_id in block:
            return False
        return True

    def _apply_macro_interaction(self, actor_idx: int):
        macros = list(self._profile.macros)
        if actor_idx < 0 or actor_idx >= len(macros):
            return
        actor_macro = macros[actor_idx]
        mode = self._interaction_mode(actor_macro)
        if mode is None:
            return

        suspended = False
        for idx, runner in list(self._macro_runners.items()):
            if idx == actor_idx:
                continue
            target_macro: Optional[Macro] = None
            try:
                target_macro = macros[idx]
            except Exception:
                target_macro = None
            if not target_macro:
                continue
            if not self._interaction_target_allowed(actor_macro, actor_idx, target_macro, idx):
                continue
            toggle_on = bool(self._toggle_states.get(idx, False))
            is_toggle_runner = runner.is_alive() and toggle_on
            if mode == "stop":
                runner.stop()
                self._macro_runners.pop(idx, None)
                self._clear_macro_state(idx)
            elif mode == "suspend":
                if is_toggle_runner:
                    self._suspended_toggle_indices.add(idx)
                    self._suspended_toggle_states[idx] = toggle_on
                    self._suspended_toggle_cycles[idx] = self._resume_cycle_for_runner(runner)
                    runner.stop(release_inputs=False, run_stop_actions=False)
                    self._record_suspended_holds(idx, runner)
                else:
                    try:
                        self._record_suspended_holds(idx, runner)
                    except Exception:
                        pass
                    runner.stop(release_inputs=False, run_stop_actions=False)
                self._macro_runners.pop(idx, None)
                self._clear_macro_state(idx)
                suspended = True
        if mode == "suspend" and suspended:
            self._guard_macro_idx = actor_idx
        self._select_backend(self._input_mode, log=True, allow_fallback=True)
        # 키 반복(초기 지연) 동안 눌림 상태가 끊겨 보이지 않도록 여유를 둔다.
        self._swallow_stale_sec = max(self.tick * 25, 1.0)

    @property
    def events(self) -> "queue.Queue[Dict[str, Any]]":
        return self._events

    def drain_events(
        self,
        *,
        drop_types: Optional[Set[str]] = None,
        max_events: Optional[int] = None,
        max_time: Optional[float] = None,
    ) -> List[Dict[str, Any]]:
        """
        이벤트 큐를 비우면서 필요한 이벤트만 반환한다.
        drop_types에 포함된 타입은 제거만 하고 무시하며,
        max_events / max_time으로 한 번에 처리량을 제한해 GUI 스레드 정지를 방지한다.
        """
        drained: List[Dict[str, Any]] = []
        drop = set(drop_types or [])
        start = time.perf_counter() if max_time not in (None, 0) else None
        while True:
            if max_events is not None and len(drained) >= max_events:
                break
            if start is not None and (time.perf_counter() - start) >= max_time:
                break
            try:
                event = self._events.get_nowait()
            except queue.Empty:
                break
            if drop and event.get("type") in drop:
                continue
            drained.append(event)
        return drained

    def _reset_timers(self):
        with self._timer_lock:
            self._timers = [{"start": None, "offset": 0.0} for _ in range(20)]

    def _set_timer(self, slot: int, seconds: float):
        idx = max(0, min(len(self._timers) - 1, slot - 1))
        value = max(0.0, float(seconds))
        now = time.monotonic()
        with self._timer_lock:
            self._timers[idx] = {"start": now, "offset": value}

    def _get_timer_value(self, slot: int) -> float:
        idx = slot - 1
        with self._timer_lock:
            if idx < 0 or idx >= len(self._timers):
                return 0.0
            state = self._timers[idx]
            offset = float(state.get("offset", 0.0))
            start = state.get("start")
        if start is None:
            return max(0.0, offset)
        return max(0.0, offset + (time.monotonic() - start))

    def update_profile(self, profile: MacroProfile):
        app_ctx = self._get_app_context(force=True)
        with self._lock:
            self._profile = copy.deepcopy(profile)
            swallow_keys = self._swallow_keys_locked(app_ctx)
            device_id = self._profile.keyboard_device_id
            hardware_id = self._profile.keyboard_hardware_id
            mouse_device_id = getattr(self._profile, "mouse_device_id", None)
            mouse_hardware_id = getattr(self._profile, "mouse_hardware_id", None)
            self._input_mode = getattr(self._profile, "input_mode", self._input_mode) or "hardware"
            self._key_delay = copy.deepcopy(getattr(self._profile, "key_delay", self._key_delay))
            self._mouse_delay = copy.deepcopy(getattr(self._profile, "mouse_delay", getattr(self, "_mouse_delay", KeyDelayConfig())))
            self._keyboard_test_key = getattr(self._profile, "keyboard_test_key", self._keyboard_test_key)
        self._stop_all_macros()
        self._reset_condition_states()
        self._reset_timers()
        self._swallower.set_keys(swallow_keys)
        self._apply_keyboard_device(device_id, hardware_id, log=False)
        self._apply_mouse_device(mouse_device_id, mouse_hardware_id, log=False)
        self._select_backend(self._input_mode, allow_fallback=True, log=True)
        self._refresh_swallow(app_ctx)
        patterns = _load_shared_patterns()
        profile_patterns = getattr(self._profile, "pixel_patterns", {}) or {}
        for name, pat in profile_patterns.items():
            if name not in patterns:
                patterns[name] = copy.deepcopy(pat)
        self._pixel_patterns = patterns
        # 픽셀 테스트 설정도 프로필에서 동기화
        try:
            expect_exists = True
            if hasattr(profile, "pixel_expect_exists"):
                expect_exists = bool(getattr(profile, "pixel_expect_exists"))
            min_count = max(1, int(getattr(profile, "pixel_min_count", 1) or 1))
            self.update_pixel_test(profile.pixel_region, profile.pixel_color, profile.pixel_tolerance, expect_exists, min_count)
        except Exception:
            pass
        self._emit_state()

    def update_pixel_test(
        self,
        region: Region,
        color: Optional[RGB],
        tolerance: int,
        expect_exists: bool = True,
        min_count: int = 1,
        pattern: Optional[str] = None,
    ):
        self._pixel_test_region = tuple(int(v) for v in region)
        if color is not None:
            self._pixel_test_color = tuple(int(c) for c in color)  # type: ignore[assignment]
        self._pixel_test_tolerance = int(tolerance)
        self._pixel_test_expect_exists = bool(expect_exists)
        self._pixel_test_min_count = max(1, int(min_count))
        self._pixel_test_pattern = pattern

    def run_pixel_test(self, *, source: Optional[str] = None):
        self._run_pixel_test(source=source)

    def run_pixel_check(
        self,
        *,
        region: Region,
        color: Optional[RGB],
        tolerance: int,
        expect_exists: bool = True,
        min_count: int = 1,
        source: Optional[str] = None,
        label: Optional[str] = None,
        pattern: Optional[str] = None,
    ):
        self._run_pixel_test(
            region=region,
            color=color,
            tolerance=tolerance,
            expect_exists=expect_exists,
            min_count=min_count,
            source=source,
            label=label,
            pattern=pattern,
        )

    def activate(self):
        with self._lock:
            self.active = True
            self.paused = False
        self._emit_log("GUI: 활성화")
        self._refresh_swallow(self._get_app_context(force=True))
        self._emit_state()

    def deactivate(self):
        with self._lock:
            self.active = False
            self.paused = False
        self._stop_all_macros()
        self._reset_condition_states()
        self._emit_log("GUI: 비활성화")
        self._refresh_swallow(self._get_app_context(force=True))
        self._emit_state()

    def toggle_pause(self):
        with self._lock:
            if not self.active:
                return
            self.paused = not self.paused
            paused = self.paused
        if paused:
            self._pause_all_macros()
        else:
            self._resume_paused_holds()
        self._emit_log(f"GUI: {'일시정지' if paused else '재개'}")
        self._refresh_swallow(self._get_app_context(force=True))
        self._emit_state()

    def start(self):
        if self.running:
            return
        self.running = True
        self.active = True
        self.paused = False
        self._stop_event.clear()
        self._thread = threading.Thread(target=self._loop, name="MacroEngine", daemon=True)
        self._thread.start()
        self._swallower.start()
        self._refresh_swallow(self._get_app_context(force=True))
        self._emit_state()

    def stop(self):
        self.running = False
        self.active = False
        self.paused = False
        self._stop_event.set()
        self._stop_all_macros()
        self._reset_condition_states()
        self._reset_timers()
        self._swallower.set_enabled(False)
        self._swallower.stop()
        if self._thread and threading.current_thread() is not self._thread:
            self._thread.join(timeout=1.0)
        self._emit_state()

    def snapshot_state(self) -> Dict[str, Any]:
        return {"running": self.running, "active": self.active, "paused": self.paused}

    def _emit_event(self, payload: Dict[str, Any]):
        self._events.put(payload)

    def _emit_log(self, message: str):
        self._emit_event({"type": "log", "message": message})

    def _emit_state(self):
        payload = {"type": "state", **self.snapshot_state(), "backend": self._backend_state_payload()}
        self._emit_event(payload)

    def _normalize_app_ctx(self, info: Optional[Dict[str, Any]]) -> Optional[Dict[str, Any]]:
        if not info:
            return None
        path = str(info.get("path") or "").strip()
        name = str(info.get("name") or "").strip()
        base = name or (Path(path).name if path else "")
        return {
            "pid": info.get("pid"),
            "name": name,
            "path": path,
            "base": base,
            "norm_path": _norm_path(path),
            "norm_base": base.lower() if base else "",
        }

    def _get_app_context(self, *, force: bool = False) -> Optional[Dict[str, Any]]:
        if not hasattr(self, "_app_ctx"):
            self._app_ctx = None
            self._app_ctx_ts = 0.0
        now = time.monotonic()
        if not force and self._app_ctx and (now - self._app_ctx_ts) < max(self.tick * 2, 0.05):
            return self._app_ctx
        info = None
        try:
            info = get_foreground_process()
        except Exception:
            info = None
        self._app_ctx = self._normalize_app_ctx(info)
        self._app_ctx_ts = now
        return self._app_ctx

    def _macro_matches_app(self, macro: Macro, app_ctx: Optional[Dict[str, Any]]) -> bool:
        scope = getattr(macro, "scope", "global") or "global"
        if scope != "app":
            return True
        targets = getattr(macro, "app_targets", []) or []
        if not targets or not app_ctx:
            return False
        ctx_norm_path = app_ctx.get("norm_path") or ""
        ctx_base = app_ctx.get("norm_base") or (app_ctx.get("base") or "").lower()
        for t in targets:
            target = AppTarget.from_any(t)
            if not target:
                continue
            norm_path = target.norm_path()
            norm_name = target.norm_name()
            if norm_path and ctx_norm_path and ctx_norm_path == norm_path:
                return True
            if norm_name:
                if ctx_base and ctx_base == norm_name:
                    return True
                if ctx_norm_path:
                    try:
                        ctx_file = Path(ctx_norm_path).name.lower()
                    except Exception:
                        ctx_file = ctx_norm_path.lower()
                    if ctx_file and ctx_file == norm_name:
                        return True
        return False

    def _macro_triggers(self, macro: Macro) -> List[MacroTrigger]:
        triggers: List[MacroTrigger] = []
        for trig in getattr(macro, "triggers", []) or []:
            t = MacroTrigger.from_any(trig, default_mode=getattr(macro, "mode", "hold"), default_hold=getattr(macro, "hold_press_seconds", None))
            if t and t.key:
                triggers.append(t)
        if not triggers:
            triggers.append(MacroTrigger(key=macro.trigger_key, mode=getattr(macro, "mode", "hold"), hold_press_seconds=getattr(macro, "hold_press_seconds", None)))
        macro.triggers = triggers
        primary = triggers[0]
        macro.trigger_key = primary.key
        macro.mode = primary.mode
        try:
            macro.hold_press_seconds = None if primary.hold_press_seconds in (None, "", False) else max(0.0, float(primary.hold_press_seconds))
        except Exception:
            macro.hold_press_seconds = None
        return triggers

    def _swallow_keys_locked(self, app_ctx: Optional[Dict[str, Any]] = None) -> List[str]:
        ctx = app_ctx if app_ctx is not None else self._get_app_context()
        keys: List[str] = []
        seen: Set[str] = set()
        mod_keys = _TRIGGER_MOD_KEYS
        for m in self._profile.macros:
            if not getattr(m, "enabled", True) or not m.suppress_trigger:
                continue
            if not self._macro_matches_app(m, ctx):
                continue
            for trig in self._macro_triggers(m):
                for k in parse_trigger_keys(trig.key):
                    if k in mod_keys:
                        continue  # modifier는 삼키지 않아야 다른 앱 단축키/조합이 깨지지 않는다
                    if k in seen:
                        continue
                    seen.add(k)
                    keys.append(k)
        return keys

    def _swallow_keys(self, app_ctx: Optional[Dict[str, Any]] = None) -> List[str]:
        with self._lock:
            return self._swallow_keys_locked(app_ctx)

    def _refresh_swallow(self, app_ctx: Optional[Dict[str, Any]] = None):
        keys = self._swallow_keys(app_ctx)
        self._swallower.set_keys(keys)
        # 스레드가 예외로 죽었을 때 자동으로 다시 올려준다.
        self._swallower.start()
        self._swallower.set_enabled(bool(keys) and self.active and not self.paused and self._active_backend_mode == "hardware")

    def _backend_state_payload(self, *, refresh: bool = False) -> Dict[str, Any]:
        if refresh or self._backend_status is None:
            cold_start = self._backend_status is None
            # 첫 호출에서는 FriendlyName 조회를 건너뛰어 시작 속도를 우선한다.
            friendly_lookup = not cold_start
            hardware_status = self._hardware_backend.status(friendly=friendly_lookup) if self._hardware_backend else None
            software_status = self._software_backend.status() if self._software_backend else None
            self._backend_status = {
                "requested_mode": self._input_mode,
                "active_mode": self._active_backend_mode,
                "keyboard_device_id": self._profile.keyboard_device_id,
                "keyboard_hardware_id": self._profile.keyboard_hardware_id,
                "mouse_device_id": getattr(self._profile, "mouse_device_id", None),
                "mouse_hardware_id": getattr(self._profile, "mouse_hardware_id", None),
                "keyboard_test_key": self._keyboard_test_key,
                "hardware": hardware_status.to_dict() if hardware_status else None,
                "software": software_status.to_dict() if software_status else None,
            }
        return dict(self._backend_status)

    def _select_backend(self, requested_mode: Optional[str], *, allow_fallback: bool = True, log: bool = True):
        mode = (requested_mode or "hardware").lower()
        if mode not in ("hardware", "software"):
            mode = "hardware"
        self._input_mode = mode
        if mode == "hardware":
            self._apply_keyboard_device(self._keyboard_device_id, self._keyboard_hardware_id, log=False, refresh_status=False)
            self._apply_mouse_device(self._mouse_device_id, self._mouse_hardware_id, log=False, refresh_status=False)
        hw_status = self._hardware_backend.status() if self._hardware_backend else None
        sw_status = self._software_backend.status() if self._software_backend else None
        chosen = self._hardware_backend if mode == "hardware" else self._software_backend
        chosen_status = hw_status if mode == "hardware" else sw_status
        if chosen_status and not chosen_status.available and allow_fallback and mode == "hardware":
            if sw_status and sw_status.available:
                if log:
                    msg = chosen_status.message or "Interception 미설치/권한 부족. 소프트웨어 입력으로 전환합니다."
                    self._emit_log(msg)
                chosen = self._software_backend
                self._active_backend_mode = "software"
            else:
                self._active_backend_mode = chosen.mode if chosen else None
        else:
            self._active_backend_mode = chosen.mode if chosen else None
        self._backend = chosen
        self._backend_status = self._backend_state_payload(refresh=True)
        return self._backend_status

    def _apply_keyboard_device(self, device_id: Optional[int], hardware_id: Optional[str], *, log: bool = True, refresh_status: bool = True):
        if not self._hardware_backend:
            return {}
        status = self._hardware_backend.set_device(device_id=device_id, hardware_id=hardware_id)
        current = status.current_device or {}
        with self._lock:
            self._profile.keyboard_device_id = current.get("id")
            self._profile.keyboard_hardware_id = current.get("hardware_id")
            self._keyboard_device_id = self._profile.keyboard_device_id
            self._keyboard_hardware_id = self._profile.keyboard_hardware_id

        if log:
            if status.available and current.get("id"):
                friendly = current.get("friendly_name") or (current.get("hardware_id") or "알 수 없음")
                self._emit_log(f"키보드 장치 설정: #{current.get('id')} ({friendly})")
            elif not status.installed:
                self._emit_log(f"키보드 장치 설정 실패: {status.message or 'Interception 미설치'}")
            else:
                self._emit_log(f"키보드 장치 설정 실패: {status.message or 'Interception 키보드 미검출'}")
        if refresh_status:
            self._backend_status = self._backend_state_payload(refresh=True)
        return current

    def _apply_mouse_device(self, device_id: Optional[int], hardware_id: Optional[str], *, log: bool = True, refresh_status: bool = True):
        if not self._hardware_backend:
            return {}
        status = self._hardware_backend.set_mouse_device(device_id=device_id, hardware_id=hardware_id)
        current = status.current_mouse or {}
        with self._lock:
            self._profile.mouse_device_id = current.get("id")
            self._profile.mouse_hardware_id = current.get("hardware_id")
            self._mouse_device_id = self._profile.mouse_device_id
            self._mouse_hardware_id = self._profile.mouse_hardware_id

        if log:
            if status.available and current.get("id"):
                friendly = current.get("friendly_name") or (current.get("hardware_id") or "알 수 없음")
                self._emit_log(f"마우스 장치 설정: #{current.get('id')} ({friendly})")
            elif not status.installed:
                self._emit_log(f"마우스 장치 설정 실패: {status.message or 'Interception 미설치'}")
            else:
                self._emit_log(f"마우스 장치 설정 실패: {status.message or 'Interception 마우스 미검출'}")
        if refresh_status:
            self._backend_status = self._backend_state_payload(refresh=True)
        return current

    def set_keyboard_device(self, device_id: Optional[int] = None, hardware_id: Optional[str] = None) -> Dict[str, Any]:
        """UI에서 선택한 장치를 적용."""
        status = self._apply_keyboard_device(device_id, hardware_id, log=True, refresh_status=True)
        self._select_backend(self._input_mode, allow_fallback=True, log=False)
        return status or {}

    def current_keyboard_device(self) -> Dict[str, Any]:
        backend = self._backend
        if backend:
            current = backend.current_device()
            return current or {}
        return {}

    def current_mouse_device(self) -> Dict[str, Any]:
        backend = self._backend
        if backend and hasattr(backend, "current_mouse"):
            try:
                current = backend.current_mouse()
            except Exception:
                current = None
            return current or {}
        return {}

    def keyboard_status(self, *, refresh: bool = True) -> Dict[str, Any]:
        return self._backend_state_payload(refresh=refresh)

    def apply_keyboard_settings(
        self,
        *,
        mode: str,
        device_id: Optional[int] = None,
        hardware_id: Optional[str] = None,
        mouse_device_id: Optional[int] = None,
        mouse_hardware_id: Optional[str] = None,
        key_delay: Optional[KeyDelayConfig] = None,
        mouse_delay: Optional[KeyDelayConfig] = None,
        test_key: Optional[str] = None,
    ) -> Dict[str, Any]:
        key_delay_cfg = copy.deepcopy(key_delay or self._key_delay or KeyDelayConfig())
        mouse_delay_cfg = copy.deepcopy(mouse_delay or self._mouse_delay or KeyDelayConfig())
        with self._lock:
            self._input_mode = mode or self._input_mode
            self._profile.input_mode = self._input_mode
            self._key_delay = key_delay_cfg
            self._profile.key_delay = copy.deepcopy(key_delay_cfg)
            self._mouse_delay = mouse_delay_cfg
            self._profile.mouse_delay = copy.deepcopy(mouse_delay_cfg)
            if test_key:
                self._keyboard_test_key = test_key
                self._profile.keyboard_test_key = test_key
            self._profile.keyboard_device_id = device_id
            self._profile.keyboard_hardware_id = hardware_id
            self._keyboard_device_id = device_id
            self._keyboard_hardware_id = hardware_id
            self._profile.mouse_device_id = mouse_device_id
            self._profile.mouse_hardware_id = mouse_hardware_id
            self._mouse_device_id = mouse_device_id
            self._mouse_hardware_id = mouse_hardware_id
        self._apply_keyboard_device(device_id, hardware_id, log=False)
        self._apply_mouse_device(mouse_device_id, mouse_hardware_id, log=False)
        self._select_backend(self._input_mode, allow_fallback=True, log=True)
        self._emit_state()
        return self._backend_state_payload(refresh=False)

    def test_keyboard(self, key: str) -> tuple[bool, str]:
        press_delay = self._key_delay.resolved_press_delay() if self._key_delay else 0
        ok = self._send_key("press", key, hold_ms=press_delay)
        msg = f"테스트 {'성공' if ok else '실패'}: {key.upper()}"
        self._emit_log(msg)
        return ok, msg

    def test_mouse(self, button: str = "mouse1") -> tuple[bool, str]:
        hold_ms, _ = self._resolve_mouse_delays(None)
        ok = self._send_mouse("mouse_click", button, hold_ms=hold_ms)
        msg = f"마우스 테스트 {'성공' if ok else '실패'}: {button}"
        self._emit_log(msg)
        return ok, msg

    def _resolve_key_delays(self, action: Action | None = None) -> tuple[int, int]:
        cfg = self._key_delay if self._key_delay else KeyDelayConfig()
        use_override = bool(getattr(action, "key_delay_override_enabled", False))
        override = getattr(action, "key_delay_override", None) if use_override else None
        if isinstance(override, KeyDelayConfig):
            cfg = override
        press_delay = cfg.resolved_press_delay()
        gap_delay = cfg.resolved_gap_delay()
        return press_delay, gap_delay

    def _resolve_mouse_delays(self, action: Action | None = None) -> tuple[int, int]:
        cfg = self._mouse_delay if getattr(self, "_mouse_delay", None) else KeyDelayConfig()
        use_override = bool(getattr(action, "key_delay_override_enabled", False))
        override = getattr(action, "key_delay_override", None) if use_override else None
        if isinstance(override, KeyDelayConfig):
            cfg = override
        press_delay = cfg.resolved_press_delay()
        gap_delay = cfg.resolved_gap_delay()
        return press_delay, gap_delay

    def _parse_combo_keys(self, key: str) -> list[str]:
        """
        `ctrl+shift+a` 형태의 콤보 문자열을 리스트로 풀어준다.
        구분자가 없으면 단일 키로 간주한다.
        """
        raw = str(key or "").strip()
        if not raw:
            return []
        cleaned = raw.replace(" ", "")
        parts = [p.strip().lower() for p in cleaned.split("+") if p.strip()]
        if len(parts) <= 1:
            single = cleaned.lower()
            return [single] if single else []
        return parts

    def _send_keys_with_backend(self, backend, action_type: str, keys: list[str], hold_ms: int = 0):
        if action_type == "press":
            for k in keys:
                backend.down(k)
            if hold_ms > 0:
                time.sleep(hold_ms / 1000.0)
            for k in reversed(keys):
                backend.up(k)
            return
        if action_type == "down":
            for k in keys:
                backend.down(k)
            return
        if action_type == "up":
            for k in reversed(keys):
                backend.up(k)
            return
        raise ValueError(f"Unknown key action type: {action_type}")

    def _send_key(self, action_type: str, key: str, *, hold_ms: int = 0) -> bool:
        backend = self._backend or self._software_backend
        if backend is None:
            return False
        combo_keys = self._parse_combo_keys(key)
        if not combo_keys:
            return False
        try:
            self._send_keys_with_backend(backend, action_type, combo_keys, hold_ms=hold_ms)
            for k in combo_keys:
                self._mark_sent(k)
            return True
        except Exception as exc:
            self._emit_log(f"키 입력 실패({backend.mode}): {exc}")
            if getattr(backend, "mode", None) == "hardware":
                self._select_backend("software", allow_fallback=True, log=True)
                self._emit_state()
                fb = self._backend
                if fb and fb is not backend:
                    try:
                        self._send_keys_with_backend(fb, action_type, combo_keys, hold_ms=hold_ms)
                        for k in combo_keys:
                            self._mark_sent(k)
                        return True
                    except Exception as exc2:
                        self._emit_log(f"소프트웨어 입력 실패: {exc2}")
            return False

    def _send_mouse(self, action_type: str, button: str, *, hold_ms: int = 0, pos: Optional[tuple[int, int]] = None) -> bool:
        backend = self._backend or self._software_backend
        if backend is None:
            return False
        x = pos[0] if pos else None
        y = pos[1] if pos else None
        try:
            if action_type == "mouse_move":
                if x is None or y is None:
                    return False
                backend.mouse_move(x, y)
            elif action_type == "mouse_down":
                backend.mouse_down(button, x=x, y=y)
            elif action_type == "mouse_up":
                backend.mouse_up(button, x=x, y=y)
            elif action_type == "mouse_click":
                backend.mouse_click(button, hold_ms=hold_ms, x=x, y=y)
            else:
                return False
            if action_type in ("mouse_down", "mouse_up", "mouse_click"):
                self._mark_sent(button)
            return True
        except Exception as exc:
            self._emit_log(f"마우스 입력 실패({getattr(backend, 'mode', 'unknown')}): {exc}")
            fb = self._software_backend
            if fb and fb is not backend:
                try:
                    if action_type == "mouse_move":
                        if x is None or y is None:
                            return False
                        fb.mouse_move(x, y)
                    elif action_type == "mouse_down":
                        fb.mouse_down(button, x=x, y=y)
                    elif action_type == "mouse_up":
                        fb.mouse_up(button, x=x, y=y)
                    elif action_type == "mouse_click":
                        fb.mouse_click(button, hold_ms=hold_ms, x=x, y=y)
                    else:
                        return False
                    if action_type in ("mouse_down", "mouse_up", "mouse_click"):
                        self._mark_sent(button)
                    return True
                except Exception as exc2:
                    self._emit_log(f"소프트웨어 마우스 입력 실패: {exc2}")
            return False

    def _key_state_detail(self, key: str) -> tuple[bool, Dict[str, Any]]:
        tracked = self._swallower.is_tracked(key)
        sw_enabled = tracked and self._swallower.is_enabled() and self._swallower.is_alive()
        sw_pressed = False
        sw_age: Optional[float] = None
        os_pressed = False
        if sw_enabled:
            sw_pressed = self._swallower.is_pressed(key, max_age=self._swallow_stale_sec)
            ts = self._swallower.last_pressed_at(key)
            if ts is not None:
                sw_age = time.monotonic() - ts
        try:
            os_pressed = bool(get_keystate(key, async_=True))
        except Exception:
            os_pressed = False
        pressed = bool(sw_pressed or os_pressed)
        detail = {
            "tracked": tracked,
            "sw_enabled": sw_enabled,
            "sw_pressed": sw_pressed,
            "sw_age": sw_age,
            "sw_stale": sw_age is not None and sw_age > self._swallow_stale_sec,
            "os_pressed": os_pressed,
        }
        return pressed, detail

    def _trigger_state(self, trigger: str, *, disallow_extra_modifiers: bool = False) -> tuple[bool, Dict[str, Any]]:
        keys = parse_trigger_keys(trigger)
        if not keys:
            return False, {"keys": []}

        required_mods = {k for k in keys if k in _TRIGGER_MOD_ALIASES}

        def _extra_mod_details() -> List[Dict[str, Any]]:
            mods: List[Dict[str, Any]] = []
            if not disallow_extra_modifiers:
                return mods
            for mod in _TRIGGER_MOD_ALIASES:
                if mod in required_mods:
                    continue
                pressed, detail = self._key_state_detail(mod)
                if pressed:
                    mods.append({"key": mod, "pressed": pressed, **detail})
            return mods

        if len(keys) == 1:
            pressed, detail = self._key_state_detail(keys[0])
            extra_mods = _extra_mod_details()
            blocked = bool(extra_mods)
            if blocked:
                pressed = False
            merged = dict(detail)
            merged["keys"] = [{"key": keys[0], "pressed": pressed, **detail}]
            merged.setdefault("sw_pressed", merged.get("sw_pressed", False))
            merged.setdefault("os_pressed", merged.get("os_pressed", False))
            merged.setdefault("sw_age", merged.get("sw_age"))
            merged.setdefault("sw_stale", merged.get("sw_stale", False))
            merged["extra_mods"] = extra_mods
            merged["blocked_by_extra_mods"] = blocked
            return pressed, merged

        all_pressed = True
        details: List[Dict[str, Any]] = []
        sw_pressed_any = False
        os_pressed_all = True
        sw_age: Optional[float] = None
        sw_stale_any = False
        for key in keys:
            pressed, d = self._key_state_detail(key)
            details.append({"key": key, "pressed": pressed, **d})
            if not pressed:
                all_pressed = False
            sw_pressed_any = sw_pressed_any or d.get("sw_pressed", False)
            os_pressed_all = os_pressed_all and d.get("os_pressed", False)
            age = d.get("sw_age")
            if age is not None:
                sw_age = age if sw_age is None else min(sw_age, age)
            sw_stale_any = sw_stale_any or d.get("sw_stale", False)

        extra_mods = _extra_mod_details()
        blocked = bool(extra_mods)
        if blocked:
            all_pressed = False
        merged = {
            "keys": details,
            "sw_pressed": sw_pressed_any,
            "os_pressed": os_pressed_all,
            "sw_age": sw_age,
            "sw_stale": sw_stale_any,
            "extra_mods": extra_mods,
            "blocked_by_extra_mods": blocked,
        }
        return all_pressed, merged

    def _key_pressed(self, key: str) -> bool:
        """
        트리거 키를 삼키는 경우 OS에 전달되지 않으므로 swallower가 추적한 상태로 판단.
        그 외에는 OS 키 상태를 사용.
        """
        pressed, _ = self._trigger_state(key)
        return pressed

    def _mark_sent(self, key: str):
        if not key:
            return
        try:
            norm = str(key).lower()
        except Exception:
            norm = str(key)
        self._recent_sends[norm] = time.monotonic()

    def _sent_recent(self, key: str, window: float) -> bool:
        if window <= 0:
            return False
        try:
            norm = str(key).lower()
        except Exception:
            norm = str(key)
        ts = self._recent_sends.get(norm)
        return ts is not None and (time.monotonic() - ts) <= window

    def _sent_recent_trigger(self, trigger: str, window: float) -> bool:
        keys = parse_trigger_keys(trigger)
        if not keys:
            return False
        return any(self._sent_recent(k, window) for k in keys)

    def _edge(self, trigger: str, *, ignore_recent_sec: float = 0.0, disallow_extra_modifiers: bool = False) -> bool:
        pressed, _ = self._trigger_state(trigger, disallow_extra_modifiers=disallow_extra_modifiers)
        norm = normalize_trigger_key(trigger)
        prev = self._hotkey_states.get(norm, False)

        # 매크로가 방금 보낸 입력이면 토글로 취급하지 않는다.
        if ignore_recent_sec > 0 and self._sent_recent_trigger(trigger, ignore_recent_sec):
            self._hotkey_states[norm] = pressed
            return False

        edge = pressed and not prev
        self._hotkey_states[norm] = pressed
        return edge

    def _log_hold_transition(
        self,
        macro: Macro,
        idx: int,
        trigger: str,
        stage: str,
        state: Dict[str, Any],
        *,
        elapsed: Optional[float] = None,
        note: Optional[str] = None,
    ):
        parts = [f"[hold:{stage}]", f"key={trigger}", f"idx={idx}"]
        src = "sw" if state.get("sw_pressed") else ("os" if state.get("os_pressed") else "-")
        parts.append(f"src={src}")
        if state.get("sw_age") is not None:
            parts.append(f"sw_age={state['sw_age']:.3f}s")
        if state.get("sw_stale"):
            parts.append("stale")
        if macro.cycle_count not in (None, 0):
            parts.append(f"cycle_limit={macro.cycle_count}")
        if elapsed is not None:
            parts.append(f"elapsed={elapsed:.3f}s")
        if note:
            parts.append(str(note))
        self._emit_log(" ".join(parts))

    def _handle_hotkeys(self):
        if self._edge("home", disallow_extra_modifiers=True):
            self.active = True
            self.paused = False
            self._emit_log("Home: 활성화")
            self._emit_state()
        if self._edge("insert", disallow_extra_modifiers=True):
            if self.active:
                self.paused = not self.paused
                self._emit_log(f"Insert: {'일시정지' if self.paused else '재개'}")
                if self.paused:
                    self._pause_all_macros()
                else:
                    self._resume_paused_holds()
                self._emit_state()
        if self._edge("end", disallow_extra_modifiers=True):
            self.active = False
            self.paused = False
            self._stop_all_macros()
            self._reset_condition_states()
            self._emit_log("End: 비활성화")
            self._emit_state()
        if self._edge("pageup", disallow_extra_modifiers=True):
            self._run_pixel_test(source="hotkey")

    def _loop(self):
        self._emit_state()
        while not self._stop_event.is_set():
            self._handle_hotkeys()
            app_ctx = self._get_app_context()
            self._refresh_swallow(app_ctx)
            if not self.running:
                break

            if not self.active or self.paused:
                time.sleep(self.tick)
                continue

            with self._lock:
                macros = list(self._profile.macros)

            for idx, macro in enumerate(macros):
                if self._guard_macro_idx is not None and idx != self._guard_macro_idx:
                    # 가드 매크로가 동작 중이면 다른 매크로는 대기
                    continue
                if not getattr(macro, "enabled", True):
                    runner = self._macro_runners.pop(idx, None)
                    if runner:
                        runner.stop()
                    self._clear_macro_state(idx)
                    continue
                if not self._macro_matches_app(macro, app_ctx):
                    runner = self._macro_runners.pop(idx, None)
                    if runner:
                        runner.stop()
                        if self._guard_macro_idx == idx:
                            self._guard_macro_idx = None
                            self._resume_suspended_toggles()
                    self._clear_macro_state(idx)
                    continue
                runner = self._macro_runners.get(idx)
                triggers = self._macro_triggers(macro)
                was_active_hold = any(k[0] == idx for k in self._active_hold_triggers)
                toggle_on = bool(self._toggle_states.get(idx, False))
                active_holds: Set[tuple[int, int]] = {k for k in self._active_hold_triggers if k[0] == idx}
                hold_raw_prev: Dict[int, bool] = {}
                hold_key_sets: Dict[int, Set[str]] = {}
                for trig_idx, trig in enumerate(triggers):
                    if trig.mode != "hold":
                        continue
                    hold_raw_prev[trig_idx] = self._hold_raw_state.get((idx, trig_idx), False)
                    hold_key_sets[trig_idx] = set(parse_trigger_keys(trig.key))

                for trig_idx, trig in enumerate(triggers):
                    if trig.mode == "hold":
                        is_active = self._update_hold_trigger(idx, trig_idx, macro, trig)
                        if is_active:
                            active_holds.add((idx, trig_idx))
                            # 홀드가 잡히는 순간 토글 상태를 강제로 해제하여
                            # 토글→홀드 전환 시 홀드 업에 맞춰 멈추도록 한다.
                            if toggle_on:
                                toggle_on = False
                                self._toggle_states[idx] = False
                        else:
                            active_holds.discard((idx, trig_idx))
                    else:
                        # 이미 이전 루프부터 홀드가 유지 중이면 토글을 무시하지만,
                        # 이번 루프에 처음 홀드가 잡힌 순간(예: Ctrl을 먼저 누르고 mouse4를 눌러 토글 의도)에는 허용한다.
                        toggle_keys = set(parse_trigger_keys(trig.key))
                        hold_was_down_prev = any(
                            hold_raw_prev.get(h_idx, False)
                            and bool(toggle_keys & hold_key_sets.get(h_idx, set()))
                            and not self._hold_blocked_by_extra_mods.get((idx, h_idx), False)
                            for h_idx in hold_key_sets
                        )
                        hold_was_down_cur = any(
                            # 홀드 키를 이미 누른 상태에서 모디파이어만 추가되면 토글로 전환되지 않도록 막는다.
                            self._hold_raw_state.get((idx, h_idx), False)
                            and bool(toggle_keys & hold_key_sets.get(h_idx, set()))
                            and not self._hold_blocked_by_extra_mods.get((idx, h_idx), False)
                            for h_idx in hold_key_sets
                        )
                        if (active_holds and was_active_hold) or hold_was_down_prev or hold_was_down_cur:
                            # 홀드가 잡혀 있으면 토글 트리거는 무시해 오동작을 막는다.
                            continue
                        ignore_window = self._edge_block_window if runner is not None else 0.0
                        if self._edge(trig.key, ignore_recent_sec=ignore_window, disallow_extra_modifiers=True):
                            toggle_on = not toggle_on
                            self._toggle_states[idx] = toggle_on

                self._active_hold_triggers = {k for k in self._active_hold_triggers if k[0] != idx} | active_holds
                self._toggle_states[idx] = toggle_on

                # cycle_count 설정된 홀드 매크로는 트리거를 뗄 때까지 재시작하지 않는다.
                hold_blocked = False
                if macro.mode == "hold" and idx in self._hold_exhausted_indices:
                    if active_holds:
                        hold_blocked = True
                    else:
                        self._hold_exhausted_indices.discard(idx)

                should_run = toggle_on or bool(active_holds)
                if hold_blocked:
                    should_run = False

                if should_run and runner is None:
                    self._apply_macro_interaction(idx)
                    runner = MacroRunner(macro, self, idx)
                    self._macro_runners[idx] = runner
                    runner.start()
                elif not should_run and runner is not None:
                    self._toggle_states[idx] = False
                    if runner.should_finish_first_cycle():
                        if not runner.first_cycle_done():
                            runner.request_stop_after_cycle()
                        elif runner.is_stop_after_cycle_requested():
                            pass
                        else:
                            runner.stop()
                            self._macro_runners.pop(idx, None)
                    else:
                        runner.stop()
                        self._macro_runners.pop(idx, None)

                runner = self._macro_runners.get(idx)
                if runner is not None and not runner.is_alive():
                    self._macro_runners.pop(idx, None)
                    self._toggle_states[idx] = False
                    if macro.mode == "hold" and getattr(macro, "cycle_count", None) not in (None, 0):
                        self._hold_exhausted_indices.add(idx)

            time.sleep(self.tick)
            self._clear_guard_if_needed()

        self._stop_all_macros()
        self.running = False
        self.active = False
        self.paused = False
        self._emit_state()

    def _pause_all_macros(self):
        release_keys: Set[str] = set()
        release_mouse: Set[str] = set()
        keep_keys: Set[str] = set()
        keep_mouse: Set[str] = set()
        for idx, runner in list(self._macro_runners.items()):
            try:
                key_policy, mouse_policy = runner.snapshot_held_inputs_with_policy()
            except Exception:
                key_policy, mouse_policy = {}, {}
            for k, keep in key_policy.items():
                if keep:
                    keep_keys.add(k)
                else:
                    release_keys.add(k)
            for m, keep in mouse_policy.items():
                if keep:
                    keep_mouse.add(m)
                else:
                    release_mouse.add(m)
            runner.stop(release_inputs=False, run_stop_actions=False)
            self._macro_runners.pop(idx, None)
            self._clear_macro_state(idx)
        self._paused_hold_inputs = {
            "release_keys": release_keys,
            "release_mouse": release_mouse,
            "keep_keys": keep_keys,
            "keep_mouse": keep_mouse,
        }
        if release_keys or release_mouse:
            self._release_hold_inputs({"keys": release_keys, "mouse": release_mouse})

    def _resume_paused_holds(self):
        keys = set(self._paused_hold_inputs.get("release_keys", set()))
        mouse = set(self._paused_hold_inputs.get("release_mouse", set()))
        if not keys and not mouse:
            return
        for key in keys:
            try:
                self._send_key("down", key, hold_ms=0)
            except Exception:
                pass
        for btn in mouse:
            try:
                self._send_mouse("mouse_down", btn, hold_ms=0)
            except Exception:
                pass
        self._paused_hold_inputs = {
            "release_keys": set(),
            "release_mouse": set(),
            "keep_keys": set(),
            "keep_mouse": set(),
        }

    def _stop_all_macros(self):
        for idx, runner in list(self._macro_runners.items()):
            runner.stop()
            if runner.is_alive():
                self._emit_log(f"매크로 스레드가 아직 종료되지 않음: {runner.macro.trigger_label(include_mode=False) or runner.macro.trigger_key}")
            self._macro_runners.pop(idx, None)
        if self._paused_hold_inputs:
            all_keys = set(self._paused_hold_inputs.get("release_keys", set())) | set(
                self._paused_hold_inputs.get("keep_keys", set())
            )
            all_mouse = set(self._paused_hold_inputs.get("release_mouse", set())) | set(
                self._paused_hold_inputs.get("keep_mouse", set())
            )
            if all_keys or all_mouse:
                self._release_hold_inputs({"keys": all_keys, "mouse": all_mouse})
        self._hold_release_since.clear()
        self._hold_press_since.clear()
        self._hold_raw_state.clear()
        self._hold_blocked_by_extra_mods.clear()
        self._active_hold_triggers.clear()
        self._toggle_states.clear()
        self._guard_macro_idx = None
        self._suspended_toggle_indices.clear()
        self._suspended_toggle_states.clear()
        self._suspended_toggle_cycles.clear()
        self._release_suspended_hold_inputs()
        self._paused_hold_inputs = {
            "release_keys": set(),
            "release_mouse": set(),
            "keep_keys": set(),
            "keep_mouse": set(),
        }
        self._hold_exhausted_indices.clear()

    def _stop_other_macros(self, except_idx: Optional[int] = None):
        for idx, runner in list(self._macro_runners.items()):
            if except_idx is not None and idx == except_idx:
                continue
            try:
                self._record_suspended_holds(idx, runner)
            except Exception:
                pass
            runner.stop(release_inputs=False, run_stop_actions=False)
            self._macro_runners.pop(idx, None)
            self._clear_macro_state(idx)

    def _suspend_other_macros(self, except_idx: Optional[int] = None):
        for idx, runner in list(self._macro_runners.items()):
            if except_idx is not None and idx == except_idx:
                continue
            macro = None
            try:
                macro = self._profile.macros[idx]
            except Exception:
                macro = None
            toggle_on = bool(self._toggle_states.get(idx, False))
            is_toggle_runner = macro and runner.is_alive() and toggle_on
            if is_toggle_runner:
                self._suspended_toggle_indices.add(idx)
                self._suspended_toggle_states[idx] = toggle_on
                self._suspended_toggle_cycles[idx] = self._resume_cycle_for_runner(runner)
                self._record_suspended_holds(idx, runner)
                runner.stop(release_inputs=False, run_stop_actions=False)
            else:
                try:
                    self._record_suspended_holds(idx, runner)
                except Exception:
                    pass
                runner.stop(release_inputs=False, run_stop_actions=False)
            self._macro_runners.pop(idx, None)
            self._clear_macro_state(idx)
        if except_idx is not None:
            self._guard_macro_idx = except_idx

    def _resume_suspended_toggles(self):
        # Restore held inputs for suspended non-toggle macros so their one-time holds survive temporary guard macros.
        non_toggle_indices = [i for i in list(self._suspended_hold_inputs) if i not in self._suspended_toggle_indices]
        for idx in non_toggle_indices:
            held = self._suspended_hold_inputs.pop(idx, {}) or {}
            try:
                macro = self._profile.macros[idx]
            except Exception:
                macro = None
            enabled = macro and getattr(macro, "enabled", True)
            if enabled:
                release_keys = set(held.get("release_keys", set()))
                release_mouse = set(held.get("release_mouse", set()))
                for key in release_keys:
                    try:
                        self._send_key("down", key, hold_ms=0)
                    except Exception:
                        pass
                for btn in release_mouse:
                    try:
                        self._send_mouse("mouse_down", btn, hold_ms=0)
                    except Exception:
                        pass
            else:
                all_keys = set(held.get("release_keys", set())) | set(held.get("keep_keys", set()))
                all_mouse = set(held.get("release_mouse", set())) | set(held.get("keep_mouse", set()))
                self._release_hold_inputs({"keys": all_keys, "mouse": all_mouse})
        for idx in list(self._suspended_toggle_indices):
            start_cycle = self._suspended_toggle_cycles.pop(idx, 0)
            was_on = self._suspended_toggle_states.pop(idx, False)
            held = self._suspended_hold_inputs.pop(idx, None)
            try:
                macro = self._profile.macros[idx]
            except Exception:
                macro = None
            if macro and getattr(macro, "enabled", True) and was_on:
                release_keys = set(held.get("release_keys", set())) if held else set()
                release_mouse = set(held.get("release_mouse", set())) if held else set()
                for key in release_keys:
                    try:
                        self._send_key("down", key, hold_ms=0)
                    except Exception:
                        pass
                for btn in release_mouse:
                    try:
                        self._send_mouse("mouse_down", btn, hold_ms=0)
                    except Exception:
                        pass
                inherit_keys = set(held.get("release_keys", set())) if held else None
                inherit_mouse = set(held.get("release_mouse", set())) if held else None
                runner = MacroRunner(
                    macro,
                    self,
                    idx,
                    inherit_held_keys=inherit_keys,
                    inherit_held_mouse=inherit_mouse,
                )
                self._macro_runners[idx] = runner
                runner.start(start_cycle=start_cycle)
                self._toggle_states[idx] = True
            else:
                if held:
                    all_keys = set(held.get("release_keys", set())) | set(held.get("keep_keys", set()))
                    all_mouse = set(held.get("release_mouse", set())) | set(held.get("keep_mouse", set()))
                    self._release_hold_inputs({"keys": all_keys, "mouse": all_mouse})
            self._suspended_toggle_indices.discard(idx)
            self._suspended_toggle_cycles.pop(idx, None)
            self._suspended_toggle_states.pop(idx, None)

    def _clear_guard_if_needed(self):
        guard_idx = self._guard_macro_idx
        if guard_idx is None:
            return
        if guard_idx in self._macro_runners:
            return
        # 홀드 기반 가드 매크로는 스레드가 cycle_limit으로 종료되어도 키를 떼기 전까지는
        # 다른 매크로를 막아야 하므로, 홀드가 유지되는 동안 가드를 유지한다.
        still_holding_guard = any(k[0] == guard_idx for k in self._active_hold_triggers)
        if still_holding_guard:
            return
        self._guard_macro_idx = None
        self._resume_suspended_toggles()

    def _clear_macro_state(self, macro_idx: int):
        to_remove = [k for k in set(self._hold_press_since) | set(self._hold_raw_state) if k[0] == macro_idx]
        for key in to_remove:
            self._hold_press_since.pop(key, None)
            self._hold_release_since.pop(key, None)
            self._hold_raw_state.pop(key, None)
            self._hold_blocked_by_extra_mods.pop(key, None)
        self._active_hold_triggers = {k for k in self._active_hold_triggers if k[0] != macro_idx}
        self._toggle_states.pop(macro_idx, None)
        if macro_idx not in self._suspended_toggle_indices:
            self._suspended_toggle_cycles.pop(macro_idx, None)
            self._suspended_toggle_states.pop(macro_idx, None)
        self._hold_exhausted_indices.discard(macro_idx)

    def _update_hold_trigger(self, macro_idx: int, trig_idx: int, macro: Macro, trigger: MacroTrigger) -> bool:
        key = (macro_idx, trig_idx)
        # 기본적으로는 모디파이어를 허용하지 않는(strict) 판정을 사용하되,
        # 이미 잡힌 홀드가 있는 상태에서 추가 모디파이어 때문에 strict가 풀리는 경우에는
        # 홀드를 유지하여 토글 오동작을 막는다.
        pressed_strict, strict_detail = self._trigger_state(trigger.key, disallow_extra_modifiers=True)
        pressed_raw, state_detail = self._trigger_state(trigger.key, disallow_extra_modifiers=False)
        self._hold_raw_state[key] = bool(pressed_raw)
        blocked = strict_detail.get("blocked_by_extra_mods", False)
        state_detail["blocked_by_extra_mods"] = blocked
        self._hold_blocked_by_extra_mods[key] = bool(blocked)

        if not pressed_strict and blocked and key in self._active_hold_triggers:
            pressed = True
        else:
            pressed = pressed_strict
        state_detail["raw_pressed"] = pressed_raw
        now = time.monotonic()
        threshold = trigger.hold_press_seconds
        if threshold is None:
            threshold = getattr(macro, "hold_press_seconds", 0.0) or 0.0
        try:
            threshold = max(0.0, float(threshold or 0.0))
        except Exception:
            threshold = 0.0

        if pressed:
            self._hold_release_since.pop(key, None)
            press_since = self._hold_press_since.get(key)
            if press_since is None:
                press_since = now
                self._hold_press_since[key] = press_since
            if key not in self._active_hold_triggers:
                if threshold <= 0.0 or (now - press_since) >= threshold:
                    self._active_hold_triggers.add(key)
                    self._log_hold_transition(
                        macro,
                        macro_idx,
                        trigger.key,
                        "start",
                        state_detail,
                        elapsed=now - press_since if press_since else None,
                    )
            return key in self._active_hold_triggers

        self._hold_press_since.pop(key, None)
        if key in self._active_hold_triggers:
            first_false = self._hold_release_since.get(key)
            if first_false is None:
                self._hold_release_since[key] = now
                self._log_hold_transition(macro, macro_idx, trigger.key, "release_detected", state_detail)
            elif (now - first_false) >= self._hold_release_debounce:
                elapsed = now - first_false
                self._active_hold_triggers.discard(key)
                self._hold_release_since.pop(key, None)
                self._log_hold_transition(macro, macro_idx, trigger.key, "stop", state_detail, elapsed=elapsed, note="key_up")
        else:
            self._hold_release_since.pop(key, None)
        return key in self._active_hold_triggers

    def _reset_condition_states(self):
        with self._cond_lock:
            self._cond_key_states.clear()

    def _evaluate_condition(
        self,
        cond: Condition,
        *,
        key_states: Optional[Dict[str, bool]] = None,
        resolver: Optional[VariableResolver] = None,
        macro_ctx: Optional[Dict[str, Any]] = None,
        path: Optional[List[str]] = None,
        vars_ctx: Optional[MacroVariables] = None,
        pixel_cache: Optional[Dict[Tuple[int, int, int, int], Any]] = None,
    ) -> bool:
        base_result: bool
        detail: Dict[str, Any] = {}
        vars_state = vars_ctx if vars_ctx is not None else getattr(self, "_vars", None)

        if getattr(cond, "enabled", True) is False:
            return False

        if cond.type == "key":
            if not cond.key:
                return False
            pressed = self._key_pressed(cond.key)
            mode = str(cond.key_mode or "hold").lower()
            if key_states is None:
                with self._cond_lock:
                    prev = self._cond_key_states.get(cond.key, False)
                    self._cond_key_states[cond.key] = pressed
            else:
                prev = key_states.get(cond.key, False)
                key_states[cond.key] = pressed
            if mode in ("press", "down"):
                base_result = pressed and not prev
            elif mode == "up":
                base_result = (not pressed) and prev
            elif mode == "released":
                base_result = not pressed
            else:
                base_result = pressed
            detail["key"] = {"key": cond.key, "mode": mode, "pressed": pressed, "prev": prev}
        elif cond.type == "pixel":
            region = cond.region
            color = cond.color
            if cond.region_raw is not None and resolver:
                region = Condition._parse_region(cond.region_raw, resolver)[0]
            if cond.color_raw is not None:
                if resolver:
                    if cond.color_raw.startswith(("/", "$", "@")):
                        resolved = resolver.resolve(cond.color_raw, "color")
                        try:
                            color = Condition._parse_color(resolved, None)[0]
                        except Exception:
                            color = None
                    else:
                        color = Condition._parse_color(cond.color_raw, resolver)[0]
                else:
                    color = cond.color
            pattern_name = getattr(cond, "pixel_pattern", None)
            pattern_obj = self._pixel_patterns.get(pattern_name) if pattern_name else None
            if region is None or (color is None and pattern_obj is None):
                return False
            region_tuple: Region = tuple(int(v) for v in region)
            color_tuple: Optional[RGB] = tuple(int(c) for c in color) if color is not None else None
            expect_exists = getattr(cond, "pixel_exists", True)
            min_count = max(1, int(getattr(cond, "pixel_min_count", 1) or 1))
            check = self._pixel_check(
                region_tuple,
                color_tuple,
                cond.tolerance,
                expect_exists=expect_exists,
                min_count=min_count,
                pixel_cache=pixel_cache,
                pattern=pattern_obj,
            )
            base_result = bool(check.get("result"))
            detail["pixel"] = {
                "region": region_tuple,
                "color": color_tuple,
                "pattern": pattern_name,
                "tolerance": cond.tolerance,
                "expect_exists": expect_exists,
                "min_count": min_count,
                "match_count": check.get("match_count"),
                "found": check.get("found"),
                "coord": check.get("coord"),
                "sample_coord": check.get("sample_coord"),
                "sample_color": check.get("sample_color"),
                "pattern_points": check.get("pattern_points"),
                "pattern_size": check.get("pattern_size"),
            }
        elif cond.type == "all":
            active_children = [c for c in (cond.conditions or []) if getattr(c, "enabled", True)]
            base_result = bool(active_children) and all(
                self._evaluate_condition(
                    c,
                    key_states=key_states,
                    resolver=resolver,
                    macro_ctx=macro_ctx,
                    path=(path or []) + [f"and[{idx}]"],
                    vars_ctx=vars_state,
                    pixel_cache=pixel_cache,
                )
                for idx, c in enumerate(active_children)
            )
            detail["group"] = {
                "mode": "all",
                "count": len(active_children),
                "total": len(cond.conditions or []),
            }
        elif cond.type == "any":
            active_children = [c for c in (cond.conditions or []) if getattr(c, "enabled", True)]
            base_result = bool(active_children) and any(
                self._evaluate_condition(
                    c,
                    key_states=key_states,
                    resolver=resolver,
                    macro_ctx=macro_ctx,
                    path=(path or []) + [f"or[{idx}]"],
                    vars_ctx=vars_state,
                    pixel_cache=pixel_cache,
                )
                for idx, c in enumerate(active_children)
            )
            detail["group"] = {
                "mode": "any",
                "count": len(active_children),
                "total": len(cond.conditions or []),
            }
        elif cond.type == "var":
            name = (cond.var_name or "").strip()
            if not name:
                return False
            expected_raw = cond.var_value_raw if cond.var_value_raw is not None else cond.var_value
            expected = str(expected_raw) if expected_raw is not None else ""
            if resolver:
                try:
                    expected = resolver.resolve(expected, "var")
                except Exception:
                    pass
            actual_value = vars_state.var.get(name) if vars_state else None  # type: ignore[union-attr]
            base_result = False if actual_value is None else str(actual_value) == expected
            if getattr(cond, "var_operator", "eq") == "ne":
                base_result = not base_result
            detail["var"] = {
                "name": name,
                "expected": expected,
                "actual": actual_value,
                "operator": getattr(cond, "var_operator", "eq"),
            }
        elif cond.type == "timer":
            slot = cond.timer_index or 0
            target_val = cond.timer_value
            op = (cond.timer_operator or "ge").lower()
            actual_val = round(self._get_timer_value(slot), 3) if slot else None
            ops = {
                "gt": lambda a, b: a > b,
                "ge": lambda a, b: a >= b,
                "lt": lambda a, b: a < b,
                "le": lambda a, b: a <= b,
                "eq": lambda a, b: a == b,
                "ne": lambda a, b: a != b,
            }
            compare = ops.get(op, ops["ge"])
            if actual_val is None or target_val is None or slot < 1 or slot > 20:
                base_result = False
            else:
                base_result = compare(float(actual_val), float(target_val))
            detail["timer"] = {"slot": slot, "expected": target_val, "actual": actual_val, "operator": op}
        else:
            base_result = False

        final_result = base_result
        if base_result and cond.on_true:
            active_true_children = [c for c in cond.on_true if getattr(c, "enabled", True)]
            if active_true_children:
                final_result = any(
                    self._evaluate_condition(
                        c,
                        key_states=key_states,
                        resolver=resolver,
                        macro_ctx=macro_ctx,
                        path=(path or []) + ["on_true"],
                        vars_ctx=vars_state,
                        pixel_cache=pixel_cache,
                    )
                    for c in active_true_children
                )
        elif (not base_result) and cond.on_false:
            active_false_children = [c for c in cond.on_false if getattr(c, "enabled", True)]
            if active_false_children:
                final_result = any(
                    self._evaluate_condition(
                        c,
                        key_states=key_states,
                        resolver=resolver,
                        macro_ctx=macro_ctx,
                        path=(path or []) + ["on_false"],
                        vars_ctx=vars_state,
                        pixel_cache=pixel_cache,
                    )
                    for c in active_false_children
                )

        if macro_ctx:
            payload: Dict[str, Any] = {
                "type": "condition_result",
                "macro": macro_ctx,
                "name": cond.name,
                "condition_type": cond.type,
                "enabled": getattr(cond, "enabled", True),
                "result": final_result,
                "base_result": base_result,
                "path": path or [],
                "path_text": " > ".join(path or []),
                "timestamp": time.time(),
            }
            payload.update(detail)
            self._emit_event(payload)

        return final_result

    def debug_condition_tree(
        self,
        cond: Condition,
        *,
        key_states: Optional[Dict[str, bool]] = None,
        resolver: Optional[VariableResolver] = None,
        vars_ctx: Optional[MacroVariables] = None,
        path: Optional[List[str]] = None,
    ) -> Dict[str, Any]:
        """
        조건 트리를 주기적으로 평가할 때 사용할 수 있는 디버그용 함수.
        각 노드의 base/최종 결과와 세부 정보를 반환하고, 호출자에게 이벤트를 발생시키지 않는다.
        """
        if cond is None:
            return {
                "cond": None,
                "type": None,
                "name": None,
                "path": path or [],
                "path_text": " > ".join(path or []),
                "result": False,
                "base_result": False,
                "detail": {"error": "조건이 없습니다."},
                "children": [],
                "on_true": [],
                "on_false": [],
            }

        key_states = key_states if key_states is not None else {}
        vars_state = vars_ctx if vars_ctx is not None else getattr(self, "_vars", None)
        current_path = list(path or [])
        cond_enabled = getattr(cond, "enabled", True)
        detail: Dict[str, Any] = {"enabled": cond_enabled}
        children: List[Dict[str, Any]] = []
        true_branch: List[Dict[str, Any]] = []
        false_branch: List[Dict[str, Any]] = []
        base_result = False

        if not cond_enabled:
            return {
                "cond": cond,
                "type": getattr(cond, "type", None),
                "name": getattr(cond, "name", None),
                "path": current_path,
                "path_text": " > ".join(current_path),
                "result": False,
                "base_result": False,
                "detail": detail,
                "children": [],
                "on_true": [],
                "on_false": [],
            }

        try:
            if cond.type == "key":
                if not cond.key:
                    raise ValueError("키가 비어 있습니다.")
                pressed = self._key_pressed(cond.key)
                mode = str(cond.key_mode or "hold").lower()
                prev = key_states.get(cond.key, False)
                key_states[cond.key] = pressed
                if mode in ("press", "down"):
                    base_result = pressed and not prev
                elif mode == "up":
                    base_result = (not pressed) and prev
                elif mode == "released":
                    base_result = not pressed
                else:
                    base_result = pressed
                detail["key"] = {"key": cond.key, "mode": mode, "pressed": pressed, "prev": prev}
            elif cond.type == "pixel":
                region = cond.region
                color = cond.color
                if cond.region_raw is not None and resolver:
                    region = Condition._parse_region(cond.region_raw, resolver)[0]
                if cond.color_raw is not None:
                    if resolver:
                        if cond.color_raw.startswith(("/", "$", "@")):
                            resolved = resolver.resolve(cond.color_raw, "color")
                            try:
                                color = Condition._parse_color(resolved, None)[0]
                            except Exception:
                                color = None
                        else:
                            color = Condition._parse_color(cond.color_raw, resolver)[0]
                    else:
                        color = cond.color
                pattern_name = getattr(cond, "pixel_pattern", None)
                pattern_obj = self._pixel_patterns.get(pattern_name) if pattern_name else None
                if region is None or (color is None and pattern_obj is None):
                    raise ValueError("영역/색상을 확인하세요.")
                region_tuple: Region = tuple(int(v) for v in region)
                color_tuple: Optional[RGB] = tuple(int(c) for c in color) if color is not None else None
                expect_exists = getattr(cond, "pixel_exists", True)
                check = self._pixel_check(
                    region_tuple, color_tuple, cond.tolerance, expect_exists=expect_exists, include_image=True, pattern=pattern_obj
                )
                base_result = bool(check.get("result"))
                detail["pixel"] = {
                    "region": region_tuple,
                    "color": color_tuple,
                    "pattern": pattern_name,
                    "tolerance": cond.tolerance,
                    "expect_exists": expect_exists,
                    "found": check.get("found"),
                    "coord": check.get("coord"),
                    "sample_coord": check.get("sample_coord"),
                    "sample_color": check.get("sample_color"),
                    "pattern_points": check.get("pattern_points"),
                    "pattern_size": check.get("pattern_size"),
                }
            elif cond.type in ("all", "any"):
                active_children: List[Dict[str, Any]] = []
                for idx, child in enumerate(cond.conditions or []):
                    child_res = self.debug_condition_tree(
                        child,
                        key_states=key_states,
                        resolver=resolver,
                        vars_ctx=vars_state,
                        path=current_path + [f"{'and' if cond.type == 'all' else 'or'}[{idx}]"],
                    )
                    children.append(child_res)
                    if getattr(child, "enabled", True):
                        active_children.append(child_res)
                base_result = bool(active_children) and (
                    all(r.get("result") for r in active_children) if cond.type == "all" else any(r.get("result") for r in active_children)
                )
                detail["group"] = {"mode": cond.type, "count": len(active_children), "total": len(cond.conditions or [])}
            elif cond.type == "var":
                name = (cond.var_name or "").strip()
                if not name:
                    raise ValueError("변수 이름이 없습니다.")
                expected_raw = cond.var_value_raw if cond.var_value_raw is not None else cond.var_value
                expected = str(expected_raw) if expected_raw is not None else ""
                if resolver:
                    try:
                        expected = resolver.resolve(expected, "var")
                    except Exception:
                        pass
                actual_value = vars_state.var.get(name) if vars_state else None  # type: ignore[union-attr]
                base_result = False if actual_value is None else str(actual_value) == expected
                if getattr(cond, "var_operator", "eq") == "ne":
                    base_result = not base_result
                detail["var"] = {
                    "name": name,
                    "expected": expected,
                    "actual": actual_value,
                    "operator": getattr(cond, "var_operator", "eq"),
                }
            elif cond.type == "timer":
                slot = cond.timer_index or 0
                target_val = cond.timer_value
                op = (cond.timer_operator or "ge").lower()
                actual_val = round(self._get_timer_value(slot), 3) if slot else None
                ops = {
                    "gt": lambda a, b: a > b,
                    "ge": lambda a, b: a >= b,
                    "lt": lambda a, b: a < b,
                    "le": lambda a, b: a <= b,
                    "eq": lambda a, b: a == b,
                    "ne": lambda a, b: a != b,
                }
                compare = ops.get(op, ops["ge"])
                if actual_val is None or target_val is None or slot < 1 or slot > 20:
                    base_result = False
                else:
                    base_result = compare(float(actual_val), float(target_val))
                detail["timer"] = {"slot": slot, "expected": target_val, "actual": actual_val, "operator": op}
            else:
                base_result = False
        except Exception as exc:
            detail["error"] = str(exc)
            base_result = False

        final_result = base_result
        if base_result and cond.on_true:
            active_true: List[Dict[str, Any]] = []
            for idx, child in enumerate(cond.on_true):
                child_res = self.debug_condition_tree(
                    child,
                    key_states=key_states,
                    resolver=resolver,
                    vars_ctx=vars_state,
                    path=current_path + [f"on_true[{idx}]"],
                )
                true_branch.append(child_res)
                if getattr(child, "enabled", True):
                    active_true.append(child_res)
            if active_true:
                final_result = any(r.get("result") for r in active_true)
        elif (not base_result) and cond.on_false:
            active_false: List[Dict[str, Any]] = []
            for idx, child in enumerate(cond.on_false):
                child_res = self.debug_condition_tree(
                    child,
                    key_states=key_states,
                    resolver=resolver,
                    vars_ctx=vars_state,
                    path=current_path + [f"on_false[{idx}]"],
                )
                false_branch.append(child_res)
                if getattr(child, "enabled", True):
                    active_false.append(child_res)
            if active_false:
                final_result = any(r.get("result") for r in active_false)

        return {
            "cond": cond,
            "type": getattr(cond, "type", None),
            "name": getattr(cond, "name", None),
            "path": current_path,
            "path_text": " > ".join(current_path),
            "result": bool(final_result),
            "base_result": bool(base_result),
            "detail": detail,
            "children": children,
            "on_true": true_branch,
            "on_false": false_branch,
        }

    def _pixel_check(
        self,
        region: Region,
        color: Optional[RGB],
        tolerance: int,
        *,
        expect_exists: bool = True,
        min_count: int = 1,
        include_image: bool = False,
        pixel_cache: Optional[Dict[Tuple[int, int, int, int], Any]] = None,
        pattern: Optional[PixelPattern] = None,
    ) -> Dict[str, Any]:
        x, y, w, h = region
        cache_key = (x, y, w, h)
        arr: Optional[np.ndarray] = self._extract_debug_region(region)

        if arr is None:
            try:
                if pixel_cache is not None and cache_key in pixel_cache:
                    arr = pixel_cache[cache_key]
                else:
                    arr = capture_region_np(region)
                    if pixel_cache is not None:
                        pixel_cache[cache_key] = arr
            except Exception:
                # 폴백: 기존 PIL 경로 유지
                img = capture_region(region).convert("RGB")
                arr = np.asarray(img, dtype=np.uint8)
                if pixel_cache is not None:
                    pixel_cache[cache_key] = arr

        if arr is None:
            arr = np.zeros((max(1, h), max(1, w), 3), dtype=np.uint8)

        found = False
        coord = None
        sample_color: Optional[Tuple[int, int, int]] = None
        match_count = 0
        min_count = max(1, int(min_count))

        if pattern is not None and pattern.points:
            norm_pat = pattern.normalized()
            max_dx = max(p.dx for p in norm_pat.points)
            max_dy = max(p.dy for p in norm_pat.points)
            work_w = w - max_dx
            work_h = h - max_dy
            if work_w > 0 and work_h > 0:
                mask_all = np.ones((work_h, work_w), dtype=bool)
                for pt in norm_pat.points:
                    pt_tol = int(tolerance if tolerance is not None else 0)
                    sub = arr[pt.dy : pt.dy + work_h, pt.dx : pt.dx + work_w]
                    diff = np.abs(sub.astype(np.int16) - np.array(pt.color, dtype=np.int16)).max(axis=2)
                    mask_all &= diff <= pt_tol
                    if not mask_all.any():
                        break
                match_count = int(mask_all.sum()) if mask_all is not None else 0
                found = match_count > 0
                if found:
                    py, px = np.argwhere(mask_all)[0]
                    coord = (x + int(px), y + int(py))
            sample_coord = coord or (x + max(0, w // 2), y + max(0, h // 2))
            try:
                sy = int(sample_coord[1] - y)
                sx = int(sample_coord[0] - x)
                sample_color_raw = arr[sy, sx]
                sample_color = tuple(int(c) for c in sample_color_raw)  # type: ignore[arg-type]
            except Exception:
                sample_color = None
        else:
            target = np.array(color if color is not None else (0, 0, 0), dtype=np.int16)
            diff = np.abs(arr.astype(np.int16) - target).max(axis=2)
            mask = diff <= int(tolerance)
            match_count = int(mask.sum())
            found = match_count > 0
            if found:
                py, px = np.argwhere(mask)[0]
                coord = (x + int(px), y + int(py))
            sample_coord = coord or (x + max(0, w // 2), y + max(0, h // 2))
            try:
                sy = int(sample_coord[1] - y)
                sx = int(sample_coord[0] - x)
                sample_color_raw = arr[sy, sx]
                sample_color = tuple(int(c) for c in sample_color_raw)  # type: ignore[arg-type]
            except Exception:
                sample_color = None

        if expect_exists:
            result = match_count >= min_count
        else:
            result = match_count == 0
        payload = {
            "found": found,
            "result": result,
            "min_count": min_count,
            "match_count": match_count,
            "coord": coord,
            "sample_coord": sample_coord,
            "sample_color": sample_color,
            "expect_exists": expect_exists,
            "pattern": getattr(pattern, "name", None),
            "pattern_points": (
                [(int(pt.dx), int(pt.dy)) for pt in norm_pat.points] if pattern is not None and pattern.points else None
            ),
            "pattern_size": (max_dx + 1, max_dy + 1) if pattern is not None and pattern.points else None,
        }
        if include_image:
            try:
                img = Image.fromarray(arr.astype(np.uint8), mode="RGB")
                buf = io.BytesIO()
                img.save(buf, format="PNG", optimize=True)
                payload["image_png"] = buf.getvalue()
            except Exception:
                pass
        return payload

    def _run_pixel_test(
        self,
        *,
        region: Optional[Region] = None,
        color: Optional[RGB] = None,
        pattern: Optional[str] = None,
        tolerance: Optional[int] = None,
        expect_exists: Optional[bool] = None,
        min_count: Optional[int] = None,
        source: Optional[str] = None,
        label: Optional[str] = None,
    ):
        region_val: Region = tuple(int(v) for v in (region or self._pixel_test_region))
        pattern_name = pattern if pattern is not None else self._pixel_test_pattern
        pat_obj = self._pixel_patterns.get(pattern_name) if pattern_name else None
        color_val: Optional[RGB] = None
        if color is not None:
            color_val = tuple(int(c) for c in color)  # type: ignore[assignment]
        elif pat_obj is None:
            color_val = tuple(int(c) for c in self._pixel_test_color)  # type: ignore[assignment]
        tol_val = int(tolerance if tolerance is not None else self._pixel_test_tolerance)
        expect = self._pixel_test_expect_exists if expect_exists is None else bool(expect_exists)
        min_cnt_val = max(1, int(min_count if min_count is not None else self._pixel_test_min_count))
        ts = time.time()
        try:
            check = self._pixel_check(
                region_val,
                color_val,
                tol_val,
                expect_exists=expect,
                min_count=min_cnt_val,
                pattern=pat_obj,
            )
            payload = {
                "type": "pixel_test",
                "found": check.get("found"),
                "result": check.get("result"),
                "coord": check.get("coord"),
                "sample_coord": check.get("sample_coord"),
                "sample_color": check.get("sample_color"),
                "pattern": pattern_name,
                "expect_exists": expect,
                "min_count": min_cnt_val,
                "match_count": check.get("match_count"),
                "region": region_val,
                "color": color_val,
                "tolerance": tol_val,
                "source": source or "manual",
                "label": label,
                "timestamp": ts,
            }
            self._emit_event(payload)
            self._emit_log(
                f"픽셀 테스트[{payload['source']}]: {'찾음' if check.get('found') else '없음'} ({check.get('coord')})"
            )
        except Exception as exc:
            self._emit_event(
                {
                    "type": "pixel_test",
                    "error": str(exc),
                    "region": region_val,
                    "color": color_val,
                    "pattern": pattern_name,
                    "tolerance": tol_val,
                    "source": source or "manual",
                    "label": label,
                    "timestamp": ts,
                }
            )
            self._emit_log(f"픽셀 테스트 실패: {exc}")
