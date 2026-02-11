"""
간단한 키보드 전송 헬퍼.
Interception 드라이버 기반이며 관리자 권한 + 드라이버 설치가 필요합니다.
"""

import json
import subprocess
import sys
import time
from typing import Any, Dict, List, Optional, Union

from lib.interception import (
    Interception,
    KeyFilter,
    KeyState,
    MapVk,
    Vk,
    is_key_pressed,
    map_virtual_key,
)

try:
    import winreg  # type: ignore
except Exception:  # pragma: no cover - 비윈도우 또는 제한 환경
    winreg = None

try:
    _interception = Interception()
    _interception_error: Exception | None = None
except Exception as exc:  # pragma: no cover - 런타임 환경 의존
    _interception = None
    _interception_error = exc

_keyboard_devices = [d for d in (_interception._context if _interception else []) if d.is_keyboard]
_default_device = _keyboard_devices[0] if _keyboard_devices else None
_mouse_devices = [d for d in (_interception._context if _interception else []) if getattr(d, "is_mouse", False)]
_default_mouse_device = _mouse_devices[0] if _mouse_devices else None

KeyLike = Union[str, int, Vk]
_named_vk = {
    "backspace": Vk.Back,
    "bs": Vk.Back,
    "delete": Vk.Delete,
    "del": Vk.Delete,
    "esc": Vk.Escape,
    "escape": Vk.Escape,
    "caps": Vk.Capital,
    "capslock": Vk.Capital,
    "numlock": Vk.NumLock,
    "scrolllock": Vk.Scroll,
    "apps": Vk.Apps,
    "app": Vk.Apps,
    "home": Vk.Home,
    "pause": Vk.Pause,
    "break": Vk.Pause,
    "pausebreak": Vk.Pause,
    "insert": Vk.Insert,
    "ins": Vk.Insert,
    "end": Vk.End,
    "pageup": Vk.PageUp,
    "pgup": Vk.PageUp,
    "pagedown": Vk.PageDown,
    "pgdn": Vk.PageDown,
    "space": Vk.Space,
    "tab": Vk.Tab,
    "enter": Vk.Enter,
    "return": Vk.Enter,
    "shift": Vk.ShiftKey,
    "ctrl": Vk.ControlKey,
    "alt": Vk.Menu,
    "left": Vk.Left,
    "right": Vk.Right,
    "up": Vk.Up,
    "down": Vk.Down,
    # 윈도우 키
    "win": Vk.LeftWin,
    "lwin": Vk.LeftWin,
    "rwin": Vk.RightWin,
    "super": Vk.LeftWin,
    "meta": Vk.LeftWin,
    "cmd": Vk.LeftWin,
    "command": Vk.LeftWin,
    # OEM/기호 키
    "`": Vk.Oem3,
    "~": Vk.Oem3,
    "tilde": Vk.Oem3,
    "backtick": Vk.Oem3,
    "grave": Vk.Oem3,
    "-": Vk.OemMinus,
    "_": Vk.OemMinus,
    "=": Vk.OemPlus,
    "+": Vk.OemPlus,
    "[": Vk.Oem4,
    "{": Vk.Oem4,
    "]": Vk.Oem6,
    "}": Vk.Oem6,
    "\\": Vk.Oem5,
    "|": Vk.Oem5,
    ";": Vk.Oem1,
    ":": Vk.Oem1,
    "'": Vk.Oem7,
    '"': Vk.Oem7,
    ",": Vk.OemComma,
    "<": Vk.OemComma,
    ".": Vk.OemPeriod,
    ">": Vk.OemPeriod,
    "/": Vk.Oem2,
    "?": Vk.Oem2,
}
# 좌/우 모디파이어 키를 공통 이름으로 매핑해 둔다.
_modifier_aliases = {
    "lshift": "shift",
    "rshift": "shift",
    "leftshift": "shift",
    "rightshift": "shift",
    "lctrl": "ctrl",
    "rctrl": "ctrl",
    "leftctrl": "ctrl",
    "rightctrl": "ctrl",
    "lcontrol": "ctrl",
    "rcontrol": "ctrl",
    "lalt": "alt",
    "ralt": "alt",
    "leftalt": "alt",
    "rightalt": "alt",
    "win": "win",
    "lwin": "win",
    "rwin": "win",
    "leftwin": "win",
    "rightwin": "win",
    "super": "win",
    "meta": "win",
    "cmd": "win",
    "command": "win",
    "windows": "win",
}
# 기능키 매핑
for i in range(1, 25):
    _named_vk[f"f{i}"] = Vk(111 + i)  # Vk.F1 == 112
# 마우스 버튼 매핑
_named_vk.update(
    {
        "mouse1": Vk.LeftButton,
        "lmb": Vk.LeftButton,
        "mouse_left": Vk.LeftButton,
        "mouse2": Vk.RightButton,
        "rmb": Vk.RightButton,
        "mouse_right": Vk.RightButton,
        "mouse3": Vk.MiddleButton,
        "mmb": Vk.MiddleButton,
        "mouse_middle": Vk.MiddleButton,
        "wheel": Vk.MiddleButton,
        "mouse4": Vk.XButton1,
        "mb4": Vk.XButton1,
        "x1": Vk.XButton1,
        "mouse5": Vk.XButton2,
        "mb5": Vk.XButton2,
        "x2": Vk.XButton2,
    }
)


def interception_available() -> bool:
    """Interception 컨텍스트가 준비되었는지 여부."""
    return _interception is not None


def interception_error() -> Exception | None:
    """Interception 초기화 실패 시 예외를 반환."""
    return _interception_error


_friendly_cache: dict[str, Any] = {"ts": 0.0, "value": {}}


def _friendly_name_map() -> dict[str, str]:
    """
    현재 연결된 키보드/마우스의 FriendlyName을 PnP에서 조회한다.
    실패하면 빈 매핑을 반환한다.
    """
    now = time.time()
    # Cache for 30s even when empty to avoid repeated slow PowerShell calls.
    if now - _friendly_cache["ts"] < 30:
        return dict(_friendly_cache["value"])
    if not sys.platform.startswith("win"):
        _friendly_cache["value"] = {}
        _friendly_cache["ts"] = now
        return {}
    try:
        cmd = [
            "powershell",
            "-NoProfile",
            "-Command",
            "(Get-PnpDevice -Class Keyboard,Mouse) | Select-Object InstanceId,FriendlyName,Name | ConvertTo-Json -Depth 3",
        ]
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=0.2)
        if proc.returncode != 0 or not proc.stdout:
            _friendly_cache["ts"] = now
            return dict(_friendly_cache["value"])
        data = json.loads(proc.stdout)
        devices = data if isinstance(data, list) else [data]
        mapping: dict[str, str] = {}
        for dev in devices:
            if not isinstance(dev, dict):
                continue
            inst = str(dev.get("InstanceId") or dev.get("InstanceID") or "").upper()
            name = dev.get("FriendlyName") or dev.get("Name") or ""
            if inst:
                mapping[inst] = str(name)
        _friendly_cache["value"] = mapping
        _friendly_cache["ts"] = time.time()
        return dict(mapping)
    except Exception:
        _friendly_cache["ts"] = now
        return dict(_friendly_cache["value"])


def _kbdclass_enum() -> list[str]:
    """kbdclass Enum 키에서 장치 InstanceId를 순서대로 가져온다."""
    if not sys.platform.startswith("win") or not winreg:
        return []
    path = r"SYSTEM\CurrentControlSet\Services\kbdclass\Enum"
    ids: list[str] = []
    try:
        key = winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE, path)
        idx = 0
        while True:
            try:
                name, val, _ = winreg.EnumValue(key, idx)
            except OSError:
                break
            if str(name).isdigit():
                try:
                    ids.append(str(val))
                except Exception:
                    pass
            idx += 1
        winreg.CloseKey(key)
    except Exception:
        return ids
    return ids


def _mouclass_enum() -> list[str]:
    """mouclass Enum 키에서 장치 InstanceId를 순서대로 가져온다."""
    if not sys.platform.startswith("win") or not winreg:
        return []
    path = r"SYSTEM\\CurrentControlSet\\Services\\mouclass\\Enum"
    ids: list[str] = []
    try:
        key = winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE, path)
        idx = 0
        while True:
            try:
                name, val, _ = winreg.EnumValue(key, idx)
            except OSError:
                break
            if str(name).isdigit():
                try:
                    ids.append(str(val))
                except Exception:
                    pass
            idx += 1
        winreg.CloseKey(key)
    except Exception:
        return ids
    return ids


def vk_from_key(key: KeyLike) -> int:
    """문자/가상키/F-키 문자열을 Windows VK 코드로 변환한다."""
    if isinstance(key, int):
        return int(key)
    if isinstance(key, Vk):
        return int(key)
    if isinstance(key, str):
        low = key.lower()
        low = _modifier_aliases.get(low, low)
        if low in _named_vk:
            return int(_named_vk[low])
        if len(key) == 1:
            return ord(key.upper())
    raise TypeError("key must be Vk, int(vk), 1-char string (예: 'r'), or 'esc'.")


def _refresh_keyboard_devices():
    global _keyboard_devices, _default_device
    if not _interception:
        _keyboard_devices = []
        _default_device = None
        return
    _keyboard_devices = [d for d in _interception._context if getattr(d, "is_keyboard", False)]
    if _default_device not in _keyboard_devices:
        _default_device = _keyboard_devices[0] if _keyboard_devices else None


def _refresh_mouse_devices():
    global _mouse_devices, _default_mouse_device
    if not _interception:
        _mouse_devices = []
        _default_mouse_device = None
        return
    _mouse_devices = [d for d in _interception._context if getattr(d, "is_mouse", False)]
    if _default_mouse_device not in _mouse_devices:
        _default_mouse_device = _mouse_devices[0] if _mouse_devices else None


def _safe_hardware_id(dev) -> str:
    try:
        return dev.get_hardware_id() or ""
    except Exception:
        return ""


def list_keyboard_devices(*, friendly: bool = True) -> List[Dict[str, Any]]:
    """Interception이 감지한 키보드 장치 목록을 반환합니다.

    friendly=False이면 FriendlyName 조회를 건너뛰어 속도를 우선한다.
    """
    if not _interception:
        return []
    _refresh_keyboard_devices()
    name_map = _friendly_name_map() if friendly else {}
    enum_ids = _kbdclass_enum()
    kb_idx = 0
    devices: List[Dict[str, Any]] = []
    for idx, dev in enumerate(_interception._context if _interception else [], start=1):
        if not getattr(dev, "is_keyboard", False):
            continue
        hwid = _safe_hardware_id(dev)
        if not hwid and 0 <= kb_idx < len(enum_ids):
            hwid = enum_ids[kb_idx]
        if not hwid and len(enum_ids) == 1:
            hwid = enum_ids[0]
        kb_idx += 1
        if not hwid:
            hwid = f"UNKNOWN_KB_{idx}"
        friendly = name_map.get(hwid.upper()) or name_map.get(hwid) or ""
        if not friendly and hwid.startswith("UNKNOWN"):
            friendly = hwid
        devices.append({"id": idx, "hardware_id": hwid, "friendly_name": friendly, "is_default": dev is _default_device})
    return devices


def list_interception_devices(*, friendly: bool = True) -> List[Dict[str, Any]]:
    """
    Interception이 감지한 키보드/마우스 장치 목록을 반환합니다.
    friendly=False이면 FriendlyName 조회를 건너뛰어 속도를 우선한다.
    """
    if not _interception:
        return []
    _refresh_keyboard_devices()
    _refresh_mouse_devices()
    name_map = _friendly_name_map() if friendly else {}
    enum_ids = _kbdclass_enum()
    mouse_enum_ids = _mouclass_enum()
    kb_idx = 0
    mouse_idx = 0
    devices: List[Dict[str, Any]] = []
    for idx, dev in enumerate(_interception._context if _interception else [], start=1):
        hwid = _safe_hardware_id(dev)
        if not hwid and getattr(dev, "is_keyboard", False) and 0 <= kb_idx < len(enum_ids):
            hwid = enum_ids[kb_idx]
        if getattr(dev, "is_keyboard", False):
            kb_idx += 1
        if not hwid and getattr(dev, "is_keyboard", False) and len(enum_ids) == 1:
            hwid = enum_ids[0]
        if not hwid and getattr(dev, "is_mouse", False) and 0 <= mouse_idx < len(mouse_enum_ids):
            hwid = mouse_enum_ids[mouse_idx]
        if getattr(dev, "is_mouse", False):
            mouse_idx += 1
        if not hwid and getattr(dev, "is_mouse", False) and len(mouse_enum_ids) == 1:
            hwid = mouse_enum_ids[0]
        if not hwid:
            hwid = f"UNKNOWN_DEV_{idx}"
        friendly = name_map.get(hwid.upper()) or name_map.get(hwid) or ""
        if not friendly and hwid.startswith("UNKNOWN"):
            friendly = hwid
        is_kb = getattr(dev, "is_keyboard", False)
        is_mouse = getattr(dev, "is_mouse", False)
        devices.append(
            {
                "id": idx,
                "hardware_id": hwid,
                "friendly_name": friendly,
                "is_default": (dev is _default_device) if is_kb else (dev is _default_mouse_device),
                "is_keyboard": is_kb,
                "is_mouse": is_mouse,
                "type": "키보드" if is_kb else ("마우스" if is_mouse else "장치"),
            }
        )
    return devices


def _resolve_keyboard_device(device_id: Optional[int] = None, hardware_id: Optional[str] = None):
    devices = list_keyboard_devices()
    selected = None
    matched_by = None
    hw_lower = (hardware_id or "").lower()

    if hw_lower:
        for info in devices:
            if info["hardware_id"] and info["hardware_id"].lower() == hw_lower:
                selected = info
                matched_by = "hardware_id"
                break

    if selected is None and device_id:
        for info in devices:
            if info["id"] == device_id:
                selected = info
                matched_by = "device_id"
                break

    if selected is None and hw_lower:
        for info in devices:
            if info["hardware_id"] and hw_lower in info["hardware_id"].lower():
                selected = info
                matched_by = "hardware_id_partial"
                break

    if selected is None and devices:
        selected = devices[0]
        matched_by = "default"

    return selected, matched_by, devices


def select_keyboard_device(device_id: Optional[int] = None, hardware_id: Optional[str] = None) -> Dict[str, Any]:
    """기본으로 사용할 키보드 장치를 선택해 `_default_device`로 설정."""
    global _default_device
    if not _interception:
        return {
            "id": None,
            "hardware_id": None,
            "matched_by": None,
            "total": 0,
            "friendly_name": None,
            "error": str(_interception_error) if _interception_error else "Interception unavailable",
        }
    selected, matched_by, devices = _resolve_keyboard_device(device_id, hardware_id)
    total = len(devices)
    friendly = selected.get("friendly_name") if selected else None
    if selected and _interception:
        try:
            _default_device = _interception._context[selected["id"] - 1]
        except Exception:
            _default_device = None
    else:
        _default_device = None
    return {
        "id": selected["id"] if selected else None,
        "hardware_id": selected["hardware_id"] if selected else None,
        "friendly_name": friendly,
        "matched_by": matched_by if selected else None,
        "total": total,
    }


def list_mouse_devices(*, friendly: bool = True) -> List[Dict[str, Any]]:
    """Interception이 감지한 마우스 장치 목록을 반환합니다."""
    if not _interception:
        return []
    _refresh_mouse_devices()
    name_map = _friendly_name_map() if friendly else {}
    enum_ids = _mouclass_enum()
    mouse_idx = 0
    devices: List[Dict[str, Any]] = []
    for idx, dev in enumerate(_interception._context if _interception else [], start=1):
        if not getattr(dev, "is_mouse", False):
            continue
        hwid = _safe_hardware_id(dev)
        if not hwid and 0 <= mouse_idx < len(enum_ids):
            hwid = enum_ids[mouse_idx]
        if not hwid and len(enum_ids) == 1:
            hwid = enum_ids[0]
        mouse_idx += 1
        if not hwid:
            hwid = f"UNKNOWN_MS_{idx}"
        friendly = name_map.get(hwid.upper()) or name_map.get(hwid) or ""
        if not friendly and hwid.startswith("UNKNOWN"):
            friendly = hwid
        devices.append({"id": idx, "hardware_id": hwid, "friendly_name": friendly, "is_default": dev is _default_mouse_device})
    return devices


def _resolve_mouse_device(device_id: Optional[int] = None, hardware_id: Optional[str] = None):
    devices = list_mouse_devices()
    selected = None
    matched_by = None
    hw_lower = (hardware_id or "").lower()

    if hw_lower:
        for info in devices:
            if info["hardware_id"] and info["hardware_id"].lower() == hw_lower:
                selected = info
                matched_by = "hardware_id"
                break

    if selected is None and device_id:
        for info in devices:
            if info["id"] == device_id:
                selected = info
                matched_by = "device_id"
                break

    if selected is None and hw_lower:
        for info in devices:
            if info["hardware_id"] and hw_lower in info["hardware_id"].lower():
                selected = info
                matched_by = "hardware_id_partial"
                break

    if selected is None and devices:
        selected = devices[0]
        matched_by = "default"

    return selected, matched_by, devices


def select_mouse_device(device_id: Optional[int] = None, hardware_id: Optional[str] = None) -> Dict[str, Any]:
    """기본으로 사용할 마우스 장치를 선택해 `_default_mouse_device`로 설정."""
    global _default_mouse_device
    if not _interception:
        return {
            "id": None,
            "hardware_id": None,
            "matched_by": None,
            "total": 0,
            "friendly_name": None,
            "error": str(_interception_error) if _interception_error else "Interception unavailable",
        }
    selected, matched_by, devices = _resolve_mouse_device(device_id, hardware_id)
    total = len(devices)
    friendly = selected.get("friendly_name") if selected else None
    if selected and _interception:
        try:
            _default_mouse_device = _interception._context[selected["id"] - 1]
        except Exception:
            _default_mouse_device = None
    else:
        _default_mouse_device = None
    return {
        "id": selected["id"] if selected else None,
        "hardware_id": selected["hardware_id"] if selected else None,
        "friendly_name": friendly,
        "matched_by": matched_by if selected else None,
        "total": total,
    }


def get_default_keyboard_info(*, friendly: bool = True) -> Dict[str, Any]:
    """현재 기본 장치의 id/hardware id를 반환합니다."""
    _refresh_keyboard_devices()
    if not _default_device:
        return {"id": None, "hardware_id": None, "friendly_name": None}
    try:
        idx = _interception._context.index(_default_device) + 1
    except ValueError:
        idx = None
    hwid = _safe_hardware_id(_default_device)
    names = _friendly_name_map() if friendly else {}
    friendly_name = names.get(hwid.upper()) or names.get(hwid) or None
    return {"id": idx, "hardware_id": hwid, "friendly_name": friendly_name}


def get_default_mouse_info(*, friendly: bool = True) -> Dict[str, Any]:
    """현재 기본 마우스 장치의 id/hardware id를 반환합니다."""
    _refresh_mouse_devices()
    if not _default_mouse_device:
        return {"id": None, "hardware_id": None, "friendly_name": None}
    try:
        idx = _interception._context.index(_default_mouse_device) + 1
    except ValueError:
        idx = None
    hwid = _safe_hardware_id(_default_mouse_device)
    if not hwid:
        hwid = f"UNKNOWN_MS_{idx or 0}"
    names = _friendly_name_map() if friendly else {}
    friendly_name = names.get(hwid.upper()) or names.get(hwid) or None
    return {"id": idx, "hardware_id": hwid, "friendly_name": friendly_name}


def get_default_mouse_device():
    """현재 설정된 기본 마우스 장치 객체를 반환한다."""
    _refresh_mouse_devices()
    return _default_mouse_device


def send_key_on_device(key: KeyLike, *, device_id: Optional[int] = None, hardware_id: Optional[str] = None):
    """지정한 장치(또는 기본값)로 테스트 키를 전송합니다."""
    if not _interception:
        raise RuntimeError("Interception driver is not available.")
    selected, _, _ = _resolve_keyboard_device(device_id, hardware_id)
    device = _interception._context[selected["id"] - 1] if selected else None
    key_press(key, device=device)


_listeners: list[tuple[int, callable]] = []


def _require_device(device=None):
    if not _interception:
        raise RuntimeError("Interception driver is not available.")
    dev = device or _default_device
    if dev is None:
        raise RuntimeError("No keyboard device found. Is the Interception driver installed and running as admin?")
    return dev


def _vk_code(key: KeyLike) -> int:
    if isinstance(key, Vk):
        return int(key)
    if isinstance(key, int):
        return key
    if isinstance(key, str):
        low = _modifier_aliases.get(key.lower(), key.lower())
        # 명시 매핑이 우선(길이와 무관)
        if low in _named_vk:
            return int(_named_vk[low])
        if len(key) == 1:
            return ord(key.upper())
    raise TypeError("key must be Vk, int(vk), 1-char string (e.g. 'r'), or 'esc'.")


def _scan_code(key: KeyLike) -> int:
    return map_virtual_key(_vk_code(key), MapVk.VkToSc)


def get_interception() -> Interception | None:
    """Return the shared Interception instance used for keyboard IO."""
    return _interception


def _send(key: KeyLike, state: KeyState, *, device=None, info: int = 0):
    dev = _require_device(device)
    vk = _vk_code(key)
    sc = map_virtual_key(vk, MapVk.VkToSc)

    stroke = dev.stroke.__class__()  # KeyStroke
    stroke.code = sc
    stroke.state = state
    stroke.info = info
    stroke.reserved = 0
    stroke.id = 0
    dev.send(stroke)


def get_keystate(key: KeyLike, async_: bool = True) -> bool:
    """
    현재 키가 눌려있는지 반환합니다.
    key는 가상 키 코드, 스캔 코드, 문자 중 하나를 받을 수 있습니다.
    """
    if isinstance(key, int):
        # 스캔 코드(int)도 받을 수 있도록 우선 ScToVk 변환을 시도합니다.
        vk = map_virtual_key(key, MapVk.ScToVk) or key
    else:
        vk = _vk_code(key)
    return is_key_pressed(int(vk), async_=async_)


def to_scan_code(key: KeyLike) -> int:
    """주어진 키를 스캔 코드로 변환합니다."""
    return map_virtual_key(_vk_code(key), MapVk.VkToSc)


def key_down(key: KeyLike, *, device=None, info: int = 0):
    """지정 키를 누른 상태로 보냅니다."""
    _send(key, KeyState.Down, device=device, info=info)


def key_up(key: KeyLike, *, device=None, info: int = 0):
    """지정 키를 뗀 상태로 보냅니다."""
    _send(key, KeyState.Up, device=device, info=info)


def key_press(key: KeyLike, *, device=None, info: int = 0):
    """지정 키를 눌렀다가 뗍니다."""
    key_down(key, device=device, info=info)
    key_up(key, device=device, info=info)


def key(key: KeyLike, state: Optional[str] = None, *, device=None, info: int = 0):
    """
    간단 라우터: state가 'down'이면 key_down, 'up'이면 key_up,
    그 외(또는 None)는 press 동작.
    """
    if state is None or state.lower() == "press":
        key_press(key, device=device, info=info)
    elif state.lower() == "down":
        key_down(key, device=device, info=info)
    elif state.lower() == "up":
        key_up(key, device=device, info=info)
    else:
        raise ValueError("state must be one of: None/'press', 'down', 'up'")


def listen_and_press(trigger: KeyLike, target: KeyLike, *, exit_key: KeyLike = "esc"):
    """
    간단 리스너: trigger 키를 누르면 target 키를 한번 press. exit_key 누르면 종료.
    """
    _listeners.clear()

    def handler(device, stroke):
        key_press(target, device=device)

    listen(trigger, handler)
    run_listeners(exit_keys=(exit_key,))


def listen(trigger: KeyLike, callback):
    """
    trigger 키(Down 시)와 콜백을 등록합니다.
    콜백 시그니처: callback(device, stroke)
    """
    sc = _scan_code(trigger)
    _listeners.append((sc, callback))


def clear_listeners():
    _listeners.clear()


def run_listeners(*, exit_keys=("esc",)):
    inter = _interception
    inter.set_keyboard_filter(KeyFilter.All)
    exit_scs = {_scan_code(k) for k in exit_keys}

    while True:
        device = inter.wait_receive()
        if not device:
            continue

        stroke = device.stroke
        is_down = stroke.state == KeyState.Down

        if device.is_keyboard:
            for sc, cb in _listeners:
                if stroke.code == sc:
                    cb(device, stroke)
            if is_down and stroke.code in exit_scs:
                device.send()
                break

        device.send()
