from __future__ import annotations

import ctypes
import random
import sys
import time
from dataclasses import dataclass, field
from typing import Dict, List, Literal, Optional

from lib import keyboard
from lib.interception import MouseState

# SendInput 설정
user32 = ctypes.windll.user32 if sys.platform.startswith("win") else None
INPUT_KEYBOARD = 1
KEYEVENTF_KEYUP = 0x0002
KEYEVENTF_SCANCODE = 0x0008
MOUSEEVENTF_MOVE = 0x0001
MOUSEEVENTF_LEFTDOWN = 0x0002
MOUSEEVENTF_LEFTUP = 0x0004
MOUSEEVENTF_RIGHTDOWN = 0x0008
MOUSEEVENTF_RIGHTUP = 0x0010
MOUSEEVENTF_MIDDLEDOWN = 0x0020
MOUSEEVENTF_MIDDLEUP = 0x0040
MOUSEEVENTF_XDOWN = 0x0080
MOUSEEVENTF_XUP = 0x0100
MOUSEEVENTF_WHEEL = 0x0800
MOUSEEVENTF_HWHEEL = 0x01000
MOUSEEVENTF_ABSOLUTE = 0x8000
XBUTTON1 = 0x0001
XBUTTON2 = 0x0002


class KEYBDINPUT(ctypes.Structure):
    _fields_ = [
        ("wVk", ctypes.c_ushort),
        ("wScan", ctypes.c_ushort),
        ("dwFlags", ctypes.c_uint),
        ("time", ctypes.c_uint),
        ("dwExtraInfo", ctypes.c_ulonglong),
    ]


class INPUT(ctypes.Structure):
    _fields_ = [("type", ctypes.c_uint), ("ki", KEYBDINPUT)]


def _is_admin() -> bool:
    if not sys.platform.startswith("win"):
        return True
    try:
        return bool(ctypes.windll.shell32.IsUserAnAdmin())
    except Exception:
        return False


@dataclass
class KeyDelayConfig:
    press_delay_ms: int = 0
    press_delay_random: bool = False
    press_delay_min_ms: int = 0
    press_delay_max_ms: int = 0
    gap_delay_ms: int = 0
    gap_delay_random: bool = False
    gap_delay_min_ms: int = 0
    gap_delay_max_ms: int = 0

    def _resolve_random(self, enabled: bool, value: int, low: int, high: int) -> int:
        if not enabled:
            return max(0, int(value or 0))
        lo, hi = sorted((int(low or 0), int(high or 0)))
        lo = max(0, lo)
        hi = max(0, hi)
        if hi < lo:
            hi = lo
        return random.randint(lo, hi)

    def resolved_press_delay(self) -> int:
        return self._resolve_random(self.press_delay_random, self.press_delay_ms, self.press_delay_min_ms, self.press_delay_max_ms)

    def resolved_gap_delay(self) -> int:
        return self._resolve_random(self.gap_delay_random, self.gap_delay_ms, self.gap_delay_min_ms, self.gap_delay_max_ms)

    @classmethod
    def from_dict(cls, data: Dict | None) -> "KeyDelayConfig":
        data = data or {}
        return cls(
            press_delay_ms=int(data.get("press_delay_ms", 0) or 0),
            press_delay_random=bool(data.get("press_delay_random", False)),
            press_delay_min_ms=int(data.get("press_delay_min_ms", 0) or 0),
            press_delay_max_ms=int(data.get("press_delay_max_ms", 0) or 0),
            gap_delay_ms=int(data.get("gap_delay_ms", 0) or 0),
            gap_delay_random=bool(data.get("gap_delay_random", False)),
            gap_delay_min_ms=int(data.get("gap_delay_min_ms", 0) or 0),
            gap_delay_max_ms=int(data.get("gap_delay_max_ms", 0) or 0),
        )

    def to_dict(self) -> Dict[str, int | bool]:
        return {
            "press_delay_ms": int(self.press_delay_ms),
            "press_delay_random": bool(self.press_delay_random),
            "press_delay_min_ms": int(self.press_delay_min_ms),
            "press_delay_max_ms": int(self.press_delay_max_ms),
            "gap_delay_ms": int(self.gap_delay_ms),
            "gap_delay_random": bool(self.gap_delay_random),
            "gap_delay_min_ms": int(self.gap_delay_min_ms),
            "gap_delay_max_ms": int(self.gap_delay_max_ms),
        }


@dataclass
class KeyboardBackendStatus:
    mode: Literal["hardware", "software"]
    available: bool
    installed: bool = True
    admin: Optional[bool] = None
    reboot_required: bool = False
    message: str = ""
    current_device: Optional[Dict] = None
    devices: List[Dict] = field(default_factory=list)
    current_mouse: Optional[Dict] = None
    mouse_devices: List[Dict] = field(default_factory=list)

    def to_dict(self) -> Dict:
        return {
            "mode": self.mode,
            "available": self.available,
            "installed": self.installed,
            "admin": self.admin,
            "reboot_required": self.reboot_required,
            "message": self.message,
            "current_device": self.current_device,
            "devices": self.devices,
            "current_mouse": self.current_mouse,
            "mouse_devices": self.mouse_devices,
        }


class KeyboardBackend:
    mode: Literal["hardware", "software"]
    name: str

    def status(self, *, friendly: bool = True) -> KeyboardBackendStatus:
        raise NotImplementedError

    def set_device(self, device_id: Optional[int] = None, hardware_id: Optional[str] = None) -> KeyboardBackendStatus:
        raise NotImplementedError

    def current_device(self) -> Optional[Dict]:
        raise NotImplementedError

    def set_mouse_device(self, device_id: Optional[int] = None, hardware_id: Optional[str] = None) -> KeyboardBackendStatus:
        raise NotImplementedError

    def current_mouse(self) -> Optional[Dict]:
        raise NotImplementedError

    def press(self, key: str):
        raise NotImplementedError

    def down(self, key: str):
        raise NotImplementedError

    def up(self, key: str):
        raise NotImplementedError

    def mouse_down(self, button: str, *, x: Optional[int] = None, y: Optional[int] = None):
        raise NotImplementedError

    def mouse_up(self, button: str, *, x: Optional[int] = None, y: Optional[int] = None):
        raise NotImplementedError

    def mouse_click(self, button: str, *, hold_ms: int = 0, x: Optional[int] = None, y: Optional[int] = None):
        raise NotImplementedError

    def mouse_move(self, x: int, y: int):
        raise NotImplementedError

    def test(self, key: str):
        """전송 테스트를 수행한다."""
        self.press(key)


def _sendinput_key(vk: int, *, is_down: bool = True):
    if user32 is None:
        raise RuntimeError("SendInput is unavailable on this platform.")
    scan = user32.MapVirtualKeyW(int(vk), 0)
    flags = KEYEVENTF_SCANCODE
    if not is_down:
        flags |= KEYEVENTF_KEYUP
    ki = KEYBDINPUT(wVk=int(vk), wScan=int(scan), dwFlags=flags, time=0, dwExtraInfo=0)
    inp = INPUT(type=INPUT_KEYBOARD, ki=ki)
    sent = user32.SendInput(1, ctypes.byref(inp), ctypes.sizeof(INPUT))
    if sent != 1:
        raise RuntimeError("SendInput failed")


def _canonical_button(button: str | None) -> str:
    btn = (button or "left").strip().lower()
    mapping = {
        "mouse1": "left",
        "lmb": "left",
        "mouse_left": "left",
        "left": "left",
        "mouse2": "right",
        "rmb": "right",
        "mouse_right": "right",
        "right": "right",
        "mouse3": "middle",
        "mmb": "middle",
        "mouse_middle": "middle",
        "middle": "middle",
        "wheel": "middle",
        "mouse4": "x1",
        "x1": "x1",
        "mouse5": "x2",
        "x2": "x2",
    }
    return mapping.get(btn, btn)


def _mouse_flags(button: str, *, is_down: bool) -> tuple[int, int]:
    btn = _canonical_button(button)
    if btn == "left":
        return (MOUSEEVENTF_LEFTDOWN if is_down else MOUSEEVENTF_LEFTUP, 0)
    if btn == "right":
        return (MOUSEEVENTF_RIGHTDOWN if is_down else MOUSEEVENTF_RIGHTUP, 0)
    if btn == "middle":
        return (MOUSEEVENTF_MIDDLEDOWN if is_down else MOUSEEVENTF_MIDDLEUP, 0)
    if btn == "x1":
        return (MOUSEEVENTF_XDOWN if is_down else MOUSEEVENTF_XUP, XBUTTON1)
    if btn == "x2":
        return (MOUSEEVENTF_XDOWN if is_down else MOUSEEVENTF_XUP, XBUTTON2)
    raise ValueError(f"Unknown mouse button: {button}")


def _mouse_state(button: str, *, is_down: bool) -> tuple[int, int]:
    btn = _canonical_button(button)
    middle_down = getattr(MouseState, "MiddleButtonDown", getattr(MouseState, "MuddleButtonDown", None))
    if btn == "left":
        return (MouseState.LeftButtonDown if is_down else MouseState.LeftButtonUp, 0)
    if btn == "right":
        return (MouseState.RightButtonDown if is_down else MouseState.RightButtonUp, 0)
    if btn == "middle":
        if not middle_down:
            raise ValueError("MouseState.MiddleButtonDown is unavailable")
        return (middle_down if is_down else MouseState.MiddleButtonUp, 0)
    if btn == "x1":
        return (MouseState.XButton1Down if is_down else MouseState.XButton1Up, XBUTTON1)
    if btn == "x2":
        return (MouseState.XButton2Down if is_down else MouseState.XButton2Up, XBUTTON2)
    raise ValueError(f"Unknown mouse button: {button}")


def _send_mouse_button(button: str, *, is_down: bool, x: Optional[int] = None, y: Optional[int] = None):
    if user32 is None:
        raise RuntimeError("SendInput(mouse_event) is unavailable on this platform.")
    if x is not None and y is not None:
        user32.SetCursorPos(int(x), int(y))
    flag, data = _mouse_flags(button, is_down=is_down)
    user32.mouse_event(flag, 0, 0, data, 0)


def _send_mouse_move(x: int, y: int):
    if user32 is None:
        raise RuntimeError("SendInput(mouse_event) is unavailable on this platform.")
    user32.SetCursorPos(int(x), int(y))


def _send_mouse_click(button: str, *, hold_ms: int = 0, x: Optional[int] = None, y: Optional[int] = None):
    _send_mouse_button(button, is_down=True, x=x, y=y)
    if hold_ms > 0:
        time.sleep(max(0.0, hold_ms) / 1000.0)
    _send_mouse_button(button, is_down=False)


class SoftwareBackend(KeyboardBackend):
    mode: Literal["software", "hardware"] = "software"

    def __init__(self):
        self.name = "소프트웨어 (SendInput)"

    def status(self, *, friendly: bool = True) -> KeyboardBackendStatus:
        available = sys.platform.startswith("win") and user32 is not None
        msg = "" if available else "Windows SendInput를 사용할 수 없습니다."
        return KeyboardBackendStatus(
            mode="software",
            available=available,
            installed=available,
            admin=None,
            reboot_required=False,
            message=msg,
            current_device=None,
            devices=[],
            current_mouse=None,
            mouse_devices=[],
        )

    def set_device(self, device_id: Optional[int] = None, hardware_id: Optional[str] = None) -> KeyboardBackendStatus:
        return self.status()

    def current_device(self) -> Optional[Dict]:
        return None

    def set_mouse_device(self, device_id: Optional[int] = None, hardware_id: Optional[str] = None) -> KeyboardBackendStatus:
        return self.status()

    def current_mouse(self) -> Optional[Dict]:
        return None

    def press(self, key: str):
        vk = keyboard.vk_from_key(key)
        _sendinput_key(vk, is_down=True)
        _sendinput_key(vk, is_down=False)

    def down(self, key: str):
        vk = keyboard.vk_from_key(key)
        _sendinput_key(vk, is_down=True)

    def up(self, key: str):
        vk = keyboard.vk_from_key(key)
        _sendinput_key(vk, is_down=False)

    def mouse_down(self, button: str, *, x: Optional[int] = None, y: Optional[int] = None):
        _send_mouse_button(button, is_down=True, x=x, y=y)

    def mouse_up(self, button: str, *, x: Optional[int] = None, y: Optional[int] = None):
        _send_mouse_button(button, is_down=False, x=x, y=y)

    def mouse_click(self, button: str, *, hold_ms: int = 0, x: Optional[int] = None, y: Optional[int] = None):
        _send_mouse_click(button, hold_ms=hold_ms, x=x, y=y)

    def mouse_move(self, x: int, y: int):
        _send_mouse_move(x, y)


class InterceptionBackend(KeyboardBackend):
    mode: Literal["hardware", "software"] = "hardware"

    def __init__(self, *, is_admin: Optional[bool] = None):
        self.name = "하드웨어 (Interception)"
        self.is_admin = is_admin if is_admin is not None else _is_admin()
        self._mouse_dev = None

    def _installed(self) -> bool:
        return keyboard.interception_available()

    def status(self, *, friendly: bool = True) -> KeyboardBackendStatus:
        installed = self._installed()
        admin_ok = self.is_admin if self.is_admin is not None else _is_admin()
        devices: List[Dict] = []
        current = None
        mouse_devices: List[Dict] = []
        current_mouse = None
        available = False
        message = ""
        if installed:
            try:
                devices = keyboard.list_interception_devices(friendly=friendly)
                current = keyboard.get_default_keyboard_info(friendly=friendly)
                mouse_devices = keyboard.list_mouse_devices(friendly=friendly)
                current_mouse = keyboard.get_default_mouse_info(friendly=friendly)
                available = admin_ok and bool(devices)
                if not admin_ok:
                    message = "관리자 권한이 필요합니다."
                elif not devices:
                    message = "Interception 입력 장치를 찾을 수 없습니다."
            except Exception as exc:  # pragma: no cover - 환경 의존
                message = str(exc)
                available = False
        else:
            err = keyboard.interception_error()
            message = f"Interception 미설치: {err}" if err else "Interception 미설치"
        return KeyboardBackendStatus(
            mode="hardware",
            available=available,
            installed=installed,
            admin=admin_ok,
            reboot_required=False,
            message=message,
            current_device=current,
            devices=devices,
            current_mouse=current_mouse,
            mouse_devices=mouse_devices,
        )

    def set_device(self, device_id: Optional[int] = None, hardware_id: Optional[str] = None) -> KeyboardBackendStatus:
        status = self.status()
        if not status.installed:
            return status
        try:
            info = keyboard.select_keyboard_device(device_id=device_id, hardware_id=hardware_id)
            status.current_device = {"id": info.get("id"), "hardware_id": info.get("hardware_id"), "friendly_name": info.get("friendly_name")}
            status.devices = keyboard.list_interception_devices()
            status.mouse_devices = keyboard.list_mouse_devices()
            status.current_mouse = keyboard.get_default_mouse_info()
            status.available = True
            status.message = ""
        except Exception as exc:
            status.available = False
            status.message = str(exc)
        return status

    def current_device(self) -> Optional[Dict]:
        if not self._installed():
            return None
        try:
            return keyboard.get_default_keyboard_info()
        except Exception:
            return None

    def set_mouse_device(self, device_id: Optional[int] = None, hardware_id: Optional[str] = None) -> KeyboardBackendStatus:
        status = self.status()
        if not status.installed:
            return status
        try:
            info = keyboard.select_mouse_device(device_id=device_id, hardware_id=hardware_id)
            status.current_mouse = {"id": info.get("id"), "hardware_id": info.get("hardware_id"), "friendly_name": info.get("friendly_name")}
            status.mouse_devices = keyboard.list_mouse_devices()
            status.devices = keyboard.list_interception_devices()
            status.available = True
            status.message = ""
            # 선택한 장치를 우선 사용하도록 캐시.
            self._mouse_dev = keyboard.get_default_mouse_device()
        except Exception as exc:
            status.available = False
            status.message = str(exc)
        return status

    def current_mouse(self) -> Optional[Dict]:
        if not self._installed():
            return None
        try:
            return keyboard.get_default_mouse_info()
        except Exception:
            return None

    def press(self, key: str):
        keyboard.key_press(key)

    def down(self, key: str):
        keyboard.key_down(key)

    def up(self, key: str):
        keyboard.key_up(key)

    def mouse_down(self, button: str, *, x: Optional[int] = None, y: Optional[int] = None):
        _send_mouse_button(button, is_down=True, x=x, y=y)

    def mouse_up(self, button: str, *, x: Optional[int] = None, y: Optional[int] = None):
        _send_mouse_button(button, is_down=False, x=x, y=y)

    def mouse_click(self, button: str, *, hold_ms: int = 0, x: Optional[int] = None, y: Optional[int] = None):
        _send_mouse_click(button, hold_ms=hold_ms, x=x, y=y)

    def mouse_move(self, x: int, y: int):
        _send_mouse_move(x, y)

    def test(self, key: str):
        keyboard.send_key_on_device(key)

    def _mouse_device(self):
        selected = keyboard.get_default_mouse_device()
        if selected:
            self._mouse_dev = selected
            return selected
        if self._mouse_dev:
            return self._mouse_dev
        inter = keyboard.get_interception()
        if not inter:
            raise RuntimeError("Interception driver is not available.")
        # 실제 하드웨어 ID가 있는 마우스를 우선 선택한다.
        preferred = None
        fallback = None
        for dev in getattr(inter, "_context", []):
            if not getattr(dev, "is_mouse", False):
                continue
            if fallback is None:
                fallback = dev
            try:
                hwid = dev.get_hardware_id()
            except Exception:
                hwid = ""
            if hwid:
                preferred = dev
                break
        self._mouse_dev = preferred or fallback
        if not self._mouse_dev:
            raise RuntimeError("No mouse device found via Interception.")
        return self._mouse_dev

    def _mouse_send(self, button: str, *, is_down: bool, x: Optional[int] = None, y: Optional[int] = None):
        # 좌표 지정 시 먼저 커서를 옮긴다.
        if user32 and x is not None and y is not None:
            user32.SetCursorPos(int(x), int(y))
        dev = self._mouse_device()
        state, data = _mouse_state(button, is_down=is_down)
        stroke = dev.stroke.__class__()  # MouseStroke
        stroke.state = state
        stroke.flags = 0
        stroke.rolling = data
        stroke.rawbtns = 0
        stroke.x = 0
        stroke.y = 0
        stroke.info = 0
        dev.send(stroke)

    def mouse_down(self, button: str, *, x: Optional[int] = None, y: Optional[int] = None):
        self._mouse_send(button, is_down=True, x=x, y=y)

    def mouse_up(self, button: str, *, x: Optional[int] = None, y: Optional[int] = None):
        self._mouse_send(button, is_down=False, x=x, y=y)

    def mouse_click(self, button: str, *, hold_ms: int = 0, x: Optional[int] = None, y: Optional[int] = None):
        self._mouse_send(button, is_down=True, x=x, y=y)
        if hold_ms > 0:
            time.sleep(max(0.0, hold_ms) / 1000.0)
        self._mouse_send(button, is_down=False, x=x, y=y)

    def mouse_move(self, x: int, y: int):
        # Interception는 상대 이동 기본. 절대 이동은 SetCursorPos로 처리.
        if user32:
            user32.SetCursorPos(int(x), int(y))
