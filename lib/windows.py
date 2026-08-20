from __future__ import annotations

import ctypes
import os
import sys
import time
from ctypes import wintypes
from typing import Any, Dict, List, Optional

from lib.processes import _process_info

SW_RESTORE = 9
SW_SHOW = 5


if sys.platform.startswith("win"):
    user32 = ctypes.windll.user32
    kernel32 = ctypes.windll.kernel32
    WNDENUMPROC = ctypes.WINFUNCTYPE(wintypes.BOOL, wintypes.HWND, wintypes.LPARAM)

    EnumWindows = user32.EnumWindows
    EnumWindows.argtypes = [WNDENUMPROC, wintypes.LPARAM]
    EnumWindows.restype = wintypes.BOOL

    IsWindowVisible = user32.IsWindowVisible
    IsWindowVisible.argtypes = [wintypes.HWND]
    IsWindowVisible.restype = wintypes.BOOL

    GetWindowTextLengthW = user32.GetWindowTextLengthW
    GetWindowTextLengthW.argtypes = [wintypes.HWND]
    GetWindowTextLengthW.restype = ctypes.c_int

    GetWindowTextW = user32.GetWindowTextW
    GetWindowTextW.argtypes = [wintypes.HWND, wintypes.LPWSTR, ctypes.c_int]
    GetWindowTextW.restype = ctypes.c_int

    GetClassNameW = user32.GetClassNameW
    GetClassNameW.argtypes = [wintypes.HWND, wintypes.LPWSTR, ctypes.c_int]
    GetClassNameW.restype = ctypes.c_int

    GetWindowThreadProcessId = user32.GetWindowThreadProcessId
    GetWindowThreadProcessId.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.DWORD)]
    GetWindowThreadProcessId.restype = wintypes.DWORD

    IsIconic = user32.IsIconic
    IsIconic.argtypes = [wintypes.HWND]
    IsIconic.restype = wintypes.BOOL

    ShowWindow = user32.ShowWindow
    ShowWindow.argtypes = [wintypes.HWND, ctypes.c_int]
    ShowWindow.restype = wintypes.BOOL

    SetForegroundWindow = user32.SetForegroundWindow
    SetForegroundWindow.argtypes = [wintypes.HWND]
    SetForegroundWindow.restype = wintypes.BOOL

    BringWindowToTop = user32.BringWindowToTop
    BringWindowToTop.argtypes = [wintypes.HWND]
    BringWindowToTop.restype = wintypes.BOOL

    SetActiveWindow = user32.SetActiveWindow
    SetActiveWindow.argtypes = [wintypes.HWND]
    SetActiveWindow.restype = wintypes.HWND

    GetForegroundWindow = user32.GetForegroundWindow
    GetForegroundWindow.restype = wintypes.HWND

    GetCurrentThreadId = kernel32.GetCurrentThreadId
    GetCurrentThreadId.restype = wintypes.DWORD

    AttachThreadInput = user32.AttachThreadInput
    AttachThreadInput.argtypes = [wintypes.DWORD, wintypes.DWORD, wintypes.BOOL]
    AttachThreadInput.restype = wintypes.BOOL
else:  # pragma: no cover - Windows-only feature
    user32 = None
    kernel32 = None


def _window_text(hwnd: int) -> str:
    length = max(0, int(GetWindowTextLengthW(hwnd))) if user32 else 0
    if length <= 0:
        return ""
    buf = ctypes.create_unicode_buffer(length + 1)
    GetWindowTextW(hwnd, buf, length + 1)
    return buf.value


def _class_name(hwnd: int) -> str:
    if not user32:
        return ""
    buf = ctypes.create_unicode_buffer(256)
    GetClassNameW(hwnd, buf, 256)
    return buf.value


def _process_for_window(hwnd: int) -> Dict[str, Any]:
    pid = wintypes.DWORD()
    if user32:
        GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
    info = _process_info(int(pid.value)) if pid.value else None
    return info or {"pid": int(pid.value or 0), "name": "", "path": "", "norm_path": ""}


def list_windows() -> List[Dict[str, Any]]:
    if not user32:
        return []
    result: List[Dict[str, Any]] = []

    @WNDENUMPROC
    def callback(hwnd, _lparam):
        try:
            if not IsWindowVisible(hwnd):
                return True
            title = _window_text(hwnd).strip()
            if not title:
                return True
            proc = _process_for_window(hwnd)
            result.append(
                {
                    "hwnd": int(hwnd),
                    "title": title,
                    "class_name": _class_name(hwnd),
                    "process_name": proc.get("name", "") or "",
                    "process_path": proc.get("path", "") or "",
                    "pid": int(proc.get("pid", 0) or 0),
                }
            )
        except Exception:
            pass
        return True

    EnumWindows(callback, 0)
    result.sort(key=lambda item: (str(item.get("process_name", "")).lower(), str(item.get("title", "")).lower()))
    return result


def _contains(haystack: str, needle: str) -> bool:
    return not needle or needle.casefold() in haystack.casefold()


def _equals(left: str, right: str) -> bool:
    return not right or left.casefold() == right.casefold()


def _process_matches(window_process: str, wanted_process: str) -> bool:
    if not wanted_process:
        return True
    wp = os.path.basename(window_process or "").casefold()
    wanted = os.path.basename(wanted_process or "").casefold()
    return bool(wp and wanted and wp == wanted)


def _matches_window(info: Dict[str, Any], spec: Dict[str, Any]) -> bool:
    mode = str(spec.get("match_mode") or "process_title_contains")
    title = str(spec.get("title") or "").strip()
    class_name = str(spec.get("class_name") or "").strip()
    process_name = str(spec.get("process_name") or "").strip()
    win_title = str(info.get("title") or "")
    win_class = str(info.get("class_name") or "")
    win_process = str(info.get("process_name") or "")

    if mode == "title_exact":
        return _equals(win_title, title)
    if mode == "title_contains":
        return _contains(win_title, title)
    if mode == "class_exact":
        return _equals(win_class, class_name)
    if mode == "process_exact":
        return _process_matches(win_process, process_name)
    if mode == "process_class":
        return _process_matches(win_process, process_name) and _equals(win_class, class_name)
    return _process_matches(win_process, process_name) and _contains(win_title, title)


def find_window(spec: Dict[str, Any]) -> Optional[Dict[str, Any]]:
    for info in list_windows():
        if _matches_window(info, spec):
            return info
    return None


def focus_window(spec: Dict[str, Any], *, restore: bool = True, wait_ms: int = 150) -> tuple[bool, Optional[Dict[str, Any]], str | None]:
    if not user32:
        return False, None, "unsupported_platform"
    info = find_window(spec)
    if not info:
        return False, None, "window_not_found"
    hwnd = int(info.get("hwnd") or 0)
    if not hwnd:
        return False, info, "invalid_hwnd"
    try:
        if restore:
            ShowWindow(hwnd, SW_RESTORE if IsIconic(hwnd) else SW_SHOW)
        foreground = GetForegroundWindow()
        fg_thread = GetWindowThreadProcessId(foreground, None) if foreground else 0
        cur_thread = GetCurrentThreadId()
        attached = False
        if fg_thread and fg_thread != cur_thread:
            attached = bool(AttachThreadInput(cur_thread, fg_thread, True))
        try:
            BringWindowToTop(hwnd)
            SetActiveWindow(hwnd)
            ok = bool(SetForegroundWindow(hwnd))
        finally:
            if attached:
                AttachThreadInput(cur_thread, fg_thread, False)
        if wait_ms > 0:
            time.sleep(max(0.0, min(5.0, wait_ms / 1000.0)))
        return ok or int(GetForegroundWindow() or 0) == hwnd, info, None
    except Exception as exc:
        return False, info, str(exc)
