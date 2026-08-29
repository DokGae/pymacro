from __future__ import annotations

import ctypes
import os
import sys
from ctypes import wintypes
from typing import Any, Dict, List, Optional

PROCESS_QUERY_INFORMATION = 0x0400
PROCESS_VM_READ = 0x0010
PROCESS_QUERY_LIMITED_INFORMATION = 0x1000
PROCESS_TERMINATE = 0x0001
ERROR_INSUFFICIENT_BUFFER = 122
_MAX_PATH_LEN = 1024


if sys.platform.startswith("win"):
    kernel32 = ctypes.windll.kernel32
    psapi = ctypes.windll.psapi
    user32 = ctypes.windll.user32

    OpenProcess = kernel32.OpenProcess
    OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    OpenProcess.restype = wintypes.HANDLE

    CloseHandle = kernel32.CloseHandle
    CloseHandle.argtypes = [wintypes.HANDLE]
    CloseHandle.restype = wintypes.BOOL

    TerminateProcess = kernel32.TerminateProcess
    TerminateProcess.argtypes = [wintypes.HANDLE, wintypes.UINT]
    TerminateProcess.restype = wintypes.BOOL

    QueryFullProcessImageNameW = kernel32.QueryFullProcessImageNameW
    QueryFullProcessImageNameW.argtypes = [wintypes.HANDLE, wintypes.DWORD, wintypes.LPWSTR, ctypes.POINTER(wintypes.DWORD)]
    QueryFullProcessImageNameW.restype = wintypes.BOOL

    GetProcessImageFileNameW = psapi.GetProcessImageFileNameW
    GetProcessImageFileNameW.argtypes = [wintypes.HANDLE, wintypes.LPWSTR, wintypes.DWORD]
    GetProcessImageFileNameW.restype = wintypes.DWORD

    EnumProcesses = psapi.EnumProcesses
    EnumProcesses.argtypes = [ctypes.POINTER(wintypes.DWORD), wintypes.DWORD, ctypes.POINTER(wintypes.DWORD)]
    EnumProcesses.restype = wintypes.BOOL

    GetWindowThreadProcessId = user32.GetWindowThreadProcessId
    GetWindowThreadProcessId.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.DWORD)]
    GetWindowThreadProcessId.restype = wintypes.DWORD

    GetForegroundWindow = user32.GetForegroundWindow
    GetForegroundWindow.restype = wintypes.HWND
else:  # pragma: no cover - non-Windows fallback
    kernel32 = None
    psapi = None
    user32 = None


def _safe_close(handle: wintypes.HANDLE):
    if kernel32 and handle:
        try:
            CloseHandle(handle)
        except Exception:
            pass


def _normalize_path(path: str | None) -> str:
    if not path:
        return ""
    try:
        return os.path.normcase(os.path.abspath(path))
    except Exception:
        return os.path.normcase(path)


def _process_name_matches(process_name: str | None, wanted_name: str | None) -> bool:
    if not wanted_name:
        return True
    current = os.path.basename(process_name or "").casefold()
    wanted = os.path.basename(wanted_name or "").casefold()
    return bool(current and wanted and current == wanted)


def _image_path_from_handle(handle: wintypes.HANDLE) -> Optional[str]:
    if not kernel32 or not handle:
        return None

    buf_len = wintypes.DWORD(_MAX_PATH_LEN)
    while True:
        buf = ctypes.create_unicode_buffer(buf_len.value)
        size = wintypes.DWORD(buf_len.value)
        if QueryFullProcessImageNameW(handle, 0, buf, ctypes.byref(size)):
            return buf.value[: size.value]
        err = ctypes.get_last_error()
        if err == ERROR_INSUFFICIENT_BUFFER:
            buf_len.value *= 2
            continue
        break

    # fallback
    try:
        buf = ctypes.create_unicode_buffer(buf_len.value)
        res = GetProcessImageFileNameW(handle, buf, buf_len.value)
        if res:
            return buf.value[:res]
    except Exception:
        pass
    return None


def _process_info(pid: int) -> Optional[Dict[str, Any]]:
    if not kernel32:
        return None
    try:
        handle = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION | PROCESS_QUERY_INFORMATION | PROCESS_VM_READ, False, int(pid))
    except Exception:
        handle = None
    if not handle:
        return None
    try:
        path = _image_path_from_handle(handle)
    finally:
        _safe_close(handle)
    name = os.path.basename(path) if path else ""
    return {"pid": int(pid), "name": name, "path": path or "", "norm_path": _normalize_path(path)}


def list_processes(max_count: Optional[int] = None) -> List[Dict[str, Any]]:
    if not psapi or not kernel32:
        return []
    size = 4096
    arr = (wintypes.DWORD * size)()
    needed = wintypes.DWORD()
    ok = EnumProcesses(arr, ctypes.sizeof(arr), ctypes.byref(needed))
    if not ok:
        return []
    count = min(needed.value // ctypes.sizeof(wintypes.DWORD), size)
    seen_norm: set[str] = set()
    result: List[Dict[str, Any]] = []
    for pid in arr[:count]:
        if pid == 0:
            continue
        info = _process_info(pid)
        if not info:
            continue
        norm = info.get("norm_path") or info.get("name")
        if norm and norm in seen_norm:
            continue
        if norm:
            seen_norm.add(norm)
        result.append(info)
        if max_count is not None and len(result) >= max_count:
            break
    return result


def get_foreground_process() -> Optional[Dict[str, Any]]:
    if not user32 or not kernel32:
        return None
    hwnd = GetForegroundWindow()
    if not hwnd:
        return None
    pid = wintypes.DWORD()
    GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
    if not pid.value:
        return None
    return _process_info(pid.value)


def terminate_processes(
    *,
    process_name: str | None = None,
    process_path: str | None = None,
    max_count: Optional[int] = None,
) -> tuple[int, list[str]]:
    if not kernel32:
        return 0, ["unsupported_platform"]
    wanted_path = _normalize_path(process_path)
    wanted_name = os.path.basename(process_name or process_path or "")
    if not wanted_name and not wanted_path:
        return 0, ["empty_process_spec"]
    current_pid = os.getpid()
    terminated = 0
    errors: list[str] = []
    for info in list_processes():
        pid = int(info.get("pid", 0) or 0)
        if not pid or pid == current_pid:
            continue
        if wanted_path:
            info_path = _normalize_path(info.get("path"))
            if info_path != wanted_path:
                continue
        elif not _process_name_matches(info.get("name"), wanted_name):
            continue
        handle = None
        try:
            handle = OpenProcess(PROCESS_TERMINATE, False, pid)
            if not handle:
                errors.append(f"pid={pid}: open_failed")
                continue
            if not TerminateProcess(handle, 1):
                errors.append(f"pid={pid}: terminate_failed")
                continue
            terminated += 1
            if max_count is not None and terminated >= max_count:
                break
        except Exception as exc:
            errors.append(f"pid={pid}: {exc}")
        finally:
            _safe_close(handle)
    return terminated, errors
