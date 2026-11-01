"""Windows program/batch launching, with optional UAC elevation."""
import ctypes
import os
import subprocess
from pathlib import Path
from types import SimpleNamespace


def launch_program(path, args='', cwd='', *, elevated=False):
    path = os.path.expandvars(path.strip().strip('"'))
    args = args.strip()
    cwd = os.path.expandvars(cwd.strip().strip('"')) or None
    target = path
    parameters = args
    if Path(path).suffix.lower() in ('.cmd', '.bat'):
        target = os.path.join(os.environ.get('SystemRoot', r'C:\Windows'), 'System32', 'cmd.exe')
        parameters = '/d /s /c ""' + path + '"' + (' ' + args if args else '') + '"'
    if elevated:
        execute = ctypes.windll.shell32.ShellExecuteW
        execute.argtypes = [ctypes.c_void_p, ctypes.c_wchar_p, ctypes.c_wchar_p,
                            ctypes.c_wchar_p, ctypes.c_wchar_p, ctypes.c_int]
        execute.restype = ctypes.c_ssize_t
        result = execute(None, 'runas', target, parameters or None, cwd, 1)
        if result <= 32:
            raise OSError(f'관리자 권한 실행 실패 또는 승인 취소 (Windows 오류 {result})')
        # ShellExecute reports accepted launch, not the child's completion/PID.
        return SimpleNamespace(pid=None)
    command = subprocess.list2cmdline([target]) + (' ' + parameters if parameters else '')
    return subprocess.Popen(command, cwd=cwd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
