@echo off
setlocal
REM Run main.py with uv from the repository root so it can be double-clicked.

set "SCRIPT_DIR=%~dp0"
pushd "%SCRIPT_DIR%"

uv run main.py
set "EXITCODE=%ERRORLEVEL%"

popd

if %EXITCODE% neq 0 (
    echo uv run main.py exited with %EXITCODE%.
    pause
)

exit /b %EXITCODE%
