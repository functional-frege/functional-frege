@echo off
rem Double-click to check the certificate (offline; add --run for the live Lean check).
cd /d "%~dp0"
where python >nul 2>nul || (echo Python 3.9 or later is required: https://www.python.org/downloads/ & pause & exit /b 1)
python check_certificate.py %*
pause
