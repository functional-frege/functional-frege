@echo off
rem Double-click to check the certificate with the Lean kernel.
rem Offers to install Lean (elan + Lean 4.33.1) and the prebuilt Mathlib library if they are missing.
cd /d "%~dp0"
where python >nul 2>nul || (echo Python 3.9 or later is required: https://www.python.org/downloads/ & pause & exit /b 1)
python check_certificate.py --run
