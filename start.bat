@echo off
title RMKCET Parent Connect
color 0A
echo.
echo  ============================================
echo   RMKCET Parent Connect
echo   Starting server...
echo  ============================================
echo.

:: Move to the folder where this .bat lives
cd /d "%~dp0"

:: Check if Python is installed
python --version >nul 2>&1
if errorlevel 1 (
    echo  [ERROR] Python is not installed or not in PATH!
    echo  Please install Python 3.8 or later from https://python.org
    echo  Make sure to check "Add Python to PATH" during installation.
    pause
    exit /b 1
)

:: Define virtual environment paths
set "VENV_DIR="
set "PY_EXE="
set "PIP_EXE="

:: Check for existing virtual environment
if exist "venv\Scripts\python.exe" (
    set "VENV_DIR=venv"
    set "PY_EXE=venv\Scripts\python.exe"
    set "PIP_EXE=venv\Scripts\pip.exe"
    echo  [INFO] Found existing virtual environment: venv
) else if exist ".venv\Scripts\python.exe" (
    set "VENV_DIR=.venv"
    set "PY_EXE=.venv\Scripts\python.exe"
    set "PIP_EXE=.venv\Scripts\pip.exe"
    echo  [INFO] Found existing virtual environment: .venv
)

:: If no virtual environment exists, create one
if "%PY_EXE%"=="" (
    echo  [INFO] Virtual environment not found. Creating one...
    echo  Creating venv...
    python -m venv venv
    if errorlevel 1 (
        echo  [ERROR] Failed to create virtual environment!
        pause
        exit /b 1
    )
    set "VENV_DIR=venv"
    set "PY_EXE=venv\Scripts\python.exe"
    set "PIP_EXE=venv\Scripts\pip.exe"
    echo  [SUCCESS] Virtual environment created successfully!
)

:: Kill any old process on port 5000
echo  [INFO] Checking for existing processes on port 5000...
for /f "tokens=5" %%a in ('netstat -ano ^| findstr ":5000" ^| findstr "LISTENING"') do (
    echo  [INFO] Killing process with PID: %%a
    taskkill /F /PID %%a >nul 2>&1
)

:: Install dependencies if requirements.txt exists
if exist "backend\requirements.txt" (
    echo  [INFO] Checking/Installing dependencies...
    "%PY_EXE%" -c "import flask" 2>nul
    if errorlevel 1 (
        echo  [INFO] Installing dependencies from requirements.txt...
        "%PIP_EXE%" install -r backend\requirements.txt
        if errorlevel 1 (
            echo  [ERROR] Failed to install dependencies!
            pause
            exit /b 1
        )
        echo  [SUCCESS] Dependencies installed successfully!
    ) else (
        echo  [INFO] Dependencies already installed.
    )
) else (
    echo  [WARNING] backend\requirements.txt not found. Skipping dependency installation.
)

:: Start server
echo.
echo  ============================================
echo   Server starting...
echo   Opening http://localhost:5000 in your browser...
echo   Press Ctrl+C to stop the server.
echo  ============================================
echo.
start "" http://localhost:5000
"%PY_EXE%" backend\app.py

:: If the server stops, wait for user input before closing
echo.
echo  Server has stopped.
pause