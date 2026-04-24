@echo off
cd /d "%~dp0"
echo Controleren op benodigde pakketten...
py -m pip install pyclick pyautogui pytesseract matplotlib numpy pillow
cls
py roulette_bot_enhanced.py
if errorlevel 1 (
    echo.
    echo Er is een fout opgetreden tijdens het draaien van de bot.
    pause
)