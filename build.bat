@echo off
rem Builds build\JerichoKO_Patcher.exe with the C# compiler that ships with .NET Framework 4.
setlocal
cd /d "%~dp0src"
set CSC=%WINDIR%\Microsoft.NET\Framework64\v4.0.30319\csc.exe
if not exist "%CSC%" set CSC=%WINDIR%\Microsoft.NET\Framework\v4.0.30319\csc.exe
if not exist "%CSC%" (
  echo csc.exe not found. .NET Framework 4 is required.
  exit /b 1
)
if not exist "..\build" mkdir "..\build"
"%CSC%" /nologo /codepage:65001 /target:winexe /platform:x64 /optimize+ /out:..\build\JerichoKO_Patcher.exe ^
 /r:System.Drawing.dll /r:System.Windows.Forms.dll /r:System.Core.dll /r:System.IO.Compression.dll ^
 /resource:ko.tsv.gz,ko.tsv.gz /resource:intro_ko.ass,intro_ko.ass /resource:prologue_ko.ass,prologue_ko.ass ^
 /resource:splash.bik.gz,splash.bik.gz JerichoKoPatcher.cs
if errorlevel 1 exit /b 1
echo Done: build\JerichoKO_Patcher.exe
