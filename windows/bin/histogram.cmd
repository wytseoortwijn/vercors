@echo off

rem %~dp0 is expanded pathname of the current script under NT
set VCT_HOME=%~dp0..\..

rem Create class path with run time libraries
set HISTOGRAM_PATH=%VCT_HOME%\histogram\bin
set HISTOGRAM_PATH=%HISTOGRAM_PATH%;%VCT_HOME%\histogram\libs\commons-cli-1.2.jar
set HISTOGRAM_PATH=%HISTOGRAM_PATH%;%VCT_HOME%\histogram\libs\asm-commons-3.3.1.jar
set HISTOGRAM_PATH=%HISTOGRAM_PATH%;%VCT_HOME%\histogram\libs\asm.jar

java -cp "%HISTOGRAM_PATH%" root.Main %*

