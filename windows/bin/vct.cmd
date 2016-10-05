@echo off

rem %~dp0 is expanded pathname of the current script under NT
rem because of problem with %cd% was used instead of %~dp0..\..\ 
rem in configuration.java --> getparent of %~dp0..\..\ is %~dp0..\ which does not seem to work

@echo off

rem %~dp0 is expanded pathname of the current script under NT

setlocal
set VCT_HOME=%~dp0..\..\

rem Create class path with run time libraries

set VCT_PATH=%VCT_HOME%\hre\bin
set VCT_PATH=%VCT_PATH%;%VCT_HOME%\hre\hre.jar
set VCT_PATH=%VCT_PATH%;%VCT_HOME%\core\bin
set VCT_PATH=%VCT_PATH%;%VCT_HOME%\core\vct-core.jar
set VCT_PATH=%VCT_PATH%;%VCT_HOME%\viper\viper-api\bin
set VCT_PATH=%VCT_PATH%;%VCT_HOME%\core\libs\antlr-4.5.3-complete.jar
set VCT_PATH=%VCT_PATH%;%VCT_HOME%\core\libs\gson-2.7.jar
set VCT_PATH=%VCT_PATH%;%VCT_HOME%\libs\commons-lang3-3.1\commons-lang3-3.1.jar
set VCT_PATH=%VCT_PATH%;%VCT_HOME%\main\bin
set VCT_PATH=%VCT_PATH%;%VCT_HOME%\main\vct-tool.jar

java -Xss128M -cp "%VCT_PATH%" vct.main.Main %*

