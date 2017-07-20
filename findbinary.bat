@REM finds a binary in the PATH directories
@REM forces result to use "short" names, avoids spaces-in-names problems
@echo %~s$PATH:1
@REM returns value through this variable - hmmmmm! 
@set FINDBINARY=%~s$PATH:1
