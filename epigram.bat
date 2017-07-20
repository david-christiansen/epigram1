REM windows epigram start script
REM xemacs does the hard work of deciding where things live.
REM see comments in "epigram" script (for Unix) re conventions
set EPIGRAM_ROOT=%~dp0
set EPIGRAM_EXT=.exe
call %EPIGRAM_ROOT%\findbinary.bat xemacs.exe
set XEMACS=%FINDBINARY%
start %XEMACS% -l "%EPIGRAM_ROOT%epigram.el"
REM c:\"Program Files"\XEmacs\XEmacs-21.4.13\i586-pc-win32\XEmacs.exe 
