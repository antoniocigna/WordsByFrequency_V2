@echo off

::  start File  
::
::-------------------------------------------------------------------------------------------------------
:: root is the path to the software    
::   
:: the -input keyword precedes the control file name 
:: 
::-------------------------------------------------------------------------------------------------------
::
set root=..\

echo root=%root%

"%root%wordsByFrequencyV2"   -html "%root%WBF_html_js"    -input "inputControl.txt"

