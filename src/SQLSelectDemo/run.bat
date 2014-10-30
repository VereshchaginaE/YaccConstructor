set input=test input.sql
echo %input%
set type=cpu
echo %type%

bin\Release\SQLSelectDemo.exe -i "%input%" -t "%type%"