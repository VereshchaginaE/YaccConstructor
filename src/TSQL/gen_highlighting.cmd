rem -c "ReplaceLiterals KW_%%s"
del log.txt

..\..\Bin\Release\v40\AbstractLexer.Generator.exe Lexer.fsl -o Lexer.fs --unicode

rem echo mssql.yrd >> log.txt
    ..\..\Bin\Release\v40\YC.YaccConstructor.exe -f YardFrontend -i mssql.yrd -c ExpandEbnf -c Linearize ^
        -g "RNGLRGenerator -module Yard.Examples.MSParser -translate true -highlighting true -namespace TSQLHighlighting -table LALR -o MSParser.fs -abstract true" >> log.txt