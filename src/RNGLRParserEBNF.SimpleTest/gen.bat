
del log.txt

for %%i in (CalcEBNF, ComplexRightNull, Longest, ManyAndOne, ManyAndOpt, RightNull, SimpleOneTerm, SimpleOpt, SimpleRightNull, SimpleSome, SimpleTwoTerms, StackingConflict, TwoEpsilonsMiddle) do (
		echo . >> log.txt
		echo %%i >> log.txt
    ..\..\bin\Release\v40\YaccConstructor.exe -i %%i.yrd -c ExpandMeta ^
        -g "RNGLRGenerator -pos int -token int -module RNGLR.Parse%%i -translate true -table LR -o %%i.yrd.fs" >> log.txt
)
