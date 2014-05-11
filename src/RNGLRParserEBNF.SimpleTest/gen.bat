
del log.txt

for %%i in (ComplexRightNull, Longest, ManyAndOne, RightNull, SimpleOneTerm, SimpleRightNull, SimpleTwoTerms, TwoEpsilonsMiddle) do (
		echo . >> log.txt
		echo %%i >> log.txt
    ..\..\bin\Release\v40\YaccConstructor.exe -i %%i.yrd -c ExpandMeta ^
        -g "RNGLRGenerator -pos int -token int -module RNGLR.Parse%%i -translate true -table LR -o %%i.yrd.fs" >> log.txt
)
