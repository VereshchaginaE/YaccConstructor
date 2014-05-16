// Learn more about F# at http://fsharp.net
// See the 'F# Tutorial' project for more help.

module RNGLRParserEBNF.SimpleTest

open System
open Yard.Generators.RNGLR.AST
open Yard.Generators.RNGLR.ParserEBNF  
open LexCommon

let run path astBuilder =
    let tokens = LexCommon.tokens(path)
    astBuilder tokens

let dir = @"../../../Tests/RNGLR/EBNF/"
let inline printErr (num, token : 'a, msg) =
    printfn "Error in position %d on Token %A: %s" num token msg
    //Assert.Fail(sprintf "Error in position %d on Token %A: %s" num token msg)

type ``RNGLR parser tests with simple lexer`` () =


    member test.``Longest epsilon test``() =
        let parser = RNGLR.ParseLongest.buildAst
        let path = dir + "simpleEpsilon.txt"

        match run path parser with
        | Error (num, tok, err, _) -> printErr (num, tok, err)
        | Success (tree, _) -> printfn "Success"

    member test.``ManyAndOne epsilon test``() =
        let parser = RNGLR.ParseManyAndOne.buildAst
        let path = dir + "ManyAndOne0.txt"

        match run path parser with
        | Error (num, tok, err, _) -> printErr (num, tok, err)
        | Success (tree, _) -> printfn "Success"

    member test.``ManyAndOne one test``() =
        let parser = RNGLR.ParseManyAndOne.buildAst
        let path = dir + "ManyAndOne1.txt"

        match run path parser with
        | Error (num, tok, err, _) -> printErr (num, tok, err)
        | Success (tree, _) -> printfn "Success"

    member test.``ManyAndOne many test``() =
        let parser = RNGLR.ParseManyAndOne.buildAst
        let path = dir + "ManyAndOne2.txt"

        match run path parser with
        | Error (num, tok, err, _) -> printErr (num, tok, err)
        | Success (tree, _) ->
            printfn "Success"
            RNGLR.ParseManyAndOne.defaultAstToDot tree "ast.dot"

    member test.``ManyAndOne wrong test``() =
        let parser = RNGLR.ParseManyAndOne.buildAst
        let path = dir + "ManyAndOneWrong.txt"

        match run path parser with
        | Error (num, tok, err, _) -> printErr (num, tok, err)
        | Success (tree, _) -> printfn "Success"

    member test.``SimpleRightNull test``() =
        let parser = RNGLR.ParseSimpleRightNull.buildAst
        let path = dir + "SimpleRightNull.txt"

        match run path parser with
        | Error (num, tok, err, _) -> printErr (num, tok, err)
        | Success (tree, _) -> printfn "Success"

    member test.``RightNull test``() =
        let parser = RNGLR.ParseRightNull.buildAst
        let path = dir + "RightNull.txt"

        match run path parser with
        | Error (num, tok, err, _) -> printErr (num, tok, err)
        | Success (tree, _) -> printfn "Success"

    member test.``TwoEpsilonsMiddle test``() =
        let parser = RNGLR.ParseTwoEpsilonsMiddle.buildAst
        let path = dir + "TwoEpsilonsMiddle.txt"

        match run path parser with
        | Error (num, tok, err, _) -> printErr (num, tok, err)
        | Success (tree, _) -> printfn "Success"

    member test.``TwoEpsilonsMiddleWrong test``() =
        let parser = RNGLR.ParseTwoEpsilonsMiddle.buildAst
        let path = dir + "TwoEpsilonsMiddleWrong.txt"

        match run path parser with
        | Error (num, tok, err, _) -> printErr (num, tok, err)
        | Success (tree, _) -> printfn "Success"

    member test.``ComplexRightNull test``() =
        let parser = RNGLR.ParseComplexRightNull.buildAst
        let path = dir + "ComplexRightNull.txt"

        match run path parser with
        | Error (num, tok, err, _) -> printErr (num, tok, err)
        | Success (tree, _) -> printfn "Success"

    member test.``ComplexRightNull2 test``() =
        let parser = RNGLR.ParseComplexRightNull.buildAst
        let path = dir + "ComplexRightNull2.txt"

        match run path parser with
        | Error (num, tok, err, _) -> printErr (num, tok, err)
        | Success (tree, _) -> 
            printfn "Success"
            RNGLR.ParseComplexRightNull.defaultAstToDot tree "ast.dot"

    member test.``ComplexRightNullWrong test``() =
        let parser = RNGLR.ParseComplexRightNull.buildAst
        let path = dir + "ComplexRightNullWrong.txt"

        match run path parser with
        | Error (num, tok, err, _) -> printErr (num, tok, err)
        | Success (tree, _) -> printfn "Success"

    member test.``CalcEBNF test``() =
        let parser = RNGLR.ParseCalcEBNF.buildAst
        let path = dir + "CalcEBNF.txt"

        match run path parser with
        | Error (num, tok, err, _) -> printErr (num, tok, err)
        | Success (tree, _) -> 
            printfn "Success"
            RNGLR.ParseCalcEBNF.defaultAstToDot tree "calc.ast.dot"

    member test.``StackingConflictWrong test``() =
        let parser = RNGLR.ParseStackingConflict.buildAst
        let path = dir + "StackingConflictWrong.txt"

        match run path parser with
        | Error (num, tok, err, _) -> printErr (num, tok, err)
        | Success (tree, _) -> 
            printfn "Success"
            RNGLR.ParseStackingConflict.defaultAstToDot tree "StackingConflict.dot"


[<EntryPoint>]
(new ``RNGLR parser tests with simple lexer``()).``Longest epsilon test``()
(new ``RNGLR parser tests with simple lexer``()).``ManyAndOne epsilon test``()
(new ``RNGLR parser tests with simple lexer``()).``ManyAndOne one test``()
(new ``RNGLR parser tests with simple lexer``()).``ManyAndOne many test``()
(new ``RNGLR parser tests with simple lexer``()).``ManyAndOne wrong test``()
(new ``RNGLR parser tests with simple lexer``()).``SimpleRightNull test``()
(new ``RNGLR parser tests with simple lexer``()).``RightNull test``()
(new ``RNGLR parser tests with simple lexer``()).``TwoEpsilonsMiddle test``()
(new ``RNGLR parser tests with simple lexer``()).``TwoEpsilonsMiddleWrong test``()
(new ``RNGLR parser tests with simple lexer``()).``ComplexRightNull test``()
(new ``RNGLR parser tests with simple lexer``()).``ComplexRightNull2 test``()
(new ``RNGLR parser tests with simple lexer``()).``ComplexRightNullWrong test``()
(new ``RNGLR parser tests with simple lexer``()).``CalcEBNF test``()
(new ``RNGLR parser tests with simple lexer``()).``StackingConflictWrong test``()

Console.ReadLine() |> ignore
