module BooleanGrammarTest

open Yard.Core
open Yard.Core.IL
open Yard.Core.IL.Production
open Yard.Core.IL.Definition
open NUnit.Framework
open ConversionsTests

[<TestFixture>]
type ``Boolean Grammar Tests`` () =
    let basePath = @"../../../../Tests/YardFrontend/BooleanGrammars/ConversionTests"
    let fe = getFrontend("YardFrontend")
    let conversion = "ConvertBooleanGrammar"
    [<Test>]
    //!(A | B) -> (!A & !B)
    member test.``Bool gram test 1`` () =
        let loadIL = fe.ParseGrammar (System.IO.Path.Combine(basePath,"booleanGrammar4.yrd"))
        Namer.initNamer loadIL.grammar
        let result = ConversionsManager.ApplyConversion conversion loadIL
        let rules =
            verySimpleRules "s"
                [{
                   omit = false                    
                   rule = PConjuct (PNegat (PToken (Source.t "A")),PNegat (PToken (Source.t "B")));
                   binding = None
                   checker = None
                }]
        let expected = defaultDefinition rules

        expected |> treeDump.Generate |> string |> printfn "%s"
        printfn "%s" "************************"
        result |> treeDump.Generate |> string |> printfn "%s"
        Assert.IsTrue(ILComparators.GrammarEqualsWithoutLineNumbers expected.grammar result.grammar)

    [<Test>]
    //(A | B) & C -> (A & C) | (B & C)
    member test.``Bool gram test 2`` () =
        let loadIL = fe.ParseGrammar (System.IO.Path.Combine(basePath,"booleanGrammar5.yrd"))
        Namer.initNamer loadIL.grammar
        let result = ConversionsManager.ApplyConversion conversion loadIL
        let rules =
            verySimpleRules "s"
                [{
                   omit = false                    
                   rule = PAlt (PConjuct (PToken (Source.t "A"),PToken (Source.t "C")),PConjuct (PToken (Source.t "B"),PToken (Source.t "C")));
                   binding = None
                   checker = None
                }]
        let expected = defaultDefinition rules

        expected |> treeDump.Generate |> string |> printfn "%s"
        printfn "%s" "************************"
        result |> treeDump.Generate |> string |> printfn "%s"
        Assert.IsTrue(ILComparators.GrammarEqualsWithoutLineNumbers expected.grammar result.grammar)

    [<Test>]
    // !(A & B | C) -> (!A & !C) | (!B & !C)
    member test.``Bool gram test 3`` () =
        let loadIL = fe.ParseGrammar (System.IO.Path.Combine(basePath,"booleanGrammar6.yrd"))
        Namer.initNamer loadIL.grammar
        let result = ConversionsManager.ApplyConversion conversion loadIL
        let rules =
            verySimpleRules "s"
                [{
                   omit = false                    
                   rule = PAlt (PConjuct (PNegat(PToken (Source.t "A")),PNegat(PToken (Source.t "C"))),PConjuct (PNegat(PToken (Source.t "B")),PNegat(PToken (Source.t "C"))));
                   binding = None
                   checker = None
                }]
        let expected = defaultDefinition rules

        expected |> treeDump.Generate |> string |> printfn "%s"
        printfn "%s" "************************"
        result |> treeDump.Generate |> string |> printfn "%s"
        Assert.IsTrue(ILComparators.GrammarEqualsWithoutLineNumbers expected.grammar result.grammar)
