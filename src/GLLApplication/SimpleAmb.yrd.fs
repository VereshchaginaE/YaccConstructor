
# 2 "SimpleAmb.yrd.fs"

module GLL.Parse.SimpleAmb
#nowarn "64";; // From fsyacc: turn off warnings that type variables used in production annotations are instantiated to concrete type
open Yard.Generators.GLL.Parser
open Yard.Generators.GLL
open Yard.Generators.Common.ASTGLL
type Token =
    | A of (int) 
    | B of (int)
    | D of (int)
    | RNGLR_EOF of (int)


let genLiteral (str : string) (data : int) =
    match str.ToLower() with
    | x -> None
let tokenData = function
    | A x -> box x
    | B x -> box x
    | D x -> box x
    | RNGLR_EOF x -> box x

let numToString = function
    | 0 -> "d"
    | 1 -> "error"
    | 2 -> "s"
    | 3 -> "yard_start_rule"
    | 4 -> "A"
    | 5 -> "B"
    | 6 -> "D"
    | 7 -> "RNGLR_EOF"
    | _ -> ""

let tokenToNumber = function
    | A _ -> 4
    | B _ -> 5
    | D _ -> 6
    | RNGLR_EOF _ -> 7

let isLiteral = function
    | A _ -> false
    | B _ -> false
    | D _ -> false
    | RNGLR_EOF _ -> false

let isTerminal = function
    | A _ -> true
    | B _ -> true
    | D _ -> true
    | RNGLR_EOF _ -> true
    | _ -> false

let numIsTerminal = function
    | 4 -> true
    | 5 -> true
    | 6 -> true
    | 7 -> true
    | _ -> false

let numIsNonTerminal = function
    | 0 -> true
    | 1 -> true
    | 2 -> true
    | 3 -> true
    | _ -> false

let numIsLiteral = function
    | _ -> false

let isNonTerminal = function
    | d -> true
    | error -> true
    | s -> true
    | yard_start_rule -> true
    | _ -> false

let getLiteralNames = []
let mutable private cur = 0

let acceptEmptyInput = false

let leftSide = [|2; 2; 3; 0|]
let table = [| [||];[||];[|3|];[||];[||];[||];[||];[||];[|1; 0|];[||];[||];[||];[|2|];[||];[||];[||]; |]
let private rules = [|4; 6; 5; 4; 0; 5; 2; 6|]
let private canInferEpsilon = [|false; true; false; false; false; false; false; false|]
let defaultAstToDot =
    (fun (tree : Yard.Generators.Common.ASTGLL.Tree<Token>) -> tree.AstToDot numToString)

let private rulesStart = [|0; 3; 6; 7; 8|]
let startRule = 2
let indexatorFullCount = 8
let rulesCount = 4
let indexEOF = 7
let nonTermCount = 4
let termCount = 4
let termStart = 4
let termEnd = 7
let literalStart = 8
let literalEnd = 7
let literalsCount = 0

let slots = dict <| [|(-1, 0); (65538, 1); (131073, 2)|]

let private parserSource = new ParserSourceGLL<Token> (tokenToNumber, genLiteral, numToString, tokenData, isLiteral, isTerminal, isNonTerminal, getLiteralNames, table, rules, rulesStart, leftSide, startRule, literalEnd, literalStart, termEnd, termStart, termCount, nonTermCount, literalsCount, indexEOF, rulesCount, indexatorFullCount, acceptEmptyInput,numIsTerminal, numIsNonTerminal, numIsLiteral, canInferEpsilon, slots)
let buildAst : (seq<Token> -> ParseResult<_>) =
    buildAst<Token> parserSource


