
# 2 "SimpleAmb.yrd.fs"
module GLL.Parse.SimpleAmb
#nowarn "64";; // From fsyacc: turn off warnings that type variables used in production annotations are instantiated to concrete type
open Yard.Generators.GLL.Parser
open Yard.Generators.GLL
open Yard.Generators.Common.AST3

# 1 "SimpleAmb.yrd"

//open AbstractLexer.Core

# 13 "SimpleAmb.yrd.fs"
type Token =
    | DIV of (int)
    | ERROR of (int)
    | LBRACE of (int)
    | MINUS of (int)
    | MULT of (int)
    | NUMBER of (int)
    | PLUS of (int)
    | POW of (int)
    | RBRACE of (int)
    | RNGLR_EOF of (int)


let genLiteral (str : string) (data : int) =
    match str.ToLower() with
    | x -> None
let tokenData = function
    | DIV x -> box x
    | ERROR x -> box x
    | LBRACE x -> box x
    | MINUS x -> box x
    | MULT x -> box x
    | NUMBER x -> box x
    | PLUS x -> box x
    | POW x -> box x
    | RBRACE x -> box x
    | RNGLR_EOF x -> box x

let numToString = function
    | 0 -> "error"
    | 1 -> "expr"
    | 2 -> "factor"
    | 3 -> "factorOp"
    | 4 -> "powExpr"
    | 5 -> "powOp"
    | 6 -> "term"
    | 7 -> "termOp"
    | 8 -> "yard_rule_binExpr_1"
    | 9 -> "yard_rule_binExpr_3"
    | 10 -> "yard_rule_binExpr_5"
    | 11 -> "yard_rule_yard_many_1_2"
    | 12 -> "yard_rule_yard_many_1_4"
    | 13 -> "yard_rule_yard_many_1_6"
    | 14 -> "yard_start_rule"
    | 15 -> "DIV"
    | 16 -> "ERROR"
    | 17 -> "LBRACE"
    | 18 -> "MINUS"
    | 19 -> "MULT"
    | 20 -> "NUMBER"
    | 21 -> "PLUS"
    | 22 -> "POW"
    | 23 -> "RBRACE"
    | 24 -> "RNGLR_EOF"
    | _ -> ""

let tokenToNumber = function
    | DIV _ -> 15
    | ERROR _ -> 16
    | LBRACE _ -> 17
    | MINUS _ -> 18
    | MULT _ -> 19
    | NUMBER _ -> 20
    | PLUS _ -> 21
    | POW _ -> 22
    | RBRACE _ -> 23
    | RNGLR_EOF _ -> 24

let isLiteral = function
    | DIV _ -> false
    | ERROR _ -> false
    | LBRACE _ -> false
    | MINUS _ -> false
    | MULT _ -> false
    | NUMBER _ -> false
    | PLUS _ -> false
    | POW _ -> false
    | RBRACE _ -> false
    | RNGLR_EOF _ -> false

let isTerminal = function
    | DIV _ -> true
    | ERROR _ -> true
    | LBRACE _ -> true
    | MINUS _ -> true
    | MULT _ -> true
    | NUMBER _ -> true
    | PLUS _ -> true
    | POW _ -> true
    | RBRACE _ -> true
    | RNGLR_EOF _ -> true
    | _ -> false

let numIsTerminal = function
    | 15 -> true
    | 16 -> true
    | 17 -> true
    | 18 -> true
    | 19 -> true
    | 20 -> true
    | 21 -> true
    | 22 -> true
    | 23 -> true
    | 24 -> true
    | _ -> false

let numIsNonTerminal = function
    | 0 -> true
    | 1 -> true
    | 2 -> true
    | 3 -> true
    | 4 -> true
    | 5 -> true
    | 6 -> true
    | 7 -> true
    | 8 -> true
    | 9 -> true
    | 10 -> true
    | 11 -> true
    | 12 -> true
    | 13 -> true
    | 14 -> true
    | _ -> false

let numIsLiteral = function
    | _ -> false

let isNonTerminal = function
    | error -> true
    | expr -> true
    | factor -> true
    | factorOp -> true
    | powExpr -> true
    | powOp -> true
    | term -> true
    | termOp -> true
    | yard_rule_binExpr_1 -> true
    | yard_rule_binExpr_3 -> true
    | yard_rule_binExpr_5 -> true
    | yard_rule_yard_many_1_2 -> true
    | yard_rule_yard_many_1_4 -> true
    | yard_rule_yard_many_1_6 -> true
    | yard_start_rule -> true
    | _ -> false

let getLiteralNames = []
let mutable private cur = 0

let acceptEmptyInput = false

let leftSide = [|1; 1; 14; 8; 11; 11; 7; 7; 6; 6; 9; 12; 12; 3; 3; 2; 2; 10; 13; 13; 5; 4; 4; 4|]
let table = [| [||];[||];[||];[||];[||];[||];[||];[||];[||];[||];[||];[|1; 0|];[|0|];[||];[||];[|0|];[||];[||];[||];[||];[||];[|16; 15|];[|15|];[||];[||];[|15|];[||];[||];[||];[||];[|14|];[||];[||];[||];[|13|];[||];[||];[||];[||];[||];[||];[|23|];[|22|];[||];[||];[|21|];[||];[||];[||];[||];[||];[||];[||];[||];[||];[||];[||];[|20|];[||];[||];[||];[|9; 8|];[|8|];[||];[||];[|8|];[||];[||];[||];[||];[||];[||];[||];[|7|];[||];[||];[|6|];[||];[||];[||];[||];[|3|];[|3|];[||];[||];[|3|];[||];[||];[||];[||];[||];[|10|];[|10|];[||];[||];[|10|];[||];[||];[||];[||];[||];[|17|];[|17|];[||];[||];[|17|];[||];[||];[||];[||];[||];[||];[||];[|5|];[||];[||];[|5|];[||];[|5; 4|];[|5; 4|];[|12|];[||];[||];[|12; 11|];[|12|];[||];[|12; 11|];[||];[|12; 11|];[|12; 11|];[|19; 18|];[||];[||];[|19; 18|];[|19; 18|];[||];[|19; 18|];[|19|];[|19; 18|];[|19; 18|];[||];[|2|];[|2|];[||];[||];[|2|];[||];[||];[||];[||]; |]
let private rules = [|8; 16; 1; 6; 11; 7; 6; 11; 21; 18; 9; 16; 2; 12; 3; 2; 12; 19; 15; 10; 16; 4; 13; 5; 4; 13; 22; 20; 17; 1; 23; 16|]
let private canInferEpsilon = [|true; false; false; false; false; false; false; false; false; false; false; true; true; true; false; false; false; false; false; false; false; false; false; false; false|]
let defaultAstToDot =
    (fun (tree : Yard.Generators.Common.AST3.Tree<Token>) -> tree.AstToDot numToString tokenToNumber leftSide)

let private rulesStart = [|0; 1; 2; 3; 5; 5; 8; 9; 10; 11; 12; 14; 14; 17; 18; 19; 20; 21; 23; 23; 26; 27; 28; 31; 32|]
let startRule = 2
let indexatorFullCount = 25
let rulesCount = 24
let indexEOF = 24
let nonTermCount = 15
let termCount = 10
let termStart = 15
let termEnd = 24
let literalStart = 25
let literalEnd = 24
let literalsCount = 0

let slots = dict <| [|(-1, 0); (1, 1); (131073, 2); (196609, 3); (196610, 4); (327681, 5); (327682, 6); (327683, 7); (524289, 8); (655361, 9); (655362, 10); (786433, 11); (786434, 12); (786435, 13); (983041, 14); (1114113, 15); (1114114, 16); (1245185, 17); (1245186, 18); (1245187, 19); (1441794, 20)|]

let private parserSource = new ParserSource2<Token> (tokenToNumber, genLiteral, numToString, tokenData, isLiteral, isTerminal, isNonTerminal, getLiteralNames, table, rules, rulesStart, leftSide, startRule, literalEnd, literalStart, termEnd, termStart, termCount, nonTermCount, literalsCount, indexEOF, rulesCount, indexatorFullCount, acceptEmptyInput,numIsTerminal, numIsNonTerminal, numIsLiteral, canInferEpsilon, slots)
let buildAst : (seq<Token> -> ParseResult<_>) =
    buildAst<Token> parserSource


