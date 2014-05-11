
# 2 "RightNull.yrd.fs"
module RNGLR.ParseRightNull
#nowarn "64";; // From fsyacc: turn off warnings that type variables used in production annotations are instantiated to concrete type
open Yard.Generators.RNGLR
open Yard.Generators.RNGLR.StackLabel
open Yard.Generators.RNGLR.EBNF
open Yard.Generators.RNGLR.ParserEBNF
open Yard.Generators.RNGLR.AST
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
    | 0 -> "a"
    | 1 -> "b"
    | 2 -> "d"
    | 3 -> "error"
    | 4 -> "s"
    | 5 -> "yard_start_rule"
    | 6 -> "A"
    | 7 -> "B"
    | 8 -> "D"
    | 9 -> "RNGLR_EOF"
    | _ -> ""

let tokenToNumber = function
    | A _ -> 6
    | B _ -> 7
    | D _ -> 8
    | RNGLR_EOF _ -> 9

let isLiteral = function
    | A _ -> false
    | B _ -> false
    | D _ -> false
    | RNGLR_EOF _ -> false

let getLiteralNames = []
let mutable private cur = 0
let leftSide = [|4; 4; 5; 2; 0; 0; 1|]
let startRule = 2

let acceptEmptyInput = false

let defaultAstToDot =
    (fun (tree : Yard.Generators.RNGLR.AST.Tree<Token>) -> tree.AstToDot numToString tokenToNumber leftSide)

let private lists_gotos = [|1; 11; 12; 2; 5; 3; 4; 6; 8; 7; 9; 10; 13; 14; 15|]
let private stackArrays = [|[|0|]; [|1|]; [|3|]; [|4|]|]
let private stackSets = stackArrays |> Array.map Set.ofArray
let private small_gotos =
        [|3; 65536; 65536; 262145; 0; 393218; 65537; 65538; 131075; 0; 393220; 65538; 131073; 393221; 0; 196609; 458758; 0; 327682; 7; 0; 393224; 65539; 393217; 65545; 0; 524289; 65546; 0; 589825; 65547; 0; 786434; 131084; 0; 393220; 65538; 851969; 393229; 0; 917505; 524302; 0|]
let gotos = Array.zeroCreate 16
for i = 0 to 15 do
        gotos.[i] <- Array.create 10 None
cur <- 0
while cur < small_gotos.Length do
    let i = small_gotos.[cur] >>> 16
    let length = small_gotos.[cur] &&& 65535
    cur <- cur + 1
    for k = 0 to length-1 do
        let j = small_gotos.[cur + k*2] >>> 16
        let x = small_gotos.[cur + k*2] &&& 65535
        let label = small_gotos.[cur + k*2 + 1] >>> 16
        let setId = small_gotos.[cur + k*2 + 1] &&& 65535
        let stackLabel = GetStackLabel label setId
        gotos.[i].[j] <- Some (lists_gotos.[x], stackLabel)
    cur <- cur + length * 2
let private lists_reduces = [|[|0|]; [|3|]; [|4|]; [|1|]|]
let private small_reduces =
        [|262146; 393216; 589824; 327681; 393217; 393217; 393217; 458753; 393217; 524289; 393218; 589825; 393218; 655361; 393218; 983042; 393219; 589827|]
let reduces = Array.zeroCreate 16
for i = 0 to 15 do
        reduces.[i] <- Array.zeroCreate 10
cur <- 0
while cur < small_reduces.Length do
    let i = small_reduces.[cur] >>> 16
    let length = small_reduces.[cur] &&& 65535
    cur <- cur + 1
    for k = 0 to length-1 do
        let j = small_reduces.[cur + k] >>> 16
        let x = small_reduces.[cur + k] &&& 65535
        reduces.[i].[j] <- lists_reduces.[x]
    cur <- cur + length
let private lists_zeroReduces = [|[|6|]; [|5|]|]
let private small_zeroReduces =
        [|1; 393216; 327681; 393217; 393217; 393216; 524289; 393216; 589825; 393216|]
let zeroReduces = Array.zeroCreate 16
for i = 0 to 15 do
        zeroReduces.[i] <- Array.zeroCreate 10
cur <- 0
while cur < small_zeroReduces.Length do
    let i = small_zeroReduces.[cur] >>> 16
    let length = small_zeroReduces.[cur] &&& 65535
    cur <- cur + 1
    for k = 0 to length-1 do
        let j = small_zeroReduces.[cur + k] >>> 16
        let x = small_zeroReduces.[cur + k] &&& 65535
        zeroReduces.[i].[j] <- lists_zeroReduces.[x]
    cur <- cur + length
let private small_acc = [11]
let private accStates = Array.zeroCreate 16
for i = 0 to 15 do
        accStates.[i] <- List.exists ((=) i) small_acc
let eofIndex = 9
let errorIndex = 3
let private parserSource = new ParserSourceEBNF<Token> (gotos, reduces, zeroReduces, stackSets, accStates, leftSide, startRule, eofIndex, tokenToNumber, acceptEmptyInput, numToString, errorIndex)
let buildAst : (seq<'TokenType> -> ParseResultEBNF<Token>) =
    buildAst<Token> parserSource


