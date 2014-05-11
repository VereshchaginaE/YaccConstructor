
# 2 "LongestEBNF.yrd.fs"
module RNGLR.ParseLongest
#nowarn "64";; // From fsyacc: turn off warnings that type variables used in production annotations are instantiated to concrete type
open Yard.Generators.RNGLR
open Yard.Generators.RNGLR.StackLabel
open Yard.Generators.RNGLR.EBNF
open Yard.Generators.RNGLR.ParserEBNF
open Yard.Generators.RNGLR.AST
type Token =
    | A of (int)
    | RNGLR_EOF of (int)

let genLiteral (str : string) (data : int) =
    match str.ToLower() with
    | x -> None
let tokenData = function
    | A x -> box x
    | RNGLR_EOF x -> box x

let numToString = function
    | 0 -> "error"
    | 1 -> "s"
    | 2 -> "yard_start_rule"
    | 3 -> "A"
    | 4 -> "RNGLR_EOF"
    | _ -> ""

let tokenToNumber = function
    | A _ -> 3
    | RNGLR_EOF _ -> 4

let isLiteral = function
    | A _ -> false
    | RNGLR_EOF _ -> false

let getLiteralNames = []
let mutable private cur = 0
let leftSide = [|1; 2|]
let startRule = 1

let acceptEmptyInput = true

let defaultAstToDot =
    (fun (tree : Yard.Generators.RNGLR.AST.Tree<Token>) -> tree.AstToDot numToString tokenToNumber leftSide)

let private lists_gotos = [|1; 2|]
let private stackArrays = [|[|0|]|]
let private stackSets = stackArrays |> Array.map Set.ofArray
let private small_gotos =
        [|2; 65536; 0; 196609; 65536; 131073; 196609; 0|]
let gotos = Array.zeroCreate 3
for i = 0 to 2 do
        gotos.[i] <- Array.create 5 None
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
let private lists_reduces = [|[|1|]; [|0|]|]
let private small_reduces =
        [|1; 262144; 131074; 196609; 262145|]
let reduces = Array.zeroCreate 3
for i = 0 to 2 do
        reduces.[i] <- Array.zeroCreate 5
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
let private lists_zeroReduces = [|[|0|]|]
let private small_zeroReduces =
        [|2; 196608; 262144|]
let zeroReduces = Array.zeroCreate 3
for i = 0 to 2 do
        zeroReduces.[i] <- Array.zeroCreate 5
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
let private small_acc = [1; 0]
let private accStates = Array.zeroCreate 3
for i = 0 to 2 do
        accStates.[i] <- List.exists ((=) i) small_acc
let eofIndex = 4
let errorIndex = 0
let private parserSource = new ParserSourceEBNF<Token> (gotos, reduces, zeroReduces, stackSets, accStates, leftSide, startRule, eofIndex, tokenToNumber, acceptEmptyInput, numToString, errorIndex)
let buildAst : (seq<'TokenType> -> ParseResultEBNF<Token>) =
    buildAst<Token> parserSource


