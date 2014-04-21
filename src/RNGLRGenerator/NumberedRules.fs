﻿//   Copyright 2013, 2014 YaccConstructor Software Foundation
//
//   Licensed under the Apache License, Version 2.0 (the "License");
//   you may not use this file except in compliance with the License.
//   You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in writing, software
//   distributed under the License is distributed on an "AS IS" BASIS,
//   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//   See the License for the specific language governing permissions and
//   limitations under the License.

namespace Yard.Generators.RNGLR

open Yard.Core.IL.Production;
open Yard.Core.IL;
open Yard.Generators.RNGLR;

type NumberedRules (ruleList : Rule.t<Source.t,Source.t> list, indexator : Indexator, caseSensitive) =
    let transformLiteral = Indexator.transformLiteral caseSensitive
    let rules = ruleList |> Array.ofList
    let start =
        rules
        |> Array.findIndex (fun rule -> rule.isStart)
    let left = rules |> Array.map (fun x -> x.name.text |> indexator.nonTermToIndex)
    let right =
        let rec transformBody acc (*body*) = function
            | PRef (nTerm,_) -> (*printfn "N %s" <| fst nTerm;*) (indexator.nonTermToIndex nTerm.text)::acc
            | PToken token -> (*printfn "T %s" <| fst token;*) (indexator.termToIndex token.text)::acc
            | PLiteral lit -> (*printfn "L %s" <| fst lit;*) (indexator.literalToIndex <| transformLiteral lit.text)::acc
            | PSeq (s,_,_) -> List.foldBack (fun x acc -> transformBody acc x.rule) s acc
            | PMany x -> transformBody acc x
            | _ -> failwith "Unexpected construction in grammar"
        rules
        |> Array.map
            (fun x ->
                transformBody [] x.body 
                //|> List.rev
                |> Array.ofList )
        //|> (fun x -> printfn "======="; x)
    let rulesWithLeft =
        let result : int list array = Array.create indexator.fullCount []
        for i in 0..rules.Length-1 do
            result.[left.[i]] <- i::result.[left.[i]]
        result
        |> Array.map (List.rev >> Array.ofList)

    let errRulesExists = 
        let errInd = indexator.errorIndex
        let res = ref false
        for i in 0..right.GetLength(0)-1 do
            if not !res && Array.exists((=) errInd) right.[i] then
                res := true
        !res
        
    member this.rulesCount = rules.Length
    member this.startRule = start
    member this.startSymbol = left.[start]
    member this.leftSide num = left.[num]
    member this.leftSideArr = left
    member this.rightSide num = right.[num]
    member this.length num = right.[num].Length
    member this.symbol rule pos = right.[rule].[pos]
    member this.rulesWithLeftSide symbol = rulesWithLeft.[symbol]
    member this.errorRulesExists = errRulesExists