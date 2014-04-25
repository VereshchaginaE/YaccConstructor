//   Copyright 2013, 2014 YaccConstructor Software Foundation
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

module Yard.Generators.RNGLR.SymbolSetsNFA

open Yard.Generators.RNGLR
//open Yard.Generators.RNGLR.Epsilon
open Yard.Generators.RNGLR.GrammarWithDFARightSide
open Yard.Generators.RNGLR.DFA

let firstSetNFA (rules : NumberedRulesDFA) (indexator : Indexator) (canInferEpsilon : bool[]) =
    let result : Set<int>[] = Array.create indexator.fullCount Set.empty
    
    let calc term = 
    //for term = indexator.nonTermCount to indexator.fullCount-1 do
        let was : bool[] = Array.zeroCreate indexator.fullCount
        let rec dfs u = 
            result.[u] <- result.[u].Add term
            was.[u] <- true
                        
            let rec check (prod : DFAProduction.t) = 
                let rec checkOutSymbols (state : Vertex<_,_>) =
                    let rec checkEdges = function
                        |[] -> false
                        | (x : Edge<_,_>) :: xs -> 
                            if (x.label = u) then true
                            elif (canInferEpsilon.[x.label] && state.label < x.dest.label) then checkOutSymbols x.dest || checkEdges xs
                            else checkEdges xs
                    if state.label >= prod.numberOfStates then false
                    else state.outEdges |> List.ofSeq |> checkEdges
                checkOutSymbols prod.startState
                    

            for i = 0 to rules.rulesCount-1 do
                let v = rules.leftSide i
                if (not was.[v]) then
                    if (check (rules.rightSide i)) then
                      dfs v
        dfs term

    calc indexator.errorIndex
    for term = indexator.nonTermCount to indexator.fullCount-1 do
        calc term
    result

(*let followSetNFA (rules : NumberedRulesDFA) (indexator : Indexator) (canInferEpsilon : bool[]) (firstSet : Set<int>[]) =
    let result : Set<int>[][] = Array.zeroCreate rules.rulesCount
    
    let rec followForState (state : Vertex<_,_>) fSet stepped =
        if stepped |> List.exists (fun x -> x = state.label) then ()
        else
            for edge in state.outEdges do
                if (edge.label = indexator.epsilonIndex) then followForState edge.dest fSet (state.label::stepped)
                else fSet := Set.union !fSet firstSet.[edge.label]
    
    for i = 0 to rules.rulesCount-1 do
        result.[i] <- Array.create (rules.numberOfStates i) Set.empty
        
        for j = rules.numberOfStates i - 1 downto 0 do
            let curSet = ref Set.empty
            result.[i].[j] <- !curSet
            let value = rules.symbol i j
            followForState value curSet []
    result*)

let followSetNFA (rules : NumberedRulesDFA) (indexator : Indexator) (canInferEpsilon : bool[]) (firstSet : Set<int>[]) =
    let result : Set<int>[][] = Array.zeroCreate rules.rulesCount
        
    
    for i = 0 to rules.rulesCount-1 do
        result.[i] <- Array.create (rules.numberOfStates i) Set.empty
        let evaluateFollowWithoutReturns() =
            for j = rules.numberOfStates i - 1 downto 0 do
                result.[i].[j] <- Set.empty
                let state = rules.state i j
                for edge in state.outEdges |> List.ofSeq |> List.filter (fun (x : Edge<_,_>) -> state.label < x.dest.label) do
                    if (canInferEpsilon.[edge.label]) then 
                        result.[i].[j] <- Set.union result.[i].[j] result.[i].[rules.relativeStateNumber i edge.dest.label]
                    if (edge.label <> indexator.epsilonIndex) then 
                        result.[i].[j] <- Set.union result.[i].[j] firstSet.[edge.label]
        let rec addFollows() =
            let mutable modified = false
            for j = rules.numberOfStates i - 1 downto 0 do
                let state = rules.state i j
                for edge in state.outEdges do
                    let nextFollow = result.[i].[rules.relativeStateNumber i edge.dest.label]
                    if (canInferEpsilon.[edge.label] && not (Set.isSubset nextFollow result.[i].[j])) then
                        modified <- true
                        result.[i].[j] <- Set.union result.[i].[j] nextFollow
            if modified then addFollows()
        evaluateFollowWithoutReturns()
        addFollows()
    result
