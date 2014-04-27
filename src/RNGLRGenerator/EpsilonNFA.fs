module Yard.Generators.RNGLR.EpsilonNFA

open Yard.Generators.RNGLR
open Yard.Generators.RNGLR.DFA
open Yard.Core.IL
open Yard.Core.IL.Production

let canInferEpsilonNFA (rules : NumberedRulesDFA) (indexator : Indexator) =
    let result : bool[] = Array.zeroCreate (indexator.fullCount + 1) //+1 for epsilon
    let mutable modified = true
    result.[indexator.errorIndex] <- true
    result.[indexator.epsilonIndex] <- true
    while modified do
        modified <- false
        for i in 0..rules.rulesCount-1 do
            if not result.[rules.leftSide i] then
                let rec checkEpsilon stateNum =
                    if stateNum = (rules.numberOfStates i) - 1 then true
                    else
                        let stateVertex = rules.state i stateNum
                        let rec checkEdges = function
                        |[] -> false
                        |(x : Edge<_,_>)::xs ->
                            if result.[x.label] && checkEpsilon x.dest.label then true
                            else checkEdges xs
                        stateVertex.outEdges |> List.ofSeq |> checkEdges
                if checkEpsilon 0 then
                    modified <- true
                    result.[rules.leftSide i] <- true
    result
