﻿namespace Yard.Generators.RNGLR.EBNF

open Yard.Generators.RNGLR.FinalGrammarNFA
open Yard.Generators.RNGLR.States
open Yard.Generators.RNGLR.StatesEBNF
open Yard.Generators.RNGLR

module StackLabel =
    type t =
        | DontStack
        | Stack of int[]
        | StackingConflict of int[]

    let GetStackLabel label rules =
        match label with
        | 0 -> DontStack
        | 1 -> Stack rules
        | 2 -> StackingConflict rules
        | _ -> failwith "GetStackLabel wrong argument"

type TablesEBNF(grammar : FinalGrammarNFA, states : StatesInterpreterEBNF) =
    let _reduces, _gotos, _acc =
        let symbolCount = grammar.indexator.fullCount
        let reduces : list<int * ReduceLabel>[,] = Array2D.create states.count symbolCount []
        let gotos : list<int * StackLabel>[,] = Array2D.create states.count symbolCount []
        let mutable acc = []
        if grammar.canInferEpsilon.[grammar.rules.leftSide grammar.startRule] then acc <- (*startState*)0::acc
        let endRule = KernelInterpreter.toKernel (grammar.startRule, grammar.rules.numberOfStates grammar.startRule - 1)
        for i = 0 to states.count-1 do
            let vertex = states.vertex i
            let mainKernels, mainLookaheads = states.mainKernels i, states.mainLookaheads i
            let derivedKernels, derivedLookaheads = states.derivedKernels i, states.derivedLookaheads i

            for e in vertex.outEdges do
                let symbol, stackLabel = e.label
                gotos.[i, symbol] <- (e.dest.label, stackLabel)::gotos.[i, symbol]
                if gotos.[i, symbol].Length > 1 then
                    eprintfn "Several gotos form state %d on symbol %d: %A" i symbol gotos.[i, symbol]
            
            for j = 0 to mainKernels.Length - 1 do
                let k, la = mainKernels.[j], mainLookaheads.[j]
                let prod, pos = KernelInterpreter.unzip k
                if k = endRule then acc <- i::acc
                elif grammar.hasEpsilonTail.[prod].[pos] then
                    for symbol in la do 
                        reduces.[i, symbol] <- (prod, Reduce)::reduces.[i, symbol]
            
            for j = 0 to derivedKernels.Length - 1 do
                let k, la = derivedKernels.[j], derivedLookaheads.[j]
                let prod, pos = KernelInterpreter.unzip k
                if k = endRule then acc <- i::acc
                elif grammar.hasEpsilonTail.[prod].[pos] then
                    for symbol in la do 
                        reduces.[i, symbol] <- (prod, StackReduce)::reduces.[i, symbol]
        reduces, gotos, acc

    member this.reduces = _reduces
    member this.gotos = _gotos
    member this.acc = _acc