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

module Yard.Generators.RNGLR.StatesEBNF

open System.Collections.Generic
open Yard.Generators.RNGLR.FinalGrammarNFA
open Yard.Generators.RNGLR
open Yard.Generators.RNGLR.States

//type Item = Kernel * Set<int>

type KernelInterpreter =
    (*static member inline toKernel (prod,pos) = (prod <<< 16) ||| pos
    static member inline getProd kernel = kernel >>> 16
    static member inline getPos kernel = kernel &&& ((1 <<< 16) - 1)
    static member inline unzip kernel = (KernelInterpreter.getProd kernel, KernelInterpreter.getPos kernel)
    static member inline kernelsOfState = fst
    static member inline lookAheadsOfState = snd*)

    static member inline nextPos (grammar : FinalGrammarNFA) kernel =
        let rule = KernelInterpreter.getProd kernel
        let pos = KernelInterpreter.getPos kernel
        let nextStates = grammar.nextPositions.[rule].[pos]
        nextStates |> Set.map (fun x -> KernelInterpreter.toKernel(rule, x))

    static member inline symbol (grammar : FinalGrammarNFA) kernel =
        let rule = KernelInterpreter.getProd kernel
        let pos = KernelInterpreter.getPos kernel
        if pos = grammar.rules.numberOfStates rule - 1 then grammar.indexator.eofIndex
        else grammar.rules.symbol rule pos

    static member symbolAndLookAheads (grammar : FinalGrammarNFA) (kernel, endLookeheads) =
        let rule = KernelInterpreter.getProd kernel
        let pos = KernelInterpreter.getPos kernel
        if pos = grammar.rules.numberOfStates rule - 1 then
            grammar.indexator.eofIndex, Set.empty
        else
            let lookAheads =
                let nextPositions = grammar.nextPositions.[rule].[pos]
                let hasEpsilonTail = ref false
                let foldFun acc x =
                     if grammar.hasEpsilonTail.[rule].[x] then hasEpsilonTail := true
                     Set.union grammar.followSet.[rule].[x] acc
                nextPositions |> Set.fold foldFun Set.empty
                |> Set.remove grammar.indexator.epsilonIndex
                |> fun x -> if !hasEpsilonTail then Set.union x endLookeheads else x
            grammar.rules.symbol rule pos, lookAheads

type StackLabel =
    | Stack of Set<int>
    | DontStack
    | StackingConflict of Set<int>

type ReduceLabel =
    | Reduce
    | StackReduce

type StatesInterpreterEBNF (stateToVertex : Vertex<int,int * StackLabel>[], stateToMainKernels : Kernel[][], stateToMainLookahead : Set<int>[][], stateToDerivedKernels : Kernel[][], stateToDerivedLookahead : Set<int>[][]) =
    member this.count = stateToVertex.Length
    member this.vertex i = stateToVertex.[i]
    member this.mainKernels i = stateToMainKernels.[i]
    member this.mainLookaheads i = stateToMainLookahead.[i]
    member this.derivedKernels i = stateToDerivedKernels.[i]
    member this.derivedLookaheads i = stateToDerivedLookahead.[i]
    
let buildStatesNFA outTable (grammar : FinalGrammarNFA) = //(kernelIndexator : KernelIndexator) =
    let nextIndex, vertexCount =
        let num = ref -1
        (fun () -> incr num; !num)
        , (fun () -> !num + 1)
    let kernelsToVertex = new Dictionary<string, Vertex<int,int * StackLabel>>()
    let vertices = new ResizeArray<Vertex<int,int * StackLabel> >()
    let stateToMainKernels = new ResizeArray<Kernel[]>()
    let stateToMainLookahead = new ResizeArray<Set<int>[] >()
    let stateToDerivedKernels = new ResizeArray<Kernel[]>()
    let stateToDerivedLookahead = new ResizeArray<Set<int>[] >()
    let curSymbol kernel = KernelInterpreter.symbol grammar kernel
    let symbolAndLookAheads (*kernel lookAheads*) = KernelInterpreter.symbolAndLookAheads grammar
    let wasEdge = new ResizeArray<Set<int> >()
    let wasNonTerm = Array.zeroCreate grammar.indexator.fullCount
    let wasNTermSymbol : bool[,] = Array2D.zeroCreate grammar.indexator.fullCount grammar.indexator.fullCount
    let addedNTermsSymbols = new ResizeArray<_>(grammar.indexator.fullCount * grammar.indexator.fullCount)

    let closure (mainKernelsAndLookAheads : (Kernel * Set<int>)[]) =
        //eprintf "%d " <| addedNTermsSymbols.Capacity
        let mutable resultMain = mainKernelsAndLookAheads |> Array.map fst |> Set.ofArray
        let mutable resultDerived : Set<Kernel>  = Set.empty
        let mainKernelToLookAhead = new Dictionary<_,_> ()// Array.zip kernels lookAheads |> dict
        let derivedKernelToLookAhead = new Dictionary<_,_> ()
        let queue = new Queue<_>()
        let enqueue (nonTerm, symbolSet) = 
            let checkWas symbol =
                if not wasNTermSymbol.[nonTerm, symbol] then
                    wasNTermSymbol.[nonTerm, symbol] <- true
                    addedNTermsSymbols.Add(nonTerm, symbol)
                    wasNonTerm.[nonTerm] <- true
                    true
                else false
            let newSymbolSet = Set.filter checkWas symbolSet
            queue.Enqueue (nonTerm, newSymbolSet)
        for i = 0 to mainKernelsAndLookAheads.Length - 1 do
            if (fst mainKernelsAndLookAheads.[i] |> mainKernelToLookAhead.ContainsKey |> not) then
                mainKernelToLookAhead.Add (mainKernelsAndLookAheads.[i])
            else
                mainKernelToLookAhead.[fst mainKernelsAndLookAheads.[i]] 
                    <- Set.union mainKernelToLookAhead.[fst mainKernelsAndLookAheads.[i]] (snd mainKernelsAndLookAheads.[i])
            enqueue <| symbolAndLookAheads mainKernelsAndLookAheads.[i]
        while queue.Count > 0 do
            let nonterm, symbolSet = queue.Dequeue()
            for rule in grammar.rules.rulesWithLeftSide nonterm do
                let kernelsAndStarts = grammar.startPositions.[rule] |> Set.map (fun x -> KernelInterpreter.toKernel (rule,x), x)
                for (kernel, startPosition) in kernelsAndStarts do                
                    let newSymbolSet = 
                        if not <| resultDerived.Contains kernel then
                            resultDerived <- resultDerived.Add kernel
                            derivedKernelToLookAhead.Add(kernel, symbolSet)
                            symbolSet
                        else
                            let newSymbolSet = Set.difference symbolSet derivedKernelToLookAhead.[kernel]
                            derivedKernelToLookAhead.[kernel] <- Set.union derivedKernelToLookAhead.[kernel] newSymbolSet
                            newSymbolSet
                    if (*grammar.rules.length rule > 0 &&*) (not newSymbolSet.IsEmpty || not wasNonTerm.[grammar.rules.symbol rule startPosition]) then
                        enqueue <| symbolAndLookAheads (kernel, newSymbolSet)
        for (f,s) in addedNTermsSymbols do
            wasNonTerm.[f] <- false
            wasNTermSymbol.[f,s] <- false
        addedNTermsSymbols.Clear()
        (Array.ofSeq resultMain, Array.ofSeq resultDerived)
        |> (fun (mks, dks) -> mks , mks |> Array.map (fun x -> mainKernelToLookAhead.[x]), dks , dks |> Array.map (fun x -> derivedKernelToLookAhead.[x]))

    let incount = ref 0
    (*let rec dfsLALR initKernelsAndLookAheads =
        incr incount
        //if !incount % 100 = 0 then eprintf "%d " !incount
        let kernels,lookaheads = initKernelsAndLookAheads |> closure
        let key = String.concat "|" (kernels |> Array.map string)
        let vertex, newLookAheads, needDfs =
            if kernelsToVertex.ContainsKey key then
                let vertex = kernelsToVertex.[key]
                let alreadySets = stateToLookahead.[vertex.label]
                let mutable needDfs = false
                let diff = Array.zeroCreate kernels.Length
                for i = 0 to kernels.Length - 1 do
                    let diffSet = Set.difference lookaheads.[i] alreadySets.[i]
                    alreadySets.[i] <- Set.union alreadySets.[i] diffSet
                    if not diffSet.IsEmpty then needDfs <- true
                    diff.[i] <- diffSet
                vertex, diff, needDfs
            else
                let vertex = new Vertex<int,int>(nextIndex())
                wasEdge.Add Set.empty
                vertices.Add vertex
                kernelsToVertex.[key] <- vertex
                stateToKernels.Add kernels
                stateToLookahead.Add lookaheads
                vertex, lookaheads, true
        if needDfs then
            for i = 0 to grammar.indexator.fullCount - 1 do
                if i <> grammar.indexator.eofIndex then
                    let mutable newSymbols = false
                    let mutable count = 0
                    for j = 0 to kernels.Length-1 do
                        if curSymbol kernels.[j] = i then
                            if not newLookAheads.[j].IsEmpty then newSymbols <- true
                            count <- count + 1
                    if count > 0 && newSymbols then
                        let destStates = Array.zeroCreate count
                        let mutable curi = 0
                        for j = 0 to kernels.Length-1 do
                            if curSymbol kernels.[j] = i then
                                destStates.[curi] <- KernelInterpreter.incPos kernels.[j], newLookAheads.[j]
                                curi <- curi + 1
                        let newVertex : Vertex<_,_> = dfsLALR destStates
                        if not <| wasEdge.[vertex.label].Contains newVertex.label then
                            wasEdge.[vertex.label] <- wasEdge.[vertex.label].Add newVertex.label
                            vertex.addEdge <| new Edge<_,_>(newVertex, i)
        vertex*)

    let rec dfsLR initKernelsAndLookAheads =
        incr incount
        if !incount % 5000 = 0 then eprintf "%d " !incount
        let mainKernels,mainLookaheads,derivedKernels,derivedLookaheads = initKernelsAndLookAheads |> closure
        let setToStr = Set.map (sprintf "%d") >> String.concat ","
        let key = String.concat "|" (Array.map2 (fun x y -> sprintf "%d(%s)" x (setToStr y)) mainKernels mainLookaheads)
        //printfn "%s" key
        if kernelsToVertex.ContainsKey key then
            kernelsToVertex.[key]
        else
            let vertex = new Vertex<int,int * StackLabel>(nextIndex())
            //wasEdge.Add Set.empty
            vertices.Add vertex
            kernelsToVertex.[key] <- vertex
            stateToMainKernels.Add mainKernels
            stateToMainLookahead.Add mainLookaheads
            stateToDerivedKernels.Add derivedKernels
            stateToDerivedLookahead.Add derivedLookaheads
            for i = 0 to grammar.indexator.fullCount - 1 do
                if i <> grammar.indexator.eofIndex then
                    let destStates = new ResizeArray<int * Set<int>>()
                    let dontStack = ref false
                    let mutable stackSet = Set.empty
                    for j = 0 to mainKernels.Length-1 do
                            if curSymbol mainKernels.[j] = i && not mainLookaheads.[j].IsEmpty then
                                let nextKernels = KernelInterpreter.nextPos grammar mainKernels.[j]
                                dontStack := true
                                for nextKernel in nextKernels do
                                    destStates.Add (nextKernel, mainLookaheads.[j])
                    for j = 0 to derivedKernels.Length-1 do
                            if curSymbol derivedKernels.[j] = i && not derivedLookaheads.[j].IsEmpty then
                                let nextKernels = KernelInterpreter.nextPos grammar derivedKernels.[j]
                                stackSet <- Set.add (KernelInterpreter.getProd derivedKernels.[j]) stackSet
                                for nextKernel in nextKernels do
                                    destStates.Add (nextKernel, derivedLookaheads.[j])
                    if destStates.Count <> 0 then
                        let newVertex : Vertex<_,_> = destStates.ToArray() |> dfsLR
                        //wasEdge.[vertex.label] <- wasEdge.[vertex.label].Add newVertex.label
                        let stackLabel = 
                            if !dontStack then
                                if  stackSet.IsEmpty then
                                    DontStack
                                else StackingConflict stackSet
                            else
                                Stack stackSet
                        vertex.addEdge <| new Edge<_,_>(newVertex, (i, stackLabel))
            vertex

    let initKernels = grammar.startPositions.[grammar.startRule] |> Set.map (fun x -> KernelInterpreter.toKernel(grammar.startRule, x))
    let initLookAhead = Set.ofSeq [grammar.indexator.eofIndex]
    let initKernelsAndLookAheads = Set.map (fun x -> (x, initLookAhead)) initKernels |> Set.toArray
    initKernelsAndLookAheads
    |> match outTable with
        | LALR //-> dfsLALR
        | LR -> dfsLR
    |> ignore
    //eprintfn "Dfs calls count: %d" !incount
    eprintfn "States count: %d" <| vertexCount()
    //printfn "rules count = %d; states count = %d" grammar.rules.rulesCount <| vertexCount()
        (*
    let printSymbol (symbol : int) =
        if symbol < grammar.indexator.nonTermCount then
            grammar.indexator.indexToNonTerm symbol
        elif symbol >= grammar.indexator.termsStart && symbol <= grammar.indexator.termsEnd then
            grammar.indexator.indexToTerm symbol
        else grammar.indexator.indexToLiteral symbol
    printfn "\nstates:"
    for i = 0 to vertexCount()-1 do
        printfn "==============================\n%d:" i
        let kernels = stateToKernels.[i]
        let lookaheads = stateToLookahead.[i]
        for k = 0 to kernels.Length-1 do
            printfn "(%d,%d) [%s]" (KernelInterpreter.getProd kernels.[k]) (KernelInterpreter.getPos kernels.[k])
                <| (lookaheads.[k] |> List.ofSeq
                    |> List.map (fun x -> printSymbol x)
                    |> String.concat "," )
        printfn "------------------------------"
        let vertex = vertices.[i]
        for edge in vertex.outEdges do
            printf "(%s,%d) " (printSymbol edge.label) edge.dest.label
        printfn ""*)
    new StatesInterpreterEBNF(vertices.ToArray(), stateToMainKernels.ToArray(), stateToMainLookahead.ToArray(), stateToDerivedKernels.ToArray(), stateToDerivedLookahead.ToArray())
