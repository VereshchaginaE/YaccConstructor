namespace Yard.Generators.RNGLR.DFA

open Yard.Core.IL
open Yard.Core.IL.Production
open System.Collections.Generic
open Yard.Generators.RNGLR.GrammarWithDFARightSide
open Yard.Generators.RNGLR

type NumberedRulesDFA (ruleList : Rule.t<Source.t,Source.t> list, indexator : Indexator, caseSensitive) =
    let transformLiteral = Indexator.transformLiteral caseSensitive
    let rules = ruleList |> Array.ofList
    let start =
        rules
        |> Array.findIndex (fun rule -> rule.isStart)
    let left = rules |> Array.map (fun x -> x.name.text |> indexator.nonTermToIndex)
    let right =
        let bodyToDFA a_firstStateNumber body = 
            
            let rec regExToDFA (firstState : Vertex<_,_>) lastState (stateToVertex : ResizeArray<Vertex<_,_>>) = function
                |PAlt (x,y) ->
                    let lastSt = regExToDFA firstState lastState stateToVertex x
                    regExToDFA firstState lastState stateToVertex y
                |PSeq (s, _, _) ->
                    let firstSt = ref firstState
                    let seqToDFA = function
                        | x::_::xs ->
                            firstSt := regExToDFA !firstSt None stateToVertex x
                            !firstSt
                        | x::[] ->
                            regExToDFA !firstSt lastState stateToVertex x
                        | x -> failwithf "Unexpected construction %A" x
                    s |> List.map (fun (x : elem<_,_>) -> x.rule) |> seqToDFA
                |PToken token -> 
                    let lastSt = 
                        match lastState with
                        | Some x ->
                            x
                        | None -> 
                            let x = new Vertex<_,_>(firstState.label + 1)
                            stateToVertex.Add(x)
                            x
                    firstState.addEdge(new Edge<_,_>(lastSt, indexator.termToIndex token.text))
                    lastSt
                |PRef (nTerm, _) ->
                    let lastSt = 
                        match lastState with
                        | Some x ->
                            x
                        | None -> 
                            let x = new Vertex<_,_>(firstState.label + 1)
                            stateToVertex.Add(x)
                            x
                    firstState.addEdge(new Edge<_,_>(lastSt, indexator.nonTermToIndex nTerm.text))
                    lastSt
                |PMany x -> 
                    regExToDFA firstState (Some firstState) stateToVertex x
                    
                //|PMetaRef
                |PLiteral lit -> 
                    let lastSt = 
                        match lastState with
                        | Some x ->
                            x
                        | None -> 
                            let x = new Vertex<_,_>(firstState.label + 1)
                            stateToVertex.Add(x)
                            x
                    firstState.addEdge(new Edge<_,_>(lastSt, indexator.literalToIndex <| transformLiteral lit.text))
                    lastSt
                //|PRepet
                //|PPerm
                //|PSome
                //|POpt
                | x -> failwithf "Unexpected construction %A" x
            
            let firstState = new Vertex<int, int>(a_firstStateNumber) 
            let stateToVertex = new ResizeArray<Vertex<_,_>>()
            regExToDFA firstState None stateToVertex body |> ignore
            let prod : DFAProduction.t = {firstStateNumber = a_firstStateNumber; numberOfStates = stateToVertex.Count; startState = firstState; stateToVertex = stateToVertex |> Seq.toArray}
            prod

        let firstState = ref 0
        ruleList
        |> List.fold
            (fun (res : DFARule.t<_,_> list) rule->
                let dfaRule : DFARule.t<_,_> =
                    {
                        name = rule.name;
                        args = rule.args;
                        body = bodyToDFA !firstState rule.body;
                        isStart = rule.isStart;
                        isPublic = rule.isPublic;
                        metaArgs = rule.metaArgs
                    }
                firstState := !firstState + dfaRule.body.numberOfStates
                dfaRule::res
            )
            []
        |> Array.ofList

    let rulesWithLeft =
        let result : int list array = Array.create indexator.fullCount []
        for i in 0..rules.Length-1 do
            result.[left.[i]] <- i::result.[left.[i]]
        result
        |> Array.map (List.rev >> Array.ofList)

    (*let errRulesExists = 
        let errInd = indexator.errorIndex
        let res = ref false
        for i in 0..right.GetLength(0)-1 do
            if not !res && Array.exists((=) errInd) right.[i] then
                res := true
        !res*)

    member this.rulesCount = rules.Length
    member this.startRule = start
    member this.startSymbol = left.[start]
    member this.leftSide num = left.[num]
    member this.leftSideArr = left
    member this.rightSide num = right.[num]
    member this.numberOfStates num = right.[num].body.numberOfStates
    member this.symbol rule pos = right.[rule].body.stateToVertex.[pos]
    member this.rulesWithLeftSide symbol = rulesWithLeft.[symbol]
    //member this.errorRulesExists = errRulesExists