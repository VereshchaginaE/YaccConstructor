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
            let nextStateNumber, vertexCount =
                let number = ref a_firstStateNumber
                (fun () -> incr number; !number),
                (fun () -> !number + 1 - a_firstStateNumber)
            let rec regExToDFA (firstState : Vertex<_,_>)  (stateToVertex : ResizeArray<Vertex<_,_>>)  = function
                |PAlt (x,y) ->
                    let lastStateX : Vertex<_,_> = regExToDFA firstState stateToVertex x 
                    let lastStateY = regExToDFA firstState stateToVertex y
                    let lastState = new Vertex<_,_>(nextStateNumber())
                    stateToVertex.Add(lastState)
                    lastStateX.addEdge(new Edge<_,_>(lastState, indexator.epsilonIndex))
                    lastStateY.addEdge(new Edge<_,_>(lastState, indexator.epsilonIndex))
                    lastState
                |PSeq (s, _, _) ->
                    match s with
                    | [] ->
                        let lastState = new Vertex<_,_>(nextStateNumber())
                        firstState.addEdge(new Edge<_,_>(lastState, indexator.epsilonIndex))
                        lastState
                    | _ ->                    
                        let seqToDFA fstState = regExToDFA fstState stateToVertex 
                        s |> List.map (fun (x : elem<_,_>) -> x.rule) |> List.fold seqToDFA firstState
                |PToken _ | PLiteral _ | PRef _ as x -> 
                    let index =
                        match x with
                        | PToken token -> indexator.termToIndex token.text
                        | PLiteral lit -> indexator.literalToIndex <| transformLiteral lit.text
                        | PRef (nTerm, _) -> indexator.nonTermToIndex nTerm.text
                        | _ -> failwithf "Unexpected construction"
                    let lastState = new Vertex<_,_>(nextStateNumber())
                    stateToVertex.Add(lastState)
                    firstState.addEdge(new Edge<_,_>(lastState, index))
                    lastState
                |PMany x -> 
                    let lastState = regExToDFA firstState stateToVertex x
                    lastState.addEdge(new Edge<_,_>(firstState, indexator.epsilonIndex))
                    firstState
                //|PMetaRef
                  
                //|PRepet
                //|PPerm
                //|PSome
                //|POpt
                | x -> failwithf "Unexpected construction %A" x
            
            let firstState = new Vertex<int, int>(a_firstStateNumber) 
            let stateToVertex = new ResizeArray<Vertex<_,_>>()
            regExToDFA firstState stateToVertex body|> ignore
            let prod : DFAProduction.t = {firstStateNumber = a_firstStateNumber; numberOfStates = vertexCount(); startState = firstState; stateToVertex = stateToVertex |> Seq.toArray}
            prod

        let firstState = ref 0
        ruleList
        |> List.map
            (fun rule->
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
                dfaRule
            )
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