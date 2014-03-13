module Yard.Core.Conversions.ConvertBooleanGrammar

open Yard.Core
open Yard.Core.IL
open Yard.Core.IL.Production

//Conversion to disjunctive normal form
let private convertBooleanGrammar (ruleList: Rule.t<_,_> list) = 
    let  isLoop = ref false
    let rec convert = function
        | PConjuct(a, b) ->
                match (a, b) with
                | (PAlt(l, r), x) | (x, PAlt(l, r)) -> PAlt(convert <| PConjuct( l, x), convert <| PConjuct(r, x))
                | (POpt x, y) | (x, POpt y) -> POpt(convert <| PConjuct(x, y))   
                | (PMany x, y) -> PMany(convert <| PConjuct(PSome x, y))
                | (x, PMany y) -> PMany(convert <| PConjuct(x,PSome y))  
                | (PSome x, y) | (x, PSome y) -> PSome(convert <| PConjuct(x, y))
                | (PToken x, PToken y) -> PConjuct(PToken x,PToken y)
                | (x, y) -> match !isLoop with
                            | true -> isLoop := false
                                      PConjuct(convert x,convert y)
                            | false -> isLoop := true
                                       convert <| PConjuct(convert x,convert y)   
        | PNegat x ->
                match x with
                | PNegat(PNegat(s)) -> convert s
                | PAlt(l, r) -> convert <| PConjuct(convert <| PNegat l, convert <| PNegat r)
                | PConjuct(l, r) -> PAlt(convert <| PNegat l, convert <| PNegat r)
                | POpt n -> convert (PNegat <| convert n)
                | PMany n -> PMany (PNegat <| convert n)
                | PSome n -> convert <| PNegat (PMany <| convert n)
                | PToken a -> PNegat(PToken a)
                | s -> match !isLoop with
                            | true -> isLoop := false
                                      PNegat <| convert s
                            | false -> isLoop := true
                                       convert <| (PNegat <| convert s)
        | PAlt(l,r) -> PAlt(convert l, convert r)
        | PMany(x) -> PMany(convert x)
        | PSome(x) -> PSome(convert x)
        | POpt(x) -> POpt(convert x)
        | PSeq(l, a, b) when l.Length = 1 && a.IsNone -> convert l.[0].rule
        | PSeq(l, a, b) -> PSeq(List.map (fun x -> {x with rule = convert x.rule}) l, a, b)
        | x -> x
    ruleList |> List.map (fun rule -> {rule with body = convert rule.body})

type ConvertBooleanGrammar() = 
    inherit Conversion()
        override this.Name = "ConvertBooleanGrammar"
        override this.ConvertGrammar (grammar,_) = mapGrammar convertBooleanGrammar grammar

