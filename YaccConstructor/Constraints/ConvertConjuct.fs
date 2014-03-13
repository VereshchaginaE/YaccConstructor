module Yard.Core.ConstraintsImpl.ConvertConjuct

open Yard.Core
open IL.Production
open Yard.Core.ConstraintsImpl.Common

let private checker grammar =
    let isConjuct = function PConjuct _ -> true | _ -> false
    not <| existsProd isConjuct grammar

let convertConjuct = new Constraint("Conjuct", checker, Conversions.ConvertBooleanGrammar.ConvertBooleanGrammar())
