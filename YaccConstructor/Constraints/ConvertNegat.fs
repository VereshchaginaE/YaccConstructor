module Yard.Core.ConstraintsImpl.ConvertNegat

open Yard.Core
open IL.Production
open Yard.Core.ConstraintsImpl.Common

let private isNegat = function
        | PNegat _ -> true
        | _ -> false

let private checker grammar = not <| existsProd isNegat grammar

let convertNegat = new Constraint("NoNegat", checker, Conversions.ConvertBooleanGrammar.ConvertBooleanGrammar())

