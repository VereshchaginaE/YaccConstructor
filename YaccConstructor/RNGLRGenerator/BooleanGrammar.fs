module Yard.Generators.RNGLR.BooleanGrammar

//open Yard.Generators.RNGLR.States

let algorithm  =
    let mutable isModified = true
    while isModified do
        isModified <- false
        
