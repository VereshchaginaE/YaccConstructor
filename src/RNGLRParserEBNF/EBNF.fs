module Yard.Generators.RNGLR.StackLabel

type StackLabel =
        | DontStack
        | Stack of int
        | StackingConflict of int

let GetStackLabel label rulesSetPtr =
    match label with
    | 0 -> DontStack
    | 1 -> Stack rulesSetPtr
    | 2 -> StackingConflict rulesSetPtr
    | _ -> failwith "GetStackLabel wrong argument"

