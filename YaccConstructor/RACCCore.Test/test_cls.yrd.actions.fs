//this file was generated by RACC
//source grammar:..\Tests\RACC\test_cls\\test_cls.yrd
//date:12/13/2010 12:14:10

module RACC.Actions_Cls

open Yard.Generators.RACCGenerator

let value x =
    ((x:>Lexeme<string>).value)

let s0 expr = 
    let inner () = 
        match expr with
        | RESeq [x0] -> 
            let (lst) =
                let yardElemAction expr = 
                    match expr with
                    | REClosure(lst) -> 
                        let yardClsAction expr = 
                            match expr with
                            | RESeq [x0] -> 
                                let (m) =
                                    let yardElemAction expr = 
                                        match expr with
                                        | RELeaf tMULT -> tMULT :?> 'a
                                        | x -> "Unexpected type of node\nType " + x.ToString() + " is not expected in this position\nRELeaf was expected." |> failwith

                                    yardElemAction(x0)
                                (m)
                            | x -> "Unexpected type of node\nType " + x.ToString() + " is not expected in this position\nRESeq was expected." |> failwith

                        List.map yardClsAction lst 
                    | x -> "Unexpected type of node\nType " + x.ToString() + " is not expected in this position\nREClosure was expected." |> failwith

                yardElemAction(x0)
            (List.map value lst |> String.concat ";")
        | x -> "Unexpected type of node\nType " + x.ToString() + " is not expected in this position\nRESeq was expected." |> failwith
    box (inner ())

let ruleToAction = dict [|("s",s0)|]

