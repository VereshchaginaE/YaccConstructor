module Yard.Generators.RNGLR.ToDFAConvert

open Yard.Core.IL
open Yard.Core.IL.Production
open System.Collections.Generic
open Yard.Generators.RNGLR.GrammarWithDFARightSide

let ToDFAConvert (ruleList : Rule.t<_,_> list) =
   
    let bodyToDFA  = function
        |PAlt
        |PSeq
        |PToken 
        |PRef
        |PMany
        //|PMetaRef
        //|PLiteral
        //|PRepet
        //|PPerm
        //|PSome
        //|POpt
        
    
    ruleList
    |> List.fold
        (fun (res : DFARule.t<_,_> list) rule->
            let DFARule : DFARule.t<_,_> =
                {
                    name = rule.name;
                    args = rule.args;
                    body = bodyToDFA rule.body;
                    isStart = rule.isStart;
                    isPublic = rule.isPublic;
                    metaArgs = rule.metaArgs
                }
            DFARule::res
        )
        []
