﻿// Generator.fs
//
// Copyright 2009 Semen Grigorev
//
// This program is free software; you can redistribute it and/or
// modify it under the terms of the GNU General Public License
// as published by the Free Software Foundation.

#light

module Generator

open IL.Production
open IL.Rule
open IL
open Grammar.Item
open Grammar.Symbol

let start_time = ref System.DateTime.Now
let end_time   = ref System.DateTime.Now      

let items,_grammar,(_generate:IL.Grammar.t<IL.Source.t,IL.Source.t>->unit) =
    let _items:(Set<Grammar.Item.t<Source.t>> ref) = ref Set.Empty
    let _grammar:IL.Grammar.t<IL.Source.t,IL.Source.t> ref = ref[]
    let generate rules =
       _grammar := rules;
       let rules_map  = List.zip ([0..(List.length rules)-1])rules
       _items:= List.map (fun (i,rl) -> 
                let (itm,s,f) = FinitAutomata.FA_rules(rl.body) 
                let get_symb =  function 
                                Some(PLiteral(s)|PToken(s)|PRef(s,_)) -> Some(Terminal(s))                                                                                  
                                | _ -> failwith "Generator error."                                          
#if DEBUG
                Log.print_item itm s f;
#endif
                Set.fold (fun buf (a,b,c) ->                                                    
                                   let new_item  item_num next_num =
                                      {prod_num = i;
                                       prod_name = rl.name;
                                       item_num = item_num;
                                       symb = get_symb b;                                                                           
                                       next_num = next_num;
                                       s=s;
                                       f=f                                                                                          
                                      }
                                   buf + Set.singleton(new_item a (Some(c)))+
                                    if Set.exists ((=)c) f
                                    then Set.singleton(new_item c None)
                                    else Set.empty 
                                   )Set.empty itm)rules_map
    |> Set.unionMany
    let items () = !_items
    let grammar () = !_grammar
    items,grammar,generate
    
let closure q = 
    let rec inner_closure i q = 
      if i = Set.count q 
      then q
      else
        let next_cl f = inner_closure (i+1) (q + Set.filter f (items()))
        let closure_one elt = 
            let el_for_cl = List.nth (Set.to_list q) i 
            elt.prod_name = Utils.getText el_for_cl.symb && elt.item_num = elt.s 
        next_cl closure_one                                                                                 
    in
    inner_closure 0 q
        
let get_closure_set,calc_closure_set = 
#if DEBUG
  Log.print_items (items())
#endif
  let _closure_set = ref( dict <| []);
  let calculate_clousure_set () = _closure_set:=dict <| Set.map (fun x -> x, closure (Set.singleton x)) (items())                
  let closure_set () = !_closure_set
  closure_set,calculate_clousure_set

let goto_set ()=     
    let eql = function 
        | (PToken x |PLiteral x), Some(Terminal y | Nonterminal y ) -> x=y
        | _ -> false
    in 
    let make_goto q x =  
        calc_closure_set()
        let closure = Set.fold (fun y x -> y + get_closure_set().[x]) Set.empty q
        Set.unionMany [for item in closure do if eql(x, item.symb) then yield Utils.nextItem item (items())]
    let toString = function | PToken y |PLiteral y | PRef (y,_) -> Source.toString y 
                            | _ -> ""
    let goto_data symbol item = 
        let gt = make_goto (Set.singleton item) symbol
        hash(item, toString symbol),gt
    dict <| List.fold (fun buf symbol -> buf@[for item in (items()) -> goto_data symbol item]) 
                      [] (GrammarPreparer.get_all_t(_grammar()))
                       
let generate (input_grammar:IL.Definition.t<Source.t,Source.t>)= 
    let head,grammar,foot = GrammarPreparer.prepare input_grammar
    _generate(ExpandMeta.expandMetaRules grammar);
#if DEBUG
    printf "Input extracted rules \n %A \n"<| grammar;
    printf "Transformed grammar \n %A\n" <|(ExpandMeta.expandMetaRules grammar)
    printf "\n Token list: \n %A " <|(GrammarPreparer.get_all_t(_grammar()))
    printf "\n Start Nterms: \n %A " <|GrammarPreparer.get_start_nterms (_grammar())
#endif            
    IO.writeValue "goto.dta" (System.Linq.Enumerable.ToList(goto_set())) ; 
    IO.writeValue "items.dta" (items());
    IO.writeValue "start_nterms.dta" (GrammarPreparer.get_start_nterms (_grammar()));
    //PrettyPrinter.out := IO.text_writer "test1.fs";
    //PrettyPrinter.print_header "test" ["IL"];
    //(!PrettyPrinter.out).Close();
    printfn "End working time: %A Total: %A" System.DateTime.Now (System.DateTime.Now - (!start_time));