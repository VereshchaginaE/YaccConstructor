
# 2 "Parser.fs"
module Yard.Frontends.YardFrontend.GrammarParser
#nowarn "64";; // From fsyacc: turn off warnings that type variables used in production annotations are instantiated to concrete type
open Yard.Generators.RNGLR.Parser
open Yard.Generators.RNGLR
open Yard.Generators.RNGLR.AST

# 1 "Parser.fsy"

//  Copyright 2009 Jake Kirilenko
//
//  This file is part of YaccConctructor.
//
//  YaccConstructor is free software: you can redistribute it and/or modify
//  it under the terms of the GNU General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.
//
//  This program is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU General Public License for more details.
//
//  You should have received a copy of the GNU General Public License
//  along with this program.  If not, see <http://www.gnu.org/licenses/>.

#nowarn "62";; 
open Microsoft.FSharp.Text
open Yard.Core.IL
open Yard.Core
open Yard.Core.IL.Production
open Yard.Core.IL.Grammar
open Yard.Core.IL.Definition
open System.Text.RegularExpressions
 
type Range = struct
    val Start: Lexing.Position
    val End: Lexing.Position

    new (start,end_) = {Start = start; End = end_}
end

exception ParseError of Source.t * string
let parseFile = ref Unchecked.defaultof<_>
let currentFilename = ref ""
let allPublic = ref false
let o2l = function Some x -> [x] | None -> []
let getList = function Some x -> x | None -> []
let fst_ (x,_,_) = x
let snd_ (_,x,_) = x
let trd_ (_,_,x) = x

let joinMaps (p:Map<'a,'b>) (q:Map<'a,'b>) = 
    Map(Seq.concat [ (Map.toSeq p) ; (Map.toSeq q) ])

let makeNewSeq seq (lbl:Source.t) (w:Option<Source.t>) = 
    match seq,w with 
     | PSeq(els,ac,_),_ -> match w with
                           | None -> PSeq (els,ac,Some {label=lbl.text; weight=None})
                           | _ -> let wVal = w.Value
                                  try
                                      PSeq (els,ac,Some {label=lbl.text; weight = Some (float wVal.text)})
                                  with 
                                  | :? System.FormatException as ex ->
                                      failwithf "Parse error on position (%i,%i) on token %s: %s" wVal.startPos.line wVal.startPos.column wVal.text "illegal weight. Number expected."
     | x,_ -> x

let missing name = System.Console.WriteLine("Missing " + name)
let createSeqElem bnd omitted r check =
    { binding = bnd; omit = omitted; rule = r; checker = check }

let parseRules (filename:string) : Definition.t<Source.t, Source.t> =
    let oldFileName = !currentFilename
    currentFilename := filename
    let ext = filename.Substring(filename.LastIndexOf(".") + 1)    
    let userDefs =
        let args = oldFileName.Trim().Split('%') in
        if args.Length = 2
        then args.[1]
        else ""
    let sameDirFilename = System.IO.Path.Combine(System.IO.Path.GetDirectoryName oldFileName, filename) in
    let res = !parseFile (sameDirFilename + "%" + userDefs)
    currentFilename := oldFileName
    res

# 87 "Parser.fs"
type Token =
    | ACTION of (Source.t)
    | ALL_PUBLIC of (Source.t)
    | AMPERSAND of (Source.t)
    | BAR of (Source.t)
    | BLOCK_END of (Source.t)
    | COLON of (Source.t)
    | COMMA of (Source.t)
    | DLABEL of (Source.t)
    | EOF of (Source.t)
    | EQUAL of (Source.t)
    | EXCLAMATION of (Source.t)
    | GREAT of (Source.t)
    | INCLUDE of (Source.t)
    | LESS of (Source.t)
    | LIDENT of (Source.t)
    | LITERAL of (Source.t)
    | LPAREN of (Source.t)
    | MINUS of (Source.t)
    | MODULE of (Source.t)
    | NUMBER of (Source.t)
    | OPEN of (Source.t)
    | OPTIONS_START of (Source.t)
    | PARAM of (Source.t)
    | PLUS of (Source.t)
    | PREDICATE of (Source.t)
    | PRIVATE of (Source.t)
    | PUBLIC of (Source.t)
    | QUESTION of (Source.t)
    | RNGLR_EOF of (Source.t)
    | RPAREN of (Source.t)
    | SEMICOLON of (Source.t)
    | SHARPLINE of (Source.t)
    | SQR_LBR of (Source.t)
    | SQR_RBR of (Source.t)
    | STAR of (Source.t)
    | START_RULE_SIGN of (Source.t)
    | STRING of (Source.t)
    | TOKENS_BLOCK of (Source.t)
    | UIDENT of (Source.t)

let genLiteral (str : string) posStart posEnd =
    match str.ToLower() with
    | x -> failwithf "Literal %s undefined" x
let tokenData = function
    | ACTION x -> box x
    | ALL_PUBLIC x -> box x
    | AMPERSAND x -> box x
    | BAR x -> box x
    | BLOCK_END x -> box x
    | COLON x -> box x
    | COMMA x -> box x
    | DLABEL x -> box x
    | EOF x -> box x
    | EQUAL x -> box x
    | EXCLAMATION x -> box x
    | GREAT x -> box x
    | INCLUDE x -> box x
    | LESS x -> box x
    | LIDENT x -> box x
    | LITERAL x -> box x
    | LPAREN x -> box x
    | MINUS x -> box x
    | MODULE x -> box x
    | NUMBER x -> box x
    | OPEN x -> box x
    | OPTIONS_START x -> box x
    | PARAM x -> box x
    | PLUS x -> box x
    | PREDICATE x -> box x
    | PRIVATE x -> box x
    | PUBLIC x -> box x
    | QUESTION x -> box x
    | RNGLR_EOF x -> box x
    | RPAREN x -> box x
    | SEMICOLON x -> box x
    | SHARPLINE x -> box x
    | SQR_LBR x -> box x
    | SQR_RBR x -> box x
    | STAR x -> box x
    | START_RULE_SIGN x -> box x
    | STRING x -> box x
    | TOKENS_BLOCK x -> box x
    | UIDENT x -> box x

let numToString = function
    | 0 -> "access_modifier_opt"
    | 1 -> "action_opt"
    | 2 -> "alts"
    | 3 -> "alts_call"
    | 4 -> "bar_seq_nlist"
    | 5 -> "boolean_grammar"
    | 6 -> "bound"
    | 7 -> "call"
    | 8 -> "error"
    | 9 -> "file"
    | 10 -> "foot_opt"
    | 11 -> "formal_meta_list"
    | 12 -> "formal_meta_param_opt"
    | 13 -> "ident"
    | 14 -> "include_"
    | 15 -> "includes_or_options_or_tokens"
    | 16 -> "kw"
    | 17 -> "lbl_seq"
    | 18 -> "meta_param"
    | 19 -> "meta_param_opt"
    | 20 -> "meta_params"
    | 21 -> "module_"
    | 22 -> "module_header"
    | 23 -> "modules"
    | 24 -> "negation_alts_call"
    | 25 -> "no_lbl_seq"
    | 26 -> "omit_opt"
    | 27 -> "open_list"
    | 28 -> "openings"
    | 29 -> "option"
    | 30 -> "option_block"
    | 31 -> "option_l_value"
    | 32 -> "option_value"
    | 33 -> "opts"
    | 34 -> "param_list"
    | 35 -> "param_opt"
    | 36 -> "patt"
    | 37 -> "predicate_opt"
    | 38 -> "prim"
    | 39 -> "rule"
    | 40 -> "rule_nlist"
    | 41 -> "semi_opt"
    | 42 -> "seq"
    | 43 -> "seq_elem"
    | 44 -> "seq_elem_list"
    | 45 -> "start_rule_sign_opt"
    | 46 -> "tada_rule"
    | 47 -> "tokens_block"
    | 48 -> "unnamed_module_opt"
    | 49 -> "weight_opt"
    | 50 -> "yard_start_rule"
    | 51 -> "ACTION"
    | 52 -> "ALL_PUBLIC"
    | 53 -> "AMPERSAND"
    | 54 -> "BAR"
    | 55 -> "BLOCK_END"
    | 56 -> "COLON"
    | 57 -> "COMMA"
    | 58 -> "DLABEL"
    | 59 -> "EOF"
    | 60 -> "EQUAL"
    | 61 -> "EXCLAMATION"
    | 62 -> "GREAT"
    | 63 -> "INCLUDE"
    | 64 -> "LESS"
    | 65 -> "LIDENT"
    | 66 -> "LITERAL"
    | 67 -> "LPAREN"
    | 68 -> "MINUS"
    | 69 -> "MODULE"
    | 70 -> "NUMBER"
    | 71 -> "OPEN"
    | 72 -> "OPTIONS_START"
    | 73 -> "PARAM"
    | 74 -> "PLUS"
    | 75 -> "PREDICATE"
    | 76 -> "PRIVATE"
    | 77 -> "PUBLIC"
    | 78 -> "QUESTION"
    | 79 -> "RNGLR_EOF"
    | 80 -> "RPAREN"
    | 81 -> "SEMICOLON"
    | 82 -> "SHARPLINE"
    | 83 -> "SQR_LBR"
    | 84 -> "SQR_RBR"
    | 85 -> "STAR"
    | 86 -> "START_RULE_SIGN"
    | 87 -> "STRING"
    | 88 -> "TOKENS_BLOCK"
    | 89 -> "UIDENT"
    | _ -> ""

let tokenToNumber = function
    | ACTION _ -> 51
    | ALL_PUBLIC _ -> 52
    | AMPERSAND _ -> 53
    | BAR _ -> 54
    | BLOCK_END _ -> 55
    | COLON _ -> 56
    | COMMA _ -> 57
    | DLABEL _ -> 58
    | EOF _ -> 59
    | EQUAL _ -> 60
    | EXCLAMATION _ -> 61
    | GREAT _ -> 62
    | INCLUDE _ -> 63
    | LESS _ -> 64
    | LIDENT _ -> 65
    | LITERAL _ -> 66
    | LPAREN _ -> 67
    | MINUS _ -> 68
    | MODULE _ -> 69
    | NUMBER _ -> 70
    | OPEN _ -> 71
    | OPTIONS_START _ -> 72
    | PARAM _ -> 73
    | PLUS _ -> 74
    | PREDICATE _ -> 75
    | PRIVATE _ -> 76
    | PUBLIC _ -> 77
    | QUESTION _ -> 78
    | RNGLR_EOF _ -> 79
    | RPAREN _ -> 80
    | SEMICOLON _ -> 81
    | SHARPLINE _ -> 82
    | SQR_LBR _ -> 83
    | SQR_RBR _ -> 84
    | STAR _ -> 85
    | START_RULE_SIGN _ -> 86
    | STRING _ -> 87
    | TOKENS_BLOCK _ -> 88
    | UIDENT _ -> 89

let isLiteral = function
    | ACTION _ -> false
    | ALL_PUBLIC _ -> false
    | AMPERSAND _ -> false
    | BAR _ -> false
    | BLOCK_END _ -> false
    | COLON _ -> false
    | COMMA _ -> false
    | DLABEL _ -> false
    | EOF _ -> false
    | EQUAL _ -> false
    | EXCLAMATION _ -> false
    | GREAT _ -> false
    | INCLUDE _ -> false
    | LESS _ -> false
    | LIDENT _ -> false
    | LITERAL _ -> false
    | LPAREN _ -> false
    | MINUS _ -> false
    | MODULE _ -> false
    | NUMBER _ -> false
    | OPEN _ -> false
    | OPTIONS_START _ -> false
    | PARAM _ -> false
    | PLUS _ -> false
    | PREDICATE _ -> false
    | PRIVATE _ -> false
    | PUBLIC _ -> false
    | QUESTION _ -> false
    | RNGLR_EOF _ -> false
    | RPAREN _ -> false
    | SEMICOLON _ -> false
    | SHARPLINE _ -> false
    | SQR_LBR _ -> false
    | SQR_RBR _ -> false
    | STAR _ -> false
    | START_RULE_SIGN _ -> false
    | STRING _ -> false
    | TOKENS_BLOCK _ -> false
    | UIDENT _ -> false

let getLiteralNames = []
let mutable private cur = 0
let leftSide = [|16; 16; 16; 16; 16; 9; 50; 15; 15; 15; 15; 47; 14; 30; 33; 33; 29; 32; 32; 32; 31; 31; 48; 23; 23; 21; 13; 13; 22; 22; 28; 28; 27; 27; 1; 1; 10; 10; 40; 40; 39; 45; 45; 0; 0; 0; 12; 12; 11; 11; 35; 35; 34; 34; 49; 49; 2; 2; 4; 4; 42; 42; 25; 25; 17; 44; 44; 43; 26; 26; 41; 41; 37; 37; 6; 6; 36; 36; 38; 38; 38; 38; 38; 38; 38; 38; 38; 18; 20; 20; 19; 19; 7; 7; 46; 46; 3; 3; 24; 24; 5; 5|]
let private rules = [|69; 63; 71; 77; 76; 1; 15; 48; 23; 10; 59; 9; 14; 15; 30; 15; 47; 15; 88; 63; 87; 72; 33; 55; 29; 33; 31; 60; 32; 13; 87; 16; 13; 16; 40; 21; 23; 22; 13; 28; 40; 89; 65; 52; 69; 69; 71; 13; 27; 57; 13; 27; 51; 81; 51; 39; 41; 40; 45; 0; 65; 12; 34; 56; 2; 86; 77; 76; 64; 11; 62; 65; 65; 11; 73; 73; 34; 83; 70; 84; 42; 42; 4; 54; 42; 4; 54; 42; 17; 25; 43; 44; 1; 51; 58; 49; 67; 25; 80; 43; 44; 26; 6; 37; 68; 81; 75; 36; 60; 38; 38; 65; 51; 38; 85; 38; 74; 38; 78; 83; 2; 84; 67; 2; 80; 7; 17; 66; 5; 38; 18; 18; 20; 64; 20; 62; 89; 65; 19; 35; 82; 59; 67; 2; 80; 7; 61; 3; 3; 24; 24; 53; 5|]
let private rulesStart = [|0; 1; 2; 3; 4; 5; 11; 12; 12; 14; 16; 18; 19; 21; 24; 26; 26; 29; 30; 31; 32; 33; 34; 35; 37; 37; 41; 42; 43; 45; 46; 46; 49; 52; 52; 52; 53; 53; 55; 58; 58; 65; 65; 66; 67; 68; 68; 68; 71; 72; 74; 74; 75; 75; 77; 77; 80; 81; 83; 86; 88; 89; 90; 93; 94; 99; 99; 101; 104; 104; 105; 105; 106; 106; 107; 110; 111; 112; 113; 115; 117; 119; 122; 125; 126; 127; 128; 129; 130; 131; 133; 133; 136; 137; 140; 141; 142; 145; 146; 148; 149; 150; 153|]
let startRule = 6

let acceptEmptyInput = false

let defaultAstToDot =
    (fun (tree : Yard.Generators.RNGLR.AST.Tree<Token>) -> tree.AstToDot numToString tokenToNumber leftSide)

let private lists_gotos = [|1; 142; 88; 2; 31; 4; 6; 8; 10; 30; 3; 5; 7; 9; 11; 12; 13; 14; 28; 19; 20; 21; 22; 23; 24; 26; 27; 15; 16; 17; 18; 25; 29; 32; 120; 35; 121; 118; 33; 119; 34; 36; 116; 117; 37; 38; 111; 39; 109; 40; 41; 42; 43; 44; 97; 82; 89; 77; 85; 45; 46; 47; 50; 51; 52; 71; 105; 108; 56; 106; 93; 94; 102; 70; 48; 49; 53; 54; 55; 58; 67; 57; 59; 62; 60; 61; 63; 65; 107; 64; 66; 68; 69; 72; 73; 74; 75; 76; 78; 90; 79; 80; 81; 83; 86; 84; 87; 91; 92; 95; 96; 98; 99; 100; 101; 103; 104; 110; 112; 114; 113; 115; 122; 123; 137; 134; 136; 133; 124; 125; 127; 126; 128; 129; 130; 131; 132; 135; 138; 140; 139; 141|]
let private small_gotos =
        [|3; 65536; 589825; 3342338; 65543; 917507; 983044; 1966085; 3080198; 4128775; 4718600; 5767177; 131079; 917507; 983050; 1966085; 3080198; 4128775; 4718600; 5767177; 262151; 917507; 983051; 1966085; 3080198; 4128775; 4718600; 5767177; 393223; 917507; 983052; 1966085; 3080198; 4128775; 4718600; 5767177; 524289; 5701645; 655372; 851982; 1048591; 1900560; 2031633; 2162706; 4128787; 4259860; 4522005; 4653078; 4980759; 5046296; 5832729; 851980; 851982; 1048591; 1900560; 2031633; 2162714; 4128787; 4259860; 4522005; 4653078; 4980759; 5046296; 5832729; 917505; 3932187; 983051; 851996; 1048605; 2097182; 4128787; 4259860; 4522005; 4653078; 4980759; 5046296; 5701663; 5832729; 1835009; 3604512; 2031621; 2555937; 2621474; 2949155; 3145764; 5636133; 2097154; 2687014; 5308455; 2162692; 2555937; 2621480; 2949155; 5636133; 2293763; 41; 4980778; 5046315; 2359297; 4259884; 2424834; 786477; 4194350; 2490370; 2228271; 4784176; 2555905; 3670065; 2621449; 131122; 1114163; 1638452; 1703989; 2752566; 2818103; 3342392; 3801145; 4456506; 2883600; 196667; 327740; 393277; 458814; 1114175; 1572928; 2359361; 2490434; 3342403; 3801145; 3997764; 4259909; 4325446; 4390983; 5439560; 5832777; 3080194; 2424906; 4915275; 3407873; 3473484; 3473416; 196667; 327757; 458830; 1572928; 3997764; 4259919; 4390992; 5832777; 3670021; 196689; 458830; 4259919; 4390992; 5832777; 3801090; 1245266; 4194387; 3866626; 2293844; 4784213; 4063247; 196667; 327740; 458814; 1114175; 1179734; 1310807; 1572928; 2490456; 3801145; 3997764; 4259919; 4325446; 4390983; 5439560; 5832777; 4128783; 196667; 327740; 458814; 1114175; 1179734; 1310809; 1572928; 2490456; 3801145; 3997764; 4259919; 4325446; 4390983; 5439560; 5832777; 4259841; 4063322; 4390921; 131163; 1114163; 1638452; 1703989; 2752566; 2818103; 3342392; 3801145; 4456506; 4456449; 5242972; 4653057; 3932253; 4718605; 196667; 327740; 458814; 1114175; 1572928; 2490462; 3801145; 3997764; 4259919; 4325446; 4390983; 5439560; 5832777; 4784131; 4849759; 5111904; 5570657; 5046274; 3211362; 5439587; 5111809; 4391012; 5177349; 1638501; 1703989; 2818103; 3342392; 4456506; 5242881; 5242982; 5373956; 1703989; 2818151; 2883688; 4456506; 5439492; 1703989; 2818151; 2883689; 4456506; 5636098; 65642; 3342338; 5898241; 4587627; 5963777; 5505132; 6160393; 131181; 1114163; 1638452; 1703989; 2752566; 2818103; 3342392; 3801145; 4456506; 6225921; 5242990; 6356994; 262255; 3539056; 6488072; 1114163; 1638452; 1703989; 2752625; 2818103; 3342392; 3801145; 4456506; 6553602; 262258; 3539056; 6684681; 131187; 1114163; 1638452; 1703989; 2752566; 2818103; 3342392; 3801145; 4456506; 6750209; 5505140; 6881283; 4849759; 5111904; 5570657; 6946818; 1245266; 4194387; 7012355; 4849759; 5111904; 5570657; 7143426; 2228341; 4784176; 7274498; 721014; 4259959; 7340033; 4063352; 7471106; 721017; 4259959; 7929861; 1376378; 1441915; 1507452; 3407997; 4522110; 7995397; 1376378; 1441915; 1507455; 3407997; 4522110; 8060931; 852096; 4259860; 5832729; 8126466; 1835137; 4653186; 8192004; 2555937; 2621571; 2949155; 5636133; 8323075; 852100; 4259860; 5832729; 8388610; 1769605; 3735686; 8519683; 852103; 4259860; 5832729; 8585218; 1769608; 3735686; 8781825; 4522121; 8978434; 655498; 5308555; 9043969; 3866764; 9175041; 3342477|]
let gotos = Array.zeroCreate 143
for i = 0 to 142 do
        gotos.[i] <- Array.zeroCreate 90
cur <- 0
while cur < small_gotos.Length do
    let i = small_gotos.[cur] >>> 16
    let length = small_gotos.[cur] &&& 65535
    cur <- cur + 1
    for k = 0 to length-1 do
        let j = small_gotos.[cur + k] >>> 16
        let x = small_gotos.[cur + k] &&& 65535
        gotos.[i].[j] <- lists_gotos.[x]
    cur <- cur + length
let private lists_reduces = [|[|8,1|]; [|8,2|]; [|9,1|]; [|9,2|]; [|10,1|]; [|10,2|]; [|12,2|]; [|20,1|]; [|21,1|]; [|14,1|]; [|17,1|]; [|19,1|]; [|16,3|]; [|1,1|]; [|27,1|]; [|0,1|]; [|2,1|]; [|4,1|]; [|3,1|]; [|18,1|]; [|26,1|]; [|14,2|]; [|13,3|]; [|11,1|]; [|38,1|]; [|38,2|]; [|38,3|]; [|40,7|]; [|60,1|]; [|61,1|]; [|99,1|]; [|86,1|]; [|67,2|]; [|67,3|]; [|73,1|]; [|97,1; 83,1|]; [|97,1|]; [|84,1|]; [|100,1|]; [|101,3|]; [|98,2|]; [|93,1|]; [|93,2|]; [|93,3|]; [|51,1|]; [|88,1|]; [|89,2|]; [|91,3|]; [|96,3|]; [|92,1|]; [|74,3|]; [|79,2|]; [|80,2|]; [|78,2|]; [|64,5|]; [|62,1|]; [|66,1|]; [|66,2|]; [|69,1|]; [|62,2|]; [|62,3|]; [|35,1|]; [|63,1|]; [|55,3|]; [|85,1|]; [|96,3; 82,3|]; [|56,1|]; [|57,2|]; [|59,2|]; [|58,3|]; [|81,3|]; [|75,1|]; [|76,1|]; [|87,1|]; [|77,1|]; [|53,1|]; [|53,2|]; [|47,3|]; [|48,1|]; [|49,2|]; [|44,1|]; [|43,1|]; [|42,1|]; [|71,1|]; [|22,1|]; [|23,1|]; [|25,2|]; [|25,3|]; [|25,4|]; [|31,2|]; [|31,3|]; [|32,2|]; [|32,3|]; [|23,2|]; [|28,2|]; [|29,1|]; [|5,6|]; [|37,2|]|]
let private small_reduces =
        [|131080; 3407872; 3866624; 4259840; 4521984; 4980736; 5046272; 5308416; 5636096; 196616; 3407873; 3866625; 4259841; 4521985; 4980737; 5046273; 5308417; 5636097; 262152; 3407874; 3866626; 4259842; 4521986; 4980738; 5046274; 5308418; 5636098; 327688; 3407875; 3866627; 4259843; 4521987; 4980739; 5046275; 5308419; 5636099; 393224; 3407876; 3866628; 4259844; 4521988; 4980740; 5046276; 5308420; 5636100; 458760; 3407877; 3866629; 4259845; 4521989; 4980741; 5046277; 5308421; 5636101; 589835; 3407878; 3866630; 4128774; 4259846; 4521990; 4718598; 4980742; 5046278; 5308422; 5636102; 5767174; 720897; 3932167; 786433; 3932168; 851969; 3604489; 1048584; 3604490; 4128778; 4259850; 4521994; 4653066; 4980746; 5046282; 5832714; 1114120; 3604491; 4128779; 4259851; 4521995; 4653067; 4980747; 5046283; 5832715; 1179656; 3604492; 4128780; 4259852; 4521996; 4653068; 4980748; 5046284; 5832716; 1245193; 3604493; 3932173; 4128781; 4259853; 4521997; 4653069; 4980749; 5046285; 5832717; 1310734; 3407886; 3604494; 3735566; 3866638; 3932174; 4128782; 4259854; 4521998; 4653070; 4980750; 5046286; 5308430; 5636110; 5832718; 1376265; 3604495; 3932175; 4128783; 4259855; 4521999; 4653071; 4980751; 5046287; 5832719; 1441801; 3604496; 3932176; 4128784; 4259856; 4522000; 4653072; 4980752; 5046288; 5832720; 1507337; 3604497; 3932177; 4128785; 4259857; 4522001; 4653073; 4980753; 5046289; 5832721; 1572873; 3604498; 3932178; 4128786; 4259858; 4522002; 4653074; 4980754; 5046290; 5832722; 1638408; 3604499; 4128787; 4259859; 4522003; 4653075; 4980755; 5046291; 5832723; 1703950; 3407892; 3604500; 3735572; 3866644; 3932180; 4128788; 4259860; 4522004; 4653076; 4980756; 5046292; 5308436; 5636116; 5832724; 1769473; 3604501; 1900555; 3407894; 3866646; 4128790; 4259862; 4522006; 4718614; 4980758; 5046294; 5308438; 5636118; 5767190; 1966091; 3407895; 3866647; 4128791; 4259863; 4522007; 4718615; 4980759; 5046295; 5308439; 5636119; 5767191; 2097156; 3407896; 3866648; 4522008; 5308440; 2162692; 3407897; 3866649; 4522009; 5308441; 2228228; 3407898; 3866650; 4522010; 5308442; 2686984; 3407899; 3866651; 4259867; 4522011; 4980763; 5046299; 5308443; 5636123; 2752523; 3407900; 3538972; 3866652; 4259868; 4522012; 4980764; 5046300; 5242908; 5308444; 5505052; 5636124; 2818059; 3407901; 3538973; 3866653; 4259869; 4522013; 4980765; 5046301; 5242909; 5308445; 5505053; 5636125; 2949145; 3342366; 3407902; 3473438; 3538974; 3801118; 3866654; 3997726; 4063262; 4259870; 4325406; 4390942; 4456478; 4522014; 4849694; 4915230; 4980766; 5046302; 5111838; 5242910; 5308446; 5439518; 5505054; 5570590; 5636126; 5832734; 3014680; 3342367; 3407903; 3538975; 3801119; 3866655; 3997727; 4063263; 4259871; 4325407; 4390943; 4456479; 4522015; 4849695; 4915231; 4980767; 5046303; 5111839; 5242911; 5308447; 5439519; 5505055; 5570591; 5636127; 5832735; 3080211; 3342368; 3407904; 3538976; 3801120; 3866656; 3997728; 4259872; 4325408; 4390944; 4456480; 4522016; 4980768; 5046304; 5242912; 5308448; 5439520; 5505056; 5636128; 5832736; 3145747; 3342369; 3407905; 3538977; 3801121; 3866657; 3997729; 4259873; 4325409; 4390945; 4456481; 4522017; 4980769; 5046305; 5242913; 5308449; 5439521; 5505057; 5636129; 5832737; 3211283; 3342370; 3407906; 3538978; 3801122; 3866658; 3997730; 4259874; 4325410; 4390946; 4456482; 4522018; 4980770; 5046306; 5242914; 5308450; 5439522; 5505058; 5636130; 5832738; 3276825; 3342371; 3407907; 3473444; 3538979; 3801123; 3866659; 3997731; 4063267; 4259875; 4325411; 4390947; 4456483; 4522019; 4849699; 4915235; 4980771; 5046307; 5111843; 5242915; 5308451; 5439523; 5505059; 5570595; 5636131; 5832739; 3342360; 3342373; 3407909; 3538981; 3801125; 3866661; 3997733; 4063269; 4259877; 4325413; 4390949; 4456485; 4522021; 4849701; 4915237; 4980773; 5046309; 5111845; 5242917; 5308453; 5439525; 5505061; 5570597; 5636133; 5832741; 3407896; 3342374; 3407910; 3538982; 3801126; 3866662; 3997734; 4063270; 4259878; 4325414; 4390950; 4456486; 4522022; 4849702; 4915238; 4980774; 5046310; 5111846; 5242918; 5308454; 5439526; 5505062; 5570598; 5636134; 5832742; 3538968; 3342375; 3407911; 3538983; 3801127; 3866663; 3997735; 4063271; 4259879; 4325415; 4390951; 4456487; 4522023; 4849703; 4915239; 4980775; 5046311; 5111847; 5242919; 5308455; 5439527; 5505063; 5570599; 5636135; 5832743; 3604505; 3342372; 3407908; 3473444; 3538980; 3801124; 3866660; 3997732; 4063268; 4259876; 4325412; 4390948; 4456484; 4522020; 4849700; 4915236; 4980772; 5046308; 5111844; 5242916; 5308452; 5439524; 5505060; 5570596; 5636132; 5832740; 3735577; 3342376; 3407912; 3473448; 3538984; 3801128; 3866664; 3997736; 4063272; 4259880; 4325416; 4390952; 4456488; 4522024; 4849704; 4915240; 4980776; 5046312; 5111848; 5242920; 5308456; 5439528; 5505064; 5570600; 5636136; 5832744; 3801113; 3342377; 3407913; 3473449; 3538985; 3801129; 3866665; 3997737; 4063273; 4259881; 4325417; 4390953; 4456489; 4522025; 4849705; 4915241; 4980777; 5046313; 5111849; 5242921; 5308457; 5439529; 5505065; 5570601; 5636137; 5832745; 3866649; 3342378; 3407914; 3473450; 3538986; 3801130; 3866666; 3997738; 4063274; 4259882; 4325418; 4390954; 4456490; 4522026; 4849706; 4915242; 4980778; 5046314; 5111850; 5242922; 5308458; 5439530; 5505066; 5570602; 5636138; 5832746; 3932185; 3342379; 3407915; 3473451; 3538987; 3801131; 3866667; 3997739; 4063275; 4259883; 4325419; 4390955; 4456491; 4522027; 4849707; 4915243; 4980779; 5046315; 5111851; 5242923; 5308459; 5439531; 5505067; 5570603; 5636139; 5832747; 3997721; 3342380; 3407916; 3473452; 3538988; 3801132; 3866668; 3997740; 4063276; 4259884; 4325420; 4390956; 4456492; 4522028; 4849708; 4915244; 4980780; 5046316; 5111852; 5242924; 5308460; 5439532; 5505068; 5570604; 5636140; 5832748; 4128769; 4063277; 4194305; 4063278; 4325402; 3342383; 3407919; 3473455; 3538991; 3801135; 3866671; 3997743; 4063279; 4259887; 4325423; 4390959; 4456495; 4522031; 4784175; 4849711; 4915247; 4980783; 5046319; 5111855; 5242927; 5308463; 5439535; 5505071; 5570607; 5636143; 5832751; 4522009; 3342384; 3407920; 3473456; 3538992; 3801136; 3866672; 3997744; 4063280; 4259888; 4325424; 4390960; 4456496; 4522032; 4849712; 4915248; 4980784; 5046320; 5111856; 5242928; 5308464; 5439536; 5505072; 5570608; 5636144; 5832752; 4587545; 3342385; 3407921; 3473457; 3538993; 3801137; 3866673; 3997745; 4063281; 4259889; 4325425; 4390961; 4456497; 4522033; 4849713; 4915249; 4980785; 5046321; 5111857; 5242929; 5308465; 5439537; 5505073; 5570609; 5636145; 5832753; 4784148; 3342386; 3407922; 3538994; 3801138; 3866674; 3997746; 4259890; 4325426; 4390962; 4456498; 4522034; 4915250; 4980786; 5046322; 5242930; 5308466; 5439538; 5505074; 5636146; 5832754; 4849688; 3342387; 3407923; 3538995; 3801139; 3866675; 3997747; 4063283; 4259891; 4325427; 4390963; 4456499; 4522035; 4849715; 4915251; 4980787; 5046323; 5111859; 5242931; 5308467; 5439539; 5505075; 5570611; 5636147; 5832755; 4915224; 3342388; 3407924; 3538996; 3801140; 3866676; 3997748; 4063284; 4259892; 4325428; 4390964; 4456500; 4522036; 4849716; 4915252; 4980788; 5046324; 5111860; 5242932; 5308468; 5439540; 5505076; 5570612; 5636148; 5832756; 4980760; 3342389; 3407925; 3538997; 3801141; 3866677; 3997749; 4063285; 4259893; 4325429; 4390965; 4456501; 4522037; 4849717; 4915253; 4980789; 5046325; 5111861; 5242933; 5308469; 5439541; 5505077; 5570613; 5636149; 5832757; 5308440; 3342390; 3407926; 3538998; 3801142; 3866678; 3997750; 4063286; 4259894; 4325430; 4390966; 4456502; 4522038; 4849718; 4915254; 4980790; 5046326; 5111862; 5242934; 5308470; 5439542; 5505078; 5570614; 5636150; 5832758; 5373963; 3407927; 3538999; 3866679; 4259895; 4522039; 4980791; 5046327; 5242935; 5308471; 5505079; 5636151; 5439500; 3342392; 3407928; 3539000; 3866680; 4259896; 4522040; 4980792; 5046328; 5242936; 5308472; 5505080; 5636152; 5505036; 3342393; 3407929; 3539001; 3866681; 4259897; 4522041; 4980793; 5046329; 5242937; 5308473; 5505081; 5636153; 5570568; 3342394; 3801146; 3997754; 4259898; 4325434; 4390970; 5439546; 5832762; 5636107; 3407931; 3539003; 3866683; 4259899; 4522043; 4980795; 5046331; 5242939; 5308475; 5505083; 5636155; 5701643; 3407932; 3539004; 3866684; 4259900; 4522044; 4980796; 5046332; 5242940; 5308476; 5505084; 5636156; 5767182; 3407933; 3539005; 3866685; 4128829; 4259901; 4522045; 4718653; 4980797; 5046333; 5242941; 5308477; 5505085; 5636157; 5767229; 5832715; 3407934; 3539006; 3866686; 4259902; 4522046; 4980798; 5046334; 5242942; 5308478; 5505086; 5636158; 6029313; 4390975; 6094872; 3342400; 3407936; 3539008; 3801152; 3866688; 3997760; 4063296; 4259904; 4325440; 4390976; 4456512; 4522048; 4849728; 4915264; 4980800; 5046336; 5111872; 5242944; 5308480; 5439552; 5505088; 5570624; 5636160; 5832768; 6291481; 3342401; 3407937; 3473456; 3539009; 3801153; 3866689; 3997761; 4063297; 4259905; 4325441; 4390977; 4456513; 4522049; 4849729; 4915265; 4980801; 5046337; 5111873; 5242945; 5308481; 5439553; 5505089; 5570625; 5636161; 5832769; 6357002; 3407938; 3866690; 4259906; 4522050; 4980802; 5046338; 5242946; 5308482; 5505090; 5636162; 6422538; 3407939; 3866691; 4259907; 4522051; 4980803; 5046339; 5242947; 5308483; 5505091; 5636163; 6553610; 3407940; 3866692; 4259908; 4522052; 4980804; 5046340; 5242948; 5308484; 5505092; 5636164; 6619146; 3407941; 3866693; 4259909; 4522053; 4980805; 5046341; 5242949; 5308485; 5505093; 5636165; 6815768; 3342406; 3407942; 3539014; 3801158; 3866694; 3997766; 4063302; 4259910; 4325446; 4390982; 4456518; 4522054; 4849734; 4915270; 4980806; 5046342; 5111878; 5242950; 5308486; 5439558; 5505094; 5570630; 5636166; 5832774; 6881300; 3342407; 3407943; 3539015; 3801159; 3866695; 3997767; 4259911; 4325447; 4390983; 4456519; 4522055; 4915271; 4980807; 5046343; 5242951; 5308487; 5439559; 5505095
                                        ; 5636167; 5832775; 6946841; 3342377; 3407913; 3473449; 3538985; 3801129; 3866665; 3932232; 3997737; 4259881; 4325417; 4390953; 4456489; 4522025; 4849705; 4915241; 4980777; 5046313; 5111849; 5242921; 5308457; 5439529; 5505065; 5570601; 5636137; 5832745; 7012360; 3801161; 3997769; 4063305; 4259913; 4325449; 4390985; 5439561; 5832777; 7077889; 3932234; 7143425; 3670091; 7208961; 3670092; 7405570; 3670093; 4784205; 7471105; 4063310; 7536641; 4063311; 7602177; 4259920; 7667713; 4259921; 7733251; 4259922; 4980818; 5046354; 7798792; 3407955; 3866707; 4259923; 4522067; 4980819; 5046355; 5308499; 5636179; 7864324; 3407956; 3866708; 4522068; 5308500; 7995394; 3866709; 5308501; 8126468; 3407958; 3866710; 4522070; 5308502; 8192004; 3407959; 3866711; 4522071; 5308503; 8257540; 3407960; 3866712; 4522072; 5308504; 8388616; 3407961; 3866713; 4259929; 4522073; 4980825; 5046361; 5308505; 5636185; 8454152; 3407962; 3866714; 4259930; 4522074; 4980826; 5046362; 5308506; 5636186; 8585224; 3407963; 3866715; 4259931; 4522075; 4980827; 5046363; 5308507; 5636187; 8650760; 3407964; 3866716; 4259932; 4522076; 4980828; 5046364; 5308508; 5636188; 8716290; 3866717; 5308509; 8847362; 4259934; 5832798; 8912898; 4259935; 5832799; 9109505; 5177440; 9240577; 3866721|]
let reduces = Array.zeroCreate 143
for i = 0 to 142 do
        reduces.[i] <- Array.zeroCreate 90
cur <- 0
while cur < small_reduces.Length do
    let i = small_reduces.[cur] >>> 16
    let length = small_reduces.[cur] &&& 65535
    cur <- cur + 1
    for k = 0 to length-1 do
        let j = small_reduces.[cur + k] >>> 16
        let x = small_reduces.[cur + k] &&& 65535
        reduces.[i].[j] <- lists_reduces.[x]
    cur <- cur + length
let private lists_zeroReduces = [|[|34|]; [|7|]; [|15|]; [|39; 22|]; [|41|]; [|70|]; [|39|]; [|45|]; [|46|]; [|52|]; [|68|]; [|72|]; [|90|]; [|50|]; [|54|]; [|68; 65|]; [|65|]; [|24|]; [|30|]; [|33|]; [|36|]|]
let private small_zeroReduces =
        [|11; 3407872; 3866624; 4128768; 4259840; 4521984; 4718592; 4980736; 5046272; 5308416; 5636096; 5767168; 65544; 3407873; 3866625; 4259841; 4521985; 4980737; 5046273; 5308417; 5636097; 131080; 3407873; 3866625; 4259841; 4521985; 4980737; 5046273; 5308417; 5636097; 262152; 3407873; 3866625; 4259841; 4521985; 4980737; 5046273; 5308417; 5636097; 393224; 3407873; 3866625; 4259841; 4521985; 4980737; 5046273; 5308417; 5636097; 655361; 3604482; 851969; 3604482; 2031623; 3407875; 3866627; 4259844; 4521987; 4980740; 5046276; 5308419; 2097160; 3407877; 3866629; 4259845; 4521989; 4980741; 5046277; 5308421; 5636101; 2162695; 3407878; 3866630; 4259844; 4521990; 4980740; 5046276; 5308422; 2293761; 4259847; 2424834; 3670024; 4784136; 2490369; 3670025; 2621448; 3342346; 3801098; 3997706; 4259850; 4325386; 4390922; 5439498; 5832714; 3080211; 3342347; 3407883; 3538955; 3801099; 3866635; 3997707; 4259851; 4325387; 4390923; 4456459; 4521995; 4980747; 5046283; 5242891; 5308427; 5439499; 5505035; 5636107; 5832715; 3801114; 3342348; 3407884; 3473420; 3538956; 3801100; 3866636; 3997708; 4063244; 4259852; 4325388; 4390924; 4456460; 4521996; 4784140; 4849676; 4915212; 4980748; 5046284; 5111820; 5242892; 5308428; 5439500; 5505036; 5570572; 5636108; 5832716; 3866649; 3342349; 3407885; 3473421; 3538957; 3801101; 3866637; 3997709; 4063245; 4259853; 4325389; 4390925; 4456461; 4521997; 4849677; 4915213; 4980749; 5046285; 5111821; 5242893; 5308429; 5439501; 5505037; 5570573; 5636109; 5832717; 4390920; 3342346; 3801098; 3997706; 4259850; 4325386; 4390922; 5439498; 5832714; 5046273; 4390926; 5177352; 3342346; 3801098; 3997706; 4259850; 4325386; 4390922; 5439498; 5832714; 5373970; 3342351; 3407888; 3538960; 3801098; 3866640; 3997706; 4259855; 4325386; 4390922; 4522000; 4980752; 5046288; 5242896; 5308432; 5439498; 5505040; 5636112; 5832714; 5439506; 3342351; 3407888; 3538960; 3801098; 3866640; 3997706; 4259855; 4325386; 4390922; 4522000; 4980752; 5046288; 5242896; 5308432; 5439498; 5505040; 5636112; 5832714; 5636107; 3407872; 3538944; 3866624; 4259840; 4521984; 4980736; 5046272; 5242880; 5308416; 5505024; 5636096; 6160392; 3342346; 3801098; 3997706; 4259850; 4325386; 4390922; 5439498; 5832714; 6488072; 3342346; 3801098; 3997706; 4259850; 4325386; 4390922; 5439498; 5832714; 6684680; 3342346; 3801098; 3997706; 4259850; 4325386; 4390922; 5439498; 5832714; 6946841; 3342348; 3407884; 3473420; 3538956; 3801100; 3866636; 3997708; 4259852; 4325388; 4390924; 4456460; 4521996; 4784140; 4849676; 4915212; 4980748; 5046284; 5111820; 5242892; 5308428; 5439500; 5505036; 5570572; 5636108; 5832716; 7143425; 3670025; 7929858; 3866641; 5308433; 7995394; 3866641; 5308433; 8126472; 3407890; 3866642; 4259858; 4522002; 4980754; 5046290; 5308434; 5636114; 8192007; 3407878; 3866630; 4259844; 4521990; 4980740; 5046276; 5308422; 8388616; 3407891; 3866643; 4259859; 4522003; 4980755; 5046291; 5308435; 5636115; 8585224; 3407891; 3866643; 4259859; 4522003; 4980755; 5046291; 5308435; 5636115; 8978433; 3866644|]
let zeroReduces = Array.zeroCreate 143
for i = 0 to 142 do
        zeroReduces.[i] <- Array.zeroCreate 90
cur <- 0
while cur < small_zeroReduces.Length do
    let i = small_zeroReduces.[cur] >>> 16
    let length = small_zeroReduces.[cur] &&& 65535
    cur <- cur + 1
    for k = 0 to length-1 do
        let j = small_zeroReduces.[cur + k] >>> 16
        let x = small_zeroReduces.[cur + k] &&& 65535
        zeroReduces.[i].[j] <- lists_zeroReduces.[x]
    cur <- cur + length
let private small_acc = [142]
let private accStates = Array.zeroCreate 143
for i = 0 to 142 do
        accStates.[i] <- List.exists ((=) i) small_acc
let eofIndex = 79
let errorIndex = 8
let errorRulesExists = false
let private parserSource = new ParserSource<Token> (gotos, reduces, zeroReduces, accStates, rules, rulesStart, leftSide, startRule, eofIndex, tokenToNumber, acceptEmptyInput, numToString, errorIndex, errorRulesExists)
let buildAst : (seq<Token> -> ParseResult<Token>) =
    buildAst<Token> parserSource

let _rnglr_epsilons : Tree<Token>[] = [|new Tree<_>(null,box (new AST(new Family(45, new Nodes([||])), null)), null); new Tree<_>(null,box (new AST(new Family(34, new Nodes([||])), null)), null); null; null; null; null; null; null; null; null; new Tree<_>(null,box (new AST(new Family(36, new Nodes([||])), null)), null); null; new Tree<_>(null,box (new AST(new Family(46, new Nodes([||])), null)), null); null; null; new Tree<_>(null,box (new AST(new Family(7, new Nodes([||])), null)), null); null; null; null; new Tree<_>(null,box (new AST(new Family(90, new Nodes([||])), null)), null); null; null; null; new Tree<_>(null,box (new AST(new Family(24, new Nodes([||])), null)), null); null; null; new Tree<_>(null,box (new AST(new Family(68, new Nodes([||])), null)), null); new Tree<_>(null,box (new AST(new Family(33, new Nodes([||])), null)), null); new Tree<_>(null,box (new AST(new Family(30, new Nodes([||])), null)), null); null; null; null; null; new Tree<_>(null,box (new AST(new Family(15, new Nodes([||])), null)), null); new Tree<_>(null,box (new AST(new Family(52, new Nodes([||])), null)), null); new Tree<_>(null,box (new AST(new Family(50, new Nodes([||])), null)), null); null; new Tree<_>(null,box (new AST(new Family(72, new Nodes([||])), null)), null); null; null; new Tree<_>(null,box (new AST(new Family(39, new Nodes([||])), null)), null); new Tree<_>(null,box (new AST(new Family(70, new Nodes([||])), null)), null); null; null; new Tree<_>(null,box (new AST(new Family(65, new Nodes([||])), null)), null); new Tree<_>(null,box (new AST(new Family(41, new Nodes([||])), null)), null); null; null; new Tree<_>(null,box (new AST(new Family(22, new Nodes([|box (new AST(new Family(39, new Nodes([||])), null))|])), null)), null); new Tree<_>(null,box (new AST(new Family(54, new Nodes([||])), null)), null); null|]
let _rnglr_filtered_epsilons : Tree<Token>[] = [|new Tree<_>(null,box (new AST(new Family(45, new Nodes([||])), null)), null); new Tree<_>(null,box (new AST(new Family(34, new Nodes([||])), null)), null); null; null; null; null; null; null; null; null; new Tree<_>(null,box (new AST(new Family(36, new Nodes([||])), null)), null); null; new Tree<_>(null,box (new AST(new Family(46, new Nodes([||])), null)), null); null; null; new Tree<_>(null,box (new AST(new Family(7, new Nodes([||])), null)), null); null; null; null; new Tree<_>(null,box (new AST(new Family(90, new Nodes([||])), null)), null); null; null; null; new Tree<_>(null,box (new AST(new Family(24, new Nodes([||])), null)), null); null; null; new Tree<_>(null,box (new AST(new Family(68, new Nodes([||])), null)), null); new Tree<_>(null,box (new AST(new Family(33, new Nodes([||])), null)), null); new Tree<_>(null,box (new AST(new Family(30, new Nodes([||])), null)), null); null; null; null; null; new Tree<_>(null,box (new AST(new Family(15, new Nodes([||])), null)), null); new Tree<_>(null,box (new AST(new Family(52, new Nodes([||])), null)), null); new Tree<_>(null,box (new AST(new Family(50, new Nodes([||])), null)), null); null; new Tree<_>(null,box (new AST(new Family(72, new Nodes([||])), null)), null); null; null; new Tree<_>(null,box (new AST(new Family(39, new Nodes([||])), null)), null); new Tree<_>(null,box (new AST(new Family(70, new Nodes([||])), null)), null); null; null; new Tree<_>(null,box (new AST(new Family(65, new Nodes([||])), null)), null); new Tree<_>(null,box (new AST(new Family(41, new Nodes([||])), null)), null); null; null; new Tree<_>(null,box (new AST(new Family(22, new Nodes([|box (new AST(new Family(39, new Nodes([||])), null))|])), null)), null); new Tree<_>(null,box (new AST(new Family(54, new Nodes([||])), null)), null); null|]
for x in _rnglr_filtered_epsilons do if x <> null then x.ChooseSingleAst()
let _rnglr_extra_array, _rnglr_rule_, _rnglr_concats = 
  (Array.zeroCreate 0 : array<'_rnglr_type_access_modifier_opt * '_rnglr_type_action_opt * '_rnglr_type_alts * '_rnglr_type_alts_call * '_rnglr_type_bar_seq_nlist * '_rnglr_type_boolean_grammar * '_rnglr_type_bound * '_rnglr_type_call * '_rnglr_type_error * '_rnglr_type_file * '_rnglr_type_foot_opt * '_rnglr_type_formal_meta_list * '_rnglr_type_formal_meta_param_opt * '_rnglr_type_ident * '_rnglr_type_include_ * '_rnglr_type_includes_or_options_or_tokens * '_rnglr_type_kw * '_rnglr_type_lbl_seq * '_rnglr_type_meta_param * '_rnglr_type_meta_param_opt * '_rnglr_type_meta_params * '_rnglr_type_module_ * '_rnglr_type_module_header * '_rnglr_type_modules * '_rnglr_type_negation_alts_call * '_rnglr_type_no_lbl_seq * '_rnglr_type_omit_opt * '_rnglr_type_open_list * '_rnglr_type_openings * '_rnglr_type_option * '_rnglr_type_option_block * '_rnglr_type_option_l_value * '_rnglr_type_option_value * '_rnglr_type_opts * '_rnglr_type_param_list * '_rnglr_type_param_opt * '_rnglr_type_patt * '_rnglr_type_predicate_opt * '_rnglr_type_prim * '_rnglr_type_rule * '_rnglr_type_rule_nlist * '_rnglr_type_semi_opt * '_rnglr_type_seq * '_rnglr_type_seq_elem * '_rnglr_type_seq_elem_list * '_rnglr_type_start_rule_sign_opt * '_rnglr_type_tada_rule * '_rnglr_type_tokens_block * '_rnglr_type_unnamed_module_opt * '_rnglr_type_weight_opt * '_rnglr_type_yard_start_rule>), 
  [|
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with MODULE _rnglr_val -> [_rnglr_val] | a -> failwith "MODULE expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 110 "Parser.fsy"
                             _S1
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 110 "Parser.fsy"
               : '_rnglr_type_kw) 
# 444 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with INCLUDE _rnglr_val -> [_rnglr_val] | a -> failwith "INCLUDE expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 110 "Parser.fsy"
                                            _S1
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 110 "Parser.fsy"
               : '_rnglr_type_kw) 
# 464 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with OPEN _rnglr_val -> [_rnglr_val] | a -> failwith "OPEN expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 110 "Parser.fsy"
                                                        _S1
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 110 "Parser.fsy"
               : '_rnglr_type_kw) 
# 484 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with PUBLIC _rnglr_val -> [_rnglr_val] | a -> failwith "PUBLIC expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 110 "Parser.fsy"
                                                                      _S1
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 110 "Parser.fsy"
               : '_rnglr_type_kw) 
# 504 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with PRIVATE _rnglr_val -> [_rnglr_val] | a -> failwith "PRIVATE expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 110 "Parser.fsy"
                                                                                     _S1
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 110 "Parser.fsy"
               : '_rnglr_type_kw) 
# 524 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_action_opt) 
             |> List.iter (fun (_S1) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_includes_or_options_or_tokens) 
               |> List.iter (fun (_S2) -> 
                ((unbox _rnglr_children.[2]) : '_rnglr_type_unnamed_module_opt) 
                 |> List.iter (fun (_S3) -> 
                  ((unbox _rnglr_children.[3]) : '_rnglr_type_modules) 
                   |> List.iter (fun (_S4) -> 
                    ((unbox _rnglr_children.[4]) : '_rnglr_type_foot_opt) 
                     |> List.iter (fun (_S5) -> 
                      (match ((unbox _rnglr_children.[5]) : Token) with EOF _rnglr_val -> [_rnglr_val] | a -> failwith "EOF expected, but %A found" a )
                       |> List.iter (fun (_) -> 
                        _rnglr_cycle_res := (
                          
# 118 "Parser.fsy"
                                  
                                  {
                                      info = { fileName = !currentFilename }
                                      head = _S1
                                      grammar = fst_ _S2 @ _S3 @ _S4
                                      foot = _S5
                                      options = snd_ _S2
                                      tokens = trd_ _S2
                                  }
                                
                            )::!_rnglr_cycle_res ) ) ) ) ) )
            !_rnglr_cycle_res
          )
            )
# 112 "Parser.fsy"
               : '_rnglr_type_file) 
# 563 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          ((unbox _rnglr_children.[0]) : '_rnglr_type_file) 
            )
# 112 "Parser.fsy"
               : '_rnglr_type_yard_start_rule) 
# 573 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 131 "Parser.fsy"
                     [],    Map.empty, Map.empty 
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 129 "Parser.fsy"
               : '_rnglr_type_includes_or_options_or_tokens) 
# 591 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_include_) 
             |> List.iter (fun (_S1) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_includes_or_options_or_tokens) 
               |> List.iter (fun (_S2) -> 
                _rnglr_cycle_res := (
                  
# 132 "Parser.fsy"
                                                                     (_S1 @ fst_ _S2), snd_ _S2, trd_ _S2
                    )::!_rnglr_cycle_res ) )
            !_rnglr_cycle_res
          )
            )
# 129 "Parser.fsy"
               : '_rnglr_type_includes_or_options_or_tokens) 
# 613 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_option_block) 
             |> List.iter (fun (_S1) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_includes_or_options_or_tokens) 
               |> List.iter (fun (_S2) -> 
                _rnglr_cycle_res := (
                  
# 133 "Parser.fsy"
                                                                     fst_ _S2, joinMaps _S1 (snd_ _S2), trd_ _S2
                    )::!_rnglr_cycle_res ) )
            !_rnglr_cycle_res
          )
            )
# 129 "Parser.fsy"
               : '_rnglr_type_includes_or_options_or_tokens) 
# 635 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_tokens_block) 
             |> List.iter (fun (_S1) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_includes_or_options_or_tokens) 
               |> List.iter (fun (_S2) -> 
                _rnglr_cycle_res := (
                  
# 134 "Parser.fsy"
                                                                   fst_ _S2, snd_ _S2, joinMaps _S1 (trd_ _S2)
                    )::!_rnglr_cycle_res ) )
            !_rnglr_cycle_res
          )
            )
# 129 "Parser.fsy"
               : '_rnglr_type_includes_or_options_or_tokens) 
# 657 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with TOKENS_BLOCK _rnglr_val -> [_rnglr_val] | a -> failwith "TOKENS_BLOCK expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 137 "Parser.fsy"
                   
                    let block = _S1.text
                    let inner = block.[block.IndexOf '{' + 1 .. block.LastIndexOf '}' - 1]
                    inner.Split [|'|'|]
                    |> Array.map (fun s -> s.Trim())
                    |> Array.filter ((<>) "")
                    |> Array.map (fun s ->
                        let genError msg = raise <| ParseError (new Source.t(s, fst parserRange, snd parserRange, !currentFilename),
                                                                "Error in tokens block: " + msg)
                        if Regex.IsMatch(s, @"^(_|[A-Z][A-Za-z0-9_]*)$") then s, None
                        else
                            let m = Regex.Match(s, @"^(_|[A-Z][A-Za-z0-9_]*)\s*of\s*(.*)$")
                            if m.Success then
                                m.Groups.[1].Value, Some m.Groups.[2].Value
                            else
                                if not (System.Char.IsUpper s.[0]) && not (s.[0] = '_' && s.Length > 1 && System.Char.IsWhiteSpace s.[1])
                                then genError "Terminal must start from upper letter"
                                else genError "Token type description is incorrect"
                            
                    ) |> Map.ofArray
                  
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 136 "Parser.fsy"
               : '_rnglr_type_tokens_block) 
# 697 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with INCLUDE _rnglr_val -> [_rnglr_val] | a -> failwith "INCLUDE expected, but %A found" a )
             |> List.iter (fun (_) -> 
              (match ((unbox _rnglr_children.[1]) : Token) with STRING _rnglr_val -> [_rnglr_val] | a -> failwith "STRING expected, but %A found" a )
               |> List.iter (fun (_S2) -> 
                _rnglr_cycle_res := (
                  
# 161 "Parser.fsy"
                       
                          let grammar = (parseRules _S2.text).grammar
                          if grammar |> List.exists (fun m -> m.name.IsNone) then
                              eprintfn "Error %s: Grammar in included files must be inside modules" _S2.text
                          grammar
                      
                    )::!_rnglr_cycle_res ) )
            !_rnglr_cycle_res
          )
            )
# 159 "Parser.fsy"
               : '_rnglr_type_include_) 
# 724 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with OPTIONS_START _rnglr_val -> [_rnglr_val] | a -> failwith "OPTIONS_START expected, but %A found" a )
             |> List.iter (fun (_) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_opts) 
               |> List.iter (fun (_S2) -> 
                (match ((unbox _rnglr_children.[2]) : Token) with BLOCK_END _rnglr_val -> [_rnglr_val] | a -> failwith "BLOCK_END expected, but %A found" a )
                 |> List.iter (fun (_) -> 
                  _rnglr_cycle_res := (
                    
# 168 "Parser.fsy"
                                                                 Map.ofList _S2 : Map<_,_>
                      )::!_rnglr_cycle_res ) ) )
            !_rnglr_cycle_res
          )
            )
# 168 "Parser.fsy"
               : '_rnglr_type_option_block) 
# 748 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_option) 
             |> List.iter (fun (_S1) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_opts) 
               |> List.iter (fun (_S2) -> 
                _rnglr_cycle_res := (
                  
# 170 "Parser.fsy"
                                      _S1::_S2 
                    )::!_rnglr_cycle_res ) )
            !_rnglr_cycle_res
          )
            )
# 170 "Parser.fsy"
               : '_rnglr_type_opts) 
# 770 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 170 "Parser.fsy"
                                               [] 
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 170 "Parser.fsy"
               : '_rnglr_type_opts) 
# 788 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_option_l_value) 
             |> List.iter (fun (_S1) -> 
              (match ((unbox _rnglr_children.[1]) : Token) with EQUAL _rnglr_val -> [_rnglr_val] | a -> failwith "EQUAL expected, but %A found" a )
               |> List.iter (fun (_) -> 
                ((unbox _rnglr_children.[2]) : '_rnglr_type_option_value) 
                 |> List.iter (fun (_S3) -> 
                  _rnglr_cycle_res := (
                    
# 172 "Parser.fsy"
                                                                (_S1 : Source.t).text, (_S3 : Source.t).text 
                      )::!_rnglr_cycle_res ) ) )
            !_rnglr_cycle_res
          )
            )
# 172 "Parser.fsy"
               : '_rnglr_type_option) 
# 812 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_ident) 
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 174 "Parser.fsy"
                                      _S1 
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 174 "Parser.fsy"
               : '_rnglr_type_option_value) 
# 832 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with STRING _rnglr_val -> [_rnglr_val] | a -> failwith "STRING expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 174 "Parser.fsy"
                                                      _S1 
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 174 "Parser.fsy"
               : '_rnglr_type_option_value) 
# 852 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_kw) 
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 174 "Parser.fsy"
                                                                  _S1 
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 174 "Parser.fsy"
               : '_rnglr_type_option_value) 
# 872 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_ident) 
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 176 "Parser.fsy"
                                        _S1 
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 176 "Parser.fsy"
               : '_rnglr_type_option_l_value) 
# 892 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_kw) 
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 176 "Parser.fsy"
                                                    _S1 
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 176 "Parser.fsy"
               : '_rnglr_type_option_l_value) 
# 912 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_rule_nlist) 
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 179 "Parser.fsy"
                     
                        match _S1 with
                        | [] -> []
                        | x ->  defaultModules x
                    
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 178 "Parser.fsy"
               : '_rnglr_type_unnamed_module_opt) 
# 936 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_module_) 
             |> List.iter (fun (_S1) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_modules) 
               |> List.iter (fun (_S2) -> 
                _rnglr_cycle_res := (
                  
# 185 "Parser.fsy"
                                              _S1 :: _S2 
                    )::!_rnglr_cycle_res ) )
            !_rnglr_cycle_res
          )
            )
# 185 "Parser.fsy"
               : '_rnglr_type_modules) 
# 958 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 185 "Parser.fsy"
                                                         [] 
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 185 "Parser.fsy"
               : '_rnglr_type_modules) 
# 976 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_module_header) 
             |> List.iter (fun (_S1) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_ident) 
               |> List.iter (fun (_S2) -> 
                ((unbox _rnglr_children.[2]) : '_rnglr_type_openings) 
                 |> List.iter (fun (_S3) -> 
                  ((unbox _rnglr_children.[3]) : '_rnglr_type_rule_nlist) 
                   |> List.iter (fun (_S4) -> 
                    _rnglr_cycle_res := (
                      
# 188 "Parser.fsy"
                           
                              {
                                  allPublic = _S1
                                  name = Some _S2
                                  openings = _S3
                                  rules = _S4
                              }
                          
                        )::!_rnglr_cycle_res ) ) ) )
            !_rnglr_cycle_res
          )
            )
# 187 "Parser.fsy"
               : '_rnglr_type_module_) 
# 1009 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with UIDENT _rnglr_val -> [_rnglr_val] | a -> failwith "UIDENT expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 197 "Parser.fsy"
                                 _S1 
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 197 "Parser.fsy"
               : '_rnglr_type_ident) 
# 1029 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with LIDENT _rnglr_val -> [_rnglr_val] | a -> failwith "LIDENT expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 197 "Parser.fsy"
                                                 _S1 
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 197 "Parser.fsy"
               : '_rnglr_type_ident) 
# 1049 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with ALL_PUBLIC _rnglr_val -> [_rnglr_val] | a -> failwith "ALL_PUBLIC expected, but %A found" a )
             |> List.iter (fun (_) -> 
              (match ((unbox _rnglr_children.[1]) : Token) with MODULE _rnglr_val -> [_rnglr_val] | a -> failwith "MODULE expected, but %A found" a )
               |> List.iter (fun (_) -> 
                _rnglr_cycle_res := (
                  
# 200 "Parser.fsy"
                                                     
                                    (* It's important the word "module" is here. It guaranties, that it won't be an epsilon-tree, so allPublic will be evaluated before rules *)
                                    allPublic := true; true
                                  
                    )::!_rnglr_cycle_res ) )
            !_rnglr_cycle_res
          )
            )
# 200 "Parser.fsy"
               : '_rnglr_type_module_header) 
# 1074 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with MODULE _rnglr_val -> [_rnglr_val] | a -> failwith "MODULE expected, but %A found" a )
             |> List.iter (fun (_) -> 
              _rnglr_cycle_res := (
                
# 204 "Parser.fsy"
                                         allPublic := false; false 
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 200 "Parser.fsy"
               : '_rnglr_type_module_header) 
# 1094 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 206 "Parser.fsy"
                            [] 
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 206 "Parser.fsy"
               : '_rnglr_type_openings) 
# 1112 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with OPEN _rnglr_val -> [_rnglr_val] | a -> failwith "OPEN expected, but %A found" a )
             |> List.iter (fun (_) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_ident) 
               |> List.iter (fun (_S2) -> 
                ((unbox _rnglr_children.[2]) : '_rnglr_type_open_list) 
                 |> List.iter (fun (_S3) -> 
                  _rnglr_cycle_res := (
                    
# 206 "Parser.fsy"
                                                                _S2::_S3 
                      )::!_rnglr_cycle_res ) ) )
            !_rnglr_cycle_res
          )
            )
# 206 "Parser.fsy"
               : '_rnglr_type_openings) 
# 1136 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with COMMA _rnglr_val -> [_rnglr_val] | a -> failwith "COMMA expected, but %A found" a )
             |> List.iter (fun (_) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_ident) 
               |> List.iter (fun (_S2) -> 
                ((unbox _rnglr_children.[2]) : '_rnglr_type_open_list) 
                 |> List.iter (fun (_S3) -> 
                  _rnglr_cycle_res := (
                    
# 208 "Parser.fsy"
                                                        _S2::_S3 
                      )::!_rnglr_cycle_res ) ) )
            !_rnglr_cycle_res
          )
            )
# 208 "Parser.fsy"
               : '_rnglr_type_open_list) 
# 1160 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 208 "Parser.fsy"
                                                               [] 
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 208 "Parser.fsy"
               : '_rnglr_type_open_list) 
# 1178 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 210 "Parser.fsy"
                            None 
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 210 "Parser.fsy"
               : '_rnglr_type_action_opt) 
# 1196 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with ACTION _rnglr_val -> [_rnglr_val] | a -> failwith "ACTION expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 210 "Parser.fsy"
                                                Some _S1 
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 210 "Parser.fsy"
               : '_rnglr_type_action_opt) 
# 1216 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 212 "Parser.fsy"
                          None 
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 212 "Parser.fsy"
               : '_rnglr_type_foot_opt) 
# 1234 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with SEMICOLON _rnglr_val -> [_rnglr_val] | a -> failwith "SEMICOLON expected, but %A found" a )
             |> List.iter (fun (_) -> 
              (match ((unbox _rnglr_children.[1]) : Token) with ACTION _rnglr_val -> [_rnglr_val] | a -> failwith "ACTION expected, but %A found" a )
               |> List.iter (fun (_S2) -> 
                _rnglr_cycle_res := (
                  
# 212 "Parser.fsy"
                                                          Some _S2 
                    )::!_rnglr_cycle_res ) )
            !_rnglr_cycle_res
          )
            )
# 212 "Parser.fsy"
               : '_rnglr_type_foot_opt) 
# 1256 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_rule) 
             |> List.iter (fun (_S1) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_semi_opt) 
               |> List.iter (fun (_) -> 
                ((unbox _rnglr_children.[2]) : '_rnglr_type_rule_nlist) 
                 |> List.iter (fun (_S3) -> 
                  _rnglr_cycle_res := (
                    
# 215 "Parser.fsy"
                            _S1::_S3 
                      )::!_rnglr_cycle_res ) ) )
            !_rnglr_cycle_res
          )
            )
# 214 "Parser.fsy"
               : '_rnglr_type_rule_nlist) 
# 1280 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 216 "Parser.fsy"
                      [] 
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 214 "Parser.fsy"
               : '_rnglr_type_rule_nlist) 
# 1298 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_start_rule_sign_opt) 
             |> List.iter (fun (_S1) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_access_modifier_opt) 
               |> List.iter (fun (_S2) -> 
                (match ((unbox _rnglr_children.[2]) : Token) with LIDENT _rnglr_val -> [_rnglr_val] | a -> failwith "LIDENT expected, but %A found" a )
                 |> List.iter (fun (_S3) -> 
                  ((unbox _rnglr_children.[3]) : '_rnglr_type_formal_meta_param_opt) 
                   |> List.iter (fun (_S4) -> 
                    ((unbox _rnglr_children.[4]) : '_rnglr_type_param_list) 
                     |> List.iter (fun (_S5) -> 
                      (match ((unbox _rnglr_children.[5]) : Token) with COLON _rnglr_val -> [_rnglr_val] | a -> failwith "COLON expected, but %A found" a )
                       |> List.iter (fun (_) -> 
                        ((unbox _rnglr_children.[6]) : '_rnglr_type_alts) 
                         |> List.iter (fun (_S7) -> 
                          _rnglr_cycle_res := (
                            
# 219 "Parser.fsy"
                                  
                                    {
                                        Rule.isStart = _S1
                                        Rule.isPublic = _S2
                                        Rule.name = _S3
                                        Rule.metaArgs = getList _S4
                                        Rule.body = _S7
                                        Rule.args = _S5
                                    }
                                
                              )::!_rnglr_cycle_res ) ) ) ) ) ) )
            !_rnglr_cycle_res
          )
            )
# 218 "Parser.fsy"
               : '_rnglr_type_rule) 
# 1339 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 230 "Parser.fsy"
                                    false
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 230 "Parser.fsy"
               : '_rnglr_type_start_rule_sign_opt) 
# 1357 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with START_RULE_SIGN _rnglr_val -> [_rnglr_val] | a -> failwith "START_RULE_SIGN expected, but %A found" a )
             |> List.iter (fun (_) -> 
              _rnglr_cycle_res := (
                
# 230 "Parser.fsy"
                                                                true
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 230 "Parser.fsy"
               : '_rnglr_type_start_rule_sign_opt) 
# 1377 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with PUBLIC _rnglr_val -> [_rnglr_val] | a -> failwith "PUBLIC expected, but %A found" a )
             |> List.iter (fun (_) -> 
              _rnglr_cycle_res := (
                
# 232 "Parser.fsy"
                                              true 
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 232 "Parser.fsy"
               : '_rnglr_type_access_modifier_opt) 
# 1397 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with PRIVATE _rnglr_val -> [_rnglr_val] | a -> failwith "PRIVATE expected, but %A found" a )
             |> List.iter (fun (_) -> 
              _rnglr_cycle_res := (
                
# 232 "Parser.fsy"
                                                                 false 
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 232 "Parser.fsy"
               : '_rnglr_type_access_modifier_opt) 
# 1417 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 232 "Parser.fsy"
                                                                           !allPublic 
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 232 "Parser.fsy"
               : '_rnglr_type_access_modifier_opt) 
# 1435 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 234 "Parser.fsy"
                                       None 
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 234 "Parser.fsy"
               : '_rnglr_type_formal_meta_param_opt) 
# 1453 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with LESS _rnglr_val -> [_rnglr_val] | a -> failwith "LESS expected, but %A found" a )
             |> List.iter (fun (_) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_formal_meta_list) 
               |> List.iter (fun (_S2) -> 
                (match ((unbox _rnglr_children.[2]) : Token) with GREAT _rnglr_val -> [_rnglr_val] | a -> failwith "GREAT expected, but %A found" a )
                 |> List.iter (fun (_) -> 
                  _rnglr_cycle_res := (
                    
# 234 "Parser.fsy"
                                                                                   Some _S2
                      )::!_rnglr_cycle_res ) ) )
            !_rnglr_cycle_res
          )
            )
# 234 "Parser.fsy"
               : '_rnglr_type_formal_meta_param_opt) 
# 1477 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with LIDENT _rnglr_val -> [_rnglr_val] | a -> failwith "LIDENT expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 236 "Parser.fsy"
                                          [_S1]
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 236 "Parser.fsy"
               : '_rnglr_type_formal_meta_list) 
# 1497 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with LIDENT _rnglr_val -> [_rnglr_val] | a -> failwith "LIDENT expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_formal_meta_list) 
               |> List.iter (fun (_S2) -> 
                _rnglr_cycle_res := (
                  
# 237 "Parser.fsy"
                                                             _S1::_S2
                    )::!_rnglr_cycle_res ) )
            !_rnglr_cycle_res
          )
            )
# 236 "Parser.fsy"
               : '_rnglr_type_formal_meta_list) 
# 1519 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 239 "Parser.fsy"
                           None 
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 239 "Parser.fsy"
               : '_rnglr_type_param_opt) 
# 1537 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with PARAM _rnglr_val -> [_rnglr_val] | a -> failwith "PARAM expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 239 "Parser.fsy"
                                             Some _S1
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 239 "Parser.fsy"
               : '_rnglr_type_param_opt) 
# 1557 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 241 "Parser.fsy"
                            [] 
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 241 "Parser.fsy"
               : '_rnglr_type_param_list) 
# 1575 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with PARAM _rnglr_val -> [_rnglr_val] | a -> failwith "PARAM expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_param_list) 
               |> List.iter (fun (_S2) -> 
                _rnglr_cycle_res := (
                  
# 241 "Parser.fsy"
                                                         _S1::_S2
                    )::!_rnglr_cycle_res ) )
            !_rnglr_cycle_res
          )
            )
# 241 "Parser.fsy"
               : '_rnglr_type_param_list) 
# 1597 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 243 "Parser.fsy"
                            None 
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 243 "Parser.fsy"
               : '_rnglr_type_weight_opt) 
# 1615 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with SQR_LBR _rnglr_val -> [_rnglr_val] | a -> failwith "SQR_LBR expected, but %A found" a )
             |> List.iter (fun (_) -> 
              (match ((unbox _rnglr_children.[1]) : Token) with NUMBER _rnglr_val -> [_rnglr_val] | a -> failwith "NUMBER expected, but %A found" a )
               |> List.iter (fun (_S2) -> 
                (match ((unbox _rnglr_children.[2]) : Token) with SQR_RBR _rnglr_val -> [_rnglr_val] | a -> failwith "SQR_RBR expected, but %A found" a )
                 |> List.iter (fun (_) -> 
                  _rnglr_cycle_res := (
                    
# 243 "Parser.fsy"
                                                                    Some _S2
                      )::!_rnglr_cycle_res ) ) )
            !_rnglr_cycle_res
          )
            )
# 243 "Parser.fsy"
               : '_rnglr_type_weight_opt) 
# 1639 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_seq) 
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 245 "Parser.fsy"
                            _S1 
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 245 "Parser.fsy"
               : '_rnglr_type_alts) 
# 1659 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_seq) 
             |> List.iter (fun (_S1) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_bar_seq_nlist) 
               |> List.iter (fun (_S2) -> 
                _rnglr_cycle_res := (
                  
# 245 "Parser.fsy"
                                                        PAlt (_S1,_S2)
                    )::!_rnglr_cycle_res ) )
            !_rnglr_cycle_res
          )
            )
# 245 "Parser.fsy"
               : '_rnglr_type_alts) 
# 1681 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with BAR _rnglr_val -> [_rnglr_val] | a -> failwith "BAR expected, but %A found" a )
             |> List.iter (fun (_) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_seq) 
               |> List.iter (fun (_S2) -> 
                ((unbox _rnglr_children.[2]) : '_rnglr_type_bar_seq_nlist) 
                 |> List.iter (fun (_S3) -> 
                  _rnglr_cycle_res := (
                    
# 247 "Parser.fsy"
                                                           PAlt(_S2,_S3) 
                      )::!_rnglr_cycle_res ) ) )
            !_rnglr_cycle_res
          )
            )
# 247 "Parser.fsy"
               : '_rnglr_type_bar_seq_nlist) 
# 1705 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with BAR _rnglr_val -> [_rnglr_val] | a -> failwith "BAR expected, but %A found" a )
             |> List.iter (fun (_) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_seq) 
               |> List.iter (fun (_S2) -> 
                _rnglr_cycle_res := (
                  
# 248 "Parser.fsy"
                                           _S2
                    )::!_rnglr_cycle_res ) )
            !_rnglr_cycle_res
          )
            )
# 247 "Parser.fsy"
               : '_rnglr_type_bar_seq_nlist) 
# 1727 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_lbl_seq) 
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 250 "Parser.fsy"
                              _S1
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 250 "Parser.fsy"
               : '_rnglr_type_seq) 
# 1747 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_no_lbl_seq) 
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 250 "Parser.fsy"
                                                _S1
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 250 "Parser.fsy"
               : '_rnglr_type_seq) 
# 1767 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_seq_elem) 
             |> List.iter (fun (_S1) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_seq_elem_list) 
               |> List.iter (fun (_S2) -> 
                ((unbox _rnglr_children.[2]) : '_rnglr_type_action_opt) 
                 |> List.iter (fun (_S3) -> 
                  _rnglr_cycle_res := (
                    
# 252 "Parser.fsy"
                                                                    PSeq (_S1::_S2, _S3, None)
                      )::!_rnglr_cycle_res ) ) )
            !_rnglr_cycle_res
          )
            )
# 252 "Parser.fsy"
               : '_rnglr_type_no_lbl_seq) 
# 1791 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with ACTION _rnglr_val -> [_rnglr_val] | a -> failwith "ACTION expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 253 "Parser.fsy"
                                     PSeq([], Some _S1, None) 
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 252 "Parser.fsy"
               : '_rnglr_type_no_lbl_seq) 
# 1811 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with DLABEL _rnglr_val -> [_rnglr_val] | a -> failwith "DLABEL expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_weight_opt) 
               |> List.iter (fun (_S2) -> 
                (match ((unbox _rnglr_children.[2]) : Token) with LPAREN _rnglr_val -> [_rnglr_val] | a -> failwith "LPAREN expected, but %A found" a )
                 |> List.iter (fun (_) -> 
                  ((unbox _rnglr_children.[3]) : '_rnglr_type_no_lbl_seq) 
                   |> List.iter (fun (_S4) -> 
                    (match ((unbox _rnglr_children.[4]) : Token) with RPAREN _rnglr_val -> [_rnglr_val] | a -> failwith "RPAREN expected, but %A found" a )
                     |> List.iter (fun (_) -> 
                      _rnglr_cycle_res := (
                        
# 255 "Parser.fsy"
                                                                             makeNewSeq _S4 _S1 _S2
                          )::!_rnglr_cycle_res ) ) ) ) )
            !_rnglr_cycle_res
          )
            )
# 255 "Parser.fsy"
               : '_rnglr_type_lbl_seq) 
# 1839 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 257 "Parser.fsy"
                               [] 
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 257 "Parser.fsy"
               : '_rnglr_type_seq_elem_list) 
# 1857 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_seq_elem) 
             |> List.iter (fun (_S1) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_seq_elem_list) 
               |> List.iter (fun (_S2) -> 
                _rnglr_cycle_res := (
                  
# 257 "Parser.fsy"
                                                                  _S1::_S2
                    )::!_rnglr_cycle_res ) )
            !_rnglr_cycle_res
          )
            )
# 257 "Parser.fsy"
               : '_rnglr_type_seq_elem_list) 
# 1879 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_omit_opt) 
             |> List.iter (fun (_S1) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_bound) 
               |> List.iter (fun (_S2) -> 
                ((unbox _rnglr_children.[2]) : '_rnglr_type_predicate_opt) 
                 |> List.iter (fun (_S3) -> 
                  _rnglr_cycle_res := (
                    
# 259 "Parser.fsy"
                                                            {_S2 with checker = _S3; omit = _S1 }
                      )::!_rnglr_cycle_res ) ) )
            !_rnglr_cycle_res
          )
            )
# 259 "Parser.fsy"
               : '_rnglr_type_seq_elem) 
# 1903 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 261 "Parser.fsy"
                          false 
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 261 "Parser.fsy"
               : '_rnglr_type_omit_opt) 
# 1921 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with MINUS _rnglr_val -> [_rnglr_val] | a -> failwith "MINUS expected, but %A found" a )
             |> List.iter (fun (_) -> 
              _rnglr_cycle_res := (
                
# 261 "Parser.fsy"
                                              true 
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 261 "Parser.fsy"
               : '_rnglr_type_omit_opt) 
# 1941 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 263 "Parser.fsy"
                           false 
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 263 "Parser.fsy"
               : '_rnglr_type_semi_opt) 
# 1959 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with SEMICOLON _rnglr_val -> [_rnglr_val] | a -> failwith "SEMICOLON expected, but %A found" a )
             |> List.iter (fun (_) -> 
              _rnglr_cycle_res := (
                
# 263 "Parser.fsy"
                                                  true
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 263 "Parser.fsy"
               : '_rnglr_type_semi_opt) 
# 1979 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 265 "Parser.fsy"
                               None 
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 265 "Parser.fsy"
               : '_rnglr_type_predicate_opt) 
# 1997 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with PREDICATE _rnglr_val -> [_rnglr_val] | a -> failwith "PREDICATE expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 265 "Parser.fsy"
                                                      Some _S1 
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 265 "Parser.fsy"
               : '_rnglr_type_predicate_opt) 
# 2017 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_patt) 
             |> List.iter (fun (_S1) -> 
              (match ((unbox _rnglr_children.[1]) : Token) with EQUAL _rnglr_val -> [_rnglr_val] | a -> failwith "EQUAL expected, but %A found" a )
               |> List.iter (fun (_) -> 
                ((unbox _rnglr_children.[2]) : '_rnglr_type_prim) 
                 |> List.iter (fun (_S3) -> 
                  _rnglr_cycle_res := (
                    
# 267 "Parser.fsy"
                                             createSeqElem (Some _S1) false _S3 None 
                      )::!_rnglr_cycle_res ) ) )
            !_rnglr_cycle_res
          )
            )
# 267 "Parser.fsy"
               : '_rnglr_type_bound) 
# 2041 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_prim) 
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 268 "Parser.fsy"
                                         createSeqElem None false _S1 None      
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 267 "Parser.fsy"
               : '_rnglr_type_bound) 
# 2061 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with LIDENT _rnglr_val -> [_rnglr_val] | a -> failwith "LIDENT expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 270 "Parser.fsy"
                              _S1
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 270 "Parser.fsy"
               : '_rnglr_type_patt) 
# 2081 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with ACTION _rnglr_val -> [_rnglr_val] | a -> failwith "ACTION expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 270 "Parser.fsy"
                                            _S1
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 270 "Parser.fsy"
               : '_rnglr_type_patt) 
# 2101 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_prim) 
             |> List.iter (fun (_S1) -> 
              (match ((unbox _rnglr_children.[1]) : Token) with STAR _rnglr_val -> [_rnglr_val] | a -> failwith "STAR expected, but %A found" a )
               |> List.iter (fun (_) -> 
                _rnglr_cycle_res := (
                  
# 272 "Parser.fsy"
                                              PMany _S1
                    )::!_rnglr_cycle_res ) )
            !_rnglr_cycle_res
          )
            )
# 272 "Parser.fsy"
               : '_rnglr_type_prim) 
# 2123 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_prim) 
             |> List.iter (fun (_S1) -> 
              (match ((unbox _rnglr_children.[1]) : Token) with PLUS _rnglr_val -> [_rnglr_val] | a -> failwith "PLUS expected, but %A found" a )
               |> List.iter (fun (_) -> 
                _rnglr_cycle_res := (
                  
# 273 "Parser.fsy"
                                              PSome _S1
                    )::!_rnglr_cycle_res ) )
            !_rnglr_cycle_res
          )
            )
# 272 "Parser.fsy"
               : '_rnglr_type_prim) 
# 2145 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_prim) 
             |> List.iter (fun (_S1) -> 
              (match ((unbox _rnglr_children.[1]) : Token) with QUESTION _rnglr_val -> [_rnglr_val] | a -> failwith "QUESTION expected, but %A found" a )
               |> List.iter (fun (_) -> 
                _rnglr_cycle_res := (
                  
# 274 "Parser.fsy"
                                              POpt _S1
                    )::!_rnglr_cycle_res ) )
            !_rnglr_cycle_res
          )
            )
# 272 "Parser.fsy"
               : '_rnglr_type_prim) 
# 2167 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with SQR_LBR _rnglr_val -> [_rnglr_val] | a -> failwith "SQR_LBR expected, but %A found" a )
             |> List.iter (fun (_) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_alts) 
               |> List.iter (fun (_S2) -> 
                (match ((unbox _rnglr_children.[2]) : Token) with SQR_RBR _rnglr_val -> [_rnglr_val] | a -> failwith "SQR_RBR expected, but %A found" a )
                 |> List.iter (fun (_) -> 
                  _rnglr_cycle_res := (
                    
# 275 "Parser.fsy"
                                                POpt _S2
                      )::!_rnglr_cycle_res ) ) )
            !_rnglr_cycle_res
          )
            )
# 272 "Parser.fsy"
               : '_rnglr_type_prim) 
# 2191 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with LPAREN _rnglr_val -> [_rnglr_val] | a -> failwith "LPAREN expected, but %A found" a )
             |> List.iter (fun (_) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_alts) 
               |> List.iter (fun (_S2) -> 
                (match ((unbox _rnglr_children.[2]) : Token) with RPAREN _rnglr_val -> [_rnglr_val] | a -> failwith "RPAREN expected, but %A found" a )
                 |> List.iter (fun (_) -> 
                  _rnglr_cycle_res := (
                    
# 276 "Parser.fsy"
                                                _S2
                      )::!_rnglr_cycle_res ) ) )
            !_rnglr_cycle_res
          )
            )
# 272 "Parser.fsy"
               : '_rnglr_type_prim) 
# 2215 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_call) 
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 277 "Parser.fsy"
                                            _S1
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 272 "Parser.fsy"
               : '_rnglr_type_prim) 
# 2235 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_lbl_seq) 
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 278 "Parser.fsy"
                                            _S1
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 272 "Parser.fsy"
               : '_rnglr_type_prim) 
# 2255 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with LITERAL _rnglr_val -> [_rnglr_val] | a -> failwith "LITERAL expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 279 "Parser.fsy"
                                            PLiteral _S1
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 272 "Parser.fsy"
               : '_rnglr_type_prim) 
# 2275 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_boolean_grammar) 
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 280 "Parser.fsy"
                                         _S1
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 272 "Parser.fsy"
               : '_rnglr_type_prim) 
# 2295 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_prim) 
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 282 "Parser.fsy"
                                  _S1
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 282 "Parser.fsy"
               : '_rnglr_type_meta_param) 
# 2315 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_meta_param) 
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 284 "Parser.fsy"
                                         [_S1]
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 284 "Parser.fsy"
               : '_rnglr_type_meta_params) 
# 2335 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_meta_param) 
             |> List.iter (fun (_S1) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_meta_params) 
               |> List.iter (fun (_S2) -> 
                _rnglr_cycle_res := (
                  
# 285 "Parser.fsy"
                                                       _S1 :: _S2
                    )::!_rnglr_cycle_res ) )
            !_rnglr_cycle_res
          )
            )
# 284 "Parser.fsy"
               : '_rnglr_type_meta_params) 
# 2357 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              
# 287 "Parser.fsy"
                                None 
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )
# 287 "Parser.fsy"
               : '_rnglr_type_meta_param_opt) 
# 2375 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with LESS _rnglr_val -> [_rnglr_val] | a -> failwith "LESS expected, but %A found" a )
             |> List.iter (fun (_) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_meta_params) 
               |> List.iter (fun (_S2) -> 
                (match ((unbox _rnglr_children.[2]) : Token) with GREAT _rnglr_val -> [_rnglr_val] | a -> failwith "GREAT expected, but %A found" a )
                 |> List.iter (fun (_) -> 
                  _rnglr_cycle_res := (
                    
# 287 "Parser.fsy"
                                                                       Some _S2
                      )::!_rnglr_cycle_res ) ) )
            !_rnglr_cycle_res
          )
            )
# 287 "Parser.fsy"
               : '_rnglr_type_meta_param_opt) 
# 2399 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with UIDENT _rnglr_val -> [_rnglr_val] | a -> failwith "UIDENT expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 289 "Parser.fsy"
                              PToken _S1
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 289 "Parser.fsy"
               : '_rnglr_type_call) 
# 2419 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with LIDENT _rnglr_val -> [_rnglr_val] | a -> failwith "LIDENT expected, but %A found" a )
             |> List.iter (fun (_S1) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_meta_param_opt) 
               |> List.iter (fun (_S2) -> 
                ((unbox _rnglr_children.[2]) : '_rnglr_type_param_opt) 
                 |> List.iter (fun (_S3) -> 
                  _rnglr_cycle_res := (
                    
# 291 "Parser.fsy"
                            match _S2 with
                            | None -> PRef  (_S1, _S3)
                            | Some x -> PMetaRef (_S1,_S3,x)
                          
                      )::!_rnglr_cycle_res ) ) )
            !_rnglr_cycle_res
          )
            )
# 289 "Parser.fsy"
               : '_rnglr_type_call) 
# 2446 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with SHARPLINE _rnglr_val -> [_rnglr_val] | a -> failwith "SHARPLINE expected, but %A found" a )
             |> List.iter (fun (_) -> 
              _rnglr_cycle_res := (
                
# 296 "Parser.fsy"
                                       
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 296 "Parser.fsy"
               : '_rnglr_type_tada_rule) 
# 2466 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with EOF _rnglr_val -> [_rnglr_val] | a -> failwith "EOF expected, but %A found" a )
             |> List.iter (fun (_) -> 
              _rnglr_cycle_res := (
                
# 296 "Parser.fsy"
                                                
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 296 "Parser.fsy"
               : '_rnglr_type_tada_rule) 
# 2486 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with LPAREN _rnglr_val -> [_rnglr_val] | a -> failwith "LPAREN expected, but %A found" a )
             |> List.iter (fun (_) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_alts) 
               |> List.iter (fun (_S2) -> 
                (match ((unbox _rnglr_children.[2]) : Token) with RPAREN _rnglr_val -> [_rnglr_val] | a -> failwith "RPAREN expected, but %A found" a )
                 |> List.iter (fun (_) -> 
                  _rnglr_cycle_res := (
                    
# 298 "Parser.fsy"
                                                    _S2
                      )::!_rnglr_cycle_res ) ) )
            !_rnglr_cycle_res
          )
            )
# 298 "Parser.fsy"
               : '_rnglr_type_alts_call) 
# 2510 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_call) 
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 298 "Parser.fsy"
                                                            _S1
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 298 "Parser.fsy"
               : '_rnglr_type_alts_call) 
# 2530 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            (match ((unbox _rnglr_children.[0]) : Token) with EXCLAMATION _rnglr_val -> [_rnglr_val] | a -> failwith "EXCLAMATION expected, but %A found" a )
             |> List.iter (fun (_) -> 
              ((unbox _rnglr_children.[1]) : '_rnglr_type_alts_call) 
               |> List.iter (fun (_S2) -> 
                _rnglr_cycle_res := (
                  
# 300 "Parser.fsy"
                                                              PNegat _S2
                    )::!_rnglr_cycle_res ) )
            !_rnglr_cycle_res
          )
            )
# 300 "Parser.fsy"
               : '_rnglr_type_negation_alts_call) 
# 2552 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_alts_call) 
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 300 "Parser.fsy"
                                                                                    _S1
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 300 "Parser.fsy"
               : '_rnglr_type_negation_alts_call) 
# 2572 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_negation_alts_call) 
             |> List.iter (fun (_S1) -> 
              _rnglr_cycle_res := (
                
# 302 "Parser.fsy"
                                                      _S1
                  )::!_rnglr_cycle_res )
            !_rnglr_cycle_res
          )
            )
# 302 "Parser.fsy"
               : '_rnglr_type_boolean_grammar) 
# 2592 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            ((unbox _rnglr_children.[0]) : '_rnglr_type_negation_alts_call) 
             |> List.iter (fun (_S1) -> 
              (match ((unbox _rnglr_children.[1]) : Token) with AMPERSAND _rnglr_val -> [_rnglr_val] | a -> failwith "AMPERSAND expected, but %A found" a )
               |> List.iter (fun (_) -> 
                ((unbox _rnglr_children.[2]) : '_rnglr_type_boolean_grammar) 
                 |> List.iter (fun (_S3) -> 
                  _rnglr_cycle_res := (
                    
# 302 "Parser.fsy"
                                                                                                              PConjuct (_S1, _S3)
                      )::!_rnglr_cycle_res ) ) )
            !_rnglr_cycle_res
          )
            )
# 302 "Parser.fsy"
               : '_rnglr_type_boolean_grammar) 
# 2616 "Parser.fs"
      );
  (
    fun (_rnglr_children : array<_>) (parserRange : (Source.Position * Source.Position)) -> 
      box (
        ( 
          (
            let _rnglr_cycle_res = ref []
            _rnglr_cycle_res := (
              

              parserRange
                )::!_rnglr_cycle_res
            !_rnglr_cycle_res
          )
            )

               : '_rnglr_type_error) 
# 2634 "Parser.fs"
      );
  |] , [|
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_access_modifier_opt)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_action_opt)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_alts)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_alts_call)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_bar_seq_nlist)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_boolean_grammar)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_bound)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_call)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_error)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_file)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_foot_opt)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_formal_meta_list)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_formal_meta_param_opt)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_ident)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_include_)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_includes_or_options_or_tokens)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_kw)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_lbl_seq)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_meta_param)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_meta_param_opt)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_meta_params)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_module_)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_module_header)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_modules)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_negation_alts_call)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_no_lbl_seq)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_omit_opt)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_open_list)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_openings)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_option)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_option_block)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_option_l_value)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_option_value)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_opts)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_param_list)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_param_opt)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_patt)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_predicate_opt)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_prim)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_rule)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_rule_nlist)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_semi_opt)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_seq)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_seq_elem)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_seq_elem_list)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_start_rule_sign_opt)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_tada_rule)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_tokens_block)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_unnamed_module_opt)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_weight_opt)   ) |> List.concat));
    (fun (_rnglr_list : list<_>) -> 
      box ( 
        _rnglr_list |> List.map (fun _rnglr_item -> ((unbox _rnglr_item) : '_rnglr_type_yard_start_rule)   ) |> List.concat));
  |] 
let translate (args : TranslateArguments<_,_>) (tree : Tree<_>) : '_rnglr_type_yard_start_rule = 
  unbox (tree.Translate _rnglr_rule_  leftSide _rnglr_concats (if args.filterEpsilons then _rnglr_filtered_epsilons else _rnglr_epsilons) args.tokenToRange args.zeroPosition args.clearAST) : '_rnglr_type_yard_start_rule
