﻿module Yard.Generators.RNGLR.ParserEBNF        


open Yard.Generators.RNGLR.AST
open Yard.Generators.RNGLR.StackLabel
open Yard.Generators.RNGLR.EBNF
open System.Collections.Generic
open Yard.Generators.RNGLR.DataStructures
open Microsoft.FSharp.Collections
// Custom graph structure. For optimization and needed (by algorithm) relation with AST

[<AllowNullLiteral>]
type Vertex  =
    val mutable OutEdges : UsualOne<Edge>
    /// Number of token, processed when the vertex was created
    val Level : int
    /// Usual LALR state
    val State : int
    new (state, level) = {OutEdges = Unchecked.defaultof<_>; State = state; Level = level}

and Edge =
    struct
        /// AST on the edge
        val Ast : obj
        val StackAction : StackLabel
        /// End of the vertex (begin is not needed)
        val Dest : Vertex
        new (d, s, a) = {Dest = d; StackAction = s; Ast = a}
    end

type ParserDebugFuns<'TokenType> = {
    drawGSSDot : string -> unit
    /// If you need more then one last token
    lastTokens : int -> 'TokenType[]
}

type ParseResultEBNF<'TokenType> =
    | Success of Tree<'TokenType> * Dictionary<Family, ErrorNode>
    | Error of int * array<'TokenType> * string * Dictionary<Family, ErrorNode>

/// Compare vertex like a pair: (level, state)
let inline private less (v' : Vertex) (v : Vertex) = v'.Level < v.Level || (v'.Level = v.Level && v'.State < v.State)
let inline private eq (v' : Vertex) (v : Vertex) = v'.Level = v.Level && v'.State = v.State

//Compare stack label
let private stackLabeltoPair = function
    |DontStack -> (0, 0)
    |Stack x -> (1, x)
    |StackingConflict x -> (2, x)

let inline private stLLess (s' : StackLabel) (s : StackLabel) = 
    let s'x, s'y = stackLabeltoPair s'
    let sx, sy = stackLabeltoPair s
    s'x < sx || (s'x = sx && s'y < sy)

let inline private stLEq (s' : StackLabel) (s : StackLabel) = 
    let s'x, s'y = stackLabeltoPair s'
    let sx, sy = stackLabeltoPair s
    s'x = sx && s'y = sy

/// Add edges, what must be unique (after shift or epsilon-edges).
/// All edges are sorted by destination ascending.
let private addSimpleEdge (v : Vertex) (stackLabel : StackLabel) (ast : obj) (out : ResizeArray<Vertex * StackLabel * obj>) =
    let inline fst3 (x,_,_) = x
    let inline snd3 (_,x,_) = x
    let mutable i = out.Count - 1
    while i >= 0 && less (fst3 out.[i]) v do
        i <- i - 1
    while i >= 0 && eq (fst3 out.[i]) v && stLLess (snd3 out.[i]) stackLabel do
        i <- i - 1
    out.Insert (i+1, (v, stackLabel, ast))

/// Check if edge with specified destination and AST already exists
let private containsSimpleEdge (v : Vertex) (s : StackLabel) (f : obj) (out : ResizeArray<Vertex * StackLabel * obj>) =
    let inline fst3 (x,_,_) = x
    let inline snd3 (_,x,_) = x
    let mutable i = out.Count - 1
    while i >= 0 && less (fst3 out.[i]) v do
        i <- i - 1
    while i >= 0 && eq (fst3 out.[i]) v && stLLess (snd3 out.[i]) s do
        i <- i - 1
    while i >= 0 && (let v',s',f' = out.[i] in eq v' v && stLEq s' s && f <> f') do
        i <- i - 1
    i >= 0 && (let v',s',f' = out.[i] in eq v' v && stLEq s' s && f = f')

/// Add or extend edge with specified destination and family.
/// All edges are sorted by destination ascending.
let private addEdge (v : Vertex) (s : StackLabel) (family : Family) (out : ResizeArray<Vertex * StackLabel * Family * AST>) isError =
    let mutable i = out.Count - 1
    let inline fst4 (x,_,_,_) = x
    let inline snd4 (_,x,_,_) = x
    let inline trd4 (_,_,x,_) = x
    while i >= 0 && less (fst4 out.[i]) v do
        i <- i - 1
    while i >= 0 && eq (fst4 out.[i]) v && stLLess (snd4 out.[i]) s do
        i <- i - 1

    let isCreated = not (i >= 0 && eq (fst4 out.[i]) v && stLEq (snd4 out.[i]) s)

    let ast = 
        if isError
        then new AST(family, null)
        else 
            if not isCreated 
            then let _,_,_,n = out.[i] in n
            else new AST (Unchecked.defaultof<_>, null)
    let newVal = v, s, family, ast
    if isCreated || family.prod = (trd4 out.[i]).prod then
        out.Insert (i+1, newVal)
    elif family.prod < (trd4 out.[i]).prod then
        out.[i] <- newVal
        let mutable j = i-1
        while j >= 0 && stLEq (snd4 out.[j]) (snd4 out.[i]) && eq (fst4 out.[j])  (fst4 out.[i]) do
            j <- j-1
        out.RemoveRange(j+1, i-j-1)
    isCreated, ast

/// Check if edge with specified destination and family already exists
let private containsEdge (v : Vertex) (s : StackLabel) (f : Family) (out : ResizeArray<Vertex * StackLabel * Family * AST>) =
    let inline fst4 (x,_,_,_) = x
    let inline snd4 (_,x,_,_) = x
    let mutable i = out.Count - 1
    while i >= 0 && less (fst4 out.[i]) v do
        i <- i - 1
    while i >= 0 && eq (fst4 out.[i]) v && stLLess (snd4 out.[i]) s do
        i <- i - 1
    while i >= 0 && (let v',s',f',_ = out.[i] in eq v' v && stLEq s' s && f <> f') do
        i <- i - 1
    i >= 0 && (let v',s',f',_ = out.[i] in eq v' v && stLEq s' s && f = f')

let drawDot (tokenToNumber : _ -> int) (tokens : BlockResizeArray<_>) (leftSide : int[])
        (initNodes : seq<Vertex>) (numToString : int -> string) (errInd: int) (path : string) =
    use out = new System.IO.StreamWriter (path)
    let was = new Dictionary<_,_>()
    let levels = new Dictionary<_,_>()
    out.WriteLine "digraph GSS {"
    let print s = out.WriteLine ("    " + s)
    let curNum = ref 0
    print "rankdir=RL"
    let getAstString (ast : obj) =
        match ast with
        | :? int as i when i >= 0 -> tokens.[i] |> tokenToNumber |> numToString |> sprintf "%s"    
        | :? int as i when i < 0 -> "eps " + numToString (-i-1)
        | :? AST as ast -> 
            let nonT = 
                if ast.first.prod < leftSide.Length then ast.first.prod
                else errInd
            numToString leftSide.[nonT]
        | _ -> failwith "Unexpected ast"

    let rec dfs (u : Vertex) =
        was.Add (u, !curNum)
        if not <| levels.ContainsKey u.Level then
            levels.[u.Level] <- [!curNum]
        else
            levels.[u.Level] <- !curNum :: levels.[u.Level]
        print <| sprintf "%d [label=\"%d\"]" !curNum u.State
        incr curNum
        if not (u.Level = 0 && u.State = 0) && u.OutEdges.first <> Unchecked.defaultof<_> then
            handleEdge u u.OutEdges.first
            if u.OutEdges.other <> null then
                u.OutEdges.other |> Array.iter (handleEdge u)

    and handleEdge u (e : Edge) =
        let v = e.Dest
        if not <| was.ContainsKey v then
            dfs v
        print <| sprintf "%d -> %d [label=\"%s\"]" was.[u] was.[v] (getAstString e.Ast)

    for v in initNodes do
        if not <| was.ContainsKey v then
            dfs v
    
    for level in levels do
        print <| sprintf "{rank=same; %s}" (level.Value |> List.map (fun (u : int) -> string u) |> String.concat " ")

    out.WriteLine "}"
    out.Close()

type ReduceLabel =
    |Reduce
    |StackReduce

let buildAst<'TokenType> (parserSource : ParserSourceEBNF<'TokenType>) (tokens : seq<'TokenType>) =
    let enum = tokens.GetEnumerator()
    // Change if it doesn't equal to zero. Now it's true according to states building algorithm
    let startState = 0
    let startNonTerm = parserSource.LeftSide.[parserSource.StartRule]
    let nonTermsCountLimit = 1 + (Array.max parserSource.LeftSide)
    let getEpsilon =
        let epsilons = Array.init nonTermsCountLimit (fun i -> box (-i-1))
        fun i -> epsilons.[i]
    /// info about errors
    let errDict = new Dictionary<Family, ErrorNode>()
                              
    let getExpectedGoto i j =
        match parserSource.Gotos.[i].[j] with
            |Some x -> x
            |None -> failwithf "Expected goto[%d][%s]" i (parserSource.NumToString j)

    // If input stream is empty or consists only of RNGLR_EOF token
    if not <| enum.MoveNext() || parserSource.EofIndex = parserSource.TokenToNumber enum.Current then
        if parserSource.AcceptEmptyInput 
        then
            Success (new Tree<_>(null, getEpsilon startNonTerm, null), errDict)
        else
            Error (0, [||], "This grammar cannot accept empty string",
                    (*{
                        drawGSSDot = fun _ -> ()
                        lastTokens = fun _ -> [||]
                    }, *)
                    errDict)
    else                                     
        // Currently processed token
        let curToken = ref enum.Current
        let curNum = ref (parserSource.TokenToNumber enum.Current)
        /// Here all tokens from the input will be collected
        let tokens = new BlockResizeArray<_>()
        let reductions = new Stack<_>(10)
        let statesCount = parserSource.Gotos.Length
        // New edges can be created only from last level.
        /// Temporary storage for edges data (after all reductions real edges will be created).
        let edges = Array.init statesCount (fun _ -> new ResizeArray<Vertex * StackLabel * Family * AST>())
        let simpleEdges = Array.init statesCount (fun _ -> new ResizeArray<Vertex * StackLabel * obj>())

        let pushes = new Stack<_> (statesCount * 2 + 10)
        /// Stores states, used on current level. Instead statesCount must be number of non-terminals, but doesn't matter
        let usedStates = new Stack<_>(statesCount)
        let stateToVertex : Vertex[] = Array.zeroCreate statesCount

        let addVertex state level (edgeOpt : option<Vertex * StackLabel * obj>) =
            let dict = stateToVertex
            if dict.[state] = null then
                let v = new Vertex(state, level)
                dict.[state] <- v
                
                match parserSource.Gotos.[state].[!curNum] with
                | Some x ->
                    let push = x
                    // Push to init state is impossible
                    if fst push <> 0 then
                        pushes.Push (v, push)
                | None -> ()
                let arr = parserSource.ZeroReduces.[state].[!curNum]
                if arr <> null then
                    for prod in arr do
                        reductions.Push (v, prod, StackReduce, None)
                usedStates.Push state
            let v = dict.[state]
            if edgeOpt.IsSome then 
                let arr = parserSource.Reduces.[state].[!curNum]
                if arr <> null then
                    for prod in arr do
                        reductions.Push (v, prod, Reduce, edgeOpt)
            v

        ignore <| addVertex startState 0 None
        let inline fst3 (x,_,_) = x
        let inline snd3 (_,x,_) = x
        let inline trd (_,_,x) = x
        let inline trd4 (_,_,x,_) = x
        let inline frth (_,_,_,x) = x
        let makeReductions num recovery =
            while reductions.Count > 0 do
                let vertex, prod, rLabel, edgeOpt = reductions.Pop()
                let nonTerm = parserSource.LeftSide.[prod]
                let vertexSet = ref Set.empty

                let handlePath (path : obj list) (final : Vertex) =
                    if final = null
                    then recovery()//pushes.Clear()
                    else
                        
                        let state,stackLabel = getExpectedGoto final.State nonTerm
                        let newVertex = addVertex state num None
                    
                        let family = new Family(prod, new Nodes(Array.ofList path))
                        if not <| containsEdge final stackLabel family edges.[state] then
                            let isCreated, edgeLabel = addEdge final stackLabel family edges.[state] false
                            if (rLabel = Reduce && isCreated) then
                                let arr = parserSource.Reduces.[state].[!curNum]
                                if arr <> null then
                                    for prod in arr do
                                        reductions.Push (newVertex, prod, Reduce, Some (final, stackLabel, box edgeLabel))

                let rec walk (vertex : Vertex) (stackLabel : StackLabel) prod (path : obj list) =
                    let handle, walkFurther =
                        match stackLabel with
                        |DontStack -> false, true
                        |Stack x -> if parserSource.StackSets.[x].Contains prod then true,false else false,false
                        |StackingConflict x -> if parserSource.StackSets.[x].Contains prod then true, true else false,true
                    
                    if handle then handlePath path vertex
                    elif walkFurther && vertex <> null
                    then
                        let visitVertex (v : Vertex) s a =
                            if not <| Set.contains (v.Level, v.State) !vertexSet then
                                vertexSet := Set.add (v.Level, v.State) !vertexSet
                                walk v s prod (a::path)

                        if vertex.Level <> num then
                            if vertex.OutEdges.other <> null then
                                vertex.OutEdges.other |> Array.iter
                                    (fun e -> 
                                        visitVertex e.Dest e.StackAction e.Ast)
                            let e = vertex.OutEdges.first
                            visitVertex e.Dest e.StackAction e.Ast
                        else
                            simpleEdges.[vertex.State] |> ResizeArray.iter(fun (v,s,a) ->
                                visitVertex v s a)
                            
                            let mutable i = 0
                            let edges = edges.[vertex.State]
                            while i < edges.Count do
                                let (v,s,_,a) = edges.[i]
                                visitVertex v s a
                    else recovery() //pushes.Clear()
                match rLabel with
                |StackReduce ->
                    let goto = getExpectedGoto vertex.State nonTerm
                    let newVertex = addVertex (fst goto) num None
                    let ast = getEpsilon parserSource.LeftSide.[prod]
                    if not <| containsSimpleEdge vertex (snd goto) ast simpleEdges.[fst goto] then
                        addSimpleEdge vertex (snd goto) ast simpleEdges.[fst goto]
                |Reduce ->
                    let path = [trd edgeOpt.Value]
                    vertexSet := Set.add ((fst3 edgeOpt.Value).Level, (fst3 edgeOpt.Value).State) !vertexSet
                    walk (fst3 edgeOpt.Value) (snd3 edgeOpt.Value) prod path                    

        let curInd = ref 0
        let isEnd = ref false
        let attachEdges () =
            let inline snd3 (_,x,_) = x
            for vertex in usedStates do
                let mutable i = 0
                let edges = edges.[vertex]
                let mutable count = -1
                while i < edges.Count do
                    let k = frth edges.[i]
                    let mutable j = i+1
                    while j < edges.Count && frth edges.[j] = k do
                        j <- j + 1
                    i <- j
                    count <- count + 1
                count <- count + simpleEdges.[vertex].Count
                let vEdges =
                    if count > 0 then Array.zeroCreate count
                    else null
                let mutable first = Unchecked.defaultof<_>
                i <- 0
                count <- -1
                while i < edges.Count do
                    let (v, s, _,a) = edges.[i]
                    let mutable j = i+1
                    while j < edges.Count && frth edges.[j] = a do
                        j <- j + 1
                    let other = 
                        if j <> i + 1 then
                            let res = Array.zeroCreate (j - i - 1)
                            for k = i + 1 to j-1 do
                                res.[k-i-1] <- trd4 edges.[k]
                            res
                        else
                            null
                    if count >= 0 then
                        vEdges.[count] <- new Edge(v, s, box a)
                    else
                        first <- new Edge(v, s, box a)
                    count <- count + 1
                    a.first <- trd4 edges.[i]
                    a.other <- other
                    i <- j

                for i = 0 to simpleEdges.[vertex].Count - 1 do
                    let v, s, a = simpleEdges.[vertex].[i]
                    if count >= 0 then
                        vEdges.[count] <- new Edge(v, s, a)
                    else
                        first <- new Edge(v, s, a)
                    count <- count + 1

                stateToVertex.[vertex].OutEdges <- UsualOne<_>(first, vEdges)
                edges.Clear()
                simpleEdges.[vertex].Clear()

        let shift num =
            let newAstNode = box tokens.Count
            tokens.Add enum.Current
            if enum.MoveNext() then
                curToken := enum.Current
                curNum := parserSource.TokenToNumber enum.Current
            else
                curNum := parserSource.EofIndex
            for vertex in usedStates do
                stateToVertex.[vertex] <- null
            (*usedStates.Clear()
            let oldPushes = pushes.ToArray()
            pushes.Clear()*)
            let oldPushes = new Stack<_>()
            for vertex, state in pushes do
                if vertex.State |> usedStates.Contains 
                then 
                    oldPushes.Push (vertex, state)
            pushes.Clear()
            usedStates.Clear()

            for (vertex, (state, stackLabel)) in oldPushes do
                let newVertex = addVertex state num <| Some (vertex, stackLabel, newAstNode)
                addSimpleEdge vertex stackLabel newAstNode simpleEdges.[state]
        
        /// returns all the terminals and non-terminals that make the push or reduce
        /// it's used by recovery
        let getExpectedTokens state = 
            let expected = ref <| Set.empty
            let ps = parserSource

            for i = 0 to ps.Gotos.[0].GetLength(0)-1 do
                if (ps.Gotos.[state].[i].IsSome && fst ps.Gotos.[state].[i].Value <> 0) || ps.Reduces.[state].[i] <> null
                then expected := expected.Value.Add i
            
            !expected
        
        /// returns  array that consists of tokens or error non-teminal (and its children)
        let astToTokens (x : obj) =            
            let visited = ref 0
            let rec go (x : obj) =
                let mutable res = []
                incr visited
                if !visited < 100 
                then                    
                    match x : obj with 
                    | :? int as t when t >= 0 -> res <- x :: res
                    | :? Family as fam ->                    
                        for i = 0 to fam.nodes.Length - 1 do
                            res <- res @ go fam.nodes.[i]
                    | :? AST as ast ->
                        if ast.other <> null 
                        then                            
                            for family in ast.other do
                                if family.prod = parserSource.LeftSide.Length
                                then res <- res @ [ast]
                                else res <- res @ go family
                            
                        if ast.first.prod = parserSource.LeftSide.Length
                        then res <- [ast] @ res
                        else res <- go ast.first @ res
                    | _ -> ()
                res
            go x
        
        /// collects info about error that is needed in the translation
        let createErrorNode (errFamily : Family) (errOn : obj) (prod : int) (expected : int[]) (recToks : int[]) = 

            let exp = expected |> Array.map (fun i -> parserSource.NumToString i)
            let recToks = recToks |> Array.map (fun i -> parserSource.NumToString i)
            
            try errDict.Add (errFamily, new ErrorNode (errOn, -1, exp, recToks))
            with _ -> ()

        let containsRecState (oldVertices : Stack<Vertex * _ list>)(temp : Queue<_>) recVertNum recovery =
            let oldVert = oldVertices.ToArray()
            for vertex, path in oldVert do
                if pushes.Count <> recVertNum
                then
                    //if reduce is possible
                    let arr = parserSource.Reduces.[vertex.State].[!curNum]
                    if arr <> null
                    then 
                        for prod in arr do
                            //probably StackLabel.Stack prod doesn't make sense
                            let edgeOpt = Some (vertex.OutEdges.first.Dest, StackLabel.Stack prod, vertex.OutEdges.first.Ast)
                            reductions.Push (vertex, prod, Reduce, edgeOpt)
                        makeReductions !curInd recovery
                        temp.Enqueue path
                    //if shift is possible
                    if parserSource.Gotos.[vertex.State].[!curNum].IsSome && fst parserSource.Gotos.[vertex.State].[!curNum].Value <> 0 
                    then
                        let push = parserSource.Gotos.[vertex.State].[!curNum].Value
                        if pushes.Count <> 0 
                        then
                            let recVert = fst <| pushes.Peek()
                            if  recVert.State <> vertex.State 
                            then 
                                pushes.Push (vertex, push)
                                temp.Enqueue path
                        else 
                            pushes.Push (vertex, push)
                            temp.Enqueue path

            pushes.Count + reductions.Count >= recVertNum

        ///returns all the vertices from the previous level
        let getPrevVertices (curVertices : Stack<Vertex * _>) = 
            let inline isOldVertex (v : Vertex) = 
                curVertices.ToArray() 
                |> Array.exists (fun (x, y) -> x.Level = v.Level && x.State = v.State) 
                    
            let oldVertices = curVertices.ToArray()
            curVertices.Clear()
            for vertex, path in oldVertices do
                if vertex.OutEdges.first.Dest <> null 
                then
                    if vertex.OutEdges.other <> null 
                    then
                        for edge in vertex.OutEdges.other do 
                            if  not <| isOldVertex edge.Dest
                            then
                                let tmp = astToTokens edge.Ast
                                let newPath = tmp @ path 
                                curVertices.Push (edge.Dest, newPath)

                    if  not <| isOldVertex vertex.OutEdges.first.Dest
                    then
                        let tmp = astToTokens vertex.OutEdges.first.Ast
                        let newPath = tmp @ path 
                        curVertices.Push (vertex.OutEdges.first.Dest, newPath)
            curVertices

        /// creates a family of the unbrowsed tokens
        (*let createErrorFam (unbrowsed : obj[])  = 
            let reduceToError (vertex : Vertex) state (unbrowsed : obj[])= 
                let prodNumber = parserSource.Rules.Length
                if unbrowsed.Length = 0 
                then 
                    let ast = getEpsilon parserSource.ErrorIndex
                    if not <| containsSimpleEdge vertex ast simpleEdges.[state] 
                    then
                        addSimpleEdge vertex ast simpleEdges.[state]
                        let arr = parserSource.Reduces.[state].[!curNum]
                        if arr <> null 
                        then
                            for (prod, pos) in arr do
                                reductions.Push (vertex, prod, pos, Some (vertex, ast))
                    new Family(prodNumber, new Nodes([|ast|]))
                else
                    let family = new Family(prodNumber, new Nodes(unbrowsed))
                            
                    if not <| containsEdge vertex family edges.[state] 
                    then
                        let _, edgeLabel = addEdge vertex family edges.[state] true
                        let arr = parserSource.Reduces.[state].[!curNum]
                        if arr <> null 
                        then
                            for (prod, pos) in arr do
                                reductions.Push (vertex, prod, pos, Some (vertex, box edgeLabel))
                    family
                           
            let state = snd <| pushes.Peek()

            if parserSource.Reduces.[state].[!curNum] <> null
            then // reductions is possible
                let vertex = fst <| pushes.Peek()
                reduceToError vertex state unbrowsed
                                            
            else // if shift is possible
                let oldPushes = pushes.ToArray()
                for state in usedStates do
                    stateToVertex.[state] <- null
                pushes.Clear()
                usedStates.Clear()
                let fam = ref <| new Family ()
                for vertex, state in oldPushes do
                    fam := reduceToError vertex state unbrowsed

                    let astNode = box tokens.Count
                    tokens.Add !curToken
                    addVertex state !curInd None |> ignore
                !fam*)

        let recovery() = ()(*
            let recVertNumber = 1
            if usedStates.Count <> 0 
            then 
                let prevNum = !curNum
                let expected = ref Set.empty
                let errInd = !curInd

                curNum := parserSource.ErrorIndex
                let temp = new Queue<_>()
                let curVertices = ref <| new Stack<_> (statesCount)

                for vertex in usedStates do
                    expected := !expected + getExpectedTokens vertex
                    let path = []
                    curVertices.Value.Push (stateToVertex.[vertex], path)
                    stateToVertex.[vertex] <- null
                usedStates.Clear()
                //pushes.count may be equal to 1
                //if parser finished in the non-accepting state and it generates the recovery
                pushes.Clear()

                while curVertices.Value.Count <> 0 && not <| containsRecState !curVertices temp recVertNumber (fun () -> ()) do
                    curVertices := getPrevVertices !curVertices
                
                let skipped = Queue<_>()
                let oldPushes = pushes.ToArray() |> Array.rev
                pushes.Clear()

                let arr : array<Vertex * int * StackLabel * array<int>> = Array.zeroCreate oldPushes.Length
                    
                for i in 0..oldPushes.Length-1 do
                    let vertex, (state, stackLabel) = oldPushes.[i]
                    let recToks = Set.toArray <| getExpectedTokens state      
                    arr.[i] <- vertex, state, stackLabel, recToks
                
                let inline fst4 (s, _, _, _) = s
                let inline snd4 (_, s, _, _) = s
                let inline thr4  (_, _, s, _) = s
                let inline frth  (_, _, _, s) = s

                let isRecToken num = 
                    let res = ref -1
                    for i in 0..arr.Length-1 do
                        if !res < 0 && Array.exists ((=) num) <| frth arr.[i] 
                        then res := i
                    !res

                curNum := prevNum
                let var = ref <| isRecToken !curNum

                while !var = -1 && !curNum <> parserSource.EofIndex do
                    let newAstNode = box tokens.Count
                    tokens.Add !curToken
                    skipped.Enqueue newAstNode
                    if enum.MoveNext() 
                    then
                        curToken := enum.Current
                        curNum := parserSource.TokenToNumber enum.Current
                        incr curInd
                    else             
                        curNum := parserSource.EofIndex
                    var := isRecToken !curNum
                
                if  !var >= 0
                then 
                    let path = temp.ToArray()
                    let need = List.toArray path.[!var]
                    let unbrowsed = Array.append need <| skipped.ToArray()
                    pushes.Push (fst4 arr.[!var], (snd4 arr.[!var], thr4 arr.[!var]))
                    let fam = createErrorFam unbrowsed
                    let rec onTok i =
                        if i >= 0
                        then
                            let x = tokens.[i] 
                            if box x <> null
                            then box x
                            else onTok (i-1)
                        else null
                            
                    createErrorNode fam <| onTok errInd <| 0 <| Set.toArray !expected <| frth arr.[!var]*)

        //let errorRuleExist = parserSource.ErrorRulesExists
        let wasError = ref false

        while not !isEnd && not !wasError do
            if usedStates.Count = 0 && reductions.Count = 0
            then 
                wasError := true
            else
                makeReductions !curInd recovery
                attachEdges()
                if !curNum = parserSource.EofIndex then isEnd := true
                elif pushes.Count = 0 then 
                    (*if errorRuleExist 
                    then recovery()
                    else*) wasError := true
                else
                    incr curInd
                    shift !curInd
        
        let isAcceptState() =                
            usedStates.ToArray()
            |> Array.exists (fun state -> parserSource.AccStates.[state])

        // if finish isn't accepting state then error
        if !isEnd && usedStates.Count > 0 && not <| isAcceptState() 
        then
            (*if errorRuleExist 
            then 
                 recovery()
                 makeReductions (!curInd + 1) recovery
                 attachEdges()
            else*) wasError := true

        let lastTokens count =
            [| for i = max 0 (tokens.Count-count) to tokens.Count-1 do
                yield tokens.[i]|]
        let debugFuns () =
            let vertices = usedStates.ToArray() |> Array.map (fun i -> stateToVertex.[i])
            {
                drawGSSDot = drawDot parserSource.TokenToNumber tokens parserSource.LeftSide vertices parserSource.NumToString parserSource.ErrorIndex
                lastTokens = lastTokens
            }
        
        if !wasError 
        then 
            Error (!curInd , [|!curToken|] , "Parse Error", errDict)
        else
            let root = ref None
            let addTreeTop res =
                let children = new Family(parserSource.StartRule,  new Nodes(res, null, null))
                new AST(children, null)
            for vertex in usedStates do
                if parserSource.AccStates.[vertex]
                then
                    root :=
                        stateToVertex.[vertex].OutEdges.first.Ast
                        |> addTreeTop
                        |> Some
            match !root with
            | None -> Error (!curInd, [|!curToken|], "Input was fully processed, but it's not complete correct string.", errDict)
            | Some res -> 
                debugFuns().drawGSSDot "res.dot"
                Success (new Tree<_> (tokens.ToArray(), res, [||]), errDict)
