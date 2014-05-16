namespace Yard.Generators.RNGLR.EBNF

//open Yard.Generators.RNGLR.StackLabel

type ParserSourceEBNF<'TokenType> (gotos : (int * (int * int)) option [][] //goto consists of number of state where to go to and sets of productions to Stack/not to Stack
                               , reduces : int [][][]
                               , zeroReduces : int[][][]
                               , stackSets : Set<int>[]
                               , accStates : bool[]
                               , leftSide : int[]
                               , startRule : int
                               , eofIndex : int
                               , tokenToNumber : 'TokenType -> int
                               , acceptEmptyInput : bool
                               , numToString : int -> string
                               , errorIndex : int
                               (*, errorRulesExists : bool*)
                               ) =
   
    member this.Reduces = reduces
    member this.ZeroReduces = zeroReduces
    member this.Gotos = gotos
    member this.StackSets = stackSets
    member this.AccStates = accStates
    member this.LeftSide = leftSide
    member this.StartRule = startRule
    member this.EofIndex = eofIndex
    member this.TokenToNumber = tokenToNumber
    member this.AcceptEmptyInput = acceptEmptyInput
    member this.NumToString = numToString
    member this.ErrorIndex = errorIndex
    //member this.ErrorRulesExists = errorRulesExists
