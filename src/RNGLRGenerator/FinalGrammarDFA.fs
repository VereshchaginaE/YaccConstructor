namespace Yard.Generators.RNGLR.FinalGrammarDFA

open Yard.Core.IL
open Yard.Generators.RNGLR
open Yard.Generators.RNGLR.Epsilon
//open Yard.Generators.RNGLR.SymbolSets
open Yard.Generators.RNGLR.DFA


type FinalGrammarDFA(ruleList : Rule.t<Source.t,Source.t> list, caseSensitive) =
    let _indexator = new Indexator(ruleList, caseSensitive)
    let dfaRules = new NumberedRulesDFA (ruleList, _indexator, caseSensitive)
    let _canInferEpsilon = canInferEpsilon _numberedRules _indexator // возможен бесконечный вывод
    //let _firstSet = firstSet _numberedRules _indexator _canInferEpsilon //
    //let _followSet = followSet _numberedRules _indexator _canInferEpsilon _firstSet
    let _epsilonCyclicNonTerms = getEpsilonCyclicNonTerms _numberedRules _indexator _canInferEpsilon // нетермиалы
    let _epsilonTrees = epsilonTrees _numberedRules _indexator _canInferEpsilon // написать Дмитрию Авдюхину. 
    let _epsilonTailStart = epsilonTailStart _numberedRules _canInferEpsilon //  --//-- специальные вещи для интерпретирования
    let _errorIndex = _indexator.errorIndex // номер для терминала-еррора
    let _errorRulesExists = _numberedRules.errorRulesExists // проверка на правила с ошибками (error recovery)

    member this.indexator = _indexator
    member this.rules = _numberedRules
    member this.EpsilonCyclicNonTerms = _epsilonCyclicNonTerms
    member this.canInferEpsilon = _canInferEpsilon
    //member this.firstSet = _firstSet
    //member this.followSet = _followSet
    member this.epsilonTrees = _epsilonTrees
    member this.epsilonTailStart = _epsilonTailStart
    member this.startRule = _numberedRules.startRule
    member this.errorIndex = _errorIndex
    member this.errorRulesExists = _errorRulesExists