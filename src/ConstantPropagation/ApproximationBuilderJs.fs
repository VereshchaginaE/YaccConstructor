﻿module YC.ReSharper.AbstractAnalysis.LanguageApproximation.ApproximationBuilderJs

open JetBrains.ReSharper.Psi.JavaScript.ControlFlow

open Utils

open System.IO

let BuildApproximation (cfg: IJsControlFlowGraf) =
    let outFile = Path.Combine (myDebugFolderPath, "JsCfg_" + cfg.GetHashCode().ToString() + ".dot")
    DotUtils.cfgToDot cfg outFile "JsCfg"