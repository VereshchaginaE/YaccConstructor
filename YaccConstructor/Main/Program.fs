﻿module Main.Program

open Yard.Core
open Yard.Core.IL

//TODO: move it to ConvertionManager
let ApplyConvertion (ilTree:Definition.t<Source.t,Source.t>) (conv:IConvertion) = 
    {   new Definition.t<Source.t,Source.t>
        with info = ilTree.info
        and  head = ilTree.head
        and  grammar = conv.ConvertList ilTree.grammar
        and  foot = ilTree.foot
    }

let () =
//    let commandLineArgs = System.Environment.GetCommandLineArgs()
    let grammarFilePath = @"..\..\..\..\Tests\test001.yrd"
    let feName = "YardFrontend"
    let generatorName = "RecursiveAscent"

    // Load frontends assemblies dlls - get them from file, current folder or command line
    let assembly = System.Reflection.Assembly.Load(feName)
    let inst = assembly.CreateInstance("Yard.Frontends."+feName+"."+feName)
    FrontendsManager.Register(inst :?> IFrontend);

    // Load generator assemblies dlls - get them from file, current folder or command line
    let assembly = System.Reflection.Assembly.Load(generatorName)
    let inst = assembly.CreateInstance("Yard.Generators."+generatorName+"."+generatorName)
    GeneratorsManager.Register(inst :?> IGenerator);


    // Parse grammar
    let ilTree = (FrontendsManager.Frontend feName).ParseFile grammarFilePath

    // Apply convertions
    let ilTreeExpandedMeta = ApplyConvertion ilTree (new Yard.Core.Convertions.ExpandMeta.ExpandMeta())

    // Generate something
    let gen = GeneratorsManager.Generator(generatorName)
    let s = gen.Generate ilTreeExpandedMeta

    printf "%A" s
