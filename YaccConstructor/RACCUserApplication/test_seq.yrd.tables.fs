//this tyables was generated by RACC
//source grammar:..\..\..\..\Tests\Tests\test_seq\\test_seq.yrd
//date:11/17/2010 18:00:44

#light "off"
module Yard.Generators._RACCGenerator.Tables

open Yard.Generators._RACCGenerator

let autumataDict = 
dict [|("s",{ 
   DIDToStateMap = dict [|(0,(State 0));(1,(State 1));(2,(State 2));(3,(State 3));(4,DummyState)|];
   DStartState   = 0;
   DFinaleStates = Set.ofArray [|3|];
   DRules        = Set.ofArray [|{ 
   FromStateID = 0;
   Symbol      = (DSymbol "NUMBER");
   Label       = Set.ofArray [|List.ofArray [|(FATrace TSeqS);(FATrace TSmbS)|]|];
   ToStateID   = 1;
}
;{ 
   FromStateID = 1;
   Symbol      = (DSymbol "PLUS");
   Label       = Set.ofArray [|List.ofArray [|(FATrace TSmbE);(FATrace TSmbS)|]|];
   ToStateID   = 2;
}
;{ 
   FromStateID = 2;
   Symbol      = (DSymbol "NUMBER");
   Label       = Set.ofArray [|List.ofArray [|(FATrace TSmbE);(FATrace TSmbS)|]|];
   ToStateID   = 3;
}
;{ 
   FromStateID = 3;
   Symbol      = Dummy;
   Label       = Set.ofArray [|List.ofArray [|(FATrace TSmbE);(FATrace TSeqE)|]|];
   ToStateID   = 4;
}
|];
}
)|]

let items = 
List.ofArray [|("s",0);("s",1);("s",2);("s",3);("s",4)|]

let gotoSet = 
Set.ofArray [|(1800920879,("s",4));(1904107658,("s",3));(1904107720,("s",1));(452886726,("s",2))|]

