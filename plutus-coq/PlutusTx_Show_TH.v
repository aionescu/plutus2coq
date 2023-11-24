(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

From Coq Require Extraction.
From Coq Require ExtrHaskellBasic.
From Coq Require ExtrHaskellNatInteger.
From Coq Require ExtrHaskellZInteger.
From Coq Require ExtrHaskellString.

Extraction Language Haskell.
Unset Extraction Optimize.
Set Extraction KeepSingleton.

Require GHC.Base.
Import GHC.Base.Notations.

(* Converted imports: *)

Require BinNums.
Require GHC.Base.
Require Language.Haskell.TH.Datatype.
Require Language.Haskell.TH.Syntax.
Require PlutusTx_Builtins_Internal.

(* Converted type declarations: *)

Definition ShowS :=
  (list PlutusTx_Builtins_Internal.BuiltinString ->
   list PlutusTx_Builtins_Internal.BuiltinString)%type.

(* Converted value declarations: *)

Axiom showString : PlutusTx_Builtins_Internal.BuiltinString -> ShowS.

Axiom showSpace : ShowS.

Axiom showCommaSpace : ShowS.

Axiom showParen : bool -> ShowS -> ShowS.

Axiom appPrec : BinNums.Z.

Axiom appPrec1 : BinNums.Z.

Axiom concatBuiltinStrings : list PlutusTx_Builtins_Internal.BuiltinString ->
                             PlutusTx_Builtins_Internal.BuiltinString.

Axiom deriveShow : Language.Haskell.TH.Syntax.Name ->
                   Language.Haskell.TH.Syntax.Q (list Language.Haskell.TH.Syntax.Dec).

Axiom deriveShowsPrec : list Language.Haskell.TH.Datatype.ConstructorInfo ->
                        list (Language.Haskell.TH.Syntax.Q Language.Haskell.TH.Syntax.Dec).

Axiom deriveShowsPrecBody : list Language.Haskell.TH.Datatype.ConstructorInfo ->
                            Language.Haskell.TH.Syntax.Q Language.Haskell.TH.Syntax.Exp.

Axiom deriveMatchForCon : Language.Haskell.TH.Syntax.Name ->
                          Language.Haskell.TH.Datatype.ConstructorInfo ->
                          Language.Haskell.TH.Syntax.Q Language.Haskell.TH.Syntax.Match.

Axiom deriveShowExpForArg : BinNums.Z ->
                            Language.Haskell.TH.Syntax.Name ->
                            Language.Haskell.TH.Syntax.Q Language.Haskell.TH.Syntax.Exp.

Axiom parenInfixConName : Language.Haskell.TH.Syntax.Name -> GHC.Base.String.

(* External variables:
     bool list BinNums.Z GHC.Base.String Language.Haskell.TH.Datatype.ConstructorInfo
     Language.Haskell.TH.Syntax.Dec Language.Haskell.TH.Syntax.Exp
     Language.Haskell.TH.Syntax.Match Language.Haskell.TH.Syntax.Name
     Language.Haskell.TH.Syntax.Q PlutusTx_Builtins_Internal.BuiltinString
*)
