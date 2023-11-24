(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Preamble *)

Require GHC.Base.
Import GHC.Base.Notations.

(* Converted imports: *)

Require BinNums.
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

(* Skipping definition `PlutusTx_Show_TH.deriveShow' *)

(* Skipping definition `PlutusTx_Show_TH.deriveShowsPrec' *)

(* Skipping definition `PlutusTx_Show_TH.deriveShowsPrecBody' *)

(* Skipping definition `PlutusTx_Show_TH.deriveMatchForCon' *)

(* Skipping definition `PlutusTx_Show_TH.deriveShowExpForArg' *)

(* Skipping definition `PlutusTx_Show_TH.parenInfixConName' *)

(* External variables:
     bool list BinNums.Z PlutusTx_Builtins_Internal.BuiltinString
*)
