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
Require PlutusTx_Show_TH.

(* No type declarations to convert. *)

(* Converted value declarations: *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__Z' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__BuiltinByteString' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__BuiltinString' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__BuiltinData' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__bool' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__unit' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__list' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__pair_type' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__triple_type' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__quad_type' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__quint_type' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__sext_type' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__sept_type' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__op_Z8T__' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__op_Z9T__' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__op_Z10T__' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__op_Z11T__' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__op_Z12T__' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__op_Z13T__' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__op_Z14T__' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__op_Z15T__' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__op_Z16T__' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__op_Z17T__' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__op_Z18T__' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__op_Z19T__' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__op_Z20T__' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__op_Z21T__' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__op_Z22T__' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__op_Z23T__' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__op_Z24T__' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__op_Z25T__' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__op_Z26T__' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__op_Z27T__' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__option' *)

(* Skipping all instances of class `PlutusTx_Show_TH.Show', including
   `PlutusTx_Show.Show__Either' *)

Axiom toDigits : BinNums.Z -> list BinNums.Z.

Axiom showList : forall {a},
                 (a -> PlutusTx_Show_TH.ShowS) -> list a -> PlutusTx_Show_TH.ShowS.

(* External variables:
     list BinNums.Z PlutusTx_Show_TH.ShowS
*)
