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
Require GHC.Num.
Require PlutusTx_Base.
Require PlutusTx_Eq.
Require PlutusTx_List.
Require PlutusTx_Numeric.
Require PlutusTx_Show_TH.
Import GHC.Num.Notations.
Import PlutusTx_Base.Notations.
Import PlutusTx_Eq.Notations.

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

Definition toDigits : BinNums.Z -> list BinNums.Z :=
  let fix go acc n
    := let 'pair q r := PlutusTx_Numeric.quotRem n #10 in
       if q PlutusTx_Eq.== #0 : bool
       then cons r acc
       else go (cons r acc) q in
  go nil.

Definition showList {a}
   : (a -> PlutusTx_Show_TH.ShowS) -> list a -> PlutusTx_Show_TH.ShowS :=
  fun showElem =>
    fun arg_0__ =>
      match arg_0__ with
      | nil => PlutusTx_Show_TH.showString (GHC.Base.hs_string__ "[]")
      | cons x xs =>
          let alg : a -> PlutusTx_Show_TH.ShowS -> PlutusTx_Show_TH.ShowS :=
            fun a acc =>
              PlutusTx_Show_TH.showString (GHC.Base.hs_string__ ",") PlutusTx_Base.∘
              (showElem a PlutusTx_Base.∘ acc) in
          PlutusTx_Show_TH.showString (GHC.Base.hs_string__ "[") PlutusTx_Base.∘
          (showElem x PlutusTx_Base.∘
           (PlutusTx_List.foldr alg PlutusTx_Base.id xs PlutusTx_Base.∘
            PlutusTx_Show_TH.showString (GHC.Base.hs_string__ "]")))
      end.

(* External variables:
     bool cons list nil pair BinNums.Z GHC.Num.fromInteger PlutusTx_Base.id
     PlutusTx_Base.op_z2218U__ PlutusTx_Eq.op_zeze__ PlutusTx_List.foldr
     PlutusTx_Numeric.quotRem PlutusTx_Show_TH.ShowS PlutusTx_Show_TH.showString
*)
