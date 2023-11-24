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
Require Data.Either.
Require PlutusTx_Bool.
Require PlutusTx_Builtins.
Require PlutusTx_Builtins_Internal.
Require ZArith.BinInt.
Import PlutusTx_Bool.Notations.

(* Converted type declarations: *)

Record Eq__Dict (a : Type) := Eq__Dict_Build {
  op_zeze____ : a -> a -> bool }.

Definition Eq (a : Type) :=
  forall r__, (Eq__Dict a -> r__) -> r__.
Existing Class Eq.

Definition op_zeze__ `{g__0__ : Eq a} : a -> a -> bool :=
  g__0__ _ (op_zeze____ a).

Notation "'_==_'" := (op_zeze__).

Infix "==" := (_==_) (at level 99).

(* Converted value declarations: *)

Local Definition Eq__Z_op_zeze__ : BinNums.Z -> BinNums.Z -> bool :=
  ZArith.BinInt.Z.eqb.

Program Instance Eq__Z : Eq BinNums.Z :=
  fun _ k__ => k__ {| op_zeze____ := Eq__Z_op_zeze__ |}.

(* Skipping instance `PlutusTx_Eq.Eq__BuiltinByteString' of class
   `PlutusTx_Eq.Eq' *)

(* Skipping instance `PlutusTx_Eq.Eq__BuiltinData' of class `PlutusTx_Eq.Eq' *)

Local Definition Eq__BuiltinString_op_zeze__
   : PlutusTx_Builtins_Internal.BuiltinString ->
     PlutusTx_Builtins_Internal.BuiltinString -> bool :=
  PlutusTx_Builtins.equalsString.

Program Instance Eq__BuiltinString
   : Eq PlutusTx_Builtins_Internal.BuiltinString :=
  fun _ k__ => k__ {| op_zeze____ := Eq__BuiltinString_op_zeze__ |}.

(* Skipping instance `PlutusTx_Eq.Eq__BuiltinBLS12_381_G1_Element' of class
   `PlutusTx_Eq.Eq' *)

(* Skipping instance `PlutusTx_Eq.Eq__BuiltinBLS12_381_G2_Element' of class
   `PlutusTx_Eq.Eq' *)

Fixpoint eqList {a} `{Eq a} (arg_0__ arg_1__ : list a) : bool
  := match arg_0__, arg_1__ with
     | nil, nil => true
     | cons x xs, cons y ys => (x == y) PlutusTx_Bool.&& eqList xs ys
     | _, _ => false
     end.

Local Definition Eq__list_op_zeze__ {inst_a : Type} `{Eq inst_a}
   : list inst_a -> list inst_a -> bool :=
  eqList.

Program Instance Eq__list {a : Type} `{Eq a} : Eq (list a) :=
  fun _ k__ => k__ {| op_zeze____ := Eq__list_op_zeze__ |}.

Local Definition Eq__bool_op_zeze__ : bool -> bool -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | true, true => true
    | false, false => true
    | _, _ => false
    end.

Program Instance Eq__bool : Eq bool :=
  fun _ k__ => k__ {| op_zeze____ := Eq__bool_op_zeze__ |}.

Local Definition Eq__option_op_zeze__ {inst_a : Type} `{Eq inst_a}
   : option inst_a -> option inst_a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Some a1, Some a2 => a1 == a2
    | None, None => true
    | _, _ => false
    end.

Program Instance Eq__option {a : Type} `{Eq a} : Eq (option a) :=
  fun _ k__ => k__ {| op_zeze____ := Eq__option_op_zeze__ |}.

Local Definition Eq__Either_op_zeze__ {inst_a : Type} {inst_b : Type} `{Eq
  inst_a} `{Eq inst_b}
   : Data.Either.Either inst_a inst_b ->
     Data.Either.Either inst_a inst_b -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Data.Either.Left a1, Data.Either.Left a2 => a1 == a2
    | Data.Either.Right b1, Data.Either.Right b2 => b1 == b2
    | _, _ => false
    end.

Program Instance Eq__Either {a : Type} {b : Type} `{Eq a} `{Eq b}
   : Eq (Data.Either.Either a b) :=
  fun _ k__ => k__ {| op_zeze____ := Eq__Either_op_zeze__ |}.

Local Definition Eq__unit_op_zeze__ : unit -> unit -> bool :=
  fun arg_0__ arg_1__ => true.

Program Instance Eq__unit : Eq unit :=
  fun _ k__ => k__ {| op_zeze____ := Eq__unit_op_zeze__ |}.

Local Definition Eq__op_zt___op_zeze__ {inst_a : Type} {inst_b : Type} `{Eq
  inst_a} `{Eq inst_b}
   : (inst_a * inst_b)%type -> (inst_a * inst_b)%type -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair a b, pair a' b' => (a == a') PlutusTx_Bool.&& (b == b')
    end.

Program Instance Eq__op_zt__ {a : Type} {b : Type} `{Eq a} `{Eq b}
   : Eq (a * b)%type :=
  fun _ k__ => k__ {| op_zeze____ := Eq__op_zt___op_zeze__ |}.

Definition op_zsze__ {a : Type} `{Eq a} : a -> a -> bool :=
  fun x y => PlutusTx_Bool.not (x == y).

Notation "'_/=_'" := (op_zsze__).

Infix "/=" := (_/=_) (at level 99).

Module Notations.
Notation "'_PlutusTx_Eq.==_'" := (op_zeze__).
Infix "PlutusTx_Eq.==" := (_==_) (at level 99).
Notation "'_PlutusTx_Eq./=_'" := (op_zsze__).
Infix "PlutusTx_Eq./=" := (_/=_) (at level 99).
End Notations.

(* External variables:
     None Some Type bool cons false list nil op_zt__ option pair true unit BinNums.Z
     Data.Either.Either Data.Either.Left Data.Either.Right PlutusTx_Bool.not
     PlutusTx_Bool.op_zaza__ PlutusTx_Builtins.equalsString
     PlutusTx_Builtins_Internal.BuiltinString ZArith.BinInt.Z.eqb
*)
