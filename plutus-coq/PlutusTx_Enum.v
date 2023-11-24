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
Require GHC.Num.
Require PlutusTx_Eq.
Require PlutusTx_ErrorCodes.
Require PlutusTx_Trace.
Import GHC.Num.Notations.
Import PlutusTx_Eq.Notations.

(* Converted type declarations: *)

Record Enum__Dict (a : Type) := Enum__Dict_Build {
  enumFromTo__ : a -> a -> list a ;
  fromEnum__ : a -> BinNums.Z ;
  pred__ : a -> a ;
  succ__ : a -> a ;
  toEnum__ : BinNums.Z -> a }.

Definition Enum (a : Type) :=
  forall r__, (Enum__Dict a -> r__) -> r__.
Existing Class Enum.

Definition enumFromTo `{g__0__ : Enum a} : a -> a -> list a :=
  g__0__ _ (enumFromTo__ a).

Definition fromEnum `{g__0__ : Enum a} : a -> BinNums.Z :=
  g__0__ _ (fromEnum__ a).

Definition pred `{g__0__ : Enum a} : a -> a :=
  g__0__ _ (pred__ a).

Definition succ `{g__0__ : Enum a} : a -> a :=
  g__0__ _ (succ__ a).

Definition toEnum `{g__0__ : Enum a} : BinNums.Z -> a :=
  g__0__ _ (toEnum__ a).

(* Converted value declarations: *)

Axiom enumFromToInteger : BinNums.Z -> BinNums.Z -> list BinNums.Z.

Local Definition Enum__Z_enumFromTo
   : BinNums.Z -> BinNums.Z -> list BinNums.Z :=
  enumFromToInteger.

Local Definition Enum__Z_fromEnum : BinNums.Z -> BinNums.Z :=
  fun x => x.

Local Definition Enum__Z_pred : BinNums.Z -> BinNums.Z :=
  fun x => Z.sub x #1.

Local Definition Enum__Z_succ : BinNums.Z -> BinNums.Z :=
  fun x => Z.add x #1.

Local Definition Enum__Z_toEnum : BinNums.Z -> BinNums.Z :=
  fun x => x.

Program Instance Enum__Z : Enum BinNums.Z :=
  fun _ k__ =>
    k__ {| enumFromTo__ := Enum__Z_enumFromTo ;
           fromEnum__ := Enum__Z_fromEnum ;
           pred__ := Enum__Z_pred ;
           succ__ := Enum__Z_succ ;
           toEnum__ := Enum__Z_toEnum |}.

Local Definition Enum__unit_enumFromTo : unit -> unit -> list unit :=
  fun arg_0__ arg_1__ => cons tt nil.

Local Definition Enum__unit_fromEnum : unit -> BinNums.Z :=
  fun '(tt) => #0.

Local Definition Enum__unit_pred : unit -> unit :=
  fun arg_0__ =>
    PlutusTx_Trace.traceError PlutusTx_ErrorCodes.predVoidBadArgumentError.

Local Definition Enum__unit_succ : unit -> unit :=
  fun arg_0__ =>
    PlutusTx_Trace.traceError PlutusTx_ErrorCodes.succVoidBadArgumentError.

Local Definition Enum__unit_toEnum : BinNums.Z -> unit :=
  fun x =>
    if x PlutusTx_Eq.== #0 : bool then tt else
    PlutusTx_Trace.traceError PlutusTx_ErrorCodes.toEnumVoidBadArgumentError.

Program Instance Enum__unit : Enum unit :=
  fun _ k__ =>
    k__ {| enumFromTo__ := Enum__unit_enumFromTo ;
           fromEnum__ := Enum__unit_fromEnum ;
           pred__ := Enum__unit_pred ;
           succ__ := Enum__unit_succ ;
           toEnum__ := Enum__unit_toEnum |}.

Axiom enumFromToBool : bool -> bool -> list bool.

Local Definition Enum__bool_enumFromTo : bool -> bool -> list bool :=
  enumFromToBool.

Local Definition Enum__bool_fromEnum : bool -> BinNums.Z :=
  fun arg_0__ => match arg_0__ with | false => #0 | true => #1 end.

Local Definition Enum__bool_pred : bool -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | true => false
    | false =>
        PlutusTx_Trace.traceError PlutusTx_ErrorCodes.predBoolBadArgumentError
    end.

Local Definition Enum__bool_succ : bool -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | false => true
    | true => PlutusTx_Trace.traceError PlutusTx_ErrorCodes.succBoolBadArgumentError
    end.

Local Definition Enum__bool_toEnum : BinNums.Z -> bool :=
  fun n =>
    if n PlutusTx_Eq.== #0 : bool then false else
    if n PlutusTx_Eq.== #1 : bool then true else
    PlutusTx_Trace.traceError PlutusTx_ErrorCodes.toEnumBoolBadArgumentError.

Program Instance Enum__bool : Enum bool :=
  fun _ k__ =>
    k__ {| enumFromTo__ := Enum__bool_enumFromTo ;
           fromEnum__ := Enum__bool_fromEnum ;
           pred__ := Enum__bool_pred ;
           succ__ := Enum__bool_succ ;
           toEnum__ := Enum__bool_toEnum |}.

Axiom enumFromToOrdering : comparison -> comparison -> list comparison.

Local Definition Enum__comparison_enumFromTo
   : comparison -> comparison -> list comparison :=
  enumFromToOrdering.

Local Definition Enum__comparison_fromEnum : comparison -> BinNums.Z :=
  fun arg_0__ => match arg_0__ with | Lt => #0 | Eq => #1 | Gt => #2 end.

Local Definition Enum__comparison_pred : comparison -> comparison :=
  fun arg_0__ =>
    match arg_0__ with
    | Gt => Eq
    | Eq => Lt
    | Lt =>
        PlutusTx_Trace.traceError PlutusTx_ErrorCodes.predOrderingBadArgumentError
    end.

Local Definition Enum__comparison_succ : comparison -> comparison :=
  fun arg_0__ =>
    match arg_0__ with
    | Lt => Eq
    | Eq => Gt
    | Gt =>
        PlutusTx_Trace.traceError PlutusTx_ErrorCodes.succOrderingBadArgumentError
    end.

Local Definition Enum__comparison_toEnum : BinNums.Z -> comparison :=
  fun '(n) =>
    if n PlutusTx_Eq.== #0 : bool then Lt else
    if n PlutusTx_Eq.== #1 : bool then Eq else
    if n PlutusTx_Eq.== #2 : bool then Gt else
    PlutusTx_Trace.traceError PlutusTx_ErrorCodes.toEnumOrderingBadArgumentError.

Program Instance Enum__comparison : Enum comparison :=
  fun _ k__ =>
    k__ {| enumFromTo__ := Enum__comparison_enumFromTo ;
           fromEnum__ := Enum__comparison_fromEnum ;
           pred__ := Enum__comparison_pred ;
           succ__ := Enum__comparison_succ ;
           toEnum__ := Enum__comparison_toEnum |}.

(* External variables:
     Eq Gt Lt Type bool comparison cons false list nil true tt unit BinNums.Z
     GHC.Num.fromInteger PlutusTx_Eq.op_zeze__
     PlutusTx_ErrorCodes.predBoolBadArgumentError
     PlutusTx_ErrorCodes.predOrderingBadArgumentError
     PlutusTx_ErrorCodes.predVoidBadArgumentError
     PlutusTx_ErrorCodes.succBoolBadArgumentError
     PlutusTx_ErrorCodes.succOrderingBadArgumentError
     PlutusTx_ErrorCodes.succVoidBadArgumentError
     PlutusTx_ErrorCodes.toEnumBoolBadArgumentError
     PlutusTx_ErrorCodes.toEnumOrderingBadArgumentError
     PlutusTx_ErrorCodes.toEnumVoidBadArgumentError PlutusTx_Trace.traceError Z.add
     Z.sub
*)
