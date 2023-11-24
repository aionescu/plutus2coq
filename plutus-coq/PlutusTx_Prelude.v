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
Require PlutusTx_Eq.
Require PlutusTx_ErrorCodes.
Require PlutusTx_Trace.
Import GHC.Num.Notations.
Import PlutusTx_Eq.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition check : bool -> unit :=
  fun b =>
    if b : bool
    then tt
    else PlutusTx_Trace.traceError PlutusTx_ErrorCodes.checkHasFailedError.

Definition divide : BinNums.Z -> BinNums.Z -> BinNums.Z :=
  Z.div.

Definition modulo : BinNums.Z -> BinNums.Z -> BinNums.Z :=
  Z.modulo.

Definition quotient : BinNums.Z -> BinNums.Z -> BinNums.Z :=
  Z.quot.

Definition remainder : BinNums.Z -> BinNums.Z -> BinNums.Z :=
  Z.rem.

Definition even : BinNums.Z -> bool :=
  fun n => if modulo n #2 PlutusTx_Eq.== #0 : bool then true else false.

Definition odd : BinNums.Z -> bool :=
  fun n => if even n : bool then false else true.

(* Skipping definition `PlutusTx_Prelude.takeByteString' *)

(* Skipping definition `PlutusTx_Prelude.dropByteString' *)

(* External variables:
     bool false true tt unit BinNums.Z GHC.Num.fromInteger PlutusTx_Eq.op_zeze__
     PlutusTx_ErrorCodes.checkHasFailedError PlutusTx_Trace.traceError Z.div Z.modulo
     Z.quot Z.rem
*)
