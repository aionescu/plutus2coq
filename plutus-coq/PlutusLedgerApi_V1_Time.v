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
Require HsToCoq.Err.
Require PlutusLedgerApi_V1_Interval.

(* Converted type declarations: *)

Inductive POSIXTime : Type :=
  | MkPOSIXTime (getPOSIXTime : BinNums.Z) : POSIXTime.

Definition POSIXTimeRange :=
  (PlutusLedgerApi_V1_Interval.Interval POSIXTime)%type.

Inductive DiffMilliSeconds : Type :=
  | MkDiffMilliSeconds : BinNums.Z -> DiffMilliSeconds.

Instance Default__POSIXTime : HsToCoq.Err.Default POSIXTime :=
  HsToCoq.Err.Build_Default _ (MkPOSIXTime HsToCoq.Err.default).

Definition getPOSIXTime (arg_0__ : POSIXTime) :=
  let 'MkPOSIXTime getPOSIXTime := arg_0__ in
  getPOSIXTime.

(* Converted value declarations: *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Time.Lift__DefaultUni__DiffMilliSeconds' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Time.Typeable__DefaultUni__DiffMilliSeconds' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Time.Lift__DefaultUni__POSIXTime' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Time.Typeable__DefaultUni__POSIXTime' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V1_Time.Pretty__POSIXTime' *)

Definition fromMilliSeconds : DiffMilliSeconds -> POSIXTime :=
  fun '(MkDiffMilliSeconds s) => MkPOSIXTime s.

(* External variables:
     BinNums.Z HsToCoq.Err.Build_Default HsToCoq.Err.Default HsToCoq.Err.default
     PlutusLedgerApi_V1_Interval.Interval
*)
