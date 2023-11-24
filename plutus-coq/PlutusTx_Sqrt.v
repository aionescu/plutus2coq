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
Require HsToCoq.Err.
Require PlutusTx_Ratio.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Sqrt : Type :=
  | Imaginary : Sqrt
  | Exactly : BinNums.Z -> Sqrt
  | Approximately : BinNums.Z -> Sqrt.

Instance Default__Sqrt : HsToCoq.Err.Default Sqrt :=
  HsToCoq.Err.Build_Default _ Imaginary.

(* Converted value declarations: *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusTx_Sqrt.Lift__DefaultUni__Sqrt' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusTx_Sqrt.Typeable__DefaultUni__Sqrt' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusTx_Sqrt.UnsafeFromData__Sqrt' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusTx_Sqrt.FromData__Sqrt' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusTx_Sqrt.ToData__Sqrt' *)

Axiom rsqrt : PlutusTx_Ratio.Rational -> Sqrt.

Definition isqrt : BinNums.Z -> Sqrt :=
  fun n => rsqrt (PlutusTx_Ratio.unsafeRatio n #1).

(* External variables:
     BinNums.Z GHC.Num.fromInteger HsToCoq.Err.Build_Default HsToCoq.Err.Default
     PlutusTx_Ratio.Rational PlutusTx_Ratio.unsafeRatio
*)
