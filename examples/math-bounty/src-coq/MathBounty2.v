Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

From Coq Require Extraction.
From Coq Require ExtrHaskellBasic.
From Coq Require ExtrHaskellNatInteger.
From Coq Require ExtrHaskellZInteger.
From Coq Require ExtrHaskellString.

Extraction Language Haskell.
Unset Extraction Optimize.

Require GHC.Base.
Import GHC.Base.Notations.

Require Import ZArith.BinInt.
Require Import ZArith.BinIntDef.

Notation Datum := Z.

Inductive Datum :=
  | uninitialized : Datum
  | initialized   : Z -> Datum
  | claimed       : Datum.

Inductive Redeemer :=
  | init  : Z -> Redeemer
  | claim : Z -> Redeemer.

Definition mathBounty : Datum -> Redeemer -> option Datum :=
  fun datum redeemer ctx =>
    match datum, redeemer with
    | initialized n, claim m ->
        if Z.eqb (Z.mul m m) n then
          Some claimed
        else
          None
    | uninitialized, init n ->
        match Z.sqrtrem n with
        | (_, 0%Z) -> Some (initialized n)
        | _ -> None
        end
    | _, _ -> None
    end.

Inductive valid_datum : Datum -> Prop :=
  | valid_datum_uninitialized : valid_datum uninitialized
  | valid_datum_initialized : forall m, valid_datum (initialized (Z.mul m m)).

Theorem mathBounty_safety : forall d r d', mathBounty d r = Some d' -> valid_datum d -> valid_datum d'.
Proof.
Admitted.

Theorem mathBounty_liquidity : forall d, exists r d', valid_datum d -> d <> claimed -> mathBounty d r = Some d'.
Proof.
Admitted.
