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

Require PlutusTx_Bool.
Require Import ZArith.BinInt.
Require Import PlutusTx_Eq.
Require Import PlutusTx_Functor.
Require Import PlutusTx_Numeric.
Require Import PlutusLedgerApi_V1_Time.
Require Import PlutusLedgerApi_V1_Interval.
Require Import PlutusLedgerApi_V3_Contexts.

(*
  A very simple Math Bounty smart contract.
  Inspired by the math bounty example from https://github.com/ernius/plutus-cardano-samples

  The contract stores a square number in the Datum, which can be redeemed by guessing the square root of the number,
  but only before the deadline passes.
*)

Record Datum := MkDatum { square : Z; deadline : POSIXTime }.
Record Redeemer := MkRedeemer { guess : Z }.

Definition mathBounty : Datum -> Redeemer -> ScriptContext -> bool :=
  fun datum redeemer ctx =>
    let guessCorrect :=
      let guess := guess redeemer in
      (guess * guess =? square datum)%Z in
    let beforeDeadline :=
      let deadlineRange := to (getPOSIXTime (deadline datum)) in
      let txRange := fmap getPOSIXTime (txInfoValidRange (scriptContextTxInfo ctx)) in
      contains deadlineRange txRange
    in
    (guessCorrect && beforeDeadline)%bool.

Theorem mathBounty_guessCorrect : forall datum redeemer ctx, (mathBounty datum redeemer ctx = true) -> (guess redeemer * guess redeemer)%Z = square datum.
Proof.
  intros datum redeemer ctx H.
  unfold mathBounty in H.
  apply Bool.andb_true_iff in H.
  destruct H as [H1 H2].
  apply Z.eqb_eq in H1.
  exact H1.
Qed.

Theorem mathBounty_guessCorrect_beforeDeadline : forall datum redeemer ctx, (mathBounty datum redeemer ctx = true) -> (guess redeemer * guess redeemer)%Z = square datum /\ contains (to (getPOSIXTime (deadline datum))) (fmap getPOSIXTime (txInfoValidRange (scriptContextTxInfo ctx))) = true.
Proof.
Admitted.
