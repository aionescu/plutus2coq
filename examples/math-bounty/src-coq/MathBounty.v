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
Require Import PlutusTx_Functor.
Require Import PlutusLedgerApi_V1_Time.
Require Import PlutusLedgerApi_V1_Interval.
Require Import PlutusLedgerApi_V3_Contexts.

(*
  A very simple Math Bounty smart contract.
  Inspired by the math bounty example from https://github.com/ernius/plutus-cardano-samples

  The contract stores a square number in the Datum, which can be redeemed by guessing the square root of the number.
*)

Record Datum := MkDatum { square : Z }.
Record Redeemer := MkRedeemer { guess : Z }.

Definition mathBounty : Datum -> Redeemer -> ScriptContext -> bool :=
  fun datum redeemer ctx => (guess redeemer * guess redeemer =? square datum)%Z.

Theorem mathBountyCorrect : forall datum redeemer ctx, mathBounty datum redeemer ctx = true -> (guess redeemer * guess redeemer = square datum)%Z.
Proof.
  intros datum redeemer ctx H.
  unfold mathBounty in H.
  apply Z.eqb_eq in H.
  exact H.
Qed.

Extract Inlined Constant Z.eqb => "(Prelude.==)".

(*
Timed version, which additionally checks that the guess is made before a deadline.
Doesn't work, because hs-to-coq does not properly translate `deriving` clauses,
so the `PlutusTx.Enum.Enum POSIXTime` instance is missing.

Definition timedMathBounty : Datum -> Redeemer -> ScriptContext -> bool :=
  fun datum redeemer ctx =>
    let guessCorrect := (guess redeemer * guess redeemer =? square datum)%Z in
    let beforeDeadline := contains (to (getPOSIXTime (deadline datum))) (fmap getPOSIXTime (txInfoValidRange (scriptContextTxInfo ctx))) in
    andb guessCorrect beforeDeadline.
*)
