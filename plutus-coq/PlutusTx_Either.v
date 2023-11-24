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

Require Data.Either.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition isLeft {a : Type} {b : Type} : Data.Either.Either a b -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Data.Either.Left _ => true
    | Data.Either.Right _ => false
    end.

Definition isRight {a : Type} {b : Type} : Data.Either.Either a b -> bool :=
  fun arg_0__ =>
    match arg_0__ with
    | Data.Either.Left _ => false
    | Data.Either.Right _ => true
    end.

Definition either {a : Type} {c : Type} {b : Type}
   : (a -> c) -> (b -> c) -> Data.Either.Either a b -> c :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, _, Data.Either.Left x => f x
    | _, g, Data.Either.Right y => g y
    end.

(* External variables:
     Type bool false true Data.Either.Either Data.Either.Left Data.Either.Right
*)
