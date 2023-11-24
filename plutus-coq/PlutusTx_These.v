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

(* No imports to convert. *)

(* Converted type declarations: *)

Inductive These a b : Type :=
  | This : a -> These a b
  | That : b -> These a b
  | MkThese : a -> b -> These a b.

Arguments This {_} {_} _.

Arguments That {_} {_} _.

Arguments MkThese {_} {_} _ _.

(* Converted value declarations: *)

Definition theseWithDefault {a : Type} {b : Type} {c : Type}
   : a -> b -> (a -> b -> c) -> These a b -> c :=
  fun a' b' f =>
    fun arg_0__ =>
      match arg_0__ with
      | This a => f a b'
      | That b => f a' b
      | MkThese a b => f a b
      end.

Definition these {a : Type} {c : Type} {b : Type}
   : (a -> c) -> (b -> c) -> (a -> b -> c) -> These a b -> c :=
  fun f g h =>
    fun arg_0__ =>
      match arg_0__ with
      | This a => f a
      | That b => g b
      | MkThese a b => h a b
      end.

(* External variables:
     Type
*)
