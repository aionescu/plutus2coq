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

Require GHC.Tuple.
Require String.

(* Converted type declarations: *)

Inductive Emitter a : Type :=
  | MkEmitter (unEmitter : GHC.Tuple.pair_type (list String.string) a)
   : Emitter a.

Arguments MkEmitter {_} _.

Definition unEmitter {a} (arg_0__ : Emitter a) :=
  let 'MkEmitter unEmitter := arg_0__ in
  unEmitter.

(* Converted value declarations: *)

Axiom runEmitter : forall {a : Type},
                   Emitter a -> (a * list String.string)%type.

Axiom emit : String.string -> Emitter unit.

(* External variables:
     Type list op_zt__ unit GHC.Tuple.pair_type String.string
*)
