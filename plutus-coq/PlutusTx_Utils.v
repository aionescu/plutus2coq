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

Require GHC.Base.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Axiom mustBeReplaced : forall {a : Type}, GHC.Base.String -> a.

(* External variables:
     Type GHC.Base.String
*)
