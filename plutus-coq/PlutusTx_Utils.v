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

Require GHC.Base.
Require GHC.Err.
Import GHC.Base.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition mustBeReplaced {a : Type} : GHC.Base.String -> a :=
  fun message =>
    GHC.Err.error (GHC.Base.hs_string__
                   "This must be replaced by the core-to-plc plugin during compilation: "
                   GHC.Base.<<>>
                   message).

(* External variables:
     Type GHC.Base.String GHC.Base.op_zlzlzgzg__ GHC.Err.error
*)
