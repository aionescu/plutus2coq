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

Require Language.Haskell.TH.Syntax.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Axiom asData : Language.Haskell.TH.Syntax.Q (list
                                             Language.Haskell.TH.Syntax.Dec) ->
               Language.Haskell.TH.Syntax.Q (list Language.Haskell.TH.Syntax.Dec).

Axiom asDataFor : Language.Haskell.TH.Syntax.Dec ->
                  Language.Haskell.TH.Syntax.Q (list Language.Haskell.TH.Syntax.Dec).

(* External variables:
     list Language.Haskell.TH.Syntax.Dec Language.Haskell.TH.Syntax.Q
*)
