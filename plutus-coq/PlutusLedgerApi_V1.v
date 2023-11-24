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

Require PlutusLedgerApi_Common_Versions.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition thisLedgerLanguage
   : PlutusLedgerApi_Common_Versions.PlutusLedgerLanguage :=
  PlutusLedgerApi_Common_Versions.PlutusV1.

(* Skipping definition `PlutusLedgerApi_V1.deserialiseScript' *)

(* Skipping definition `PlutusLedgerApi_V1.evaluateScriptCounting' *)

(* Skipping definition `PlutusLedgerApi_V1.evaluateScriptRestricting' *)

(* External variables:
     PlutusLedgerApi_Common_Versions.PlutusLedgerLanguage
     PlutusLedgerApi_Common_Versions.PlutusV1
*)
