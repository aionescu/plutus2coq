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

Require PlutusLedgerApi_Common_ProtocolVersions.

(* Converted type declarations: *)

Inductive PlutusLedgerLanguage : Type :=
  | PlutusV1 : PlutusLedgerLanguage
  | PlutusV2 : PlutusLedgerLanguage
  | PlutusV3 : PlutusLedgerLanguage.

(* Converted value declarations: *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_Common_Versions.Pretty__PlutusLedgerLanguage' *)

(* Skipping definition `PlutusLedgerApi_Common_Versions.builtinsIntroducedIn' *)

(* Skipping definition
   `PlutusLedgerApi_Common_Versions.plcVersionsIntroducedIn' *)

Axiom ledgerLanguageIntroducedIn : PlutusLedgerLanguage ->
                                   PlutusLedgerApi_Common_ProtocolVersions.MajorProtocolVersion.

Axiom ledgerLanguagesAvailableIn
        : PlutusLedgerApi_Common_ProtocolVersions.MajorProtocolVersion ->
          list PlutusLedgerLanguage.

(* Skipping definition
   `PlutusLedgerApi_Common_Versions.plcVersionsAvailableIn' *)

(* Skipping definition `PlutusLedgerApi_Common_Versions.builtinsAvailableIn' *)

(* External variables:
     list PlutusLedgerApi_Common_ProtocolVersions.MajorProtocolVersion
*)
