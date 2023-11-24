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

Require Control.Monad.Error.Class.
Require Data.Either.
Require PlutusCore.Evaluation.Machine.ExBudget.
Require PlutusCore_Data.
Require PlutusLedgerApi.Common.Eval.
Require PlutusLedgerApi.Common.SerialisedScript.
Require PlutusLedgerApi_Common_ProtocolVersions.
Require PlutusLedgerApi_Common_Versions.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition thisLedgerLanguage
   : PlutusLedgerApi_Common_Versions.PlutusLedgerLanguage :=
  PlutusLedgerApi_Common_Versions.PlutusV3.

Definition deserialiseScript {m : Type -> Type}
  `{Control.Monad.Error.Class.MonadError
  PlutusLedgerApi.Common.SerialisedScript.ScriptDecodeError m}
   : PlutusLedgerApi_Common_ProtocolVersions.MajorProtocolVersion ->
     PlutusLedgerApi.Common.SerialisedScript.SerialisedScript ->
     m PlutusLedgerApi.Common.SerialisedScript.ScriptForEvaluation :=
  PlutusLedgerApi.Common.SerialisedScript.deserialiseScript thisLedgerLanguage.

Definition evaluateScriptCounting
   : PlutusLedgerApi_Common_ProtocolVersions.MajorProtocolVersion ->
     PlutusLedgerApi.Common.Eval.VerboseMode ->
     PlutusLedgerApi.Common.Eval.EvaluationContext ->
     PlutusLedgerApi.Common.SerialisedScript.ScriptForEvaluation ->
     list PlutusCore_Data.Data ->
     (PlutusLedgerApi.Common.Eval.LogOutput *
      Data.Either.Either PlutusLedgerApi.Common.Eval.EvaluationError
                         PlutusCore.Evaluation.Machine.ExBudget.ExBudget)%type :=
  PlutusLedgerApi.Common.Eval.evaluateScriptCounting thisLedgerLanguage.

Definition evaluateScriptRestricting
   : PlutusLedgerApi_Common_ProtocolVersions.MajorProtocolVersion ->
     PlutusLedgerApi.Common.Eval.VerboseMode ->
     PlutusLedgerApi.Common.Eval.EvaluationContext ->
     PlutusCore.Evaluation.Machine.ExBudget.ExBudget ->
     PlutusLedgerApi.Common.SerialisedScript.ScriptForEvaluation ->
     list PlutusCore_Data.Data ->
     (PlutusLedgerApi.Common.Eval.LogOutput *
      Data.Either.Either PlutusLedgerApi.Common.Eval.EvaluationError
                         PlutusCore.Evaluation.Machine.ExBudget.ExBudget)%type :=
  PlutusLedgerApi.Common.Eval.evaluateScriptRestricting thisLedgerLanguage.

(* External variables:
     Type list op_zt__ Control.Monad.Error.Class.MonadError Data.Either.Either
     PlutusCore.Evaluation.Machine.ExBudget.ExBudget PlutusCore_Data.Data
     PlutusLedgerApi.Common.Eval.EvaluationContext
     PlutusLedgerApi.Common.Eval.EvaluationError
     PlutusLedgerApi.Common.Eval.LogOutput PlutusLedgerApi.Common.Eval.VerboseMode
     PlutusLedgerApi.Common.Eval.evaluateScriptCounting
     PlutusLedgerApi.Common.Eval.evaluateScriptRestricting
     PlutusLedgerApi.Common.SerialisedScript.ScriptDecodeError
     PlutusLedgerApi.Common.SerialisedScript.ScriptForEvaluation
     PlutusLedgerApi.Common.SerialisedScript.SerialisedScript
     PlutusLedgerApi.Common.SerialisedScript.deserialiseScript
     PlutusLedgerApi_Common_ProtocolVersions.MajorProtocolVersion
     PlutusLedgerApi_Common_Versions.PlutusLedgerLanguage
     PlutusLedgerApi_Common_Versions.PlutusV3
*)
