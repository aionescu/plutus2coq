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

(* No imports to convert. *)

(* Converted type declarations: *)

Inductive EvaluationResult a : Type :=
  | EvaluationSuccess : a -> EvaluationResult a
  | EvaluationFailure : EvaluationResult a.

Arguments EvaluationSuccess {_} _.

Arguments EvaluationFailure {_}.

(* Converted value declarations: *)

(* Skipping all instances of class
   `PlutusCore_Evaluation_Result.AsEvaluationFailure', including
   `PlutusCore_Evaluation_Result.AsEvaluationFailure__unit' *)

(* Skipping instance
   `PlutusCore_Evaluation_Result.MonadError__unit__EvaluationResult' of class
   `Control.Monad.Error.Class.MonadError' *)

(* Skipping instance
   `PlutusCore_Evaluation_Result.Applicative__EvaluationResult' of class
   `GHC.Base.Applicative' *)

(* Skipping instance `PlutusCore_Evaluation_Result.Monad__EvaluationResult' of
   class `GHC.Base.Monad' *)

(* Skipping all instances of class `GHC.Base.Alternative', including
   `PlutusCore_Evaluation_Result.Alternative__EvaluationResult' *)

(* Skipping instance `PlutusCore_Evaluation_Result.MonadFail__EvaluationResult'
   of class `Control.Monad.Fail.MonadFail' *)

(* Skipping all instances of class `Text.PrettyBy.Internal.PrettyBy', including
   `PlutusCore_Evaluation_Result.PrettyBy__EvaluationResult__5' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusCore_Evaluation_Result.Pretty__EvaluationResult' *)

(* Skipping definition `PlutusCore_Evaluation_Result.evaluationFailure' *)

(* Skipping definition `PlutusCore_Evaluation_Result._EvaluationFailureVia' *)

Axiom isEvaluationSuccess : forall {a : Type}, EvaluationResult a -> bool.

Axiom isEvaluationFailure : forall {a : Type}, EvaluationResult a -> bool.

(* External variables:
     Type bool
*)
