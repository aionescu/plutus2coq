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

Require BinNums.
Require Control.Monad.
Require Control.Monad.Error.Class.
Require Control.Monad.Writer.Class.
Require GHC.Base.
Require PlutusCore.Default.Builtins.
Require PlutusCore.Evaluation.Machine.CostModelInterface.
Require PlutusLedgerApi.Common.Eval.
Require PlutusLedgerApi_Common_ParamName.
Import Control.Monad.Notations.
Import GHC.Base.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition mkEvaluationContext {m : Type -> Type}
  `{Control.Monad.Error.Class.MonadError
  PlutusCore.Evaluation.Machine.CostModelInterface.CostModelApplyError m}
  `{Control.Monad.Writer.Class.MonadWriter (list
                                            PlutusCore.Evaluation.Machine.CostModelInterface.CostModelApplyWarn) m}
   : list BinNums.Z -> m PlutusLedgerApi.Common.Eval.EvaluationContext :=
  PlutusLedgerApi_Common_ParamName.tagWithParamNames Control.Monad.>=>
  ((GHC.Base.pure GHC.Base.∘ PlutusLedgerApi_Common_ParamName.toCostModelParams)
   Control.Monad.>=>
   PlutusLedgerApi.Common.Eval.mkDynEvaluationContext
   PlutusCore.Default.Builtins.DefaultFunSemanticsVariant2).

(* External variables:
     Type list BinNums.Z Control.Monad.op_zgzezg__
     Control.Monad.Error.Class.MonadError Control.Monad.Writer.Class.MonadWriter
     GHC.Base.op_z2218U__ GHC.Base.pure
     PlutusCore.Default.Builtins.DefaultFunSemanticsVariant2
     PlutusCore.Evaluation.Machine.CostModelInterface.CostModelApplyError
     PlutusCore.Evaluation.Machine.CostModelInterface.CostModelApplyWarn
     PlutusLedgerApi.Common.Eval.EvaluationContext
     PlutusLedgerApi.Common.Eval.mkDynEvaluationContext
     PlutusLedgerApi_Common_ParamName.tagWithParamNames
     PlutusLedgerApi_Common_ParamName.toCostModelParams
*)
