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
Require Control.Monad.Error.Class.
Require Control.Monad.Writer.Class.
Require Data.Bifunctor.
Require Data.List.Extra.
Require Data.Map.Internal.
Require GHC.Base.
Require GHC.Enum.
Require GHC.List.
Require PlutusCore.Evaluation.Machine.CostModelInterface.
Require String.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Record IsParamName__Dict (a : Type) := IsParamName__Dict_Build {
  readParamName__ : String.string -> option a ;
  showParamName__ : a -> String.string }.

Definition IsParamName (a : Type) `{GHC.Enum.Enum a} `{GHC.Enum.Bounded a} :=
  forall r__, (IsParamName__Dict a -> r__) -> r__.
Existing Class IsParamName.

Definition readParamName `{g__0__ : IsParamName a}
   : String.string -> option a :=
  g__0__ _ (readParamName__ a).

Definition showParamName `{g__0__ : IsParamName a} : a -> String.string :=
  g__0__ _ (showParamName__ a).

Inductive GenericParamName a : Type :=
  | GenericParamName : a -> GenericParamName a.

Arguments GenericParamName {_} _.

(* Converted value declarations: *)

Local Definition IsParamName__GenericParamName_showParamName {inst_a : Type}
  `{GHC.Enum.Enum (GenericParamName inst_a)} `{GHC.Enum.Bounded (GenericParamName
                                                                 inst_a)} `{GHC.Generics.Generic inst_a} `{GIsParamName
  (GHC.Generics.Rep inst_a)}
   : GenericParamName inst_a -> String.string :=
  fun '(GenericParamName a) => gshowParamName (GHC.Generics.from a).

Local Definition IsParamName__GenericParamName_readParamName {inst_a : Type}
  `{GHC.Enum.Enum (GenericParamName inst_a)} `{GHC.Enum.Bounded (GenericParamName
                                                                 inst_a)} `{GHC.Generics.Generic inst_a} `{GIsParamName
  (GHC.Generics.Rep inst_a)}
   : String.string -> option (GenericParamName inst_a) :=
  fun str =>
    GHC.List.lookup str (GHC.Base.fmap (fun p =>
                                          pair (IsParamName__GenericParamName_showParamName p) p)
                                       Data.List.Extra.enumerate).

Program Instance IsParamName__GenericParamName {a : Type} `{GHC.Enum.Enum
  (GenericParamName a)} `{GHC.Enum.Bounded (GenericParamName a)}
  `{GHC.Generics.Generic a} `{GIsParamName (GHC.Generics.Rep a)}
   : IsParamName (GenericParamName a) :=
  fun _ k__ =>
    k__ {| readParamName__ := IsParamName__GenericParamName_readParamName ;
           showParamName__ := IsParamName__GenericParamName_showParamName |}.

(* Skipping all instances of class
   `PlutusLedgerApi_Common_ParamName.GIsParamName', including
   `PlutusLedgerApi_Common_ParamName.GIsParamName__M1__D' *)

(* Skipping all instances of class
   `PlutusLedgerApi_Common_ParamName.GIsParamName', including
   `PlutusLedgerApi_Common_ParamName.GIsParamName__M1__C__U1__23' *)

(* Skipping all instances of class
   `PlutusLedgerApi_Common_ParamName.GIsParamName', including
   `PlutusLedgerApi_Common_ParamName.GIsParamName__op_ZCzpZC__' *)

Axiom tagWithParamNames : forall {k : Type},
                          forall {m : Type -> Type},
                          forall `{GHC.Enum.Enum k},
                          forall `{GHC.Enum.Bounded k},
                          forall `{Control.Monad.Error.Class.MonadError
                          PlutusCore.Evaluation.Machine.CostModelInterface.CostModelApplyError m},
                          forall `{Control.Monad.Writer.Class.MonadWriter (list
                                                                           PlutusCore.Evaluation.Machine.CostModelInterface.CostModelApplyWarn)
                                                                          m},
                          list BinNums.Z -> m (list (k * BinNums.Z)%type).

Definition toCostModelParams {p : Type} `{IsParamName p}
   : list (p * BinNums.Z)%type ->
     PlutusCore.Evaluation.Machine.CostModelInterface.CostModelParams :=
  Data.Map.Internal.fromList GHC.Base.∘
  GHC.Base.fmap (Data.Bifunctor.first showParamName).

(* External variables:
     GIsParamName Type gshowParamName list op_zt__ option pair BinNums.Z
     Control.Monad.Error.Class.MonadError Control.Monad.Writer.Class.MonadWriter
     Data.Bifunctor.first Data.List.Extra.enumerate Data.Map.Internal.fromList
     GHC.Base.fmap GHC.Base.op_z2218U__ GHC.Enum.Bounded GHC.Enum.Enum
     GHC.Generics.Generic GHC.Generics.Rep GHC.Generics.from GHC.List.lookup
     PlutusCore.Evaluation.Machine.CostModelInterface.CostModelApplyError
     PlutusCore.Evaluation.Machine.CostModelInterface.CostModelApplyWarn
     PlutusCore.Evaluation.Machine.CostModelInterface.CostModelParams String.string
*)
