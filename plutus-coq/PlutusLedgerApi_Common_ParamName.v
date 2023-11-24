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

Require GHC.Enum.
Require String.

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
  | MkGenericParamName : a -> GenericParamName a.

Arguments MkGenericParamName {_} _.

(* No value declarations to convert. *)

(* Skipping instance
   `PlutusLedgerApi_Common_ParamName.IsParamName__GenericParamName' of class
   `PlutusLedgerApi_Common_ParamName.IsParamName' *)

(* Skipping all instances of class
   `PlutusLedgerApi_Common_ParamName.GIsParamName', including
   `PlutusLedgerApi_Common_ParamName.GIsParamName__M1__D' *)

(* Skipping all instances of class
   `PlutusLedgerApi_Common_ParamName.GIsParamName', including
   `PlutusLedgerApi_Common_ParamName.GIsParamName__M1__C__U1__23' *)

(* Skipping all instances of class
   `PlutusLedgerApi_Common_ParamName.GIsParamName', including
   `PlutusLedgerApi_Common_ParamName.GIsParamName__op_ZCzpZC__' *)

(* Skipping definition `PlutusLedgerApi_Common_ParamName.tagWithParamNames' *)

(* Skipping definition `PlutusLedgerApi_Common_ParamName.toCostModelParams' *)

(* External variables:
     Type option GHC.Enum.Bounded GHC.Enum.Enum String.string
*)
