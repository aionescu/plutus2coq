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
Require PlutusTx_Builtins_Internal.
Require String.

(* Converted type declarations: *)

Inductive ScriptHash : Type :=
  | MkScriptHash (getScriptHash : PlutusTx_Builtins_Internal.BuiltinByteString)
   : ScriptHash.

Inductive ScriptError : Type :=
  | EvaluationError : list String.string -> GHC.Base.String -> ScriptError
  | EvaluationException : GHC.Base.String -> GHC.Base.String -> ScriptError.

Inductive RedeemerHash : Type :=
  | MkRedeemerHash : PlutusTx_Builtins_Internal.BuiltinByteString -> RedeemerHash.

Inductive Redeemer : Type :=
  | MkRedeemer (getRedeemer : PlutusTx_Builtins_Internal.BuiltinData) : Redeemer.

Inductive DatumHash : Type :=
  | MkDatumHash : PlutusTx_Builtins_Internal.BuiltinByteString -> DatumHash.

Inductive Datum : Type :=
  | MkDatum (getDatum : PlutusTx_Builtins_Internal.BuiltinData) : Datum.

Inductive Context : Type :=
  | MkContext : PlutusTx_Builtins_Internal.BuiltinData -> Context.

Definition getScriptHash (arg_0__ : ScriptHash) :=
  let 'MkScriptHash getScriptHash := arg_0__ in
  getScriptHash.

Definition getRedeemer (arg_0__ : Redeemer) :=
  let 'MkRedeemer getRedeemer := arg_0__ in
  getRedeemer.

Definition getDatum (arg_0__ : Datum) :=
  let 'MkDatum getDatum := arg_0__ in
  getDatum.

(* No value declarations to convert. *)

(* Skipping all instances of class `Codec.Serialise.Class.Serialise', including
   `PlutusLedgerApi_V1_Scripts.Serialise__Datum' *)

(* Skipping all instances of class `Codec.Serialise.Class.Serialise', including
   `PlutusLedgerApi_V1_Scripts.Serialise__Redeemer' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Scripts.Lift__DefaultUni__ScriptHash' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Scripts.Typeable__DefaultUni__ScriptHash' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Scripts.Lift__DefaultUni__DatumHash' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Scripts.Typeable__DefaultUni__DatumHash' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Scripts.Lift__DefaultUni__RedeemerHash' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Scripts.Typeable__DefaultUni__RedeemerHash' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Scripts.Lift__DefaultUni__Datum' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Scripts.Typeable__DefaultUni__Datum' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Scripts.Lift__DefaultUni__Redeemer' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Scripts.Typeable__DefaultUni__Redeemer' *)

(* External variables:
     list GHC.Base.String PlutusTx_Builtins_Internal.BuiltinByteString
     PlutusTx_Builtins_Internal.BuiltinData String.string
*)
