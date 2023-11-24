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
Require PlutusLedgerApi_V1_Address.
Require PlutusLedgerApi_V1_Crypto.
Require PlutusLedgerApi_V1_Scripts.
Require PlutusLedgerApi_V1_Value.
Require PlutusTx_Builtins_Internal.
Require PlutusTx_Eq.

(* Converted type declarations: *)

Inductive TxOut : Type :=
  | MkTxOut (txOutAddress : PlutusLedgerApi_V1_Address.Address) (txOutValue
    : PlutusLedgerApi_V1_Value.Value) (txOutDatumHash
    : option PlutusLedgerApi_V1_Scripts.DatumHash)
   : TxOut.

Inductive TxId : Type :=
  | MkTxId (getTxId : PlutusTx_Builtins_Internal.BuiltinByteString) : TxId.

Inductive TxOutRef : Type :=
  | MkTxOutRef (txOutRefId : TxId) (txOutRefIdx : BinNums.Z) : TxOutRef.

Inductive ScriptTag : Type :=
  | Spend : ScriptTag
  | Mint : ScriptTag
  | Cert : ScriptTag
  | Reward : ScriptTag.

Inductive RedeemerPtr : Type :=
  | MkRedeemerPtr : ScriptTag -> BinNums.Z -> RedeemerPtr.

Definition txOutAddress (arg_0__ : TxOut) :=
  let 'MkTxOut txOutAddress _ _ := arg_0__ in
  txOutAddress.

Definition txOutDatumHash (arg_0__ : TxOut) :=
  let 'MkTxOut _ _ txOutDatumHash := arg_0__ in
  txOutDatumHash.

Definition txOutValue (arg_0__ : TxOut) :=
  let 'MkTxOut _ txOutValue _ := arg_0__ in
  txOutValue.

Definition getTxId (arg_0__ : TxId) :=
  let 'MkTxId getTxId := arg_0__ in
  getTxId.

Definition txOutRefId (arg_0__ : TxOutRef) :=
  let 'MkTxOutRef txOutRefId _ := arg_0__ in
  txOutRefId.

Definition txOutRefIdx (arg_0__ : TxOutRef) :=
  let 'MkTxOutRef _ txOutRefIdx := arg_0__ in
  txOutRefIdx.

(* Converted value declarations: *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V1_Tx.Pretty__TxOutRef' *)

Instance Eq__TxOutRef : PlutusTx_Eq.Eq TxOutRef.
Proof.
Admitted.

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V1_Tx.Pretty__TxOut' *)

Instance Eq__TxOut : PlutusTx_Eq.Eq TxOut.
Proof.
Admitted.

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Tx.Lift__DefaultUni__TxId' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Tx.Typeable__DefaultUni__TxId' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V1_Tx.UnsafeFromData__TxId' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V1_Tx.FromData__TxId' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V1_Tx.ToData__TxId' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V1_Tx.UnsafeFromData__TxOut' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V1_Tx.FromData__TxOut' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V1_Tx.ToData__TxOut' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Tx.Lift__DefaultUni__TxOut' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Tx.Typeable__DefaultUni__TxOut' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V1_Tx.UnsafeFromData__TxOutRef' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V1_Tx.FromData__TxOutRef' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V1_Tx.ToData__TxOutRef' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Tx.Lift__DefaultUni__TxOutRef' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Tx.Typeable__DefaultUni__TxOutRef' *)

Axiom txOutDatum : TxOut -> option PlutusLedgerApi_V1_Scripts.DatumHash.

Axiom txOutPubKey : TxOut -> option PlutusLedgerApi_V1_Crypto.PubKeyHash.

Axiom txOutScriptHash : TxOut -> option PlutusLedgerApi_V1_Scripts.ScriptHash.

(* Skipping definition `PlutusLedgerApi_V1_Tx.outAddress' *)

(* Skipping definition `PlutusLedgerApi_V1_Tx.outValue' *)

Axiom isPubKeyOut : TxOut -> bool.

Axiom isPayToScriptOut : TxOut -> bool.

Axiom pubKeyHashTxOut : PlutusLedgerApi_V1_Value.Value ->
                        PlutusLedgerApi_V1_Crypto.PubKeyHash -> TxOut.

(* External variables:
     bool option BinNums.Z PlutusLedgerApi_V1_Address.Address
     PlutusLedgerApi_V1_Crypto.PubKeyHash PlutusLedgerApi_V1_Scripts.DatumHash
     PlutusLedgerApi_V1_Scripts.ScriptHash PlutusLedgerApi_V1_Value.Value
     PlutusTx_Builtins_Internal.BuiltinByteString PlutusTx_Eq.Eq
*)
