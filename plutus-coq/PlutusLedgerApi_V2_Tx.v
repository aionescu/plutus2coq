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

Require PlutusLedgerApi_V1_Address.
Require PlutusLedgerApi_V1_Crypto.
Require PlutusLedgerApi_V1_Scripts.
Require PlutusLedgerApi_V1_Value.
Require PlutusTx_Eq.

(* Converted type declarations: *)

Inductive OutputDatum : Type :=
  | NoOutputDatum : OutputDatum
  | OutputDatumHash : PlutusLedgerApi_V1_Scripts.DatumHash -> OutputDatum
  | MkOutputDatum : PlutusLedgerApi_V1_Scripts.Datum -> OutputDatum.

Inductive TxOut : Type :=
  | MkTxOut (txOutAddress : PlutusLedgerApi_V1_Address.Address) (txOutValue
    : PlutusLedgerApi_V1_Value.Value) (txOutDatum : OutputDatum)
  (txOutReferenceScript : option PlutusLedgerApi_V1_Scripts.ScriptHash)
   : TxOut.

Definition txOutAddress (arg_0__ : TxOut) :=
  let 'MkTxOut txOutAddress _ _ _ := arg_0__ in
  txOutAddress.

Definition txOutDatum (arg_0__ : TxOut) :=
  let 'MkTxOut _ _ txOutDatum _ := arg_0__ in
  txOutDatum.

Definition txOutReferenceScript (arg_0__ : TxOut) :=
  let 'MkTxOut _ _ _ txOutReferenceScript := arg_0__ in
  txOutReferenceScript.

Definition txOutValue (arg_0__ : TxOut) :=
  let 'MkTxOut _ txOutValue _ _ := arg_0__ in
  txOutValue.

(* Converted value declarations: *)

Instance Eq__OutputDatum : PlutusTx_Eq.Eq OutputDatum.
Proof.
Admitted.

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V2_Tx.Pretty__OutputDatum' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V2_Tx.Pretty__TxOut' *)

Instance Eq__TxOut : PlutusTx_Eq.Eq TxOut.
Proof.
Admitted.

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V2_Tx.UnsafeFromData__OutputDatum' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V2_Tx.FromData__OutputDatum' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V2_Tx.ToData__OutputDatum' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V2_Tx.Lift__DefaultUni__OutputDatum' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V2_Tx.Typeable__DefaultUni__OutputDatum' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V2_Tx.UnsafeFromData__TxOut' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V2_Tx.FromData__TxOut' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V2_Tx.ToData__TxOut' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V2_Tx.Lift__DefaultUni__TxOut' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V2_Tx.Typeable__DefaultUni__TxOut' *)

Axiom txOutPubKey : TxOut -> option PlutusLedgerApi_V1_Crypto.PubKeyHash.

Axiom txOutScriptHash : TxOut -> option PlutusLedgerApi_V1_Scripts.ScriptHash.

(* Skipping definition `PlutusLedgerApi_V2_Tx.outAddress' *)

(* Skipping definition `PlutusLedgerApi_V2_Tx.outDatum' *)

(* Skipping definition `PlutusLedgerApi_V2_Tx.outValue' *)

(* Skipping definition `PlutusLedgerApi_V2_Tx.outReferenceScript' *)

Axiom isPubKeyOut : TxOut -> bool.

Axiom isPayToScriptOut : TxOut -> bool.

Axiom pubKeyHashTxOut : PlutusLedgerApi_V1_Value.Value ->
                        PlutusLedgerApi_V1_Crypto.PubKeyHash -> TxOut.

(* External variables:
     bool option PlutusLedgerApi_V1_Address.Address
     PlutusLedgerApi_V1_Crypto.PubKeyHash PlutusLedgerApi_V1_Scripts.Datum
     PlutusLedgerApi_V1_Scripts.DatumHash PlutusLedgerApi_V1_Scripts.ScriptHash
     PlutusLedgerApi_V1_Value.Value PlutusTx_Eq.Eq
*)
