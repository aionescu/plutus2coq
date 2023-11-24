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
Require PlutusLedgerApi_V1_Credential.
Require PlutusLedgerApi_V1_Crypto.
Require PlutusLedgerApi_V1_DCert.
Require PlutusLedgerApi_V1_Scripts.
Require PlutusLedgerApi_V1_Time.
Require PlutusLedgerApi_V1_Tx.
Require PlutusLedgerApi_V1_Value.

(* Converted type declarations: *)

Inductive TxInInfo : Type :=
  | MkTxInInfo (txInInfoOutRef : PlutusLedgerApi_V1_Tx.TxOutRef) (txInInfoResolved
    : PlutusLedgerApi_V1_Tx.TxOut)
   : TxInInfo.

Inductive TxInfo : Type :=
  | MkTxInfo (txInfoInputs : list TxInInfo) (txInfoOutputs
    : list PlutusLedgerApi_V1_Tx.TxOut) (txInfoFee
    : PlutusLedgerApi_V1_Value.Value) (txInfoMint : PlutusLedgerApi_V1_Value.Value)
  (txInfoDCert : list PlutusLedgerApi_V1_DCert.DCert) (txInfoWdrl
    : list (PlutusLedgerApi_V1_Credential.StakingCredential * BinNums.Z)%type)
  (txInfoValidRange : PlutusLedgerApi_V1_Time.POSIXTimeRange) (txInfoSignatories
    : list PlutusLedgerApi_V1_Crypto.PubKeyHash) (txInfoData
    : list (PlutusLedgerApi_V1_Scripts.DatumHash *
            PlutusLedgerApi_V1_Scripts.Datum)%type) (txInfoId : PlutusLedgerApi_V1_Tx.TxId)
   : TxInfo.

Inductive ScriptPurpose : Type :=
  | Minting : PlutusLedgerApi_V1_Value.CurrencySymbol -> ScriptPurpose
  | Spending : PlutusLedgerApi_V1_Tx.TxOutRef -> ScriptPurpose
  | Rewarding : PlutusLedgerApi_V1_Credential.StakingCredential -> ScriptPurpose
  | Certifying : PlutusLedgerApi_V1_DCert.DCert -> ScriptPurpose.

Inductive ScriptContext : Type :=
  | MkScriptContext (scriptContextTxInfo : TxInfo) (scriptContextPurpose
    : ScriptPurpose)
   : ScriptContext.

Definition txInInfoOutRef (arg_0__ : TxInInfo) :=
  let 'MkTxInInfo txInInfoOutRef _ := arg_0__ in
  txInInfoOutRef.

Definition txInInfoResolved (arg_0__ : TxInInfo) :=
  let 'MkTxInInfo _ txInInfoResolved := arg_0__ in
  txInInfoResolved.

Definition txInfoDCert (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ _ _ txInfoDCert _ _ _ _ _ := arg_0__ in
  txInfoDCert.

Definition txInfoData (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ _ _ _ _ _ _ txInfoData _ := arg_0__ in
  txInfoData.

Definition txInfoFee (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ txInfoFee _ _ _ _ _ _ _ := arg_0__ in
  txInfoFee.

Definition txInfoId (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ _ _ _ _ _ _ _ txInfoId := arg_0__ in
  txInfoId.

Definition txInfoInputs (arg_0__ : TxInfo) :=
  let 'MkTxInfo txInfoInputs _ _ _ _ _ _ _ _ _ := arg_0__ in
  txInfoInputs.

Definition txInfoMint (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ _ txInfoMint _ _ _ _ _ _ := arg_0__ in
  txInfoMint.

Definition txInfoOutputs (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ txInfoOutputs _ _ _ _ _ _ _ _ := arg_0__ in
  txInfoOutputs.

Definition txInfoSignatories (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ _ _ _ _ _ txInfoSignatories _ _ := arg_0__ in
  txInfoSignatories.

Definition txInfoValidRange (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ _ _ _ _ txInfoValidRange _ _ _ := arg_0__ in
  txInfoValidRange.

Definition txInfoWdrl (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ _ _ _ txInfoWdrl _ _ _ _ := arg_0__ in
  txInfoWdrl.

Definition scriptContextPurpose (arg_0__ : ScriptContext) :=
  let 'MkScriptContext _ scriptContextPurpose := arg_0__ in
  scriptContextPurpose.

Definition scriptContextTxInfo (arg_0__ : ScriptContext) :=
  let 'MkScriptContext scriptContextTxInfo _ := arg_0__ in
  scriptContextTxInfo.

(* Converted value declarations: *)

(* Skipping instance `PlutusLedgerApi_V1_Contexts.Eq__TxInInfo' of class
   `PlutusTx_Eq.Eq' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V1_Contexts.Pretty__TxInInfo' *)

(* Skipping instance `PlutusLedgerApi_V1_Contexts.Eq__ScriptPurpose' of class
   `PlutusTx_Eq.Eq' *)

(* Skipping instance `PlutusLedgerApi_V1_Contexts.Eq__TxInfo' of class
   `PlutusTx_Eq.Eq' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V1_Contexts.Pretty__TxInfo' *)

(* Skipping instance `PlutusLedgerApi_V1_Contexts.Eq__ScriptContext' of class
   `PlutusTx_Eq.Eq' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V1_Contexts.Pretty__ScriptContext' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Contexts.Lift__DefaultUni__TxInInfo' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Contexts.Typeable__DefaultUni__TxInInfo' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V1_Contexts.UnsafeFromData__TxInInfo' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V1_Contexts.FromData__TxInInfo' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V1_Contexts.ToData__TxInInfo' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Contexts.Lift__DefaultUni__TxInfo' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Contexts.Typeable__DefaultUni__TxInfo' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V1_Contexts.UnsafeFromData__TxInfo' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V1_Contexts.FromData__TxInfo' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V1_Contexts.ToData__TxInfo' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Contexts.Lift__DefaultUni__ScriptPurpose' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Contexts.Typeable__DefaultUni__ScriptPurpose' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V1_Contexts.UnsafeFromData__ScriptPurpose' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V1_Contexts.FromData__ScriptPurpose' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V1_Contexts.ToData__ScriptPurpose' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Contexts.Lift__DefaultUni__ScriptContext' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Contexts.Typeable__DefaultUni__ScriptContext' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V1_Contexts.UnsafeFromData__ScriptContext' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V1_Contexts.FromData__ScriptContext' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V1_Contexts.ToData__ScriptContext' *)

Axiom findOwnInput : ScriptContext -> option TxInInfo.

Axiom findDatum : PlutusLedgerApi_V1_Scripts.DatumHash ->
                  TxInfo -> option PlutusLedgerApi_V1_Scripts.Datum.

Axiom findDatumHash : PlutusLedgerApi_V1_Scripts.Datum ->
                      TxInfo -> option PlutusLedgerApi_V1_Scripts.DatumHash.

Axiom findTxInByTxOutRef : PlutusLedgerApi_V1_Tx.TxOutRef ->
                           TxInfo -> option TxInInfo.

Axiom findContinuingOutputs : ScriptContext -> list BinNums.Z.

Axiom getContinuingOutputs : ScriptContext -> list PlutusLedgerApi_V1_Tx.TxOut.

Axiom txSignedBy : TxInfo -> PlutusLedgerApi_V1_Crypto.PubKeyHash -> bool.

Axiom pubKeyOutputsAt : PlutusLedgerApi_V1_Crypto.PubKeyHash ->
                        TxInfo -> list PlutusLedgerApi_V1_Value.Value.

Axiom valuePaidTo : TxInfo ->
                    PlutusLedgerApi_V1_Crypto.PubKeyHash -> PlutusLedgerApi_V1_Value.Value.

Axiom valueSpent : TxInfo -> PlutusLedgerApi_V1_Value.Value.

Axiom valueProduced : TxInfo -> PlutusLedgerApi_V1_Value.Value.

Axiom ownCurrencySymbol : ScriptContext ->
                          PlutusLedgerApi_V1_Value.CurrencySymbol.

Axiom spendsOutput : TxInfo -> PlutusLedgerApi_V1_Tx.TxId -> BinNums.Z -> bool.

(* External variables:
     bool list op_zt__ option BinNums.Z
     PlutusLedgerApi_V1_Credential.StakingCredential
     PlutusLedgerApi_V1_Crypto.PubKeyHash PlutusLedgerApi_V1_DCert.DCert
     PlutusLedgerApi_V1_Scripts.Datum PlutusLedgerApi_V1_Scripts.DatumHash
     PlutusLedgerApi_V1_Time.POSIXTimeRange PlutusLedgerApi_V1_Tx.TxId
     PlutusLedgerApi_V1_Tx.TxOut PlutusLedgerApi_V1_Tx.TxOutRef
     PlutusLedgerApi_V1_Value.CurrencySymbol PlutusLedgerApi_V1_Value.Value
*)
