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
Require PlutusLedgerApi_V1_Scripts.
Require PlutusLedgerApi_V1_Time.
Require PlutusLedgerApi_V1_Tx.
Require PlutusLedgerApi_V1_Value.
Require PlutusLedgerApi_V2_Contexts.
Require PlutusLedgerApi_V2_Tx.
Require PlutusTx_AssocMap.
Require PlutusTx_Builtins_Internal.
Require PlutusTx_Ratio.

(* Converted type declarations: *)

Inductive Vote : Type := | VoteNo : Vote | VoteYes : Vote | Abstain : Vote.

Inductive ProtocolVersion : Type :=
  | MkProtocolVersion (pvMajor : BinNums.Z) (pvMinor : BinNums.Z)
   : ProtocolVersion.

Inductive HotCommitteeCredential : Type :=
  | MkHotCommitteeCredential
   : PlutusLedgerApi_V1_Credential.Credential -> HotCommitteeCredential.

Inductive GovernanceActionId : Type :=
  | MkGovernanceActionId (gaidTxId : PlutusLedgerApi_V1_Tx.TxId) (gaidGovActionIx
    : BinNums.Z)
   : GovernanceActionId.

Inductive DRepCredential : Type :=
  | MkDRepCredential : PlutusLedgerApi_V1_Credential.Credential -> DRepCredential.

Inductive Voter : Type :=
  | CommitteeVoter : HotCommitteeCredential -> Voter
  | DRepVoter : DRepCredential -> Voter
  | StakePoolVoter : PlutusLedgerApi_V1_Crypto.PubKeyHash -> Voter.

Inductive DRep : Type :=
  | MkDRep : DRepCredential -> DRep
  | DRepAlwaysAbstain : DRep
  | DRepAlwaysNoConfidence : DRep.

Inductive Delegatee : Type :=
  | DelegStake : PlutusLedgerApi_V1_Crypto.PubKeyHash -> Delegatee
  | DelegVote : DRep -> Delegatee
  | DelegStakeVote : PlutusLedgerApi_V1_Crypto.PubKeyHash -> DRep -> Delegatee.

Inductive Constitution : Type :=
  | MkConstitution (constitutionScript
    : option PlutusLedgerApi_V1_Scripts.ScriptHash)
   : Constitution.

Inductive ColdCommitteeCredential : Type :=
  | MkColdCommitteeCredential
   : PlutusLedgerApi_V1_Credential.Credential -> ColdCommitteeCredential.

Inductive Committee : Type :=
  | MkCommittee (committeeMembers
    : PlutusTx_AssocMap.Map ColdCommitteeCredential BinNums.Z) (committeeQuorum
    : PlutusTx_Ratio.Rational)
   : Committee.

Inductive TxCert : Type :=
  | TxCertRegStaking
   : PlutusLedgerApi_V1_Credential.Credential ->
     (option PlutusLedgerApi_V1_Value.Value) -> TxCert
  | TxCertUnRegStaking
   : PlutusLedgerApi_V1_Credential.Credential ->
     (option PlutusLedgerApi_V1_Value.Value) -> TxCert
  | TxCertDelegStaking
   : PlutusLedgerApi_V1_Credential.Credential -> Delegatee -> TxCert
  | TxCertRegDeleg
   : PlutusLedgerApi_V1_Credential.Credential ->
     Delegatee -> PlutusLedgerApi_V1_Value.Value -> TxCert
  | TxCertRegDRep : DRepCredential -> PlutusLedgerApi_V1_Value.Value -> TxCert
  | TxCertUpdateDRep : DRepCredential -> TxCert
  | TxCertUnRegDRep : DRepCredential -> PlutusLedgerApi_V1_Value.Value -> TxCert
  | TxCertAuthHotCommittee
   : ColdCommitteeCredential -> HotCommitteeCredential -> TxCert
  | TxCertResignColdCommittee : ColdCommitteeCredential -> TxCert.

Inductive ScriptPurpose : Type :=
  | Minting : PlutusLedgerApi_V1_Value.CurrencySymbol -> ScriptPurpose
  | Spending : PlutusLedgerApi_V1_Tx.TxOutRef -> ScriptPurpose
  | Rewarding : PlutusLedgerApi_V1_Credential.Credential -> ScriptPurpose
  | Certifying : TxCert -> ScriptPurpose
  | Voting : Voter -> GovernanceActionId -> ScriptPurpose
  | Proposing : BinNums.Z -> ScriptPurpose.

Inductive ChangedParameters : Type :=
  | MkChangedParameters (getChangedParameters
    : PlutusTx_Builtins_Internal.BuiltinData)
   : ChangedParameters.

Inductive GovernanceAction : Type :=
  | ParameterChange
   : (option GovernanceActionId) -> ChangedParameters -> GovernanceAction
  | HardForkInitiation
   : (option GovernanceActionId) -> ProtocolVersion -> GovernanceAction
  | TreasuryWithdrawals
   : (PlutusTx_AssocMap.Map PlutusLedgerApi_V1_Credential.Credential
      PlutusLedgerApi_V1_Value.Value) ->
     GovernanceAction
  | NoConfidence : (option GovernanceActionId) -> GovernanceAction
  | NewCommittee
   : (option GovernanceActionId) ->
     list ColdCommitteeCredential -> Committee -> GovernanceAction
  | NewConstitution
   : (option GovernanceActionId) -> Constitution -> GovernanceAction
  | InfoAction : GovernanceAction.

Inductive ProposalProcedure : Type :=
  | MkProposalProcedure (ppDeposit : PlutusLedgerApi_V1_Value.Value) (ppReturnAddr
    : PlutusLedgerApi_V1_Credential.Credential) (ppGovernanceAction
    : GovernanceAction)
   : ProposalProcedure.

Inductive TxInfo : Type :=
  | MkTxInfo (txInfoInputs : list PlutusLedgerApi_V2_Contexts.TxInInfo)
  (txInfoReferenceInputs : list PlutusLedgerApi_V2_Contexts.TxInInfo)
  (txInfoOutputs : list PlutusLedgerApi_V2_Tx.TxOut) (txInfoFee
    : PlutusLedgerApi_V1_Value.Value) (txInfoMint : PlutusLedgerApi_V1_Value.Value)
  (txInfoTxCerts : list TxCert) (txInfoWdrl
    : PlutusTx_AssocMap.Map PlutusLedgerApi_V1_Credential.Credential BinNums.Z)
  (txInfoValidRange : PlutusLedgerApi_V1_Time.POSIXTimeRange) (txInfoSignatories
    : list PlutusLedgerApi_V1_Crypto.PubKeyHash) (txInfoRedeemers
    : PlutusTx_AssocMap.Map ScriptPurpose PlutusLedgerApi_V1_Scripts.Redeemer)
  (txInfoData
    : PlutusTx_AssocMap.Map PlutusLedgerApi_V1_Scripts.DatumHash
      PlutusLedgerApi_V1_Scripts.Datum) (txInfoId : PlutusLedgerApi_V1_Tx.TxId)
  (txInfoVotes
    : PlutusTx_AssocMap.Map Voter (PlutusTx_AssocMap.Map GovernanceActionId Vote))
  (txInfoProposalProcedures : list ProposalProcedure) (txInfoCurrentTreasuryAmount
    : option PlutusLedgerApi_V1_Value.Value) (txInfoTreasuryDonation
    : option PlutusLedgerApi_V1_Value.Value)
   : TxInfo.

Inductive ScriptContext : Type :=
  | MkScriptContext (scriptContextTxInfo : TxInfo) (scriptContextPurpose
    : ScriptPurpose)
   : ScriptContext.

Definition pvMajor (arg_0__ : ProtocolVersion) :=
  let 'MkProtocolVersion pvMajor _ := arg_0__ in
  pvMajor.

Definition pvMinor (arg_0__ : ProtocolVersion) :=
  let 'MkProtocolVersion _ pvMinor := arg_0__ in
  pvMinor.

Definition gaidGovActionIx (arg_0__ : GovernanceActionId) :=
  let 'MkGovernanceActionId _ gaidGovActionIx := arg_0__ in
  gaidGovActionIx.

Definition gaidTxId (arg_0__ : GovernanceActionId) :=
  let 'MkGovernanceActionId gaidTxId _ := arg_0__ in
  gaidTxId.

Definition constitutionScript (arg_0__ : Constitution) :=
  let 'MkConstitution constitutionScript := arg_0__ in
  constitutionScript.

Definition committeeMembers (arg_0__ : Committee) :=
  let 'MkCommittee committeeMembers _ := arg_0__ in
  committeeMembers.

Definition committeeQuorum (arg_0__ : Committee) :=
  let 'MkCommittee _ committeeQuorum := arg_0__ in
  committeeQuorum.

Definition getChangedParameters (arg_0__ : ChangedParameters) :=
  let 'MkChangedParameters getChangedParameters := arg_0__ in
  getChangedParameters.

Definition ppDeposit (arg_0__ : ProposalProcedure) :=
  let 'MkProposalProcedure ppDeposit _ _ := arg_0__ in
  ppDeposit.

Definition ppGovernanceAction (arg_0__ : ProposalProcedure) :=
  let 'MkProposalProcedure _ _ ppGovernanceAction := arg_0__ in
  ppGovernanceAction.

Definition ppReturnAddr (arg_0__ : ProposalProcedure) :=
  let 'MkProposalProcedure _ ppReturnAddr _ := arg_0__ in
  ppReturnAddr.

Definition txInfoCurrentTreasuryAmount (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ _ _ _ _ _ _ _ _ _ _ _ _ txInfoCurrentTreasuryAmount _ :=
    arg_0__ in
  txInfoCurrentTreasuryAmount.

Definition txInfoData (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ _ _ _ _ _ _ _ _ txInfoData _ _ _ _ _ := arg_0__ in
  txInfoData.

Definition txInfoFee (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ _ txInfoFee _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  txInfoFee.

Definition txInfoId (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ _ _ _ _ _ _ _ _ _ txInfoId _ _ _ _ := arg_0__ in
  txInfoId.

Definition txInfoInputs (arg_0__ : TxInfo) :=
  let 'MkTxInfo txInfoInputs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  txInfoInputs.

Definition txInfoMint (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ _ _ txInfoMint _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  txInfoMint.

Definition txInfoOutputs (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ txInfoOutputs _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  txInfoOutputs.

Definition txInfoProposalProcedures (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ _ _ _ _ _ _ _ _ _ _ _ txInfoProposalProcedures _ _ :=
    arg_0__ in
  txInfoProposalProcedures.

Definition txInfoRedeemers (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ _ _ _ _ _ _ _ txInfoRedeemers _ _ _ _ _ _ := arg_0__ in
  txInfoRedeemers.

Definition txInfoReferenceInputs (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ txInfoReferenceInputs _ _ _ _ _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  txInfoReferenceInputs.

Definition txInfoSignatories (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ _ _ _ _ _ _ txInfoSignatories _ _ _ _ _ _ _ := arg_0__ in
  txInfoSignatories.

Definition txInfoTreasuryDonation (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ txInfoTreasuryDonation := arg_0__ in
  txInfoTreasuryDonation.

Definition txInfoTxCerts (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ _ _ _ txInfoTxCerts _ _ _ _ _ _ _ _ _ _ := arg_0__ in
  txInfoTxCerts.

Definition txInfoValidRange (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ _ _ _ _ _ txInfoValidRange _ _ _ _ _ _ _ _ := arg_0__ in
  txInfoValidRange.

Definition txInfoVotes (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ _ _ _ _ _ _ _ _ _ _ txInfoVotes _ _ _ := arg_0__ in
  txInfoVotes.

Definition txInfoWdrl (arg_0__ : TxInfo) :=
  let 'MkTxInfo _ _ _ _ _ _ txInfoWdrl _ _ _ _ _ _ _ _ _ := arg_0__ in
  txInfoWdrl.

Definition scriptContextPurpose (arg_0__ : ScriptContext) :=
  let 'MkScriptContext _ scriptContextPurpose := arg_0__ in
  scriptContextPurpose.

Definition scriptContextTxInfo (arg_0__ : ScriptContext) :=
  let 'MkScriptContext scriptContextTxInfo _ := arg_0__ in
  scriptContextTxInfo.

(* No value declarations to convert. *)

(* Skipping instance `PlutusLedgerApi_V3_Contexts.Eq__DRep' of class
   `PlutusTx_Eq.Eq' *)

(* Skipping instance `PlutusLedgerApi_V3_Contexts.Eq__Delegatee' of class
   `PlutusTx_Eq.Eq' *)

(* Skipping instance `PlutusLedgerApi_V3_Contexts.Eq__TxCert' of class
   `PlutusTx_Eq.Eq' *)

(* Skipping instance `PlutusLedgerApi_V3_Contexts.Eq__Voter' of class
   `PlutusTx_Eq.Eq' *)

(* Skipping instance `PlutusLedgerApi_V3_Contexts.Eq__Vote' of class
   `PlutusTx_Eq.Eq' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V3_Contexts.Pretty__GovernanceActionId' *)

(* Skipping instance `PlutusLedgerApi_V3_Contexts.Eq__GovernanceActionId' of
   class `PlutusTx_Eq.Eq' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V3_Contexts.Pretty__Committee' *)

(* Skipping instance `PlutusLedgerApi_V3_Contexts.Eq__Committee' of class
   `PlutusTx_Eq.Eq' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V3_Contexts.Pretty__Constitution' *)

(* Skipping instance `PlutusLedgerApi_V3_Contexts.Eq__Constitution' of class
   `PlutusTx_Eq.Eq' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V3_Contexts.Pretty__ProtocolVersion' *)

(* Skipping instance `PlutusLedgerApi_V3_Contexts.Eq__ProtocolVersion' of class
   `PlutusTx_Eq.Eq' *)

(* Skipping instance `PlutusLedgerApi_V3_Contexts.Eq__GovernanceAction' of class
   `PlutusTx_Eq.Eq' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V3_Contexts.Pretty__ProposalProcedure' *)

(* Skipping instance `PlutusLedgerApi_V3_Contexts.Eq__ProposalProcedure' of
   class `PlutusTx_Eq.Eq' *)

(* Skipping instance `PlutusLedgerApi_V3_Contexts.Eq__ScriptPurpose' of class
   `PlutusTx_Eq.Eq' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V3_Contexts.Pretty__TxInfo' *)

(* Skipping instance `PlutusLedgerApi_V3_Contexts.Eq__TxInfo' of class
   `PlutusTx_Eq.Eq' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V3_Contexts.Pretty__ScriptContext' *)

(* Skipping instance `PlutusLedgerApi_V3_Contexts.Eq__ScriptContext' of class
   `PlutusTx_Eq.Eq' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V3_Contexts.Lift__DefaultUni__ColdCommitteeCredential' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V3_Contexts.Typeable__DefaultUni__ColdCommitteeCredential' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V3_Contexts.Lift__DefaultUni__HotCommitteeCredential' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V3_Contexts.Typeable__DefaultUni__HotCommitteeCredential' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V3_Contexts.Lift__DefaultUni__DRepCredential' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V3_Contexts.Typeable__DefaultUni__DRepCredential' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V3_Contexts.Lift__DefaultUni__DRep' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V3_Contexts.Typeable__DefaultUni__DRep' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V3_Contexts.UnsafeFromData__DRep' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V3_Contexts.FromData__DRep' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V3_Contexts.ToData__DRep' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V3_Contexts.Lift__DefaultUni__Delegatee' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V3_Contexts.Typeable__DefaultUni__Delegatee' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V3_Contexts.UnsafeFromData__Delegatee' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V3_Contexts.FromData__Delegatee' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V3_Contexts.ToData__Delegatee' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V3_Contexts.Lift__DefaultUni__TxCert' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V3_Contexts.Typeable__DefaultUni__TxCert' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V3_Contexts.UnsafeFromData__TxCert' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V3_Contexts.FromData__TxCert' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V3_Contexts.ToData__TxCert' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V3_Contexts.Lift__DefaultUni__Voter' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V3_Contexts.Typeable__DefaultUni__Voter' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V3_Contexts.UnsafeFromData__Voter' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V3_Contexts.FromData__Voter' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V3_Contexts.ToData__Voter' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V3_Contexts.Lift__DefaultUni__Vote' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V3_Contexts.Typeable__DefaultUni__Vote' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V3_Contexts.UnsafeFromData__Vote' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V3_Contexts.FromData__Vote' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V3_Contexts.ToData__Vote' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V3_Contexts.Lift__DefaultUni__GovernanceActionId' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V3_Contexts.Typeable__DefaultUni__GovernanceActionId' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V3_Contexts.UnsafeFromData__GovernanceActionId' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V3_Contexts.FromData__GovernanceActionId' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V3_Contexts.ToData__GovernanceActionId' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V3_Contexts.Lift__DefaultUni__Committee' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V3_Contexts.Typeable__DefaultUni__Committee' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V3_Contexts.UnsafeFromData__Committee' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V3_Contexts.FromData__Committee' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V3_Contexts.ToData__Committee' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V3_Contexts.Lift__DefaultUni__Constitution' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V3_Contexts.Typeable__DefaultUni__Constitution' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V3_Contexts.UnsafeFromData__Constitution' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V3_Contexts.FromData__Constitution' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V3_Contexts.ToData__Constitution' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V3_Contexts.Lift__DefaultUni__ProtocolVersion' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V3_Contexts.Typeable__DefaultUni__ProtocolVersion' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V3_Contexts.UnsafeFromData__ProtocolVersion' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V3_Contexts.FromData__ProtocolVersion' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V3_Contexts.ToData__ProtocolVersion' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V3_Contexts.Lift__DefaultUni__ChangedParameters' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V3_Contexts.Typeable__DefaultUni__ChangedParameters' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V3_Contexts.Lift__DefaultUni__GovernanceAction' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V3_Contexts.Typeable__DefaultUni__GovernanceAction' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V3_Contexts.UnsafeFromData__GovernanceAction' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V3_Contexts.FromData__GovernanceAction' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V3_Contexts.ToData__GovernanceAction' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V3_Contexts.Lift__DefaultUni__ProposalProcedure' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V3_Contexts.Typeable__DefaultUni__ProposalProcedure' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V3_Contexts.UnsafeFromData__ProposalProcedure' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V3_Contexts.FromData__ProposalProcedure' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V3_Contexts.ToData__ProposalProcedure' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V3_Contexts.Lift__DefaultUni__ScriptPurpose' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V3_Contexts.Typeable__DefaultUni__ScriptPurpose' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V3_Contexts.UnsafeFromData__ScriptPurpose' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V3_Contexts.FromData__ScriptPurpose' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V3_Contexts.ToData__ScriptPurpose' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V3_Contexts.Lift__DefaultUni__TxInfo' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V3_Contexts.Typeable__DefaultUni__TxInfo' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V3_Contexts.UnsafeFromData__TxInfo' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V3_Contexts.FromData__TxInfo' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V3_Contexts.ToData__TxInfo' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V3_Contexts.Lift__DefaultUni__ScriptContext' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V3_Contexts.Typeable__DefaultUni__ScriptContext' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V3_Contexts.UnsafeFromData__ScriptContext' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V3_Contexts.FromData__ScriptContext' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V3_Contexts.ToData__ScriptContext' *)

(* External variables:
     list option BinNums.Z PlutusLedgerApi_V1_Credential.Credential
     PlutusLedgerApi_V1_Crypto.PubKeyHash PlutusLedgerApi_V1_Scripts.Datum
     PlutusLedgerApi_V1_Scripts.DatumHash PlutusLedgerApi_V1_Scripts.Redeemer
     PlutusLedgerApi_V1_Scripts.ScriptHash PlutusLedgerApi_V1_Time.POSIXTimeRange
     PlutusLedgerApi_V1_Tx.TxId PlutusLedgerApi_V1_Tx.TxOutRef
     PlutusLedgerApi_V1_Value.CurrencySymbol PlutusLedgerApi_V1_Value.Value
     PlutusLedgerApi_V2_Contexts.TxInInfo PlutusLedgerApi_V2_Tx.TxOut
     PlutusTx_AssocMap.Map PlutusTx_Builtins_Internal.BuiltinData
     PlutusTx_Ratio.Rational
*)
