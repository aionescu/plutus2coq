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

Require PlutusLedgerApi_V1_Credential.
Require PlutusLedgerApi_V1_Crypto.
Require PlutusLedgerApi_V1_Scripts.
Require PlutusTx_Bool.
Require PlutusTx_Eq.
Import PlutusTx_Bool.Notations.
Import PlutusTx_Eq.Notations.

(* Converted type declarations: *)

Inductive Address : Type :=
  | MkAddress (addressCredential : PlutusLedgerApi_V1_Credential.Credential)
  (addressStakingCredential
    : option PlutusLedgerApi_V1_Credential.StakingCredential)
   : Address.

Definition addressCredential (arg_0__ : Address) :=
  let 'MkAddress addressCredential _ := arg_0__ in
  addressCredential.

Definition addressStakingCredential (arg_0__ : Address) :=
  let 'MkAddress _ addressStakingCredential := arg_0__ in
  addressStakingCredential.

(* Converted value declarations: *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V1_Address.Pretty__Address' *)

Local Definition Eq__Address_op_zeze__ : Address -> Address -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkAddress cred stakingCred, MkAddress cred' stakingCred' =>
        (cred PlutusTx_Eq.== cred') PlutusTx_Bool.&&
        (stakingCred PlutusTx_Eq.== stakingCred')
    end.

Program Instance Eq__Address : PlutusTx_Eq.Eq Address :=
  fun _ k__ => k__ {| PlutusTx_Eq.op_zeze____ := Eq__Address_op_zeze__ |}.

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V1_Address.UnsafeFromData__Address' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V1_Address.FromData__Address' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V1_Address.ToData__Address' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Address.Lift__DefaultUni__Address' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Address.Typeable__DefaultUni__Address' *)

Definition pubKeyHashAddress
   : PlutusLedgerApi_V1_Crypto.PubKeyHash -> Address :=
  fun pkh => MkAddress (PlutusLedgerApi_V1_Credential.PubKeyCredential pkh) None.

Definition toPubKeyHash
   : Address -> option PlutusLedgerApi_V1_Crypto.PubKeyHash :=
  fun arg_0__ =>
    match arg_0__ with
    | MkAddress (PlutusLedgerApi_V1_Credential.PubKeyCredential k) _ => Some k
    | _ => None
    end.

Definition toScriptHash
   : Address -> option PlutusLedgerApi_V1_Scripts.ScriptHash :=
  fun arg_0__ =>
    match arg_0__ with
    | MkAddress (PlutusLedgerApi_V1_Credential.ScriptCredential k) _ => Some k
    | _ => None
    end.

Definition scriptHashAddress
   : PlutusLedgerApi_V1_Scripts.ScriptHash -> Address :=
  fun vh => MkAddress (PlutusLedgerApi_V1_Credential.ScriptCredential vh) None.

Definition stakingCredential
   : Address -> option PlutusLedgerApi_V1_Credential.StakingCredential :=
  fun '(MkAddress _ s) => s.

(* External variables:
     None Some bool option PlutusLedgerApi_V1_Credential.Credential
     PlutusLedgerApi_V1_Credential.PubKeyCredential
     PlutusLedgerApi_V1_Credential.ScriptCredential
     PlutusLedgerApi_V1_Credential.StakingCredential
     PlutusLedgerApi_V1_Crypto.PubKeyHash PlutusLedgerApi_V1_Scripts.ScriptHash
     PlutusTx_Bool.op_zaza__ PlutusTx_Eq.Eq PlutusTx_Eq.op_zeze__
     PlutusTx_Eq.op_zeze____
*)
