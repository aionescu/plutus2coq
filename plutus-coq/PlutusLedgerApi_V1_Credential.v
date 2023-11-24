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

Require BinNums.
Require PlutusLedgerApi_V1_Crypto.
Require PlutusLedgerApi_V1_Scripts.
Require PlutusTx_Eq.

(* Converted type declarations: *)

Inductive Credential : Type :=
  | PubKeyCredential : PlutusLedgerApi_V1_Crypto.PubKeyHash -> Credential
  | ScriptCredential : PlutusLedgerApi_V1_Scripts.ScriptHash -> Credential.

Inductive StakingCredential : Type :=
  | StakingHash : Credential -> StakingCredential
  | StakingPtr : BinNums.Z -> BinNums.Z -> BinNums.Z -> StakingCredential.

(* Converted value declarations: *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V1_Credential.Pretty__StakingCredential' *)

Instance Eq__Credential : PlutusTx_Eq.Eq Credential.
Proof.
Admitted.

Instance Eq__StakingCredential : PlutusTx_Eq.Eq StakingCredential.
Proof.
Admitted.

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V1_Credential.Pretty__Credential' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V1_Credential.UnsafeFromData__Credential' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V1_Credential.FromData__Credential' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V1_Credential.ToData__Credential' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V1_Credential.UnsafeFromData__StakingCredential' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V1_Credential.FromData__StakingCredential' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V1_Credential.ToData__StakingCredential' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Credential.Lift__DefaultUni__Credential' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Credential.Typeable__DefaultUni__Credential' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Credential.Lift__DefaultUni__StakingCredential' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Credential.Typeable__DefaultUni__StakingCredential' *)

(* External variables:
     BinNums.Z PlutusLedgerApi_V1_Crypto.PubKeyHash
     PlutusLedgerApi_V1_Scripts.ScriptHash PlutusTx_Eq.Eq
*)
