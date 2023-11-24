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
Require HsToCoq.Err.
Require PlutusLedgerApi_V1_Credential.
Require PlutusLedgerApi_V1_Crypto.

(* Converted type declarations: *)

Inductive DCert : Type :=
  | DCertDelegRegKey : PlutusLedgerApi_V1_Credential.StakingCredential -> DCert
  | DCertDelegDeRegKey : PlutusLedgerApi_V1_Credential.StakingCredential -> DCert
  | DCertDelegDelegate
   : PlutusLedgerApi_V1_Credential.StakingCredential ->
     PlutusLedgerApi_V1_Crypto.PubKeyHash -> DCert
  | DCertPoolRegister
   : PlutusLedgerApi_V1_Crypto.PubKeyHash ->
     PlutusLedgerApi_V1_Crypto.PubKeyHash -> DCert
  | DCertPoolRetire : PlutusLedgerApi_V1_Crypto.PubKeyHash -> BinNums.Z -> DCert
  | DCertGenesis : DCert
  | DCertMir : DCert.

Instance Default__DCert : HsToCoq.Err.Default DCert :=
  HsToCoq.Err.Build_Default _ DCertGenesis.

(* No value declarations to convert. *)

(* Skipping instance `PlutusLedgerApi_V1_DCert.Eq__DCert' of class
   `PlutusTx_Eq.Eq' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V1_DCert.UnsafeFromData__DCert' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V1_DCert.FromData__DCert' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V1_DCert.ToData__DCert' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_DCert.Lift__DefaultUni__DCert' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_DCert.Typeable__DefaultUni__DCert' *)

(* External variables:
     BinNums.Z HsToCoq.Err.Build_Default HsToCoq.Err.Default
     PlutusLedgerApi_V1_Credential.StakingCredential
     PlutusLedgerApi_V1_Crypto.PubKeyHash
*)
