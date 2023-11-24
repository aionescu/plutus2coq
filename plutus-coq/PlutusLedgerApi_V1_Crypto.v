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

Require PlutusTx_Builtins_Internal.

(* Converted type declarations: *)

Inductive PubKeyHash : Type :=
  | MkPubKeyHash (getPubKeyHash : PlutusTx_Builtins_Internal.BuiltinByteString)
   : PubKeyHash.

Definition getPubKeyHash (arg_0__ : PubKeyHash) :=
  let 'MkPubKeyHash getPubKeyHash := arg_0__ in
  getPubKeyHash.

(* No value declarations to convert. *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Crypto.Lift__DefaultUni__PubKeyHash' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Crypto.Typeable__DefaultUni__PubKeyHash' *)

(* External variables:
     PlutusTx_Builtins_Internal.BuiltinByteString
*)
