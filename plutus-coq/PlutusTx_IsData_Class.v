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

Require PlutusCore_Data.

(* No type declarations to convert. *)

(* Converted value declarations: *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusTx_IsData_Class.ToData__BuiltinData' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusTx_IsData_Class.FromData__BuiltinData' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusTx_IsData_Class.UnsafeFromData__BuiltinData' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusTx_IsData_Class.ToData__Int' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusTx_IsData_Class.FromData__Int' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusTx_IsData_Class.UnsafeFromData__Int' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusTx_IsData_Class.ToData__Z' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusTx_IsData_Class.FromData__Z' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusTx_IsData_Class.UnsafeFromData__Z' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusTx_IsData_Class.ToData__BuiltinByteString' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusTx_IsData_Class.FromData__BuiltinByteString' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusTx_IsData_Class.UnsafeFromData__BuiltinByteString' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusTx_IsData_Class.ToData__list' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusTx_IsData_Class.FromData__list' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusTx_IsData_Class.UnsafeFromData__list' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusTx_IsData_Class.ToData__Void' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusTx_IsData_Class.FromData__Void' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusTx_IsData_Class.UnsafeFromData__Void' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusTx_IsData_Class.ToData__BuiltinBLS12_381_G1_Element' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusTx_IsData_Class.FromData__BuiltinBLS12_381_G1_Element' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusTx_IsData_Class.UnsafeFromData__BuiltinBLS12_381_G1_Element' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusTx_IsData_Class.ToData__BuiltinBLS12_381_G2_Element' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusTx_IsData_Class.FromData__BuiltinBLS12_381_G2_Element' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusTx_IsData_Class.UnsafeFromData__BuiltinBLS12_381_G2_Element' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusTx_IsData_Class.ToData__BuiltinBLS12_381_MlResult' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusTx_IsData_Class.FromData__BuiltinBLS12_381_MlResult' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusTx_IsData_Class.UnsafeFromData__BuiltinBLS12_381_MlResult' *)

Axiom toData : forall {a}, forall `{ToData a}, a -> PlutusCore_Data.Data.

Axiom fromData : forall {a},
                 forall `{FromData a}, PlutusCore_Data.Data -> option a.

(* External variables:
     FromData ToData option PlutusCore_Data.Data
*)
