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

(* No imports to convert. *)

(* No type declarations to convert. *)

(* No value declarations to convert. *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusTx_IsData_Instances.UnsafeFromData__bool' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusTx_IsData_Instances.FromData__bool' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusTx_IsData_Instances.ToData__bool' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusTx_IsData_Instances.UnsafeFromData__option' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusTx_IsData_Instances.FromData__option' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusTx_IsData_Instances.ToData__option' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusTx_IsData_Instances.UnsafeFromData__Either' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusTx_IsData_Instances.FromData__Either' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusTx_IsData_Instances.ToData__Either' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusTx_IsData_Instances.UnsafeFromData__unit' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusTx_IsData_Instances.FromData__unit' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusTx_IsData_Instances.ToData__unit' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusTx_IsData_Instances.UnsafeFromData__pair_type' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusTx_IsData_Instances.FromData__pair_type' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusTx_IsData_Instances.ToData__pair_type' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusTx_IsData_Instances.UnsafeFromData__triple_type' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusTx_IsData_Instances.FromData__triple_type' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusTx_IsData_Instances.ToData__triple_type' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusTx_IsData_Instances.UnsafeFromData__quad_type' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusTx_IsData_Instances.FromData__quad_type' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusTx_IsData_Instances.ToData__quad_type' *)
