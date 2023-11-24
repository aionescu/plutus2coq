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

Require GHC.Base.
Require PlutusTx_Base.
Require PlutusTx_Builtins_Internal.
Import PlutusTx_Base.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.FromBuiltin',
   including `PlutusTx_Builtins_Class.FromBuiltin__BuiltinInteger__Z' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.ToBuiltin',
   including `PlutusTx_Builtins_Class.ToBuiltin__Z__BuiltinInteger' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.FromBuiltin',
   including `PlutusTx_Builtins_Class.FromBuiltin__BuiltinBool__bool' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.ToBuiltin',
   including `PlutusTx_Builtins_Class.ToBuiltin__bool__BuiltinBool' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.FromBuiltin',
   including `PlutusTx_Builtins_Class.FromBuiltin__BuiltinUnit__unit' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.ToBuiltin',
   including `PlutusTx_Builtins_Class.ToBuiltin__unit__BuiltinUnit' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.FromBuiltin',
   including `PlutusTx_Builtins_Class.FromBuiltin__BuiltinByteString__string' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.ToBuiltin',
   including `PlutusTx_Builtins_Class.ToBuiltin__string__BuiltinByteString' *)

(* Skipping all instances of class `Data.String.IsString', including
   `PlutusTx_Builtins_Class.IsString__BuiltinString' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.FromBuiltin',
   including `PlutusTx_Builtins_Class.FromBuiltin__BuiltinString__string' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.ToBuiltin',
   including `PlutusTx_Builtins_Class.ToBuiltin__string__BuiltinString' *)

(* Skipping all instances of class `Data.String.IsString', including
   `PlutusTx_Builtins_Class.IsString__BuiltinByteString' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.FromBuiltin',
   including `PlutusTx_Builtins_Class.FromBuiltin__BuiltinPair__op_zt__' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.ToBuiltin',
   including
   `PlutusTx_Builtins_Class.ToBuiltin__op_zt____BuiltinPair__BuiltinData__BuiltinData__BuiltinData__BuiltinData' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.FromBuiltin',
   including `PlutusTx_Builtins_Class.FromBuiltin__BuiltinList__list' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.ToBuiltin',
   including
   `PlutusTx_Builtins_Class.ToBuiltin__list__BuiltinList__BuiltinData__BuiltinData' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.ToBuiltin',
   including
   `PlutusTx_Builtins_Class.ToBuiltin__list__BuiltinList__op_zt____BuiltinPair__BuiltinData__BuiltinData__BuiltinData__BuiltinData' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.FromBuiltin',
   including `PlutusTx_Builtins_Class.FromBuiltin__BuiltinData__BuiltinData' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.ToBuiltin',
   including `PlutusTx_Builtins_Class.ToBuiltin__BuiltinData__BuiltinData' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.FromBuiltin',
   including
   `PlutusTx_Builtins_Class.FromBuiltin__BuiltinBLS12_381_G1_Element__Element' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.ToBuiltin',
   including
   `PlutusTx_Builtins_Class.ToBuiltin__Element__BuiltinBLS12_381_G1_Element' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.FromBuiltin',
   including
   `PlutusTx_Builtins_Class.FromBuiltin__BuiltinBLS12_381_G2_Element__Element' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.ToBuiltin',
   including
   `PlutusTx_Builtins_Class.ToBuiltin__Element__BuiltinBLS12_381_G2_Element' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.FromBuiltin',
   including
   `PlutusTx_Builtins_Class.FromBuiltin__BuiltinBLS12_381_MlResult__MlResult' *)

(* Skipping all instances of class `PlutusTx_Builtins_Class.ToBuiltin',
   including
   `PlutusTx_Builtins_Class.ToBuiltin__MlResult__BuiltinBLS12_381_MlResult' *)

Axiom stringToBuiltinString : GHC.Base.String ->
                              PlutusTx_Builtins_Internal.BuiltinString.

Definition obfuscatedId {a : Type} : a -> a :=
  fun a => a.

Definition stringToBuiltinByteString
   : GHC.Base.String -> PlutusTx_Builtins_Internal.BuiltinByteString :=
  fun str =>
    PlutusTx_Builtins_Internal.encodeUtf8 PlutusTx_Base.$ stringToBuiltinString str.

(* External variables:
     Type GHC.Base.String PlutusTx_Base.op_zd__
     PlutusTx_Builtins_Internal.BuiltinByteString
     PlutusTx_Builtins_Internal.BuiltinString PlutusTx_Builtins_Internal.encodeUtf8
*)
