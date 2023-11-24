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
Require GHC.Base.
Require PlutusCore_Data.
Require String.

(* Converted type declarations: *)

Inductive BuiltinUnit : Type := | MkBuiltinUnit : unit -> BuiltinUnit.

Inductive BuiltinString : Type :=
  | MkBuiltinString : String.string -> BuiltinString.

Inductive BuiltinPair a b : Type :=
  | MkBuiltinPair : (a * b)%type -> BuiltinPair a b.

Inductive BuiltinList a : Type := | MkBuiltinList : list a -> BuiltinList a.

Definition BuiltinInteger :=
  BinNums.Z%type.

Inductive BuiltinData : Type :=
  | MkBuiltinData : PlutusCore_Data.Data -> BuiltinData.

Inductive BuiltinByteString : Type :=
  | MkBuiltinByteString : String.string -> BuiltinByteString.

Inductive BuiltinBool : Type := | MkBuiltinBool : bool -> BuiltinBool.

Inductive BuiltinBLS12_381_MlResult : Type :=.

Inductive BuiltinBLS12_381_G2_Element : Type :=.

Inductive BuiltinBLS12_381_G1_Element : Type :=.

Arguments MkBuiltinPair {_} {_} _.

Arguments MkBuiltinList {_} _.

(* Converted value declarations: *)

(* Skipping all instances of class `GHC.Show.Show', including
   `PlutusTx_Builtins_Internal.Show__BuiltinByteString' *)

Instance Eq___BuiltinByteString : GHC.Base.Eq_ BuiltinByteString.
Proof.
Admitted.

(* Skipping all instances of class `GHC.Base.Ord', including
   `PlutusTx_Builtins_Internal.Ord__BuiltinByteString' *)

(* Skipping all instances of class `GHC.Base.Semigroup', including
   `PlutusTx_Builtins_Internal.Semigroup__BuiltinByteString' *)

(* Skipping all instances of class `GHC.Base.Monoid', including
   `PlutusTx_Builtins_Internal.Monoid__BuiltinByteString' *)

(* Skipping all instances of class `Data.Hashable.Class.Hashable', including
   `PlutusTx_Builtins_Internal.Hashable__BuiltinByteString' *)

(* Skipping all instances of class `Codec.Serialise.Class.Serialise', including
   `PlutusTx_Builtins_Internal.Serialise__BuiltinByteString' *)

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `PlutusTx_Builtins_Internal.NFData__BuiltinByteString' *)

(* Skipping all instances of class `Data.ByteArray.Types.ByteArrayAccess',
   including `PlutusTx_Builtins_Internal.ByteArrayAccess__BuiltinByteString' *)

(* Skipping all instances of class `Data.ByteArray.Types.ByteArray', including
   `PlutusTx_Builtins_Internal.ByteArray__BuiltinByteString' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusTx_Builtins_Internal.Pretty__BuiltinByteString' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `PlutusTx_Builtins_Internal.Show__BuiltinString' *)

Instance Eq___BuiltinString : GHC.Base.Eq_ BuiltinString.
Proof.
Admitted.

(* Skipping all instances of class `GHC.Base.Ord', including
   `PlutusTx_Builtins_Internal.Ord__BuiltinString' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `PlutusTx_Builtins_Internal.Show__BuiltinPair' *)

Instance Eq___BuiltinPair
   : forall {a} {b},
     forall `{GHC.Base.Eq_ a} `{GHC.Base.Eq_ b}, GHC.Base.Eq_ (BuiltinPair a b).
Proof.
Admitted.

(* Skipping all instances of class `GHC.Base.Ord', including
   `PlutusTx_Builtins_Internal.Ord__BuiltinPair' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `PlutusTx_Builtins_Internal.Show__BuiltinList' *)

Instance Eq___BuiltinList
   : forall {a}, forall `{GHC.Base.Eq_ a}, GHC.Base.Eq_ (BuiltinList a).
Proof.
Admitted.

(* Skipping all instances of class `GHC.Base.Ord', including
   `PlutusTx_Builtins_Internal.Ord__BuiltinList' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `PlutusTx_Builtins_Internal.Show__BuiltinData' *)

Instance Eq___BuiltinData : GHC.Base.Eq_ BuiltinData.
Proof.
Admitted.

(* Skipping all instances of class `GHC.Base.Ord', including
   `PlutusTx_Builtins_Internal.Ord__BuiltinData' *)

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `PlutusTx_Builtins_Internal.NFData__BuiltinData' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusTx_Builtins_Internal.Pretty__BuiltinData' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `PlutusTx_Builtins_Internal.Show__BuiltinBLS12_381_G1_Element' *)

Instance Eq___BuiltinBLS12_381_G1_Element
   : GHC.Base.Eq_ BuiltinBLS12_381_G1_Element.
Proof.
Admitted.

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `PlutusTx_Builtins_Internal.NFData__BuiltinBLS12_381_G1_Element' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusTx_Builtins_Internal.Pretty__BuiltinBLS12_381_G1_Element' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `PlutusTx_Builtins_Internal.Show__BuiltinBLS12_381_G2_Element' *)

Instance Eq___BuiltinBLS12_381_G2_Element
   : GHC.Base.Eq_ BuiltinBLS12_381_G2_Element.
Proof.
Admitted.

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `PlutusTx_Builtins_Internal.NFData__BuiltinBLS12_381_G2_Element' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusTx_Builtins_Internal.Pretty__BuiltinBLS12_381_G2_Element' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `PlutusTx_Builtins_Internal.Show__BuiltinBLS12_381_MlResult' *)

Instance Eq___BuiltinBLS12_381_MlResult
   : GHC.Base.Eq_ BuiltinBLS12_381_MlResult.
Proof.
Admitted.

(* Skipping all instances of class `Control.DeepSeq.NFData', including
   `PlutusTx_Builtins_Internal.NFData__BuiltinBLS12_381_MlResult' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusTx_Builtins_Internal.Pretty__BuiltinBLS12_381_MlResult' *)

Axiom error : forall {a : Type}, BuiltinUnit -> a.

Axiom true : BuiltinBool.

Axiom false : BuiltinBool.

Axiom ifThenElse : forall {a : Type}, BuiltinBool -> a -> a -> a.

Axiom unitval : BuiltinUnit.

Axiom chooseUnit : forall {a : Type}, BuiltinUnit -> a -> a.

Axiom addInteger : BuiltinInteger -> BuiltinInteger -> BuiltinInteger.

Axiom subtractInteger : BuiltinInteger -> BuiltinInteger -> BuiltinInteger.

Axiom multiplyInteger : BuiltinInteger -> BuiltinInteger -> BuiltinInteger.

Axiom divideInteger : BuiltinInteger -> BuiltinInteger -> BuiltinInteger.

Axiom modInteger : BuiltinInteger -> BuiltinInteger -> BuiltinInteger.

Axiom quotientInteger : BuiltinInteger -> BuiltinInteger -> BuiltinInteger.

Axiom remainderInteger : BuiltinInteger -> BuiltinInteger -> BuiltinInteger.

Axiom lessThanInteger : BuiltinInteger -> BuiltinInteger -> BuiltinBool.

Axiom lessThanEqualsInteger : BuiltinInteger -> BuiltinInteger -> BuiltinBool.

Axiom equalsInteger : BuiltinInteger -> BuiltinInteger -> BuiltinBool.

Axiom appendByteString : BuiltinByteString ->
                         BuiltinByteString -> BuiltinByteString.

Axiom consByteString : BuiltinInteger -> BuiltinByteString -> BuiltinByteString.

Axiom sliceByteString : BuiltinInteger ->
                        BuiltinInteger -> BuiltinByteString -> BuiltinByteString.

Axiom lengthOfByteString : BuiltinByteString -> BuiltinInteger.

Axiom indexByteString : BuiltinByteString -> BuiltinInteger -> BuiltinInteger.

Axiom emptyByteString : BuiltinByteString.

Axiom sha2_256 : BuiltinByteString -> BuiltinByteString.

Axiom sha3_256 : BuiltinByteString -> BuiltinByteString.

Axiom blake2b_224 : BuiltinByteString -> BuiltinByteString.

Axiom blake2b_256 : BuiltinByteString -> BuiltinByteString.

Axiom keccak_256 : BuiltinByteString -> BuiltinByteString.

Axiom verifyEd25519Signature : BuiltinByteString ->
                               BuiltinByteString -> BuiltinByteString -> BuiltinBool.

Axiom verifyEcdsaSecp256k1Signature : BuiltinByteString ->
                                      BuiltinByteString -> BuiltinByteString -> BuiltinBool.

Axiom verifySchnorrSecp256k1Signature : BuiltinByteString ->
                                        BuiltinByteString -> BuiltinByteString -> BuiltinBool.

(* Skipping definition `PlutusTx_Builtins_Internal.traceAll' *)

Axiom equalsByteString : BuiltinByteString -> BuiltinByteString -> BuiltinBool.

Axiom lessThanByteString : BuiltinByteString ->
                           BuiltinByteString -> BuiltinBool.

Axiom lessThanEqualsByteString : BuiltinByteString ->
                                 BuiltinByteString -> BuiltinBool.

Axiom decodeUtf8 : BuiltinByteString -> BuiltinString.

Axiom appendString : BuiltinString -> BuiltinString -> BuiltinString.

Axiom emptyString : BuiltinString.

Axiom equalsString : BuiltinString -> BuiltinString -> BuiltinBool.

Axiom trace : forall {a : Type}, BuiltinString -> a -> a.

Axiom encodeUtf8 : BuiltinString -> BuiltinByteString.

Axiom fst : forall {a : Type}, forall {b : Type}, BuiltinPair a b -> a.

Axiom snd : forall {a : Type}, forall {b : Type}, BuiltinPair a b -> b.

Axiom mkPairData : BuiltinData ->
                   BuiltinData -> BuiltinPair BuiltinData BuiltinData.

Axiom null : forall {a : Type}, BuiltinList a -> BuiltinBool.

Axiom head : forall {a : Type}, BuiltinList a -> a.

Axiom tail : forall {a : Type}, BuiltinList a -> BuiltinList a.

Axiom chooseList : forall {a : Type},
                   forall {b : Type}, BuiltinList a -> b -> b -> b.

Axiom mkNilData : BuiltinUnit -> BuiltinList BuiltinData.

Axiom mkNilPairData : BuiltinUnit ->
                      BuiltinList (BuiltinPair BuiltinData BuiltinData).

Axiom mkCons : forall {a : Type}, a -> BuiltinList a -> BuiltinList a.

Axiom builtinDataToData : BuiltinData -> PlutusCore_Data.Data.

Axiom dataToBuiltinData : PlutusCore_Data.Data -> BuiltinData.

Axiom chooseData : forall {a : Type}, BuiltinData -> a -> a -> a -> a -> a -> a.

Axiom mkConstr : BuiltinInteger -> BuiltinList BuiltinData -> BuiltinData.

Axiom mkMap : BuiltinList (BuiltinPair BuiltinData BuiltinData) -> BuiltinData.

Axiom mkList : BuiltinList BuiltinData -> BuiltinData.

Axiom mkI : BuiltinInteger -> BuiltinData.

Axiom mkB : BuiltinByteString -> BuiltinData.

Axiom unsafeDataAsConstr : BuiltinData ->
                           BuiltinPair BuiltinInteger (BuiltinList BuiltinData).

Axiom unsafeDataAsMap : BuiltinData ->
                        BuiltinList (BuiltinPair BuiltinData BuiltinData).

Axiom unsafeDataAsList : BuiltinData -> BuiltinList BuiltinData.

Axiom unsafeDataAsI : BuiltinData -> BuiltinInteger.

Axiom unsafeDataAsB : BuiltinData -> BuiltinByteString.

Axiom equalsData : BuiltinData -> BuiltinData -> BuiltinBool.

Axiom serialiseData : BuiltinData -> BuiltinByteString.

Axiom bls12_381_G1_equals : BuiltinBLS12_381_G1_Element ->
                            BuiltinBLS12_381_G1_Element -> BuiltinBool.

Axiom bls12_381_G1_add : BuiltinBLS12_381_G1_Element ->
                         BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element.

Axiom bls12_381_G1_neg : BuiltinBLS12_381_G1_Element ->
                         BuiltinBLS12_381_G1_Element.

Axiom bls12_381_G1_scalarMul : BuiltinInteger ->
                               BuiltinBLS12_381_G1_Element -> BuiltinBLS12_381_G1_Element.

Axiom bls12_381_G1_compress : BuiltinBLS12_381_G1_Element -> BuiltinByteString.

Axiom bls12_381_G1_uncompress : BuiltinByteString ->
                                BuiltinBLS12_381_G1_Element.

Axiom bls12_381_G1_hashToGroup : BuiltinByteString ->
                                 BuiltinByteString -> BuiltinBLS12_381_G1_Element.

Axiom bls12_381_G1_zero : BuiltinBLS12_381_G1_Element.

Axiom bls12_381_G1_generator : BuiltinBLS12_381_G1_Element.

Axiom bls12_381_G2_equals : BuiltinBLS12_381_G2_Element ->
                            BuiltinBLS12_381_G2_Element -> BuiltinBool.

Axiom bls12_381_G2_add : BuiltinBLS12_381_G2_Element ->
                         BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element.

Axiom bls12_381_G2_neg : BuiltinBLS12_381_G2_Element ->
                         BuiltinBLS12_381_G2_Element.

Axiom bls12_381_G2_scalarMul : BuiltinInteger ->
                               BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_G2_Element.

Axiom bls12_381_G2_compress : BuiltinBLS12_381_G2_Element -> BuiltinByteString.

Axiom bls12_381_G2_uncompress : BuiltinByteString ->
                                BuiltinBLS12_381_G2_Element.

Axiom bls12_381_G2_hashToGroup : BuiltinByteString ->
                                 BuiltinByteString -> BuiltinBLS12_381_G2_Element.

Axiom bls12_381_G2_zero : BuiltinBLS12_381_G2_Element.

Axiom bls12_381_G2_generator : BuiltinBLS12_381_G2_Element.

Axiom bls12_381_millerLoop : BuiltinBLS12_381_G1_Element ->
                             BuiltinBLS12_381_G2_Element -> BuiltinBLS12_381_MlResult.

Axiom bls12_381_mulMlResult : BuiltinBLS12_381_MlResult ->
                              BuiltinBLS12_381_MlResult -> BuiltinBLS12_381_MlResult.

Axiom bls12_381_finalVerify : BuiltinBLS12_381_MlResult ->
                              BuiltinBLS12_381_MlResult -> BuiltinBool.

(* External variables:
     Type bool list op_zt__ unit BinNums.Z GHC.Base.Eq_ PlutusCore_Data.Data
     String.string
*)
