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
Require PlutusTx_Builtins_Internal.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Axiom appendByteString : PlutusTx_Builtins_Internal.BuiltinByteString ->
                         PlutusTx_Builtins_Internal.BuiltinByteString ->
                         PlutusTx_Builtins_Internal.BuiltinByteString.

Axiom consByteString : BinNums.Z ->
                       PlutusTx_Builtins_Internal.BuiltinByteString ->
                       PlutusTx_Builtins_Internal.BuiltinByteString.

Axiom sliceByteString : BinNums.Z ->
                        BinNums.Z ->
                        PlutusTx_Builtins_Internal.BuiltinByteString ->
                        PlutusTx_Builtins_Internal.BuiltinByteString.

Axiom lengthOfByteString : PlutusTx_Builtins_Internal.BuiltinByteString ->
                           BinNums.Z.

Axiom indexByteString : PlutusTx_Builtins_Internal.BuiltinByteString ->
                        BinNums.Z -> BinNums.Z.

Axiom emptyByteString : PlutusTx_Builtins_Internal.BuiltinByteString.

Axiom sha2_256 : PlutusTx_Builtins_Internal.BuiltinByteString ->
                 PlutusTx_Builtins_Internal.BuiltinByteString.

Axiom sha3_256 : PlutusTx_Builtins_Internal.BuiltinByteString ->
                 PlutusTx_Builtins_Internal.BuiltinByteString.

Axiom blake2b_224 : PlutusTx_Builtins_Internal.BuiltinByteString ->
                    PlutusTx_Builtins_Internal.BuiltinByteString.

Axiom blake2b_256 : PlutusTx_Builtins_Internal.BuiltinByteString ->
                    PlutusTx_Builtins_Internal.BuiltinByteString.

Axiom keccak_256 : PlutusTx_Builtins_Internal.BuiltinByteString ->
                   PlutusTx_Builtins_Internal.BuiltinByteString.

Axiom verifyEd25519Signature : PlutusTx_Builtins_Internal.BuiltinByteString ->
                               PlutusTx_Builtins_Internal.BuiltinByteString ->
                               PlutusTx_Builtins_Internal.BuiltinByteString -> bool.

Axiom equalsByteString : PlutusTx_Builtins_Internal.BuiltinByteString ->
                         PlutusTx_Builtins_Internal.BuiltinByteString -> bool.

Axiom lessThanByteString : PlutusTx_Builtins_Internal.BuiltinByteString ->
                           PlutusTx_Builtins_Internal.BuiltinByteString -> bool.

Axiom lessThanEqualsByteString : PlutusTx_Builtins_Internal.BuiltinByteString ->
                                 PlutusTx_Builtins_Internal.BuiltinByteString -> bool.

Axiom greaterThanByteString : PlutusTx_Builtins_Internal.BuiltinByteString ->
                              PlutusTx_Builtins_Internal.BuiltinByteString -> bool.

Axiom greaterThanEqualsByteString
        : PlutusTx_Builtins_Internal.BuiltinByteString ->
          PlutusTx_Builtins_Internal.BuiltinByteString -> bool.

Axiom decodeUtf8 : PlutusTx_Builtins_Internal.BuiltinByteString ->
                   PlutusTx_Builtins_Internal.BuiltinString.

Axiom verifyEcdsaSecp256k1Signature
        : PlutusTx_Builtins_Internal.BuiltinByteString ->
          PlutusTx_Builtins_Internal.BuiltinByteString ->
          PlutusTx_Builtins_Internal.BuiltinByteString -> bool.

Axiom verifySchnorrSecp256k1Signature
        : PlutusTx_Builtins_Internal.BuiltinByteString ->
          PlutusTx_Builtins_Internal.BuiltinByteString ->
          PlutusTx_Builtins_Internal.BuiltinByteString -> bool.

(* Skipping definition `Z.add' *)

(* Skipping definition `Z.sub' *)

(* Skipping definition `Z.mul' *)

(* Skipping definition `Z.div' *)

(* Skipping definition `Z.modulo' *)

(* Skipping definition `Z.quot' *)

(* Skipping definition `Z.rem' *)

(* Skipping definition `ZArith.BinInt.Z.gtb' *)

(* Skipping definition `ZArith.BinInt.Z.geb' *)

(* Skipping definition `ZArith.BinInt.Z.ltb' *)

(* Skipping definition `ZArith.BinInt.Z.leb' *)

(* Skipping definition `ZArith.BinInt.Z.eqb' *)

Axiom error : forall {a : Type}, unit -> a.

Axiom appendString : PlutusTx_Builtins_Internal.BuiltinString ->
                     PlutusTx_Builtins_Internal.BuiltinString ->
                     PlutusTx_Builtins_Internal.BuiltinString.

Axiom emptyString : PlutusTx_Builtins_Internal.BuiltinString.

Axiom equalsString : PlutusTx_Builtins_Internal.BuiltinString ->
                     PlutusTx_Builtins_Internal.BuiltinString -> bool.

Axiom trace : forall {a : Type},
              PlutusTx_Builtins_Internal.BuiltinString -> a -> a.

Axiom encodeUtf8 : PlutusTx_Builtins_Internal.BuiltinString ->
                   PlutusTx_Builtins_Internal.BuiltinByteString.

Axiom matchList : forall {a : Type},
                  forall {r : Type},
                  PlutusTx_Builtins_Internal.BuiltinList a ->
                  r -> (a -> PlutusTx_Builtins_Internal.BuiltinList a -> r) -> r.

Axiom uncons : forall {a : Type},
               PlutusTx_Builtins_Internal.BuiltinList a ->
               option (a * PlutusTx_Builtins_Internal.BuiltinList a)%type.

Axiom unsafeUncons : forall {a : Type},
                     PlutusTx_Builtins_Internal.BuiltinList a ->
                     (a * PlutusTx_Builtins_Internal.BuiltinList a)%type.

Axiom pairToPair : forall {a : Type},
                   forall {b : Type}, PlutusTx_Builtins_Internal.BuiltinPair a b -> (a * b)%type.

Axiom chooseData : forall {a : Type},
                   PlutusTx_Builtins_Internal.BuiltinData -> a -> a -> a -> a -> a -> a.

Axiom serialiseData : PlutusTx_Builtins_Internal.BuiltinData ->
                      PlutusTx_Builtins_Internal.BuiltinByteString.

Axiom mkConstr : BinNums.Z ->
                 list PlutusTx_Builtins_Internal.BuiltinData ->
                 PlutusTx_Builtins_Internal.BuiltinData.

Axiom mkMap : list (PlutusTx_Builtins_Internal.BuiltinData *
                    PlutusTx_Builtins_Internal.BuiltinData)%type ->
              PlutusTx_Builtins_Internal.BuiltinData.

Axiom mkList : list PlutusTx_Builtins_Internal.BuiltinData ->
               PlutusTx_Builtins_Internal.BuiltinData.

Axiom mkI : BinNums.Z -> PlutusTx_Builtins_Internal.BuiltinData.

Axiom mkB : PlutusTx_Builtins_Internal.BuiltinByteString ->
            PlutusTx_Builtins_Internal.BuiltinData.

Axiom unsafeDataAsConstr : PlutusTx_Builtins_Internal.BuiltinData ->
                           (BinNums.Z * list PlutusTx_Builtins_Internal.BuiltinData)%type.

Axiom unsafeDataAsMap : PlutusTx_Builtins_Internal.BuiltinData ->
                        list (PlutusTx_Builtins_Internal.BuiltinData *
                              PlutusTx_Builtins_Internal.BuiltinData)%type.

Axiom unsafeDataAsList : PlutusTx_Builtins_Internal.BuiltinData ->
                         list PlutusTx_Builtins_Internal.BuiltinData.

Axiom unsafeDataAsI : PlutusTx_Builtins_Internal.BuiltinData -> BinNums.Z.

Axiom unsafeDataAsB : PlutusTx_Builtins_Internal.BuiltinData ->
                      PlutusTx_Builtins_Internal.BuiltinByteString.

Axiom equalsData : PlutusTx_Builtins_Internal.BuiltinData ->
                   PlutusTx_Builtins_Internal.BuiltinData -> bool.

Axiom matchData : forall {r : Type},
                  PlutusTx_Builtins_Internal.BuiltinData ->
                  (BinNums.Z -> list PlutusTx_Builtins_Internal.BuiltinData -> r) ->
                  (list (PlutusTx_Builtins_Internal.BuiltinData *
                         PlutusTx_Builtins_Internal.BuiltinData)%type ->
                   r) ->
                  (list PlutusTx_Builtins_Internal.BuiltinData -> r) ->
                  (BinNums.Z -> r) -> (PlutusTx_Builtins_Internal.BuiltinByteString -> r) -> r.

Axiom matchData' : forall {r : Type},
                   PlutusTx_Builtins_Internal.BuiltinData ->
                   (BinNums.Z ->
                    PlutusTx_Builtins_Internal.BuiltinList PlutusTx_Builtins_Internal.BuiltinData ->
                    r) ->
                   (PlutusTx_Builtins_Internal.BuiltinList (PlutusTx_Builtins_Internal.BuiltinPair
                                                            PlutusTx_Builtins_Internal.BuiltinData
                                                            PlutusTx_Builtins_Internal.BuiltinData) ->
                    r) ->
                   (PlutusTx_Builtins_Internal.BuiltinList
                    PlutusTx_Builtins_Internal.BuiltinData ->
                    r) ->
                   (BinNums.Z -> r) -> (PlutusTx_Builtins_Internal.BuiltinByteString -> r) -> r.

Axiom bls12_381_G1_equals
        : PlutusTx_Builtins_Internal.BuiltinBLS12_381_G1_Element ->
          PlutusTx_Builtins_Internal.BuiltinBLS12_381_G1_Element -> bool.

Axiom bls12_381_G1_add
        : PlutusTx_Builtins_Internal.BuiltinBLS12_381_G1_Element ->
          PlutusTx_Builtins_Internal.BuiltinBLS12_381_G1_Element ->
          PlutusTx_Builtins_Internal.BuiltinBLS12_381_G1_Element.

Axiom bls12_381_G1_scalarMul : BinNums.Z ->
                               PlutusTx_Builtins_Internal.BuiltinBLS12_381_G1_Element ->
                               PlutusTx_Builtins_Internal.BuiltinBLS12_381_G1_Element.

Axiom bls12_381_G1_neg
        : PlutusTx_Builtins_Internal.BuiltinBLS12_381_G1_Element ->
          PlutusTx_Builtins_Internal.BuiltinBLS12_381_G1_Element.

Axiom bls12_381_G1_compress
        : PlutusTx_Builtins_Internal.BuiltinBLS12_381_G1_Element ->
          PlutusTx_Builtins_Internal.BuiltinByteString.

Axiom bls12_381_G1_uncompress : PlutusTx_Builtins_Internal.BuiltinByteString ->
                                PlutusTx_Builtins_Internal.BuiltinBLS12_381_G1_Element.

Axiom bls12_381_G1_hashToGroup : PlutusTx_Builtins_Internal.BuiltinByteString ->
                                 PlutusTx_Builtins_Internal.BuiltinByteString ->
                                 PlutusTx_Builtins_Internal.BuiltinBLS12_381_G1_Element.

Axiom bls12_381_G1_zero
        : PlutusTx_Builtins_Internal.BuiltinBLS12_381_G1_Element.

Axiom bls12_381_G1_generator
        : PlutusTx_Builtins_Internal.BuiltinBLS12_381_G1_Element.

Axiom bls12_381_G2_equals
        : PlutusTx_Builtins_Internal.BuiltinBLS12_381_G2_Element ->
          PlutusTx_Builtins_Internal.BuiltinBLS12_381_G2_Element -> bool.

Axiom bls12_381_G2_add
        : PlutusTx_Builtins_Internal.BuiltinBLS12_381_G2_Element ->
          PlutusTx_Builtins_Internal.BuiltinBLS12_381_G2_Element ->
          PlutusTx_Builtins_Internal.BuiltinBLS12_381_G2_Element.

Axiom bls12_381_G2_scalarMul : BinNums.Z ->
                               PlutusTx_Builtins_Internal.BuiltinBLS12_381_G2_Element ->
                               PlutusTx_Builtins_Internal.BuiltinBLS12_381_G2_Element.

Axiom bls12_381_G2_neg
        : PlutusTx_Builtins_Internal.BuiltinBLS12_381_G2_Element ->
          PlutusTx_Builtins_Internal.BuiltinBLS12_381_G2_Element.

Axiom bls12_381_G2_compress
        : PlutusTx_Builtins_Internal.BuiltinBLS12_381_G2_Element ->
          PlutusTx_Builtins_Internal.BuiltinByteString.

Axiom bls12_381_G2_uncompress : PlutusTx_Builtins_Internal.BuiltinByteString ->
                                PlutusTx_Builtins_Internal.BuiltinBLS12_381_G2_Element.

Axiom bls12_381_G2_hashToGroup : PlutusTx_Builtins_Internal.BuiltinByteString ->
                                 PlutusTx_Builtins_Internal.BuiltinByteString ->
                                 PlutusTx_Builtins_Internal.BuiltinBLS12_381_G2_Element.

Axiom bls12_381_G2_zero
        : PlutusTx_Builtins_Internal.BuiltinBLS12_381_G2_Element.

Axiom bls12_381_G2_generator
        : PlutusTx_Builtins_Internal.BuiltinBLS12_381_G2_Element.

Axiom bls12_381_millerLoop
        : PlutusTx_Builtins_Internal.BuiltinBLS12_381_G1_Element ->
          PlutusTx_Builtins_Internal.BuiltinBLS12_381_G2_Element ->
          PlutusTx_Builtins_Internal.BuiltinBLS12_381_MlResult.

Axiom bls12_381_mulMlResult
        : PlutusTx_Builtins_Internal.BuiltinBLS12_381_MlResult ->
          PlutusTx_Builtins_Internal.BuiltinBLS12_381_MlResult ->
          PlutusTx_Builtins_Internal.BuiltinBLS12_381_MlResult.

Axiom bls12_381_finalVerify
        : PlutusTx_Builtins_Internal.BuiltinBLS12_381_MlResult ->
          PlutusTx_Builtins_Internal.BuiltinBLS12_381_MlResult -> bool.

(* External variables:
     Type bool list op_zt__ option unit BinNums.Z
     PlutusTx_Builtins_Internal.BuiltinBLS12_381_G1_Element
     PlutusTx_Builtins_Internal.BuiltinBLS12_381_G2_Element
     PlutusTx_Builtins_Internal.BuiltinBLS12_381_MlResult
     PlutusTx_Builtins_Internal.BuiltinByteString
     PlutusTx_Builtins_Internal.BuiltinData PlutusTx_Builtins_Internal.BuiltinList
     PlutusTx_Builtins_Internal.BuiltinPair PlutusTx_Builtins_Internal.BuiltinString
*)
