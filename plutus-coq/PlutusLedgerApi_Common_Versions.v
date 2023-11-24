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

Require Data.Foldable.
Require Data.List.Extra.
Require Data.Map.Internal.
Require Data.Set.Internal.
Require GHC.Base.
Require HsToCoq.Err.
Require PlutusCore.Default.Builtins.
Require PlutusCore.Version.
Require PlutusLedgerApi_Common_ProtocolVersions.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive PlutusLedgerLanguage : Type :=
  | PlutusV1 : PlutusLedgerLanguage
  | PlutusV2 : PlutusLedgerLanguage
  | PlutusV3 : PlutusLedgerLanguage.

Instance Default__PlutusLedgerLanguage
   : HsToCoq.Err.Default PlutusLedgerLanguage :=
  HsToCoq.Err.Build_Default _ PlutusV1.

(* Converted value declarations: *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_Common_Versions.Pretty__PlutusLedgerLanguage' *)

Definition builtinsIntroducedIn
   : Data.Map.Internal.Map (PlutusLedgerLanguage *
                            PlutusLedgerApi_Common_ProtocolVersions.MajorProtocolVersion)%type
                           (Data.Set.Internal.Set_ PlutusCore.Default.Builtins.DefaultFun) :=
  Data.Map.Internal.fromList (cons (pair (pair PlutusV1
                                               PlutusLedgerApi_Common_ProtocolVersions.alonzoPV)
                                         (Data.Set.Internal.fromList (cons PlutusCore.Default.Builtins.AddInteger (cons
                                                                            PlutusCore.Default.Builtins.SubtractInteger
                                                                            (cons
                                                                             PlutusCore.Default.Builtins.MultiplyInteger
                                                                             (cons
                                                                              PlutusCore.Default.Builtins.DivideInteger
                                                                              (cons
                                                                               PlutusCore.Default.Builtins.QuotientInteger
                                                                               (cons
                                                                                PlutusCore.Default.Builtins.RemainderInteger
                                                                                (cons
                                                                                 PlutusCore.Default.Builtins.ModInteger
                                                                                 (cons
                                                                                  PlutusCore.Default.Builtins.EqualsInteger
                                                                                  (cons
                                                                                   PlutusCore.Default.Builtins.LessThanInteger
                                                                                   (cons
                                                                                    PlutusCore.Default.Builtins.LessThanEqualsInteger
                                                                                    (cons
                                                                                     PlutusCore.Default.Builtins.AppendByteString
                                                                                     (cons
                                                                                      PlutusCore.Default.Builtins.ConsByteString
                                                                                      (cons
                                                                                       PlutusCore.Default.Builtins.SliceByteString
                                                                                       (cons
                                                                                        PlutusCore.Default.Builtins.LengthOfByteString
                                                                                        (cons
                                                                                         PlutusCore.Default.Builtins.IndexByteString
                                                                                         (cons
                                                                                          PlutusCore.Default.Builtins.EqualsByteString
                                                                                          (cons
                                                                                           PlutusCore.Default.Builtins.LessThanByteString
                                                                                           (cons
                                                                                            PlutusCore.Default.Builtins.LessThanEqualsByteString
                                                                                            (cons
                                                                                             PlutusCore.Default.Builtins.Sha2_256
                                                                                             (cons
                                                                                              PlutusCore.Default.Builtins.Sha3_256
                                                                                              (cons
                                                                                               PlutusCore.Default.Builtins.Blake2b_256
                                                                                               (cons
                                                                                                PlutusCore.Default.Builtins.VerifyEd25519Signature
                                                                                                (cons
                                                                                                 PlutusCore.Default.Builtins.AppendString
                                                                                                 (cons
                                                                                                  PlutusCore.Default.Builtins.EqualsString
                                                                                                  (cons
                                                                                                   PlutusCore.Default.Builtins.EncodeUtf8
                                                                                                   (cons
                                                                                                    PlutusCore.Default.Builtins.DecodeUtf8
                                                                                                    (cons
                                                                                                     PlutusCore.Default.Builtins.IfThenElse
                                                                                                     (cons
                                                                                                      PlutusCore.Default.Builtins.ChooseUnit
                                                                                                      (cons
                                                                                                       PlutusCore.Default.Builtins.Trace
                                                                                                       (cons
                                                                                                        PlutusCore.Default.Builtins.FstPair
                                                                                                        (cons
                                                                                                         PlutusCore.Default.Builtins.SndPair
                                                                                                         (cons
                                                                                                          PlutusCore.Default.Builtins.ChooseList
                                                                                                          (cons
                                                                                                           PlutusCore.Default.Builtins.MkCons
                                                                                                           (cons
                                                                                                            PlutusCore.Default.Builtins.HeadList
                                                                                                            (cons
                                                                                                             PlutusCore.Default.Builtins.TailList
                                                                                                             (cons
                                                                                                              PlutusCore.Default.Builtins.NullList
                                                                                                              (cons
                                                                                                               PlutusCore.Default.Builtins.ChooseData
                                                                                                               (cons
                                                                                                                PlutusCore.Default.Builtins.ConstrData
                                                                                                                (cons
                                                                                                                 PlutusCore.Default.Builtins.MapData
                                                                                                                 (cons
                                                                                                                  PlutusCore.Default.Builtins.ListData
                                                                                                                  (cons
                                                                                                                   PlutusCore.Default.Builtins.IData
                                                                                                                   (cons
                                                                                                                    PlutusCore.Default.Builtins.BData
                                                                                                                    (cons
                                                                                                                     PlutusCore.Default.Builtins.UnConstrData
                                                                                                                     (cons
                                                                                                                      PlutusCore.Default.Builtins.UnMapData
                                                                                                                      (cons
                                                                                                                       PlutusCore.Default.Builtins.UnListData
                                                                                                                       (cons
                                                                                                                        PlutusCore.Default.Builtins.UnIData
                                                                                                                        (cons
                                                                                                                         PlutusCore.Default.Builtins.UnBData
                                                                                                                         (cons
                                                                                                                          PlutusCore.Default.Builtins.EqualsData
                                                                                                                          (cons
                                                                                                                           PlutusCore.Default.Builtins.MkPairData
                                                                                                                           (cons
                                                                                                                            PlutusCore.Default.Builtins.MkNilData
                                                                                                                            (cons
                                                                                                                             PlutusCore.Default.Builtins.MkNilPairData
                                                                                                                             nil)))))))))))))))))))))))))))))))))))))))))))))))))))))
                                   (cons (pair (pair PlutusV2 PlutusLedgerApi_Common_ProtocolVersions.vasilPV)
                                               (Data.Set.Internal.fromList (cons
                                                                            PlutusCore.Default.Builtins.SerialiseData
                                                                            nil))) (cons (pair (pair PlutusV2
                                                                                                     PlutusLedgerApi_Common_ProtocolVersions.valentinePV)
                                                                                               (Data.Set.Internal.fromList
                                                                                                (cons
                                                                                                 PlutusCore.Default.Builtins.VerifyEcdsaSecp256k1Signature
                                                                                                 (cons
                                                                                                  PlutusCore.Default.Builtins.VerifySchnorrSecp256k1Signature
                                                                                                  nil)))) (cons (pair
                                                                                                                 (pair
                                                                                                                  PlutusV3
                                                                                                                  PlutusLedgerApi_Common_ProtocolVersions.conwayPV)
                                                                                                                 (Data.Set.Internal.fromList
                                                                                                                  (cons
                                                                                                                   PlutusCore.Default.Builtins.Bls12_381_G1_add
                                                                                                                   (cons
                                                                                                                    PlutusCore.Default.Builtins.Bls12_381_G1_neg
                                                                                                                    (cons
                                                                                                                     PlutusCore.Default.Builtins.Bls12_381_G1_scalarMul
                                                                                                                     (cons
                                                                                                                      PlutusCore.Default.Builtins.Bls12_381_G1_equal
                                                                                                                      (cons
                                                                                                                       PlutusCore.Default.Builtins.Bls12_381_G1_hashToGroup
                                                                                                                       (cons
                                                                                                                        PlutusCore.Default.Builtins.Bls12_381_G1_compress
                                                                                                                        (cons
                                                                                                                         PlutusCore.Default.Builtins.Bls12_381_G1_uncompress
                                                                                                                         (cons
                                                                                                                          PlutusCore.Default.Builtins.Bls12_381_G2_add
                                                                                                                          (cons
                                                                                                                           PlutusCore.Default.Builtins.Bls12_381_G2_neg
                                                                                                                           (cons
                                                                                                                            PlutusCore.Default.Builtins.Bls12_381_G2_scalarMul
                                                                                                                            (cons
                                                                                                                             PlutusCore.Default.Builtins.Bls12_381_G2_equal
                                                                                                                             (cons
                                                                                                                              PlutusCore.Default.Builtins.Bls12_381_G2_hashToGroup
                                                                                                                              (cons
                                                                                                                               PlutusCore.Default.Builtins.Bls12_381_G2_compress
                                                                                                                               (cons
                                                                                                                                PlutusCore.Default.Builtins.Bls12_381_G2_uncompress
                                                                                                                                (cons
                                                                                                                                 PlutusCore.Default.Builtins.Bls12_381_millerLoop
                                                                                                                                 (cons
                                                                                                                                  PlutusCore.Default.Builtins.Bls12_381_mulMlResult
                                                                                                                                  (cons
                                                                                                                                   PlutusCore.Default.Builtins.Bls12_381_finalVerify
                                                                                                                                   (cons
                                                                                                                                    PlutusCore.Default.Builtins.Keccak_256
                                                                                                                                    (cons
                                                                                                                                     PlutusCore.Default.Builtins.Blake2b_224
                                                                                                                                     nil)))))))))))))))))))))
                                                                                                                nil)))).

Definition plcVersionsIntroducedIn
   : Data.Map.Internal.Map (PlutusLedgerLanguage *
                            PlutusLedgerApi_Common_ProtocolVersions.MajorProtocolVersion)%type
                           (Data.Set.Internal.Set_ PlutusCore.Version.Version) :=
  Data.Map.Internal.fromList (cons (pair (pair PlutusV1
                                               PlutusLedgerApi_Common_ProtocolVersions.alonzoPV)
                                         (Data.Set.Internal.fromList (cons PlutusCore.Version.plcVersion100 nil))) (cons
                                    (pair (pair PlutusV3 PlutusLedgerApi_Common_ProtocolVersions.conwayPV)
                                          (Data.Set.Internal.fromList (cons PlutusCore.Version.plcVersion110 nil)))
                                    nil)).

Definition ledgerLanguageIntroducedIn
   : PlutusLedgerLanguage ->
     PlutusLedgerApi_Common_ProtocolVersions.MajorProtocolVersion :=
  fun arg_0__ =>
    match arg_0__ with
    | PlutusV1 => PlutusLedgerApi_Common_ProtocolVersions.alonzoPV
    | PlutusV2 => PlutusLedgerApi_Common_ProtocolVersions.vasilPV
    | PlutusV3 => PlutusLedgerApi_Common_ProtocolVersions.conwayPV
    end.

Definition ledgerLanguagesAvailableIn
   : PlutusLedgerApi_Common_ProtocolVersions.MajorProtocolVersion ->
     Data.Set.Internal.Set_ PlutusLedgerLanguage :=
  fun searchPv =>
    let ledgerVersionToSet
     : PlutusLedgerLanguage -> Data.Set.Internal.Set_ PlutusLedgerLanguage :=
      fun lv =>
        if ledgerLanguageIntroducedIn lv GHC.Base.<= searchPv : bool
        then Data.Set.Internal.singleton lv else
        GHC.Base.mempty in
    Data.Foldable.foldMap ledgerVersionToSet Data.List.Extra.enumerate.

Definition plcVersionsAvailableIn
   : PlutusLedgerLanguage ->
     PlutusLedgerApi_Common_ProtocolVersions.MajorProtocolVersion ->
     Data.Set.Internal.Set_ PlutusCore.Version.Version :=
  fun thisLv thisPv =>
    let plcVersionAvailableIn
     : (PlutusLedgerLanguage *
        PlutusLedgerApi_Common_ProtocolVersions.MajorProtocolVersion)%type ->
       bool :=
      fun '(pair introducedInLv introducedInPv) =>
        andb (introducedInLv GHC.Base.<= thisLv) (introducedInPv GHC.Base.<= thisPv) in
    Data.Foldable.fold (Data.Map.Internal.elems (Data.Map.Internal.takeWhileAntitone
                                                 plcVersionAvailableIn plcVersionsIntroducedIn)).

Definition builtinsAvailableIn
   : PlutusLedgerLanguage ->
     PlutusLedgerApi_Common_ProtocolVersions.MajorProtocolVersion ->
     Data.Set.Internal.Set_ PlutusCore.Default.Builtins.DefaultFun :=
  fun thisLv thisPv =>
    let builtinAvailableIn
     : (PlutusLedgerLanguage *
        PlutusLedgerApi_Common_ProtocolVersions.MajorProtocolVersion)%type ->
       bool :=
      fun '(pair introducedInLv introducedInPv) =>
        andb (introducedInLv GHC.Base.<= thisLv) (introducedInPv GHC.Base.<= thisPv) in
    Data.Foldable.fold (Data.Map.Internal.elems (Data.Map.Internal.takeWhileAntitone
                                                 builtinAvailableIn builtinsIntroducedIn)).

(* External variables:
     andb bool cons nil op_zt__ pair Data.Foldable.fold Data.Foldable.foldMap
     Data.List.Extra.enumerate Data.Map.Internal.Map Data.Map.Internal.elems
     Data.Map.Internal.fromList Data.Map.Internal.takeWhileAntitone
     Data.Set.Internal.Set_ Data.Set.Internal.fromList Data.Set.Internal.singleton
     GHC.Base.mempty GHC.Base.op_zlze__ HsToCoq.Err.Build_Default HsToCoq.Err.Default
     PlutusCore.Default.Builtins.AddInteger
     PlutusCore.Default.Builtins.AppendByteString
     PlutusCore.Default.Builtins.AppendString PlutusCore.Default.Builtins.BData
     PlutusCore.Default.Builtins.Blake2b_224 PlutusCore.Default.Builtins.Blake2b_256
     PlutusCore.Default.Builtins.Bls12_381_G1_add
     PlutusCore.Default.Builtins.Bls12_381_G1_compress
     PlutusCore.Default.Builtins.Bls12_381_G1_equal
     PlutusCore.Default.Builtins.Bls12_381_G1_hashToGroup
     PlutusCore.Default.Builtins.Bls12_381_G1_neg
     PlutusCore.Default.Builtins.Bls12_381_G1_scalarMul
     PlutusCore.Default.Builtins.Bls12_381_G1_uncompress
     PlutusCore.Default.Builtins.Bls12_381_G2_add
     PlutusCore.Default.Builtins.Bls12_381_G2_compress
     PlutusCore.Default.Builtins.Bls12_381_G2_equal
     PlutusCore.Default.Builtins.Bls12_381_G2_hashToGroup
     PlutusCore.Default.Builtins.Bls12_381_G2_neg
     PlutusCore.Default.Builtins.Bls12_381_G2_scalarMul
     PlutusCore.Default.Builtins.Bls12_381_G2_uncompress
     PlutusCore.Default.Builtins.Bls12_381_finalVerify
     PlutusCore.Default.Builtins.Bls12_381_millerLoop
     PlutusCore.Default.Builtins.Bls12_381_mulMlResult
     PlutusCore.Default.Builtins.ChooseData PlutusCore.Default.Builtins.ChooseList
     PlutusCore.Default.Builtins.ChooseUnit
     PlutusCore.Default.Builtins.ConsByteString
     PlutusCore.Default.Builtins.ConstrData PlutusCore.Default.Builtins.DecodeUtf8
     PlutusCore.Default.Builtins.DefaultFun PlutusCore.Default.Builtins.DivideInteger
     PlutusCore.Default.Builtins.EncodeUtf8
     PlutusCore.Default.Builtins.EqualsByteString
     PlutusCore.Default.Builtins.EqualsData PlutusCore.Default.Builtins.EqualsInteger
     PlutusCore.Default.Builtins.EqualsString PlutusCore.Default.Builtins.FstPair
     PlutusCore.Default.Builtins.HeadList PlutusCore.Default.Builtins.IData
     PlutusCore.Default.Builtins.IfThenElse
     PlutusCore.Default.Builtins.IndexByteString
     PlutusCore.Default.Builtins.Keccak_256
     PlutusCore.Default.Builtins.LengthOfByteString
     PlutusCore.Default.Builtins.LessThanByteString
     PlutusCore.Default.Builtins.LessThanEqualsByteString
     PlutusCore.Default.Builtins.LessThanEqualsInteger
     PlutusCore.Default.Builtins.LessThanInteger PlutusCore.Default.Builtins.ListData
     PlutusCore.Default.Builtins.MapData PlutusCore.Default.Builtins.MkCons
     PlutusCore.Default.Builtins.MkNilData PlutusCore.Default.Builtins.MkNilPairData
     PlutusCore.Default.Builtins.MkPairData PlutusCore.Default.Builtins.ModInteger
     PlutusCore.Default.Builtins.MultiplyInteger PlutusCore.Default.Builtins.NullList
     PlutusCore.Default.Builtins.QuotientInteger
     PlutusCore.Default.Builtins.RemainderInteger
     PlutusCore.Default.Builtins.SerialiseData PlutusCore.Default.Builtins.Sha2_256
     PlutusCore.Default.Builtins.Sha3_256 PlutusCore.Default.Builtins.SliceByteString
     PlutusCore.Default.Builtins.SndPair PlutusCore.Default.Builtins.SubtractInteger
     PlutusCore.Default.Builtins.TailList PlutusCore.Default.Builtins.Trace
     PlutusCore.Default.Builtins.UnBData PlutusCore.Default.Builtins.UnConstrData
     PlutusCore.Default.Builtins.UnIData PlutusCore.Default.Builtins.UnListData
     PlutusCore.Default.Builtins.UnMapData
     PlutusCore.Default.Builtins.VerifyEcdsaSecp256k1Signature
     PlutusCore.Default.Builtins.VerifyEd25519Signature
     PlutusCore.Default.Builtins.VerifySchnorrSecp256k1Signature
     PlutusCore.Version.Version PlutusCore.Version.plcVersion100
     PlutusCore.Version.plcVersion110
     PlutusLedgerApi_Common_ProtocolVersions.MajorProtocolVersion
     PlutusLedgerApi_Common_ProtocolVersions.alonzoPV
     PlutusLedgerApi_Common_ProtocolVersions.conwayPV
     PlutusLedgerApi_Common_ProtocolVersions.valentinePV
     PlutusLedgerApi_Common_ProtocolVersions.vasilPV
*)
