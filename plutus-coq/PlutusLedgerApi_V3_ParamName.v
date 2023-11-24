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

Require HsToCoq.Err.

(* Converted type declarations: *)

Inductive ParamName : Type :=
  | AddInteger'cpu'arguments'intercept : ParamName
  | AddInteger'cpu'arguments'slope : ParamName
  | AddInteger'memory'arguments'intercept : ParamName
  | AddInteger'memory'arguments'slope : ParamName
  | AppendByteString'cpu'arguments'intercept : ParamName
  | AppendByteString'cpu'arguments'slope : ParamName
  | AppendByteString'memory'arguments'intercept : ParamName
  | AppendByteString'memory'arguments'slope : ParamName
  | AppendString'cpu'arguments'intercept : ParamName
  | AppendString'cpu'arguments'slope : ParamName
  | AppendString'memory'arguments'intercept : ParamName
  | AppendString'memory'arguments'slope : ParamName
  | BData'cpu'arguments : ParamName
  | BData'memory'arguments : ParamName
  | Blake2b_256'cpu'arguments'intercept : ParamName
  | Blake2b_256'cpu'arguments'slope : ParamName
  | Blake2b_256'memory'arguments : ParamName
  | CekApplyCost'exBudgetCPU : ParamName
  | CekApplyCost'exBudgetMemory : ParamName
  | CekBuiltinCost'exBudgetCPU : ParamName
  | CekBuiltinCost'exBudgetMemory : ParamName
  | CekConstCost'exBudgetCPU : ParamName
  | CekConstCost'exBudgetMemory : ParamName
  | CekDelayCost'exBudgetCPU : ParamName
  | CekDelayCost'exBudgetMemory : ParamName
  | CekForceCost'exBudgetCPU : ParamName
  | CekForceCost'exBudgetMemory : ParamName
  | CekLamCost'exBudgetCPU : ParamName
  | CekLamCost'exBudgetMemory : ParamName
  | CekStartupCost'exBudgetCPU : ParamName
  | CekStartupCost'exBudgetMemory : ParamName
  | CekVarCost'exBudgetCPU : ParamName
  | CekVarCost'exBudgetMemory : ParamName
  | ChooseData'cpu'arguments : ParamName
  | ChooseData'memory'arguments : ParamName
  | ChooseList'cpu'arguments : ParamName
  | ChooseList'memory'arguments : ParamName
  | ChooseUnit'cpu'arguments : ParamName
  | ChooseUnit'memory'arguments : ParamName
  | ConsByteString'cpu'arguments'intercept : ParamName
  | ConsByteString'cpu'arguments'slope : ParamName
  | ConsByteString'memory'arguments'intercept : ParamName
  | ConsByteString'memory'arguments'slope : ParamName
  | ConstrData'cpu'arguments : ParamName
  | ConstrData'memory'arguments : ParamName
  | DecodeUtf8'cpu'arguments'intercept : ParamName
  | DecodeUtf8'cpu'arguments'slope : ParamName
  | DecodeUtf8'memory'arguments'intercept : ParamName
  | DecodeUtf8'memory'arguments'slope : ParamName
  | DivideInteger'cpu'arguments'constant : ParamName
  | DivideInteger'cpu'arguments'model'arguments'intercept : ParamName
  | DivideInteger'cpu'arguments'model'arguments'slope : ParamName
  | DivideInteger'memory'arguments'intercept : ParamName
  | DivideInteger'memory'arguments'minimum : ParamName
  | DivideInteger'memory'arguments'slope : ParamName
  | EncodeUtf8'cpu'arguments'intercept : ParamName
  | EncodeUtf8'cpu'arguments'slope : ParamName
  | EncodeUtf8'memory'arguments'intercept : ParamName
  | EncodeUtf8'memory'arguments'slope : ParamName
  | EqualsByteString'cpu'arguments'constant : ParamName
  | EqualsByteString'cpu'arguments'intercept : ParamName
  | EqualsByteString'cpu'arguments'slope : ParamName
  | EqualsByteString'memory'arguments : ParamName
  | EqualsData'cpu'arguments'intercept : ParamName
  | EqualsData'cpu'arguments'slope : ParamName
  | EqualsData'memory'arguments : ParamName
  | EqualsInteger'cpu'arguments'intercept : ParamName
  | EqualsInteger'cpu'arguments'slope : ParamName
  | EqualsInteger'memory'arguments : ParamName
  | EqualsString'cpu'arguments'constant : ParamName
  | EqualsString'cpu'arguments'intercept : ParamName
  | EqualsString'cpu'arguments'slope : ParamName
  | EqualsString'memory'arguments : ParamName
  | FstPair'cpu'arguments : ParamName
  | FstPair'memory'arguments : ParamName
  | HeadList'cpu'arguments : ParamName
  | HeadList'memory'arguments : ParamName
  | IData'cpu'arguments : ParamName
  | IData'memory'arguments : ParamName
  | IfThenElse'cpu'arguments : ParamName
  | IfThenElse'memory'arguments : ParamName
  | IndexByteString'cpu'arguments : ParamName
  | IndexByteString'memory'arguments : ParamName
  | LengthOfByteString'cpu'arguments : ParamName
  | LengthOfByteString'memory'arguments : ParamName
  | LessThanByteString'cpu'arguments'intercept : ParamName
  | LessThanByteString'cpu'arguments'slope : ParamName
  | LessThanByteString'memory'arguments : ParamName
  | LessThanEqualsByteString'cpu'arguments'intercept : ParamName
  | LessThanEqualsByteString'cpu'arguments'slope : ParamName
  | LessThanEqualsByteString'memory'arguments : ParamName
  | LessThanEqualsInteger'cpu'arguments'intercept : ParamName
  | LessThanEqualsInteger'cpu'arguments'slope : ParamName
  | LessThanEqualsInteger'memory'arguments : ParamName
  | LessThanInteger'cpu'arguments'intercept : ParamName
  | LessThanInteger'cpu'arguments'slope : ParamName
  | LessThanInteger'memory'arguments : ParamName
  | ListData'cpu'arguments : ParamName
  | ListData'memory'arguments : ParamName
  | MapData'cpu'arguments : ParamName
  | MapData'memory'arguments : ParamName
  | MkCons'cpu'arguments : ParamName
  | MkCons'memory'arguments : ParamName
  | MkNilData'cpu'arguments : ParamName
  | MkNilData'memory'arguments : ParamName
  | MkNilPairData'cpu'arguments : ParamName
  | MkNilPairData'memory'arguments : ParamName
  | MkPairData'cpu'arguments : ParamName
  | MkPairData'memory'arguments : ParamName
  | ModInteger'cpu'arguments'constant : ParamName
  | ModInteger'cpu'arguments'model'arguments'intercept : ParamName
  | ModInteger'cpu'arguments'model'arguments'slope : ParamName
  | ModInteger'memory'arguments'intercept : ParamName
  | ModInteger'memory'arguments'minimum : ParamName
  | ModInteger'memory'arguments'slope : ParamName
  | MultiplyInteger'cpu'arguments'intercept : ParamName
  | MultiplyInteger'cpu'arguments'slope : ParamName
  | MultiplyInteger'memory'arguments'intercept : ParamName
  | MultiplyInteger'memory'arguments'slope : ParamName
  | NullList'cpu'arguments : ParamName
  | NullList'memory'arguments : ParamName
  | QuotientInteger'cpu'arguments'constant : ParamName
  | QuotientInteger'cpu'arguments'model'arguments'intercept : ParamName
  | QuotientInteger'cpu'arguments'model'arguments'slope : ParamName
  | QuotientInteger'memory'arguments'intercept : ParamName
  | QuotientInteger'memory'arguments'minimum : ParamName
  | QuotientInteger'memory'arguments'slope : ParamName
  | RemainderInteger'cpu'arguments'constant : ParamName
  | RemainderInteger'cpu'arguments'model'arguments'intercept : ParamName
  | RemainderInteger'cpu'arguments'model'arguments'slope : ParamName
  | RemainderInteger'memory'arguments'intercept : ParamName
  | RemainderInteger'memory'arguments'minimum : ParamName
  | RemainderInteger'memory'arguments'slope : ParamName
  | SerialiseData'cpu'arguments'intercept : ParamName
  | SerialiseData'cpu'arguments'slope : ParamName
  | SerialiseData'memory'arguments'intercept : ParamName
  | SerialiseData'memory'arguments'slope : ParamName
  | Sha2_256'cpu'arguments'intercept : ParamName
  | Sha2_256'cpu'arguments'slope : ParamName
  | Sha2_256'memory'arguments : ParamName
  | Sha3_256'cpu'arguments'intercept : ParamName
  | Sha3_256'cpu'arguments'slope : ParamName
  | Sha3_256'memory'arguments : ParamName
  | SliceByteString'cpu'arguments'intercept : ParamName
  | SliceByteString'cpu'arguments'slope : ParamName
  | SliceByteString'memory'arguments'intercept : ParamName
  | SliceByteString'memory'arguments'slope : ParamName
  | SndPair'cpu'arguments : ParamName
  | SndPair'memory'arguments : ParamName
  | SubtractInteger'cpu'arguments'intercept : ParamName
  | SubtractInteger'cpu'arguments'slope : ParamName
  | SubtractInteger'memory'arguments'intercept : ParamName
  | SubtractInteger'memory'arguments'slope : ParamName
  | TailList'cpu'arguments : ParamName
  | TailList'memory'arguments : ParamName
  | Trace'cpu'arguments : ParamName
  | Trace'memory'arguments : ParamName
  | UnBData'cpu'arguments : ParamName
  | UnBData'memory'arguments : ParamName
  | UnConstrData'cpu'arguments : ParamName
  | UnConstrData'memory'arguments : ParamName
  | UnIData'cpu'arguments : ParamName
  | UnIData'memory'arguments : ParamName
  | UnListData'cpu'arguments : ParamName
  | UnListData'memory'arguments : ParamName
  | UnMapData'cpu'arguments : ParamName
  | UnMapData'memory'arguments : ParamName
  | VerifyEcdsaSecp256k1Signature'cpu'arguments : ParamName
  | VerifyEcdsaSecp256k1Signature'memory'arguments : ParamName
  | VerifyEd25519Signature'cpu'arguments'intercept : ParamName
  | VerifyEd25519Signature'cpu'arguments'slope : ParamName
  | VerifyEd25519Signature'memory'arguments : ParamName
  | VerifySchnorrSecp256k1Signature'cpu'arguments'intercept : ParamName
  | VerifySchnorrSecp256k1Signature'cpu'arguments'slope : ParamName
  | VerifySchnorrSecp256k1Signature'memory'arguments : ParamName
  | CekConstrCost'exBudgetCPU : ParamName
  | CekConstrCost'exBudgetMemory : ParamName
  | CekCaseCost'exBudgetCPU : ParamName
  | CekCaseCost'exBudgetMemory : ParamName
  | Bls12_381_G1_add'cpu'arguments : ParamName
  | Bls12_381_G1_add'memory'arguments : ParamName
  | Bls12_381_G1_compress'cpu'arguments : ParamName
  | Bls12_381_G1_compress'memory'arguments : ParamName
  | Bls12_381_G1_equal'cpu'arguments : ParamName
  | Bls12_381_G1_equal'memory'arguments : ParamName
  | Bls12_381_G1_hashToGroup'cpu'arguments'intercept : ParamName
  | Bls12_381_G1_hashToGroup'cpu'arguments'slope : ParamName
  | Bls12_381_G1_hashToGroup'memory'arguments : ParamName
  | Bls12_381_G1_neg'cpu'arguments : ParamName
  | Bls12_381_G1_neg'memory'arguments : ParamName
  | Bls12_381_G1_scalarMul'cpu'arguments'intercept : ParamName
  | Bls12_381_G1_scalarMul'cpu'arguments'slope : ParamName
  | Bls12_381_G1_scalarMul'memory'arguments : ParamName
  | Bls12_381_G1_uncompress'cpu'arguments : ParamName
  | Bls12_381_G1_uncompress'memory'arguments : ParamName
  | Bls12_381_G2_add'cpu'arguments : ParamName
  | Bls12_381_G2_add'memory'arguments : ParamName
  | Bls12_381_G2_compress'cpu'arguments : ParamName
  | Bls12_381_G2_compress'memory'arguments : ParamName
  | Bls12_381_G2_equal'cpu'arguments : ParamName
  | Bls12_381_G2_equal'memory'arguments : ParamName
  | Bls12_381_G2_hashToGroup'cpu'arguments'intercept : ParamName
  | Bls12_381_G2_hashToGroup'cpu'arguments'slope : ParamName
  | Bls12_381_G2_hashToGroup'memory'arguments : ParamName
  | Bls12_381_G2_neg'cpu'arguments : ParamName
  | Bls12_381_G2_neg'memory'arguments : ParamName
  | Bls12_381_G2_scalarMul'cpu'arguments'intercept : ParamName
  | Bls12_381_G2_scalarMul'cpu'arguments'slope : ParamName
  | Bls12_381_G2_scalarMul'memory'arguments : ParamName
  | Bls12_381_G2_uncompress'cpu'arguments : ParamName
  | Bls12_381_G2_uncompress'memory'arguments : ParamName
  | Bls12_381_finalVerify'cpu'arguments : ParamName
  | Bls12_381_finalVerify'memory'arguments : ParamName
  | Bls12_381_millerLoop'cpu'arguments : ParamName
  | Bls12_381_millerLoop'memory'arguments : ParamName
  | Bls12_381_mulMlResult'cpu'arguments : ParamName
  | Bls12_381_mulMlResult'memory'arguments : ParamName
  | Keccak_256'cpu'arguments'intercept : ParamName
  | Keccak_256'cpu'arguments'slope : ParamName
  | Keccak_256'memory'arguments : ParamName
  | Blake2b_224'cpu'arguments'intercept : ParamName
  | Blake2b_224'cpu'arguments'slope : ParamName
  | Blake2b_224'memory'arguments : ParamName.

Instance Default__ParamName : HsToCoq.Err.Default ParamName :=
  HsToCoq.Err.Build_Default _ AddInteger'cpu'arguments'intercept.

(* No value declarations to convert. *)

(* External variables:
     HsToCoq.Err.Build_Default HsToCoq.Err.Default
*)
