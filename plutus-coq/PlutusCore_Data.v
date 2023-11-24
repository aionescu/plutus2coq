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
Require String.

(* Converted type declarations: *)

Inductive Data : Type :=
  | Constr : BinNums.Z -> list Data -> Data
  | Map : list (Data * Data)%type -> Data
  | List : list Data -> Data
  | I : BinNums.Z -> Data
  | B : String.string -> Data.

(* No value declarations to convert. *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusCore_Data.Pretty__Data' *)

(* Skipping all instances of class `Codec.Serialise.Class.Serialise', including
   `PlutusCore_Data.Serialise__Data' *)

(* Skipping definition `PlutusCore_Data.encodeData' *)

(* Skipping definition `PlutusCore_Data.encodeInteger' *)

(* Skipping definition `PlutusCore_Data.integerToBytes' *)

(* Skipping definition `PlutusCore_Data.encodeBs' *)

(* Skipping definition `PlutusCore_Data.to64ByteChunks' *)

(* Skipping definition `PlutusCore_Data.decodeData' *)

(* Skipping definition `PlutusCore_Data.decodeBoundedBigInteger' *)

(* Skipping definition `PlutusCore_Data.decodeBoundedBytesIndef' *)

(* Skipping definition `PlutusCore_Data.decodeBoundedBytesIndefLen' *)

(* Skipping definition `PlutusCore_Data.decodeBoundedBytes' *)

(* Skipping definition `PlutusCore_Data.decodeList' *)

(* Skipping definition `PlutusCore_Data.decodeListOf' *)

(* Skipping definition `PlutusCore_Data.decodeMap' *)

(* Skipping definition `PlutusCore_Data.decodeConstr' *)

(* External variables:
     list op_zt__ BinNums.Z String.string
*)
