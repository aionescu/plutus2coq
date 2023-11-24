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

Require GHC.Base.
Require GHC.Num.
Require PlutusTx_AssocMap.

(* Converted type declarations: *)

Inductive Metadata : Type :=
  | ApplicationHeadSymbol : GHC.Base.String -> Metadata
  | IgnoredAnnotation : Metadata.

Inductive CoverageMetadata : Type :=
  | MkCoverageMetadata (_metadataSet : list Metadata) : CoverageMetadata.

Inductive CovLoc : Type :=
  | MkCovLoc (_covLocFile : GHC.Base.String) (_covLocStartLine : GHC.Num.Int)
  (_covLocEndLine : GHC.Num.Int) (_covLocStartCol : GHC.Num.Int) (_covLocEndCol
    : GHC.Num.Int)
   : CovLoc.

Inductive CoverageAnnotation : Type :=
  | CoverLocation : CovLoc -> CoverageAnnotation
  | CoverBool : CovLoc -> bool -> CoverageAnnotation.

Inductive CoverageData : Type :=
  | MkCoverageData (_coveredAnnotations : list CoverageAnnotation) : CoverageData.

Inductive CoverageIndex : Type :=
  | MkCoverageIndex (_coverageMetadata
    : PlutusTx_AssocMap.Map CoverageAnnotation CoverageMetadata)
   : CoverageIndex.

Inductive CoverageReport : Type :=
  | MkCoverageReport (_coverageIndex : CoverageIndex) (_coverageData
    : CoverageData)
   : CoverageReport.

Definition _metadataSet (arg_0__ : CoverageMetadata) :=
  let 'MkCoverageMetadata _metadataSet := arg_0__ in
  _metadataSet.

Definition _covLocEndCol (arg_0__ : CovLoc) :=
  let 'MkCovLoc _ _ _ _ _covLocEndCol := arg_0__ in
  _covLocEndCol.

Definition _covLocEndLine (arg_0__ : CovLoc) :=
  let 'MkCovLoc _ _ _covLocEndLine _ _ := arg_0__ in
  _covLocEndLine.

Definition _covLocFile (arg_0__ : CovLoc) :=
  let 'MkCovLoc _covLocFile _ _ _ _ := arg_0__ in
  _covLocFile.

Definition _covLocStartCol (arg_0__ : CovLoc) :=
  let 'MkCovLoc _ _ _ _covLocStartCol _ := arg_0__ in
  _covLocStartCol.

Definition _covLocStartLine (arg_0__ : CovLoc) :=
  let 'MkCovLoc _ _covLocStartLine _ _ _ := arg_0__ in
  _covLocStartLine.

Definition _coveredAnnotations (arg_0__ : CoverageData) :=
  let 'MkCoverageData _coveredAnnotations := arg_0__ in
  _coveredAnnotations.

Definition _coverageMetadata (arg_0__ : CoverageIndex) :=
  let 'MkCoverageIndex _coverageMetadata := arg_0__ in
  _coverageMetadata.

Definition _coverageData (arg_0__ : CoverageReport) :=
  let 'MkCoverageReport _ _coverageData := arg_0__ in
  _coverageData.

Definition _coverageIndex (arg_0__ : CoverageReport) :=
  let 'MkCoverageReport _coverageIndex _ := arg_0__ in
  _coverageIndex.

(* Converted value declarations: *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusTx_Coverage.Pretty__CovLoc' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusTx_Coverage.Pretty__CoverageAnnotation' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusTx_Coverage.Pretty__Metadata' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusTx_Coverage.Pretty__CoverageMetadata' *)

(* Skipping all instances of class `GHC.Base.Semigroup', including
   `PlutusTx_Coverage.Semigroup__CoverageIndex' *)

(* Skipping all instances of class `GHC.Base.Monoid', including
   `PlutusTx_Coverage.Monoid__CoverageIndex' *)

(* Skipping all instances of class `GHC.Base.Semigroup', including
   `PlutusTx_Coverage.Semigroup__CoverageReport' *)

(* Skipping all instances of class `GHC.Base.Monoid', including
   `PlutusTx_Coverage.Monoid__CoverageReport' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusTx_Coverage.Pretty__CoverageReport' *)

(* Skipping definition `PlutusTx_Coverage.covLocStartLine' *)

(* Skipping definition `PlutusTx_Coverage.covLocStartCol' *)

(* Skipping definition `PlutusTx_Coverage.covLocFile' *)

(* Skipping definition `PlutusTx_Coverage.covLocEndLine' *)

(* Skipping definition `PlutusTx_Coverage.covLocEndCol' *)

(* Skipping definition `PlutusTx_Coverage.metadataSet' *)

(* Skipping definition `PlutusTx_Coverage.coverageMetadata' *)

(* Skipping definition `PlutusTx_Coverage.coverageAnnotations' *)

(* Skipping definition `PlutusTx_Coverage.ignoredAnnotations' *)

(* Skipping definition `PlutusTx_Coverage.addLocationToCoverageIndex' *)

(* Skipping definition `PlutusTx_Coverage.addBoolCaseToCoverageIndex' *)

Axiom addCoverageMetadata : CoverageAnnotation ->
                            Metadata -> CoverageIndex -> CoverageIndex.

Axiom boolCaseCoverageAnn : CovLoc -> bool -> CoverageAnnotation.

(* Skipping definition `PlutusTx_Coverage.coveredAnnotations' *)

(* Skipping definition `PlutusTx_Coverage.coverageIndex' *)

(* Skipping definition `PlutusTx_Coverage.coverageData' *)

Axiom coverageDataFromLogMsg : GHC.Base.String -> CoverageData.

(* External variables:
     bool list GHC.Base.String GHC.Num.Int PlutusTx_AssocMap.Map
*)
