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

Require Control.Lens.At.
Require Control.Lens.Getter.
Require Control.Lens.Iso.
Require Control.Lens.Prism.
Require Control.Lens.Setter.
Require Control.Lens.Type.
Require Control.Monad.Writer.Class.
Require Data.Foldable.
Require Data.Function.
Require Data.Map.Internal.
Require Data.Set.Internal.
Require GHC.Base.
Require GHC.Num.
Require HsToCoq.Err.
Require Text.Read.
Import Control.Lens.Setter.Notations.
Import Data.Function.Notations.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Metadata : Type :=
  | ApplicationHeadSymbol : GHC.Base.String -> Metadata
  | IgnoredAnnotation : Metadata.

Inductive CoverageMetadata : Type :=
  | CoverageMetadata (_metadataSet : Data.Set.Internal.Set_ Metadata)
   : CoverageMetadata.

Inductive CovLoc : Type :=
  | CovLoc (_covLocFile : GHC.Base.String) (_covLocStartLine : GHC.Num.Int)
  (_covLocEndLine : GHC.Num.Int) (_covLocStartCol : GHC.Num.Int) (_covLocEndCol
    : GHC.Num.Int)
   : CovLoc.

Inductive CoverageAnnotation : Type :=
  | CoverLocation : CovLoc -> CoverageAnnotation
  | CoverBool : CovLoc -> bool -> CoverageAnnotation.

Inductive CoverageData : Type :=
  | CoverageData (_coveredAnnotations : Data.Set.Internal.Set_ CoverageAnnotation)
   : CoverageData.

Inductive CoverageIndex : Type :=
  | CoverageIndex (_coverageMetadata
    : Data.Map.Internal.Map CoverageAnnotation CoverageMetadata)
   : CoverageIndex.

Inductive CoverageReport : Type :=
  | CoverageReport (_coverageIndex : CoverageIndex) (_coverageData : CoverageData)
   : CoverageReport.

Instance Default__Metadata : HsToCoq.Err.Default Metadata :=
  HsToCoq.Err.Build_Default _ IgnoredAnnotation.

Instance Default__CoverageMetadata : HsToCoq.Err.Default CoverageMetadata :=
  HsToCoq.Err.Build_Default _ (CoverageMetadata HsToCoq.Err.default).

Instance Default__CovLoc : HsToCoq.Err.Default CovLoc :=
  HsToCoq.Err.Build_Default _ (CovLoc HsToCoq.Err.default HsToCoq.Err.default
                             HsToCoq.Err.default HsToCoq.Err.default HsToCoq.Err.default).

Instance Default__CoverageData : HsToCoq.Err.Default CoverageData :=
  HsToCoq.Err.Build_Default _ (CoverageData HsToCoq.Err.default).

Instance Default__CoverageIndex : HsToCoq.Err.Default CoverageIndex :=
  HsToCoq.Err.Build_Default _ (CoverageIndex HsToCoq.Err.default).

Instance Default__CoverageReport : HsToCoq.Err.Default CoverageReport :=
  HsToCoq.Err.Build_Default _ (CoverageReport HsToCoq.Err.default
                             HsToCoq.Err.default).

Definition _metadataSet (arg_0__ : CoverageMetadata) :=
  let 'CoverageMetadata _metadataSet := arg_0__ in
  _metadataSet.

Definition _covLocEndCol (arg_0__ : CovLoc) :=
  let 'CovLoc _ _ _ _ _covLocEndCol := arg_0__ in
  _covLocEndCol.

Definition _covLocEndLine (arg_0__ : CovLoc) :=
  let 'CovLoc _ _ _covLocEndLine _ _ := arg_0__ in
  _covLocEndLine.

Definition _covLocFile (arg_0__ : CovLoc) :=
  let 'CovLoc _covLocFile _ _ _ _ := arg_0__ in
  _covLocFile.

Definition _covLocStartCol (arg_0__ : CovLoc) :=
  let 'CovLoc _ _ _ _covLocStartCol _ := arg_0__ in
  _covLocStartCol.

Definition _covLocStartLine (arg_0__ : CovLoc) :=
  let 'CovLoc _ _covLocStartLine _ _ _ := arg_0__ in
  _covLocStartLine.

Definition _coveredAnnotations (arg_0__ : CoverageData) :=
  let 'CoverageData _coveredAnnotations := arg_0__ in
  _coveredAnnotations.

Definition _coverageMetadata (arg_0__ : CoverageIndex) :=
  let 'CoverageIndex _coverageMetadata := arg_0__ in
  _coverageMetadata.

Definition _coverageData (arg_0__ : CoverageReport) :=
  let 'CoverageReport _ _coverageData := arg_0__ in
  _coverageData.

Definition _coverageIndex (arg_0__ : CoverageReport) :=
  let 'CoverageReport _coverageIndex _ := arg_0__ in
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

Definition covLocStartLine : Control.Lens.Type.Lens' CovLoc GHC.Num.Int :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, CovLoc x1 x2 x3 x4 x5 =>
        (GHC.Base.fmap (fun y1 => ((((CovLoc x1) y1) x3) x4) x5)) (f x2)
    end.

Definition covLocStartCol : Control.Lens.Type.Lens' CovLoc GHC.Num.Int :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, CovLoc x1 x2 x3 x4 x5 =>
        (GHC.Base.fmap (fun y1 => ((((CovLoc x1) x2) x3) y1) x5)) (f x4)
    end.

Definition covLocFile : Control.Lens.Type.Lens' CovLoc GHC.Base.String :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, CovLoc x1 x2 x3 x4 x5 =>
        (GHC.Base.fmap (fun y1 => ((((CovLoc y1) x2) x3) x4) x5)) (f x1)
    end.

Definition covLocEndLine : Control.Lens.Type.Lens' CovLoc GHC.Num.Int :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, CovLoc x1 x2 x3 x4 x5 =>
        (GHC.Base.fmap (fun y1 => ((((CovLoc x1) x2) y1) x4) x5)) (f x3)
    end.

Definition covLocEndCol : Control.Lens.Type.Lens' CovLoc GHC.Num.Int :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, CovLoc x1 x2 x3 x4 x5 =>
        (GHC.Base.fmap (fun y1 => ((((CovLoc x1) x2) x3) x4) y1)) (f x5)
    end.

Definition metadataSet
   : Control.Lens.Type.Iso' CoverageMetadata (Data.Set.Internal.Set_ Metadata) :=
  (Control.Lens.Iso.iso (fun '(CoverageMetadata x) => x)) CoverageMetadata.

Definition coverageMetadata
   : Control.Lens.Type.Iso' CoverageIndex (Data.Map.Internal.Map
                             CoverageAnnotation CoverageMetadata) :=
  (Control.Lens.Iso.iso (fun '(CoverageIndex x) => x)) CoverageIndex.

Definition coverageAnnotations
   : Control.Lens.Type.Getter CoverageIndex (Data.Set.Internal.Set_
                               CoverageAnnotation) :=
  coverageMetadata GHC.Base.∘ Control.Lens.Getter.to Data.Map.Internal.keysSet.

Definition ignoredAnnotations
   : Control.Lens.Type.Getter CoverageIndex (Data.Set.Internal.Set_
                               CoverageAnnotation) :=
  coverageMetadata GHC.Base.∘
  Control.Lens.Getter.to (Data.Map.Internal.keysSet GHC.Base.∘
                          Data.Map.Internal.filter (Data.Set.Internal.member IgnoredAnnotation GHC.Base.∘
                                                    _metadataSet)).

Definition addLocationToCoverageIndex {m : Type -> Type}
  `{Control.Monad.Writer.Class.MonadWriter CoverageIndex m}
   : CovLoc -> m CoverageAnnotation :=
  fun src =>
    let ann := CoverLocation src in
    Control.Monad.Writer.Class.tell (CoverageIndex (Data.Map.Internal.singleton ann
                                                                                GHC.Base.mempty)) GHC.Base.>>
    GHC.Base.pure ann.

Definition boolCaseCoverageAnn : CovLoc -> bool -> CoverageAnnotation :=
  fun src b => CoverBool src b.

Definition addBoolCaseToCoverageIndex {m : Type -> Type}
  `{Control.Monad.Writer.Class.MonadWriter CoverageIndex m}
   : CovLoc -> bool -> CoverageMetadata -> m CoverageAnnotation :=
  fun src b meta =>
    let ann := boolCaseCoverageAnn src b in
    Control.Monad.Writer.Class.tell (CoverageIndex (Data.Map.Internal.singleton ann
                                                    meta)) GHC.Base.>>
    GHC.Base.pure ann.

Definition addCoverageMetadata
   : CoverageAnnotation -> Metadata -> CoverageIndex -> CoverageIndex :=
  fun ann meta idx =>
    idx Data.Function.&
    ((coverageMetadata GHC.Base.∘
      (Control.Lens.At.at ann GHC.Base.∘
       (Control.Lens.Prism._Just GHC.Base.∘ metadataSet))) Control.Lens.Setter.%~
     Data.Set.Internal.insert meta).

Definition coveredAnnotations
   : Control.Lens.Type.Iso' CoverageData (Data.Set.Internal.Set_
                             CoverageAnnotation) :=
  (Control.Lens.Iso.iso (fun '(CoverageData x) => x)) CoverageData.

Definition coverageIndex
   : Control.Lens.Type.Lens' CoverageReport CoverageIndex :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, CoverageReport x1 x2 =>
        (GHC.Base.fmap (fun y1 => (CoverageReport y1) x2)) (f x1)
    end.

Definition coverageData : Control.Lens.Type.Lens' CoverageReport CoverageData :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, CoverageReport x1 x2 =>
        (GHC.Base.fmap (fun y1 => (CoverageReport x1) y1)) (f x2)
    end.

Definition coverageDataFromLogMsg : GHC.Base.String -> CoverageData :=
  Data.Foldable.foldMap (CoverageData GHC.Base.∘ Data.Set.Internal.singleton)
  GHC.Base.∘
  Text.Read.readMaybe.

(* External variables:
     Type bool Control.Lens.At.at Control.Lens.Getter.to Control.Lens.Iso.iso
     Control.Lens.Prism._Just Control.Lens.Setter.op_zvz7eU__
     Control.Lens.Type.Getter Control.Lens.Type.Iso' Control.Lens.Type.Lens'
     Control.Monad.Writer.Class.MonadWriter Control.Monad.Writer.Class.tell
     Data.Foldable.foldMap Data.Function.op_za__ Data.Map.Internal.Map
     Data.Map.Internal.filter Data.Map.Internal.keysSet Data.Map.Internal.singleton
     Data.Set.Internal.Set_ Data.Set.Internal.insert Data.Set.Internal.member
     Data.Set.Internal.singleton GHC.Base.String GHC.Base.fmap GHC.Base.mempty
     GHC.Base.op_z2218U__ GHC.Base.op_zgzg__ GHC.Base.pure GHC.Num.Int
     HsToCoq.Err.Build_Default HsToCoq.Err.Default HsToCoq.Err.default
     Text.Read.readMaybe
*)
