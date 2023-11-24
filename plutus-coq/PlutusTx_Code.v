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
Require Data.Either.
Require Flat.Class.
Require Flat.Decoder.Types.
Require GHC.Base.
Require PlutusCore.Annotation.
Require PlutusCore.DeBruijn.Internal.
Require PlutusCore.Default.Builtins.
Require PlutusCore.Default.Universe.
Require PlutusCore.Name.
Require PlutusCore.Pretty.PrettyConst.
Require PlutusIR.Core.Type.
Require PlutusTx_Coverage.
Require Prettyprinter.Internal.
Require String.
Require Text.Fixity.
Require Text.PrettyBy.Internal.
Require Universe.Core.
Require UntypedPlutusCore.Core.Type.

(* Converted type declarations: *)

Inductive ImpossibleDeserialisationFailure : Type :=
  | ImpossibleDeserialisationFailure
   : Flat.Decoder.Types.DecodeException -> ImpossibleDeserialisationFailure.

Inductive CompiledCodeIn uni fun_ a : Type :=
  | SerializedCode
   : String.string ->
     (option String.string) ->
     PlutusTx_Coverage.CoverageIndex -> CompiledCodeIn uni fun_ a
  | DeserializedCode
   : (UntypedPlutusCore.Core.Type.Program
      PlutusCore.DeBruijn.Internal.NamedDeBruijn uni fun_
      PlutusCore.Annotation.SrcSpans) ->
     (option (PlutusIR.Core.Type.Program PlutusCore.Name.TyName PlutusCore.Name.Name
              uni fun_ PlutusCore.Annotation.SrcSpans)) ->
     PlutusTx_Coverage.CoverageIndex -> CompiledCodeIn uni fun_ a.

Definition CompiledCode :=
  (CompiledCodeIn PlutusCore.Default.Universe.DefaultUni
   PlutusCore.Default.Builtins.DefaultFun)%type.

Arguments SerializedCode {_} {_} {_} _ _ _.

Arguments DeserializedCode {_} {_} {_} _ _ _.

(* Converted value declarations: *)

(* Skipping all instances of class `GHC.Show.Show', including
   `PlutusTx_Code.Show__ImpossibleDeserialisationFailure' *)

Axiom applyCode : forall {uni : GHC.Types.Type_ -> Type},
                  forall {fun_ : Type},
                  forall {a : Type},
                  forall {b : Type},
                  forall `{Universe.Core.Closed uni},
                  forall `{Universe.Core.Everywhere uni Flat.Class.Flat},
                  forall `{Flat.Class.Flat fun_},
                  forall `{Prettyprinter.Internal.Pretty fun_},
                  forall `{Universe.Core.Everywhere uni
                                                    PlutusCore.Pretty.PrettyConst.PrettyConst},
                  forall `{Text.PrettyBy.Internal.PrettyBy Text.Fixity.RenderContext
                                                           (Universe.Core.SomeTypeIn uni)},
                  CompiledCodeIn uni fun_ (a -> b) ->
                  CompiledCodeIn uni fun_ a ->
                  Data.Either.Either GHC.Base.String (CompiledCodeIn uni fun_ b).

Axiom unsafeApplyCode : forall {uni : GHC.Types.Type_ -> Type},
                        forall {fun_ : Type},
                        forall {a : Type},
                        forall {b : Type},
                        forall `{Universe.Core.Closed uni},
                        forall `{Universe.Core.Everywhere uni Flat.Class.Flat},
                        forall `{Flat.Class.Flat fun_},
                        forall `{Prettyprinter.Internal.Pretty fun_},
                        forall `{Universe.Core.Everywhere uni
                                                          PlutusCore.Pretty.PrettyConst.PrettyConst},
                        forall `{Text.PrettyBy.Internal.PrettyBy Text.Fixity.RenderContext
                                                                 (Universe.Core.SomeTypeIn uni)},
                        CompiledCodeIn uni fun_ (a -> b) ->
                        CompiledCodeIn uni fun_ a -> CompiledCodeIn uni fun_ b.

Axiom sizePlc : forall {uni : GHC.Types.Type_ -> Type},
                forall {fun_ : Type},
                forall {a : Type},
                forall `{Universe.Core.Closed uni},
                forall `{Universe.Core.Everywhere uni Flat.Class.Flat},
                forall `{Flat.Class.Flat fun_}, CompiledCodeIn uni fun_ a -> BinNums.Z.

Axiom getPlc : forall {uni : GHC.Types.Type_ -> Type},
               forall {fun_ : Type},
               forall {a : Type},
               forall `{Universe.Core.Closed uni},
               forall `{Universe.Core.Everywhere uni Flat.Class.Flat},
               forall `{Flat.Class.Flat fun_},
               CompiledCodeIn uni fun_ a ->
               UntypedPlutusCore.Core.Type.Program PlutusCore.DeBruijn.Internal.NamedDeBruijn
                                                   uni fun_ PlutusCore.Annotation.SrcSpans.

Axiom getPlcNoAnn : forall {uni : GHC.Types.Type_ -> Type},
                    forall {fun_ : Type},
                    forall {a : Type},
                    forall `{Universe.Core.Closed uni},
                    forall `{Universe.Core.Everywhere uni Flat.Class.Flat},
                    forall `{Flat.Class.Flat fun_},
                    CompiledCodeIn uni fun_ a ->
                    UntypedPlutusCore.Core.Type.Program PlutusCore.DeBruijn.Internal.NamedDeBruijn
                                                        uni fun_ unit.

Axiom getPir : forall {uni : GHC.Types.Type_ -> Type},
               forall {fun_ : Type},
               forall {a : Type},
               forall `{Universe.Core.Closed uni},
               forall `{Universe.Core.Everywhere uni Flat.Class.Flat},
               forall `{Flat.Class.Flat fun_},
               CompiledCodeIn uni fun_ a ->
               option (PlutusIR.Core.Type.Program PlutusCore.Name.TyName PlutusCore.Name.Name
                                                  uni fun_ PlutusCore.Annotation.SrcSpans).

Axiom getPirNoAnn : forall {uni : GHC.Types.Type_ -> Type},
                    forall {fun_ : Type},
                    forall {a : Type},
                    forall `{Universe.Core.Closed uni},
                    forall `{Universe.Core.Everywhere uni Flat.Class.Flat},
                    forall `{Flat.Class.Flat fun_},
                    CompiledCodeIn uni fun_ a ->
                    option (PlutusIR.Core.Type.Program PlutusCore.Name.TyName PlutusCore.Name.Name
                                                       uni fun_ unit).

Axiom getCovIdx : forall {uni : GHC.Types.Type_ -> GHC.Types.Type_},
                  forall {fun_ : Type},
                  forall {a : Type}, CompiledCodeIn uni fun_ a -> PlutusTx_Coverage.CoverageIndex.

(* External variables:
     Type option unit BinNums.Z Data.Either.Either Flat.Class.Flat
     Flat.Decoder.Types.DecodeException GHC.Base.String GHC.Types.Type_
     PlutusCore.Annotation.SrcSpans PlutusCore.DeBruijn.Internal.NamedDeBruijn
     PlutusCore.Default.Builtins.DefaultFun PlutusCore.Default.Universe.DefaultUni
     PlutusCore.Name.Name PlutusCore.Name.TyName
     PlutusCore.Pretty.PrettyConst.PrettyConst PlutusIR.Core.Type.Program
     PlutusTx_Coverage.CoverageIndex Prettyprinter.Internal.Pretty String.string
     Text.Fixity.RenderContext Text.PrettyBy.Internal.PrettyBy Universe.Core.Closed
     Universe.Core.Everywhere Universe.Core.SomeTypeIn
     UntypedPlutusCore.Core.Type.Program
*)
