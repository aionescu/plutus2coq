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

Require GHC.LanguageExtensions.Type.
Require Language.Haskell.TH.Datatype.
Require Language.Haskell.TH.Lib.Internal.
Require Language.Haskell.TH.Syntax.
Require PlutusCore.Core.Type.
Require PlutusCore.Name.
Require PlutusCore.Quote.
Require String.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Axiom showName : Language.Haskell.TH.Syntax.Name -> String.string.

Axiom normalizeType : Language.Haskell.TH.Syntax.Type_ ->
                      Language.Haskell.TH.Syntax.Type_.

Axiom requireExtension : GHC.LanguageExtensions.Type.Extension ->
                         Language.Haskell.TH.Syntax.Q unit.

Axiom mkTyVarDecl : forall {m : Type -> Type},
                    forall `{PlutusCore.Quote.MonadQuote m},
                    Language.Haskell.TH.Syntax.Name ->
                    PlutusCore.Core.Type.Kind unit ->
                    m (Language.Haskell.TH.Syntax.Name *
                       PlutusCore.Core.Type.TyVarDecl PlutusCore.Name.TyName unit)%type.

Axiom isNewtype : Language.Haskell.TH.Datatype.DatatypeInfo -> bool.

Axiom tyListE : forall {a : Type},
                list (Language.Haskell.TH.Lib.Internal.TExpQ a) ->
                Language.Haskell.TH.Lib.Internal.TExpQ (list a).

(* External variables:
     Type bool list op_zt__ unit GHC.LanguageExtensions.Type.Extension
     Language.Haskell.TH.Datatype.DatatypeInfo Language.Haskell.TH.Lib.Internal.TExpQ
     Language.Haskell.TH.Syntax.Name Language.Haskell.TH.Syntax.Q
     Language.Haskell.TH.Syntax.Type_ PlutusCore.Core.Type.Kind
     PlutusCore.Core.Type.TyVarDecl PlutusCore.Name.TyName
     PlutusCore.Quote.MonadQuote String.string
*)
