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

Require Control.Monad.Reader.Class.
Require Control.Monad.Trans.Except.
Require Control.Monad.Trans.Reader.
Require Control.Monad.Trans.State.Lazy.
Require Data.Map.Internal.
Require Data.Set.Internal.
Require GHC.Num.
Require HsToCoq.Err.
Require Language.Haskell.TH.Datatype.
Require Language.Haskell.TH.Lib.Internal.
Require Language.Haskell.TH.Syntax.
Require PlutusCore.Core.Type.
Require PlutusCore.Default.Universe.
Require PlutusCore.Name.
Require PlutusIR.Core.Type.
Require PlutusIR.MkPir.
Require PlutusTx_Lift_Class.
Require String.

(* Converted type declarations: *)

Definition THLocalVars :=
  (Data.Set.Internal.Set_ Language.Haskell.TH.Syntax.Name)%type.

Definition LocalVars uni :=
  (Data.Map.Internal.Map Language.Haskell.TH.Syntax.Name
   (PlutusCore.Core.Type.Type_ PlutusCore.Name.TyName uni unit))%type.

Definition RTCompileScope uni fun_ :=
  (Control.Monad.Trans.Reader.ReaderT (LocalVars uni)
   (PlutusTx_Lift_Class.RTCompile uni fun_))%type.

Inductive LiftError : Type :=
  | UnsupportedLiftKind : Language.Haskell.TH.Syntax.Kind -> LiftError
  | UnsupportedLiftType : Language.Haskell.TH.Syntax.Type_ -> LiftError
  | UserLiftError : String.string -> LiftError
  | LiftMissingDataCons : Language.Haskell.TH.Syntax.Name -> LiftError
  | LiftMissingVar : Language.Haskell.TH.Syntax.Name -> LiftError.

Inductive Dep : Type :=
  | TypeableDep : Language.Haskell.TH.Syntax.Type_ -> Dep
  | LiftDep : Language.Haskell.TH.Syntax.Type_ -> Dep.

Definition Deps :=
  (Data.Set.Internal.Set_ Dep)%type.

Definition THCompile :=
  (Control.Monad.Trans.State.Lazy.StateT Deps (Control.Monad.Trans.Reader.ReaderT
                                               THLocalVars (Control.Monad.Trans.Except.ExceptT LiftError
                                                            Language.Haskell.TH.Syntax.Q)))%type.

Inductive CompileTypeScope : Type :=
  | CompileTypeScope (unCompileTypeScope
    : forall {fun_},
      RTCompileScope PlutusCore.Default.Universe.DefaultUni fun_
      (PlutusCore.Core.Type.Type_ PlutusCore.Name.TyName
       PlutusCore.Default.Universe.DefaultUni unit))
   : CompileTypeScope.

Inductive CompileType : Type :=
  | CompileType (unCompileType
    : forall {fun_},
      PlutusTx_Lift_Class.RTCompile PlutusCore.Default.Universe.DefaultUni fun_
      (PlutusCore.Core.Type.Type_ PlutusCore.Name.TyName
       PlutusCore.Default.Universe.DefaultUni unit))
   : CompileType.

Inductive CompileTerm : Type :=
  | CompileTerm (unCompileTerm
    : forall {fun_},
      PlutusTx_Lift_Class.RTCompile PlutusCore.Default.Universe.DefaultUni fun_
      (PlutusIR.Core.Type.Term PlutusCore.Name.TyName PlutusCore.Name.Name
       PlutusCore.Default.Universe.DefaultUni fun_ unit))
   : CompileTerm.

Inductive CompileDeclFun : Type :=
  | CompileDeclFun (unCompileDeclFun
    : forall {fun_},
      PlutusCore.Core.Type.Type_ PlutusCore.Name.TyName
      PlutusCore.Default.Universe.DefaultUni unit ->
      RTCompileScope PlutusCore.Default.Universe.DefaultUni fun_
      (PlutusCore.Core.Type.VarDecl PlutusCore.Name.TyName PlutusCore.Name.Name
       PlutusCore.Default.Universe.DefaultUni unit))
   : CompileDeclFun.

Instance Default__CompileTypeScope : HsToCoq.Err.Default CompileTypeScope :=
  HsToCoq.Err.Build_Default _ (CompileTypeScope HsToCoq.Err.default).

Instance Default__CompileType : HsToCoq.Err.Default CompileType :=
  HsToCoq.Err.Build_Default _ (CompileType HsToCoq.Err.default).

Instance Default__CompileTerm : HsToCoq.Err.Default CompileTerm :=
  HsToCoq.Err.Build_Default _ (CompileTerm HsToCoq.Err.default).

Instance Default__CompileDeclFun : HsToCoq.Err.Default CompileDeclFun :=
  HsToCoq.Err.Build_Default _ (CompileDeclFun HsToCoq.Err.default).

Definition unCompileTypeScope (arg_0__ : CompileTypeScope) :=
  let 'CompileTypeScope unCompileTypeScope := arg_0__ in
  unCompileTypeScope.

Definition unCompileType (arg_0__ : CompileType) :=
  let 'CompileType unCompileType := arg_0__ in
  unCompileType.

Definition unCompileTerm (arg_0__ : CompileTerm) :=
  let 'CompileTerm unCompileTerm := arg_0__ in
  unCompileTerm.

Definition unCompileDeclFun (arg_0__ : CompileDeclFun) :=
  let 'CompileDeclFun unCompileDeclFun := arg_0__ in
  unCompileDeclFun.

(* Converted value declarations: *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusTx_Lift_TH.Pretty__LiftError' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `PlutusTx_Lift_TH.Show__LiftError' *)

Axiom withTyVars : forall {uni} {m} {a},
                   forall `{(Control.Monad.Reader.Class.MonadReader (LocalVars uni) m)},
                   list (Language.Haskell.TH.Syntax.Name *
                         PlutusCore.Core.Type.TyVarDecl PlutusCore.Name.TyName unit)%type ->
                   m a -> m a.

Axiom thWithTyVars : forall {m} {a},
                     forall `{(Control.Monad.Reader.Class.MonadReader THLocalVars m)},
                     list Language.Haskell.TH.Syntax.Name -> m a -> m a.

Axiom getTyConDeps : Deps ->
                     Data.Set.Internal.Set_ Language.Haskell.TH.Syntax.Name.

Axiom addTypeableDep : Language.Haskell.TH.Syntax.Type_ -> THCompile unit.

Axiom addLiftDep : Language.Haskell.TH.Syntax.Type_ -> THCompile unit.

Axiom typeablePir : Language.Haskell.TH.Syntax.Type_ ->
                    Language.Haskell.TH.Syntax.Type_ -> Language.Haskell.TH.Syntax.Type_.

Axiom liftPir : Language.Haskell.TH.Syntax.Type_ ->
                Language.Haskell.TH.Syntax.Type_ -> Language.Haskell.TH.Syntax.Type_.

Axiom toConstraint : Language.Haskell.TH.Syntax.Type_ ->
                     Dep -> Language.Haskell.TH.Syntax.Pred.

Axiom isClosedConstraint : Language.Haskell.TH.Syntax.Pred -> bool.

Axiom normalizeAndResolve : Language.Haskell.TH.Syntax.Type_ ->
                            THCompile Language.Haskell.TH.Syntax.Type_.

Axiom sortedCons : Language.Haskell.TH.Datatype.DatatypeInfo ->
                   list Language.Haskell.TH.Datatype.ConstructorInfo.

Axiom tvNameAndKind : Language.Haskell.TH.Syntax.TyVarBndr ->
                      THCompile (Language.Haskell.TH.Syntax.Name *
                                 PlutusCore.Core.Type.Kind unit)%type.

Axiom compileKind : Language.Haskell.TH.Syntax.Kind ->
                    THCompile (PlutusCore.Core.Type.Kind unit).

Axiom compileType : Language.Haskell.TH.Syntax.Type_ ->
                    THCompile (Language.Haskell.TH.Lib.Internal.TExpQ CompileTypeScope).

Axiom compileTypeableType : Language.Haskell.TH.Syntax.Type_ ->
                            Language.Haskell.TH.Syntax.Name ->
                            THCompile (Language.Haskell.TH.Lib.Internal.TExpQ CompileTypeScope).

Axiom recordAlias' : forall {fun_},
                     Language.Haskell.TH.Syntax.Name ->
                     RTCompileScope PlutusCore.Default.Universe.DefaultUni fun_ unit.

Axiom defineDatatype' : forall {fun_},
                        Language.Haskell.TH.Syntax.Name ->
                        PlutusIR.MkPir.DatatypeDef PlutusCore.Name.TyName PlutusCore.Name.Name
                        PlutusCore.Default.Universe.DefaultUni unit ->
                        Data.Set.Internal.Set_ Language.Haskell.TH.Syntax.Name ->
                        RTCompileScope PlutusCore.Default.Universe.DefaultUni fun_ unit.

Axiom compileTypeRep : Language.Haskell.TH.Datatype.DatatypeInfo ->
                       THCompile (Language.Haskell.TH.Lib.Internal.TExpQ CompileType).

Axiom compileConstructorDecl : Language.Haskell.TH.Datatype.ConstructorInfo ->
                               THCompile (Language.Haskell.TH.Lib.Internal.TExpQ CompileDeclFun).

Axiom makeTypeable : Language.Haskell.TH.Syntax.Type_ ->
                     Language.Haskell.TH.Syntax.Name ->
                     Language.Haskell.TH.Syntax.Q (list Language.Haskell.TH.Syntax.Dec).

Axiom compileLift : Language.Haskell.TH.Datatype.DatatypeInfo ->
                    THCompile (list (Language.Haskell.TH.Syntax.Q
                                     Language.Haskell.TH.Syntax.Clause)).

Axiom compileConstructorClause : Language.Haskell.TH.Datatype.DatatypeInfo ->
                                 GHC.Num.Int ->
                                 Language.Haskell.TH.Datatype.ConstructorInfo ->
                                 THCompile (Language.Haskell.TH.Syntax.Q Language.Haskell.TH.Syntax.Clause).

Axiom makeLift : Language.Haskell.TH.Syntax.Name ->
                 Language.Haskell.TH.Syntax.Q (list Language.Haskell.TH.Syntax.Dec).

Axiom runTHCompile : forall {a},
                     THCompile a -> Language.Haskell.TH.Syntax.Q (a * Deps)%type.

(* External variables:
     bool list op_zt__ unit Control.Monad.Reader.Class.MonadReader
     Control.Monad.Trans.Except.ExceptT Control.Monad.Trans.Reader.ReaderT
     Control.Monad.Trans.State.Lazy.StateT Data.Map.Internal.Map
     Data.Set.Internal.Set_ GHC.Num.Int HsToCoq.Err.Build_Default HsToCoq.Err.Default
     HsToCoq.Err.default Language.Haskell.TH.Datatype.ConstructorInfo
     Language.Haskell.TH.Datatype.DatatypeInfo Language.Haskell.TH.Lib.Internal.TExpQ
     Language.Haskell.TH.Syntax.Clause Language.Haskell.TH.Syntax.Dec
     Language.Haskell.TH.Syntax.Kind Language.Haskell.TH.Syntax.Name
     Language.Haskell.TH.Syntax.Pred Language.Haskell.TH.Syntax.Q
     Language.Haskell.TH.Syntax.TyVarBndr Language.Haskell.TH.Syntax.Type_
     PlutusCore.Core.Type.Kind PlutusCore.Core.Type.TyVarDecl
     PlutusCore.Core.Type.Type_ PlutusCore.Core.Type.VarDecl
     PlutusCore.Default.Universe.DefaultUni PlutusCore.Name.Name
     PlutusCore.Name.TyName PlutusIR.Core.Type.Term PlutusIR.MkPir.DatatypeDef
     PlutusTx_Lift_Class.RTCompile String.string
*)
