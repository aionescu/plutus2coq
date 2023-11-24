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

Require Control.Monad.Error.Class.
Require Control.Monad.Trans.Except.
Require Data.Default.Class.
Require Data.GADT.Internal.
Require Data.Proxy.
Require PlutusCore.Builtin.Meaning.
Require PlutusCore.Core.Type.
Require PlutusCore.DeBruijn.Internal.
Require PlutusCore.Default.Builtins.
Require PlutusCore.Default.Universe.
Require PlutusCore.Error.
Require PlutusCore.Name.
Require PlutusCore.Pretty.PrettyConst.
Require PlutusCore.Quote.
Require PlutusCore.TypeCheck.
Require PlutusCore.Version.
Require PlutusIR.Compiler.Provenance.
Require PlutusIR.Core.Type.
Require PlutusIR.Error.
Require PlutusTx_Code.
Require PlutusTx_Lift_Class.
Require Prettyprinter.Internal.
Require UntypedPlutusCore.Core.Type.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Axiom safeLift : forall {uni : GHC.Types.Type_ -> GHC.Types.Type_},
                 forall {a : Type},
                 forall {e : Type},
                 forall {fun_ : Type},
                 forall {m : Type -> Type},
                 forall `{PlutusTx_Lift_Class.Lift uni a},
                 forall `{PlutusCore.Error.AsTypeError e (PlutusIR.Core.Type.Term
                                                        PlutusCore.Name.TyName PlutusCore.Name.Name uni fun_ unit) uni
                                                       fun_ (PlutusIR.Compiler.Provenance.Provenance unit)},
                 forall `{Data.GADT.Internal.GEq GHC.Types.Type_ uni},
                 forall `{PlutusIR.Error.AsTypeErrorExt e uni
                                                        (PlutusIR.Compiler.Provenance.Provenance unit)},
                 forall `{PlutusCore.DeBruijn.Internal.AsFreeVariableError e},
                 forall `{PlutusIR.Error.AsError e uni fun_
                                                 (PlutusIR.Compiler.Provenance.Provenance unit)},
                 forall `{Control.Monad.Error.Class.MonadError e m},
                 forall `{PlutusCore.Quote.MonadQuote m},
                 forall `{PlutusCore.TypeCheck.Typecheckable uni fun_},
                 forall `{PlutusCore.Pretty.PrettyConst.PrettyUni uni},
                 forall `{Prettyprinter.Internal.Pretty fun_},
                 forall `{Data.Default.Class.Default (PlutusCore.Builtin.Meaning.CostingPart uni
                                                                                             fun_)},
                 PlutusCore.Version.Version ->
                 a ->
                 m (PlutusIR.Core.Type.Term PlutusCore.Name.TyName PlutusCore.Name.Name uni fun_
                                            unit *
                    UntypedPlutusCore.Core.Type.Term PlutusCore.DeBruijn.Internal.NamedDeBruijn uni
                                                     fun_ unit)%type.

Axiom safeLiftProgram : forall {uni : GHC.Types.Type_ -> GHC.Types.Type_},
                        forall {a : Type},
                        forall {e : Type},
                        forall {fun_ : Type},
                        forall {m : Type -> Type},
                        forall `{PlutusTx_Lift_Class.Lift uni a},
                        forall `{PlutusCore.Error.AsTypeError e (PlutusIR.Core.Type.Term
                                                               PlutusCore.Name.TyName PlutusCore.Name.Name uni fun_
                                                               unit) uni fun_ (PlutusIR.Compiler.Provenance.Provenance
                                                               unit)},
                        forall `{Data.GADT.Internal.GEq GHC.Types.Type_ uni},
                        forall `{PlutusIR.Error.AsTypeErrorExt e uni
                                                               (PlutusIR.Compiler.Provenance.Provenance unit)},
                        forall `{PlutusCore.DeBruijn.Internal.AsFreeVariableError e},
                        forall `{PlutusIR.Error.AsError e uni fun_
                                                        (PlutusIR.Compiler.Provenance.Provenance unit)},
                        forall `{Control.Monad.Error.Class.MonadError e m},
                        forall `{PlutusCore.Quote.MonadQuote m},
                        forall `{PlutusCore.TypeCheck.Typecheckable uni fun_},
                        forall `{PlutusCore.Pretty.PrettyConst.PrettyUni uni},
                        forall `{Prettyprinter.Internal.Pretty fun_},
                        forall `{Data.Default.Class.Default (PlutusCore.Builtin.Meaning.CostingPart uni
                                                                                                    fun_)},
                        PlutusCore.Version.Version ->
                        a ->
                        m (PlutusIR.Core.Type.Program PlutusCore.Name.TyName PlutusCore.Name.Name uni
                                                      fun_ unit *
                           UntypedPlutusCore.Core.Type.Program PlutusCore.DeBruijn.Internal.NamedDeBruijn
                                                               uni fun_ unit)%type.

Axiom safeLiftCode : forall {uni : GHC.Types.Type_ -> GHC.Types.Type_},
                     forall {a : Type},
                     forall {e : Type},
                     forall {fun_ : Type},
                     forall {m : Type -> Type},
                     forall `{PlutusTx_Lift_Class.Lift uni a},
                     forall `{PlutusCore.Error.AsTypeError e (PlutusIR.Core.Type.Term
                                                            PlutusCore.Name.TyName PlutusCore.Name.Name uni fun_ unit)
                                                           uni fun_ (PlutusIR.Compiler.Provenance.Provenance unit)},
                     forall `{Data.GADT.Internal.GEq GHC.Types.Type_ uni},
                     forall `{PlutusIR.Error.AsTypeErrorExt e uni
                                                            (PlutusIR.Compiler.Provenance.Provenance unit)},
                     forall `{PlutusCore.DeBruijn.Internal.AsFreeVariableError e},
                     forall `{PlutusIR.Error.AsError e uni fun_
                                                     (PlutusIR.Compiler.Provenance.Provenance unit)},
                     forall `{Control.Monad.Error.Class.MonadError e m},
                     forall `{PlutusCore.Quote.MonadQuote m},
                     forall `{PlutusCore.TypeCheck.Typecheckable uni fun_},
                     forall `{PlutusCore.Pretty.PrettyConst.PrettyUni uni},
                     forall `{Prettyprinter.Internal.Pretty fun_},
                     forall `{Data.Default.Class.Default (PlutusCore.Builtin.Meaning.CostingPart uni
                                                                                                 fun_)},
                     PlutusCore.Version.Version -> a -> m (PlutusTx_Code.CompiledCodeIn uni fun_ a).

Axiom unsafely : forall {uni} {fun_} {a},
                 forall `{PlutusCore.Pretty.PrettyConst.ThrowableBuiltins uni fun_},
                 Control.Monad.Trans.Except.ExceptT (PlutusIR.Error.Error uni fun_
                                                     (PlutusIR.Compiler.Provenance.Provenance unit))
                 PlutusCore.Quote.Quote a ->
                 a.

Axiom lift : forall {uni : GHC.Types.Type_ -> GHC.Types.Type_},
             forall {a : Type},
             forall {fun_ : Type},
             forall `{PlutusTx_Lift_Class.Lift uni a},
             forall `{PlutusCore.Pretty.PrettyConst.ThrowableBuiltins uni fun_},
             forall `{PlutusCore.TypeCheck.Typecheckable uni fun_},
             forall `{Data.GADT.Internal.GEq GHC.Types.Type_ uni},
             forall `{Data.Default.Class.Default (PlutusCore.Builtin.Meaning.CostingPart uni
                                                                                         fun_)},
             PlutusCore.Version.Version ->
             a ->
             (PlutusIR.Core.Type.Term PlutusCore.Name.TyName PlutusCore.Name.Name uni fun_
                                      unit *
              UntypedPlutusCore.Core.Type.Term PlutusCore.DeBruijn.Internal.NamedDeBruijn uni
                                               fun_ unit)%type.

Axiom liftProgram : forall {uni : GHC.Types.Type_ -> GHC.Types.Type_},
                    forall {a : Type},
                    forall {fun_ : Type},
                    forall `{PlutusTx_Lift_Class.Lift uni a},
                    forall `{PlutusCore.Pretty.PrettyConst.ThrowableBuiltins uni fun_},
                    forall `{PlutusCore.TypeCheck.Typecheckable uni fun_},
                    forall `{Data.GADT.Internal.GEq GHC.Types.Type_ uni},
                    forall `{Data.Default.Class.Default (PlutusCore.Builtin.Meaning.CostingPart uni
                                                                                                fun_)},
                    PlutusCore.Version.Version ->
                    a ->
                    (PlutusIR.Core.Type.Program PlutusCore.Name.TyName PlutusCore.Name.Name uni fun_
                                                unit *
                     UntypedPlutusCore.Core.Type.Program PlutusCore.DeBruijn.Internal.NamedDeBruijn
                                                         uni fun_ unit)%type.

Axiom liftProgramDef : forall {a : Type},
                       forall `{PlutusTx_Lift_Class.Lift PlutusCore.Default.Universe.DefaultUni a},
                       a ->
                       (PlutusIR.Core.Type.Program PlutusCore.Name.TyName PlutusCore.Name.Name
                                                   PlutusCore.Default.Universe.DefaultUni
                                                   PlutusCore.Default.Builtins.DefaultFun unit *
                        UntypedPlutusCore.Core.Type.Program PlutusCore.DeBruijn.Internal.NamedDeBruijn
                                                            PlutusCore.Default.Universe.DefaultUni
                                                            PlutusCore.Default.Builtins.DefaultFun unit)%type.

Axiom liftCode : forall {uni : GHC.Types.Type_ -> GHC.Types.Type_},
                 forall {a : Type},
                 forall {fun_ : Type},
                 forall `{PlutusTx_Lift_Class.Lift uni a},
                 forall `{Data.GADT.Internal.GEq GHC.Types.Type_ uni},
                 forall `{PlutusCore.Pretty.PrettyConst.ThrowableBuiltins uni fun_},
                 forall `{PlutusCore.TypeCheck.Typecheckable uni fun_},
                 forall `{Data.Default.Class.Default (PlutusCore.Builtin.Meaning.CostingPart uni
                                                                                             fun_)},
                 PlutusCore.Version.Version -> a -> PlutusTx_Code.CompiledCodeIn uni fun_ a.

Axiom liftCodeDef : forall {uni : GHC.Types.Type_ -> GHC.Types.Type_},
                    forall {a : Type},
                    forall {fun_ : Type},
                    forall `{PlutusTx_Lift_Class.Lift uni a},
                    forall `{Data.GADT.Internal.GEq GHC.Types.Type_ uni},
                    forall `{PlutusCore.Pretty.PrettyConst.ThrowableBuiltins uni fun_},
                    forall `{PlutusCore.TypeCheck.Typecheckable uni fun_},
                    forall `{Data.Default.Class.Default (PlutusCore.Builtin.Meaning.CostingPart uni
                                                                                                fun_)},
                    a -> PlutusTx_Code.CompiledCodeIn uni fun_ a.

Axiom typeCheckAgainst : forall {e : Type},
                         forall {a : Type},
                         forall {uni : GHC.Types.Type_ -> GHC.Types.Type_},
                         forall {fun_ : Type},
                         forall {m : Type -> Type},
                         forall `{PlutusTx_Lift_Class.Typeable Type uni a},
                         forall `{PlutusCore.Error.AsTypeError e (PlutusIR.Core.Type.Term
                                                                PlutusCore.Name.TyName PlutusCore.Name.Name uni fun_
                                                                unit) uni fun_ (PlutusIR.Compiler.Provenance.Provenance
                                                                unit)},
                         forall `{PlutusIR.Error.AsTypeErrorExt e uni
                                                                (PlutusIR.Compiler.Provenance.Provenance unit)},
                         forall `{PlutusIR.Error.AsError e uni fun_
                                                         (PlutusIR.Compiler.Provenance.Provenance unit)},
                         forall `{Control.Monad.Error.Class.MonadError e m},
                         forall `{PlutusCore.Quote.MonadQuote m},
                         forall `{Data.GADT.Internal.GEq GHC.Types.Type_ uni},
                         forall `{PlutusCore.TypeCheck.Typecheckable uni fun_},
                         forall `{PlutusCore.Pretty.PrettyConst.PrettyUni uni},
                         forall `{Prettyprinter.Internal.Pretty fun_},
                         forall `{Data.Default.Class.Default (PlutusCore.Builtin.Meaning.CostingPart uni
                                                                                                     fun_)},
                         Data.Proxy.Proxy a ->
                         PlutusCore.Core.Type.Program PlutusCore.Name.TyName PlutusCore.Name.Name uni
                                                      fun_ unit ->
                         m unit.

Axiom typeCode : forall {e : Type},
                 forall {a : Type},
                 forall {uni : GHC.Types.Type_ -> GHC.Types.Type_},
                 forall {fun_ : Type},
                 forall {m : Type -> Type},
                 forall `{PlutusTx_Lift_Class.Typeable Type uni a},
                 forall `{PlutusCore.Error.AsTypeError e (PlutusIR.Core.Type.Term
                                                        PlutusCore.Name.TyName PlutusCore.Name.Name uni fun_ unit) uni
                                                       fun_ (PlutusIR.Compiler.Provenance.Provenance unit)},
                 forall `{PlutusIR.Error.AsTypeErrorExt e uni
                                                        (PlutusIR.Compiler.Provenance.Provenance unit)},
                 forall `{PlutusCore.DeBruijn.Internal.AsFreeVariableError e},
                 forall `{PlutusIR.Error.AsError e uni fun_
                                                 (PlutusIR.Compiler.Provenance.Provenance unit)},
                 forall `{Control.Monad.Error.Class.MonadError e m},
                 forall `{PlutusCore.Quote.MonadQuote m},
                 forall `{Data.GADT.Internal.GEq GHC.Types.Type_ uni},
                 forall `{PlutusCore.TypeCheck.Typecheckable uni fun_},
                 forall `{PlutusCore.Pretty.PrettyConst.PrettyUni uni},
                 forall `{Prettyprinter.Internal.Pretty fun_},
                 forall `{Data.Default.Class.Default (PlutusCore.Builtin.Meaning.CostingPart uni
                                                                                             fun_)},
                 Data.Proxy.Proxy a ->
                 PlutusCore.Core.Type.Program PlutusCore.Name.TyName PlutusCore.Name.Name uni
                                              fun_ unit ->
                 m (PlutusTx_Code.CompiledCodeIn uni fun_ a).

(* External variables:
     Type op_zt__ unit Control.Monad.Error.Class.MonadError
     Control.Monad.Trans.Except.ExceptT Data.Default.Class.Default
     Data.GADT.Internal.GEq Data.Proxy.Proxy GHC.Types.Type_
     PlutusCore.Builtin.Meaning.CostingPart PlutusCore.Core.Type.Program
     PlutusCore.DeBruijn.Internal.AsFreeVariableError
     PlutusCore.DeBruijn.Internal.NamedDeBruijn
     PlutusCore.Default.Builtins.DefaultFun PlutusCore.Default.Universe.DefaultUni
     PlutusCore.Error.AsTypeError PlutusCore.Name.Name PlutusCore.Name.TyName
     PlutusCore.Pretty.PrettyConst.PrettyUni
     PlutusCore.Pretty.PrettyConst.ThrowableBuiltins PlutusCore.Quote.MonadQuote
     PlutusCore.Quote.Quote PlutusCore.TypeCheck.Typecheckable
     PlutusCore.Version.Version PlutusIR.Compiler.Provenance.Provenance
     PlutusIR.Core.Type.Program PlutusIR.Core.Type.Term PlutusIR.Error.AsError
     PlutusIR.Error.AsTypeErrorExt PlutusIR.Error.Error PlutusTx_Code.CompiledCodeIn
     PlutusTx_Lift_Class.Lift PlutusTx_Lift_Class.Typeable
     Prettyprinter.Internal.Pretty UntypedPlutusCore.Core.Type.Program
     UntypedPlutusCore.Core.Type.Term
*)
