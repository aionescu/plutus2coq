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

Require Data.Proxy.
Require Language.Haskell.TH.Syntax.
Require PlutusCore.Builtin.KnownTypeAst.
Require PlutusCore.Core.Type.
Require PlutusCore.Name.
Require PlutusCore.Quote.
Require PlutusIR.Compiler.Definitions.
Require PlutusIR.Core.Type.

(* Converted type declarations: *)

Definition RTCompile uni fun_ :=
  (PlutusIR.Compiler.Definitions.DefT Language.Haskell.TH.Syntax.Name uni fun_
   unit PlutusCore.Quote.Quote)%type.

(* Converted value declarations: *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusTx_Lift_Class.Typeable' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusTx_Lift_Class.Typeable__op_zmzg____5' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusTx_Lift_Class.Typeable__Int__5' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusTx_Lift_Class.Lift__Int__5' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusTx_Lift_Class.Typeable__Z__5' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusTx_Lift_Class.Lift__Z__5' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusTx_Lift_Class.Typeable__string__5' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusTx_Lift_Class.Lift__string__5' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusTx_Lift_Class.Typeable__BuiltinData__5' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusTx_Lift_Class.Lift__BuiltinData__5' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusTx_Lift_Class.Typeable__BuiltinByteString__5' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusTx_Lift_Class.Lift__BuiltinByteString__5' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusTx_Lift_Class.Typeable__BuiltinString__5' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusTx_Lift_Class.Lift__BuiltinString__5' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusTx_Lift_Class.Lift__BuiltinList__5' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusTx_Lift_Class.Typeable__BuiltinBLS12_381_G1_Element__5' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusTx_Lift_Class.Lift__BuiltinBLS12_381_G1_Element__5' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusTx_Lift_Class.Typeable__BuiltinBLS12_381_G2_Element__5' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusTx_Lift_Class.Lift__BuiltinBLS12_381_G2_Element__5' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusTx_Lift_Class.Typeable__BuiltinBLS12_381_MlResult__5' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusTx_Lift_Class.Lift__BuiltinBLS12_381_MlResult__5' *)

Axiom typeRepBuiltin : forall {a : GHC.Types.Type_} {uni} {fun_},
                       forall `{PlutusCore.Builtin.KnownTypeAst.HasTypeLevel uni a},
                       Data.Proxy.Proxy a ->
                       RTCompile uni fun_ (PlutusCore.Core.Type.Type_ PlutusCore.Name.TyName uni unit).

Axiom liftBuiltin : forall {a} {uni} {fun_},
                    forall `{PlutusCore.Core.Type.HasTermLevel uni a},
                    a ->
                    RTCompile uni fun_ (PlutusIR.Core.Type.Term PlutusCore.Name.TyName
                                        PlutusCore.Name.Name uni fun_ unit).

(* External variables:
     unit Data.Proxy.Proxy GHC.Types.Type_ Language.Haskell.TH.Syntax.Name
     PlutusCore.Builtin.KnownTypeAst.HasTypeLevel PlutusCore.Core.Type.HasTermLevel
     PlutusCore.Core.Type.Type_ PlutusCore.Name.Name PlutusCore.Name.TyName
     PlutusCore.Quote.Quote PlutusIR.Compiler.Definitions.DefT
     PlutusIR.Core.Type.Term
*)
