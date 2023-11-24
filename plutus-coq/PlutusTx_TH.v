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
Require Language.Haskell.TH.Syntax.
Require Language.Haskell.TH.Syntax.Compat.
Require PlutusTx_Code.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Axiom compile : forall {a : Type},
                Language.Haskell.TH.Syntax.Compat.SpliceQ a ->
                Language.Haskell.TH.Syntax.Compat.SpliceQ (PlutusTx_Code.CompiledCode a).

Axiom loadFromFile : forall {a : Type},
                     GHC.Base.String ->
                     Language.Haskell.TH.Syntax.Compat.SpliceQ (PlutusTx_Code.CompiledCode a).

Axiom compileUntyped : Language.Haskell.TH.Syntax.Q
                       Language.Haskell.TH.Syntax.Exp ->
                       Language.Haskell.TH.Syntax.Q Language.Haskell.TH.Syntax.Exp.

(* External variables:
     Type GHC.Base.String Language.Haskell.TH.Syntax.Exp Language.Haskell.TH.Syntax.Q
     Language.Haskell.TH.Syntax.Compat.SpliceQ PlutusTx_Code.CompiledCode
*)
