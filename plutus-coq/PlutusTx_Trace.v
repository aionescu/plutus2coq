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

Require PlutusTx_Builtins_Internal.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Axiom traceError : forall {a : Type},
                   PlutusTx_Builtins_Internal.BuiltinString -> a.

Axiom traceIfFalse : PlutusTx_Builtins_Internal.BuiltinString -> bool -> bool.

Axiom traceIfTrue : PlutusTx_Builtins_Internal.BuiltinString -> bool -> bool.

Axiom traceBool : PlutusTx_Builtins_Internal.BuiltinString ->
                  PlutusTx_Builtins_Internal.BuiltinString -> bool -> bool.

(* External variables:
     Type bool PlutusTx_Builtins_Internal.BuiltinString
*)
