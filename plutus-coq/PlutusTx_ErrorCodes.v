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

(* Skipping definition `PlutusTx_ErrorCodes.allErrorCodes' *)

Axiom reconstructCaseError : PlutusTx_Builtins_Internal.BuiltinString.

Axiom voidIsNotSupportedError : PlutusTx_Builtins_Internal.BuiltinString.

Axiom ratioHasZeroDenominatorError : PlutusTx_Builtins_Internal.BuiltinString.

Axiom roundDefaultDefnError : PlutusTx_Builtins_Internal.BuiltinString.

Axiom checkHasFailedError : PlutusTx_Builtins_Internal.BuiltinString.

Axiom negativeIndexError : PlutusTx_Builtins_Internal.BuiltinString.

Axiom indexTooLargeError : PlutusTx_Builtins_Internal.BuiltinString.

Axiom headEmptyListError : PlutusTx_Builtins_Internal.BuiltinString.

Axiom tailEmptyListError : PlutusTx_Builtins_Internal.BuiltinString.

Axiom succVoidBadArgumentError : PlutusTx_Builtins_Internal.BuiltinString.

Axiom predVoidBadArgumentError : PlutusTx_Builtins_Internal.BuiltinString.

Axiom toEnumVoidBadArgumentError : PlutusTx_Builtins_Internal.BuiltinString.

Axiom succBoolBadArgumentError : PlutusTx_Builtins_Internal.BuiltinString.

Axiom predBoolBadArgumentError : PlutusTx_Builtins_Internal.BuiltinString.

Axiom toEnumBoolBadArgumentError : PlutusTx_Builtins_Internal.BuiltinString.

Axiom succOrderingBadArgumentError : PlutusTx_Builtins_Internal.BuiltinString.

Axiom predOrderingBadArgumentError : PlutusTx_Builtins_Internal.BuiltinString.

Axiom toEnumOrderingBadArgumentError : PlutusTx_Builtins_Internal.BuiltinString.

Axiom lastEmptyListError : PlutusTx_Builtins_Internal.BuiltinString.

(* External variables:
     PlutusTx_Builtins_Internal.BuiltinString
*)
