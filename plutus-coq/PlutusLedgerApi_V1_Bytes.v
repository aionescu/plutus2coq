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

Require Data.Either.
Require GHC.Char.
Require PlutusTx_Builtins_Internal.
Require String.

(* Converted type declarations: *)

Inductive LedgerBytesError : Type :=
  | UnpairedDigit : LedgerBytesError
  | NotHexit : GHC.Char.Char -> LedgerBytesError.

Inductive LedgerBytes : Type :=
  | MkLedgerBytes (getLedgerBytes : PlutusTx_Builtins_Internal.BuiltinByteString)
   : LedgerBytes.

Definition getLedgerBytes (arg_0__ : LedgerBytes) :=
  let 'MkLedgerBytes getLedgerBytes := arg_0__ in
  getLedgerBytes.

(* Converted value declarations: *)

(* Skipping all instances of class `Data.String.IsString', including
   `PlutusLedgerApi_V1_Bytes.IsString__LedgerBytes' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `PlutusLedgerApi_V1_Bytes.Show__LedgerBytes' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Bytes.Lift__DefaultUni__LedgerBytes' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Bytes.Typeable__DefaultUni__LedgerBytes' *)

Axiom fromHex : String.string ->
                Data.Either.Either LedgerBytesError LedgerBytes.

Axiom fromBytes : String.string -> LedgerBytes.

Axiom bytes : LedgerBytes -> String.string.

Axiom encodeByteString : String.string -> String.string.

(* External variables:
     Data.Either.Either GHC.Char.Char PlutusTx_Builtins_Internal.BuiltinByteString
     String.string
*)
