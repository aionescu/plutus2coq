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

Require Data.Proxy.
Require PlutusTx_Code.
Require PlutusTx_Utils.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition plc {loc : GHC.Types.Symbol} {a : Type}
   : Data.Proxy.Proxy loc -> a -> PlutusTx_Code.CompiledCode a :=
  fun arg_0__ arg_1__ =>
    PlutusTx_Code.SerializedCode (PlutusTx_Utils.mustBeReplaced
                                  (GHC.Base.hs_string__ "plc")) (PlutusTx_Utils.mustBeReplaced
                                                                 (GHC.Base.hs_string__ "pir"))
    (PlutusTx_Utils.mustBeReplaced (GHC.Base.hs_string__ "covidx")).

(* External variables:
     Type Data.Proxy.Proxy GHC.Types.Symbol PlutusTx_Code.CompiledCode
     PlutusTx_Code.SerializedCode PlutusTx_Utils.mustBeReplaced
*)
