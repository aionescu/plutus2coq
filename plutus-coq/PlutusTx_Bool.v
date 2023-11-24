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

(* No imports to convert. *)

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition op_zaza__ : bool -> bool -> bool :=
  fun l r => if l : bool then r else false.

Notation "'_&&_'" := (op_zaza__).

Infix "&&" := (_&&_).

Definition op_zbzb__ : bool -> bool -> bool :=
  fun l r => if l : bool then true else r.

Notation "'_||_'" := (op_zbzb__).

Infix "||" := (_||_).

Definition not : bool -> bool :=
  fun a => if a : bool then false else true.

Module Notations.
Notation "'_PlutusTx_Bool.&&_'" := (op_zaza__).
Infix "PlutusTx_Bool.&&" := (_&&_) (at level 99).
Notation "'_PlutusTx_Bool.||_'" := (op_zbzb__).
Infix "PlutusTx_Bool.||" := (_||_) (at level 99).
End Notations.

(* External variables:
     bool false true
*)
