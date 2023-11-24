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

Definition fst {a : Type} {b : Type} : (a * b)%type -> a :=
  fun '(pair a _) => a.

Definition snd {a : Type} {b : Type} : (a * b)%type -> b :=
  fun '(pair _ b) => b.

Definition curry {a : Type} {b : Type} {c : Type}
   : ((a * b)%type -> c) -> a -> b -> c :=
  fun f a b => f (pair a b).

Definition uncurry {a : Type} {b : Type} {c : Type}
   : (a -> b -> c) -> (a * b)%type -> c :=
  fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | f, pair a b => f a b end.

Definition op_zd__ {a : Type} {b : Type} : (a -> b) -> a -> b :=
  fun f a => f a.

Notation "'_$_'" := (op_zd__).

Infix "$" := (_$_) (at level 99).

Definition flip {a : Type} {b : Type} {c : Type}
   : (a -> b -> c) -> b -> a -> c :=
  fun f x y => f y x.

Axiom until : forall {a : Type}, (a -> bool) -> (a -> a) -> a -> a.

Definition op_z2218U__ {b : Type} {c : Type} {a : Type}
   : (b -> c) -> (a -> b) -> a -> c :=
  fun f g => fun x => f (g x).

Notation "'_∘_'" := (op_z2218U__).

Infix "∘" := (_∘_) (left associativity, at level 40).

Definition const {a : Type} {b : Type} : a -> b -> a :=
  fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | x, _ => x end.

Definition id {a : Type} : a -> a :=
  fun x => x.

Module Notations.
Notation "'_PlutusTx_Base.$_'" := (op_zd__).
Infix "PlutusTx_Base.$" := (_$_) (at level 99).
Notation "'_PlutusTx_Base.∘_'" := (op_z2218U__).
Infix "PlutusTx_Base.∘" := (_∘_) (left associativity, at level 40).
End Notations.

(* External variables:
     Type bool op_zt__ pair
*)
