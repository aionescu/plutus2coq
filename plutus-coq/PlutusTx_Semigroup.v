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

Require Data.Monoid.
Require Data.SemigroupInternal.
Require PlutusTx_Base.
Require PlutusTx_Builtins.
Require PlutusTx_Builtins_Internal.
Require PlutusTx_Functor.
Require PlutusTx_List.
Require PlutusTx_Ord.
Import PlutusTx_Base.Notations.
Import PlutusTx_List.Notations.

(* Converted type declarations: *)

Record Semigroup__Dict (a : Type) := Semigroup__Dict_Build {
  op_zlzg____ : a -> a -> a }.

Definition Semigroup (a : Type) :=
  forall r__, (Semigroup__Dict a -> r__) -> r__.
Existing Class Semigroup.

Definition op_zlzg__ `{g__0__ : Semigroup a} : a -> a -> a :=
  g__0__ _ (op_zlzg____ a).

Notation "'_<>_'" := (op_zlzg__).

Infix "<>" := (_<>_) (at level 70).

Inductive Min a : Type := | MkMin (getMin : a) : Min a.

Inductive Max a : Type := | MkMax (getMax : a) : Max a.

Arguments MkMin {_} _.

Arguments MkMax {_} _.

Definition getMin {a} (arg_0__ : Min a) :=
  let 'MkMin getMin := arg_0__ in
  getMin.

Definition getMax {a} (arg_0__ : Max a) :=
  let 'MkMax getMax := arg_0__ in
  getMax.

(* Converted value declarations: *)

(* Skipping instance `PlutusTx_Semigroup.Semigroup__BuiltinByteString' of class
   `PlutusTx_Semigroup.Semigroup' *)

Local Definition Semigroup__BuiltinString_op_zlzg__
   : PlutusTx_Builtins_Internal.BuiltinString ->
     PlutusTx_Builtins_Internal.BuiltinString ->
     PlutusTx_Builtins_Internal.BuiltinString :=
  PlutusTx_Builtins.appendString.

Program Instance Semigroup__BuiltinString
   : Semigroup PlutusTx_Builtins_Internal.BuiltinString :=
  fun _ k__ => k__ {| op_zlzg____ := Semigroup__BuiltinString_op_zlzg__ |}.

Local Definition Semigroup__list_op_zlzg__ {inst_a : Type}
   : list inst_a -> list inst_a -> list inst_a :=
  _PlutusTx_List.++_.

Program Instance Semigroup__list {a : Type} : Semigroup (list a) :=
  fun _ k__ => k__ {| op_zlzg____ := Semigroup__list_op_zlzg__ |}.

Local Definition Semigroup__op_zt___op_zlzg__ {inst_a : Type} {inst_b : Type}
  `{Semigroup inst_a} `{Semigroup inst_b}
   : (inst_a * inst_b)%type -> (inst_a * inst_b)%type -> (inst_a * inst_b)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair a1 b1, pair a2 b2 => pair (a1 <> a2) (b1 <> b2)
    end.

Program Instance Semigroup__op_zt__ {a : Type} {b : Type} `{Semigroup a}
  `{Semigroup b}
   : Semigroup (a * b)%type :=
  fun _ k__ => k__ {| op_zlzg____ := Semigroup__op_zt___op_zlzg__ |}.

Local Definition Semigroup__option_op_zlzg__ {inst_a : Type} `{Semigroup inst_a}
   : option inst_a -> option inst_a -> option inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Some a1, Some a2 => Some (a1 <> a2)
    | Some a1, None => Some a1
    | None, Some a2 => Some a2
    | None, None => None
    end.

Program Instance Semigroup__option {a : Type} `{Semigroup a}
   : Semigroup (option a) :=
  fun _ k__ => k__ {| op_zlzg____ := Semigroup__option_op_zlzg__ |}.

Local Definition Semigroup__comparison_op_zlzg__
   : comparison -> comparison -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Lt, _ => Lt
    | Eq, y => y
    | Gt, _ => Gt
    end.

Program Instance Semigroup__comparison : Semigroup comparison :=
  fun _ k__ => k__ {| op_zlzg____ := Semigroup__comparison_op_zlzg__ |}.

Local Definition Semigroup__unit_op_zlzg__ : unit -> unit -> unit :=
  fun arg_0__ arg_1__ => tt.

Program Instance Semigroup__unit : Semigroup unit :=
  fun _ k__ => k__ {| op_zlzg____ := Semigroup__unit_op_zlzg__ |}.

Local Definition Semigroup__Dual_op_zlzg__ {inst_a : Type} `{Semigroup inst_a}
   : Data.SemigroupInternal.Dual inst_a ->
     Data.SemigroupInternal.Dual inst_a -> Data.SemigroupInternal.Dual inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Data.SemigroupInternal.Mk_Dual a1, Data.SemigroupInternal.Mk_Dual a2 =>
        Data.SemigroupInternal.Mk_Dual (a2 <> a1)
    end.

Program Instance Semigroup__Dual {a : Type} `{Semigroup a}
   : Semigroup (Data.SemigroupInternal.Dual a) :=
  fun _ k__ => k__ {| op_zlzg____ := Semigroup__Dual_op_zlzg__ |}.

Local Definition Semigroup__Endo_op_zlzg__ {inst_a : Type}
   : Data.SemigroupInternal.Endo inst_a ->
     Data.SemigroupInternal.Endo inst_a -> Data.SemigroupInternal.Endo inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Data.SemigroupInternal.Mk_Endo a, Data.SemigroupInternal.Mk_Endo b =>
        Data.SemigroupInternal.Mk_Endo (a PlutusTx_Base.∘ b)
    end.

Program Instance Semigroup__Endo {a : Type}
   : Semigroup (Data.SemigroupInternal.Endo a) :=
  fun _ k__ => k__ {| op_zlzg____ := Semigroup__Endo_op_zlzg__ |}.

Local Definition Semigroup__First_op_zlzg__ {inst_a : Type}
   : Data.Monoid.First inst_a ->
     Data.Monoid.First inst_a -> Data.Monoid.First inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Data.Monoid.Mk_First None, b => b
    | a, _ => a
    end.

Program Instance Semigroup__First {a : Type}
   : Semigroup (Data.Monoid.First a) :=
  fun _ k__ => k__ {| op_zlzg____ := Semigroup__First_op_zlzg__ |}.

Local Definition Functor__Max_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Max a -> Max b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, MkMax m => MkMax (f m)
      end.

Program Instance Functor__Max : PlutusTx_Functor.Functor Max :=
  fun _ k__ =>
    k__ {| PlutusTx_Functor.fmap__ := fun {a : Type} {b : Type} =>
             Functor__Max_fmap |}.

Local Definition Semigroup__Max_op_zlzg__ {inst_a : Type} `{PlutusTx_Ord.Ord
  inst_a}
   : Max inst_a -> Max inst_a -> Max inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkMax a, MkMax b => MkMax (PlutusTx_Ord.max a b)
    end.

Program Instance Semigroup__Max {a : Type} `{PlutusTx_Ord.Ord a}
   : Semigroup (Max a) :=
  fun _ k__ => k__ {| op_zlzg____ := Semigroup__Max_op_zlzg__ |}.

Local Definition Functor__Min_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Min a -> Min b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, MkMin m => MkMin (f m)
      end.

Program Instance Functor__Min : PlutusTx_Functor.Functor Min :=
  fun _ k__ =>
    k__ {| PlutusTx_Functor.fmap__ := fun {a : Type} {b : Type} =>
             Functor__Min_fmap |}.

Local Definition Semigroup__Min_op_zlzg__ {inst_a : Type} `{PlutusTx_Ord.Ord
  inst_a}
   : Min inst_a -> Min inst_a -> Min inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkMin a, MkMin b => MkMin (PlutusTx_Ord.min a b)
    end.

Program Instance Semigroup__Min {a : Type} `{PlutusTx_Ord.Ord a}
   : Semigroup (Min a) :=
  fun _ k__ => k__ {| op_zlzg____ := Semigroup__Min_op_zlzg__ |}.

Module Notations.
Notation "'_PlutusTx_Semigroup.<>_'" := (op_zlzg__).
Infix "PlutusTx_Semigroup.<>" := (_<>_) (at level 70).
End Notations.

(* External variables:
     Eq Gt Lt None Some Type comparison list op_zt__ option pair tt unit
     Data.Monoid.First Data.Monoid.Mk_First Data.SemigroupInternal.Dual
     Data.SemigroupInternal.Endo Data.SemigroupInternal.Mk_Dual
     Data.SemigroupInternal.Mk_Endo PlutusTx_Base.op_z2218U__
     PlutusTx_Builtins.appendString PlutusTx_Builtins_Internal.BuiltinString
     PlutusTx_Functor.Functor PlutusTx_Functor.fmap__ PlutusTx_List.op_zpzp__
     PlutusTx_Ord.Ord PlutusTx_Ord.max PlutusTx_Ord.min
*)
