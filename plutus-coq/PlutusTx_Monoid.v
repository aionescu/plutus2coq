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
Require PlutusTx_List.
Require PlutusTx_Semigroup.
Import PlutusTx_Semigroup.Notations.

(* Converted type declarations: *)

Record Monoid__Dict (a : Type) := Monoid__Dict_Build {
  mempty__ : a }.

Definition Monoid (a : Type) `{PlutusTx_Semigroup.Semigroup a} :=
  forall r__, (Monoid__Dict a -> r__) -> r__.
Existing Class Monoid.

Record Group__Dict (a : Type) := Group__Dict_Build {
  inv__ : a -> a }.

Definition mempty `{g__0__ : Monoid a} : a :=
  g__0__ _ (mempty__ a).

Definition Group (a : Type) `{Monoid a} :=
  forall r__, (Group__Dict a -> r__) -> r__.
Existing Class Group.

Definition inv `{g__0__ : Group a} : a -> a :=
  g__0__ _ (inv__ a).

(* Converted value declarations: *)

(* Skipping instance `PlutusTx_Monoid.Monoid__BuiltinByteString' of class
   `PlutusTx_Monoid.Monoid' *)

Local Definition Monoid__BuiltinString_mempty
   : PlutusTx_Builtins_Internal.BuiltinString :=
  PlutusTx_Builtins.emptyString.

Program Instance Monoid__BuiltinString
   : Monoid PlutusTx_Builtins_Internal.BuiltinString :=
  fun _ k__ => k__ {| mempty__ := Monoid__BuiltinString_mempty |}.

Local Definition Monoid__list_mempty {inst_a : Type} : list inst_a :=
  nil.

Program Instance Monoid__list {a : Type} : Monoid (list a) :=
  fun _ k__ => k__ {| mempty__ := Monoid__list_mempty |}.

Local Definition Monoid__option_mempty {inst_a : Type}
  `{PlutusTx_Semigroup.Semigroup inst_a}
   : option inst_a :=
  None.

Program Instance Monoid__option {a : Type} `{PlutusTx_Semigroup.Semigroup a}
   : Monoid (option a) :=
  fun _ k__ => k__ {| mempty__ := Monoid__option_mempty |}.

Local Definition Monoid__unit_mempty : unit :=
  tt.

Program Instance Monoid__unit : Monoid unit :=
  fun _ k__ => k__ {| mempty__ := Monoid__unit_mempty |}.

Local Definition Monoid__op_zt___mempty {inst_a : Type} {inst_b : Type} `{Monoid
  inst_a} `{Monoid inst_b}
   : (inst_a * inst_b)%type :=
  pair mempty mempty.

Program Instance Monoid__op_zt__ {a : Type} {b : Type} `{Monoid a} `{Monoid b}
   : Monoid (a * b)%type :=
  fun _ k__ => k__ {| mempty__ := Monoid__op_zt___mempty |}.

Local Definition Monoid__Dual_mempty {inst_a : Type} `{Monoid inst_a}
   : Data.SemigroupInternal.Dual inst_a :=
  Data.SemigroupInternal.Mk_Dual mempty.

Program Instance Monoid__Dual {a : Type} `{Monoid a}
   : Monoid (Data.SemigroupInternal.Dual a) :=
  fun _ k__ => k__ {| mempty__ := Monoid__Dual_mempty |}.

Local Definition Monoid__Endo_mempty {inst_a : Type}
   : Data.SemigroupInternal.Endo inst_a :=
  Data.SemigroupInternal.Mk_Endo PlutusTx_Base.id.

Program Instance Monoid__Endo {a : Type}
   : Monoid (Data.SemigroupInternal.Endo a) :=
  fun _ k__ => k__ {| mempty__ := Monoid__Endo_mempty |}.

Local Definition Monoid__First_mempty {inst_a : Type}
   : Data.Monoid.First inst_a :=
  Data.Monoid.Mk_First None.

Program Instance Monoid__First {a : Type} : Monoid (Data.Monoid.First a) :=
  fun _ k__ => k__ {| mempty__ := Monoid__First_mempty |}.

Definition mappend {a : Type} `{Monoid a} : a -> a -> a :=
  _PlutusTx_Semigroup.<>_.

Definition mconcat {a : Type} `{Monoid a} : list a -> a :=
  PlutusTx_List.foldr mappend mempty.

Definition gsub {a : Type} `{Group a} : a -> a -> a :=
  fun x y => x PlutusTx_Semigroup.<> inv y.

(* External variables:
     None Type list nil op_zt__ option pair tt unit Data.Monoid.First
     Data.Monoid.Mk_First Data.SemigroupInternal.Dual Data.SemigroupInternal.Endo
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Endo PlutusTx_Base.id
     PlutusTx_Builtins.emptyString PlutusTx_Builtins_Internal.BuiltinString
     PlutusTx_List.foldr PlutusTx_Semigroup.Semigroup PlutusTx_Semigroup.op_zlzg__
*)
