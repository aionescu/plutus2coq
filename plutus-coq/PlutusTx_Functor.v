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

Require Data.Either.
Require Data.Functor.Const.
Require Data.Functor.Identity.
Require GHC.Prim.
Require GHC.Tuple.
Require PlutusTx_Base.

(* Converted type declarations: *)

Record Functor__Dict (f : Type -> Type) := Functor__Dict_Build {
  fmap__ : forall {a : Type}, forall {b : Type}, (a -> b) -> f a -> f b }.

Definition Functor (f : Type -> Type) :=
  forall r__, (Functor__Dict f -> r__) -> r__.
Existing Class Functor.

Definition fmap `{g__0__ : Functor f}
   : forall {a : Type}, forall {b : Type}, (a -> b) -> f a -> f b :=
  g__0__ _ (fmap__ f).

(* Converted value declarations: *)

Local Definition Functor__list_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> list a -> list b :=
  fun {a : Type} {b : Type} =>
    fun f =>
      let fix go arg_0__
        := match arg_0__ with
           | nil => nil
           | cons x xs => cons (f x) (go xs)
           end in
      go.

Program Instance Functor__list : Functor list :=
  fun _ k__ =>
    k__ {| fmap__ := fun {a : Type} {b : Type} => Functor__list_fmap |}.

Local Definition Functor__option_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> option a -> option b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Some a => Some (f a)
      | _, None => None
      end.

Program Instance Functor__option : Functor option :=
  fun _ k__ =>
    k__ {| fmap__ := fun {a : Type} {b : Type} => Functor__option_fmap |}.

Local Definition Functor__Either_fmap {inst_c : Type}
   : forall {a : Type},
     forall {b : Type},
     (a -> b) -> Data.Either.Either inst_c a -> Data.Either.Either inst_c b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Data.Either.Right a => Data.Either.Right (f a)
      | _, Data.Either.Left c => Data.Either.Left c
      end.

Program Instance Functor__Either {c : Type} : Functor (Data.Either.Either c) :=
  fun _ k__ =>
    k__ {| fmap__ := fun {a : Type} {b : Type} => Functor__Either_fmap |}.

Local Definition Functor__pair_type_fmap {inst_c : Type}
   : forall {a : Type},
     forall {b : Type},
     (a -> b) -> GHC.Tuple.pair_type inst_c a -> GHC.Tuple.pair_type inst_c b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, pair c a => pair c (f a)
      end.

Program Instance Functor__pair_type {c : Type}
   : Functor (GHC.Tuple.pair_type c) :=
  fun _ k__ =>
    k__ {| fmap__ := fun {a : Type} {b : Type} => Functor__pair_type_fmap |}.

Local Definition Functor__Identity_fmap
   : forall {a : Type},
     forall {b : Type},
     (a -> b) ->
     Data.Functor.Identity.Identity a -> Data.Functor.Identity.Identity b :=
  fun {a : Type} {b : Type} =>
    GHC.Prim.coerce (PlutusTx_Base.id : (a -> b) -> a -> b).

Program Instance Functor__Identity : Functor Data.Functor.Identity.Identity :=
  fun _ k__ =>
    k__ {| fmap__ := fun {a : Type} {b : Type} => Functor__Identity_fmap |}.

Local Definition Functor__Const_fmap {inst_m : Type}
   : forall {a : Type},
     forall {b : Type},
     (a -> b) ->
     Data.Functor.Const.Const inst_m a -> Data.Functor.Const.Const inst_m b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ => GHC.Prim.coerce (PlutusTx_Base.id : inst_m -> inst_m).

Program Instance Functor__Const {m : Type}
   : Functor (Data.Functor.Const.Const m) :=
  fun _ k__ =>
    k__ {| fmap__ := fun {a : Type} {b : Type} => Functor__Const_fmap |}.

Definition op_zlzdzg__ {f : Type -> Type} {a : Type} {b : Type} `{Functor f}
   : (a -> b) -> f a -> f b :=
  fmap.

Notation "'_<$>_'" := (op_zlzdzg__).

Infix "<$>" := (_<$>_) (at level 99).

Definition op_zlzazg__ {f : Type -> Type} {a : Type} {b : Type} `{Functor f}
   : f a -> (a -> b) -> f b :=
  fun as_ f => f <$> as_.

Notation "'_<&>_'" := (op_zlzazg__).

Infix "<&>" := (_<&>_) (at level 99).

Definition op_zlzd__ {f : Type -> Type} {a : Type} {b : Type} `{Functor f}
   : a -> f b -> f a :=
  fun a => fmap (PlutusTx_Base.const a).

Notation "'_<$_'" := (op_zlzd__).

Infix "<$" := (_<$_) (at level 99).

Module Notations.
Notation "'_PlutusTx_Functor.<$>_'" := (op_zlzdzg__).
Infix "PlutusTx_Functor.<$>" := (_<$>_) (at level 99).
Notation "'_PlutusTx_Functor.<&>_'" := (op_zlzazg__).
Infix "PlutusTx_Functor.<&>" := (_<&>_) (at level 99).
Notation "'_PlutusTx_Functor.<$_'" := (op_zlzd__).
Infix "PlutusTx_Functor.<$" := (_<$_) (at level 99).
End Notations.

(* External variables:
     None Some Type cons list nil option pair Data.Either.Either Data.Either.Left
     Data.Either.Right Data.Functor.Const.Const Data.Functor.Identity.Identity
     GHC.Prim.coerce GHC.Tuple.pair_type PlutusTx_Base.const PlutusTx_Base.id
*)
