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
Require PlutusTx_Applicative.
Require PlutusTx_Base.
Require PlutusTx_Foldable.
Require PlutusTx_Functor.
Require PlutusTx_Monoid.
Import PlutusTx_Functor.Notations.

(* Converted type declarations: *)

Record Traversable__Dict (t : Type -> Type) := Traversable__Dict_Build {
  traverse__ : forall {f : Type -> Type},
  forall {a : Type},
  forall {b : Type},
  forall `{PlutusTx_Applicative.Applicative f}, (a -> f b) -> t a -> f (t b) }.

Definition Traversable (t : Type -> Type) `{PlutusTx_Functor.Functor t}
  `{PlutusTx_Foldable.Foldable t} :=
  forall r__, (Traversable__Dict t -> r__) -> r__.
Existing Class Traversable.

Definition traverse `{g__0__ : Traversable t}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{PlutusTx_Applicative.Applicative f}, (a -> f b) -> t a -> f (t b) :=
  g__0__ _ (traverse__ t).

(* Converted value declarations: *)

Local Definition Traversable__list_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{PlutusTx_Applicative.Applicative f},
     (a -> f b) -> list a -> f (list b) :=
  fun {f : Type -> Type}
  {a : Type}
  {b : Type}
  `{PlutusTx_Applicative.Applicative f} =>
    fun f =>
      let fix go arg_0__
        := match arg_0__ with
           | nil => PlutusTx_Applicative.pure nil
           | cons x xs => PlutusTx_Applicative.liftA2 cons (f x) (go xs)
           end in
      go.

Program Instance Traversable__list : Traversable list :=
  fun _ k__ =>
    k__ {| traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{PlutusTx_Applicative.Applicative f} =>
             Traversable__list_traverse |}.

Local Definition Traversable__option_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{PlutusTx_Applicative.Applicative f},
     (a -> f b) -> option a -> f (option b) :=
  fun {f : Type -> Type}
  {a : Type}
  {b : Type}
  `{PlutusTx_Applicative.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, None => PlutusTx_Applicative.pure None
      | f, Some a => Some PlutusTx_Functor.<$> f a
      end.

Program Instance Traversable__option : Traversable option :=
  fun _ k__ =>
    k__ {| traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{PlutusTx_Applicative.Applicative f} =>
             Traversable__option_traverse |}.

Local Definition Traversable__Either_traverse {inst_c : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{PlutusTx_Applicative.Applicative f},
     (a -> f b) -> Data.Either.Either inst_c a -> f (Data.Either.Either inst_c b) :=
  fun {f : Type -> Type}
  {a : Type}
  {b : Type}
  `{PlutusTx_Applicative.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Data.Either.Left a => PlutusTx_Applicative.pure (Data.Either.Left a)
      | f, Data.Either.Right a => Data.Either.Right PlutusTx_Functor.<$> f a
      end.

Program Instance Traversable__Either {c : Type}
   : Traversable (Data.Either.Either c) :=
  fun _ k__ =>
    k__ {| traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{PlutusTx_Applicative.Applicative f} =>
             Traversable__Either_traverse |}.

Local Definition Traversable__pair_type_traverse {inst_c : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{PlutusTx_Applicative.Applicative f},
     (a -> f b) ->
     GHC.Tuple.pair_type inst_c a -> f (GHC.Tuple.pair_type inst_c b) :=
  fun {f : Type -> Type}
  {a : Type}
  {b : Type}
  `{PlutusTx_Applicative.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, pair c a => (fun arg_2__ => pair c arg_2__) PlutusTx_Functor.<$> f a
      end.

Program Instance Traversable__pair_type {c : Type}
   : Traversable (GHC.Tuple.pair_type c) :=
  fun _ k__ =>
    k__ {| traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{PlutusTx_Applicative.Applicative f} =>
             Traversable__pair_type_traverse |}.

Local Definition Traversable__Identity_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{PlutusTx_Applicative.Applicative f},
     (a -> f b) ->
     Data.Functor.Identity.Identity a -> f (Data.Functor.Identity.Identity b) :=
  fun {f : Type -> Type}
  {a : Type}
  {b : Type}
  `{PlutusTx_Applicative.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Data.Functor.Identity.Mk_Identity a =>
          Data.Functor.Identity.Mk_Identity PlutusTx_Functor.<$> f a
      end.

Program Instance Traversable__Identity
   : Traversable Data.Functor.Identity.Identity :=
  fun _ k__ =>
    k__ {| traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{PlutusTx_Applicative.Applicative f} =>
             Traversable__Identity_traverse |}.

Local Definition Traversable__Const_traverse {inst_c : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{PlutusTx_Applicative.Applicative f},
     (a -> f b) ->
     Data.Functor.Const.Const inst_c a -> f (Data.Functor.Const.Const inst_c b) :=
  fun {f : Type -> Type}
  {a : Type}
  {b : Type}
  `{PlutusTx_Applicative.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, Data.Functor.Const.Mk_Const c =>
          PlutusTx_Applicative.pure (Data.Functor.Const.Mk_Const c)
      end.

Program Instance Traversable__Const {c : Type}
   : Traversable (Data.Functor.Const.Const c) :=
  fun _ k__ =>
    k__ {| traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{PlutusTx_Applicative.Applicative f} =>
             Traversable__Const_traverse |}.

Definition sequenceA {t : Type -> Type} {f : Type -> Type} {a : Type}
  `{Traversable t} `{PlutusTx_Applicative.Applicative f}
   : t (f a) -> f (t a) :=
  traverse PlutusTx_Base.id.

Definition sequence {t : Type -> Type} {f : Type -> Type} {a : Type}
  `{Traversable t} `{PlutusTx_Applicative.Applicative f}
   : t (f a) -> f (t a) :=
  sequenceA.

Definition mapM {t : Type -> Type} {f : Type -> Type} {a : Type} {b : Type}
  `{Traversable t} `{PlutusTx_Applicative.Applicative f}
   : (a -> f b) -> t a -> f (t b) :=
  traverse.

Definition for_ {t : Type -> Type} {f : Type -> Type} {a : Type} {b : Type}
  `{Traversable t} `{PlutusTx_Applicative.Applicative f}
   : t a -> (a -> f b) -> f (t b) :=
  PlutusTx_Base.flip traverse.

Definition fmapDefault {t : Type -> Type} {a : Type} {b : Type} `{Traversable t}
   : (a -> b) -> t a -> t b :=
  GHC.Prim.coerce (traverse : (a -> Data.Functor.Identity.Identity b) ->
                   t a -> Data.Functor.Identity.Identity (t b)).

Axiom foldMapDefault : forall {t : Type -> Type},
                       forall {m : Type},
                       forall {a : Type},
                       forall `{Traversable t},
                       forall `{PlutusTx_Monoid.Monoid m}, (a -> m) -> t a -> m.

(* External variables:
     None Some Type cons list nil option pair Data.Either.Either Data.Either.Left
     Data.Either.Right Data.Functor.Const.Const Data.Functor.Const.Mk_Const
     Data.Functor.Identity.Identity Data.Functor.Identity.Mk_Identity GHC.Prim.coerce
     GHC.Tuple.pair_type PlutusTx_Applicative.Applicative PlutusTx_Applicative.liftA2
     PlutusTx_Applicative.pure PlutusTx_Base.flip PlutusTx_Base.id
     PlutusTx_Foldable.Foldable PlutusTx_Functor.Functor PlutusTx_Functor.op_zlzdzg__
     PlutusTx_Monoid.Monoid
*)
