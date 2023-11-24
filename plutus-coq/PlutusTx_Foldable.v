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

Require BinNums.
Require Data.Either.
Require Data.Functor.Const.
Require Data.Functor.Identity.
Require GHC.Base.
Require GHC.Num.
Require GHC.Tuple.
Require PlutusTx_Applicative.
Require PlutusTx_Base.
Require PlutusTx_Monoid.
Require PlutusTx_Numeric.
Require PlutusTx_Semigroup.
Import GHC.Num.Notations.
Import PlutusTx_Applicative.Notations.
Import PlutusTx_Base.Notations.
Import PlutusTx_Numeric.Notations.
Import PlutusTx_Semigroup.Notations.

(* Converted type declarations: *)

Record Foldable__Dict (t : Type -> Type) := Foldable__Dict_Build {
  foldr__ : forall {a : Type},
  forall {b : Type}, (a -> b -> b) -> b -> t a -> b }.

Definition Foldable (t : Type -> Type) :=
  forall r__, (Foldable__Dict t -> r__) -> r__.
Existing Class Foldable.

Definition foldr `{g__0__ : Foldable t}
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> t a -> b :=
  g__0__ _ (foldr__ t).

(* Converted value declarations: *)

Local Definition Foldable__list_foldr
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> list a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z =>
      let fix go arg_0__
        := match arg_0__ with
           | nil => z
           | cons x xs => f x (go xs)
           end in
      go.

Program Instance Foldable__list : Foldable list :=
  fun _ k__ =>
    k__ {| foldr__ := fun {a : Type} {b : Type} => Foldable__list_foldr |}.

Local Definition Foldable__option_foldr
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> option a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z => fun arg_0__ => match arg_0__ with | None => z | Some a => f a z end.

Program Instance Foldable__option : Foldable option :=
  fun _ k__ =>
    k__ {| foldr__ := fun {a : Type} {b : Type} => Foldable__option_foldr |}.

Local Definition Foldable__Either_foldr {inst_c : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Data.Either.Either inst_c a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z =>
      fun arg_0__ =>
        match arg_0__ with
        | Data.Either.Left _ => z
        | Data.Either.Right a => f a z
        end.

Program Instance Foldable__Either {c : Type}
   : Foldable (Data.Either.Either c) :=
  fun _ k__ =>
    k__ {| foldr__ := fun {a : Type} {b : Type} => Foldable__Either_foldr |}.

Local Definition Foldable__pair_type_foldr {inst_c : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> GHC.Tuple.pair_type inst_c a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, pair _ a => f a z
      end.

Program Instance Foldable__pair_type {c : Type}
   : Foldable (GHC.Tuple.pair_type c) :=
  fun _ k__ =>
    k__ {| foldr__ := fun {a : Type} {b : Type} => Foldable__pair_type_foldr |}.

Local Definition Foldable__Identity_foldr
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> b) -> b -> Data.Functor.Identity.Identity a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Data.Functor.Identity.Mk_Identity a => f a z
      end.

Program Instance Foldable__Identity : Foldable Data.Functor.Identity.Identity :=
  fun _ k__ =>
    k__ {| foldr__ := fun {a : Type} {b : Type} => Foldable__Identity_foldr |}.

Local Definition Foldable__Const_foldr {inst_c : Type}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> b) -> b -> Data.Functor.Const.Const inst_c a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | _, z, _ => z
      end.

Program Instance Foldable__Const {c : Type}
   : Foldable (Data.Functor.Const.Const c) :=
  fun _ k__ =>
    k__ {| foldr__ := fun {a : Type} {b : Type} => Foldable__Const_foldr |}.

Definition foldMap {t : Type -> Type} {m : Type} {a : Type} `{Foldable t}
  `{PlutusTx_Monoid.Monoid m}
   : (a -> m) -> t a -> m :=
  fun f =>
    foldr (_PlutusTx_Semigroup.<>_ PlutusTx_Base.∘ f) PlutusTx_Monoid.mempty.

Definition fold {t : Type -> Type} {m : Type} `{Foldable t}
  `{PlutusTx_Monoid.Monoid m}
   : t m -> m :=
  foldMap PlutusTx_Base.id.

Definition foldl {t : Type -> Type} {b : Type} {a : Type} `{Foldable t}
   : (b -> a -> b) -> b -> t a -> b :=
  fun f z t => foldr (fun a g b => g (f b a)) PlutusTx_Base.id t z.

Definition toList {t : Type -> Type} {a : Type} `{Foldable t} : t a -> list a :=
  fun t => GHC.Base.build' (fun _ => (fun c n => foldr c n t)).

Definition length {t : Type -> Type} {a : Type} `{Foldable t}
   : t a -> BinNums.Z :=
  foldr (fun arg_0__ arg_1__ =>
           match arg_0__, arg_1__ with
           | _, acc => acc PlutusTx_Numeric.+ #1
           end) #0.

Definition sum {t : Type -> Type} {a : Type} `{Foldable t}
  `{PlutusTx_Numeric.AdditiveMonoid a}
   : t a -> a :=
  foldr _PlutusTx_Numeric.+_ PlutusTx_Numeric.zero.

Definition product {t : Type -> Type} {a : Type} `{Foldable t}
  `{PlutusTx_Numeric.MultiplicativeMonoid a}
   : t a -> a :=
  foldr _PlutusTx_Numeric.*_ PlutusTx_Numeric.one.

Definition traverse_ {t : Type -> Type} {f : Type -> Type} {a : Type} {b : Type}
  `{Foldable t} `{PlutusTx_Applicative.Applicative f}
   : (a -> f b) -> t a -> f unit :=
  fun f =>
    let c := fun x k => f x PlutusTx_Applicative.*> k in
    foldr c (PlutusTx_Applicative.pure tt).

Definition for__ {t : Type -> Type} {f : Type -> Type} {a : Type} {b : Type}
  `{Foldable t} `{PlutusTx_Applicative.Applicative f}
   : t a -> (a -> f b) -> f unit :=
  PlutusTx_Base.flip traverse_.

Definition sequenceA_ {t : Type -> Type} {f : Type -> Type} {a : Type}
  `{Foldable t} `{PlutusTx_Applicative.Applicative f}
   : t (f a) -> f unit :=
  let c := fun m k => m PlutusTx_Applicative.*> k in
  foldr c (PlutusTx_Applicative.pure tt).

(* Skipping definition `PlutusTx_Foldable.asum' *)

Axiom concat : forall {t : Type -> Type},
               forall {a : Type}, forall `{Foldable t}, t (list a) -> list a.

Definition concatMap {t : Type -> Type} {a : Type} {b : Type} `{Foldable t}
   : (a -> list b) -> t a -> list b :=
  fun f xs =>
    GHC.Base.build' (fun _ => (fun c n => foldr (fun x b => foldr c b (f x)) n xs)).

(* External variables:
     None Some Type cons list nil option pair tt unit BinNums.Z Data.Either.Either
     Data.Either.Left Data.Either.Right Data.Functor.Const.Const
     Data.Functor.Identity.Identity Data.Functor.Identity.Mk_Identity GHC.Base.build'
     GHC.Num.fromInteger GHC.Tuple.pair_type PlutusTx_Applicative.Applicative
     PlutusTx_Applicative.op_ztzg__ PlutusTx_Applicative.pure PlutusTx_Base.flip
     PlutusTx_Base.id PlutusTx_Base.op_z2218U__ PlutusTx_Monoid.Monoid
     PlutusTx_Monoid.mempty PlutusTx_Numeric.AdditiveMonoid
     PlutusTx_Numeric.MultiplicativeMonoid PlutusTx_Numeric.one
     PlutusTx_Numeric.op_zp__ PlutusTx_Numeric.op_zt__ PlutusTx_Numeric.zero
     PlutusTx_Semigroup.op_zlzg__
*)
