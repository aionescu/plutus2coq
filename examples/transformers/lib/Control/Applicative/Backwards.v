(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.Functor.Classes.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive Backwards (f : Type -> Type) (a : Type) : Type :=
  | Mk_Backwards (forwards : f a) : Backwards f a.

Arguments Mk_Backwards {_} {_} _.

Definition forwards {f : Type -> Type} {a : Type} (arg_0__ : Backwards f a) :=
  let 'Mk_Backwards forwards := arg_0__ in
  forwards.

(* Converted value declarations: *)

Local Definition Eq1__Backwards_liftEq {inst_f : Type -> Type}
  `{(Data.Functor.Classes.Eq1 inst_f)}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> bool) -> Backwards inst_f a -> Backwards inst_f b -> bool :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, Mk_Backwards x, Mk_Backwards y => Data.Functor.Classes.liftEq eq x y
      end.

Program Instance Eq1__Backwards {f : Type -> Type} `{(Data.Functor.Classes.Eq1
   f)}
   : Data.Functor.Classes.Eq1 (Backwards f) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftEq__ := fun {a : Type} {b : Type} =>
             Eq1__Backwards_liftEq |}.

Local Definition Ord1__Backwards_liftCompare {inst_f : Type -> Type}
  `{(Data.Functor.Classes.Ord1 inst_f)}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> comparison) ->
     Backwards inst_f a -> Backwards inst_f b -> comparison :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, Mk_Backwards x, Mk_Backwards y =>
          Data.Functor.Classes.liftCompare comp x y
      end.

Program Instance Ord1__Backwards {f : Type -> Type} `{(Data.Functor.Classes.Ord1
   f)}
   : Data.Functor.Classes.Ord1 (Backwards f) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftCompare__ := fun {a : Type} {b : Type} =>
             Ord1__Backwards_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Control.Applicative.Backwards.Read1__Backwards' *)

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Control.Applicative.Backwards.Show1__Backwards' *)

Local Definition Eq___Backwards_op_zeze__ {inst_f : Type -> Type} {inst_a
   : Type} `{Data.Functor.Classes.Eq1 inst_f} `{GHC.Base.Eq_ inst_a}
   : Backwards inst_f inst_a -> Backwards inst_f inst_a -> bool :=
  Data.Functor.Classes.eq1.

Local Definition Eq___Backwards_op_zsze__ {inst_f : Type -> Type} {inst_a
   : Type} `{Data.Functor.Classes.Eq1 inst_f} `{GHC.Base.Eq_ inst_a}
   : Backwards inst_f inst_a -> Backwards inst_f inst_a -> bool :=
  fun x y => negb (Eq___Backwards_op_zeze__ x y).

Program Instance Eq___Backwards {f : Type -> Type} {a : Type}
  `{Data.Functor.Classes.Eq1 f} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Backwards f a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Backwards_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Backwards_op_zsze__ |}.

Local Definition Ord__Backwards_compare {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : Backwards inst_f inst_a -> Backwards inst_f inst_a -> comparison :=
  Data.Functor.Classes.compare1.

Local Definition Ord__Backwards_op_zl__ {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : Backwards inst_f inst_a -> Backwards inst_f inst_a -> bool :=
  fun x y => Ord__Backwards_compare x y GHC.Base.== Lt.

Local Definition Ord__Backwards_op_zlze__ {inst_f : Type -> Type} {inst_a
   : Type} `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : Backwards inst_f inst_a -> Backwards inst_f inst_a -> bool :=
  fun x y => Ord__Backwards_compare x y GHC.Base./= Gt.

Local Definition Ord__Backwards_op_zg__ {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : Backwards inst_f inst_a -> Backwards inst_f inst_a -> bool :=
  fun x y => Ord__Backwards_compare x y GHC.Base.== Gt.

Local Definition Ord__Backwards_op_zgze__ {inst_f : Type -> Type} {inst_a
   : Type} `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : Backwards inst_f inst_a -> Backwards inst_f inst_a -> bool :=
  fun x y => Ord__Backwards_compare x y GHC.Base./= Lt.

Local Definition Ord__Backwards_max {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : Backwards inst_f inst_a ->
     Backwards inst_f inst_a -> Backwards inst_f inst_a :=
  fun x y => if Ord__Backwards_op_zlze__ x y : bool then y else x.

Local Definition Ord__Backwards_min {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : Backwards inst_f inst_a ->
     Backwards inst_f inst_a -> Backwards inst_f inst_a :=
  fun x y => if Ord__Backwards_op_zlze__ x y : bool then x else y.

Program Instance Ord__Backwards {f : Type -> Type} {a : Type}
  `{Data.Functor.Classes.Ord1 f} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Backwards f a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Backwards_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Backwards_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Backwards_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Backwards_op_zgze__ ;
           GHC.Base.compare__ := Ord__Backwards_compare ;
           GHC.Base.max__ := Ord__Backwards_max ;
           GHC.Base.min__ := Ord__Backwards_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Control.Applicative.Backwards.Read__Backwards' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Control.Applicative.Backwards.Show__Backwards' *)

Local Definition Functor__Backwards_fmap {inst_f : Type -> Type}
  `{(GHC.Base.Functor inst_f)}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> Backwards inst_f a -> Backwards inst_f b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Backwards a => Mk_Backwards (GHC.Base.fmap f a)
      end.

Local Definition Functor__Backwards_op_zlzd__ {inst_f : Type -> Type}
  `{(GHC.Base.Functor inst_f)}
   : forall {a : Type},
     forall {b : Type}, a -> Backwards inst_f b -> Backwards inst_f a :=
  fun {a : Type} {b : Type} => Functor__Backwards_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Backwards {f : Type -> Type} `{(GHC.Base.Functor f)}
   : GHC.Base.Functor (Backwards f) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__Backwards_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__Backwards_op_zlzd__ |}.

Local Definition Applicative__Backwards_op_zlztzg__ {inst_f : Type -> Type}
  `{(GHC.Base.Applicative inst_f)}
   : forall {a : Type},
     forall {b : Type},
     Backwards inst_f (a -> b) -> Backwards inst_f a -> Backwards inst_f b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_Backwards f, Mk_Backwards a => Mk_Backwards (a GHC.Base.<**> f)
      end.

Local Definition Applicative__Backwards_liftA2 {inst_f : Type -> Type}
  `{(GHC.Base.Applicative inst_f)}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) ->
     Backwards inst_f a -> Backwards inst_f b -> Backwards inst_f c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__Backwards_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Backwards_op_ztzg__ {inst_f : Type -> Type}
  `{(GHC.Base.Applicative inst_f)}
   : forall {a : Type},
     forall {b : Type},
     Backwards inst_f a -> Backwards inst_f b -> Backwards inst_f b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 => Applicative__Backwards_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Backwards_pure {inst_f : Type -> Type}
  `{(GHC.Base.Applicative inst_f)}
   : forall {a : Type}, a -> Backwards inst_f a :=
  fun {a : Type} => fun a => Mk_Backwards (GHC.Base.pure a).

Program Instance Applicative__Backwards {f : Type -> Type}
  `{(GHC.Base.Applicative f)}
   : GHC.Base.Applicative (Backwards f) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__Backwards_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Backwards_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Backwards_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__Backwards_pure |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Control.Applicative.Backwards.Alternative__Backwards' *)

Local Definition Foldable__Backwards_foldMap {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Backwards inst_f a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Backwards t => Data.Foldable.foldMap f t
      end.

Local Definition Foldable__Backwards_fold {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Backwards inst_f m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Backwards_foldMap GHC.Base.id.

Local Definition Foldable__Backwards_foldl {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Backwards inst_f a -> b :=
  fun {b : Type} {a : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Mk_Backwards t => Data.Foldable.foldl f z t
      end.

Local Definition Foldable__Backwards_foldr {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Backwards inst_f a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, Mk_Backwards t => Data.Foldable.foldr f z t
      end.

Local Definition Foldable__Backwards_foldl' {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Backwards inst_f a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in
      Foldable__Backwards_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__Backwards_foldr' {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Backwards inst_f a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in
      Foldable__Backwards_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__Backwards_length {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, Backwards inst_f a -> GHC.Num.Int :=
  fun {a : Type} => fun '(Mk_Backwards t) => Data.Foldable.length t.

Local Definition Foldable__Backwards_null {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, Backwards inst_f a -> bool :=
  fun {a : Type} => fun '(Mk_Backwards t) => Data.Foldable.null t.

Local Definition Foldable__Backwards_product {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Backwards inst_f a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Backwards_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__Backwards_sum {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Backwards inst_f a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__Backwards_foldMap Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__Backwards_toList {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, Backwards inst_f a -> list a :=
  fun {a : Type} =>
    fun t =>
      GHC.Base.build' (fun _ => (fun c n => Foldable__Backwards_foldr c n t)).

Program Instance Foldable__Backwards {f : Type -> Type}
  `{(Data.Foldable.Foldable f)}
   : Data.Foldable.Foldable (Backwards f) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m : Type} `{GHC.Base.Monoid m} =>
             Foldable__Backwards_fold ;
           Data.Foldable.foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Backwards_foldMap ;
           Data.Foldable.foldl__ := fun {b : Type} {a : Type} =>
             Foldable__Backwards_foldl ;
           Data.Foldable.foldl'__ := fun {b : Type} {a : Type} =>
             Foldable__Backwards_foldl' ;
           Data.Foldable.foldr__ := fun {a : Type} {b : Type} =>
             Foldable__Backwards_foldr ;
           Data.Foldable.foldr'__ := fun {a : Type} {b : Type} =>
             Foldable__Backwards_foldr' ;
           Data.Foldable.length__ := fun {a : Type} => Foldable__Backwards_length ;
           Data.Foldable.null__ := fun {a : Type} => Foldable__Backwards_null ;
           Data.Foldable.product__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__Backwards_product ;
           Data.Foldable.sum__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__Backwards_sum ;
           Data.Foldable.toList__ := fun {a : Type} => Foldable__Backwards_toList |}.

Local Definition Traversable__Backwards_traverse {inst_f : Type -> Type}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> Backwards inst_f a -> f (Backwards inst_f b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Mk_Backwards t =>
          GHC.Base.fmap Mk_Backwards (Data.Traversable.traverse f t)
      end.

Local Definition Traversable__Backwards_mapM {inst_f : Type -> Type}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m},
     (a -> m b) -> Backwards inst_f a -> m (Backwards inst_f b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Backwards_traverse.

Local Definition Traversable__Backwards_sequenceA {inst_f : Type -> Type}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f},
     Backwards inst_f (f a) -> f (Backwards inst_f a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    fun '(Mk_Backwards t) =>
      GHC.Base.fmap Mk_Backwards (Data.Traversable.sequenceA t).

Local Definition Traversable__Backwards_sequence {inst_f : Type -> Type}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m}, Backwards inst_f (m a) -> m (Backwards inst_f a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Backwards_sequenceA.

Program Instance Traversable__Backwards {f : Type -> Type}
  `{(Data.Traversable.Traversable f)}
   : Data.Traversable.Traversable (Backwards f) :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Backwards_mapM ;
           Data.Traversable.sequence__ := fun {m : Type -> Type}
           {a : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Backwards_sequence ;
           Data.Traversable.sequenceA__ := fun {f : Type -> Type}
           {a : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Backwards_sequenceA ;
           Data.Traversable.traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Backwards_traverse |}.

(* External variables:
     Gt Lt Type bool comparison list negb Coq.Program.Basics.compose
     Data.Foldable.Foldable Data.Foldable.foldMap Data.Foldable.foldMap__
     Data.Foldable.fold__ Data.Foldable.foldl Data.Foldable.foldl'__
     Data.Foldable.foldl__ Data.Foldable.foldr Data.Foldable.foldr'__
     Data.Foldable.foldr__ Data.Foldable.length Data.Foldable.length__
     Data.Foldable.null Data.Foldable.null__ Data.Foldable.product__
     Data.Foldable.sum__ Data.Foldable.toList__ Data.Functor.Classes.Eq1
     Data.Functor.Classes.Ord1 Data.Functor.Classes.compare1 Data.Functor.Classes.eq1
     Data.Functor.Classes.liftCompare Data.Functor.Classes.liftCompare__
     Data.Functor.Classes.liftEq Data.Functor.Classes.liftEq__
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     Data.Traversable.Traversable Data.Traversable.mapM__ Data.Traversable.sequenceA
     Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse Data.Traversable.traverse__ GHC.Base.Applicative
     GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord
     GHC.Base.build' GHC.Base.compare__ GHC.Base.const GHC.Base.fmap GHC.Base.fmap__
     GHC.Base.id GHC.Base.liftA2__ GHC.Base.max__ GHC.Base.min__ GHC.Base.op_z2218U__
     GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg____ GHC.Base.op_zgze____
     GHC.Base.op_zl____ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____ GHC.Base.op_zlze____
     GHC.Base.op_zlztzg____ GHC.Base.op_zlztztzg__ GHC.Base.op_zsze__
     GHC.Base.op_zsze____ GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__
     GHC.Num.Int GHC.Num.Num
*)
