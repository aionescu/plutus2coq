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
Require Data.Either.
Require Data.Foldable.
Require Data.Functor.
Require Data.Functor.Classes.
Require Data.Functor.Constant.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive Lift f a : Type := | Pure : a -> Lift f a | Other : (f a) -> Lift f a.

Definition Errors e :=
  (Lift (Data.Functor.Constant.Constant e))%type.

Arguments Pure {_} {_} _.

Arguments Other {_} {_} _.

(* Converted value declarations: *)

Local Definition Eq1__Lift_liftEq {inst_f : Type -> Type}
  `{(Data.Functor.Classes.Eq1 inst_f)}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> bool) -> Lift inst_f a -> Lift inst_f b -> bool :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | eq, Pure x1, Pure x2 => eq x1 x2
      | _, Pure _, Other _ => false
      | _, Other _, Pure _ => false
      | eq, Other y1, Other y2 => Data.Functor.Classes.liftEq eq y1 y2
      end.

Program Instance Eq1__Lift {f : Type -> Type} `{(Data.Functor.Classes.Eq1 f)}
   : Data.Functor.Classes.Eq1 (Lift f) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftEq__ := fun {a : Type} {b : Type} =>
             Eq1__Lift_liftEq |}.

Local Definition Ord1__Lift_liftCompare {inst_f : Type -> Type}
  `{(Data.Functor.Classes.Ord1 inst_f)}
   : forall {a : Type},
     forall {b : Type},
     (a -> b -> comparison) -> Lift inst_f a -> Lift inst_f b -> comparison :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | comp, Pure x1, Pure x2 => comp x1 x2
      | _, Pure _, Other _ => Lt
      | _, Other _, Pure _ => Gt
      | comp, Other y1, Other y2 => Data.Functor.Classes.liftCompare comp y1 y2
      end.

Program Instance Ord1__Lift {f : Type -> Type} `{(Data.Functor.Classes.Ord1 f)}
   : Data.Functor.Classes.Ord1 (Lift f) :=
  fun _ k__ =>
    k__ {| Data.Functor.Classes.liftCompare__ := fun {a : Type} {b : Type} =>
             Ord1__Lift_liftCompare |}.

(* Skipping all instances of class `Data.Functor.Classes.Read1', including
   `Control.Applicative.Lift.Read1__Lift' *)

(* Skipping all instances of class `Data.Functor.Classes.Show1', including
   `Control.Applicative.Lift.Show1__Lift' *)

Local Definition Eq___Lift_op_zeze__ {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Eq1 inst_f} `{GHC.Base.Eq_ inst_a}
   : Lift inst_f inst_a -> Lift inst_f inst_a -> bool :=
  Data.Functor.Classes.eq1.

Local Definition Eq___Lift_op_zsze__ {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Eq1 inst_f} `{GHC.Base.Eq_ inst_a}
   : Lift inst_f inst_a -> Lift inst_f inst_a -> bool :=
  fun x y => negb (Eq___Lift_op_zeze__ x y).

Program Instance Eq___Lift {f : Type -> Type} {a : Type}
  `{Data.Functor.Classes.Eq1 f} `{GHC.Base.Eq_ a}
   : GHC.Base.Eq_ (Lift f a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Lift_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Lift_op_zsze__ |}.

Local Definition Ord__Lift_compare {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : Lift inst_f inst_a -> Lift inst_f inst_a -> comparison :=
  Data.Functor.Classes.compare1.

Local Definition Ord__Lift_op_zl__ {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : Lift inst_f inst_a -> Lift inst_f inst_a -> bool :=
  fun x y => Ord__Lift_compare x y GHC.Base.== Lt.

Local Definition Ord__Lift_op_zlze__ {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : Lift inst_f inst_a -> Lift inst_f inst_a -> bool :=
  fun x y => Ord__Lift_compare x y GHC.Base./= Gt.

Local Definition Ord__Lift_op_zg__ {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : Lift inst_f inst_a -> Lift inst_f inst_a -> bool :=
  fun x y => Ord__Lift_compare x y GHC.Base.== Gt.

Local Definition Ord__Lift_op_zgze__ {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : Lift inst_f inst_a -> Lift inst_f inst_a -> bool :=
  fun x y => Ord__Lift_compare x y GHC.Base./= Lt.

Local Definition Ord__Lift_max {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : Lift inst_f inst_a -> Lift inst_f inst_a -> Lift inst_f inst_a :=
  fun x y => if Ord__Lift_op_zlze__ x y : bool then y else x.

Local Definition Ord__Lift_min {inst_f : Type -> Type} {inst_a : Type}
  `{Data.Functor.Classes.Ord1 inst_f} `{GHC.Base.Ord inst_a}
   : Lift inst_f inst_a -> Lift inst_f inst_a -> Lift inst_f inst_a :=
  fun x y => if Ord__Lift_op_zlze__ x y : bool then x else y.

Program Instance Ord__Lift {f : Type -> Type} {a : Type}
  `{Data.Functor.Classes.Ord1 f} `{GHC.Base.Ord a}
   : GHC.Base.Ord (Lift f a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zl____ := Ord__Lift_op_zl__ ;
           GHC.Base.op_zlze____ := Ord__Lift_op_zlze__ ;
           GHC.Base.op_zg____ := Ord__Lift_op_zg__ ;
           GHC.Base.op_zgze____ := Ord__Lift_op_zgze__ ;
           GHC.Base.compare__ := Ord__Lift_compare ;
           GHC.Base.max__ := Ord__Lift_max ;
           GHC.Base.min__ := Ord__Lift_min |}.

(* Skipping all instances of class `GHC.Read.Read', including
   `Control.Applicative.Lift.Read__Lift' *)

(* Skipping all instances of class `GHC.Show.Show', including
   `Control.Applicative.Lift.Show__Lift' *)

Local Definition Functor__Lift_fmap {inst_f : Type -> Type} `{(GHC.Base.Functor
   inst_f)}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> Lift inst_f a -> Lift inst_f b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Pure x => Pure (f x)
      | f, Other y => Other (GHC.Base.fmap f y)
      end.

Local Definition Functor__Lift_op_zlzd__ {inst_f : Type -> Type}
  `{(GHC.Base.Functor inst_f)}
   : forall {a : Type}, forall {b : Type}, a -> Lift inst_f b -> Lift inst_f a :=
  fun {a : Type} {b : Type} => Functor__Lift_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__Lift {f : Type -> Type} `{(GHC.Base.Functor f)}
   : GHC.Base.Functor (Lift f) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__Lift_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} => Functor__Lift_op_zlzd__ |}.

Local Definition Foldable__Lift_foldMap {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {m : Type},
     forall {a : Type},
     forall `{GHC.Base.Monoid m}, (a -> m) -> Lift inst_f a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Pure x => f x
      | f, Other y => Data.Foldable.foldMap f y
      end.

Local Definition Foldable__Lift_fold {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, Lift inst_f m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__Lift_foldMap GHC.Base.id.

Local Definition Foldable__Lift_foldl {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Lift inst_f a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__Lift_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                               (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                GHC.Base.flip f)) t)) z.

Local Definition Foldable__Lift_foldr {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Lift inst_f a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Foldable__Lift_foldMap
                                      (Coq.Program.Basics.compose Data.SemigroupInternal.Mk_Endo f) t) z.

Local Definition Foldable__Lift_foldl' {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {b : Type},
     forall {a : Type}, (b -> a -> b) -> b -> Lift inst_f a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in Foldable__Lift_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__Lift_foldr' {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Lift inst_f a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in Foldable__Lift_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__Lift_length {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, Lift inst_f a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__Lift_foldl' (fun arg_0__ arg_1__ =>
                             match arg_0__, arg_1__ with
                             | c, _ => c GHC.Num.+ #1
                             end) #0.

Local Definition Foldable__Lift_null {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, Lift inst_f a -> bool :=
  fun {a : Type} => Foldable__Lift_foldr (fun arg_0__ arg_1__ => false) true.

Local Definition Foldable__Lift_product {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Lift inst_f a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__Lift_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__Lift_sum {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, forall `{GHC.Num.Num a}, Lift inst_f a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum (Foldable__Lift_foldMap
                                Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__Lift_toList {inst_f : Type -> Type}
  `{(Data.Foldable.Foldable inst_f)}
   : forall {a : Type}, Lift inst_f a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__Lift_foldr c n t)).

Program Instance Foldable__Lift {f : Type -> Type} `{(Data.Foldable.Foldable f)}
   : Data.Foldable.Foldable (Lift f) :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m : Type} `{GHC.Base.Monoid m} =>
             Foldable__Lift_fold ;
           Data.Foldable.foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__Lift_foldMap ;
           Data.Foldable.foldl__ := fun {b : Type} {a : Type} => Foldable__Lift_foldl ;
           Data.Foldable.foldl'__ := fun {b : Type} {a : Type} => Foldable__Lift_foldl' ;
           Data.Foldable.foldr__ := fun {a : Type} {b : Type} => Foldable__Lift_foldr ;
           Data.Foldable.foldr'__ := fun {a : Type} {b : Type} => Foldable__Lift_foldr' ;
           Data.Foldable.length__ := fun {a : Type} => Foldable__Lift_length ;
           Data.Foldable.null__ := fun {a : Type} => Foldable__Lift_null ;
           Data.Foldable.product__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__Lift_product ;
           Data.Foldable.sum__ := fun {a : Type} `{GHC.Num.Num a} => Foldable__Lift_sum ;
           Data.Foldable.toList__ := fun {a : Type} => Foldable__Lift_toList |}.

Local Definition Traversable__Lift_traverse {inst_f : Type -> Type}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f},
     (a -> f b) -> Lift inst_f a -> f (Lift inst_f b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, Pure x => Pure Data.Functor.<$> f x
      | f, Other y => Other Data.Functor.<$> Data.Traversable.traverse f y
      end.

Local Definition Traversable__Lift_mapM {inst_f : Type -> Type}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m}, (a -> m b) -> Lift inst_f a -> m (Lift inst_f b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__Lift_traverse.

Local Definition Traversable__Lift_sequenceA {inst_f : Type -> Type}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f}, Lift inst_f (f a) -> f (Lift inst_f a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__Lift_traverse GHC.Base.id.

Local Definition Traversable__Lift_sequence {inst_f : Type -> Type}
  `{(Data.Traversable.Traversable inst_f)}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m}, Lift inst_f (m a) -> m (Lift inst_f a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__Lift_sequenceA.

Program Instance Traversable__Lift {f : Type -> Type}
  `{(Data.Traversable.Traversable f)}
   : Data.Traversable.Traversable (Lift f) :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Lift_mapM ;
           Data.Traversable.sequence__ := fun {m : Type -> Type}
           {a : Type}
           `{GHC.Base.Monad m} =>
             Traversable__Lift_sequence ;
           Data.Traversable.sequenceA__ := fun {f : Type -> Type}
           {a : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Lift_sequenceA ;
           Data.Traversable.traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__Lift_traverse |}.

Local Definition Applicative__Lift_op_zlztzg__ {inst_f : Type -> Type}
  `{(GHC.Base.Applicative inst_f)}
   : forall {a : Type},
     forall {b : Type}, Lift inst_f (a -> b) -> Lift inst_f a -> Lift inst_f b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Pure f, Pure x => Pure (f x)
      | Pure f, Other y => Other (f Data.Functor.<$> y)
      | Other f, Pure x => Other ((fun arg_4__ => arg_4__ x) Data.Functor.<$> f)
      | Other f, Other y => Other (f GHC.Base.<*> y)
      end.

Local Definition Applicative__Lift_liftA2 {inst_f : Type -> Type}
  `{(GHC.Base.Applicative inst_f)}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) -> Lift inst_f a -> Lift inst_f b -> Lift inst_f c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__Lift_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__Lift_op_ztzg__ {inst_f : Type -> Type}
  `{(GHC.Base.Applicative inst_f)}
   : forall {a : Type},
     forall {b : Type}, Lift inst_f a -> Lift inst_f b -> Lift inst_f b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 => Applicative__Lift_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__Lift_pure {inst_f : Type -> Type}
  `{(GHC.Base.Applicative inst_f)}
   : forall {a : Type}, a -> Lift inst_f a :=
  fun {a : Type} => Pure.

Program Instance Applicative__Lift {f : Type -> Type} `{(GHC.Base.Applicative
   f)}
   : GHC.Base.Applicative (Lift f) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__Lift_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Lift_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Lift_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__Lift_pure |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Control.Applicative.Lift.Alternative__Lift' *)

Definition unLift {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f}
   : Lift f a -> f a :=
  fun arg_0__ =>
    match arg_0__ with
    | Pure x => GHC.Base.pure x
    | Other e => e
    end.

Definition mapLift {f : Type -> Type} {a : Type} {g : Type -> Type}
   : (f a -> g a) -> Lift f a -> Lift g a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, Pure x => Pure x
    | f, Other e => Other (f e)
    end.

Definition elimLift {a : Type} {r : Type} {f : Type -> Type}
   : (a -> r) -> (f a -> r) -> Lift f a -> r :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | f, _, Pure x => f x
    | _, g, Other e => g e
    end.

Definition runErrors {e : Type} {a : Type}
   : Errors e a -> Data.Either.Either e a :=
  fun arg_0__ =>
    match arg_0__ with
    | Other (Data.Functor.Constant.Mk_Constant e) => Data.Either.Left e
    | Pure x => Data.Either.Right x
    end.

Definition failure {e : Type} {a : Type} : e -> Errors e a :=
  fun e => Other (Data.Functor.Constant.Mk_Constant e).

Definition eitherToErrors {e : Type} {a : Type}
   : Data.Either.Either e a -> Errors e a :=
  Data.Either.either failure Pure.

(* External variables:
     Gt Lt Type bool comparison false list negb true Coq.Program.Basics.compose
     Data.Either.Either Data.Either.Left Data.Either.Right Data.Either.either
     Data.Foldable.Foldable Data.Foldable.foldMap Data.Foldable.foldMap__
     Data.Foldable.fold__ Data.Foldable.foldl'__ Data.Foldable.foldl__
     Data.Foldable.foldr'__ Data.Foldable.foldr__ Data.Foldable.length__
     Data.Foldable.null__ Data.Foldable.product__ Data.Foldable.sum__
     Data.Foldable.toList__ Data.Functor.op_zlzdzg__ Data.Functor.Classes.Eq1
     Data.Functor.Classes.Ord1 Data.Functor.Classes.compare1 Data.Functor.Classes.eq1
     Data.Functor.Classes.liftCompare Data.Functor.Classes.liftCompare__
     Data.Functor.Classes.liftEq Data.Functor.Classes.liftEq__
     Data.Functor.Constant.Constant Data.Functor.Constant.Mk_Constant
     Data.SemigroupInternal.Mk_Dual Data.SemigroupInternal.Mk_Endo
     Data.SemigroupInternal.Mk_Product Data.SemigroupInternal.Mk_Sum
     Data.SemigroupInternal.appEndo Data.SemigroupInternal.getDual
     Data.SemigroupInternal.getProduct Data.SemigroupInternal.getSum
     Data.Traversable.Traversable Data.Traversable.mapM__
     Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse Data.Traversable.traverse__ GHC.Base.Applicative
     GHC.Base.Eq_ GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Ord
     GHC.Base.build' GHC.Base.compare__ GHC.Base.const GHC.Base.flip GHC.Base.fmap
     GHC.Base.fmap__ GHC.Base.id GHC.Base.liftA2__ GHC.Base.max__ GHC.Base.min__
     GHC.Base.op_z2218U__ GHC.Base.op_zeze__ GHC.Base.op_zeze____ GHC.Base.op_zg____
     GHC.Base.op_zgze____ GHC.Base.op_zl____ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____
     GHC.Base.op_zlze____ GHC.Base.op_zlztzg__ GHC.Base.op_zlztzg____
     GHC.Base.op_zsze__ GHC.Base.op_zsze____ GHC.Base.op_ztzg____ GHC.Base.pure
     GHC.Base.pure__ GHC.Num.Int GHC.Num.Num GHC.Num.fromInteger GHC.Num.op_zp__
*)
