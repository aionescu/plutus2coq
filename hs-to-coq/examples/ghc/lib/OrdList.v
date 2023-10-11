(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Coq.Init.Datatypes.
Require Coq.Program.Basics.
Require Data.Foldable.
Require Data.Functor.
Require Data.SemigroupInternal.
Require Data.Traversable.
Require GHC.Base.
Require GHC.Num.
Import Data.Functor.Notations.
Import GHC.Base.Notations.
Import GHC.Num.Notations.

(* Converted type declarations: *)

Inductive OrdList a : Type :=
  | None : OrdList a
  | One : a -> OrdList a
  | Many : list a -> OrdList a
  | Cons : a -> (OrdList a) -> OrdList a
  | Snoc : (OrdList a) -> a -> OrdList a
  | Two : (OrdList a) -> (OrdList a) -> OrdList a.

Arguments None {_}.

Arguments One {_} _.

Arguments Many {_} _.

Arguments Cons {_} _ _.

Arguments Snoc {_} _ _.

Arguments Two {_} _ _.

(* Converted value declarations: *)

(* Skipping all instances of class `Outputable.Outputable', including
   `OrdList.Outputable__OrdList' *)

Definition appOL {a : Type} : OrdList a -> OrdList a -> OrdList a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | None, b => b
    | a, None => a
    | One a, b => Cons a b
    | a, One b => Snoc a b
    | a, b => Two a b
    end.

Local Definition Semigroup__OrdList_op_zlzlzgzg__ {inst_a : Type}
   : OrdList inst_a -> OrdList inst_a -> OrdList inst_a :=
  appOL.

Program Instance Semigroup__OrdList {a : Type}
   : GHC.Base.Semigroup (OrdList a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zlzlzgzg____ := Semigroup__OrdList_op_zlzlzgzg__ |}.

Local Definition Monoid__OrdList_mappend {inst_a : Type}
   : OrdList inst_a -> OrdList inst_a -> OrdList inst_a :=
  _GHC.Base.<<>>_.

Definition concatOL {a : Type} : list (OrdList a) -> OrdList a :=
  fun aas => Data.Foldable.foldr appOL None aas.

Local Definition Monoid__OrdList_mconcat {inst_a : Type}
   : list (OrdList inst_a) -> OrdList inst_a :=
  concatOL.

Definition nilOL {a : Type} : OrdList a :=
  None.

Local Definition Monoid__OrdList_mempty {inst_a : Type} : OrdList inst_a :=
  nilOL.

Program Instance Monoid__OrdList {a : Type} : GHC.Base.Monoid (OrdList a) :=
  fun _ k__ =>
    k__ {| GHC.Base.mappend__ := Monoid__OrdList_mappend ;
           GHC.Base.mconcat__ := Monoid__OrdList_mconcat ;
           GHC.Base.mempty__ := Monoid__OrdList_mempty |}.

Fixpoint mapOL {a : Type} {b : Type} (arg_0__ : a -> b) (arg_1__ : OrdList a)
  : OrdList b
  := match arg_0__, arg_1__ with
     | _, None => None
     | f, One x => One (f x)
     | f, Cons x xs => Cons (f x) (mapOL f xs)
     | f, Snoc xs x => Snoc (mapOL f xs) (f x)
     | f, Two x y => Two (mapOL f x) (mapOL f y)
     | f, Many xs => Many (GHC.Base.map f xs)
     end.

Local Definition Functor__OrdList_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> OrdList a -> OrdList b :=
  fun {a : Type} {b : Type} => mapOL.

Local Definition Functor__OrdList_op_zlzd__
   : forall {a : Type}, forall {b : Type}, a -> OrdList b -> OrdList a :=
  fun {a : Type} {b : Type} => Functor__OrdList_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__OrdList : GHC.Base.Functor OrdList :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__OrdList_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} =>
             Functor__OrdList_op_zlzd__ |}.

Fixpoint foldrOL {a : Type} {b : Type} (arg_0__ : a -> b -> b) (arg_1__ : b)
                 (arg_2__ : OrdList a) : b
  := match arg_0__, arg_1__, arg_2__ with
     | _, z, None => z
     | k, z, One x => k x z
     | k, z, Cons x xs => k x (foldrOL k z xs)
     | k, z, Snoc xs x => foldrOL k (k x z) xs
     | k, z, Two b1 b2 => foldrOL k (foldrOL k z b2) b1
     | k, z, Many xs => Data.Foldable.foldr k z xs
     end.

Local Definition Foldable__OrdList_foldr
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> OrdList a -> b :=
  fun {a : Type} {b : Type} => foldrOL.

Local Definition Foldable__OrdList_foldMap
   : forall {m : Type},
     forall {a : Type}, forall `{GHC.Base.Monoid m}, (a -> m) -> OrdList a -> m :=
  fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
    fun f =>
      Foldable__OrdList_foldr (GHC.Base.mappend GHC.Base.∘ f) GHC.Base.mempty.

Local Definition Foldable__OrdList_fold
   : forall {m : Type}, forall `{GHC.Base.Monoid m}, OrdList m -> m :=
  fun {m : Type} `{GHC.Base.Monoid m} => Foldable__OrdList_foldMap GHC.Base.id.

Local Definition Foldable__OrdList_foldl
   : forall {b : Type}, forall {a : Type}, (b -> a -> b) -> b -> OrdList a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z t =>
      Data.SemigroupInternal.appEndo (Data.SemigroupInternal.getDual
                                      (Foldable__OrdList_foldMap (Data.SemigroupInternal.Mk_Dual GHC.Base.∘
                                                                  (Data.SemigroupInternal.Mk_Endo GHC.Base.∘
                                                                   GHC.Base.flip f)) t)) z.

Local Definition Foldable__OrdList_foldl'
   : forall {b : Type}, forall {a : Type}, (b -> a -> b) -> b -> OrdList a -> b :=
  fun {b : Type} {a : Type} =>
    fun f z0 xs =>
      let f' := fun x k z => k (f z x) in
      Foldable__OrdList_foldr f' GHC.Base.id xs z0.

Local Definition Foldable__OrdList_foldr'
   : forall {a : Type}, forall {b : Type}, (a -> b -> b) -> b -> OrdList a -> b :=
  fun {a : Type} {b : Type} =>
    fun f z0 xs =>
      let f' := fun k x z => k (f x z) in
      Foldable__OrdList_foldl f' GHC.Base.id xs z0.

Local Definition Foldable__OrdList_length
   : forall {a : Type}, OrdList a -> GHC.Num.Int :=
  fun {a : Type} =>
    Foldable__OrdList_foldl' (fun arg_0__ arg_1__ =>
                                match arg_0__, arg_1__ with
                                | c, _ => c GHC.Num.+ #1
                                end) #0.

Local Definition Foldable__OrdList_null
   : forall {a : Type}, OrdList a -> bool :=
  fun {a : Type} => Foldable__OrdList_foldr (fun arg_0__ arg_1__ => false) true.

Local Definition Foldable__OrdList_product
   : forall {a : Type}, forall `{GHC.Num.Num a}, OrdList a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getProduct
                               (Foldable__OrdList_foldMap Data.SemigroupInternal.Mk_Product).

Local Definition Foldable__OrdList_sum
   : forall {a : Type}, forall `{GHC.Num.Num a}, OrdList a -> a :=
  fun {a : Type} `{GHC.Num.Num a} =>
    Coq.Program.Basics.compose Data.SemigroupInternal.getSum
                               (Foldable__OrdList_foldMap Data.SemigroupInternal.Mk_Sum).

Local Definition Foldable__OrdList_toList
   : forall {a : Type}, OrdList a -> list a :=
  fun {a : Type} =>
    fun t => GHC.Base.build' (fun _ => (fun c n => Foldable__OrdList_foldr c n t)).

Program Instance Foldable__OrdList : Data.Foldable.Foldable OrdList :=
  fun _ k__ =>
    k__ {| Data.Foldable.fold__ := fun {m : Type} `{GHC.Base.Monoid m} =>
             Foldable__OrdList_fold ;
           Data.Foldable.foldMap__ := fun {m : Type} {a : Type} `{GHC.Base.Monoid m} =>
             Foldable__OrdList_foldMap ;
           Data.Foldable.foldl__ := fun {b : Type} {a : Type} => Foldable__OrdList_foldl ;
           Data.Foldable.foldl'__ := fun {b : Type} {a : Type} =>
             Foldable__OrdList_foldl' ;
           Data.Foldable.foldr__ := fun {a : Type} {b : Type} => Foldable__OrdList_foldr ;
           Data.Foldable.foldr'__ := fun {a : Type} {b : Type} =>
             Foldable__OrdList_foldr' ;
           Data.Foldable.length__ := fun {a : Type} => Foldable__OrdList_length ;
           Data.Foldable.null__ := fun {a : Type} => Foldable__OrdList_null ;
           Data.Foldable.product__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__OrdList_product ;
           Data.Foldable.sum__ := fun {a : Type} `{GHC.Num.Num a} =>
             Foldable__OrdList_sum ;
           Data.Foldable.toList__ := fun {a : Type} => Foldable__OrdList_toList |}.

Definition fromOL {a : Type} : OrdList a -> list a :=
  fun a =>
    let fix go arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | None, acc => acc
         | One a, acc => cons a acc
         | Cons a b, acc => cons a (go b acc)
         | Snoc a b, acc => go a (cons b acc)
         | Two a b, acc => go a (go b acc)
         | Many xs, acc => Coq.Init.Datatypes.app xs acc
         end in
    go a nil.

Definition toOL {a : Type} : list a -> OrdList a :=
  fun arg_0__ => match arg_0__ with | nil => None | xs => Many xs end.

Local Definition Traversable__OrdList_traverse
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Applicative f}, (a -> f b) -> OrdList a -> f (OrdList b) :=
  fun {f : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Applicative f} =>
    fun f xs => toOL Data.Functor.<$> Data.Traversable.traverse f (fromOL xs).

Local Definition Traversable__OrdList_mapM
   : forall {m : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{GHC.Base.Monad m}, (a -> m b) -> OrdList a -> m (OrdList b) :=
  fun {m : Type -> Type} {a : Type} {b : Type} `{GHC.Base.Monad m} =>
    Traversable__OrdList_traverse.

Local Definition Traversable__OrdList_sequenceA
   : forall {f : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Applicative f}, OrdList (f a) -> f (OrdList a) :=
  fun {f : Type -> Type} {a : Type} `{GHC.Base.Applicative f} =>
    Traversable__OrdList_traverse GHC.Base.id.

Local Definition Traversable__OrdList_sequence
   : forall {m : Type -> Type},
     forall {a : Type}, forall `{GHC.Base.Monad m}, OrdList (m a) -> m (OrdList a) :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    Traversable__OrdList_sequenceA.

Program Instance Traversable__OrdList : Data.Traversable.Traversable OrdList :=
  fun _ k__ =>
    k__ {| Data.Traversable.mapM__ := fun {m : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Monad m} =>
             Traversable__OrdList_mapM ;
           Data.Traversable.sequence__ := fun {m : Type -> Type}
           {a : Type}
           `{GHC.Base.Monad m} =>
             Traversable__OrdList_sequence ;
           Data.Traversable.sequenceA__ := fun {f : Type -> Type}
           {a : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__OrdList_sequenceA ;
           Data.Traversable.traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{GHC.Base.Applicative f} =>
             Traversable__OrdList_traverse |}.

Definition unitOL {a : Type} : a -> OrdList a :=
  fun as_ => One as_.

Definition snocOL {a : Type} : OrdList a -> a -> OrdList a :=
  fun as_ b => Snoc as_ b.

Definition consOL {a : Type} : a -> OrdList a -> OrdList a :=
  fun a bs => Cons a bs.

(* Skipping definition `OrdList.lastOL' *)

Definition isNilOL {a : Type} : OrdList a -> bool :=
  fun arg_0__ => match arg_0__ with | None => true | _ => false end.

Fixpoint foldlOL {b : Type} {a : Type} (arg_0__ : b -> a -> b) (arg_1__ : b)
                 (arg_2__ : OrdList a) : b
  := match arg_0__, arg_1__, arg_2__ with
     | _, z, None => z
     | k, z, One x => k z x
     | k, z, Cons x xs => foldlOL k (k z x) xs
     | k, z, Snoc xs x => k (foldlOL k z xs) x
     | k, z, Two b1 b2 => foldlOL k (foldlOL k z b1) b2
     | k, z, Many xs => Data.Foldable.foldl k z xs
     end.

(* External variables:
     Type bool cons false list nil true Coq.Init.Datatypes.app
     Coq.Program.Basics.compose Data.Foldable.Foldable Data.Foldable.foldMap__
     Data.Foldable.fold__ Data.Foldable.foldl Data.Foldable.foldl'__
     Data.Foldable.foldl__ Data.Foldable.foldr Data.Foldable.foldr'__
     Data.Foldable.foldr__ Data.Foldable.length__ Data.Foldable.null__
     Data.Foldable.product__ Data.Foldable.sum__ Data.Foldable.toList__
     Data.Functor.op_zlzdzg__ Data.SemigroupInternal.Mk_Dual
     Data.SemigroupInternal.Mk_Endo Data.SemigroupInternal.Mk_Product
     Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.appEndo
     Data.SemigroupInternal.getDual Data.SemigroupInternal.getProduct
     Data.SemigroupInternal.getSum Data.Traversable.Traversable
     Data.Traversable.mapM__ Data.Traversable.sequenceA__ Data.Traversable.sequence__
     Data.Traversable.traverse Data.Traversable.traverse__ GHC.Base.Applicative
     GHC.Base.Functor GHC.Base.Monad GHC.Base.Monoid GHC.Base.Semigroup
     GHC.Base.build' GHC.Base.const GHC.Base.flip GHC.Base.fmap__ GHC.Base.id
     GHC.Base.map GHC.Base.mappend GHC.Base.mappend__ GHC.Base.mconcat__
     GHC.Base.mempty GHC.Base.mempty__ GHC.Base.op_z2218U__ GHC.Base.op_zlzd____
     GHC.Base.op_zlzlzgzg__ GHC.Base.op_zlzlzgzg____ GHC.Num.Int GHC.Num.Num
     GHC.Num.fromInteger GHC.Num.op_zp__
*)
