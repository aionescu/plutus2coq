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

Require PlutusTx_Applicative.
Require PlutusTx_Base.
Require PlutusTx_Eq.
Require PlutusTx_Foldable.
Require PlutusTx_Functor.
Require PlutusTx_List.
Require PlutusTx_Maybe.
Require PlutusTx_Monoid.
Require PlutusTx_Semigroup.
Require PlutusTx_These.
Require PlutusTx_Traversable.
Import PlutusTx_Base.Notations.
Import PlutusTx_Eq.Notations.
Import PlutusTx_Functor.Notations.
Import PlutusTx_Semigroup.Notations.

(* Converted type declarations: *)

Inductive Map k v : Type := | MkMap (unMap : list (k * v)%type) : Map k v.

Arguments MkMap {_} {_} _.

Definition unMap {k} {v} (arg_0__ : Map k v) :=
  let 'MkMap unMap := arg_0__ in
  unMap.

(* Converted value declarations: *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusTx_AssocMap.ToData__Map' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusTx_AssocMap.FromData__Map' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusTx_AssocMap.UnsafeFromData__Map' *)

Axiom fmapAssocMap : forall {a} {b} {k}, (a -> b) -> Map k a -> Map k b.

Local Definition Functor__Map_fmap {inst_k : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> Map inst_k a -> Map inst_k b :=
  fun {a : Type} {b : Type} => fmapAssocMap.

Program Instance Functor__Map {k : Type} : PlutusTx_Functor.Functor (Map k) :=
  fun _ k__ =>
    k__ {| PlutusTx_Functor.fmap__ := fun {a : Type} {b : Type} =>
             Functor__Map_fmap |}.

Local Definition Foldable__Map_foldr {inst_k : Type}
   : forall {a : Type},
     forall {b : Type}, (a -> b -> b) -> b -> Map inst_k a -> b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ arg_2__ =>
      match arg_0__, arg_1__, arg_2__ with
      | f, z, MkMap mp =>
          PlutusTx_Foldable.foldr (f PlutusTx_Base.∘ PlutusTx_Base.snd) z mp
      end.

Program Instance Foldable__Map {k : Type}
   : PlutusTx_Foldable.Foldable (Map k) :=
  fun _ k__ =>
    k__ {| PlutusTx_Foldable.foldr__ := fun {a : Type} {b : Type} =>
             Foldable__Map_foldr |}.

Axiom traverseAssocMap : forall {f} {a} {b} {k},
                         forall `{PlutusTx_Applicative.Applicative f},
                         (a -> f b) -> Map k a -> f (Map k b).

Local Definition Traversable__Map_traverse {inst_k : Type}
   : forall {f : Type -> Type},
     forall {a : Type},
     forall {b : Type},
     forall `{PlutusTx_Applicative.Applicative f},
     (a -> f b) -> Map inst_k a -> f (Map inst_k b) :=
  fun {f : Type -> Type}
  {a : Type}
  {b : Type}
  `{PlutusTx_Applicative.Applicative f} =>
    traverseAssocMap.

Program Instance Traversable__Map {k : Type}
   : PlutusTx_Traversable.Traversable (Map k) :=
  fun _ k__ =>
    k__ {| PlutusTx_Traversable.traverse__ := fun {f : Type -> Type}
           {a : Type}
           {b : Type}
           `{PlutusTx_Applicative.Applicative f} =>
             Traversable__Map_traverse |}.

Axiom union : forall {k : Type},
              forall {v : Type},
              forall {r : Type},
              forall `{PlutusTx_Eq.Eq k},
              Map k v -> Map k r -> Map k (PlutusTx_These.These v r).

Definition unionWith {k : Type} {a : Type} `{PlutusTx_Eq.Eq k}
   : (a -> a -> a) -> Map k a -> Map k a -> Map k a :=
  fun merge ls rs =>
    PlutusTx_These.these PlutusTx_Base.id PlutusTx_Base.id merge
    PlutusTx_Functor.<$>
    union ls rs.

Local Definition Semigroup__Map_op_zlzg__ {inst_k : Type} {inst_v : Type}
  `{PlutusTx_Eq.Eq inst_k} `{PlutusTx_Semigroup.Semigroup inst_v}
   : Map inst_k inst_v -> Map inst_k inst_v -> Map inst_k inst_v :=
  unionWith _PlutusTx_Semigroup.<>_.

Program Instance Semigroup__Map {k : Type} {v : Type} `{PlutusTx_Eq.Eq k}
  `{PlutusTx_Semigroup.Semigroup v}
   : PlutusTx_Semigroup.Semigroup (Map k v) :=
  fun _ k__ =>
    k__ {| PlutusTx_Semigroup.op_zlzg____ := Semigroup__Map_op_zlzg__ |}.

Axiom empty : forall {k : Type}, forall {v : Type}, Map k v.

Local Definition Monoid__Map_mempty {inst_k : Type} {inst_v : Type}
  `{PlutusTx_Eq.Eq inst_k} `{PlutusTx_Semigroup.Semigroup inst_v}
   : Map inst_k inst_v :=
  empty.

Program Instance Monoid__Map {k : Type} {v : Type} `{PlutusTx_Eq.Eq k}
  `{PlutusTx_Semigroup.Semigroup v}
   : PlutusTx_Monoid.Monoid (Map k v) :=
  fun _ k__ => k__ {| PlutusTx_Monoid.mempty__ := Monoid__Map_mempty |}.

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusTx_AssocMap.Pretty__Map' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusTx_AssocMap.Lift__DefaultUni__Map' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusTx_AssocMap.Typeable__DefaultUni__Map' *)

Definition fromList {k : Type} {v : Type} : list (k * v)%type -> Map k v :=
  MkMap.

Definition insert {k : Type} {v : Type} `{PlutusTx_Eq.Eq k}
   : k -> v -> Map k v -> Map k v :=
  fun k v m =>
    unionWith (fun arg_0__ arg_1__ => match arg_0__, arg_1__ with | _, b => b end) m
    (fromList (cons (pair k v) nil)).

Definition fromListSafe {k : Type} {v : Type} `{PlutusTx_Eq.Eq k}
   : list (k * v)%type -> Map k v :=
  PlutusTx_Foldable.foldr (PlutusTx_Base.uncurry insert) empty.

Definition toList {k : Type} {v : Type} : Map k v -> list (k * v)%type :=
  fun '(MkMap l) => l.

Definition lookup {k : Type} {v : Type} `{PlutusTx_Eq.Eq k}
   : k -> Map k v -> option v :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | c, MkMap xs =>
        let go : list (k * v)%type -> option v :=
          fix go (arg_2__ : list (k * v)%type) : option v
            := match arg_2__ with
               | nil => None
               | cons (pair c' i) xs' => if c' PlutusTx_Eq.== c : bool then Some i else go xs'
               end in
        go xs
    end.

Definition member {k : Type} {v : Type} `{PlutusTx_Eq.Eq k}
   : k -> Map k v -> bool :=
  fun k m => PlutusTx_Maybe.isJust (lookup k m).

Definition delete {k : Type} {v : Type} `{PlutusTx_Eq.Eq k}
   : k -> Map k v -> Map k v :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | key, MkMap ls =>
        let fix go arg_2__
          := match arg_2__ with
             | nil => nil
             | cons (pair k v) rest =>
                 if k PlutusTx_Eq.== key : bool then rest else
                 cons (pair k v) (go rest)
             end in
        MkMap (go ls)
    end.

Axiom keys : forall {k : Type}, forall {v : Type}, Map k v -> list k.

Definition mapThese {v : Type} {a : Type} {b : Type} {k : Type}
   : (v -> PlutusTx_These.These a b) -> Map k v -> (Map k a * Map k b)%type :=
  fun f mps =>
    let f' :=
      fun arg_0__ arg_1__ =>
        match arg_0__, arg_1__ with
        | pair k v, pair as_ bs =>
            match v with
            | PlutusTx_These.This a => pair (cons (pair k a) as_) bs
            | PlutusTx_These.That b => pair as_ (cons (pair k b) bs)
            | PlutusTx_These.MkThese a b => pair (cons (pair k a) as_) (cons (pair k b) bs)
            end
        end in
    let 'MkMap mps' := PlutusTx_Functor.fmap f mps in
    let 'pair mpl mpr := PlutusTx_Foldable.foldr f' (pair nil nil) mps' in
    pair (MkMap mpl) (MkMap mpr).

Definition singleton {k : Type} {v : Type} : k -> v -> Map k v :=
  fun c i => MkMap (cons (pair c i) nil).

Definition null {k : Type} {v : Type} : Map k v -> bool :=
  PlutusTx_List.null PlutusTx_Base.∘ unMap.

Definition filter {v : Type} {k : Type} : (v -> bool) -> Map k v -> Map k v :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, MkMap m =>
        MkMap PlutusTx_Base.$
        PlutusTx_List.filter (f PlutusTx_Base.∘ PlutusTx_Base.snd) m
    end.

Axiom elems : forall {k : Type}, forall {v : Type}, Map k v -> list v.

Definition mapWithKey {k : Type} {a : Type} {b : Type}
   : (k -> a -> b) -> Map k a -> Map k b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, MkMap xs =>
        MkMap PlutusTx_Base.$
        PlutusTx_Functor.fmap (fun '(pair k v) => pair k (f k v)) xs
    end.

Definition mapMaybe {a : Type} {b : Type} {k : Type}
   : (a -> option b) -> Map k a -> Map k b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, MkMap xs =>
        MkMap PlutusTx_Base.$
        PlutusTx_Maybe.mapMaybe (fun '(pair k v) =>
                                   (fun arg_3__ => pair k arg_3__) PlutusTx_Functor.<$> f v) xs
    end.

Definition mapMaybeWithKey {k : Type} {a : Type} {b : Type}
   : (k -> a -> option b) -> Map k a -> Map k b :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, MkMap xs =>
        MkMap PlutusTx_Base.$
        PlutusTx_Maybe.mapMaybe (fun '(pair k v) =>
                                   (fun arg_3__ => pair k arg_3__) PlutusTx_Functor.<$> f k v) xs
    end.

Definition all {a : Type} {k : Type} : (a -> bool) -> Map k a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | f, MkMap m =>
        let fix go arg_2__
          := match arg_2__ with
             | nil => true
             | cons (pair _ x) xs => if f x : bool then go xs else false
             end in
        go m
    end.

(* External variables:
     None Some Type bool cons false list nil op_zt__ option pair true
     PlutusTx_Applicative.Applicative PlutusTx_Base.id PlutusTx_Base.op_z2218U__
     PlutusTx_Base.op_zd__ PlutusTx_Base.snd PlutusTx_Base.uncurry PlutusTx_Eq.Eq
     PlutusTx_Eq.op_zeze__ PlutusTx_Foldable.Foldable PlutusTx_Foldable.foldr
     PlutusTx_Foldable.foldr__ PlutusTx_Functor.Functor PlutusTx_Functor.fmap
     PlutusTx_Functor.fmap__ PlutusTx_Functor.op_zlzdzg__ PlutusTx_List.filter
     PlutusTx_List.null PlutusTx_Maybe.isJust PlutusTx_Maybe.mapMaybe
     PlutusTx_Monoid.Monoid PlutusTx_Monoid.mempty__ PlutusTx_Semigroup.Semigroup
     PlutusTx_Semigroup.op_zlzg__ PlutusTx_Semigroup.op_zlzg____
     PlutusTx_These.MkThese PlutusTx_These.That PlutusTx_These.These
     PlutusTx_These.This PlutusTx_These.these PlutusTx_Traversable.Traversable
     PlutusTx_Traversable.traverse__
*)
