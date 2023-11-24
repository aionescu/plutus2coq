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
Require PlutusTx_Base.
Require PlutusTx_Functor.
Require PlutusTx_List.
Require PlutusTx_Monoid.
Import PlutusTx_Functor.Notations.

(* Converted type declarations: *)

Record Applicative__Dict (f : Type -> Type) := Applicative__Dict_Build {
  op_zlztzg____ : forall {a : Type}, forall {b : Type}, f (a -> b) -> f a -> f b ;
  pure__ : forall {a : Type}, a -> f a }.

Definition Applicative (f : Type -> Type) `{PlutusTx_Functor.Functor f} :=
  forall r__, (Applicative__Dict f -> r__) -> r__.
Existing Class Applicative.

Definition op_zlztzg__ `{g__0__ : Applicative f}
   : forall {a : Type}, forall {b : Type}, f (a -> b) -> f a -> f b :=
  g__0__ _ (op_zlztzg____ f).

Definition pure `{g__0__ : Applicative f} : forall {a : Type}, a -> f a :=
  g__0__ _ (pure__ f).

Notation "'_<*>_'" := (op_zlztzg__).

Infix "<*>" := (_<*>_) (at level 99).

(* Converted value declarations: *)

Local Definition Applicative__option_op_zlztzg__
   : forall {a : Type},
     forall {b : Type}, option (a -> b) -> option a -> option b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | None, _ => None
      | _, None => None
      | Some f, Some x => Some (f x)
      end.

Local Definition Applicative__option_pure : forall {a : Type}, a -> option a :=
  fun {a : Type} => Some.

Program Instance Applicative__option : Applicative option :=
  fun _ k__ =>
    k__ {| op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__option_op_zlztzg__ ;
           pure__ := fun {a : Type} => Applicative__option_pure |}.

Local Definition Applicative__Either_op_zlztzg__ {inst_a : Type}
   : forall {a : Type},
     forall {b : Type},
     Data.Either.Either inst_a (a -> b) ->
     Data.Either.Either inst_a a -> Data.Either.Either inst_a b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Data.Either.Left e, _ => Data.Either.Left e
      | Data.Either.Right f, r => PlutusTx_Functor.fmap f r
      end.

Local Definition Applicative__Either_pure {inst_a : Type}
   : forall {a : Type}, a -> Data.Either.Either inst_a a :=
  fun {a : Type} => Data.Either.Right.

Program Instance Applicative__Either {a : Type}
   : Applicative (Data.Either.Either a) :=
  fun _ k__ =>
    k__ {| op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Either_op_zlztzg__ ;
           pure__ := fun {a : Type} => Applicative__Either_pure |}.

Local Definition Applicative__list_op_zlztzg__
   : forall {a : Type}, forall {b : Type}, list (a -> b) -> list a -> list b :=
  fun {a : Type} {b : Type} =>
    fun fs xs => PlutusTx_List.concatMap (fun f => PlutusTx_List.map f xs) fs.

Local Definition Applicative__list_pure : forall {a : Type}, a -> list a :=
  fun {a : Type} => fun x => cons x nil.

Program Instance Applicative__list : Applicative list :=
  fun _ k__ =>
    k__ {| op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__list_op_zlztzg__ ;
           pure__ := fun {a : Type} => Applicative__list_pure |}.

Local Definition Applicative__Identity_op_zlztzg__
   : forall {a : Type},
     forall {b : Type},
     Data.Functor.Identity.Identity (a -> b) ->
     Data.Functor.Identity.Identity a -> Data.Functor.Identity.Identity b :=
  fun {a : Type} {b : Type} =>
    GHC.Prim.coerce (PlutusTx_Base.id : (a -> b) -> a -> b).

Local Definition Applicative__Identity_pure
   : forall {a : Type}, a -> Data.Functor.Identity.Identity a :=
  fun {a : Type} => Data.Functor.Identity.Mk_Identity.

Program Instance Applicative__Identity
   : Applicative Data.Functor.Identity.Identity :=
  fun _ k__ =>
    k__ {| op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Identity_op_zlztzg__ ;
           pure__ := fun {a : Type} => Applicative__Identity_pure |}.

Local Definition Applicative__Const_op_zlztzg__ {inst_m : Type}
  `{PlutusTx_Monoid.Monoid inst_m}
   : forall {a : Type},
     forall {b : Type},
     Data.Functor.Const.Const inst_m (a -> b) ->
     Data.Functor.Const.Const inst_m a -> Data.Functor.Const.Const inst_m b :=
  fun {a : Type} {b : Type} =>
    GHC.Prim.coerce (PlutusTx_Monoid.mappend : inst_m -> inst_m -> inst_m).

Local Definition Applicative__Const_pure {inst_m : Type}
  `{PlutusTx_Monoid.Monoid inst_m}
   : forall {a : Type}, a -> Data.Functor.Const.Const inst_m a :=
  fun {a : Type} =>
    fun arg_0__ => Data.Functor.Const.Mk_Const PlutusTx_Monoid.mempty.

Program Instance Applicative__Const {m : Type} `{PlutusTx_Monoid.Monoid m}
   : Applicative (Data.Functor.Const.Const m) :=
  fun _ k__ =>
    k__ {| op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__Const_op_zlztzg__ ;
           pure__ := fun {a : Type} => Applicative__Const_pure |}.

Definition liftA2 {f : Type -> Type} {a : Type} {b : Type} {c : Type}
  `{Applicative f}
   : (a -> b -> c) -> f a -> f b -> f c :=
  fun f x => _<*>_ (PlutusTx_Functor.fmap f x).

Definition op_ztzg__ {f : Type -> Type} {a : Type} {b : Type} `{Applicative f}
   : f a -> f b -> f b :=
  fun a1 a2 => (PlutusTx_Base.id PlutusTx_Functor.<$ a1) <*> a2.

Notation "'_*>_'" := (op_ztzg__).

Infix "*>" := (_*>_) (at level 99).

Definition op_zlzt__ {f : Type -> Type} {a : Type} {b : Type} `{Applicative f}
   : f a -> f b -> f a :=
  liftA2 PlutusTx_Base.const.

Notation "'_<*_'" := (op_zlzt__).

Infix "<*" := (_<*_) (at level 99).

Definition unless {f : Type -> Type} `{Applicative f}
   : bool -> f unit -> f unit :=
  fun p s => if p : bool then pure tt else s.

Module Notations.
Notation "'_PlutusTx_Applicative.<*>_'" := (op_zlztzg__).
Infix "PlutusTx_Applicative.<*>" := (_<*>_) (at level 99).
Notation "'_PlutusTx_Applicative.*>_'" := (op_ztzg__).
Infix "PlutusTx_Applicative.*>" := (_*>_) (at level 99).
Notation "'_PlutusTx_Applicative.<*_'" := (op_zlzt__).
Infix "PlutusTx_Applicative.<*" := (_<*_) (at level 99).
End Notations.

(* External variables:
     None Some Type bool cons list nil option tt unit Data.Either.Either
     Data.Either.Left Data.Either.Right Data.Functor.Const.Const
     Data.Functor.Const.Mk_Const Data.Functor.Identity.Identity
     Data.Functor.Identity.Mk_Identity GHC.Prim.coerce PlutusTx_Base.const
     PlutusTx_Base.id PlutusTx_Functor.Functor PlutusTx_Functor.fmap
     PlutusTx_Functor.op_zlzd__ PlutusTx_List.concatMap PlutusTx_List.map
     PlutusTx_Monoid.Monoid PlutusTx_Monoid.mappend PlutusTx_Monoid.mempty
*)
