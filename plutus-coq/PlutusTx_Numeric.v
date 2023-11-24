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

Require BinNums.
Require Data.SemigroupInternal.
Require GHC.Num.
Require PlutusTx_Bool.
Require PlutusTx_Monoid.
Require PlutusTx_Ord.
Require PlutusTx_Semigroup.
Import GHC.Num.Notations.
Import PlutusTx_Bool.Notations.
Import PlutusTx_Ord.Notations.
Import PlutusTx_Semigroup.Notations.

(* Converted type declarations: *)

Record MultiplicativeSemigroup__Dict (a : Type) :=
  MultiplicativeSemigroup__Dict_Build {
  op_zt____ : a -> a -> a }.

Definition MultiplicativeSemigroup (a : Type) :=
  forall r__, (MultiplicativeSemigroup__Dict a -> r__) -> r__.
Existing Class MultiplicativeSemigroup.

Record AdditiveGroup__Dict (a : Type) := AdditiveGroup__Dict_Build {
  op_zm____ : a -> a -> a }.

Definition op_zt__ `{g__0__ : MultiplicativeSemigroup a} : a -> a -> a :=
  g__0__ _ (op_zt____ a).

Notation "'_*_'" := (op_zt__).

Infix "*" := (_*_).

Record MultiplicativeMonoid__Dict (a : Type) :=
  MultiplicativeMonoid__Dict_Build {
  one__ : a }.

Definition MultiplicativeMonoid (a : Type) `{MultiplicativeSemigroup a} :=
  forall r__, (MultiplicativeMonoid__Dict a -> r__) -> r__.
Existing Class MultiplicativeMonoid.

Definition one `{g__0__ : MultiplicativeMonoid a} : a :=
  g__0__ _ (one__ a).

Inductive Multiplicative a : Type := | MkMultiplicative : a -> Multiplicative a.

Record AdditiveSemigroup__Dict (a : Type) := AdditiveSemigroup__Dict_Build {
  op_zp____ : a -> a -> a }.

Definition AdditiveSemigroup (a : Type) :=
  forall r__, (AdditiveSemigroup__Dict a -> r__) -> r__.
Existing Class AdditiveSemigroup.

Definition op_zp__ `{g__0__ : AdditiveSemigroup a} : a -> a -> a :=
  g__0__ _ (op_zp____ a).

Notation "'_+_'" := (op_zp__).

Infix "+" := (_+_).

Record AdditiveMonoid__Dict (a : Type) := AdditiveMonoid__Dict_Build {
  zero__ : a }.

Definition AdditiveMonoid (a : Type) `{AdditiveSemigroup a} :=
  forall r__, (AdditiveMonoid__Dict a -> r__) -> r__.
Existing Class AdditiveMonoid.

Definition zero `{g__0__ : AdditiveMonoid a} : a :=
  g__0__ _ (zero__ a).

Definition AdditiveGroup (a : Type) `{AdditiveMonoid a} :=
  forall r__, (AdditiveGroup__Dict a -> r__) -> r__.
Existing Class AdditiveGroup.

Definition op_zm__ `{g__0__ : AdditiveGroup a} : a -> a -> a :=
  g__0__ _ (op_zm____ a).

Notation "'_-_'" := (op_zm__).

Infix "-" := (_-_).

Inductive Additive a : Type := | MkAdditive : a -> Additive a.

Arguments MkMultiplicative {_} _.

Arguments MkAdditive {_} _.

(* Converted value declarations: *)

Local Definition AdditiveSemigroup__Additive_op_zp__ {inst_a : Type}
  `{PlutusTx_Semigroup.Semigroup inst_a}
   : Additive inst_a -> Additive inst_a -> Additive inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkAdditive a, MkAdditive b => MkAdditive (a PlutusTx_Semigroup.<> b)
    end.

Program Instance AdditiveSemigroup__Additive {a : Type}
  `{PlutusTx_Semigroup.Semigroup a}
   : AdditiveSemigroup (Additive a) :=
  fun _ k__ => k__ {| op_zp____ := AdditiveSemigroup__Additive_op_zp__ |}.

Local Definition AdditiveMonoid__Additive_zero {inst_a : Type}
  `{PlutusTx_Monoid.Monoid inst_a}
   : Additive inst_a :=
  MkAdditive PlutusTx_Monoid.mempty.

Program Instance AdditiveMonoid__Additive {a : Type} `{PlutusTx_Monoid.Monoid a}
   : AdditiveMonoid (Additive a) :=
  fun _ k__ => k__ {| zero__ := AdditiveMonoid__Additive_zero |}.

Local Definition AdditiveGroup__Additive_op_zm__ {inst_a : Type}
  `{PlutusTx_Monoid.Group inst_a}
   : Additive inst_a -> Additive inst_a -> Additive inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkAdditive a, MkAdditive b => MkAdditive (PlutusTx_Monoid.gsub a b)
    end.

Program Instance AdditiveGroup__Additive {a : Type} `{PlutusTx_Monoid.Group a}
   : AdditiveGroup (Additive a) :=
  fun _ k__ => k__ {| op_zm____ := AdditiveGroup__Additive_op_zm__ |}.

Local Definition MultiplicativeSemigroup__Multiplicative_op_zt__ {inst_a : Type}
  `{PlutusTx_Semigroup.Semigroup inst_a}
   : Multiplicative inst_a -> Multiplicative inst_a -> Multiplicative inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkMultiplicative a, MkMultiplicative b =>
        MkMultiplicative (a PlutusTx_Semigroup.<> b)
    end.

Program Instance MultiplicativeSemigroup__Multiplicative {a : Type}
  `{PlutusTx_Semigroup.Semigroup a}
   : MultiplicativeSemigroup (Multiplicative a) :=
  fun _ k__ =>
    k__ {| op_zt____ := MultiplicativeSemigroup__Multiplicative_op_zt__ |}.

Local Definition MultiplicativeMonoid__Multiplicative_one {inst_a : Type}
  `{PlutusTx_Monoid.Monoid inst_a}
   : Multiplicative inst_a :=
  MkMultiplicative PlutusTx_Monoid.mempty.

Program Instance MultiplicativeMonoid__Multiplicative {a : Type}
  `{PlutusTx_Monoid.Monoid a}
   : MultiplicativeMonoid (Multiplicative a) :=
  fun _ k__ => k__ {| one__ := MultiplicativeMonoid__Multiplicative_one |}.

Local Definition AdditiveSemigroup__Z_op_zp__
   : BinNums.Z -> BinNums.Z -> BinNums.Z :=
  Z.add.

Program Instance AdditiveSemigroup__Z : AdditiveSemigroup BinNums.Z :=
  fun _ k__ => k__ {| op_zp____ := AdditiveSemigroup__Z_op_zp__ |}.

Local Definition AdditiveMonoid__Z_zero : BinNums.Z :=
  #0.

Program Instance AdditiveMonoid__Z : AdditiveMonoid BinNums.Z :=
  fun _ k__ => k__ {| zero__ := AdditiveMonoid__Z_zero |}.

Local Definition AdditiveGroup__Z_op_zm__
   : BinNums.Z -> BinNums.Z -> BinNums.Z :=
  Z.sub.

Program Instance AdditiveGroup__Z : AdditiveGroup BinNums.Z :=
  fun _ k__ => k__ {| op_zm____ := AdditiveGroup__Z_op_zm__ |}.

Local Definition MultiplicativeSemigroup__Z_op_zt__
   : BinNums.Z -> BinNums.Z -> BinNums.Z :=
  Z.mul.

Program Instance MultiplicativeSemigroup__Z
   : MultiplicativeSemigroup BinNums.Z :=
  fun _ k__ => k__ {| op_zt____ := MultiplicativeSemigroup__Z_op_zt__ |}.

Local Definition MultiplicativeMonoid__Z_one : BinNums.Z :=
  #1.

Program Instance MultiplicativeMonoid__Z : MultiplicativeMonoid BinNums.Z :=
  fun _ k__ => k__ {| one__ := MultiplicativeMonoid__Z_one |}.

Local Definition AdditiveSemigroup__bool_op_zp__ : bool -> bool -> bool :=
  _PlutusTx_Bool.||_.

Program Instance AdditiveSemigroup__bool : AdditiveSemigroup bool :=
  fun _ k__ => k__ {| op_zp____ := AdditiveSemigroup__bool_op_zp__ |}.

Local Definition AdditiveMonoid__bool_zero : bool :=
  false.

Program Instance AdditiveMonoid__bool : AdditiveMonoid bool :=
  fun _ k__ => k__ {| zero__ := AdditiveMonoid__bool_zero |}.

Local Definition MultiplicativeSemigroup__bool_op_zt__ : bool -> bool -> bool :=
  _PlutusTx_Bool.&&_.

Program Instance MultiplicativeSemigroup__bool : MultiplicativeSemigroup bool :=
  fun _ k__ => k__ {| op_zt____ := MultiplicativeSemigroup__bool_op_zt__ |}.

Local Definition MultiplicativeMonoid__bool_one : bool :=
  true.

Program Instance MultiplicativeMonoid__bool : MultiplicativeMonoid bool :=
  fun _ k__ => k__ {| one__ := MultiplicativeMonoid__bool_one |}.

Local Definition Semigroup__Sum_op_zlzg__ {inst_a : Type} `{AdditiveSemigroup
  inst_a}
   : Data.SemigroupInternal.Sum inst_a ->
     Data.SemigroupInternal.Sum inst_a -> Data.SemigroupInternal.Sum inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Data.SemigroupInternal.Mk_Sum a, Data.SemigroupInternal.Mk_Sum b =>
        Data.SemigroupInternal.Mk_Sum (a + b)
    end.

Program Instance Semigroup__Sum {a : Type} `{AdditiveSemigroup a}
   : PlutusTx_Semigroup.Semigroup (Data.SemigroupInternal.Sum a) :=
  fun _ k__ =>
    k__ {| PlutusTx_Semigroup.op_zlzg____ := Semigroup__Sum_op_zlzg__ |}.

Local Definition Monoid__Sum_mempty {inst_a : Type} `{AdditiveMonoid inst_a}
   : Data.SemigroupInternal.Sum inst_a :=
  Data.SemigroupInternal.Mk_Sum zero.

Program Instance Monoid__Sum {a : Type} `{AdditiveMonoid a}
   : PlutusTx_Monoid.Monoid (Data.SemigroupInternal.Sum a) :=
  fun _ k__ => k__ {| PlutusTx_Monoid.mempty__ := Monoid__Sum_mempty |}.

Local Definition Semigroup__Product_op_zlzg__ {inst_a : Type}
  `{MultiplicativeSemigroup inst_a}
   : Data.SemigroupInternal.Product inst_a ->
     Data.SemigroupInternal.Product inst_a ->
     Data.SemigroupInternal.Product inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Data.SemigroupInternal.Mk_Product a, Data.SemigroupInternal.Mk_Product b =>
        Data.SemigroupInternal.Mk_Product (a * b)
    end.

Program Instance Semigroup__Product {a : Type} `{MultiplicativeSemigroup a}
   : PlutusTx_Semigroup.Semigroup (Data.SemigroupInternal.Product a) :=
  fun _ k__ =>
    k__ {| PlutusTx_Semigroup.op_zlzg____ := Semigroup__Product_op_zlzg__ |}.

Local Definition Monoid__Product_mempty {inst_a : Type} `{MultiplicativeMonoid
  inst_a}
   : Data.SemigroupInternal.Product inst_a :=
  Data.SemigroupInternal.Mk_Product one.

Program Instance Monoid__Product {a : Type} `{MultiplicativeMonoid a}
   : PlutusTx_Monoid.Monoid (Data.SemigroupInternal.Product a) :=
  fun _ k__ => k__ {| PlutusTx_Monoid.mempty__ := Monoid__Product_mempty |}.

Definition negate {a : Type} `{AdditiveGroup a} : a -> a :=
  fun x => zero - x.

Definition divMod : BinNums.Z -> BinNums.Z -> (BinNums.Z * BinNums.Z)%type :=
  fun x y => pair (Z.div x y) (Z.modulo x y).

Definition quotRem : BinNums.Z -> BinNums.Z -> (BinNums.Z * BinNums.Z)%type :=
  fun x y => pair (Z.quot x y) (Z.rem x y).

Definition abs {n : Type} `{PlutusTx_Ord.Ord n} `{AdditiveGroup n} : n -> n :=
  fun x => if x PlutusTx_Ord.< zero : bool then negate x else x.

Module Notations.
Notation "'_PlutusTx_Numeric.*_'" := (op_zt__).
Infix "PlutusTx_Numeric.*" := (_*_) (at level 99).
Notation "'_PlutusTx_Numeric.+_'" := (op_zp__).
Infix "PlutusTx_Numeric.+" := (_+_) (at level 99).
Notation "'_PlutusTx_Numeric.-_'" := (op_zm__).
Infix "PlutusTx_Numeric.-" := (_-_) (at level 99).
End Notations.

(* External variables:
     Type bool false pair true BinNums.Z Data.SemigroupInternal.Mk_Product
     Data.SemigroupInternal.Mk_Sum Data.SemigroupInternal.Product
     Data.SemigroupInternal.Sum GHC.Num.fromInteger PlutusTx_Bool.op_zaza__
     PlutusTx_Bool.op_zbzb__ PlutusTx_Monoid.Group PlutusTx_Monoid.Monoid
     PlutusTx_Monoid.gsub PlutusTx_Monoid.mempty PlutusTx_Monoid.mempty__
     PlutusTx_Ord.Ord PlutusTx_Ord.op_zl__ PlutusTx_Semigroup.Semigroup
     PlutusTx_Semigroup.op_zlzg__ PlutusTx_Semigroup.op_zlzg____ Z.add Z.div Z.modulo
     Z.mul Z.quot Z.rem Z.sub
*)
