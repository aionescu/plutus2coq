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
Require GHC.Num.
Require GHC.Real.
Require PlutusTx_Base.
Require PlutusTx_Bool.
Require PlutusTx_Eq.
Require PlutusTx_ErrorCodes.
Require PlutusTx_Numeric.
Require PlutusTx_Ord.
Require PlutusTx_Trace.
Import GHC.Num.Notations.
Import PlutusTx_Base.Notations.
Import PlutusTx_Bool.Notations.
Import PlutusTx_Eq.Notations.
Import PlutusTx_Numeric.Notations.
Import PlutusTx_Ord.Notations.

(* Converted type declarations: *)

Inductive Rational : Type := | MkRational : BinNums.Z -> BinNums.Z -> Rational.

(* Converted value declarations: *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusTx_Ratio.Pretty__Rational' *)

Local Definition Eq__Rational_op_zeze__ : Rational -> Rational -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkRational n d, MkRational n' d' =>
        (n PlutusTx_Eq.== n') PlutusTx_Bool.&& (d PlutusTx_Eq.== d')
    end.

Program Instance Eq__Rational : PlutusTx_Eq.Eq Rational :=
  fun _ k__ => k__ {| PlutusTx_Eq.op_zeze____ := Eq__Rational_op_zeze__ |}.

Local Definition Ord__Rational_compare : Rational -> Rational -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkRational n d, MkRational n' d' =>
        PlutusTx_Ord.compare (n PlutusTx_Numeric.* d') (n' PlutusTx_Numeric.* d)
    end.

Local Definition Ord__Rational_op_zlze__ : Rational -> Rational -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkRational n d, MkRational n' d' =>
        (n PlutusTx_Numeric.* d') PlutusTx_Ord.<= (n' PlutusTx_Numeric.* d)
    end.

Local Definition Ord__Rational_max : Rational -> Rational -> Rational :=
  fun x y => if Ord__Rational_op_zlze__ x y : bool then y else x.

Local Definition Ord__Rational_min : Rational -> Rational -> Rational :=
  fun x y => if Ord__Rational_op_zlze__ x y : bool then x else y.

Local Definition Ord__Rational_op_zg__ : Rational -> Rational -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkRational n d, MkRational n' d' =>
        (n PlutusTx_Numeric.* d') PlutusTx_Ord.> (n' PlutusTx_Numeric.* d)
    end.

Local Definition Ord__Rational_op_zgze__ : Rational -> Rational -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkRational n d, MkRational n' d' =>
        (n PlutusTx_Numeric.* d') PlutusTx_Ord.>= (n' PlutusTx_Numeric.* d)
    end.

Local Definition Ord__Rational_op_zl__ : Rational -> Rational -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkRational n d, MkRational n' d' =>
        (n PlutusTx_Numeric.* d') PlutusTx_Ord.< (n' PlutusTx_Numeric.* d)
    end.

Program Instance Ord__Rational : PlutusTx_Ord.Ord Rational :=
  fun _ k__ =>
    k__ {| PlutusTx_Ord.compare__ := Ord__Rational_compare ;
           PlutusTx_Ord.max__ := Ord__Rational_max ;
           PlutusTx_Ord.min__ := Ord__Rational_min ;
           PlutusTx_Ord.op_zg____ := Ord__Rational_op_zg__ ;
           PlutusTx_Ord.op_zgze____ := Ord__Rational_op_zgze__ ;
           PlutusTx_Ord.op_zl____ := Ord__Rational_op_zl__ ;
           PlutusTx_Ord.op_zlze____ := Ord__Rational_op_zlze__ |}.

(* Skipping all instances of class `GHC.Base.Ord', including
   `PlutusTx_Ratio.Ord__Rational' *)

Axiom euclid : BinNums.Z -> BinNums.Z -> BinNums.Z.

Local Definition AdditiveSemigroup__Rational_op_zp__
   : Rational -> Rational -> Rational :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkRational n d, MkRational n' d' =>
        let newDen := d PlutusTx_Numeric.* d' in
        let newNum :=
          (n PlutusTx_Numeric.* d') PlutusTx_Numeric.+ (n' PlutusTx_Numeric.* d) in
        let gcd' := euclid newNum newDen in
        MkRational (Z.quot newNum gcd') (Z.quot newDen gcd')
    end.

Program Instance AdditiveSemigroup__Rational
   : PlutusTx_Numeric.AdditiveSemigroup Rational :=
  fun _ k__ =>
    k__ {| PlutusTx_Numeric.op_zp____ := AdditiveSemigroup__Rational_op_zp__ |}.

Local Definition AdditiveMonoid__Rational_zero : Rational :=
  MkRational PlutusTx_Numeric.zero PlutusTx_Numeric.one.

Program Instance AdditiveMonoid__Rational
   : PlutusTx_Numeric.AdditiveMonoid Rational :=
  fun _ k__ => k__ {| PlutusTx_Numeric.zero__ := AdditiveMonoid__Rational_zero |}.

Local Definition AdditiveGroup__Rational_op_zm__
   : Rational -> Rational -> Rational :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkRational n d, MkRational n' d' =>
        let newDen := d PlutusTx_Numeric.* d' in
        let newNum :=
          (n PlutusTx_Numeric.* d') PlutusTx_Numeric.- (n' PlutusTx_Numeric.* d) in
        let gcd' := euclid newNum newDen in
        MkRational (Z.quot newNum gcd') (Z.quot newDen gcd')
    end.

Program Instance AdditiveGroup__Rational
   : PlutusTx_Numeric.AdditiveGroup Rational :=
  fun _ k__ =>
    k__ {| PlutusTx_Numeric.op_zm____ := AdditiveGroup__Rational_op_zm__ |}.

Local Definition MultiplicativeSemigroup__Rational_op_zt__
   : Rational -> Rational -> Rational :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkRational n d, MkRational n' d' =>
        let newDen := d PlutusTx_Numeric.* d' in
        let newNum := n PlutusTx_Numeric.* n' in
        let gcd' := euclid newNum newDen in
        MkRational (Z.quot newNum gcd') (Z.quot newDen gcd')
    end.

Program Instance MultiplicativeSemigroup__Rational
   : PlutusTx_Numeric.MultiplicativeSemigroup Rational :=
  fun _ k__ =>
    k__
    {| PlutusTx_Numeric.op_zt____ := MultiplicativeSemigroup__Rational_op_zt__ |}.

Local Definition MultiplicativeMonoid__Rational_one : Rational :=
  MkRational PlutusTx_Numeric.one PlutusTx_Numeric.one.

Program Instance MultiplicativeMonoid__Rational
   : PlutusTx_Numeric.MultiplicativeMonoid Rational :=
  fun _ k__ =>
    k__ {| PlutusTx_Numeric.one__ := MultiplicativeMonoid__Rational_one |}.

(* Skipping all instances of class `PlutusTx_Numeric.Module', including
   `PlutusTx_Ratio.Module__Z__Rational' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusTx_Ratio.ToData__Rational' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusTx_Ratio.FromData__Rational' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusTx_Ratio.UnsafeFromData__Rational' *)

(* Skipping all instances of class `Data.Aeson.Types.ToJSON.ToJSON', including
   `PlutusTx_Ratio.ToJSON__Rational' *)

(* Skipping all instances of class `Data.Aeson.Types.FromJSON.FromJSON',
   including `PlutusTx_Ratio.FromJSON__Rational' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusTx_Ratio.Lift__DefaultUni__Rational' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusTx_Ratio.Typeable__DefaultUni__Rational' *)

Axiom unsafeRatio : BinNums.Z -> BinNums.Z -> Rational.

Definition ratio : BinNums.Z -> BinNums.Z -> option Rational :=
  fun n d =>
    if d PlutusTx_Eq.== PlutusTx_Numeric.zero : bool then None else
    if d PlutusTx_Ord.< PlutusTx_Numeric.zero : bool
    then Some (unsafeRatio (PlutusTx_Numeric.negate n) (PlutusTx_Numeric.negate
                                                        d)) else
    let gcd' := euclid n d in
    (Some PlutusTx_Base.∘ MkRational (Z.quot n gcd')) PlutusTx_Base.$ Z.quot d gcd'.

Axiom toGHC : Rational -> GHC.Real.Rational.

Definition numerator : Rational -> BinNums.Z :=
  fun '(MkRational n _) => n.

Definition denominator : Rational -> BinNums.Z :=
  fun '(MkRational _ d) => d.

Definition half : Rational :=
  MkRational #1 #2.

Definition fromInteger : BinNums.Z -> Rational :=
  fun num => MkRational num PlutusTx_Numeric.one.

Axiom fromGHC : GHC.Real.Rational -> Rational.

Definition negate : Rational -> Rational :=
  fun '(MkRational n d) => MkRational (PlutusTx_Numeric.negate n) d.

Definition abs : Rational -> Rational :=
  fun '((MkRational n d as rat)) =>
    if n PlutusTx_Ord.< PlutusTx_Numeric.zero : bool
    then MkRational (PlutusTx_Numeric.negate n) d else
    rat.

Definition properFraction : Rational -> (BinNums.Z * Rational)%type :=
  fun '(MkRational n d) => pair (Z.quot n d) (MkRational (Z.rem n d) d).

Axiom recip : Rational -> Rational.

Definition truncate : Rational -> BinNums.Z :=
  fun '(MkRational n d) => Z.quot n d.

Definition round : Rational -> BinNums.Z :=
  fun x =>
    let 'pair n r := properFraction x in
    let m :=
      if r PlutusTx_Ord.< PlutusTx_Numeric.zero : bool
      then n PlutusTx_Numeric.- PlutusTx_Numeric.one
      else n PlutusTx_Numeric.+ PlutusTx_Numeric.one in
    let flag := abs r PlutusTx_Numeric.- half in
    if flag PlutusTx_Ord.< PlutusTx_Numeric.zero : bool then n else
    if flag PlutusTx_Eq.== PlutusTx_Numeric.zero : bool
    then if Z.modulo n #2 PlutusTx_Eq.== PlutusTx_Numeric.zero : bool
         then n
         else m else
    m.

Axiom gcd : BinNums.Z -> BinNums.Z -> BinNums.Z.

Definition reduce : BinNums.Z -> BinNums.Z -> Rational :=
  fun x y =>
    if y PlutusTx_Eq.== #0 : bool
    then PlutusTx_Trace.traceError
         PlutusTx_ErrorCodes.ratioHasZeroDenominatorError else
    let d := gcd x y in MkRational (Z.quot x d) (Z.quot y d).

(* External variables:
     None Some bool comparison op_zt__ option pair BinNums.Z GHC.Num.fromInteger
     GHC.Real.Rational PlutusTx_Base.op_z2218U__ PlutusTx_Base.op_zd__
     PlutusTx_Bool.op_zaza__ PlutusTx_Eq.Eq PlutusTx_Eq.op_zeze__
     PlutusTx_Eq.op_zeze____ PlutusTx_ErrorCodes.ratioHasZeroDenominatorError
     PlutusTx_Numeric.AdditiveGroup PlutusTx_Numeric.AdditiveMonoid
     PlutusTx_Numeric.AdditiveSemigroup PlutusTx_Numeric.MultiplicativeMonoid
     PlutusTx_Numeric.MultiplicativeSemigroup PlutusTx_Numeric.negate
     PlutusTx_Numeric.one PlutusTx_Numeric.one__ PlutusTx_Numeric.op_zm__
     PlutusTx_Numeric.op_zm____ PlutusTx_Numeric.op_zp__ PlutusTx_Numeric.op_zp____
     PlutusTx_Numeric.op_zt__ PlutusTx_Numeric.op_zt____ PlutusTx_Numeric.zero
     PlutusTx_Numeric.zero__ PlutusTx_Ord.Ord PlutusTx_Ord.compare
     PlutusTx_Ord.compare__ PlutusTx_Ord.max__ PlutusTx_Ord.min__
     PlutusTx_Ord.op_zg__ PlutusTx_Ord.op_zg____ PlutusTx_Ord.op_zgze__
     PlutusTx_Ord.op_zgze____ PlutusTx_Ord.op_zl__ PlutusTx_Ord.op_zl____
     PlutusTx_Ord.op_zlze__ PlutusTx_Ord.op_zlze____ PlutusTx_Trace.traceError
     Z.modulo Z.quot Z.rem
*)
