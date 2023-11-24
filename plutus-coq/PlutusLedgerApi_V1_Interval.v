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

Require GHC.Base.
Require PlutusTx_Base.
Require PlutusTx_Bool.
Require PlutusTx_Enum.
Require PlutusTx_Eq.
Require PlutusTx_Functor.
Require PlutusTx_Lattice.
Require PlutusTx_Ord.
Import PlutusTx_Base.Notations.
Import PlutusTx_Bool.Notations.
Import PlutusTx_Eq.Notations.
Import PlutusTx_Functor.Notations.
Import PlutusTx_Ord.Notations.

(* Converted type declarations: *)

Inductive Extended a : Type :=
  | NegInf : Extended a
  | Finite : a -> Extended a
  | PosInf : Extended a.

Definition Closure :=
  bool%type.

Inductive LowerBound a : Type :=
  | MkLowerBound : (Extended a) -> Closure -> LowerBound a.

Inductive UpperBound a : Type :=
  | MkUpperBound : (Extended a) -> Closure -> UpperBound a.

Inductive Interval a : Type :=
  | MkInterval (ivFrom : LowerBound a) (ivTo : UpperBound a) : Interval a.

Arguments NegInf {_}.

Arguments Finite {_} _.

Arguments PosInf {_}.

Arguments MkLowerBound {_} _ _.

Arguments MkUpperBound {_} _ _.

Arguments MkInterval {_} _ _.

Definition ivFrom {a} (arg_0__ : Interval a) :=
  let 'MkInterval ivFrom _ := arg_0__ in
  ivFrom.

Definition ivTo {a} (arg_0__ : Interval a) :=
  let 'MkInterval _ ivTo := arg_0__ in
  ivTo.

(* Converted value declarations: *)

Local Definition Functor__Extended_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Extended a -> Extended b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | _, NegInf => NegInf
      | f, Finite a => Finite (f a)
      | _, PosInf => PosInf
      end.

Program Instance Functor__Extended : PlutusTx_Functor.Functor Extended :=
  fun _ k__ =>
    k__ {| PlutusTx_Functor.fmap__ := fun {a : Type} {b : Type} =>
             Functor__Extended_fmap |}.

Local Definition Functor__LowerBound_fmap
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> LowerBound a -> LowerBound b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, MkLowerBound e c => MkLowerBound (f PlutusTx_Functor.<$> e) c
      end.

Program Instance Functor__LowerBound : PlutusTx_Functor.Functor LowerBound :=
  fun _ k__ =>
    k__ {| PlutusTx_Functor.fmap__ := fun {a : Type} {b : Type} =>
             Functor__LowerBound_fmap |}.

Local Definition Functor__UpperBound_fmap
   : forall {a : Type},
     forall {b : Type}, (a -> b) -> UpperBound a -> UpperBound b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, MkUpperBound e c => MkUpperBound (f PlutusTx_Functor.<$> e) c
      end.

Program Instance Functor__UpperBound : PlutusTx_Functor.Functor UpperBound :=
  fun _ k__ =>
    k__ {| PlutusTx_Functor.fmap__ := fun {a : Type} {b : Type} =>
             Functor__UpperBound_fmap |}.

Local Definition Functor__Interval_fmap
   : forall {a : Type}, forall {b : Type}, (a -> b) -> Interval a -> Interval b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | f, MkInterval from to =>
          MkInterval (f PlutusTx_Functor.<$> from) (f PlutusTx_Functor.<$> to)
      end.

Program Instance Functor__Interval : PlutusTx_Functor.Functor Interval :=
  fun _ k__ =>
    k__ {| PlutusTx_Functor.fmap__ := fun {a : Type} {b : Type} =>
             Functor__Interval_fmap |}.

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V1_Interval.Pretty__Interval' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V1_Interval.Pretty__Extended' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V1_Interval.Pretty__UpperBound' *)

(* Skipping all instances of class `Prettyprinter.Internal.Pretty', including
   `PlutusLedgerApi_V1_Interval.Pretty__LowerBound' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V1_Interval.UnsafeFromData__Extended' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V1_Interval.FromData__Extended' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V1_Interval.ToData__Extended' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V1_Interval.UnsafeFromData__UpperBound' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V1_Interval.FromData__UpperBound' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V1_Interval.ToData__UpperBound' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V1_Interval.UnsafeFromData__LowerBound' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V1_Interval.FromData__LowerBound' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V1_Interval.ToData__LowerBound' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.UnsafeFromData',
   including `PlutusLedgerApi_V1_Interval.UnsafeFromData__Interval' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.FromData', including
   `PlutusLedgerApi_V1_Interval.FromData__Interval' *)

(* Skipping all instances of class `PlutusTx_IsData_Class.ToData', including
   `PlutusLedgerApi_V1_Interval.ToData__Interval' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Interval.Lift__DefaultUni__Extended' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Interval.Typeable__DefaultUni__Extended' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Interval.Lift__DefaultUni__LowerBound' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Interval.Typeable__DefaultUni__LowerBound' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Interval.Lift__DefaultUni__UpperBound' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Interval.Typeable__DefaultUni__UpperBound' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Lift', including
   `PlutusLedgerApi_V1_Interval.Lift__DefaultUni__Interval' *)

(* Skipping all instances of class `PlutusTx_Lift_Class.Typeable', including
   `PlutusLedgerApi_V1_Interval.Typeable__DefaultUni__Interval' *)

Local Definition Eq__Extended_op_zeze__ {inst_a : Type} `{PlutusTx_Eq.Eq inst_a}
   : Extended inst_a -> Extended inst_a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NegInf, NegInf => true
    | PosInf, PosInf => true
    | Finite l, Finite r => l PlutusTx_Eq.== r
    | _, _ => false
    end.

Program Instance Eq__Extended {a : Type} `{PlutusTx_Eq.Eq a}
   : PlutusTx_Eq.Eq (Extended a) :=
  fun _ k__ => k__ {| PlutusTx_Eq.op_zeze____ := Eq__Extended_op_zeze__ |}.

Local Definition Eq___Extended_op_zeze__ {inst_a : Type} `{PlutusTx_Eq.Eq
  inst_a}
   : Extended inst_a -> Extended inst_a -> bool :=
  _PlutusTx_Eq.==_.

Local Definition Eq___Extended_op_zsze__ {inst_a : Type} `{PlutusTx_Eq.Eq
  inst_a}
   : Extended inst_a -> Extended inst_a -> bool :=
  fun x y => negb (Eq___Extended_op_zeze__ x y).

Program Instance Eq___Extended {a : Type} `{PlutusTx_Eq.Eq a}
   : GHC.Base.Eq_ (Extended a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Extended_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Extended_op_zsze__ |}.

Local Definition Ord__Extended_compare {inst_a : Type} `{PlutusTx_Ord.Ord
  inst_a}
   : Extended inst_a -> Extended inst_a -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | NegInf, NegInf => Eq
    | NegInf, _ => Lt
    | _, NegInf => Gt
    | PosInf, PosInf => Eq
    | _, PosInf => Lt
    | PosInf, _ => Gt
    | Finite l, Finite r => PlutusTx_Ord.compare l r
    end.

Local Definition Ord__Extended_op_zlze__ {inst_a : Type} `{PlutusTx_Ord.Ord
  inst_a}
   : Extended inst_a -> Extended inst_a -> bool :=
  fun x y => match Ord__Extended_compare x y with | Gt => false | _ => true end.

Local Definition Ord__Extended_max {inst_a : Type} `{PlutusTx_Ord.Ord inst_a}
   : Extended inst_a -> Extended inst_a -> Extended inst_a :=
  fun x y => if Ord__Extended_op_zlze__ x y : bool then y else x.

Local Definition Ord__Extended_min {inst_a : Type} `{PlutusTx_Ord.Ord inst_a}
   : Extended inst_a -> Extended inst_a -> Extended inst_a :=
  fun x y => if Ord__Extended_op_zlze__ x y : bool then x else y.

Local Definition Ord__Extended_op_zg__ {inst_a : Type} `{PlutusTx_Ord.Ord
  inst_a}
   : Extended inst_a -> Extended inst_a -> bool :=
  fun x y => match Ord__Extended_compare x y with | Gt => true | _ => false end.

Local Definition Ord__Extended_op_zgze__ {inst_a : Type} `{PlutusTx_Ord.Ord
  inst_a}
   : Extended inst_a -> Extended inst_a -> bool :=
  fun x y => match Ord__Extended_compare x y with | Lt => false | _ => true end.

Local Definition Ord__Extended_op_zl__ {inst_a : Type} `{PlutusTx_Ord.Ord
  inst_a}
   : Extended inst_a -> Extended inst_a -> bool :=
  fun x y => match Ord__Extended_compare x y with | Lt => true | _ => false end.

Program Instance Ord__Extended {a : Type} `{PlutusTx_Ord.Ord a}
   : PlutusTx_Ord.Ord (Extended a) :=
  fun _ k__ =>
    k__ {| PlutusTx_Ord.compare__ := Ord__Extended_compare ;
           PlutusTx_Ord.max__ := Ord__Extended_max ;
           PlutusTx_Ord.min__ := Ord__Extended_min ;
           PlutusTx_Ord.op_zg____ := Ord__Extended_op_zg__ ;
           PlutusTx_Ord.op_zgze____ := Ord__Extended_op_zgze__ ;
           PlutusTx_Ord.op_zl____ := Ord__Extended_op_zl__ ;
           PlutusTx_Ord.op_zlze____ := Ord__Extended_op_zlze__ |}.

(* Skipping all instances of class `GHC.Base.Ord', including
   `PlutusLedgerApi_V1_Interval.Ord__Extended' *)

Definition inclusiveUpperBound {a} `{PlutusTx_Enum.Enum a}
   : UpperBound a -> Extended a :=
  fun arg_0__ =>
    match arg_0__ with
    | MkUpperBound v true => v
    | MkUpperBound (Finite x) false => Finite PlutusTx_Base.$ PlutusTx_Enum.pred x
    | MkUpperBound v false => v
    end.

Local Definition Eq__UpperBound_op_zeze__ {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Eq.Eq inst_a}
   : UpperBound inst_a -> UpperBound inst_a -> bool :=
  fun b1 b2 => inclusiveUpperBound b1 PlutusTx_Eq.== inclusiveUpperBound b2.

Program Instance Eq__UpperBound {a : Type} `{PlutusTx_Enum.Enum a}
  `{PlutusTx_Eq.Eq a}
   : PlutusTx_Eq.Eq (UpperBound a) :=
  fun _ k__ => k__ {| PlutusTx_Eq.op_zeze____ := Eq__UpperBound_op_zeze__ |}.

Local Definition Eq___UpperBound_op_zeze__ {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Eq.Eq inst_a}
   : UpperBound inst_a -> UpperBound inst_a -> bool :=
  _PlutusTx_Eq.==_.

Local Definition Eq___UpperBound_op_zsze__ {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Eq.Eq inst_a}
   : UpperBound inst_a -> UpperBound inst_a -> bool :=
  fun x y => negb (Eq___UpperBound_op_zeze__ x y).

Program Instance Eq___UpperBound {a : Type} `{PlutusTx_Enum.Enum a}
  `{PlutusTx_Eq.Eq a}
   : GHC.Base.Eq_ (UpperBound a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___UpperBound_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___UpperBound_op_zsze__ |}.

Local Definition Ord__UpperBound_compare {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Ord.Ord inst_a}
   : UpperBound inst_a -> UpperBound inst_a -> comparison :=
  fun b1 b2 =>
    PlutusTx_Ord.compare (inclusiveUpperBound b1) (inclusiveUpperBound b2).

Local Definition Ord__UpperBound_op_zlze__ {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Ord.Ord inst_a}
   : UpperBound inst_a -> UpperBound inst_a -> bool :=
  fun x y => match Ord__UpperBound_compare x y with | Gt => false | _ => true end.

Local Definition Ord__UpperBound_max {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Ord.Ord inst_a}
   : UpperBound inst_a -> UpperBound inst_a -> UpperBound inst_a :=
  fun x y => if Ord__UpperBound_op_zlze__ x y : bool then y else x.

Local Definition Ord__UpperBound_min {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Ord.Ord inst_a}
   : UpperBound inst_a -> UpperBound inst_a -> UpperBound inst_a :=
  fun x y => if Ord__UpperBound_op_zlze__ x y : bool then x else y.

Local Definition Ord__UpperBound_op_zg__ {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Ord.Ord inst_a}
   : UpperBound inst_a -> UpperBound inst_a -> bool :=
  fun x y => match Ord__UpperBound_compare x y with | Gt => true | _ => false end.

Local Definition Ord__UpperBound_op_zgze__ {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Ord.Ord inst_a}
   : UpperBound inst_a -> UpperBound inst_a -> bool :=
  fun x y => match Ord__UpperBound_compare x y with | Lt => false | _ => true end.

Local Definition Ord__UpperBound_op_zl__ {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Ord.Ord inst_a}
   : UpperBound inst_a -> UpperBound inst_a -> bool :=
  fun x y => match Ord__UpperBound_compare x y with | Lt => true | _ => false end.

Program Instance Ord__UpperBound {a : Type} `{PlutusTx_Enum.Enum a}
  `{PlutusTx_Ord.Ord a}
   : PlutusTx_Ord.Ord (UpperBound a) :=
  fun _ k__ =>
    k__ {| PlutusTx_Ord.compare__ := Ord__UpperBound_compare ;
           PlutusTx_Ord.max__ := Ord__UpperBound_max ;
           PlutusTx_Ord.min__ := Ord__UpperBound_min ;
           PlutusTx_Ord.op_zg____ := Ord__UpperBound_op_zg__ ;
           PlutusTx_Ord.op_zgze____ := Ord__UpperBound_op_zgze__ ;
           PlutusTx_Ord.op_zl____ := Ord__UpperBound_op_zl__ ;
           PlutusTx_Ord.op_zlze____ := Ord__UpperBound_op_zlze__ |}.

(* Skipping all instances of class `GHC.Base.Ord', including
   `PlutusLedgerApi_V1_Interval.Ord__UpperBound' *)

Definition inclusiveLowerBound {a} `{PlutusTx_Enum.Enum a}
   : LowerBound a -> Extended a :=
  fun arg_0__ =>
    match arg_0__ with
    | MkLowerBound v true => v
    | MkLowerBound (Finite x) false => Finite PlutusTx_Base.$ PlutusTx_Enum.succ x
    | MkLowerBound v false => v
    end.

Local Definition Eq__LowerBound_op_zeze__ {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Eq.Eq inst_a}
   : LowerBound inst_a -> LowerBound inst_a -> bool :=
  fun b1 b2 => inclusiveLowerBound b1 PlutusTx_Eq.== inclusiveLowerBound b2.

Program Instance Eq__LowerBound {a : Type} `{PlutusTx_Enum.Enum a}
  `{PlutusTx_Eq.Eq a}
   : PlutusTx_Eq.Eq (LowerBound a) :=
  fun _ k__ => k__ {| PlutusTx_Eq.op_zeze____ := Eq__LowerBound_op_zeze__ |}.

Local Definition Eq___LowerBound_op_zeze__ {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Eq.Eq inst_a}
   : LowerBound inst_a -> LowerBound inst_a -> bool :=
  _PlutusTx_Eq.==_.

Local Definition Eq___LowerBound_op_zsze__ {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Eq.Eq inst_a}
   : LowerBound inst_a -> LowerBound inst_a -> bool :=
  fun x y => negb (Eq___LowerBound_op_zeze__ x y).

Program Instance Eq___LowerBound {a : Type} `{PlutusTx_Enum.Enum a}
  `{PlutusTx_Eq.Eq a}
   : GHC.Base.Eq_ (LowerBound a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___LowerBound_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___LowerBound_op_zsze__ |}.

Local Definition Ord__LowerBound_compare {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Ord.Ord inst_a}
   : LowerBound inst_a -> LowerBound inst_a -> comparison :=
  fun b1 b2 =>
    PlutusTx_Ord.compare (inclusiveLowerBound b1) (inclusiveLowerBound b2).

Local Definition Ord__LowerBound_op_zlze__ {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Ord.Ord inst_a}
   : LowerBound inst_a -> LowerBound inst_a -> bool :=
  fun x y => match Ord__LowerBound_compare x y with | Gt => false | _ => true end.

Local Definition Ord__LowerBound_max {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Ord.Ord inst_a}
   : LowerBound inst_a -> LowerBound inst_a -> LowerBound inst_a :=
  fun x y => if Ord__LowerBound_op_zlze__ x y : bool then y else x.

Local Definition Ord__LowerBound_min {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Ord.Ord inst_a}
   : LowerBound inst_a -> LowerBound inst_a -> LowerBound inst_a :=
  fun x y => if Ord__LowerBound_op_zlze__ x y : bool then x else y.

Local Definition Ord__LowerBound_op_zg__ {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Ord.Ord inst_a}
   : LowerBound inst_a -> LowerBound inst_a -> bool :=
  fun x y => match Ord__LowerBound_compare x y with | Gt => true | _ => false end.

Local Definition Ord__LowerBound_op_zgze__ {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Ord.Ord inst_a}
   : LowerBound inst_a -> LowerBound inst_a -> bool :=
  fun x y => match Ord__LowerBound_compare x y with | Lt => false | _ => true end.

Local Definition Ord__LowerBound_op_zl__ {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Ord.Ord inst_a}
   : LowerBound inst_a -> LowerBound inst_a -> bool :=
  fun x y => match Ord__LowerBound_compare x y with | Lt => true | _ => false end.

Program Instance Ord__LowerBound {a : Type} `{PlutusTx_Enum.Enum a}
  `{PlutusTx_Ord.Ord a}
   : PlutusTx_Ord.Ord (LowerBound a) :=
  fun _ k__ =>
    k__ {| PlutusTx_Ord.compare__ := Ord__LowerBound_compare ;
           PlutusTx_Ord.max__ := Ord__LowerBound_max ;
           PlutusTx_Ord.min__ := Ord__LowerBound_min ;
           PlutusTx_Ord.op_zg____ := Ord__LowerBound_op_zg__ ;
           PlutusTx_Ord.op_zgze____ := Ord__LowerBound_op_zgze__ ;
           PlutusTx_Ord.op_zl____ := Ord__LowerBound_op_zl__ ;
           PlutusTx_Ord.op_zlze____ := Ord__LowerBound_op_zlze__ |}.

(* Skipping all instances of class `GHC.Base.Ord', including
   `PlutusLedgerApi_V1_Interval.Ord__LowerBound' *)

Definition hull {a : Type} `{PlutusTx_Enum.Enum a} `{PlutusTx_Ord.Ord a}
   : Interval a -> Interval a -> Interval a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkInterval l1 h1, MkInterval l2 h2 =>
        MkInterval (PlutusTx_Ord.min l1 l2) (PlutusTx_Ord.max h1 h2)
    end.

Local Definition JoinSemiLattice__Interval_op_zrzs__ {inst_a : Type}
  `{PlutusTx_Enum.Enum inst_a} `{PlutusTx_Ord.Ord inst_a}
   : Interval inst_a -> Interval inst_a -> Interval inst_a :=
  hull.

Program Instance JoinSemiLattice__Interval {a : Type} `{PlutusTx_Enum.Enum a}
  `{PlutusTx_Ord.Ord a}
   : PlutusTx_Lattice.JoinSemiLattice (Interval a) :=
  fun _ k__ =>
    k__ {| PlutusTx_Lattice.op_zrzs____ := JoinSemiLattice__Interval_op_zrzs__ |}.

Definition never {a : Type} : Interval a :=
  MkInterval (MkLowerBound PosInf true) (MkUpperBound NegInf true).

Local Definition BoundedJoinSemiLattice__Interval_bottom {inst_a : Type}
  `{PlutusTx_Enum.Enum inst_a} `{PlutusTx_Ord.Ord inst_a}
   : Interval inst_a :=
  never.

Program Instance BoundedJoinSemiLattice__Interval {a : Type}
  `{PlutusTx_Enum.Enum a} `{PlutusTx_Ord.Ord a}
   : PlutusTx_Lattice.BoundedJoinSemiLattice (Interval a) :=
  fun _ k__ =>
    k__ {| PlutusTx_Lattice.bottom__ := BoundedJoinSemiLattice__Interval_bottom |}.

Definition intersection {a : Type} `{PlutusTx_Enum.Enum a} `{PlutusTx_Ord.Ord a}
   : Interval a -> Interval a -> Interval a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkInterval l1 h1, MkInterval l2 h2 =>
        MkInterval (PlutusTx_Ord.max l1 l2) (PlutusTx_Ord.min h1 h2)
    end.

Local Definition MeetSemiLattice__Interval_op_zszr__ {inst_a : Type}
  `{PlutusTx_Enum.Enum inst_a} `{PlutusTx_Ord.Ord inst_a}
   : Interval inst_a -> Interval inst_a -> Interval inst_a :=
  intersection.

Program Instance MeetSemiLattice__Interval {a : Type} `{PlutusTx_Enum.Enum a}
  `{PlutusTx_Ord.Ord a}
   : PlutusTx_Lattice.MeetSemiLattice (Interval a) :=
  fun _ k__ =>
    k__ {| PlutusTx_Lattice.op_zszr____ := MeetSemiLattice__Interval_op_zszr__ |}.

Definition always {a : Type} : Interval a :=
  MkInterval (MkLowerBound NegInf true) (MkUpperBound PosInf true).

Local Definition BoundedMeetSemiLattice__Interval_top {inst_a : Type}
  `{PlutusTx_Enum.Enum inst_a} `{PlutusTx_Ord.Ord inst_a}
   : Interval inst_a :=
  always.

Program Instance BoundedMeetSemiLattice__Interval {a : Type}
  `{PlutusTx_Enum.Enum a} `{PlutusTx_Ord.Ord a}
   : PlutusTx_Lattice.BoundedMeetSemiLattice (Interval a) :=
  fun _ k__ =>
    k__ {| PlutusTx_Lattice.top__ := BoundedMeetSemiLattice__Interval_top |}.

Definition isEmpty {a : Type} `{PlutusTx_Enum.Enum a} `{PlutusTx_Ord.Ord a}
   : Interval a -> bool :=
  fun '(MkInterval lb ub) =>
    match PlutusTx_Ord.compare (inclusiveLowerBound lb) (inclusiveUpperBound
                                ub) with
    | Lt => false
    | Eq => false
    | Gt => true
    end.

Local Definition Eq__Interval_op_zeze__ {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Ord.Ord inst_a}
   : Interval inst_a -> Interval inst_a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | iv1, iv2 =>
        if isEmpty iv1 PlutusTx_Bool.&& isEmpty iv2 : bool then true else
        match arg_0__, arg_1__ with
        | MkInterval lb1 ub1, MkInterval lb2 ub2 =>
            (lb1 PlutusTx_Eq.== lb2) PlutusTx_Bool.&& (ub1 PlutusTx_Eq.== ub2)
        end
    end.

Program Instance Eq__Interval {a : Type} `{PlutusTx_Enum.Enum a}
  `{PlutusTx_Ord.Ord a}
   : PlutusTx_Eq.Eq (Interval a) :=
  fun _ k__ => k__ {| PlutusTx_Eq.op_zeze____ := Eq__Interval_op_zeze__ |}.

Local Definition Eq___Interval_op_zeze__ {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Ord.Ord inst_a}
   : Interval inst_a -> Interval inst_a -> bool :=
  _PlutusTx_Eq.==_.

Local Definition Eq___Interval_op_zsze__ {inst_a : Type} `{PlutusTx_Enum.Enum
  inst_a} `{PlutusTx_Ord.Ord inst_a}
   : Interval inst_a -> Interval inst_a -> bool :=
  fun x y => negb (Eq___Interval_op_zeze__ x y).

Program Instance Eq___Interval {a : Type} `{PlutusTx_Enum.Enum a}
  `{PlutusTx_Ord.Ord a}
   : GHC.Base.Eq_ (Interval a) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zeze____ := Eq___Interval_op_zeze__ ;
           GHC.Base.op_zsze____ := Eq___Interval_op_zsze__ |}.

Definition strictUpperBound {a : Type} : a -> UpperBound a :=
  fun a => MkUpperBound (Finite a) false.

Definition strictLowerBound {a : Type} : a -> LowerBound a :=
  fun a => MkLowerBound (Finite a) false.

Definition lowerBound {a : Type} : a -> LowerBound a :=
  fun a => MkLowerBound (Finite a) true.

Definition upperBound {a : Type} : a -> UpperBound a :=
  fun a => MkUpperBound (Finite a) true.

Definition interval {a : Type} : a -> a -> Interval a :=
  fun s s' => MkInterval (lowerBound s) (upperBound s').

Definition singleton {a : Type} : a -> Interval a :=
  fun s => interval s s.

Definition from {a : Type} : a -> Interval a :=
  fun s => MkInterval (lowerBound s) (MkUpperBound PosInf true).

Definition to {a : Type} : a -> Interval a :=
  fun s => MkInterval (MkLowerBound NegInf true) (upperBound s).

Definition contains {a : Type} `{PlutusTx_Enum.Enum a} `{PlutusTx_Ord.Ord a}
   : Interval a -> Interval a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, i2 =>
        if isEmpty i2 : bool then true else
        match arg_0__, arg_1__ with
        | i1, _ =>
            if isEmpty i1 : bool then false else
            match arg_0__, arg_1__ with
            | MkInterval l1 h1, MkInterval l2 h2 =>
                (l1 PlutusTx_Ord.<= l2) PlutusTx_Bool.&& (h2 PlutusTx_Ord.<= h1)
            end
        end
    end.

Definition member {a : Type} `{PlutusTx_Enum.Enum a} `{PlutusTx_Ord.Ord a}
   : a -> Interval a -> bool :=
  fun a i => contains i (singleton a).

Definition overlaps {a : Type} `{PlutusTx_Enum.Enum a} `{PlutusTx_Ord.Ord a}
   : Interval a -> Interval a -> bool :=
  fun l r => PlutusTx_Bool.not PlutusTx_Base.$ isEmpty (intersection l r).

Definition before {a : Type} `{PlutusTx_Enum.Enum a} `{PlutusTx_Ord.Ord a}
   : a -> Interval a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | h, MkInterval f _ => lowerBound h PlutusTx_Ord.< f
    end.

Definition after {a : Type} `{PlutusTx_Enum.Enum a} `{PlutusTx_Ord.Ord a}
   : a -> Interval a -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | h, MkInterval _ t => upperBound h PlutusTx_Ord.> t
    end.

(* External variables:
     Eq Gt Lt Type bool comparison false negb true GHC.Base.Eq_ GHC.Base.op_zeze____
     GHC.Base.op_zsze____ PlutusTx_Base.op_zd__ PlutusTx_Bool.not
     PlutusTx_Bool.op_zaza__ PlutusTx_Enum.Enum PlutusTx_Enum.pred PlutusTx_Enum.succ
     PlutusTx_Eq.Eq PlutusTx_Eq.op_zeze__ PlutusTx_Eq.op_zeze____
     PlutusTx_Functor.Functor PlutusTx_Functor.fmap__ PlutusTx_Functor.op_zlzdzg__
     PlutusTx_Lattice.BoundedJoinSemiLattice PlutusTx_Lattice.BoundedMeetSemiLattice
     PlutusTx_Lattice.JoinSemiLattice PlutusTx_Lattice.MeetSemiLattice
     PlutusTx_Lattice.bottom__ PlutusTx_Lattice.op_zrzs____
     PlutusTx_Lattice.op_zszr____ PlutusTx_Lattice.top__ PlutusTx_Ord.Ord
     PlutusTx_Ord.compare PlutusTx_Ord.compare__ PlutusTx_Ord.max PlutusTx_Ord.max__
     PlutusTx_Ord.min PlutusTx_Ord.min__ PlutusTx_Ord.op_zg__ PlutusTx_Ord.op_zg____
     PlutusTx_Ord.op_zgze____ PlutusTx_Ord.op_zl__ PlutusTx_Ord.op_zl____
     PlutusTx_Ord.op_zlze__ PlutusTx_Ord.op_zlze____
*)
