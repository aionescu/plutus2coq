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
Require PlutusTx_Eq.
Require ZArith.BinInt.
Import PlutusTx_Eq.Notations.

(* Converted type declarations: *)

Record Ord__Dict (a : Type) := Ord__Dict_Build {
  compare__ : a -> a -> comparison ;
  max__ : a -> a -> a ;
  min__ : a -> a -> a ;
  op_zg____ : a -> a -> bool ;
  op_zgze____ : a -> a -> bool ;
  op_zl____ : a -> a -> bool ;
  op_zlze____ : a -> a -> bool }.

Definition Ord (a : Type) `{PlutusTx_Eq.Eq a} :=
  forall r__, (Ord__Dict a -> r__) -> r__.
Existing Class Ord.

Definition compare `{g__0__ : Ord a} : a -> a -> comparison :=
  g__0__ _ (compare__ a).

Definition max `{g__0__ : Ord a} : a -> a -> a :=
  g__0__ _ (max__ a).

Definition min `{g__0__ : Ord a} : a -> a -> a :=
  g__0__ _ (min__ a).

Definition op_zg__ `{g__0__ : Ord a} : a -> a -> bool :=
  g__0__ _ (op_zg____ a).

Definition op_zgze__ `{g__0__ : Ord a} : a -> a -> bool :=
  g__0__ _ (op_zgze____ a).

Definition op_zl__ `{g__0__ : Ord a} : a -> a -> bool :=
  g__0__ _ (op_zl____ a).

Definition op_zlze__ `{g__0__ : Ord a} : a -> a -> bool :=
  g__0__ _ (op_zlze____ a).

Notation "'_>_'" := (op_zg__).

Infix ">" := (_>_).

Notation "'_>=_'" := (op_zgze__).

Infix ">=" := (_>=_).

Notation "'_<_'" := (op_zl__).

Infix "<" := (_<_).

Notation "'_<=_'" := (op_zlze__).

Infix "<=" := (_<=_).

(* Converted value declarations: *)

Local Definition Eq__comparison_op_zeze__ : comparison -> comparison -> bool :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Eq, Eq => true
    | Gt, Gt => true
    | Lt, Lt => true
    | _, _ => false
    end.

Program Instance Eq__comparison : PlutusTx_Eq.Eq comparison :=
  fun _ k__ => k__ {| PlutusTx_Eq.op_zeze____ := Eq__comparison_op_zeze__ |}.

Local Definition Ord__Z_op_zlze__ : BinNums.Z -> BinNums.Z -> bool :=
  ZArith.BinInt.Z.leb.

Local Definition Ord__Z_compare : BinNums.Z -> BinNums.Z -> comparison :=
  fun x y =>
    if x PlutusTx_Eq.== y : bool
    then Eq
    else if Ord__Z_op_zlze__ x y : bool
         then Lt
         else Gt.

Local Definition Ord__Z_max : BinNums.Z -> BinNums.Z -> BinNums.Z :=
  fun x y => if Ord__Z_op_zlze__ x y : bool then y else x.

Local Definition Ord__Z_min : BinNums.Z -> BinNums.Z -> BinNums.Z :=
  fun x y => if Ord__Z_op_zlze__ x y : bool then x else y.

Local Definition Ord__Z_op_zg__ : BinNums.Z -> BinNums.Z -> bool :=
  ZArith.BinInt.Z.gtb.

Local Definition Ord__Z_op_zgze__ : BinNums.Z -> BinNums.Z -> bool :=
  ZArith.BinInt.Z.geb.

Local Definition Ord__Z_op_zl__ : BinNums.Z -> BinNums.Z -> bool :=
  ZArith.BinInt.Z.ltb.

Program Instance Ord__Z : Ord BinNums.Z :=
  fun _ k__ =>
    k__ {| compare__ := Ord__Z_compare ;
           max__ := Ord__Z_max ;
           min__ := Ord__Z_min ;
           op_zg____ := Ord__Z_op_zg__ ;
           op_zgze____ := Ord__Z_op_zgze__ ;
           op_zl____ := Ord__Z_op_zl__ ;
           op_zlze____ := Ord__Z_op_zlze__ |}.

(* Skipping instance `PlutusTx_Ord.Ord__BuiltinByteString' of class
   `PlutusTx_Ord.Ord' *)

Fixpoint compareList {a} `{Ord a} (arg_0__ arg_1__ : list a) : comparison
  := match arg_0__, arg_1__ with
     | nil, nil => Eq
     | nil, cons _ _ => Lt
     | cons _ _, nil => Gt
     | cons x xs, cons y ys =>
         match compare x y with
         | Eq => compareList xs ys
         | c => c
         end
     end.

Local Definition Ord__list_compare {inst_a : Type} `{Ord inst_a}
   : list inst_a -> list inst_a -> comparison :=
  compareList.

Local Definition Ord__list_op_zlze__ {inst_a : Type} `{Ord inst_a}
   : list inst_a -> list inst_a -> bool :=
  fun x y => match Ord__list_compare x y with | Gt => false | _ => true end.

Local Definition Ord__list_max {inst_a : Type} `{Ord inst_a}
   : list inst_a -> list inst_a -> list inst_a :=
  fun x y => if Ord__list_op_zlze__ x y : bool then y else x.

Local Definition Ord__list_min {inst_a : Type} `{Ord inst_a}
   : list inst_a -> list inst_a -> list inst_a :=
  fun x y => if Ord__list_op_zlze__ x y : bool then x else y.

Local Definition Ord__list_op_zg__ {inst_a : Type} `{Ord inst_a}
   : list inst_a -> list inst_a -> bool :=
  fun x y => match Ord__list_compare x y with | Gt => true | _ => false end.

Local Definition Ord__list_op_zgze__ {inst_a : Type} `{Ord inst_a}
   : list inst_a -> list inst_a -> bool :=
  fun x y => match Ord__list_compare x y with | Lt => false | _ => true end.

Local Definition Ord__list_op_zl__ {inst_a : Type} `{Ord inst_a}
   : list inst_a -> list inst_a -> bool :=
  fun x y => match Ord__list_compare x y with | Lt => true | _ => false end.

Program Instance Ord__list {a : Type} `{Ord a} : Ord (list a) :=
  fun _ k__ =>
    k__ {| compare__ := Ord__list_compare ;
           max__ := Ord__list_max ;
           min__ := Ord__list_min ;
           op_zg____ := Ord__list_op_zg__ ;
           op_zgze____ := Ord__list_op_zgze__ ;
           op_zl____ := Ord__list_op_zl__ ;
           op_zlze____ := Ord__list_op_zlze__ |}.

Local Definition Ord__bool_compare : bool -> bool -> comparison :=
  fun b1 b2 =>
    match b1 with
    | false => match b2 with | false => Eq | true => Lt end
    | true => match b2 with | false => Gt | true => Eq end
    end.

Local Definition Ord__bool_op_zlze__ : bool -> bool -> bool :=
  fun x y => match Ord__bool_compare x y with | Gt => false | _ => true end.

Local Definition Ord__bool_max : bool -> bool -> bool :=
  fun x y => if Ord__bool_op_zlze__ x y : bool then y else x.

Local Definition Ord__bool_min : bool -> bool -> bool :=
  fun x y => if Ord__bool_op_zlze__ x y : bool then x else y.

Local Definition Ord__bool_op_zg__ : bool -> bool -> bool :=
  fun x y => match Ord__bool_compare x y with | Gt => true | _ => false end.

Local Definition Ord__bool_op_zgze__ : bool -> bool -> bool :=
  fun x y => match Ord__bool_compare x y with | Lt => false | _ => true end.

Local Definition Ord__bool_op_zl__ : bool -> bool -> bool :=
  fun x y => match Ord__bool_compare x y with | Lt => true | _ => false end.

Program Instance Ord__bool : Ord bool :=
  fun _ k__ =>
    k__ {| compare__ := Ord__bool_compare ;
           max__ := Ord__bool_max ;
           min__ := Ord__bool_min ;
           op_zg____ := Ord__bool_op_zg__ ;
           op_zgze____ := Ord__bool_op_zgze__ ;
           op_zl____ := Ord__bool_op_zl__ ;
           op_zlze____ := Ord__bool_op_zlze__ |}.

Local Definition Ord__option_compare {inst_a : Type} `{Ord inst_a}
   : option inst_a -> option inst_a -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Some a1, Some a2 => compare a1 a2
    | None, Some _ => Lt
    | Some _, None => Gt
    | None, None => Eq
    end.

Local Definition Ord__option_op_zlze__ {inst_a : Type} `{Ord inst_a}
   : option inst_a -> option inst_a -> bool :=
  fun x y => match Ord__option_compare x y with | Gt => false | _ => true end.

Local Definition Ord__option_max {inst_a : Type} `{Ord inst_a}
   : option inst_a -> option inst_a -> option inst_a :=
  fun x y => if Ord__option_op_zlze__ x y : bool then y else x.

Local Definition Ord__option_min {inst_a : Type} `{Ord inst_a}
   : option inst_a -> option inst_a -> option inst_a :=
  fun x y => if Ord__option_op_zlze__ x y : bool then x else y.

Local Definition Ord__option_op_zg__ {inst_a : Type} `{Ord inst_a}
   : option inst_a -> option inst_a -> bool :=
  fun x y => match Ord__option_compare x y with | Gt => true | _ => false end.

Local Definition Ord__option_op_zgze__ {inst_a : Type} `{Ord inst_a}
   : option inst_a -> option inst_a -> bool :=
  fun x y => match Ord__option_compare x y with | Lt => false | _ => true end.

Local Definition Ord__option_op_zl__ {inst_a : Type} `{Ord inst_a}
   : option inst_a -> option inst_a -> bool :=
  fun x y => match Ord__option_compare x y with | Lt => true | _ => false end.

Program Instance Ord__option {a : Type} `{Ord a} : Ord (option a) :=
  fun _ k__ =>
    k__ {| compare__ := Ord__option_compare ;
           max__ := Ord__option_max ;
           min__ := Ord__option_min ;
           op_zg____ := Ord__option_op_zg__ ;
           op_zgze____ := Ord__option_op_zgze__ ;
           op_zl____ := Ord__option_op_zl__ ;
           op_zlze____ := Ord__option_op_zlze__ |}.

Local Definition Ord__Either_compare {inst_a : Type} {inst_b : Type} `{Ord
  inst_a} `{Ord inst_b}
   : Data.Either.Either inst_a inst_b ->
     Data.Either.Either inst_a inst_b -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | Data.Either.Left a1, Data.Either.Left a2 => compare a1 a2
    | Data.Either.Left _, Data.Either.Right _ => Lt
    | Data.Either.Right _, Data.Either.Left _ => Gt
    | Data.Either.Right b1, Data.Either.Right b2 => compare b1 b2
    end.

Local Definition Ord__Either_op_zlze__ {inst_a : Type} {inst_b : Type} `{Ord
  inst_a} `{Ord inst_b}
   : Data.Either.Either inst_a inst_b ->
     Data.Either.Either inst_a inst_b -> bool :=
  fun x y => match Ord__Either_compare x y with | Gt => false | _ => true end.

Local Definition Ord__Either_max {inst_a : Type} {inst_b : Type} `{Ord inst_a}
  `{Ord inst_b}
   : Data.Either.Either inst_a inst_b ->
     Data.Either.Either inst_a inst_b -> Data.Either.Either inst_a inst_b :=
  fun x y => if Ord__Either_op_zlze__ x y : bool then y else x.

Local Definition Ord__Either_min {inst_a : Type} {inst_b : Type} `{Ord inst_a}
  `{Ord inst_b}
   : Data.Either.Either inst_a inst_b ->
     Data.Either.Either inst_a inst_b -> Data.Either.Either inst_a inst_b :=
  fun x y => if Ord__Either_op_zlze__ x y : bool then x else y.

Local Definition Ord__Either_op_zg__ {inst_a : Type} {inst_b : Type} `{Ord
  inst_a} `{Ord inst_b}
   : Data.Either.Either inst_a inst_b ->
     Data.Either.Either inst_a inst_b -> bool :=
  fun x y => match Ord__Either_compare x y with | Gt => true | _ => false end.

Local Definition Ord__Either_op_zgze__ {inst_a : Type} {inst_b : Type} `{Ord
  inst_a} `{Ord inst_b}
   : Data.Either.Either inst_a inst_b ->
     Data.Either.Either inst_a inst_b -> bool :=
  fun x y => match Ord__Either_compare x y with | Lt => false | _ => true end.

Local Definition Ord__Either_op_zl__ {inst_a : Type} {inst_b : Type} `{Ord
  inst_a} `{Ord inst_b}
   : Data.Either.Either inst_a inst_b ->
     Data.Either.Either inst_a inst_b -> bool :=
  fun x y => match Ord__Either_compare x y with | Lt => true | _ => false end.

Program Instance Ord__Either {a : Type} {b : Type} `{Ord a} `{Ord b}
   : Ord (Data.Either.Either a b) :=
  fun _ k__ =>
    k__ {| compare__ := Ord__Either_compare ;
           max__ := Ord__Either_max ;
           min__ := Ord__Either_min ;
           op_zg____ := Ord__Either_op_zg__ ;
           op_zgze____ := Ord__Either_op_zgze__ ;
           op_zl____ := Ord__Either_op_zl__ ;
           op_zlze____ := Ord__Either_op_zlze__ |}.

Local Definition Ord__unit_compare : unit -> unit -> comparison :=
  fun arg_0__ arg_1__ => Eq.

Local Definition Ord__unit_op_zlze__ : unit -> unit -> bool :=
  fun x y => match Ord__unit_compare x y with | Gt => false | _ => true end.

Local Definition Ord__unit_max : unit -> unit -> unit :=
  fun x y => if Ord__unit_op_zlze__ x y : bool then y else x.

Local Definition Ord__unit_min : unit -> unit -> unit :=
  fun x y => if Ord__unit_op_zlze__ x y : bool then x else y.

Local Definition Ord__unit_op_zg__ : unit -> unit -> bool :=
  fun x y => match Ord__unit_compare x y with | Gt => true | _ => false end.

Local Definition Ord__unit_op_zgze__ : unit -> unit -> bool :=
  fun x y => match Ord__unit_compare x y with | Lt => false | _ => true end.

Local Definition Ord__unit_op_zl__ : unit -> unit -> bool :=
  fun x y => match Ord__unit_compare x y with | Lt => true | _ => false end.

Program Instance Ord__unit : Ord unit :=
  fun _ k__ =>
    k__ {| compare__ := Ord__unit_compare ;
           max__ := Ord__unit_max ;
           min__ := Ord__unit_min ;
           op_zg____ := Ord__unit_op_zg__ ;
           op_zgze____ := Ord__unit_op_zgze__ ;
           op_zl____ := Ord__unit_op_zl__ ;
           op_zlze____ := Ord__unit_op_zlze__ |}.

Local Definition Ord__op_zt___compare {inst_a : Type} {inst_b : Type} `{Ord
  inst_a} `{Ord inst_b}
   : (inst_a * inst_b)%type -> (inst_a * inst_b)%type -> comparison :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair a b, pair a' b' =>
        match compare a a' with
        | Eq => compare b b'
        | c => c
        end
    end.

Local Definition Ord__op_zt___op_zlze__ {inst_a : Type} {inst_b : Type} `{Ord
  inst_a} `{Ord inst_b}
   : (inst_a * inst_b)%type -> (inst_a * inst_b)%type -> bool :=
  fun x y => match Ord__op_zt___compare x y with | Gt => false | _ => true end.

Local Definition Ord__op_zt___max {inst_a : Type} {inst_b : Type} `{Ord inst_a}
  `{Ord inst_b}
   : (inst_a * inst_b)%type -> (inst_a * inst_b)%type -> (inst_a * inst_b)%type :=
  fun x y => if Ord__op_zt___op_zlze__ x y : bool then y else x.

Local Definition Ord__op_zt___min {inst_a : Type} {inst_b : Type} `{Ord inst_a}
  `{Ord inst_b}
   : (inst_a * inst_b)%type -> (inst_a * inst_b)%type -> (inst_a * inst_b)%type :=
  fun x y => if Ord__op_zt___op_zlze__ x y : bool then x else y.

Local Definition Ord__op_zt___op_zg__ {inst_a : Type} {inst_b : Type} `{Ord
  inst_a} `{Ord inst_b}
   : (inst_a * inst_b)%type -> (inst_a * inst_b)%type -> bool :=
  fun x y => match Ord__op_zt___compare x y with | Gt => true | _ => false end.

Local Definition Ord__op_zt___op_zgze__ {inst_a : Type} {inst_b : Type} `{Ord
  inst_a} `{Ord inst_b}
   : (inst_a * inst_b)%type -> (inst_a * inst_b)%type -> bool :=
  fun x y => match Ord__op_zt___compare x y with | Lt => false | _ => true end.

Local Definition Ord__op_zt___op_zl__ {inst_a : Type} {inst_b : Type} `{Ord
  inst_a} `{Ord inst_b}
   : (inst_a * inst_b)%type -> (inst_a * inst_b)%type -> bool :=
  fun x y => match Ord__op_zt___compare x y with | Lt => true | _ => false end.

Program Instance Ord__op_zt__ {a : Type} {b : Type} `{Ord a} `{Ord b}
   : Ord (a * b)%type :=
  fun _ k__ =>
    k__ {| compare__ := Ord__op_zt___compare ;
           max__ := Ord__op_zt___max ;
           min__ := Ord__op_zt___min ;
           op_zg____ := Ord__op_zt___op_zg__ ;
           op_zgze____ := Ord__op_zt___op_zgze__ ;
           op_zl____ := Ord__op_zt___op_zl__ ;
           op_zlze____ := Ord__op_zt___op_zlze__ |}.

Module Notations.
Notation "'_PlutusTx_Ord.>_'" := (op_zg__).
Infix "PlutusTx_Ord.>" := (_>_) (at level 99).
Notation "'_PlutusTx_Ord.>=_'" := (op_zgze__).
Infix "PlutusTx_Ord.>=" := (_>=_) (at level 99).
Notation "'_PlutusTx_Ord.<_'" := (op_zl__).
Infix "PlutusTx_Ord.<" := (_<_) (at level 99).
Notation "'_PlutusTx_Ord.<=_'" := (op_zlze__).
Infix "PlutusTx_Ord.<=" := (_<=_) (at level 99).
End Notations.

(* External variables:
     Eq Gt Lt None Some Type bool comparison cons false list nil op_zt__ option pair
     true unit BinNums.Z Data.Either.Either Data.Either.Left Data.Either.Right
     PlutusTx_Eq.Eq PlutusTx_Eq.op_zeze__ PlutusTx_Eq.op_zeze____ ZArith.BinInt.Z.geb
     ZArith.BinInt.Z.gtb ZArith.BinInt.Z.leb ZArith.BinInt.Z.ltb
*)
