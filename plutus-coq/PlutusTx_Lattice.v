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

Require PlutusTx_Bool.
Require PlutusTx_Monoid.
Require PlutusTx_Semigroup.
Import PlutusTx_Bool.Notations.

(* Converted type declarations: *)

Record MeetSemiLattice__Dict (a : Type) := MeetSemiLattice__Dict_Build {
  op_zszr____ : a -> a -> a }.

Definition MeetSemiLattice (a : Type) :=
  forall r__, (MeetSemiLattice__Dict a -> r__) -> r__.
Existing Class MeetSemiLattice.

Record BoundedJoinSemiLattice__Dict (a : Type) :=
  BoundedJoinSemiLattice__Dict_Build {
  bottom__ : a }.

Definition op_zszr__ `{g__0__ : MeetSemiLattice a} : a -> a -> a :=
  g__0__ _ (op_zszr____ a).

Notation "'_/\_'" := (op_zszr__).

Infix "/\" := (_/\_).

Inductive Meet a : Type := | MkMeet : a -> Meet a.

Record JoinSemiLattice__Dict (a : Type) := JoinSemiLattice__Dict_Build {
  op_zrzs____ : a -> a -> a }.

Definition JoinSemiLattice (a : Type) :=
  forall r__, (JoinSemiLattice__Dict a -> r__) -> r__.
Existing Class JoinSemiLattice.

Definition op_zrzs__ `{g__0__ : JoinSemiLattice a} : a -> a -> a :=
  g__0__ _ (op_zrzs____ a).

Notation "'_\/_'" := (op_zrzs__).

Infix "\/" := (_\/_).

Inductive Join a : Type := | MkJoin : a -> Join a.

Record BoundedMeetSemiLattice__Dict (a : Type) :=
  BoundedMeetSemiLattice__Dict_Build {
  top__ : a }.

Definition BoundedMeetSemiLattice (a : Type) `{MeetSemiLattice a} :=
  forall r__, (BoundedMeetSemiLattice__Dict a -> r__) -> r__.
Existing Class BoundedMeetSemiLattice.

Definition top `{g__0__ : BoundedMeetSemiLattice a} : a :=
  g__0__ _ (top__ a).

Definition BoundedJoinSemiLattice (a : Type) `{JoinSemiLattice a} :=
  forall r__, (BoundedJoinSemiLattice__Dict a -> r__) -> r__.
Existing Class BoundedJoinSemiLattice.

Definition bottom `{g__0__ : BoundedJoinSemiLattice a} : a :=
  g__0__ _ (bottom__ a).

Arguments MkMeet {_} _.

Arguments MkJoin {_} _.

(* Converted value declarations: *)

Local Definition Semigroup__Join_op_zlzg__ {inst_a : Type} `{JoinSemiLattice
  inst_a}
   : Join inst_a -> Join inst_a -> Join inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkJoin l, MkJoin r => MkJoin (l \/ r)
    end.

Program Instance Semigroup__Join {a : Type} `{JoinSemiLattice a}
   : PlutusTx_Semigroup.Semigroup (Join a) :=
  fun _ k__ =>
    k__ {| PlutusTx_Semigroup.op_zlzg____ := Semigroup__Join_op_zlzg__ |}.

Local Definition Monoid__Join_mempty {inst_a : Type} `{BoundedJoinSemiLattice
  inst_a}
   : Join inst_a :=
  MkJoin bottom.

Program Instance Monoid__Join {a : Type} `{BoundedJoinSemiLattice a}
   : PlutusTx_Monoid.Monoid (Join a) :=
  fun _ k__ => k__ {| PlutusTx_Monoid.mempty__ := Monoid__Join_mempty |}.

Local Definition Semigroup__Meet_op_zlzg__ {inst_a : Type} `{MeetSemiLattice
  inst_a}
   : Meet inst_a -> Meet inst_a -> Meet inst_a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | MkMeet l, MkMeet r => MkMeet (l /\ r)
    end.

Program Instance Semigroup__Meet {a : Type} `{MeetSemiLattice a}
   : PlutusTx_Semigroup.Semigroup (Meet a) :=
  fun _ k__ =>
    k__ {| PlutusTx_Semigroup.op_zlzg____ := Semigroup__Meet_op_zlzg__ |}.

Local Definition Monoid__Meet_mempty {inst_a : Type} `{BoundedMeetSemiLattice
  inst_a}
   : Meet inst_a :=
  MkMeet top.

Program Instance Monoid__Meet {a : Type} `{BoundedMeetSemiLattice a}
   : PlutusTx_Monoid.Monoid (Meet a) :=
  fun _ k__ => k__ {| PlutusTx_Monoid.mempty__ := Monoid__Meet_mempty |}.

Local Definition JoinSemiLattice__bool_op_zrzs__ : bool -> bool -> bool :=
  _PlutusTx_Bool.||_.

Program Instance JoinSemiLattice__bool : JoinSemiLattice bool :=
  fun _ k__ => k__ {| op_zrzs____ := JoinSemiLattice__bool_op_zrzs__ |}.

Local Definition BoundedJoinSemiLattice__bool_bottom : bool :=
  false.

Program Instance BoundedJoinSemiLattice__bool : BoundedJoinSemiLattice bool :=
  fun _ k__ => k__ {| bottom__ := BoundedJoinSemiLattice__bool_bottom |}.

Local Definition MeetSemiLattice__bool_op_zszr__ : bool -> bool -> bool :=
  _PlutusTx_Bool.&&_.

Program Instance MeetSemiLattice__bool : MeetSemiLattice bool :=
  fun _ k__ => k__ {| op_zszr____ := MeetSemiLattice__bool_op_zszr__ |}.

Local Definition BoundedMeetSemiLattice__bool_top : bool :=
  true.

Program Instance BoundedMeetSemiLattice__bool : BoundedMeetSemiLattice bool :=
  fun _ k__ => k__ {| top__ := BoundedMeetSemiLattice__bool_top |}.

Local Definition JoinSemiLattice__op_zt___op_zrzs__ {inst_a : Type} {inst_b
   : Type} `{JoinSemiLattice inst_a} `{JoinSemiLattice inst_b}
   : (inst_a * inst_b)%type -> (inst_a * inst_b)%type -> (inst_a * inst_b)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair a1 b1, pair a2 b2 => pair (a1 \/ a2) (b1 \/ b2)
    end.

Program Instance JoinSemiLattice__op_zt__ {a : Type} {b : Type}
  `{JoinSemiLattice a} `{JoinSemiLattice b}
   : JoinSemiLattice (a * b)%type :=
  fun _ k__ => k__ {| op_zrzs____ := JoinSemiLattice__op_zt___op_zrzs__ |}.

Local Definition BoundedJoinSemiLattice__op_zt___bottom {inst_a : Type} {inst_b
   : Type} `{BoundedJoinSemiLattice inst_a} `{BoundedJoinSemiLattice inst_b}
   : (inst_a * inst_b)%type :=
  pair bottom bottom.

Program Instance BoundedJoinSemiLattice__op_zt__ {a : Type} {b : Type}
  `{BoundedJoinSemiLattice a} `{BoundedJoinSemiLattice b}
   : BoundedJoinSemiLattice (a * b)%type :=
  fun _ k__ => k__ {| bottom__ := BoundedJoinSemiLattice__op_zt___bottom |}.

Local Definition MeetSemiLattice__op_zt___op_zszr__ {inst_a : Type} {inst_b
   : Type} `{MeetSemiLattice inst_a} `{MeetSemiLattice inst_b}
   : (inst_a * inst_b)%type -> (inst_a * inst_b)%type -> (inst_a * inst_b)%type :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | pair a1 b1, pair a2 b2 => pair (a1 /\ a2) (b1 /\ b2)
    end.

Program Instance MeetSemiLattice__op_zt__ {a : Type} {b : Type}
  `{MeetSemiLattice a} `{MeetSemiLattice b}
   : MeetSemiLattice (a * b)%type :=
  fun _ k__ => k__ {| op_zszr____ := MeetSemiLattice__op_zt___op_zszr__ |}.

Local Definition BoundedMeetSemiLattice__op_zt___top {inst_a : Type} {inst_b
   : Type} `{BoundedMeetSemiLattice inst_a} `{BoundedMeetSemiLattice inst_b}
   : (inst_a * inst_b)%type :=
  pair top top.

Program Instance BoundedMeetSemiLattice__op_zt__ {a : Type} {b : Type}
  `{BoundedMeetSemiLattice a} `{BoundedMeetSemiLattice b}
   : BoundedMeetSemiLattice (a * b)%type :=
  fun _ k__ => k__ {| top__ := BoundedMeetSemiLattice__op_zt___top |}.

Local Definition JoinSemiLattice__arrow_op_zrzs__ {inst_b : Type} {inst_a
   : Type} `{JoinSemiLattice inst_b}
   : (inst_a -> inst_b) -> (inst_a -> inst_b) -> inst_a -> inst_b :=
  fun f g a => f a \/ g a.

Program Instance JoinSemiLattice__arrow {b : Type} {a : Type} `{JoinSemiLattice
  b}
   : JoinSemiLattice (a -> b) :=
  fun _ k__ => k__ {| op_zrzs____ := JoinSemiLattice__arrow_op_zrzs__ |}.

Local Definition BoundedJoinSemiLattice__arrow_bottom {inst_b : Type} {inst_a
   : Type} `{BoundedJoinSemiLattice inst_b}
   : inst_a -> inst_b :=
  fun arg_0__ => bottom.

Program Instance BoundedJoinSemiLattice__arrow {b : Type} {a : Type}
  `{BoundedJoinSemiLattice b}
   : BoundedJoinSemiLattice (a -> b) :=
  fun _ k__ => k__ {| bottom__ := BoundedJoinSemiLattice__arrow_bottom |}.

Local Definition MeetSemiLattice__arrow_op_zszr__ {inst_b : Type} {inst_a
   : Type} `{MeetSemiLattice inst_b}
   : (inst_a -> inst_b) -> (inst_a -> inst_b) -> inst_a -> inst_b :=
  fun f g a => f a /\ g a.

Program Instance MeetSemiLattice__arrow {b : Type} {a : Type} `{MeetSemiLattice
  b}
   : MeetSemiLattice (a -> b) :=
  fun _ k__ => k__ {| op_zszr____ := MeetSemiLattice__arrow_op_zszr__ |}.

Local Definition BoundedMeetSemiLattice__arrow_top {inst_b : Type} {inst_a
   : Type} `{BoundedMeetSemiLattice inst_b}
   : inst_a -> inst_b :=
  fun arg_0__ => top.

Program Instance BoundedMeetSemiLattice__arrow {b : Type} {a : Type}
  `{BoundedMeetSemiLattice b}
   : BoundedMeetSemiLattice (a -> b) :=
  fun _ k__ => k__ {| top__ := BoundedMeetSemiLattice__arrow_top |}.

Module Notations.
Notation "'_PlutusTx_Lattice./\_'" := (op_zszr__).
Infix "PlutusTx_Lattice./\" := (_/\_) (at level 99).
Notation "'_PlutusTx_Lattice.\/_'" := (op_zrzs__).
Infix "PlutusTx_Lattice.\/" := (_\/_) (at level 99).
End Notations.

(* External variables:
     Type bool false op_zt__ pair true PlutusTx_Bool.op_zaza__
     PlutusTx_Bool.op_zbzb__ PlutusTx_Monoid.Monoid PlutusTx_Monoid.mempty__
     PlutusTx_Semigroup.Semigroup PlutusTx_Semigroup.op_zlzg____
*)
