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
Require GHC.Base.
Require GHC.Num.
Require PlutusTx_Bool.
Require PlutusTx_Eq.
Require PlutusTx_ErrorCodes.
Require PlutusTx_Ord.
Require PlutusTx_Trace.
Require ZArith.BinInt.
Import GHC.Base.Notations.
Import GHC.Num.Notations.
Import PlutusTx_Bool.Notations.
Import PlutusTx_Eq.Notations.
Import PlutusTx_Ord.Notations.

(* No type declarations to convert. *)

(* Converted value declarations: *)

Definition uncons {a : Type} : list a -> option (a * list a)%type :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => None
    | cons x xs => Some (pair x xs)
    end.

Definition null {a : Type} : list a -> bool :=
  fun arg_0__ => match arg_0__ with | nil => true | _ => false end.

Definition map {a : Type} {b : Type} : (a -> b) -> list a -> list b :=
  fun f =>
    let go : list a -> list b :=
      fix go (arg_0__ : list a) : list b
        := match arg_0__ with
           | nil => nil
           | cons x xs => cons (f x) (go xs)
           end in
    go.

Fixpoint and (arg_0__ : list bool) : bool
  := match arg_0__ with
     | nil => true
     | cons x xs => if x : bool then and xs else false
     end.

Fixpoint or (arg_0__ : list bool) : bool
  := match arg_0__ with
     | nil => false
     | cons x xs => if x : bool then true else or xs
     end.

Definition any {a : Type} : (a -> bool) -> list a -> bool :=
  fun f =>
    let go : list a -> bool :=
      fix go (arg_0__ : list a) : bool
        := match arg_0__ with
           | nil => false
           | cons x xs => if f x : bool then true else go xs
           end in
    go.

Definition all {a : Type} : (a -> bool) -> list a -> bool :=
  fun f =>
    let go : list a -> bool :=
      fix go (arg_0__ : list a) : bool
        := match arg_0__ with
           | nil => true
           | cons x xs => if f x : bool then go xs else false
           end in
    go.

Definition elem {a : Type} `{PlutusTx_Eq.Eq a} : a -> list a -> bool :=
  any GHC.Base.∘ _PlutusTx_Eq.==_.

Definition notElem {a : Type} `{PlutusTx_Eq.Eq a} : a -> list a -> bool :=
  fun a => PlutusTx_Bool.not GHC.Base.∘ elem a.

Definition find {a : Type} : (a -> bool) -> list a -> option a :=
  fun f =>
    let go : list a -> option a :=
      fix go (arg_0__ : list a) : option a
        := match arg_0__ with
           | nil => None
           | cons x xs => if f x : bool then Some x else go xs
           end in
    go.

Definition foldr {a : Type} {b : Type} : (a -> b -> b) -> b -> list a -> b :=
  fun f acc =>
    let go : list a -> b :=
      fix go (arg_0__ : list a) : b
        := match arg_0__ with
           | nil => acc
           | cons x xs => f x (go xs)
           end in
    go.

Axiom foldl : forall {a : Type},
              forall {b : Type}, (b -> a -> b) -> b -> list a -> b.

Definition op_zpzp__ {a : Type} : list a -> list a -> list a :=
  fun l r => foldr cons r l.

Notation "'_++_'" := (op_zpzp__).

Infix "++" := (_++_).

Definition concat {a : Type} : list (list a) -> list a :=
  foldr _++_ nil.

Definition concatMap {a : Type} {b : Type}
   : (a -> list b) -> list a -> list b :=
  fun f => foldr (fun x ys => f x ++ ys) nil.

Definition filter {a : Type} : (a -> bool) -> list a -> list a :=
  fun p => foldr (fun e xs => if p e : bool then cons e xs else xs) nil.

Definition listToMaybe {a : Type} : list a -> option a :=
  fun arg_0__ => match arg_0__ with | nil => None | cons x _ => Some x end.

Definition uniqueElement {a : Type} : list a -> option a :=
  fun arg_0__ => match arg_0__ with | cons x nil => Some x | _ => None end.

Definition findIndices {a : Type} : (a -> bool) -> list a -> list BinNums.Z :=
  fun p =>
    let fix go i l
      := match l with
         | nil => nil
         | cons x xs =>
             let indices := go (Z.add i #1) xs in
             if p x : bool
             then cons i indices
             else indices
         end in
    go #0.

Axiom findIndex : forall {a : Type}, (a -> bool) -> list a -> option BinNums.Z.

Definition op_znzn__ {a : Type} : list a -> BinNums.Z -> a :=
  fun arg_0__ arg_1__ =>
    match arg_0__, arg_1__ with
    | _, n0 =>
        if n0 PlutusTx_Ord.< #0 : bool
        then PlutusTx_Trace.traceError PlutusTx_ErrorCodes.negativeIndexError else
        match arg_0__, arg_1__ with
        | xs0, n0 =>
            let go : BinNums.Z -> list a -> a :=
              fix go (arg_2__ : BinNums.Z) (arg_3__ : list a) : a
                := match arg_2__, arg_3__ with
                   | _, nil => PlutusTx_Trace.traceError PlutusTx_ErrorCodes.indexTooLargeError
                   | n, cons x xs =>
                       if ZArith.BinInt.Z.eqb n #0 : bool
                       then x
                       else go (Z.sub n #1) xs
                   end in
            go n0 xs0
        end
    end.

Notation "'_!!_'" := (op_znzn__).

Infix "!!" := (_!!_) (at level 99).

Definition reverse {a : Type} : list a -> list a :=
  fun l =>
    let fix rev arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | nil, a => a
         | cons x xs, a => rev xs (cons x a)
         end in
    rev l nil.

Fixpoint zip {a : Type} {b : Type} (arg_0__ : list a) (arg_1__ : list b) : list
                                                                           (a * b)%type
  := match arg_0__, arg_1__ with
     | nil, _bs => nil
     | _as, nil => nil
     | cons a as_, cons b bs => cons (pair a b) (zip as_ bs)
     end.

Fixpoint unzip {a : Type} {b : Type} (arg_0__ : list (a * b)%type) : (list a *
                                                                      list b)%type
  := match arg_0__ with
     | nil => pair nil nil
     | cons (pair x y) xys =>
         let 'pair xs ys := unzip xys in
         pair (cons x xs) (cons y ys)
     end.

Definition head {a : Type} : list a -> a :=
  fun arg_0__ =>
    match arg_0__ with
    | nil => PlutusTx_Trace.traceError PlutusTx_ErrorCodes.headEmptyListError
    | cons x _ => x
    end.

Fixpoint last {a : Type} (arg_0__ : list a) : a
  := match arg_0__ with
     | nil => PlutusTx_Trace.traceError PlutusTx_ErrorCodes.lastEmptyListError
     | cons x nil => x
     | cons _ xs => last xs
     end.

Definition tail {a : Type} : list a -> list a :=
  fun arg_0__ =>
    match arg_0__ with
    | cons _ as_ => as_
    | nil => PlutusTx_Trace.traceError PlutusTx_ErrorCodes.tailEmptyListError
    end.

Fixpoint take {a : Type} (arg_0__ : BinNums.Z) (arg_1__ : list a) : list a
  := match arg_0__, arg_1__ with
     | n, _ =>
         if n PlutusTx_Ord.<= #0 : bool then nil else
         match arg_0__, arg_1__ with
         | _, nil => nil
         | n, cons x xs => cons x (take (Z.sub n #1) xs)
         end
     end.

Fixpoint drop {a : Type} (arg_0__ : BinNums.Z) (arg_1__ : list a) : list a
  := match arg_0__, arg_1__ with
     | n, xs =>
         if n PlutusTx_Ord.<= #0 : bool then xs else
         match arg_0__, arg_1__ with
         | _, nil => nil
         | n, cons _ xs => drop (Z.sub n #1) xs
         end
     end.

Definition splitAt {a : Type} : BinNums.Z -> list a -> (list a * list a)%type :=
  fun n xs =>
    let go {a} : BinNums.Z -> list a -> (list a * list a)%type :=
      fix go (arg_0__ : BinNums.Z) (arg_1__ : list a) : (list a * list a)%type
        := match arg_0__, arg_1__ with
           | _, nil => pair nil nil
           | m, cons y ys =>
               if m PlutusTx_Eq.== #1 : bool then pair (cons y nil) ys else
               let 'pair zs ws := go (Z.sub m #1) ys in
               pair (cons y zs) ws
           end in
    if n PlutusTx_Ord.<= #0 : bool then pair nil xs else
    go n xs.

Definition elemBy {a} : (a -> a -> bool) -> a -> list a -> bool :=
  fun eq y =>
    let go : list a -> bool :=
      fix go (arg_0__ : list a) : bool
        := match arg_0__ with
           | nil => false
           | cons x xs => eq x y PlutusTx_Bool.|| go xs
           end in
    go.

Definition nubBy {a : Type} : (a -> a -> bool) -> list a -> list a :=
  fun eq l =>
    let fix nubBy' arg_0__ arg_1__
      := match arg_0__, arg_1__ with
         | nil, _ => nil
         | cons y ys, xs =>
             if elemBy eq y xs : bool then nubBy' ys xs else
             cons y (nubBy' ys (cons y xs))
         end in
    nubBy' l nil.

Definition nub {a : Type} `{PlutusTx_Eq.Eq a} : list a -> list a :=
  nubBy _PlutusTx_Eq.==_.

Definition zipWith {a : Type} {b : Type} {c : Type}
   : (a -> b -> c) -> list a -> list b -> list c :=
  fun f =>
    let go : list a -> list b -> list c :=
      fix go (arg_0__ : list a) (arg_1__ : list b) : list c
        := match arg_0__, arg_1__ with
           | nil, _ => nil
           | _, nil => nil
           | cons x xs, cons y ys => cons (f x y) (go xs ys)
           end in
    go.

Definition dropWhile {a : Type} : (a -> bool) -> list a -> list a :=
  fun p =>
    let go : list a -> list a :=
      fix go (arg_0__ : list a) : list a
        := match arg_0__ with
           | nil => nil
           | (cons x xs' as xs) => if p x : bool then go xs' else xs
           end in
    go.

Axiom replicate : forall {a : Type}, BinNums.Z -> a -> list a.

Definition select {a}
   : (a -> bool) -> a -> (list a * list a)%type -> (list a * list a)%type :=
  fun arg_0__ arg_1__ arg_2__ =>
    match arg_0__, arg_1__, arg_2__ with
    | p, x, pair ts fs =>
        if p x : bool then pair (cons x ts) fs else
        pair ts (cons x fs)
    end.

Definition partition {a : Type}
   : (a -> bool) -> list a -> (list a * list a)%type :=
  fun p xs => foldr (select p) (pair nil nil) xs.

Axiom sortBy : forall {a : Type}, (a -> a -> comparison) -> list a -> list a.

Definition sort {a : Type} `{PlutusTx_Ord.Ord a} : list a -> list a :=
  sortBy PlutusTx_Ord.compare.

Module Notations.
Notation "'_PlutusTx_List.++_'" := (op_zpzp__).
Infix "PlutusTx_List.++" := (_++_) (at level 99).
Notation "'_PlutusTx_List.!!_'" := (op_znzn__).
Infix "PlutusTx_List.!!" := (_!!_) (at level 99).
End Notations.

(* External variables:
     None Some Type bool comparison cons false list nil op_zt__ option pair true
     BinNums.Z GHC.Base.op_z2218U__ GHC.Num.fromInteger PlutusTx_Bool.not
     PlutusTx_Bool.op_zbzb__ PlutusTx_Eq.Eq PlutusTx_Eq.op_zeze__
     PlutusTx_ErrorCodes.headEmptyListError PlutusTx_ErrorCodes.indexTooLargeError
     PlutusTx_ErrorCodes.lastEmptyListError PlutusTx_ErrorCodes.negativeIndexError
     PlutusTx_ErrorCodes.tailEmptyListError PlutusTx_Ord.Ord PlutusTx_Ord.compare
     PlutusTx_Ord.op_zl__ PlutusTx_Ord.op_zlze__ PlutusTx_Trace.traceError Z.add
     Z.sub ZArith.BinInt.Z.eqb
*)
