Require Import Id.
Require Import Core.
Require Import BasicTypes.
Import GHC.Base.Notations.

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.BinNat.
Require Import Psatz.

Import ListNotations.

Require Import Proofs.Forall.
Require Import Proofs.Core.
Require Import Proofs.CoreInduct.
Require Import Proofs.Var.
Require Import Proofs.VarSet.
Require Import Proofs.VarSetStrong.
Require Import Proofs.GhcTactics.

Set Bullet Behavior "Strict Subproofs".

Open Scope nat_scope.

Notation "a =? b" := (Nat.eqb a b).
Notation "a <=? b" := (Nat.leb a b).
Notation "a <? b" := (Nat.ltb a b).

(** * Join point invariants *)

(**
The following is taken from the GHC source code:

Note [Invariants on join points]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Join points must follow these invariants:

  1. All occurrences must be tail calls. Each of these tail calls must pass the
     same number of arguments, counting both types and values; we call this the
     "join arity" (to distinguish from regular arity, which only counts values).

  2. For join arity n, the right-hand side must begin with at least n lambdas.
     No ticks, no casts, just lambdas!  C.f. CoreUtils.joinRhsArity.

  2a. Moreover, this same constraint applies to any unfolding of the binder.
     Reason: if we want to push a continuation into the RHS we must push it
     into the unfolding as well.

  3. If the binding is recursive, then all other bindings in the recursive group
     must also be join points.

  4. The binding's type must not be polymorphic in its return type (as defined
     in Note [The polymorphism rule of join points]).
*)

(** 

We can check 1, 2, 3.

We will be able to check 2a when we translate more of IdInfo.

We will be able to check 4 when we translate types.

Additionally, we found these invariant:

 * The join arity must be non-negative.
 * A lambda-, case- or pattern-bound variable is not a join point
*)

(** ** [updJPS] and [updJPSs] *)

(**
As we go under a binder [x], we either have to add it to the set of valid
join points, or remove it from there, depending on whether [x] is a join point:
*)

Definition updJPS jps v :=
   if isJoinId v
   then extendVarSet jps v
   else delVarSet    jps v.

(**
We also have to do this for lists:
*)

Definition updJPSs jps vs :=
  fold_left updJPS vs jps.

(**
These two functions behave very similar to [extendVarSet] and [delVarset], and we
have a number of simiar lemmas:
**)

Lemma updJPSs_nil:
  forall jps, updJPSs jps [] = jps.
Proof. intros. reflexivity. Qed.

Lemma updJPSs_cons:
  forall jps v vs, updJPSs jps (v :: vs) = updJPSs (updJPS jps v) vs.
Proof. intros. reflexivity. Qed.

Lemma updJPSs_singleton:
  forall jps v, updJPSs jps [v] = updJPS jps v.
Proof. intros. reflexivity. Qed.


Lemma updJPSs_append:
  forall jps vs1 vs2, updJPSs jps (vs1 ++ vs2) = updJPSs (updJPSs jps vs1) vs2.
Proof. intros. apply fold_left_app. Qed.

Lemma updJPS_not_joinId:
  forall jps v,
  isJoinId v = false ->
  updJPS jps v = delVarSet jps v.
Proof. intros. unfold updJPS. rewrite H. reflexivity. Qed.

Lemma updJPS_joinId:
  forall jps v,
  isJoinId v = true ->
  updJPS jps v = extendVarSet jps v.
Proof. intros. unfold updJPS. rewrite H. reflexivity. Qed.

Lemma updJPSs_not_joinId:
  forall jps vs,
  forallb (fun v => negb (isJoinId v)) vs = true ->
  updJPSs jps vs = delVarSetList jps vs.
Proof. 
  intros. induction vs using rev_ind.
  * rewrite delVarSetList_nil. reflexivity.
  * rewrite updJPSs_append, updJPSs_cons, updJPSs_nil.
    rewrite delVarSetList_app, delVarSetList_cons, delVarSetList_nil.
    rewrite forallb_app in H. simpl in H. rewrite andb_true_r, andb_true_iff, negb_true_iff in H. 
    rewrite IHvs by intuition.
    rewrite updJPS_not_joinId by intuition.
    reflexivity.
Qed.

Lemma updJPSs_joinId:
  forall jps vs,
  forallb isJoinId vs = true ->
  updJPSs jps vs = extendVarSetList jps vs.
Proof. 
  intros. induction vs using rev_ind.
  * rewrite extendVarSetList_nil. reflexivity.
  * rewrite updJPSs_append, updJPSs_cons, updJPSs_nil.
    rewrite extendVarSetList_append, extendVarSetList_cons, extendVarSetList_nil.
    rewrite forallb_app in H. simpl in H. rewrite andb_true_r, andb_true_iff in H. 
    rewrite IHvs by intuition.
    rewrite updJPS_joinId by intuition.
    reflexivity.
Qed.

Lemma elemVarSet_updJPS_l:
  forall v jps v',
  (v' GHC.Base.== v) = false ->
  elemVarSet v (updJPS jps v') = elemVarSet v jps.
Proof.
  intros.
  unfold updJPS.
  destruct_match.
  + rewrite elemVarSet_extendVarSet.
    rewrite H.
    reflexivity.
  + rewrite elemVarSet_delVarSet.
    rewrite H.
    reflexivity.
Qed.

Lemma elemVarSet_updJPS_cong:
  forall v jps1 jps2 v',
  ((v' GHC.Base.== v) = false -> elemVarSet v jps1 = elemVarSet v jps2) ->
  elemVarSet v (updJPS jps1 v') = elemVarSet v (updJPS jps2 v').
Proof.
  intros.
  unfold updJPS.
  destruct_match.
  + rewrite !elemVarSet_extendVarSet.
    destruct (v' GHC.Base.== v); intuition.
  + rewrite !elemVarSet_delVarSet.
    destruct (v' GHC.Base.== v); intuition.
Qed.


Lemma elemVarSet_updJPSs_l:
  forall v jps vs,
  elemVarSet v jps  = true  ->
  elemVarSet v (mkVarSet vs) = false ->
  elemVarSet v (updJPSs jps vs) = true .
Proof.
  intros.
  revert jps v H H0. induction vs; intros.
  * apply H.
  * simpl.
    rewrite elemVarSet_mkVarSet_cons in H0.
    destruct H0.
    apply IHvs.
    + rewrite elemVarSet_updJPS_l by assumption.
      assumption.
    + assumption.
Qed.

Lemma subVarSet_updJPS_extendVarSet:
  forall jps isvs v,
  subVarSet jps isvs = true ->
  subVarSet (updJPS jps v) (extendVarSet isvs v) = true.
Proof.
  intros.
  unfold updJPS.
  destruct_match.
  * apply subVarSet_extendVarSet_both.
    assumption.
  * eapply subVarSet_trans.
    apply subVarSet_delVarSet.
    apply subVarSet_extendVarSet.
    eassumption.
Qed.

Lemma subVarSet_updJPSs_extendVarSetList:
  forall jps isvs vs,
  subVarSet jps isvs = true ->
  subVarSet (updJPSs jps vs) (extendVarSetList isvs vs) = true.
Proof.
  intros. revert jps isvs H. induction vs; intros.
  * rewrite updJPSs_nil, extendVarSetList_nil.
    assumption.
  * rewrite updJPSs_cons, extendVarSetList_cons.
    apply IHvs.
    apply subVarSet_updJPS_extendVarSet.
    assumption.
Qed.

(** ** The definition of the invariants *)

(**
In this module, we define the invariant as a boolean predicate, using [Fixpoint].

Ideally, we would define these funtions

 * [isJoinPointsValid] for expressions (with an accumulator to count the number
   of arguments this expression is applied to).
 * [isJoinRHS] for the right-hand sides of join points (to strip off the correct
   number of [Lam] constructors)
 * [isJoinPointsValidPair] for when a pair (binder + definition) is valid, which
   builds on the two aboe.

Unfortunately, requirements from Coq’s termination checker make things a bit
more complicated…

We first define [isJoinPointsValidPair_aux], which is [isJoinPointsValidPair]
abstracted over the other two.
*)

Definition isJoinPointsValidPair_aux
  isJoinPointsValid isJoinRHS_aux
  (v : CoreBndr) (rhs : CoreExpr) (jps : VarSet) : bool :=
    match isJoinId_maybe v with
    | None => isJoinPointsValid rhs 0 emptyVarSet  (* Non-tail-call position *)
    | Some a => 
      if (a =? 0) (* Uh, all for the termination checker *)
      then isJoinPointsValid rhs 0 jps            (* tail-call position *)
      else isJoinRHS_aux a rhs jps                (* tail-call position *)
    end.

(** See below for why we have the [a=0] case here. *)


(** Now the other two functions: *)

Fixpoint isJoinPointsValid (e : CoreExpr) (n : nat) (jps : VarSet) {struct e} : bool :=
  match e with
  | Mk_Var v => match isJoinId_maybe v with
    | None => true
    | Some a => isLocalVar v && (a <=? n) && elemVarSet v jps
    end
  | Lit l => true
  | App e1 e2 =>
    isJoinPointsValid e1 (n+1) jps &&   (* Tail-call-position *)
    isJoinPointsValid e2 0 emptyVarSet    (* Non-tail-call position *)
  | Lam v e =>
    negb (isJoinId v) &&
    isJoinPointsValid e 0 emptyVarSet     (* Non-tail-call position *)
  | Let (NonRec v rhs) body => 
      isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS_aux v rhs jps &&
      let jps' := updJPS jps v in
      isJoinPointsValid body 0 jps'
  | Let (Rec pairs) body => 
      negb (List.null pairs) &&  (* Not join-point-specific, could be its own invariant *)
      (forallb (fun p => negb (isJoinId (fst p))) pairs ||
       forallb (fun p =>       isJoinId (fst p))  pairs) &&
      let jps' := updJPSs jps (map fst pairs) in
      forallb (fun '(v,e) => isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS_aux v e jps') pairs &&
      isJoinPointsValid body 0 jps'
  | Case scrut bndr ty alts  => 
    negb (isJoinId bndr) &&
    isJoinPointsValid scrut 0 emptyVarSet &&  (* Non-tail-call position *)
    let jps' := delVarSet jps bndr in
    forallb (fun '(dc,pats,rhs) =>
      let jps'' := delVarSetList jps' pats  in
      forallb (fun v => negb (isJoinId v)) pats &&
      isJoinPointsValid rhs 0 jps'') alts  (* Tail-call position *)
  | Cast e _ =>    isJoinPointsValid e 0 jps
(*  | Tick _ e =>    isJoinPointsValid e 0 jps *)
  | Mk_Type _  =>   true
  | Mk_Coercion _ => true 
  end
with isJoinRHS_aux (a : JoinArity) (rhs : CoreExpr) (jps : VarSet) {struct rhs} : bool :=
  if a <? 1 then false else
  match rhs with
    | Lam v e => negb (isJoinId v) &&
                 if a =? 1
                 then isJoinPointsValid e 0 (delVarSet jps v) (* tail-call position *)
                 else isJoinRHS_aux (a-1) e (delVarSet jps v)
    | _ => false
    end.

(**
The definition of [isJoinRHS_aux] is not what we want: Ideally, in the [Some] case in
[isJoinPointsValidPair_aux] we’d simply call [isJoinRHS], and if the join arity is actually
[0], then [isJoinRHS] callse [isJoinPointsValid] directly. But then the argument would not
decrease going from [isJoinRHS] to [isJoinPointsValid], and the termination checker would
not be happy. So we have to write [isJoinRHS_aux] in a way that it *always* destructs its
argument.
*)

(**
Convenience definitions, including the [isJoinRHS] we would have liked to write.
*)


Definition isJoinRHS rhs a jps :=
      if (a =? 0)
      then isJoinPointsValid rhs 0 jps
      else isJoinRHS_aux a rhs jps.


Definition isjoinPointsAlt : CoreAlt -> VarSet -> bool :=
  fun '(dc,pats,rhs) jps =>
      let jps'' := delVarSetList jps pats  in
      forallb (fun v => negb (isJoinId v)) pats &&
      isJoinPointsValid rhs 0 jps''.

Definition isJoinPointsValidPair := isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS_aux.

(**
Conjuction of [isJoinId] and [isJoinPointsValidPair]
*)

Definition isValidJoinPointsPair
  (v : CoreBndr) (rhs : CoreExpr) (jps : VarSet) : bool :=
    match isJoinId_maybe v with
    | None => false (* NB *)
    | Some a => isJoinRHS rhs a jps
    end.



(** Join-point validity of whole programs *)

Definition isJoinPointsValidProgram (pgm : CoreProgram)  :=
  Forall (fun '(v,e) =>
    isJoinId v = false /\
    isJoinPointsValid e 0 emptyVarSet = true) (flattenBinds pgm).

(** ** Lemmas *)

Lemma isJoinPointsValidPair_isJoinPoints_isJoinRHS:
  forall v rhs jps a,
  isJoinPointsValidPair v rhs jps = true ->
  isJoinId_maybe v = Some a ->
  isJoinRHS rhs a jps = true.
Proof.
  intros.
  unfold isJoinPointsValidPair,isJoinPointsValidPair_aux in H.
  rewrite H0 in H.
  apply H.
Qed.

Lemma isJoinPointsValidPair_isJoinRHS:
  forall v rhs jps a,
  isJoinId_maybe v = Some a ->
  isJoinPointsValidPair v rhs jps = true <->
  isJoinRHS rhs a jps = true.
Proof.
  intros.
  unfold isJoinPointsValidPair,isJoinPointsValidPair_aux.
  rewrite H.
  unfold isJoinRHS.
  reflexivity.
Qed.

Lemma isJoinPointsValidPair_isJoinPointsValid:
  forall v rhs jps,
  isJoinId_maybe v = None ->
  isJoinPointsValidPair v rhs jps = true <->
  isJoinPointsValid rhs 0 emptyVarSet = true.
Proof.
  intros.
  unfold isJoinPointsValidPair,isJoinPointsValidPair_aux.
  rewrite H.
  unfold isJoinRHS.
  reflexivity.
Qed.



Lemma isValidJoinPointsPair_isJoinPointsValidPair:
  forall v rhs jps,
  isValidJoinPointsPair v rhs jps = true -> isJoinPointsValidPair v rhs jps = true.
Proof.
  intros.
  unfold isValidJoinPointsPair, isJoinPointsValidPair, isJoinPointsValidPair_aux in *.
  destruct_match.
  * assumption.
  * congruence.
Qed.

Lemma isValidJoinPointsPair_isJoinId:
  forall v rhs jps,
  isValidJoinPointsPair v rhs jps = true -> isJoinId v = true.
Proof.
  intros.
  unfold isValidJoinPointsPair in *.
  rewrite isJoinId_eq.
  destruct_match; congruence.
Qed.


Lemma Forall_isValidJoinPointsPair_forallb_isJoinId_isJoinPointsValidPair:
  forall pairs jps,
  Forall (fun p => isValidJoinPointsPair (fst p) (snd p) jps = true) pairs <->
  forallb (fun p : Var * Expr CoreBndr => isJoinId (fst p)) pairs = true /\
  forallb (fun '(v, e) => isJoinPointsValidPair v e jps) pairs = true.
Proof.
  intros.
  rewrite Forall_forall, !forallb_forall.
  split; intro; only 1: split.
  * intros [v e] HIn.
    specialize (H _ HIn).
    simpl in *.
    eapply isValidJoinPointsPair_isJoinId; eassumption.
  * intros [v e] HIn.
    specialize (H _ HIn).
    simpl in *.
    eapply isValidJoinPointsPair_isJoinPointsValidPair; eassumption.
  * intros [v e] HIn.
    destruct H.
    specialize (H _ HIn).
    specialize (H0 _ HIn).
    simpl in *.
    unfold isValidJoinPointsPair in *.
    rewrite isJoinId_eq in H.
    destruct_match; auto.
    eapply isJoinPointsValidPair_isJoinPoints_isJoinRHS; eassumption.
Qed.

Lemma isJoinRHS_mkLams:
  forall vs e jps,
  Forall (fun v => isJoinId v = false) vs ->
  isJoinPointsValid e 0 (delVarSetList jps vs) = true <->
  isJoinRHS (mkLams vs e) (length vs) jps = true.
Proof.
  intros. revert jps H.
  induction vs; intros jps Hdisjoint.
  * rewrite delVarSetList_nil.
    reflexivity.
  * simpl.
    replace (mkLams _ _) with (Lam a (mkLams vs e)) by reflexivity.
    rewrite delVarSetList_cons.
    unfold isJoinRHS.
    destruct_match.
    + apply EqNat.beq_nat_true in Heq. congruence.
    + clear Heq.
      inversion_clear Hdisjoint.
      rewrite IHvs by assumption.
      simpl.
      rewrite PeanoNat.Nat.sub_0_r.
      unfold isJoinRHS.
      rewrite H.
      reflexivity.
Qed.

Lemma isJoinRHS_mkLams2:
  forall vs e jps,
  isJoinRHS (mkLams vs e) (length vs) jps = true ->
  Forall (fun v => isJoinId v = false) vs /\ isJoinPointsValid e 0 (updJPSs jps vs) = true.
Proof.
  intros. revert jps H.
  induction vs; intros jps H.
  * rewrite updJPSs_nil.
    intuition.
  * simpl.
    replace (mkLams _ _) with (Lam a (mkLams vs e)) in H by reflexivity.
    unfold isJoinRHS in H.
    destruct_match.
    + apply EqNat.beq_nat_true in Heq. simpl in Heq. congruence.
    + clear Heq.
      simpl in H.
      rewrite PeanoNat.Nat.sub_0_r in H.
      rewrite andb_true_iff, negb_true_iff in H.
      destruct H as [Hnot_isJoin H].
      change (isJoinRHS (mkLams vs e) (length vs) (delVarSet jps a) = true) in H.
      specialize (IHvs _ H).
      unfold updJPS. rewrite Hnot_isJoin.
      intuition.
Qed.

Lemma isJoinRHS_mkLams3:
  forall e ja jps,
  isJoinRHS e ja jps = true ->
  exists body vs,
  e = mkLams vs body /\ ja = length vs.
Proof.
  intros. revert e jps H. induction ja; intros.
  * exists e. exists nil.
    repeat apply conj.
    + reflexivity.
    + reflexivity.
  * unfold isJoinRHS in H.
    destruct (PeanoNat.Nat.eqb_spec (S ja) 0); only 1: (exfalso; lia). clear n.
    destruct e; simpl in H; try congruence.
    simpl_bool.
    destruct H as [HnotJoinId H].
    rewrite negb_true_iff in HnotJoinId.
    rewrite PeanoNat.Nat.sub_0_r in H.
    change (isJoinRHS e ja (delVarSet jps c) = true) in H.
    specialize (IHja _ _ H).
    destruct IHja as [body [vs [Heq1 Heq2]]].
    subst.
    exists body. exists (c :: vs).
    repeat apply conj.
    + reflexivity.
    + reflexivity.
Qed.

Lemma isJoinPointsValid_mkVarApps:
  forall e n vs jps,
  Forall (fun v => isJoinId v = false) vs ->
  isJoinPointsValid e (n + length vs) jps = true ->
  isJoinPointsValid (mkVarApps e vs) n jps = true.
Proof.
  intros ???? Hnot_iJI HiJPV.
  unfold mkVarApps.
  rewrite Foldable.hs_coq_foldl_list.
  revert e HiJPV.
  induction Hnot_iJI; intros.
  * simpl.
    simpl in HiJPV. rewrite PeanoNat.Nat.add_0_r in HiJPV.
    assumption.
  * simpl.
    apply IHHnot_iJI; clear IHHnot_iJI.
    simpl.
    rewrite andb_true_iff. split.
    - simpl in HiJPV.
      replace (_ + _ + _) with (n + S (length l)) by lia. 
      assumption.
    - unfold varToCoreExpr.
      repeat destruct_match; try reflexivity.
      + (* new case from debugIsOn *)
        rewrite andb_false_r in Heq.
        discriminate.
      + simpl. rewrite isJoinId_eq in H.
      destruct_match; congruence. 
Qed.

Lemma isJoinPointsValid_MkLetRec: forall pairs body jps,
  isJoinPointsValid (mkLetRec pairs body) 0 jps = true <->
  ( (forallb (fun p => negb (isJoinId (fst p))) pairs ||
     forallb (fun p =>       isJoinId (fst p))  pairs) &&
     let jps' := updJPSs jps (map fst pairs) in
     forallb (fun '(v,e) => isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS_aux v e jps') pairs &&
     isJoinPointsValid body 0 jps'
  ) = true.
Proof.
  intros.
  unfold mkLetRec.
  destruct pairs; try reflexivity.
Qed.

Lemma isJoinPointsValid_MkLet_Rec: forall pairs body jps,
  isJoinPointsValid (mkLet (Rec pairs) body) 0 jps = true <->
  ( (forallb (fun p => negb (isJoinId (fst p))) pairs ||
     forallb (fun p =>       isJoinId (fst p))  pairs) &&
     let jps' := updJPSs jps (map fst pairs) in
     forallb (fun '(v,e) => isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS_aux v e jps') pairs &&
     isJoinPointsValid body 0 jps'
  ) = true.
Proof.
  intros.
  destruct pairs; try reflexivity.
Qed.


(**
There may be more arguments passed to the expression.
*)

Lemma isJoinPointsValid_more_args:
  forall e n n' jps,
  n <= n' ->
  isJoinPointsValid e n jps = true ->
  isJoinPointsValid e n' jps = true.
Proof.
  intros.
  revert n n' jps H H0. apply (core_induct e);
    intros; simpl in *;
    try assumption.
  * (* Var *)
    destruct_match; only 2: reflexivity.
    destruct (PeanoNat.Nat.leb_spec j n), (PeanoNat.Nat.leb_spec j n').
    - assumption.
    - exfalso. lia.
    - exfalso. simpl_bool. destruct H0. congruence.
    - assumption.
  * (* App *)
    simpl_bool. destruct H2. split.
    - refine (H _ _ _ _ H2). lia.
    - assumption.
Qed.

(** ** Lemmas about freshness *)

Lemma forallb_conq:
  forall a (P1 P2 : a -> bool) xs,
  Forall (fun x => P1 x = P2 x) xs ->
  forallb P1 xs = forallb P2 xs.
Proof.
  intros.
  induction H.
  * reflexivity.
  * simpl. f_equal; assumption.
Qed.

Require Import CoreFVs.
Require Import Proofs.CoreFVs.
Require Import Proofs.VarSetFSet.

(* There is some worrying duplication/similarity with
[WellScoped_extendVarSetList_fresh_between] *)
Lemma isJoinPointsValid_fresh_updJPSs_aux:
  forall (vs2 vs3 : list Var) (e : CoreExpr) (jps : VarSet),
  disjointVarSet (delVarSetList (exprFreeVars e) vs3) (mkVarSet vs2) = true ->
  (forall n,
  isJoinPointsValid e n (updJPSs jps (vs2 ++ vs3)) =
  isJoinPointsValid e n (updJPSs jps vs3)
  )
  /\
  (forall v, isJoinRHS_aux v e (updJPSs jps (vs2 ++ vs3)) =
  isJoinRHS_aux v e (updJPSs jps vs3)).
Proof.
  intros.
  rewrite <- delVarSetList_rev in H.
  revert vs3 jps H.
  apply (core_induct e); intros;
    (split; intro; simpl; [| try solve[ destruct_match; reflexivity]] ).
  - simpl.
    destruct_match; only 2: reflexivity.
    destruct (isLocalVar v) eqn:?; only 2: reflexivity.
    f_equal.
    rewrite updJPSs_append.
    rewrite exprFreeVars_Var in H by assumption.
    rewrite delVarSetList_rev in H.
    clear -H.
    induction vs3 using rev_ind.
    + rewrite !updJPSs_nil.
      rewrite delVarSetList_nil in H.
      revert jps; induction vs2; intros.
       * rewrite updJPSs_nil.
         reflexivity.
       * rewrite updJPSs_cons.
         rewrite fold_is_true in H.
         rewrite disjointVarSet_mkVarSet_cons in H.
         destruct H.
         rewrite IHvs2 by assumption.
         apply elemVarSet_updJPS_l.
         rewrite <- elemVarSet_unitVarSet_is_eq. apply H.
    + rewrite delVarSetList_app, delVarSetList_cons, delVarSetList_nil in H.
      rewrite !updJPSs_append, !updJPSs_cons, !updJPSs_nil.
      apply elemVarSet_updJPS_cong. intros Hne.
      apply IHvs3.
      rewrite fold_is_true in *.
      rewrite disjointVarSet_mkVarSet in *.
      eapply Forall_impl; only 2: eapply H. intros v2 ?.
      cbv beta in H0.
      rewrite delVarSet_elemVarSet_false in H0; only 1: assumption.
      clear -Hne.
      apply elemVarSet_delVarSetList_false_l.
      rewrite elemVarSet_unitVarSet_is_eq. apply Hne.
  - reflexivity.
  - f_equal.
    apply H.
    eapply disjointVarSet_subVarSet_l; only 1: apply H1.
    apply subVarSet_delVarSetList_both.
    rewrite exprFreeVars_App.
    set_b_iff; fsetdec.
  - reflexivity.
  - destruct_match; only 1: reflexivity.
    destruct (isJoinId v) eqn:?; only 1: reflexivity.
    simpl.
    rewrite <- !updJPS_not_joinId by assumption.
    rewrite <- !updJPSs_singleton.
    rewrite <- !updJPSs_append.
    rewrite <- app_assoc.
    destruct_match.
    + apply H.
      eapply disjointVarSet_subVarSet_l; only 1: apply H0.
      rewrite rev_app_distr. simpl.
      rewrite delVarSetList_cons.
      apply subVarSet_delVarSetList_both. 
      (* Why does this even work? And how can we rewrite under [delVarSetList]
         as well, so that we can skip the previous command?
       *)
      rewrite exprFreeVars_Lam.
      set_b_iff; fsetdec.
    + apply H.
      eapply disjointVarSet_subVarSet_l; only 1: apply H0.
      rewrite rev_app_distr. simpl.
      rewrite delVarSetList_cons.
      apply subVarSet_delVarSetList_both.
      rewrite exprFreeVars_Lam.
      set_b_iff; fsetdec.
  - destruct binds as [v rhs | pairs].
    + f_equal.
      ** unfold isJoinPointsValidPair_aux.
         destruct_match; only 2: reflexivity.
         destruct_match.
         -- apply H.
            eapply disjointVarSet_subVarSet_l; only 1: apply H1.
            apply subVarSet_delVarSetList_both.
            rewrite exprFreeVars_Let_NonRec.
            set_b_iff; fsetdec.
         -- apply H.
            eapply disjointVarSet_subVarSet_l; only 1: apply H1.
            apply subVarSet_delVarSetList_both.
            rewrite exprFreeVars_Let_NonRec.
            set_b_iff; fsetdec.
      ** rewrite <- !updJPSs_singleton.
         rewrite <- !updJPSs_append.
         rewrite <- app_assoc.
         apply H0.
         eapply disjointVarSet_subVarSet_l; only 1: apply H1.
         rewrite rev_app_distr; simpl.
         rewrite delVarSetList_cons.
         apply subVarSet_delVarSetList_both.
         rewrite exprFreeVars_Let_NonRec.
         set_b_iff; fsetdec.
    + simpl.
      rewrite <- !updJPSs_append.
      rewrite <- app_assoc.
      f_equal. f_equal.
      ** apply forallb_conq.
         rewrite Forall_forall.
         intros [v rhs] HIn.
         specialize (H _ _ HIn).
         unfold isJoinPointsValidPair_aux.
         destruct_match; only 2: reflexivity.
         destruct_match.
         -- apply H.
            eapply disjointVarSet_subVarSet_l; only 1: apply H1.
            rewrite rev_app_distr; simpl.
            rewrite delVarSetList_app.
            apply subVarSet_delVarSetList_both.
            rewrite exprFreeVars_Let_Rec.
            pose proof (subVarSet_exprFreeVars_exprsFreeVars _ _ _ HIn).
            rewrite delVarSetList_rev.
            apply subVarSet_delVarSetList_both.
            set_b_iff; fsetdec.
         -- apply H.
            eapply disjointVarSet_subVarSet_l; only 1: apply H1.
            rewrite rev_app_distr; simpl.
            rewrite delVarSetList_app.
            apply subVarSet_delVarSetList_both.
            rewrite exprFreeVars_Let_Rec.
            rewrite delVarSetList_rev.
            pose proof (subVarSet_exprFreeVars_exprsFreeVars _ _ _ HIn).
            apply subVarSet_delVarSetList_both.
            set_b_iff; fsetdec.
      ** apply H0.
         eapply disjointVarSet_subVarSet_l; only 1: apply H1.
         rewrite rev_app_distr; simpl.
         rewrite delVarSetList_app.
         apply subVarSet_delVarSetList_both.
         rewrite exprFreeVars_Let_Rec.
         rewrite delVarSetList_rev.
         apply subVarSet_delVarSetList_both.
         set_b_iff; fsetdec.
  - destruct (isJoinId bndr) eqn:?; only 1: reflexivity; simpl.
    f_equal.
    apply forallb_conq.
    rewrite Forall_forall.
    intros [[dc pats] rhs] HIn.
    destruct (forallb (fun v : Var => negb (isJoinId v)) pats) eqn:?; only 2: reflexivity; simpl.
    rewrite <- !updJPSs_not_joinId by assumption.
    rewrite <- !updJPS_not_joinId by assumption.
    rewrite <- !updJPSs_cons.
    rewrite <- !updJPSs_append.
    rewrite <- app_assoc.
    specialize (H0 _ _ _ HIn).
    apply H0.
    eapply disjointVarSet_subVarSet_l; only 1: apply H1.
    rewrite rev_app_distr; simpl.
    rewrite !delVarSetList_app, delVarSetList_cons, delVarSetList_nil.
    apply subVarSet_delVarSetList_both.
    rewrite exprFreeVars_Case.
    rewrite fold_is_true in *.
    match goal with HIn : List.In _ ?xs |- context [mapUnionVarSet ?f ?xs] =>
      let H := fresh in
      epose proof (mapUnionVarSet_In_subVarSet f HIn) as H ; simpl in H end.
    rewrite delVarSetList_rev, <- delVarSetList_single, <- delVarSetList_app.
    set_b_iff; fsetdec.
  - apply H. 
    eapply disjointVarSet_subVarSet_l; only 1: apply H0.
    apply subVarSet_delVarSetList_both.
    rewrite exprFreeVars_Cast.
    set_b_iff; fsetdec.
(*  - apply H. 
    eapply disjointVarSet_subVarSet_l; only 1: apply H0.
    apply subVarSet_delVarSetList_both.
    rewrite exprFreeVars_Tick.
    set_b_iff; fsetdec. *)
  - reflexivity.
  - reflexivity. 
Qed.

Lemma isJoinPointsValid_fresh_updJPSs:
  forall (vs2 vs3 : list Var) n (e : CoreExpr) (jps : VarSet),
  disjointVarSet (delVarSetList (exprFreeVars e) vs3) (mkVarSet vs2) = true ->
  isJoinPointsValid e n (updJPSs jps (vs2 ++ vs3)) =
  isJoinPointsValid e n (updJPSs jps vs3).
Proof.
  intros.
  apply isJoinPointsValid_fresh_updJPSs_aux; assumption.
Qed.


Lemma isJoinPointsValid_fresh_between:
  forall (vs1 vs2 vs3 : list Var) (e : CoreExpr) (jps : VarSet),
  disjointVarSet (delVarSetList (exprFreeVars e) vs3) (mkVarSet vs2) = true ->
  isJoinPointsValid e 0 (updJPSs jps ((vs1 ++ vs2) ++ vs3)) =
  isJoinPointsValid e 0 (updJPSs jps (vs1 ++ vs3)).
Proof.
  intros.
  rewrite <- app_assoc.
  rewrite !updJPSs_append with (vs1 := vs1).
  apply isJoinPointsValid_fresh_updJPSs.
  assumption.
Qed.

(** ** Lemmas about [StrongSubset] *)

Lemma StrongSubset_updJPS:
  forall (v : Var) (vs1 vs2 : VarSet),
  StrongSubset vs1 vs2 ->
  StrongSubset (updJPS vs1 v) (updJPS vs2 v).
Proof.
  intros.
  unfold updJPS.
  destruct_match.
  * apply StrongSubset_extend.
    assumption.
  * apply StrongSubset_delVarSet.
    assumption.
Qed.


Lemma StrongSubset_updJPSs:
  forall (vs3 : list Var) (vs1 vs2 : VarSet),
  StrongSubset vs1 vs2 ->
  StrongSubset (updJPSs vs1 vs3) (updJPSs vs2 vs3).
Proof.
  induction vs3; intros.
  * assumption.
  * simpl.
    apply IHvs3.
    apply StrongSubset_updJPS.
    assumption.
Qed.

Lemma StrongSubset_updJPS_fresh :
  forall vs v,
  elemVarSet v vs = false ->
  StrongSubset vs (updJPS vs v).
Proof.
  intros.
  unfold updJPS. destruct_match.
  * apply StrongSubset_extend_fresh.
    apply lookupVarSet_None_elemVarSet.
    assumption.
  * apply StrongSubset_delete_fresh.
    apply lookupVarSet_None_elemVarSet.
    assumption.
Qed.

Lemma lookupVarSet_updJPS_neq:
  forall (v1 v2 : Var) (vs : VarSet),
  v1 GHC.Base.== v2 = false ->
  lookupVarSet (updJPS vs v1) v2 = lookupVarSet vs v2.
Proof.
  intros.
  unfold updJPS.
  destruct_match.
  * apply lookupVarSet_extendVarSet_neq.
    rewrite H. congruence.
  * apply lookupVarSet_delVarSet_neq.
    rewrite H. congruence.
Qed.

Lemma StrongSubset_updJPSs_fresh :
  forall vs vs2,
  disjointVarSet vs (mkVarSet vs2) = true ->
  StrongSubset vs (updJPSs vs vs2).
Proof.
  intros.
  (* A naive induction using [StrongSubset_updJPS_fresh] does not go through
     because we do not know that the [vs2] are disjoint.
  *)
  intro v.
  destruct_match; only 2: apply I.
  assert (lookupVarSet (updJPSs vs vs2) v = Some v0).
  { induction vs2 using rev_ind; intros.
    * apply Heq.
    * rewrite fold_is_true in *.
      rewrite disjointVarSet_mkVarSet_append, disjointVarSet_mkVarSet_cons in H.
      destruct H. destruct H0.
      rewrite updJPSs_append, updJPSs_cons, updJPSs_nil.
      assert (x GHC.Base.== v = false).
      { rewrite <- lookupVarSet_None_elemVarSet in H0.
        apply not_true_is_false. intro.
        erewrite lookupVarSet_eq  in H0 by eassumption.
        congruence.
      }
      rewrite lookupVarSet_updJPS_neq by assumption.
      apply IHvs2.
      assumption.
  }
  rewrite H0. apply almostEqual_refl.
Qed.


(** ** Lemmas about [Respects_StrongSubset] *)

Lemma Respects_StrongSubset_updJPS:
  forall v P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (updJPS vs v)).
Proof.
  intros.
  unfold updJPS.
  destruct_match; [apply Respects_StrongSubset_extendVarSet | apply Respects_StrongSubset_delVarSet ]; assumption.
Qed.

Lemma Respects_StrongSubset_updJPSs:
  forall vs2 P,
  Respects_StrongSubset (fun vs : VarSet => P vs) ->
  Respects_StrongSubset (fun vs : VarSet => P (updJPSs vs vs2)).
Proof.
  intros.
  induction vs2.
  * apply H.
  * simpl.
    apply Respects_StrongSubset_updJPS with (P := fun vs => P (updJPSs vs vs2)).
    apply IHvs2.
Qed.

Lemma Respects_StrongSubset_isJoinPointsValid_aux:
  forall e,
  (forall n,
  Respects_StrongSubset (fun jps => isJoinPointsValid e n jps = true)
  )
  /\
  (forall v,
  Respects_StrongSubset (fun jps => isJoinRHS_aux v e jps = true)).
Proof.
  intros.
  apply (core_induct e); intros;
    (split; intro; simpl; [| try solve[ destruct_match; apply Respects_StrongSubset_const]]).
  * destruct_match; only 2: apply Respects_StrongSubset_const.
    apply Respects_StrongSubset_andb; only 1: apply Respects_StrongSubset_const.
    apply Respects_StrongSubset_elemVarSet.
  * apply Respects_StrongSubset_const.
  * apply Respects_StrongSubset_andb; only 2: apply Respects_StrongSubset_const.
    apply H.
  * apply Respects_StrongSubset_const.
  * destruct_match; try apply Respects_StrongSubset_const.
    apply Respects_StrongSubset_andb; try apply Respects_StrongSubset_const.
    destruct_match.
    - apply Respects_StrongSubset_delVarSet with (P := fun jps => isJoinPointsValid e0 0 jps = true).
      apply H.
    - apply Respects_StrongSubset_delVarSet with (P := fun jps => isJoinRHS_aux (v0 - 1) e0 jps = true).
      apply H.
  * destruct binds as [v rhs | pairs].
    - apply Respects_StrongSubset_andb.
      + unfold isJoinPointsValidPair_aux.
        destruct_match; only 2: apply Respects_StrongSubset_const.
        destruct_match; apply H.
      + apply Respects_StrongSubset_updJPS with (P := fun jps => isJoinPointsValid body 0 jps = true).
        apply H0.
    - repeat apply Respects_StrongSubset_andb; try apply Respects_StrongSubset_const.
      + apply Respects_StrongSubset_forallb.
        rewrite Forall_forall.
        intros [v rhs] HIn.
        specialize (H _ _ HIn).
        apply Respects_StrongSubset_updJPSs with
          (P := fun jps => isJoinPointsValidPair_aux isJoinPointsValid isJoinRHS_aux v rhs jps = true).
        unfold isJoinPointsValidPair_aux.
        destruct_match; only 2: apply Respects_StrongSubset_const.
        destruct_match; apply H.
      + apply Respects_StrongSubset_updJPSs with
          (P := fun jps => isJoinPointsValid body 0 jps = true).
        apply H0.
   * repeat apply Respects_StrongSubset_andb; try apply Respects_StrongSubset_const.
     apply Respects_StrongSubset_forallb.
     rewrite Forall_forall.
     intros [[dc pats] rhs] HIn.
     specialize (H0 _ _ _ HIn).
     repeat apply Respects_StrongSubset_andb; try apply Respects_StrongSubset_const.
     apply Respects_StrongSubset_delVarSet with
          (P := fun jps => isJoinPointsValid rhs 0 (delVarSetList jps pats) = true).
     apply Respects_StrongSubset_delVarSetList with
          (P := fun jps => isJoinPointsValid rhs 0 jps = true).
     apply H0.
   * apply H.
(*   * apply H. *)
   * apply Respects_StrongSubset_const.
   * apply Respects_StrongSubset_const. 
Qed.

Instance Respects_StrongSubset_isJoinPointsValid e n :
  Respects_StrongSubset (fun jps => isJoinPointsValid e n jps = true).
Proof. apply Respects_StrongSubset_isJoinPointsValid_aux. Qed.

Instance Respects_StrongSubset_isValidJoinPointsPair x e :
  Respects_StrongSubset (fun jps => isValidJoinPointsPair x e jps = true).
Proof.
  unfold isValidJoinPointsPair.
  destruct_match; try apply Respects_StrongSubset_const.
  unfold isJoinRHS.
  destruct_match; try apply Respects_StrongSubset_const;
  apply Respects_StrongSubset_isJoinPointsValid_aux.
Qed.
