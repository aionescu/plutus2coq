(** * General tactics *)

(** These tactics are general proof management tactics, and not specific to any particular theory.
*)

Ltac expand_pairs :=
  match goal with
    |- context[let (_,_) := ?e in _] =>
    rewrite (surjective_pairing e)
  end.

Ltac destruct_match :=
  match goal with
  | [ H :context[match ?a with _ => _ end] |- _] =>
    let Heq := fresh "Heq" in
    destruct a eqn:Heq
  | [ |- context[match ?a with _ => _ end]] =>
    let Heq := fresh "Heq" in
    destruct a eqn:Heq
  end.


(* Pose the proof [prf], unless it already exists. *)
Ltac pose_new prf :=
  let prop := type of prf in
  match goal with 
    | [ H : prop |- _] => fail 1
    | _ => pose proof prf
  end.

(* Pose the [prop], using [prf], unless it already exists. *)
Ltac assert_new prop prf :=
  match goal with 
    | [ H : prop |- _] => fail 1
    | _ => assert prop by prf
  end.


(* A backtracking variant of [eassumption] *)

(** Source: http://stackissue.com/coq/coq/backtracking-eassumption-287.html *)

Ltac beassumption := multimatch goal with H :_ |- _ => exact H end.

