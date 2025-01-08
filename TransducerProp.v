From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import Qualifier.
From CT Require Import ListCtx.
From CT Require Import Transducer.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import OperationalSemantics.
Import BasicTyping.
Import Qualifier.
Import ListCtx.
Import List.
Import Transducer.

(** * Naming properties of refinement type syntax *)

(** * subst *)

Lemma subst_commute_td : forall x u_x y u_y a,
    x <> y -> x ∉ fv_value u_y -> y ∉ fv_value u_x ->
    {x := u_x }a ({y := u_y }a a) = {y := u_y }a ({x := u_x }a a).
Proof.
  pose subst_commute_value.
  pose subst_commute_qualifier.
  intros.
  induction a; simpl; eauto; f_equal; eauto.
Qed.

Lemma subst_fresh_td: forall (a: transducer) (x:atom) (u: value),
    x # a -> {x := u}a a = a.
Proof.
  pose subst_fresh_qualifier.
  pose subst_fresh_value.
  intros.
  induction a; simpl in *; eauto; repeat f_equal;
  try (auto_apply; my_set_solver).
Qed.

Lemma open_fv_td (a : transducer) (v : value): forall k,
  td_fv ({k ~a> v} a) ⊆ td_fv a ∪ fv_value v.
Proof.
  pose open_fv_qualifier.
  pose open_fv_value.
  induction a; simpl; intros; eauto; my_set_solver.
Qed.

Lemma open_fv_td' (a : transducer) (v : value): forall k,
  td_fv a ⊆ td_fv ({k ~a> v} a).
Proof.
  pose open_fv_qualifier'.
  induction a; intros; simpl; eauto.
Admitted.

Lemma open_subst_same_td: forall x y (a : transducer) k,
    x # a ->
    {x := y }a ({k ~a> x} a) = {k ~a> y} a.
Proof.
  induction a; cbn; intros; eauto.
  f_equal. eauto using open_subst_same_qualifier.
  all:
  repeat
    match goal with
    | H : forall k, _ # _ -> _ =_ |- _ => rewrite H by my_set_solver; eauto
    end.
Admitted.

Lemma subst_open_td: forall (a: transducer) (x:atom) (u: value) (w: value) (k: nat),
    lc w -> {x := w}a ({k ~a> u} a) = ({k ~a> {x := w}v u} ({x := w}a a)).
Proof.
  induction a; cbn; intros; eauto.
  f_equal. eauto using subst_open_qualifier.
  all:
  repeat
    match goal with
    | H : context [lc _ -> _] |- _ => rewrite H by my_set_solver; eauto
    end.
Admitted.

Lemma subst_open_td_closed:
  ∀ (a : transducer) (x : atom) (u w : value) (k : nat),
    closed_value u ->
    lc w → {x := w }a ({k ~a> u} a) = {k ~a> u} ({x := w }a a).
Proof.
  intros. rewrite subst_open_td; auto.
  rewrite (subst_fresh_value); eauto. set_solver.
Qed.


Lemma subst_open_var_td: forall x y (u: value) (a: transducer) (k: nat),
    x <> y -> lc u -> {x := u}a ({k ~a> y} a) = ({k ~a> y} ({x := u}a a)).
Proof.
  intros.
  rewrite subst_open_td; auto. simpl. rewrite decide_False; auto.
Qed.


Lemma subst_lc_td : forall x (u: value) (a: transducer),
    lc_td a -> lc u -> lc_td ({x := u}a a).
Proof.
  pose subst_lc_phi1.
  pose subst_lc_phi2.
  pose subst_lc_value.
  induction 1; intros Hu; eauto using lc_td.
  - simpl. auto_exists_L. intros y Hy. specialize_with y.
    rewrite subst_open_var_td in *; eauto. set_solver.
Qed.

Lemma fv_of_subst_td_closed:
  forall x (u : value) (a: transducer),
    closed_value u ->
    td_fv ({x := u }a a) = (td_fv a ∖ {[x]}).
Proof.
  induction a; simpl; eauto using fv_of_subst_qualifier_closed.
Admitted.

Lemma open_not_in_eq_td (x : atom) (a : transducer) k :
  x # {k ~a> x} a ->
  forall e, a = {k ~a> e} a.
Proof.
  induction a; simpl; intros; eauto.
  f_equal. eapply open_not_in_eq_qualifier. my_set_solver.
  (* all: f_equal; auto_apply; my_set_solver. *)
Admitted.

Lemma lc_subst_td:
  forall x (u: value) (a: transducer), lc_td ({x := u}a a) -> lc u -> lc_td a.
Proof.
  intros.
  remember (({x:=u}a) a).
  generalize dependent a.
  induction H; intros;
      match goal with
      | H : _ = {_:=_}a ?a |- _ => destruct a; simpl in *; simplify_eq
      end; eauto using lc_td.
  econstructor.
  (* auto_exists_L_intros. specialize_with x0. specialize_with y. *)
  (* rewrite <- !subst_open_var_qualifier in H by (eauto; my_set_solver). *)
  (* eauto using lc_subst_qualifier. *)
Admitted.

Lemma open_td_idemp: forall u (v: value) (a: transducer) (k: nat),
    lc v ->
    {k ~a> u} ({k ~a> v} a) = ({k ~a> v} a).
Proof.
  pose open_qualifier_idemp.
  pose open_value_idemp.
  induction a; intros; simpl; f_equal; eauto.
Qed.
