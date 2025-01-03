From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import Qualifier.
From CT Require Import ListCtx.
From CT Require Import Transducer.
From CT Require Import RefinementType.

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
Import RefinementType.

(** * Naming properties of refinement type syntax *)

(** * erase *)

Lemma rty_erase_open_eq τ : forall k s,
  rty_erase τ = rty_erase ({k ~r> s} τ).
Proof.
  induction τ; intros; simpl; eauto; f_equal; eauto.
Qed.

Lemma ctx_erase_lookup Γ x ρ :
  ctxfind Γ x = Some ρ ->
  ⌊Γ⌋* !! x = Some ⌊ρ⌋.
Proof.
  induction Γ; simpl; intros; try easy.
  destruct a. case_decide. simplify_eq.
  cbn. simplify_map_eq. reflexivity.
  simp_hyps.
  cbn. rewrite insert_empty. rewrite <- insert_union_singleton_l.
  simplify_map_eq. reflexivity.
Qed.

Lemma ctx_erase_app Γ Γ':
  ⌊Γ ++ Γ'⌋* = ⌊Γ⌋* ∪ ⌊Γ'⌋*.
Proof.
  induction Γ; simpl.
  - cbn. by rewrite map_empty_union.
  - destruct a. unfold ctx_erase in *. cbn. rewrite IHΓ.
    by rewrite map_union_assoc.
Qed.

Lemma ctx_erase_dom Γ :
  dom ⌊Γ⌋* ≡ ctxdom Γ.
Proof.
  induction Γ; simpl.
  - cbn. apply dom_empty.
  - destruct a. cbn in *.
    rewrite insert_empty.
    setoid_rewrite dom_union.
    rewrite dom_singleton.
    f_equiv. eauto.
Qed.

Lemma ctx_erase_app_r Γ x ρ :
  x # Γ ->
  ⌊Γ ++ [(x, ρ)]⌋* = <[x:=⌊ρ⌋]> ⌊Γ⌋*.
Proof.
  intros H.
  rewrite ctx_erase_app.
  cbn. rewrite map_union_empty. rewrite insert_empty.
  rewrite <- insert_union_singleton_r. auto.
  simpl in H. rewrite <- ctx_erase_dom in H.
  by apply not_elem_of_dom.
Qed.

(** * commute *)

Lemma subst_commute_am : forall x u_x y u_y a,
    x <> y -> x ∉ fv_value u_y -> y ∉ fv_value u_x ->
    {x := u_x }a ({y := u_y }a a) = {y := u_y }a ({x := u_x }a a).
Proof.
  intros.
  induction a; simpl; eauto; f_equal; eauto using subst_commute_qualifier.
Qed.

Lemma subst_commute_rty : forall x u_x y u_y ρ,
    x <> y -> x ∉ fv_value u_y -> y ∉ fv_value u_x ->
    {x := u_x }p ({y := u_y }p ρ) = {y := u_y }p ({x := u_x }p ρ)
with subst_commute_rty : forall x u_x y u_y τ,
    x <> y -> x ∉ fv_value u_y -> y ∉ fv_value u_x ->
    {x := u_x }h ({y := u_y }h τ) = {y := u_y }h ({x := u_x }h τ).
Proof.
  destruct ρ; simpl; intros; f_equal;
    eauto using subst_commute_qualifier, subst_commute_am.
  destruct τ; simpl; intros; f_equal;
    eauto using subst_commute_qualifier, subst_commute_am.
Qed.

Lemma subst_fresh_am: forall (a: am) (x:atom) (u: value),
    x # a -> {x := u}a a = a.
Proof.
  intros. induction a; simpl in *; eauto; repeat f_equal;
    eauto using subst_fresh_qualifier;
    auto_apply; try my_set_solver.
Qed.

Lemma subst_fresh_rty: forall (ρ: rty) (x:atom) (u: value),
    x # ρ -> {x := u}p ρ = ρ
with subst_fresh_rty: forall (τ: rty) (x:atom) (u: value),
    x # τ -> {x := u}h τ = τ.
Proof.
  destruct ρ; simpl; intros; f_equal; eauto using subst_fresh_qualifier;
    auto_apply; my_set_solver.
  destruct τ; simpl; intros; f_equal;
    solve [ auto_apply; my_set_solver
          | apply subst_fresh_am; my_set_solver ].
Qed.

Lemma open_fv_am (a : am) (v : value) k :
  am_fv ({k ~a> v} a) ⊆ am_fv a ∪ fv_value v.
Proof.
  induction a; simpl; eauto using open_fv_qualifier;
    repeat my_set_solver.
Qed.

Lemma open_fv_am' (a : am) (v : value) k :
  am_fv a ⊆ am_fv ({k ~a> v} a).
Proof.
  induction a; simpl; eauto using open_fv_qualifier';
    my_set_solver.
Qed.

Lemma open_fv_rty (ρ : rty) (v : value) k :
  rty_fv ({k ~p> v} ρ) ⊆ rty_fv ρ ∪ fv_value v
with open_fv_rty (τ : rty) (v : value) k :
  rty_fv ({k ~r> v} τ) ⊆ rty_fv τ ∪ fv_value v.
Proof.
  all: revert k.
  destruct ρ; simpl; intros; eauto using open_fv_qualifier.
  etrans. apply union_mono; eauto. my_set_solver.
  destruct τ; simpl; intros.
  etrans. repeat apply union_mono; eauto using open_fv_am. my_set_solver.
  etrans. repeat apply union_mono; eauto. my_set_solver.
Qed.

Lemma open_fv_rty' (ρ : rty) (v : value) k :
  rty_fv ρ ⊆ rty_fv ({k ~p> v} ρ)
with open_fv_rty' (τ : rty) (v : value) k :
  rty_fv τ ⊆ rty_fv ({k ~r> v} τ).
Proof.
  all: revert k.
  destruct ρ; simpl; intros; eauto using open_fv_qualifier';
    repeat apply union_mono; eauto.
  destruct τ; simpl; intros;
    repeat apply union_mono; eauto using open_fv_am'.
Qed.

Lemma open_subst_same_am: forall x y (a : am) k,
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
Qed.

Lemma not_in_union_list {A C} `{SemiSet A C} (x : A) (ss : list C):
  x ∉ ⋃ ss ->
  forall s, In s ss -> x ∉ s.
Proof.
  induction ss; cbn; intros; eauto.
  qsimpl.
Qed.

Lemma open_subst_same_rty: forall x y (ρ : rty) k,
    x # ρ ->
    {x := y }p ({k ~p> x} ρ) = {k ~p> y} ρ
with open_subst_same_rty: forall x y (τ : rty) k,
    x # τ ->
    {x := y }h ({k ~r> x} τ) = {k ~r> y} τ.
Proof.
  destruct ρ; simpl; intros; f_equal; eauto using open_subst_same_qualifier;
    auto_apply; my_set_solver.
  destruct τ; simpl; intros; f_equal;
    solve [ auto_apply; my_set_solver
          | apply open_subst_same_am; my_set_solver ].
Qed.

Lemma subst_open_am: forall (a: am) (x:atom) (u: value) (w: value) (k: nat),
    lc w -> {x := w}a ({k ~a> u} a) = ({k ~a> {x := w}v u} ({x := w}a a)).
Proof.
  induction a; cbn; intros; eauto.
  f_equal. eauto using subst_open_qualifier.
  all:
  repeat
    match goal with
    | H : context [lc _ -> _] |- _ => rewrite H by my_set_solver; eauto
    end.
Qed.

Lemma subst_open_rty: forall (ρ: rty) (x:atom) (u: value) (w: value) (k: nat),
    lc w -> {x := w}p ({k ~p> u} ρ) = ({k ~p> {x := w}v u} ({x := w}p ρ))
with subst_open_rty: forall (τ: rty) (x:atom) (u: value) (w: value) (k: nat),
    lc w -> {x := w}h ({k ~r> u} τ) = ({k ~r> {x := w}v u} ({x := w}h τ)).
Proof.
  destruct ρ; simpl; intros; f_equal; eauto using subst_open_qualifier.
  destruct τ; simpl; intros; f_equal; eauto using subst_open_am.
Qed.

Lemma subst_open_rty_closed:
  ∀ (ρ : rty) (x : atom) (u w : value) (k : nat),
    closed_value u ->
    lc w → {x := w }p ({k ~p> u} ρ) = {k ~p> u} ({x := w }p ρ).
Proof.
  intros. rewrite subst_open_rty; auto.
  rewrite (subst_fresh_value); eauto. set_solver.
Qed.

Lemma subst_open_am_closed:
  ∀ (a : am) (x : atom) (u w : value) (k : nat),
    closed_value u ->
    lc w → {x := w }a ({k ~a> u} a) = {k ~a> u} ({x := w }a a).
Proof.
  intros. rewrite subst_open_am; auto.
  rewrite (subst_fresh_value); eauto. set_solver.
Qed.

Lemma subst_open_rty_closed:
  ∀ (τ : rty) (x : atom) (u w : value) (k : nat),
    closed_value u ->
    lc w → {x := w }h ({k ~r> u} τ) = {k ~r> u} ({x := w }h τ).
Proof.
  intros. rewrite subst_open_rty; auto.
  rewrite (subst_fresh_value); eauto. set_solver.
Qed.

Lemma subst_open_var_am: forall x y (u: value) (a: am) (k: nat),
    x <> y -> lc u -> {x := u}a ({k ~a> y} a) = ({k ~a> y} ({x := u}a a)).
Proof.
  intros.
  rewrite subst_open_am; auto. simpl. rewrite decide_False; auto.
Qed.

Lemma subst_open_var_rty: forall x y (u: value) (ρ: rty) (k: nat),
    x <> y -> lc u -> {x := u}p ({k ~p> y} ρ) = ({k ~p> y} ({x := u}p ρ)).
Proof.
  intros.
  rewrite subst_open_rty; auto. simpl. rewrite decide_False; auto.
Qed.

Lemma subst_open_var_rty: forall x y (u: value) (τ: rty) (k: nat),
    x <> y -> lc u -> {x := u}h ({k ~r> y} τ) = ({k ~r> y} ({x := u}h τ)).
Proof.
  intros.
  rewrite subst_open_rty; auto. simpl. rewrite decide_False; auto.
Qed.

Lemma subst_lc_am : forall x (u: value) (a: am),
    lc_am a -> lc u -> lc_am ({x := u}a a).
Proof.
  induction 1; intros Hu; eauto using lc_am.
  econstructor.
  auto_exists_L_intros.
  specialize_with x0.
  specialize_with y.
  rewrite <- !subst_open_var_qualifier by (eauto; my_set_solver).
  eauto using subst_lc_qualifier.
Qed.

Lemma subst_lc_rty : forall x (u: value) (ρ: rty),
    lc_rty ρ -> lc u -> lc_rty ({x := u}p ρ)
with subst_lc_rty : forall x (u: value) (τ: rty),
    lc_rty τ -> lc u -> lc_rty ({x := u}h τ).
Proof.
  all: destruct 1; intros; simpl; econstructor; eauto using subst_lc_am;
    instantiate_atom_listctx.
  - rewrite <- subst_open_var_qualifier by (eauto; my_set_solver);
      eauto using subst_lc_qualifier.
  - rewrite <- subst_open_var_rty by (eauto; my_set_solver); eauto.
  - rewrite <- subst_open_var_rty by (eauto; my_set_solver); eauto.
Qed.

Lemma fv_of_subst_am_closed:
  forall x (u : value) (a: am),
    closed_value u ->
    am_fv ({x := u }a a) = (am_fv a ∖ {[x]}).
Proof.
  induction a; simpl; eauto using fv_of_subst_qualifier_closed; my_set_solver.
Qed.

Lemma fv_of_subst_rty_closed:
  forall x (u : value) (ρ: rty),
    closed_value u ->
    rty_fv ({x := u }p ρ) = (rty_fv ρ ∖ {[x]})
with fv_of_subst_rty_closed:
  forall x (u : value) (τ: rty),
    closed_value u ->
    rty_fv ({x := u }h τ) = (rty_fv τ ∖ {[x]}).
Proof.
  destruct ρ; simpl; intros; eauto using fv_of_subst_qualifier_closed.
  rewrite !fv_of_subst_rty_closed, !fv_of_subst_rty_closed by eauto.
  my_set_solver.
  destruct τ; simpl; intros.
  rewrite !fv_of_subst_am_closed, !fv_of_subst_rty_closed by eauto.
  my_set_solver.
  rewrite !fv_of_subst_rty_closed by eauto.
  my_set_solver.
Qed.

Lemma open_not_in_eq_am (x : atom) (a : am) k :
  x # {k ~a> x} a ->
  forall e, a = {k ~a> e} a.
Proof.
  induction a; simpl; intros; eauto.
  f_equal. eapply open_not_in_eq_qualifier. my_set_solver.
  all: f_equal; auto_apply; my_set_solver.
Qed.

Lemma open_not_in_eq_rty (x : atom) (ρ : rty) k :
  x # {k ~p> x} ρ ->
  forall e, ρ = {k ~p> e} ρ
with open_not_in_eq_rty (x : atom) (τ : rty) k :
  x # {k ~r> x} τ ->
  forall e, τ = {k ~r> e} τ.
Proof.
  all: revert k; specialize (open_not_in_eq_rty x); specialize (open_not_in_eq_rty x).
  destruct ρ; simpl; intros; f_equal; eauto using open_not_in_eq_qualifier;
    auto_apply; my_set_solver.
  destruct τ; simpl; intros; f_equal;
    solve [ auto_apply; my_set_solver
          | apply (open_not_in_eq_am x); my_set_solver ].
Qed.

Lemma subst_intro_rty: forall (ρ: rty) (x:atom) (w: value) (k: nat),
    x # ρ ->
    lc w -> {x := w}p ({k ~p> x} ρ) = ({k ~p> w} ρ).
Proof.
  intros.
  specialize (subst_open_rty ρ x x w k) as J.
  simpl in J. rewrite decide_True in J; auto.
  rewrite J; auto. rewrite subst_fresh_rty; auto.
Qed.

Lemma lc_subst_am:
  forall x (u: value) (a: am), lc_am ({x := u}a a) -> lc u -> lc_am a.
Proof.
  intros.
  remember (({x:=u}a) a).
  generalize dependent a.
  induction H; intros;
      match goal with
      | H : _ = {_:=_}a ?a |- _ => destruct a; simpl in *; simplify_eq
      end; eauto using lc_am.
  econstructor.
  auto_exists_L_intros. specialize_with x0. specialize_with y.
  rewrite <- !subst_open_var_qualifier in H by (eauto; my_set_solver).
  eauto using lc_subst_qualifier.
Qed.

Lemma lc_subst_rty: forall x (u: value) (ρ: rty), lc_rty ({x := u}p ρ) -> lc u -> lc_rty ρ
with lc_subst_rty: forall x (u: value) (τ: rty), lc_rty ({x := u}h τ) -> lc u -> lc_rty τ.
Proof.
  intros.
  remember (({x:=u}p) ρ).
  generalize dependent ρ.
  destruct H; intros ρ' **; destruct ρ'; simpl in *; simplify_eq;
    econstructor; eauto;
    instantiate_atom_listctx.
  rewrite <- subst_open_var_qualifier in * by (eauto; my_set_solver);
    eauto using lc_subst_qualifier.
  rewrite <- subst_open_var_rty in * by (eauto; my_set_solver); eauto.
  rewrite <- subst_open_var_rty in * by (eauto; my_set_solver); eauto.

  intros.
  remember (({x:=u}h) τ).
  generalize dependent τ.
  destruct H; intros τ' **; destruct τ'; simpl in *; simplify_eq;
    econstructor; eauto using lc_subst_am.
Qed.

Lemma open_am_idemp: forall u (v: value) (a: am) (k: nat),
    lc v ->
    {k ~a> u} ({k ~a> v} a) = ({k ~a> v} a).
Proof.
  induction a; intros; simpl; f_equal; eauto using open_qualifier_idemp.
Qed.

Lemma open_rty_idemp: forall u (v: value) (ρ: rty) (k: nat),
    lc v ->
    {k ~p> u} ({k ~p> v} ρ) = {k ~p> v} ρ
with open_rty_idemp: forall u (v: value)  (τ: rty) (k: nat),
    lc v ->
    {k ~r> u} ({k ~r> v} τ) = {k ~r> v} τ.
Proof.
  destruct ρ; intros; simpl; f_equal; eauto using open_qualifier_idemp.
  destruct τ; intros; simpl; f_equal; eauto using open_am_idemp.
Qed.

Lemma closed_rty_subseteq_proper s1 s2 ρ :
  closed_rty s1 ρ ->
  s1 ⊆ s2 ->
  closed_rty s2 ρ.
Proof.
  intros. sinvert H. split. eauto.
  my_set_solver.
Qed.

Lemma closed_rty_hoare_congr d ρ a b :
  closed_rty d ρ ->
  closed_am d a ->
  closed_am d b ->
  closed_rty d (<[ a ] ρ [ b ]>).
Proof.
  inversion 1. inversion 1. inversion 1.
  econstructor.
  econstructor; eauto.
  simpl. my_set_solver.
Qed.
