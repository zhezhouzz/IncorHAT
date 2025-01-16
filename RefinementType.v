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

(** Refinement types (t in Fig. 4) *)
Inductive rty : Type :=
| rtyOver (b: base_ty) (ϕ: qualifier)
| rtyUnder (b: base_ty) (ϕ: qualifier)
| rtyArr (ρ: rty) (τ: rty)
| rtyTd (ρ: rty) (τ: transducer).

Notation "'{:' b '|' ϕ '}'" := (rtyOver b ϕ) (at level 5, format "{: b | ϕ }", b constr, ϕ constr).
Notation "'[:' b '|' ϕ ']' " := (rtyUnder b ϕ) (at level 5, format "[: b | ϕ ]", b constr, ϕ constr).
Notation "ρ '⇨' τ" :=
  (rtyArr ρ τ) (at level 80, format "ρ ⇨ τ", right associativity, ρ constr, τ constr).
Notation "ρ '!<[' a ']>'" :=
  (rtyTd ρ a) (at level 80, format "ρ !<[ a ]>", right associativity, ρ constr, a constr).

(** Over-Base type and function type is *pure*, which means it can be paramater of a function type; also can be introduced into type context *)
Definition pure_rty (τ: rty) :=
  match τ with
  | {: _ | _ } | _ ⇨ _  => True
  | [: _ | _ ] | _ !<[ _ ]> => False
  end.

(** Under-Base type and function type is td-able, which means it can be refined with a transducer. *)
Definition tdable_rty (τ: rty) :=
  match τ with
  | [: _ | _ ] | _ ⇨ _  => True
  | {: _ | _ } | _ !<[ _ ]> => False
  end.

Definition is_tm_rty (τ: rty) :=
  match τ with
  | [: _ | _] | _ !<[ _ ]> | _ ⇨ _ => True
  | {: _ | _ } => False
  end.

(** Fine-defined Refinement type:
    - { b | ϕ }
    - (τ1 ⇨ τ2) where τ1 and τ2 is fine-defined, τ1 is pure
    - [ b | ϕ ] ! T
    - (τ1 ⇨ τ2) ! T where τ1 and τ2 is fine-defined, τ1 is pure
 *)
Fixpoint fine_rty (τ: rty) :=
  match τ with
  | rtyOver _ _ => True
  | rtyUnder _ _ => True
  | rtyArr ρ τ => pure_rty ρ /\ fine_rty ρ /\ fine_rty τ /\ is_tm_rty τ
  | rtyTd ρ _ => tdable_rty ρ /\ fine_rty ρ
  end.

Global Hint Constructors rty: core.

Definition flap_rty (τ: rty) :=
  match τ with
  | [: b | ϕ ] => {: b | ϕ }
  | {: b | ϕ } => [: b | ϕ ]
  | ρ ⇨ τ => ρ ⇨ τ
  | ρ !<[ a ]> => ρ !<[ a ]>
  end.

(** Type erasure (Fig. 5) *)

Fixpoint rty_erase ρ : ty :=
  match ρ with
  | {: b | ϕ } => b
  | [: b | ϕ ] => b
  | ρ ⇨ τ => (rty_erase ρ) ⤍ (rty_erase τ)
  | ρ !<[ _ ]> => (rty_erase ρ)
  end.

Notation " '⌊' ty '⌋' " := (rty_erase ty) (at level 5, format "⌊ ty ⌋", ty constr).

Definition ctx_erase (Γ: listctx rty) :=
  ⋃ ((List.map (fun e => {[e.1 := rty_erase e.2]}) Γ): list (amap ty)).

Notation " '⌊' Γ '⌋*' " := (ctx_erase Γ) (at level 5, format "⌊ Γ ⌋*", Γ constr).

(** * Naming related definitions *)

Fixpoint rty_fv ρ : aset :=
  match ρ with
  | {: _ | ϕ } => qualifier_fv ϕ
  | [: _ | ϕ ] => qualifier_fv ϕ
  | ρ ⇨ τ => rty_fv ρ ∪ rty_fv τ
  | ρ !<[ a ]> => rty_fv ρ ∪ td_fv a
  end.

#[global]
  Instance rty_stale : @Stale aset rty := rty_fv.
Arguments rty_stale /.

Fixpoint rty_open (k: nat) (s: value) (ρ: rty) : rty :=
  match ρ with
  | {: b | ϕ } => {: b | qualifier_open (S k) s ϕ }
  | [: b | ϕ ] => [: b | qualifier_open (S k) s ϕ ]
  | ρ ⇨ τ => (rty_open k s ρ) ⇨ (rty_open (S k) s τ)
  | ρ !<[ a ]> => (rty_open k s ρ) !<[ td_open (S k) s a ]>
  end.

Notation "'{' k '~r>' s '}' e" := (rty_open k s e) (at level 20, k constr).
Notation "e '^r^' s" := (rty_open 0 s e) (at level 20).

Fixpoint rty_subst (k: atom) (s: value) (ρ: rty) : rty :=
  match ρ with
  | {: b | ϕ} => {: b | qualifier_subst k s ϕ}
  | [: b | ϕ] => [: b | qualifier_subst k s ϕ]
  | ρ ⇨ τ => (rty_subst k s ρ) ⇨ (rty_subst k s τ)
  | ρ !<[ a ]> => (rty_subst k s ρ) !<[ td_subst k s a ]>
  end.

Notation "'{' x ':=' s '}r'" := (rty_subst x s) (at level 20, format "{ x := s }r", x constr).

(** Local closure *)
(** NOTE: To alaign with denotation, we assume the function type doesn't appear in transduce. *)
(** NOTE: all (L: aset) should be the first hypothesis. *)
Inductive lc_rty : rty -> Prop :=
| lc_rtyOver: forall b ϕ, lc_phi1 ϕ -> fine_rty {: b | ϕ} -> lc_rty {: b | ϕ}
| lc_rtyUnder: forall b ϕ, lc_phi1 ϕ -> fine_rty [: b | ϕ] -> lc_rty [: b | ϕ]
| lc_rtyArr: forall ρ τ (L : aset),
    (forall x : atom, x ∉ L -> lc_rty (τ ^r^ x)) ->
    fine_rty (ρ ⇨ τ) -> lc_rty ρ ->
    lc_rty (ρ ⇨ τ)
| lc_rtyTd: forall b ϕ a (L : aset),
    (forall x : atom, x ∉ L -> lc_td (a ^a^ x)) ->
    fine_rty ([:b | ϕ]!<[a]>) -> lc_rty [:b | ϕ] ->
    lc_rty ([:b | ϕ]!<[a]>)
| lc_rtyTdArr: forall ρ τ a,
    lc_td a ->
    fine_rty ((ρ ⇨ τ)!<[a]>) -> lc_rty (ρ ⇨ τ) ->
    lc_rty ((ρ ⇨ τ)!<[a]>).

Lemma lc_rty_fine: forall τ, lc_rty τ -> fine_rty τ.
Proof.
  induction 1; eauto.
Qed.

(** Closed under free variable set *)

Inductive closed_rty (d : aset) (ρ: rty): Prop :=
| closed_rty_: lc_rty ρ -> rty_fv ρ ⊆ d -> closed_rty d ρ.

Lemma closed_rty_fine: forall d τ, closed_rty d τ -> fine_rty τ.
Proof.
  pose lc_rty_fine.
  induction 1; eauto.
Qed.

(** Well-formedness of type context. All terms and types are alpha-converted to
  have unique names.
  all rty in ctx are pure.
 *)
Inductive ok_ctx: listctx rty -> Prop :=
| ok_ctx_nil: ok_ctx []
| ok_ctx_cons: forall (Γ: listctx rty)(x: atom) (ρ: rty),
    ok_ctx Γ ->
    pure_rty ρ ->
    closed_rty (ctxdom Γ) ρ ->
    x ∉ ctxdom Γ ->
    ok_ctx (Γ ++ [(x, ρ)]).

Lemma ok_ctx_ok: forall Γ, ok_ctx Γ -> ok Γ.
Proof.
  induction 1; eauto.
Qed.

Lemma is_tm_rty_open: forall τ k (v_x: value), is_tm_rty ({ k ~r> v_x} τ) <-> is_tm_rty τ.
Proof.
  split; induction τ; simpl; intros; inversion H; subst; eauto.
Qed.

Lemma is_tm_rty_subst: forall τ x (v_x: value), is_tm_rty ({ x := v_x}r τ) <-> is_tm_rty τ.
Proof.
  split; induction τ; simpl; intros; inversion H; subst; eauto.
Qed.

Lemma is_tm_rty_retrty: forall τ1 τ2 L, closed_rty L (τ1⇨τ2) -> is_tm_rty τ2.
Proof.
  intros. sinvert H. sinvert H0. sinvert H4. intuition.
Qed.

(** Shorthands, used in typing rules *)
Definition mk_eq_constant c := [: ty_of_const c | b0:c= c ].
Definition mk_bot ty := [: ty | mk_q_under_bot ].
Definition mk_top ty := [: ty | mk_q_under_top ].
Definition mk_eq_var ty (x: atom) := [: ty | b0:x= x ].

Lemma lc_rty_under_base_q: forall b ϕ, lc_rty ([:b|ϕ]) <-> lc_phi1 ϕ.
Proof.
  split; intros; sinvert H; eauto.
  econstructor; eauto. exists x. eauto. simpl; eauto.
Qed.

Lemma lc_rty_over_base_q: forall b ϕ, lc_rty ({:b|ϕ}) <-> lc_phi1 ϕ.
Proof.
  split; intros; sinvert H; eauto.
  econstructor; eauto. exists x. eauto. simpl; eauto.
Qed.

Lemma lc_rty_base_flip: forall b ϕ, lc_rty {:b|ϕ} <-> lc_rty [:b|ϕ].
Proof.
  split; intros; sinvert H; econstructor; eauto.
Qed.

Lemma closed_rty_base_flip: forall L b ϕ, closed_rty L {:b|ϕ} <-> closed_rty L [:b|ϕ].
Proof.
  split; intros; sinvert H; econstructor; eauto;
  rewrite lc_rty_base_flip in *; eauto.
Qed.

Lemma lc_rty_base_td: forall b ϕ A, lc_rty ([:b|ϕ]!<[A]>) <-> lc_rty [:b|ϕ] /\ body_td A.
Proof.
  split; intros; sinvert H.
  - split; eauto. exists L. eauto.
  - unfold body_td in H1. simp_hyps.
    auto_exists_L. simpl; eauto.
Qed.

Lemma lc_rty_arr_td: forall ρ τ A, lc_rty ((ρ ⇨ τ)!<[A]>) <-> lc_rty (ρ ⇨ τ) /\ lc_td A.
Proof.
  split; intros; sinvert H.
  - split; eauto.
  - econstructor; eauto. sinvert H0. simpl; eauto.
Qed.

Lemma closed_rty_base_td: forall L b ϕ A, closed_rty L ([:b|ϕ]!<[ A ]>) <-> closed_rty L [:b|ϕ] /\ body_td A /\ td_fv A ⊆ L.
Proof.
  split; intros; sinvert H.
  - intuition.
    + sinvert H0; eauto. econstructor; eauto. my_set_solver.
    + rewrite lc_rty_base_td in H0. intuition.
    + rewrite lc_rty_base_td in H0. my_set_solver.
  - sinvert H0. econstructor; eauto.
    + rewrite lc_rty_base_td. intuition.
    + my_set_solver.
Qed.

Lemma closed_rty_arr_td: forall L ρ τ A, closed_rty L ((ρ ⇨ τ)!<[ A ]>) <-> closed_rty L (ρ ⇨ τ) /\ closed_td L A.
Proof.
  split; intros; sinvert H.
  - sinvert H0; split; eauto.
    + econstructor; eauto. my_set_solver.
    + econstructor; eauto. my_set_solver.
  - sinvert H0. sinvert H1. econstructor; eauto.
    + rewrite lc_rty_arr_td. intuition.
    + my_set_solver.
Qed.
