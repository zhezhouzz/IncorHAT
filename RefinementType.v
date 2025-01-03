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

Inductive ou := Over | Under.

(** Refinement types (t in Fig. 4) *)
Inductive rty : Type :=
| rtyBase (ou: ou) (b: base_ty) (ϕ: qualifier)
| rtyTd (ρ: rty) (td: transducer)
| rtyArr (ρ: rty) (τ: rty).

Fixpoint pure_rty (τ: rty) :=
  match τ with
  | rtyBase _ _ _ => True
  | rtyTd _ _ => False
  | rtyArr ρ1 ρ2 => pure_rty ρ1 /\ pure_rty ρ2
  end.

Fixpoint fine_rty (τ: rty) :=
  match τ with
  | rtyBase _ _ _ => True
  | rtyTd ρ _ => pure_rty ρ
  | rtyArr ρ τ => pure_rty ρ /\ fine_rty τ
  end.

Global Hint Constructors rty: core.

Notation "'{:' b '|' ϕ '}'" := (rtyBase Over b ϕ) (at level 5, format "{: b | ϕ }", b constr, ϕ constr).
Notation "'[:' b '|' ϕ ']'" := (rtyBase Under b ϕ) (at level 5, format "[: b | ϕ ]", b constr, ϕ constr).
Notation "ρ '!<[' a ']>'" := (rtyTd ρ a) (at level 5, format "ρ !<[ a ]>", ρ constr, a constr).
Notation "ρ '⇨' τ " :=
  (rtyArr ρ τ) (at level 80, format "ρ ⇨ τ", right associativity, ρ constr, τ constr).

(** Type erasure (Fig. 5) *)

Fixpoint rty_erase ρ : ty :=
  match ρ with
  | rtyBase _ b ϕ => b
  | ρ ⇨ τ => (rty_erase ρ) ⤍ (rty_erase τ)
  | ρ !<[ _ ]> => rty_erase ρ
  end.

Notation " '⌊' ty '⌋' " := (rty_erase ty) (at level 5, format "⌊ ty ⌋", ty constr).

Definition ctx_erase (Γ: listctx rty) :=
  ⋃ ((List.map (fun e => {[e.1 := rty_erase e.2]}) Γ): list (amap ty)).

Notation " '⌊' Γ '⌋*' " := (ctx_erase Γ) (at level 5, format "⌊ Γ ⌋*", Γ constr).

(** * Naming related definitions *)

Fixpoint rty_fv ρ : aset :=
  match ρ with
  | rtyBase _ _ ϕ => qualifier_fv ϕ
  | ρ ⇨ τ => rty_fv ρ ∪ rty_fv τ
  | ρ !<[ a ]> => rty_fv ρ ∪ td_fv a
  end.

#[global]
  Instance rty_stale : @Stale aset rty := rty_fv.
Arguments rty_stale /.

Fixpoint rty_open (k: nat) (s: value) (ρ: rty) : rty :=
  match ρ with
  | rtyBase ou b ϕ => rtyBase ou b (qualifier_open (S k) s ϕ)
  | ρ !<[ a ]> => (rty_open k s ρ) !<[ td_open k s a ]>
  | ρ ⇨ τ => (rty_open k s ρ) ⇨ (rty_open (S k) s τ)
  end.

Notation "'{' k '~r>' s '}' e" := (rty_open k s e) (at level 20, k constr).
Notation "e '^r^' s" := (rty_open 0 s e) (at level 20).

Fixpoint rty_subst (k: atom) (s: value) (ρ: rty) : rty :=
  match ρ with
  | rtyBase ou b ϕ => rtyBase ou b (qualifier_subst k s ϕ)
  | ρ !<[ a ]> => (rty_subst k s ρ) !<[ td_subst k s a ]>
  | ρ ⇨ τ => (rty_subst k s ρ) ⇨ (rty_subst k s τ)
  end.

Notation "'{' x ':=' s '}r'" := (rty_subst x s) (at level 20, format "{ x := s }r", x constr).

(** Local closure *)

Inductive lc_rty : rty -> Prop :=
| lc_rtyBase: forall ou b ϕ, lc_phi1 ϕ -> fine_rty (rtyBase ou b ϕ) -> lc_rty (rtyBase ou b ϕ)
| lc_rtyTd: forall ρ td, lc_rty ρ -> lc_td td -> fine_rty (rtyTd ρ td) -> lc_rty (rtyTd ρ td)
| lc_rtyArr: forall ρ τ (L : aset),
    lc_rty ρ ->
    (forall x : atom, x ∉ L -> lc_rty (τ ^r^ x)) ->
    fine_rty (ρ ⇨ τ) ->
    lc_rty (ρ ⇨ τ).

Lemma lc_rty_fine: forall τ, lc_rty τ -> fine_rty τ.
Proof.
  induction 1; eauto.
Qed.

(** Closed under free variable set *)

Inductive closed_rty (d : aset) (ρ: rty): Prop :=
| closed_rty_: lc_rty ρ -> rty_fv ρ ⊆ d -> closed_rty d ρ.

(** Well-formedness of type context. All terms and types are alpha-converted to
  have unique names. *)
Inductive ok_ctx: listctx rty -> Prop :=
| ok_ctx_nil: ok_ctx []
| ok_ctx_cons: forall (Γ: listctx rty)(x: atom) (ρ: rty),
    ok_ctx Γ ->
    closed_rty (ctxdom Γ) ρ ->
    x ∉ ctxdom Γ ->
    ok_ctx (Γ ++ [(x, ρ)]).

Lemma ok_ctx_ok: forall Γ, ok_ctx Γ -> ok Γ.
Proof.
  induction 1; eauto.
Qed.

(** Shorthands *)
Definition mk_eq_constant c := {: ty_of_const c | b0:c= c }.
Definition mk_bot ty := {: ty | mk_q_under_bot }.
Definition mk_top ty := {: ty | mk_q_under_top }.
Definition mk_eq_var ty (x: atom) := {: ty | b0:x= x }.
