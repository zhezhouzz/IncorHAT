From stdpp Require Import mapset.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import TransducerProp.
From CT Require Import RefinementTypeProp.
From CT Require Import DenotationProp.
From CT Require Import InstantiationProp.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import ListCtx.
Import Trace.
Import OperationalSemantics.
Import BasicTyping.
Import Qualifier.
Import Transducer.
Import RefinementType.
Import Denotation.
Import Instantiation.


(** This file formalizes the type system of λᴱ and the main metatheoretic
  results. *)

(** Well-formedness (Fig. 5) *)
(* Definition wf_td (Γ: listctx rty) (A: transducer): Prop := closed_td (ctxdom Γ) A. *)

(* Definition prefix_td (Γ: listctx rty) (A B: transducer) : Prop := *)
(*   forall Γv, ctxRst Γ Γv -> *)
(*         forall α, a⟦m{ Γv }a B⟧ α → *)
(*              a⟦m{ Γv }a A ;+ ∘*⟧ α. *)

(* Definition wf_rty (Γ: listctx rty) (τ: rty): Prop := closed_rty (ctxdom Γ) τ. *)
(* | WfOver: forall Γ b ϕ, *)
(*     closed_rty (ctxdom Γ) {: b | ϕ } -> wf_rty Γ {: b | ϕ } *)
(* | WfUnder: forall Γ b ϕ a, *)
(*     closed_rty (ctxdom Γ) [: b | ϕ ]!<[ a ]> -> *)
(*     wf_td *)
(*     wf_rty Γ [: b | ϕ ]!<[ a ]> *)
(* | WfArr: forall Γ ρ τ (L: aset), *)
(*     wf_rty Γ ρ -> *)
(*     (forall x, x ∉ L -> wf_rty (Γ ++ [(x, ρ)]) (τ ^h^ x)) -> *)
(*     wf_rty Γ (ρ ⇨ τ) *)
(* | WfGhost: forall Γ b ρ (L: aset), *)
(*     (forall x, x ∉ L -> wf_rty (Γ ++ [(x, mk_top b)]) (ρ ^p^ x)) -> *)
(*     wf_rty Γ (b ⇢ ρ) *)

(* with wf_rty: listctx rty -> rty -> Prop := *)
(* | WfHoare: forall Γ ρ A B, *)
(*     wf_rty Γ ρ -> *)
(*     wf_td Γ A -> *)
(*     wf_td Γ B -> *)
(*     prefix_td Γ A B -> *)
(*     wf_rty Γ (<[ A ] ρ [ B ]>) *)
(* | WfInter: forall Γ τ1 τ2, *)
(*     wf_rty Γ τ1 -> *)
(*     wf_rty Γ τ2 -> *)
(*     ⌊ τ1 ⌋ = ⌊ τ2 ⌋ -> *)
(*     wf_rty Γ (τ1 ⊓ τ2) *)
(* . *)

Notation " Γ '⊢WF' τ " := (closed_rty (ctxdom Γ) τ) (at level 20, τ constr, Γ constr).
Notation " Γ '⊢WFa' a " := (closed_td (ctxdom Γ) a) (at level 20, a constr, Γ constr).

Reserved Notation "Γ '⊢' e '⋮' τ"  (at level 20).

(** Semantic subtyping *)
(* Instead of the syntactic subtyping relation presented in the paper, we use
semantic subtyping in the mechanization. *)
Definition subtyping (Γ: listctx rty) (ρ1 ρ2: rty) : Prop :=
  (* Assume [ρ1] and [ρ2] are valid [rty]s. *)
  ⌊ ρ1 ⌋ = ⌊ ρ2 ⌋ /\
  forall Γv, ctxRst Γ Γv ->
        forall e, ⟦m{ Γv }r ρ1⟧ e → ⟦m{ Γv }r ρ2⟧ e.

Notation " Γ '⊢' τ1 '<⋮' τ2 " := (subtyping Γ τ1 τ2) (at level 20, τ1 constr, τ2 constr, Γ constr).

Definition join (Γ: listctx rty) (ρ1 ρ2 ρ3: rty) : Prop :=
  (* Assume [ρ1] and [ρ2] are valid [rty]s. *)
  ⌊ ρ1 ⌋ = ⌊ ρ2 ⌋ /\ ⌊ ρ1 ⌋ = ⌊ ρ3 ⌋ /\
    forall Γv, ctxRst Γ Γv ->
          forall e, ⟦m{ Γv }r ρ3⟧ e <-> ⟦m{ Γv }r ρ1⟧ e \/ ⟦m{ Γv }r ρ2⟧ e.

Notation " Γ '⊢' τ1 '<⋮' τ2 " := (subtyping Γ τ1 τ2) (at level 20, τ1 constr, τ2 constr, Γ constr).

Notation " Γ '⊢' τ1 '⋮join' τ2 '⋮=' τ3" := (join Γ τ1 τ2 τ3) (at level 20, τ1 constr, τ2 constr, τ3 constr, Γ constr).

(* The builtin typing relation (Δ) that our type system is parameterized over. *)
Parameter builtin_typing_relation : effop -> rty -> Prop.

Reserved Notation "Γ '⊢' op '⋮o' ρ"  (at level 20).
Reserved Notation "Γ '⊢' e '⋮t' τ" (at level 20).
Reserved Notation "Γ '⊢' e '⋮v' τ" (at level 20).

(** * Typing rules (Fig. 6) *)

Inductive effop_type_check : listctx rty -> effop -> rty -> Prop :=
| TEOp : forall Γ op ρ_op ρ,
    Γ ⊢WF ρ ->
    builtin_typing_relation op ρ_op ->
    (* [TSubEOp] is inlined here. Consecutive applications of subtyping is just
    one subtyping. *)
    Γ ⊢ ρ_op <⋮ ρ ->
    ⌊ ρ ⌋ = ty_of_op op ->
    Γ ⊢ op ⋮o ρ
where
"Γ '⊢' op '⋮o' ρ" := (effop_type_check Γ op ρ).

(** Typing rules for values and terms. Values always have refinement types, while
  terms always have Hoare automata types. *)
Inductive term_type_check : listctx rty -> tm -> rty -> Prop :=
| TLift: forall Γ v ρ,
    Γ ⊢WF (ρ !<[ tdId ]>) ->
    Γ ⊢ v ⋮v ρ ->
    Γ ⊢ v ⋮t (ρ !<[ tdId ]>)
| TSub: forall Γ e (τ1 τ2: rty),
    Γ ⊢WF τ2 ->
    Γ ⊢ e ⋮t τ1 ->
    Γ ⊢ τ1 <⋮ τ2 ->
    Γ ⊢ e ⋮t τ2
| TJoin: forall Γ e (τ1 τ2 τ3: rty),
    Γ ⊢WF τ3 ->
    Γ ⊢ e ⋮t τ1 ->
    Γ ⊢ e ⋮t τ2 ->
    Γ ⊢ τ1 ⋮join τ2 ⋮= τ3 ->
    Γ ⊢ e ⋮t τ3
| TLetEBase: forall Γ e1 e2 b1 ϕ1 A1 τ2 A2 (L: aset),
    (forall x, x ∉ L ->
          (Γ ++ [(x, {: b1 | ϕ1})]) ⊢ (e2 ^t^ x) ⋮t (τ2 !<[ A2 ]>)) ->
    Γ ⊢WF (τ2!<[ (tdEx b1 ϕ1 A1) ○ A2 ]>) ->
    Γ ⊢ e1 ⋮t ([: b1 | ϕ1]!<[ A1 ]>) ->
    Γ ⊢ (tlete e1 e2) ⋮t (τ2!<[ (tdEx b1 ϕ1 A1) ○ A2 ]>)
| TLetEArr: forall Γ e1 e2 ρ1 τ1 A1 τ2 A2 (L: aset),
    (forall x, x ∉ L ->
          (Γ ++ [(x, ρ1 ⇨ τ1)]) ⊢ (e2 ^t^ x) ⋮t (τ2 !<[ A2 ]>)) ->
    Γ ⊢WF (τ2!<[ A1 ○ A2 ]>) ->
    Γ ⊢ e1 ⋮t (ρ1 ⇨ τ1 !<[ A1 ]>) ->
    Γ ⊢ (tlete e1 e2) ⋮t (τ2!<[ A1 ○ A2 ]>)
| TAppBase: forall Γ (v1 v2: value) e ρ2 b1 ϕ1 A1 τ2 A2 (L: aset),
    (forall x, x ∉ L ->
          (Γ ++ [(x, {: b1 | ϕ1} ^r^ v2)]) ⊢ (e ^t^ x) ⋮t (τ2 !<[ A2 ]>)) ->
    Γ ⊢WF (τ2!<[ ((tdEx b1 ϕ1 A1) ^a^ v2) ○ A2 ]>) ->
    Γ ⊢ v2 ⋮v ρ2 ->
    Γ ⊢ v1 ⋮v (ρ2 ⇨ ([: b1 | ϕ1]!<[A1]>)) ->
    Γ ⊢ (tletapp v1 v2 e) ⋮t (τ2!<[ ((tdEx b1 ϕ1 A1) ^a^ v2) ○ A2 ]>)
| TAppArr: forall Γ (v1 v2: value) e ρ2 ρ11 ρ12 A1 τ2 A2 (L: aset),
    (forall x, x ∉ L ->
          (Γ ++ [(x, (ρ11 ⇨ ρ12) ^r^ v2)]) ⊢ (e ^t^ x) ⋮t (τ2 !<[ A2 ]>)) ->
    Γ ⊢WF (τ2!<[ (A1 ^a^ v2) ○ A2 ]>) ->
    Γ ⊢ v2 ⋮v ρ2 ->
    Γ ⊢ v1 ⋮v (ρ2 ⇨ (ρ11 ⇨ ρ12!<[A1]>)) ->
    Γ ⊢ (tletapp v1 v2 e) ⋮t (τ2!<[ (A1 ^a^ v2) ○ A2 ]>)
| TAppOp: forall Γ (op: effop) (v2: value) e ρ2 b1 ϕ1 A1 τ2 A2 (L: aset),
    (forall x, x ∉ L ->
          (Γ ++ [(x, {: b1 | ϕ1} ^r^ v2)]) ⊢ (e ^t^ x) ⋮t (τ2 !<[ A2 ]>)) ->
    Γ ⊢WF (τ2!<[ (A1 ^a^ v2) ○ A2 ]>) ->
    Γ ⊢ v2 ⋮v ρ2 ->
    Γ ⊢ op ⋮o (ρ2 ⇨ ([: b1 | ϕ1]!<[A1]>)) ->
    Γ ⊢ (tleteffop op v2 e) ⋮t (τ2!<[ (A1 ^a^ v2) ○ A2 ]>)
| TMatchb: forall Γ (v: value) e1 e2 ϕ τ (L : aset),
    Γ ⊢WF τ ->
    Γ ⊢ v ⋮v {:TBool | ϕ} ->
    (* We can also directly encode the path condition without mentioning [x]: *)
(*     {: TNat | (qual [# v] (fun V => V !!! 0 = (cbool true))%fin) & ϕ ^q^ v} *)
    (forall x, x ∉ L -> (Γ ++ [(x, {: TBool | b0:c=true & b0:v= v & ϕ})]) ⊢ e1 ⋮t τ) ->
    (forall x, x ∉ L -> (Γ ++ [(x, {: TBool | b0:c=false & b0:v= v & ϕ})]) ⊢ e2 ⋮t τ) ->
    Γ ⊢ (tmatchb v e1 e2) ⋮t τ
with value_type_check : listctx rty -> value -> rty -> Prop :=
| TSubPP: forall Γ (v: value) (ρ1 ρ2: rty),
    Γ ⊢WF ρ2 ->
    Γ ⊢ v ⋮v ρ1 ->
    Γ ⊢ ρ1 <⋮ ρ2 ->
    Γ ⊢ v ⋮v ρ2
| TConst: forall Γ (c: constant),
    Γ ⊢WF (mk_eq_constant c) ->
    Γ ⊢ c ⋮v (mk_eq_constant c)
| TBaseVar: forall Γ (x: atom) b ϕ,
    Γ ⊢WF (mk_eq_var b x) ->
    ctxfind Γ x = Some {: b | ϕ} ->
    Γ ⊢ x ⋮v (mk_eq_var b x)
| TFuncVar: forall Γ (x: atom) ρ τ,
    Γ ⊢WF (ρ ⇨ τ) ->
    ctxfind Γ x = Some (ρ ⇨ τ) ->
    Γ ⊢ x ⋮v (ρ ⇨ τ)
| TFun: forall Γ Tx ρ e τ (L: aset),
    Γ ⊢WF (ρ ⇨ τ) ->
    (forall x, x ∉ L -> (Γ ++ [(x, ρ)]) ⊢ (e ^t^ x) ⋮t (τ ^r^ x)) ->
    Tx = ⌊ ρ ⌋ ->
    Γ ⊢ (vlam Tx e) ⋮v (ρ ⇨ τ)
| TFix: forall Γ (Tx : base_ty) ϕ e τ T (L: aset),
    Γ ⊢WF ({: Tx | ϕ} ⇨ τ) ->
    (* NOTE: should not open the whole type, because the first argument (bound *)
(*     variable 0) of the return type is not the fixed point function but [{: Tx | *)
(*     ϕ}]. The return type should be opened by [x]. *)
    (forall x, x ∉ L ->
          (Γ ++ [(x, {: Tx | ϕ})]) ⊢ (vlam (Tx ⤍ T) e) ^v^ x ⋮v (({: Tx | b0:x≺ x & ϕ} ⇨ τ) ⇨ (τ ^r^ x))) ->
    T = ⌊ τ ⌋ ->
    Γ ⊢ (vfix (Tx ⤍ T) (vlam (Tx ⤍ T) e)) ⋮v ({: Tx | ϕ} ⇨ τ)
where
"Γ '⊢' e '⋮t' τ" := (term_type_check Γ e τ) and "Γ '⊢' e '⋮v' ρ" := (value_type_check Γ e ρ).

Scheme value_term_type_check_ind := Minimality for value_type_check Sort Prop
    with term_value_type_check_ind := Minimality for term_type_check Sort Prop.
Combined Scheme value_term_type_check_mutind from
  value_term_type_check_ind, term_value_type_check_ind.

(** * Properties of the type system *)

Lemma subtyping_preserves_basic_typing Γ τ1 τ2 :
  Γ ⊢ τ1 <⋮ τ2 ->
  ⌊τ1⌋ = ⌊τ2⌋.
Proof.
  qauto.
Qed.

Lemma rty_subtyping_preserves_basic_typing Γ ρ1 ρ2 :
  Γ ⊢ ρ1 <⋮ ρ2 ->
  ⌊ρ1⌋ = ⌊ρ2⌋.
Proof.
  qauto.
Qed.

Lemma effop_typing_preserves_basic_typing Γ ρ op :
  Γ ⊢ op ⋮o ρ ->
  ⌊ρ⌋ = ty_of_op op.
Proof.
  inversion 1; subst. eauto.
Qed.

Lemma value_typing_regular_wf : forall (Γ: listctx rty) (v: value) (ρ: rty),
    Γ ⊢ v ⋮v ρ -> Γ ⊢WF ρ
with tm_typing_regular_wf : forall (Γ: listctx rty) (e: tm) (τ: rty),
    Γ ⊢ e ⋮t τ -> Γ ⊢WF τ.
Proof.
  all: destruct 1; eauto.
Qed.

Lemma value_tm_typing_regular_basic_typing:
  (forall (Γ: listctx rty) (v: value) (ρ: rty),
    Γ ⊢ v ⋮v ρ -> ⌊ Γ ⌋* ⊢t v ⋮v ⌊ ρ ⌋) /\
  (forall (Γ: listctx rty) (e: tm) (τ: rty),
    Γ ⊢ e ⋮t τ -> ⌊ Γ ⌋* ⊢t e ⋮t ⌊ τ ⌋).
Proof.
  apply value_term_type_check_mutind; intros; cbn; subst; eauto.
  - hauto using rty_subtyping_preserves_basic_typing.
  - (* TBaseVar *) econstructor. qauto using ctx_erase_lookup.
  - (* TFuncVar *) econstructor. qauto using ctx_erase_lookup.
  - (* TFun *) econstructor.
    instantiate_atom_listctx.
    rewrite ctx_erase_app_r in H1 by my_set_solver.
    rewrite <- rty_erase_open_eq in H1.
    eauto.
  - (* TFix *) econstructor.
    instantiate_atom_listctx.
    rewrite ctx_erase_app_r in H1 by my_set_solver.
    cbn in H1.
    rewrite <- rty_erase_open_eq in H1.
    eauto.
  - hauto using subtyping_preserves_basic_typing.
  - hauto using subtyping_preserves_basic_typing.
  - econstructor; eauto.
    instantiate_atom_listctx.
    rewrite ctx_erase_app_r in H0 by my_set_solver.
    eauto.
  - econstructor; eauto.
    instantiate_atom_listctx.
    rewrite ctx_erase_app_r in H0 by my_set_solver.
    eauto.
  - econstructor.
    cbn in H0. eauto. eauto.
    instantiate_atom_listctx.
    rewrite ctx_erase_app_r in H0 by my_set_solver.
    rewrite <- rty_erase_open_eq in H0.
    eauto.
  - econstructor.
    cbn in H0. eauto. eauto.
    instantiate_atom_listctx.
    rewrite ctx_erase_app_r in H0 by my_set_solver.
    rewrite <- rty_erase_open_eq in H0.
    eauto.
  - apply effop_typing_preserves_basic_typing in H4. cbn in H4. sinvert H4.
    econstructor; eauto. qauto.
    instantiate_atom_listctx.
    rewrite ctx_erase_app_r in H0 by my_set_solver.
    rewrite <- rty_erase_open_eq in H0; eauto.
  - auto_pose_fv x. repeat specialize_with x.
    rewrite ctx_erase_app_r in H3, H5 by my_set_solver.
    econstructor; eauto.
    eapply basic_typing_strengthen_tm; eauto. my_set_solver.
    eapply basic_typing_strengthen_tm; eauto. my_set_solver.
Qed.

Lemma value_typing_regular_basic_typing: forall (Γ: listctx rty) (v: value) (ρ: rty),
    Γ ⊢ v ⋮v ρ -> ⌊ Γ ⌋* ⊢t v ⋮v ⌊ ρ ⌋.
Proof.
  apply value_tm_typing_regular_basic_typing.
Qed.

Lemma tm_typing_regular_basic_typing: forall (Γ: listctx rty) (e: tm) (τ: rty),
    Γ ⊢ e ⋮t τ -> ⌊ Γ ⌋* ⊢t e ⋮t ⌊ τ ⌋.
Proof.
  apply value_tm_typing_regular_basic_typing.
Qed.

Lemma ctxRst_insert_easy Γ env (x: atom) ρ (v: value):
    ctxRst Γ env ->
    x ∉ ctxdom Γ ->
    ⟦ m{ env }r ρ ⟧ v ->
    pure_rty ρ ->
    ctxRst (Γ ++ [(x, ρ)]) (<[ x := v ]> env).
Proof.
  intros. econstructor; eauto.
  econstructor; eauto using ctxRst_ok_ctx.
  apply rtyR_typed_closed in H1. simp_hyps.
  (* This should be a lemma similar to [msubst_preserves_closed_rty_empty], or
  we should strenghthen this lemma. But don't bother now as it is only used
  here. *)
  sinvert H3.
  econstructor. eauto using lc_msubst_rty, ctxRst_lc.
  rewrite fv_of_msubst_rty_closed in H5 by eauto using ctxRst_closed_env.
  rewrite ctxRst_dom in * by eauto.
  my_set_solver.
Qed.

Lemma ctxRst_ctxfind Γ Γv x ρ :
  ctxRst Γ Γv ->
  ctxfind Γ x = Some ρ ->
  fine_rty ρ ->
  exists (v : value), Γv !! x = Some v /\ ⟦ m{ Γv }r ρ ⟧ v.
Proof.
  induction 1.
  - easy.
  - intros.
    select (ctxfind (_ ++ _) _ = _)
      (fun H => apply ctxfind_app in H; eauto using ok_ctx_ok).

    assert (forall (v' : value), (⟦(m{env}r) ρ⟧) v' ->
                            (⟦(m{<[x0:=v]> env}r) ρ⟧) v'). {
      select (⟦ _ ⟧ _) (fun H => apply rtyR_typed_closed in H). simp_hyps.
      intros.
      apply rtyR_msubst_insert_eq; eauto using ctxRst_closed_env.
      select (_ ⊢t _ ⋮t _)
        (fun H => apply basic_typing_contains_fv_tm in H; simpl in H).
      my_set_solver.
      select (ok_ctx _) (fun H => apply ok_ctx_ok in H; apply ok_post_destruct in H).
      srewrite ctxRst_dom.
      simp_hyps.
      apply not_elem_of_dom. eauto.
    }
    destruct_or!; simp_hyps.
    + eexists. split; eauto.
      assert (x <> x0). {
        select (ok_ctx _) (fun H => sinvert H); listctx_set_simpl.
        select (ctxfind _ _ = _) (fun H => apply ctxfind_some_implies_in_dom in H).
        my_set_solver.
      }
      by simplify_map_eq.
    + simpl in *.
      case_decide; try easy. simplify_eq.
      eexists. split; eauto. by simplify_map_eq.
Qed.

(* Lemma wf_rty_closed Γ ρ : *)
(*   Γ ⊢WF ρ -> closed_rty (ctxdom Γ) ρ. *)
(* Proof. *)
(*   all: destruct 1; eauto; split; *)
(*     let go := *)
(*       repeat select (_ ⊢WF _) (fun H => apply wf_rty_closed in H; sinvert H); *)
(*       repeat destruct select (_ ⊢WFa _); *)
(*       eauto in *)
(*     match goal with *)
(*     | |- lc_rty _ => *)
(*         repeat econstructor; try instantiate_atom_listctx; go *)
(*     | |- _ => *)
(*         simpl; auto_pose_fv x; repeat specialize_with x; go; *)
(*         rewrite <- ?open_fv_rty' in *; *)
(*         rewrite <- ?open_fv_rty' in *; *)
(*         rewrite ?ctxdom_app_union in *; *)
(*         my_set_solver *)
(*     end. *)
(* Qed. *)

Lemma closed_td_comp L A B: closed_td L A○B <-> (closed_td L A /\ closed_td L B).
Proof.
  split; intros; intuition.
  - sinvert H; sinvert H0. constructor; my_set_solver.
  - sinvert H; sinvert H0. constructor; my_set_solver.
  - sinvert H1; sinvert H0. constructor; eauto. constructor; eauto. my_set_solver.
Qed.

Lemma closed_td_ex L b ϕ A:
  closed_td L (tdEx b ϕ A) <->
    ((exists (L: aset), ∀ (x: atom), x ∉ L → lc_td (A ^a^ x)) /\ td_fv A ⊆ L /\ closed_rty L {:b|ϕ}).
Proof.
  split; intros; intuition.
  - sinvert H. sinvert H0. econstructor; my_set_solver.
  - sinvert H; sinvert H0. my_set_solver.
  - sinvert H; sinvert H0. econstructor; eauto. econstructor; simpl; eauto. my_set_solver.
  - sinvert H2. sinvert H1. simp_hyps. constructor; eauto. econstructor; eauto.
    my_set_solver.
Qed.

Lemma langA_comp_spec: forall (A B: transducer) α β,
    a⟦ A ○ B ⟧ α β <-> (exists α', a⟦ A ⟧ α α' /\ a⟦ B ⟧ α' β).
Proof.
  split; intros.
  - simpl in *; simp_hyps.
    eexists; eauto; intuition; repeat rewrite_measure_irrelevant; eauto.
  - simpl in *; simp_hyps.
    eexists; eauto; intuition; repeat rewrite_measure_irrelevant; eauto.
    + apply langA_closed in H0. apply langA_closed in H1.
      rewrite closed_td_comp; eauto.
    + apply langA_valid_trace in H0; intuition.
    + apply langA_valid_trace in H1; intuition.
Qed.

Ltac msubst_erase_simp :=
  match goal with
  | [H: context [ ⌊ (m{ _ }r) _ ⌋ ] |- _ ] => setoid_rewrite <- rty_erase_msubst_eq in H
  | [H: _ |- context [ ⌊ (m{ _ }r) _ ⌋ ] ] => setoid_rewrite <- rty_erase_msubst_eq
  end.

Lemma langA_ex_spec: forall b ϕ (A: transducer) α β,
    (a⟦tdEx b ϕ A⟧) α β <-> exists (v_x: value), (⟦{:b|ϕ}⟧) v_x /\ (a⟦A ^a^ v_x⟧) α β.
Proof.
  split; intros.
  - simpl in *; simp_hyps.
    eexists; eauto; intuition; repeat rewrite_measure_irrelevant; eauto.
    + rewrite closed_td_ex in H. intuition.
    + apply value_reduction_refl' in H4; sinvert H4; subst; eauto.
  - simpl in *; simp_hyps.
    eexists; eauto; intuition; repeat rewrite_measure_irrelevant; eauto.
    + apply langA_closed in H1. sinvert H1. rewrite closed_td_ex. intuition.
      * auto_exists_L. intros. assert (lc v_x) by lc_solver_plus.
        rewrite <- subst_intro_td with (x:=x) in H3; eauto.
        eapply lc_subst_td; eauto. my_set_solver.
      * pose open_fv_td'. my_set_solver.
    + apply langA_valid_trace in H1; intuition.
    + apply langA_valid_trace in H1; intuition.
    + exists v_x. intuition. basic_typing_solver.
      auto_apply; eauto. intros. apply value_reduction_any_ctx. lc_solver_plus.
Qed.

Ltac finerty_destruct τ :=
  destruct τ; repeat msubst_simp;
  try match goal with
  | [H: closed_rty ∅ ({: _ | _ }!<[ _ ]>) |- _ ] =>
      apply closed_rty_fine in H; simpl in H; intuition
  | [H: closed_rty ∅ ((_ !<[ _ ]> )!<[ _ ]>) |- _ ] =>
      apply closed_rty_fine in H; simpl in H; intuition
  end.

Ltac closed_simp :=
  (repeat match goal with
     | [H: _ ⊢ _ ⋮t _ |- closed_rty _ _ ] => apply tm_typing_regular_wf in H
     | [H: ?Γ ⊢WF _ , H': ctxRst ?Γ _ |- closed_rty _ _ ] =>
         eapply (msubst_preserves_closed_rty_empty _ _ _ H') in H; eauto
     end); repeat msubst_simp.

Ltac lc_simpl :=
  repeat match goal with
    | [H: closed_rty _ ([: _ | _ ]!<[ _ ]>) |- lc_td _ ] =>
        rewrite closed_rty_base_td in H; simp_hyp H
    | [H: closed_rty _ ((_ ⇨ _ )!<[ _ ]>) |- lc_td _ ] =>
        rewrite closed_rty_arr_td in H; simp_hyp H
    | [H: closed_rty _ ([: _ | _ ]!<[ _ ]>) |- lc_rty _ ] =>
        rewrite closed_rty_base_td in H; simp_hyp H
    | [H: closed_rty _ ((_ ⇨ _ )!<[ _ ]>) |- lc_rty _ ] =>
        rewrite closed_rty_arr_td in H; simp_hyp H
    | [H: lc_rty ([: _ | _ ]) |- lc_td _ ] =>
        rewrite lc_rty_under_base_q in H
    | [H: lc_rty ({: _ | _ }) |- lc_td _ ] =>
        rewrite lc_rty_over_base_q in H
    | [H: body_td (tdComp _ _) |- body_td _ ] =>
        rewrite body_td_comp in H; simp_hyp H
    | [H: lc_td (tdComp _ _) |- lc_td _ ] =>
        rewrite lc_tdComp_destruct in H; simp_hyp H
    | [H: lc_td (tdEx _ _ _) |- lc_td _ ] =>
        rewrite lc_tdComp_destruct in H; simp_hyp H
    | [H: lc_td (tdEx _ _ _) |- lc_phi1 _ ] =>
        rewrite lc_tdComp_destruct in H; simp_hyp H
    | [H: closed_rty _ _ |- lc_td _ ] => sinvert H
    | [H: closed_rty _ _ |- lc_rty _ ] => sinvert H
    | [H: closed_td _ _ |- lc_td _ ] => sinvert H
    end.

Lemma denotation_application_tlete_base b ϕ A ρ B e_x e:
  (* (exists v_x: value, ⟦ {:b|ϕ} ⟧ v_x) -> *)
  closed_rty ∅ ([:b|ϕ]!<[A]>) ->
  closed_rty ∅ (ρ !<[ (tdEx b ϕ A) ○ B ]>) ->
  ∅ ⊢t tlete e_x e ⋮t ⌊ρ⌋ ->
  ⟦ [:b|ϕ]!<[A]> ⟧ e_x ->
  (forall (v_x : value), ⟦ {:b|ϕ} ⟧ v_x -> ⟦ (ρ !<[ B ]>) ^r^ v_x⟧ (e ^t^ v_x)) ->
  (⟦ ρ !<[ (tdEx b ϕ A) ○ B ]> ⟧) (tlete e_x e).
Proof.
  intros Hclosed1 Hclosed2 HTe He_x He.
  split; [| split]; eauto.
  finerty_destruct ρ.
  - intros α β v H.
    assert (forall v, ((tdEx b ϕ A)○B ^a^ v) = (tdEx b ϕ A) ○ (B ^a^ v)) as Htmp.
    { assert (forall v, (tdEx b ϕ A) ^a^ v = (tdEx b ϕ A)) as Htmp.
      { intros. rewrite open_rec_lc_td; eauto. lc_simpl.
        rewrite lc_tdEx_destruct; intuition. }
      setoid_rewrite <- Htmp at 2. auto. }
    setoid_rewrite Htmp in H; clear Htmp.
    rewrite langA_comp_spec in H. destruct H as (α' & Hα & Hβ).
    rewrite langA_ex_spec in Hα. destruct Hα as (v_x & Hv_x & Hα).
    specialize (He v_x Hv_x).
    destruct He_x as (HTe_x & Hclosed3 & He_x).
    specialize (He_x α α' v_x Hα Hv_x).
    assert (([:b0|ϕ0]!<[B]>) ^r^ v_x = ([:b0|ϕ0]!<[B]>)) as Htmp.
    { rewrite open_rec_lc_rty; eauto. lc_simpl.
      rewrite lc_rty_base_td. intuition; lc_simpl; eauto. }
    rewrite Htmp in He. clear Htmp.
    destruct He as (HTe' & Hclosed4 & He).
    intros Hv.
    specialize (He α' β v Hβ Hv).
    eapply reduction_tlete'; eauto. lc_solver_plus.
  - intros α β H.
    rewrite langA_comp_spec in H. destruct H as (α' & Hα & Hβ).
    rewrite langA_ex_spec in Hα. destruct Hα as (v_x & Hv_x & Hα).
    specialize (He v_x Hv_x).
    destruct He_x as (HTe_x & Hclosed3 & He_x).
    specialize (He_x α α' v_x Hα Hv_x).
    assert ((ρ1⇨ρ2)!<[B]> ^r^ v_x = ((ρ1⇨ρ2)!<[B]>)) as Htmp.
    { rewrite open_rec_lc_rty; eauto. lc_simpl.
      rewrite lc_rty_arr_td. intuition; lc_simpl; eauto. }
    rewrite Htmp in He. clear Htmp.
    destruct He as (HTe' & Hclosed4 & He).
    specialize (He α' β Hβ). destruct He as (v & Hv & He).
    exists v. split; auto.
    eapply reduction_tlete'; eauto. lc_solver_plus.
Qed.

Lemma denotation_application_lam Tx T ρ τ e :
  is_tm_rty τ -> Tx ⤍ T = ⌊ ρ⇨τ ⌋ ->
  ∅ ⊢t vlam Tx e ⋮t Tx ⤍ T ->
  closed_rty ∅ (ρ⇨τ) ->
  (forall (v_x : value),
      ⟦ρ⟧ v_x ->
      ⟦τ ^r^ v_x⟧ (e ^t^ v_x)) ->
  (⟦ρ⇨τ⟧) (vlam Tx e).
Proof.
  intros Htm He Ht Hc H.
  split; [| split]; eauto. sinvert He; eauto.
  exists (vlam Tx e). split. pure_multistep_tac. intros v_x HDv_x.
  repeat rewrite_measure_irrelevant.
  specialize (H v_x HDv_x).
  eapply rtyR_refine; cycle 1; eauto.
  apply rtyR_typed_closed in HDv_x. simp_hyps. sinvert H0.
  split; intros.
  - apply rtyR_typed_closed in H. destruct H as [H _].
    repeat esplit; eauto.
    rewrite <- rty_erase_open_eq.
    sinvert He.
    eapply mk_app_e_v_has_type; eauto.
  - apply reduction_mk_app_e_v'.
    rewrite reduction_tletapp_lam.
    intuition. basic_typing_regular_simp. basic_typing_regular_simp.
    rewrite reduction_nest_tlete; eauto.
  - rewrite is_tm_rty_open; eauto.
Qed.

Lemma denotation_application_fixed (Tx : base_ty) T ϕ τ e :
  is_tm_rty τ -> T = ⌊ τ ⌋ ->
  ∅ ⊢t vfix (Tx ⤍ T) (vlam (Tx ⤍ T) e) ⋮v Tx ⤍ T ->
  closed_rty ∅ ({:Tx|ϕ}⇨τ) ->
  (forall (v_x : value),
      ⟦{:Tx | ϕ}⟧ v_x ->
      ⟦({:Tx | (b0:v≺ v_x) & ϕ} ⇨ τ) ⇨ (τ ^r^ v_x)⟧
        ((vlam (Tx ⤍ T) e) ^v^ v_x)) ->
  ⟦{:Tx | ϕ}⇨τ⟧ (vfix (Tx ⤍ T) (vlam (Tx ⤍ T) e)).
Proof.
  intros Htm He Ht Hc Hlam.
  split; [| split]; eauto. subst; eauto.
  exists (vfix (Tx ⤍ T) (vlam (Tx ⤍ T) e)). split. pure_multistep_tac. intros v_x HDc.
  repeat rewrite_measure_irrelevant.
  assert (exists c, v_x = vconst c) as H. {
    apply rtyR_typed_closed in HDc.
    destruct HDc as [H _]. sinvert H.
    eauto using basic_typing_base_canonical_form.
  }
  destruct H as [c ->].
  induction c using (well_founded_induction constant_lt_well_founded).
  specialize (Hlam c HDc).
  destruct Hlam as (HTlam & HClam & (_ & _ & HDlam)).
  specialize (HDlam (vfix (Tx ⤍ T) (vlam (Tx ⤍ T) e))). subst.
  repeat rewrite_measure_irrelevant.
  rewrite open_rty_idemp in HDlam by eauto using lc.
  eapply rtyR_refine; cycle 1.
  2: {
    apply HDlam.
    split; [| split]; eauto.
    - sinvert HClam. econstructor. sinvert H0. eauto. my_set_solver.
    - exists (vfix (Tx ⤍ ⌊τ⌋) (vlam (Tx ⤍ ⌊τ⌋) e)). split. pure_multistep_tac.
      intros v_y HDv_y.
      repeat rewrite_measure_irrelevant.
      assert (exists y, v_y = vconst y). {
        apply rtyR_typed_closed in HDv_y.
        destruct HDv_y as [HTv_y _]. sinvert HTv_y.
        eauto using basic_typing_base_canonical_form.
      }
      destruct H0 as (y&->).
      destruct HDv_y as (HTy&_&Hy).
      assert (∀ α : list evop, α ⊧ y ↪*{ α} y) as Htmp by pure_multistep_tac.
      specialize (Hy y Htmp).
      rewrite qualifier_and_open in Hy.
      rewrite denote_qualifier_and in Hy.
      simp_hyps.
      apply H; eauto.
      apply denot_const_overrty; eauto. apply rtyR_typed_closed in HDc. simp_hyps; eauto.
  }
  split; intros.
  - subst. cbn in HTlam.
    repeat esplit.
    eapply mk_app_e_v_has_type; eauto.
    + apply rtyR_typed_closed in HDc. destruct HDc as [HTc _].
      sinvert HTc. eauto.
    + eapply mk_app_e_v_has_type; eauto. simpl.
      rewrite <- rty_erase_open_eq in HTlam; eauto.
  - apply reduction_mk_app_e_v'.
    apply reduction_tletapp_fix. split; eauto.
    apply reduction_mk_app_e_v in H0; eauto.
    eauto using basic_typing_regular_value.
  - rewrite is_tm_rty_open; eauto.
Qed.
