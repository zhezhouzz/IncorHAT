From stdpp Require Import mapset.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import TransducerProp.
From CT Require Import RefinementTypeProp.
From CT Require Import DenotationProp.
From CT Require Import InstantiationProp.
From CT Require Import TypingProp.

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
Import Typing.

(** * Main metatheoretic results *)

Ltac simpl_fv :=
  do_hyps (fun H => try match type of H with
                    | _ ∉ _ =>
                        simpl in H; rewrite ?ctxRst_dom in H by eassumption
                    end).

(** Fundamental theorem for event operator typing *)
Lemma builtin_fundamental:
  well_formed_builtin_typing ->
  forall (Γ: listctx rty) (op: effop) (ρ : rty),
    Γ ⊢ op ⋮o ρ ->
    forall Γv, ctxRst Γ Γv -> ⟦ m{ Γv }r ρ ⟧ (value_of_op op).
Proof.
  intros HWF Γ op ρ Hop Γv HΓv. sinvert Hop.
  apply H1; eauto.
  apply HWF in H0.
  rewrite msubst_fresh_rty; eauto.
  apply rtyR_typed_closed in H0. simp_hyps.
  sinvert H3.
  my_set_solver.
Qed.

Check closed_rty_fine.

Lemma pure_rty_open ρ (v: value): pure_rty (ρ ^r^ v) = pure_rty ρ.
Proof.
  induction ρ; simpl; intros; eauto.
Qed.

Ltac fine_solver :=
  repeat (match goal with
          | [H: _ |- pure_rty ({: _ | _ })] => simpl; auto
          | [H: _ |- pure_rty ([: _ | _ ])] => simpl; auto
          | [H: _ |- pure_rty ( _ ^r^ _)] => rewrite pure_rty_open
          | [ H: _ ⊢WF _ |- pure_rty _ ] =>
              apply closed_rty_fine in H; eauto; simpl in H; intuition; eauto
          | [ H: _ ⊢WF _ |- fine_rty _ ] =>
              apply closed_rty_fine in H; eauto; simpl in H;intuition; eauto
          end).

Ltac finerty_destruct τ :=
  destruct τ; repeat msubst_simp;
  try match goal with
    | [H: _ ⊢WF ({: _ | _ }!<[ _ ]>) |- _ ] =>
        apply closed_rty_fine in H; simpl in H; intuition
    | [H: _ ⊢WF ((_ !<[ _ ]> )!<[ _ ]>) |- _ ] =>
        apply closed_rty_fine in H; simpl in H; intuition
    | [H: closed_rty ∅ ({: _ | _ }!<[ _ ]>) |- _ ] =>
        apply closed_rty_fine in H; simpl in H; intuition
    | [H: closed_rty ∅ ((_ !<[ _ ]> )!<[ _ ]>) |- _ ] =>
        apply closed_rty_fine in H; simpl in H; intuition
    end.

Lemma msubst_destruct_rev_tm: forall (Γv: env) (x: atom) (v_x: value) (e: tm),
    closed_env Γv -> closed_value v_x -> x ∉ dom Γv ->
    (m{<[x:=v_x]> Γv}t) e = m{Γv}t ({ x:=v_x }t e).
Proof.
  intros.
  rewrite_msubst_insert.
  2 : { apply not_elem_of_dom. eauto. }
  revert_all.
  intros *.
  msubst_tac.
  setoid_rewrite <- H1; eauto.
  2: { my_set_solver. }
  rewrite subst_commute_tm by my_set_solver; eauto.
Qed.

  (* At some point the proof is very slow without marking [msubst] opaque. *)
Opaque msubst.

Ltac basic_typing_simp :=
  repeat match goal with
    | [H: ?Γ ⊢ _ ⋮v _ |- ⌊?Γ⌋* ⊢t _ ⋮t _ ] => apply value_typing_regular_basic_typing in H; simpl in H
    | [H: ?Γ ⊢ _ ⋮v _ |- ⌊?Γ⌋* ⊢t _ ⋮v _ ] => apply value_typing_regular_basic_typing in H; simpl in H
    | [H: ?Γ ⊢ _ ⋮t _ |- ⌊?Γ⌋* ⊢t _ ⋮t _ ] => apply tm_typing_regular_basic_typing in H; simpl in H
    | [H: ?Γ ⊢ _ ⋮t _ |- ⌊?Γ⌋* ⊢t _ ⋮v _ ] => apply tm_typing_regular_basic_typing in H; simpl in H
    | [H: (_ ⊢ _ ⋮t _) |- (_ ⊢t  _ ⋮t _) ] => apply tm_typing_regular_basic_typing in H
    end.

Ltac simp_tac :=
  closed_simp; basic_typing_simp.
(* msubst_erase_simp *)

Lemma closed_rty_arr:
  ∀ (L : aset) (ρ τ : rty),
    closed_rty L (ρ⇨τ) ↔ closed_rty L ρ ∧ (fine_rty (ρ⇨τ)) /\
      (exists L: (aset), forall x : atom, x ∉ L -> lc_rty (τ ^r^ x)) /\ (rty_fv τ ⊆ L).
Proof.
  split; intros.
  - sinvert H. sinvert H0. intuition. econstructor; eauto. my_set_solver. auto_exists_L. my_set_solver.
  - simp_hyps. sinvert H. econstructor; eauto. auto_exists_L.
    my_set_solver.
Qed.

Ltac ctx_erase_tac :=
  repeat match goal with
  | [H: context [ ⌊_ ++ [(_, _)]⌋* ] |- _ ] => rewrite ctx_erase_app_r in H by my_set_solver
  | [H: _ |- context [ ⌊_ ++ [(_, _)]⌋* ] ] => rewrite ctx_erase_app_r by my_set_solver
  end.

Lemma body_rty_open_lc: forall (v: value) τ,
  lc v -> (exists (L:aset), ∀ x : atom, x ∉ L → lc_rty (τ ^r^ x)) -> lc_rty (τ ^r^ v).
Proof.
  intros. simp_hyps.
  auto_pose_fv x.
  erewrite <- open_subst_same_rty. instantiate (1:= x).
  apply subst_lc_rty; eauto.
  apply H0.
  all: my_set_solver.
Qed.

(** Combined fundamental theorem for value typing (refinemnet types) and term
  typing (Hoare automata types) *)
Theorem fundamental_combined:
  well_formed_builtin_typing ->
  (forall (Γ: listctx rty) (v: value) (ρ: rty),
      Γ ⊢ v ⋮v ρ ->
      forall Γv, ctxRst Γ Γv -> ⟦ m{Γv}r ρ ⟧ (m{Γv}v v)) /\
    (forall (Γ: listctx rty) (e: tm) (τ: rty),
        Γ ⊢ e ⋮t τ ->
        forall Γv, ctxRst Γ Γv -> ⟦ m{ Γv }r τ ⟧ (m{ Γv }t e)).
Proof.
  pose value_reduction_any_ctx as HPureStep.
  intros HWFbuiltin.
  apply value_term_type_check_mutind.
  15: {
    intros Γ v e1 e2 ϕ τ L HWF HTv HDv HTe1 HDe1 HTe2 HDe2 Γv HΓv.
    assert (∅ ⊢t (m{Γv}t) (tmatchb v e1 e2) ⋮t ⌊τ⌋) as HT. {
      apply value_typing_regular_basic_typing in HTv.
      eapply msubst_preserves_basic_typing_tm_empty; eauto.
      auto_exists_L.
      - auto_pose_fv x. ospecialize (HTe1 x _). my_set_solver.
        apply tm_typing_regular_basic_typing in HTe1.
        rewrite ctx_erase_app_r in HTe1.
        eapply basic_typing_strengthen_tm; eauto.
        all: my_set_solver.
      - auto_pose_fv x. ospecialize (HTe2 x _). my_set_solver.
        apply tm_typing_regular_basic_typing in HTe2.
        rewrite ctx_erase_app_r in HTe2.
        eapply basic_typing_strengthen_tm; eauto.
        all: my_set_solver.
    }.
    auto_pose_fv x. repeat specialize_with x.
    ospecialize* HDv; eauto.
    repeat msubst_simp.
    assert (exists (b : bool), m{Γv}v v = b) as [b He] by
        qauto using value_typing_regular_basic_typing,
                    msubst_preserves_basic_typing_value_empty,
                    basic_typing_bool_canonical_form.
    rewrite He in *.
    assert (ctxRst
              (Γ ++ [(x, {:TBool|(b0:c=b) & ((b0:v=v) & ϕ)})])
              (<[x:=vconst b]>Γv)) as HΓv'. {
      apply ctxRst_insert_easy; eauto. my_set_solver.
      repeat msubst_simp.
      repeat apply denote_base_rty_qualifier_and; eauto.
      apply_eq mk_eq_constant_denote_rty. clear - HΓv.
      rewrite_msubst msubst_qualifier. simpl. repeat msubst_simp. admit.
      apply_eq mk_eq_constant_denote_rty. clear - He HΓv.
      rewrite_msubst msubst_qualifier. simpl. rewrite He. repeat msubst_simp. admit.
      fine_solver.
    }

    destruct b.
    + ospecialize* HDe1; eauto.
      rewrite msubst_insert_fresh_tm in HDe1 by
          (eauto using ctxRst_closed_env; simpl_fv; my_set_solver).
      rewrite msubst_insert_fresh_rty in HDe1 by
          (eauto using ctxRst_closed_env; simpl_fv; my_set_solver).
      eapply rtyR_refine; eauto.
      split; eauto using reduction_matchb_true.
      repeat esplit; eauto.
      apply rtyR_typed_closed in HDe1. destruct HDe1 as [HTe1' _].
      rewrite <- rty_erase_msubst_eq in HTe1'. eauto.
    + ospecialize* HDe2; eauto.
      rewrite msubst_insert_fresh_tm in HDe2 by
          (eauto using ctxRst_closed_env; simpl_fv; my_set_solver).
      rewrite msubst_insert_fresh_rty in HDe2 by
          (eauto using ctxRst_closed_env; simpl_fv; my_set_solver).
      eapply rtyR_refine; eauto.
      split; eauto using reduction_matchb_false.
      repeat esplit; eauto.
      apply rtyR_typed_closed in HDe2. destruct HDe2 as [HTe2' _].
      rewrite <- rty_erase_msubst_eq in HTe2'. eauto.
  }
  14: {
    intros Γ op v2 e ρ2 b1 ϕ1 A1 τ2 A2 L HTe HDe HWF HTv2 HDv2 HTop Γv HΓv.
    assert (∅ ⊢t (m{Γv}t) (tleteffop op v2 e) ⋮t ⌊τ2⌋) as HT. {
      apply value_typing_regular_basic_typing in HTv2.
      eapply msubst_preserves_basic_typing_tm_empty; eauto.
      sinvert HTop. simpl in *. sinvert H2.
      auto_exists_L. rewrite <- H4. eauto. intros.
      ospecialize * (HTe x); eauto. my_set_solver.
      apply tm_typing_regular_basic_typing in HTe.
      ctx_erase_tac. eauto.
    }
    assert (∅ ⊢t (m{Γv}t) (tletapp (value_of_op op) v2 e) ⋮t ⌊τ2⌋) as HTapp. {
      repeat msubst_simp. rewrite msubst_value_of_op.
      clear - HT.
      sinvert HT. sinvert H5.
      auto_exists_L. apply value_of_op_regular_basic_typing.
    }
    assert (lc v2) as Hlcv2. {
      apply value_typing_regular_basic_typing in HTv2.
      lc_solver_plus.
    }
    sinvert HTop. apply HWFbuiltin in H0. destruct H1 as (_ & Hsub).
    ospecialize* (Hsub _ HΓv).
    rewrite msubst_fresh_rty; eauto. admit. repeat msubst_simp.
    rewrite msubst_open_td. repeat msubst_simp.
    eapply denotation_application_tletopapp; eauto.
    all: try solve [simp_tac].
    + eapply msubst_preserves_closed_rty_empty in HWF; eauto. repeat msubst_simp.
      rewrite msubst_open_td in HWF; eauto. repeat msubst_simp.
      all: simp_tac.
    + msubst_erase_simp. eauto.
    + intros v_x Hv_x.
      auto_pose_fv x.
      assert (ok_ctx (Γ ++ [(x, {:b1|ϕ1} ^r^ v2)])) as Hok. {
        econstructor.
        rtyR_regular_simp; misc_solver.
        fine_solver.
        rewrite closed_rty_arr in H. simp_hyp H.
        econstructor. apply body_rty_open_lc; eauto. admit.
        simpl in H3. simpl. pose (open_fv_qualifier ϕ1 v2 1).
        apply value_typing_regular_basic_typing in HTv2.
        apply basic_typing_contains_fv_value in HTv2.
        rewrite ctx_erase_dom in HTv2.
        all: my_set_solver.
      }
      remember (<[x:=v_x]> Γv) as Γv'.
      ospecialize* (HDe x _ Γv'); eauto; subst. misc_solver.
      { econstructor; eauto; simp_tac.
        + rewrite msubst_open_rty. repeat msubst_simp.
          all: simp_tac.
      }
      rewrite msubst_insert_fresh_rty in HDe. repeat msubst_simp.
      rewrite open_rec_lc_rty.
      erewrite msubst_intro_tm; eauto.
      all: rtyR_regular_simp; misc_solver.
  }
  (* [TSubPP] *)
  - intros Γ v ρ1 ρ2 HWFρ2 _ HDρ1 Hsub Γv HΓv. specialize (HDρ1 _ HΓv).
    apply Hsub in HDρ1; auto.
  (* [TConst] *)
  - intros Γ c HWF Γv HΓv. repeat msubst_simp. eauto using mk_eq_constant_denote_rty.
  (* [TBaseVar] *)
  - intros Γ x b ϕ Hwf Hfind Γv HΓv.
    dup_hyp HΓv (fun H => eapply ctxRst_ctxfind in H; eauto). simp_hyps.
    repeat msubst_simp. rewrite H0.
    destruct H1 as [H _].
    sinvert H. cbn in H3.
    dup_hyp H3 (fun H => apply basic_typing_base_canonical_form in H).
    simp_hyps. subst. sinvert H3.
    eauto using mk_eq_constant_denote_rty. fine_solver.
  (* [TFuncVar] *)
  - intros Γ x ρ τ Hwf Hfind Γv HΓv.
    dup_hyp HΓv (fun H => eapply ctxRst_ctxfind in H; eauto). simp_hyps.
    repeat msubst_simp.
    by rewrite H0. fine_solver.
  (* [TFun] *)
  - intros Γ Tx ρ e τ L HWF Ht HDe He Γv HΓv. repeat msubst_simp.
    eapply denotation_application_lam; eauto.
    { is_tm_rty_tac. rtyR_regular_simp; eauto. }
    cbn. repeat rewrite <- rty_erase_msubst_eq. subst. eauto.
    {
      assert (Γ ⊢ vlam Tx e ⋮v (ρ⇨τ)) by eauto using value_type_check.
      eapply value_typing_regular_basic_typing in H.
      eapply msubst_preserves_basic_typing_value_empty in H; eauto.
      repeat msubst_simp.
      econstructor. apply_eq H. cbn. subst. reflexivity.
    } {
      eapply_eq msubst_preserves_closed_rty_empty; eauto.
      msubst_simp.
    }
    intros v_x Hv_x.
    auto_pose_fv x. repeat specialize_with x.
    assert (ctxRst (Γ ++ [(x, ρ)]) (<[x:=v_x]> Γv)) as HΓv'. {
      apply ctxRst_insert_easy; eauto. my_set_solver. fine_solver.
    }
    ospecialize* HDe; eauto.
    rewrite <- msubst_intro_tm in HDe by
        (eauto using ctxRst_closed_env, ctxRst_lc, rtyR_closed_value;
         simpl_fv; my_set_solver).
    rewrite <- msubst_intro_rty in HDe by
        (eauto using ctxRst_closed_env, ctxRst_lc, rtyR_closed_value;
         simpl_fv; my_set_solver).
    eauto.
  (* [TFix] *)
  - intros Γ Tx ϕ e τ T L HWF Hlam HDlam He Γv HΓv. repeat msubst_simp.
    eapply denotation_application_fixed; eauto.
    { is_tm_rty_tac. rtyR_regular_simp; eauto. }
    by rewrite <- rty_erase_msubst_eq.
    {
      assert (Γ ⊢ vfix (Tx ⤍ T) (vlam (Tx ⤍ T) e) ⋮v ({:Tx|ϕ}⇨τ))
        by eauto using value_type_check.
      eapply value_typing_regular_basic_typing in H.
      eapply msubst_preserves_basic_typing_value_empty in H; eauto.
      repeat msubst_simp.
      apply_eq H. cbn. subst. eauto.
    } {
      eapply_eq msubst_preserves_closed_rty_empty; eauto.
      repeat msubst_simp.
    }
    intros v_x Hv_x.
    auto_pose_fv x. repeat specialize_with x.
    assert (ctxRst (Γ ++ [(x, {:Tx|ϕ})]) (<[x:=v_x]> Γv)) as HΓv'. {
      apply ctxRst_insert_easy; eauto. my_set_solver.
      msubst_simp. fine_solver.
    }
    ospecialize* HDlam; eauto.
    rewrite <- msubst_intro_value in HDlam by
        (eauto using ctxRst_closed_env, ctxRst_lc, rtyR_closed_value;
         simpl_fv; my_set_solver).
    repeat msubst_simp.
    rewrite <- msubst_intro_rty in HDlam by
        (eauto using ctxRst_closed_env, ctxRst_lc, rtyR_closed_value;
         simpl_fv; my_set_solver).
    rewrite msubst_insert_fresh_rty in HDlam by
      (eauto using ctxRst_closed_env, rtyR_closed_value; simpl_fv; my_set_solver).
    rewrite_msubst msubst_qualifier in HDlam.
    rewrite msubst_insert_fresh_qualifier in HDlam by
      (eauto using ctxRst_closed_env, rtyR_closed_value; simpl_fv; my_set_solver).
    apply_eq HDlam.
    simpl. repeat msubst_simp.
    clear. simplify_map_eq. eauto.
  (* [TEPur] *)
  - intros Γ v ρ HWF Hv HDv Γv HΓv. specialize (HDv _ HΓv).
    repeat msubst_simp.
    split; [| split]. {
      eapply value_typing_regular_basic_typing in Hv.
      eapply msubst_preserves_basic_typing_value_empty in Hv; eauto.
      cbn. rewrite <- rty_erase_msubst_eq. eauto.
    } {
      eapply_eq msubst_preserves_closed_rty_empty; eauto.
      repeat msubst_simp.
    }
    finerty_destruct ρ; intros.
    + simpl in *. simp_hyps; subst. repeat auto_apply.
      intros. apply value_reduction_any_ctx. basic_typing_regular_simp.
    + exists ((m{Γv}v) v). simpl in *. simp_hyps; subst. intuition.
      * exists ((m{Γv}v) v). intuition. apply value_reduction_any_ctx. lc_solver_plus.
      * apply value_reduction_any_ctx. basic_typing_regular_simp.
  (* [TSub] *)
  - intros Γ e τ1 τ2 HWFτ2 _ HDτ1 Hsub Γv HΓv. specialize (HDτ1 _ HΓv).
    apply Hsub in HDτ1; auto.
  (* [TJoin] *)
  - unfold join. intros Γ e τ1 τ2 τ3 HWFτ3 _ HDτ1 _ HDτ2 (_ & _ & Hjoin) Γv HΓv.
    specialize (HDτ1 _ HΓv). specialize (HDτ2 _ HΓv).
    rewrite Hjoin; eauto.
  (* [TLetE] *)
  - intros Γ e_x e b ϕ A ρ' B L HTe_x HDe_x HWF HTe HDe Γv HΓv. repeat msubst_simp.
    eapply denotation_application_tlete_base; simp_tac.
    + eapply msubst_preserves_basic_typing_tm_empty in HTe; eauto.
      auto_exists_L; intros.
      ospecialize* (HTe_x x); eauto; simp_tac. misc_solver.
      simpl in HTe_x. rewrite ctx_erase_app in HTe_x.
      eapply msubst_preserves_basic_typing_tm in HTe_x; eauto.
      unfold ctx_erase in HTe_x.
      simpl in *. my_simplify_map. repeat msubst_erase_simp.
      rewrite msubst_open_var_tm in HTe_x; eauto.
      all: rtyR_regular_simp; misc_solver.
    + ospecialize* HDe; eauto. repeat msubst_simp.
    + intros v_x Hv_x.
      auto_pose_fv x.
      remember (<[x:=v_x]> Γv) as Γv'.
      ospecialize* (HDe_x x _ Γv'); eauto; subst. misc_solver.
      { econstructor; eauto; simp_tac.
        + rtyR_regular_simp; misc_solver. simp_tac.
          rewrite closed_rty_base_td in HTe. simp_hyp HTe.
          rewrite closed_rty_base_flip; eauto. }
      rewrite msubst_insert_fresh_rty in HDe_x. repeat msubst_simp.
      rewrite open_rec_lc_rty.
      erewrite msubst_intro_tm; eauto.
      all: rtyR_regular_simp; misc_solver.
  - admit.
  - (* [TApp] *) intros Γ v1 v2 e ρ1 b2 ϕ2 A ρ B L HTe HDe HWF HTv2 HDv2 HTv1 HDv1 Γv HΓv.
    assert (lc v2) as Hlcv2. {
      apply value_typing_regular_basic_typing in HTv2.
      lc_solver_plus.
    }
    assert (⌊ Γ ⌋* ⊢t (mk_app_e_v v1 v2) ⋮t b2). {
      eapply mk_app_e_v_has_type; basic_typing_simp; eauto.
    }
    ospecialize* HDv1; eauto. ospecialize* HDv2; eauto. repeat msubst_simp.
    rewrite msubst_open_td; eauto. repeat msubst_simp.
    eapply denotation_application_tletapp_base; eauto.
    all: try solve [simp_tac].
    + eapply msubst_preserves_closed_rty_empty in HWF; eauto. repeat msubst_simp.
      rewrite msubst_open_td in HWF; eauto. repeat msubst_simp.
      all: simp_tac.
    + assert (⌊ Γ ⌋* ⊢t tletapp v1 v2 e ⋮t ⌊ ρ ⌋) as HH.
      { basic_typing_simp. auto_exists_L. intros. ospecialize * (HTe x _). my_set_solver.
        basic_typing_simp. setoid_rewrite insert_union_singleton_r. rewrite ctx_erase_app in HTe. simpl in HTe.
        unfold ctx_erase in *.
        rewrite map_cons in HTe. simpl in HTe. my_simplify_map. eauto.
        apply not_elem_of_dom_1. rewrite ctx_erase_dom. my_set_solver. }
      eapply msubst_preserves_basic_typing_tm_empty in HH; eauto.
      rewrite <- rty_erase_msubst_eq. simp_tac.
    + intros v_x Hv_x.
      auto_pose_fv x.
      remember (<[x:=v_x]> Γv) as Γv'.
      ospecialize* (HDe x _ Γv'); eauto; subst. misc_solver.
      { econstructor; eauto; simp_tac.
        + rtyR_regular_simp; misc_solver. fine_solver.
          closed_simp. rewrite closed_rty_arr in HTv1. simp_hyp HTv1.
          econstructor; eauto.
          auto_pose_fv y. ospecialize * (H6 y _). my_set_solver.
          rewrite <- open_subst_same_rty with (x:=y).
          apply subst_lc_rty. simpl. rewrite lc_rty_base_flip.
          simpl in H6. rewrite lc_rty_base_td in H6. intuition.
          auto. my_set_solver.
          pose (open_fv_qualifier).
          apply basic_typing_contains_fv_tm in H.
          rewrite ctx_erase_dom in *.
          my_set_solver.
        + rewrite msubst_open_rty. repeat msubst_simp.
          all: simp_tac.
      }
      rewrite msubst_insert_fresh_rty in HDe. repeat msubst_simp.
      rewrite open_rec_lc_rty.
      erewrite msubst_intro_tm; eauto.
      all: rtyR_regular_simp; misc_solver.
  (* [TApp] *)
  - intros Γ v1 v2 e ρ ρx ρ2 A A' B L HWF HTv2 HDv2 HTv1 HDv1 HTe HDe Γv HΓv. admit.
  (* [TEOpApp] *)
  - intros Γ op v2 e ρ2 b1 ϕ1 A1 τ2 A2 L HTe HDe HWF HTv2 HDv2 HTop Γv HΓv.
    assert (∅ ⊢t (m{Γv}t) (tleteffop op v2 e) ⋮t ⌊τ2⌋) as HT. {
      apply value_typing_regular_basic_typing in HTv2.
      eapply msubst_preserves_basic_typing_tm_empty; eauto.
      sinvert HTop. simpl in *. sinvert H2.
      auto_exists_L. rewrite <- H4. eauto. intros.
      (* Check BtEffOp. *)
      eapply BtEffOp. 
      auto_exists_L.
      eauto using term_type_check.
      apply_eq tm_typing_regular_basic_typing. eauto using term_type_check.
    }
    assert (∅ ⊢t (m{Γv}t) (tletapp (value_of_op op) v2 e) ⋮t ⌊ρ⌋) as HTapp. {
      repeat msubst_simp. rewrite msubst_value_of_op.
      clear - HT.
      sinvert HT. sinvert H5.
      econstructor; eauto.
      econstructor. instantiate_atom_listctx.
      econstructor; eauto. econstructor. by simplify_map_eq.
      instantiate_atom_listctx. simpl.
      econstructor. econstructor. by simplify_map_eq.
    }
    eapply (rtyR_refine _ (m{Γv}t (tletapp (value_of_op op) v2 e))). {
      split; eauto.
      repeat msubst_simp. rewrite msubst_value_of_op.
      assert (body ((m{Γv}t) e)) as Hbody. {
        sinvert HT. eexists. eauto using basic_typing_regular_tm.
      }
      clear - Hbody. intros * Hstepv.
      apply reduction_tleteffop in Hstepv.
      destruct Hstepv as (c2 & c_x & β' & -> & -> & Hred & Hstepv).
      eapply_eq multistep_step. econstructor; eauto using lc.
      unshelve (repeat econstructor); exact ∅.
      econstructor. simpl. econstructor; eauto.
      econstructor; eauto. by simplify_list_eq.
      simpl. econstructor. econstructor; solve [eauto].
      by simplify_list_eq. by simplify_list_eq.
    }

    eapply builtin_fundamental in HTop; eauto.
    rewrite <- (msubst_value_of_op Γv) in HTop.
    revert HTapp HTop. generalize (value_of_op op) as v1.
    intros v1 HTapp HDv1.
    ospecialize* HDv2; eauto. repeat msubst_simp.
    split; [| split]. {
      cbn. by rewrite <- rty_erase_msubst_eq.
    } {
      eapply_eq msubst_preserves_closed_rty_empty; eauto using wf_rty_closed.
      repeat msubst_simp.
    }
    (* The rest of the proof is exactly the same as [TApp]. Maybe find a way to
    abstract this and avoid copy-pasting. *)
    intros α β v HDα Hstepv.
    apply reduction_tletapp in Hstepv.
    destruct Hstepv as (βx & βe & v_x & -> & Hstepv_x & Hstepv).
    auto_pose_fv x. repeat specialize_with x.
    destruct HDv1 as (_ & _ & HDapp).
    repeat rewrite_measure_irrelevant.
    ospecialize* HDapp; eauto.
    destruct HDapp as (_ & _ & HDapp). simpl in HDapp.
    rewrite <- !msubst_open_am in HDapp by
        (eauto using ctxRst_closed_env, ctxRst_lc).
    rewrite <- !msubst_open_rty in HDapp by
        (eauto using ctxRst_closed_env, ctxRst_lc).
    ospecialize* HDapp; eauto.
    destruct HDapp as [HDv_x HDα_βx].
    assert (ctxRst (Γ ++ [(x, ρx ^p^ v2)]) (<[x:=v_x]> Γv)) as HΓv'. {
      apply ctxRst_insert_easy; eauto. my_set_solver.
    }
    ospecialize* HDe; eauto.
    rewrite <- msubst_intro_tm in HDe by
        (eauto using ctxRst_closed_env, ctxRst_lc, rtyR_closed_value;
         simpl_fv; my_set_solver).
    repeat msubst_simp.
    destruct HDe as (_ & _ & HDe).
    rewrite msubst_insert_fresh_am in HDe;
      eauto using ctxRst_closed_env, rtyR_closed_value.
    2 : {
      apply not_elem_of_union. split.
      simpl_fv; my_set_solver.
      eapply not_elem_of_weaken. 2: eauto using open_fv_am.
      my_set_solver.
    }
    ospecialize* HDe; eauto.
    repeat rewrite_measure_irrelevant.
    rewrite msubst_insert_fresh_rty in HDe by
      (eauto using ctxRst_closed_env, rtyR_closed_value;
       simpl_fv; my_set_solver).
    rewrite msubst_insert_fresh_am in HDe by
      (eauto using ctxRst_closed_env, rtyR_closed_value;
       simpl_fv; my_set_solver).
    clear - HDe.
    by simplify_list_eq.
  (* [TMatchb] *)
  - intros Γ v e1 e2 ϕ τ L HWF HTv HDv HTe1 HDe1 HTe2 HDe2 Γv HΓv.
    assert (∅ ⊢t (m{Γv}t) (tmatchb v e1 e2) ⋮t ⌊τ⌋) as HT by
      qauto using term_type_check,
                  tm_typing_regular_basic_typing,
                  msubst_preserves_basic_typing_tm_empty.
    auto_pose_fv x. repeat specialize_with x.
    ospecialize* HDv; eauto.
    repeat msubst_simp.
    assert (exists (b : bool), m{Γv}v v = b) as [b He] by
        qauto using value_typing_regular_basic_typing,
                    msubst_preserves_basic_typing_value_empty,
                    basic_typing_bool_canonical_form.
    rewrite He in *.
    assert (ctxRst
              (Γ ++ [(x, {:TBool|(b0:c=b) & ((b0:v=v) & ϕ)})])
              (<[x:=vconst b]>Γv)) as HΓv'. {
      apply ctxRst_insert_easy; eauto. my_set_solver.
      repeat msubst_simp.
      repeat apply denote_base_rty_qualifier_and; eauto.
      apply_eq mk_eq_constant_denote_rty. clear - HΓv.
      rewrite_msubst msubst_qualifier. simpl. repeat msubst_simp.
      apply_eq mk_eq_constant_denote_rty. clear - He HΓv.
      rewrite_msubst msubst_qualifier. simpl. rewrite He. repeat msubst_simp.
    }

    destruct b.
    + ospecialize* HDe1; eauto.
      rewrite msubst_insert_fresh_tm in HDe1 by
          (eauto using ctxRst_closed_env; simpl_fv; my_set_solver).
      rewrite msubst_insert_fresh_rty in HDe1 by
          (eauto using ctxRst_closed_env; simpl_fv; my_set_solver).
      eapply rtyR_refine; eauto.
      split; eauto using reduction_matchb_true.
      repeat esplit; eauto.
      apply rtyR_typed_closed in HDe1. destruct HDe1 as [HTe1' _].
      rewrite <- rty_erase_msubst_eq in HTe1'. eauto.
    + ospecialize* HDe2; eauto.
      rewrite msubst_insert_fresh_tm in HDe2 by
          (eauto using ctxRst_closed_env; simpl_fv; my_set_solver).
      rewrite msubst_insert_fresh_rty in HDe2 by
          (eauto using ctxRst_closed_env; simpl_fv; my_set_solver).
      eapply rtyR_refine; eauto.
      split; eauto using reduction_matchb_false.
      repeat esplit; eauto.
      apply rtyR_typed_closed in HDe2. destruct HDe2 as [HTe2' _].
      rewrite <- rty_erase_msubst_eq in HTe2'. eauto.
Qed.

Theorem fundamental:
  well_formed_builtin_typing ->
  forall (Γ: listctx rty) (e: tm) (τ: rty),
    Γ ⊢ e ⋮t τ ->
    forall σ, ctxRst Γ σ -> ⟦ m{ σ }r τ ⟧ (m{ σ }t e).
Proof.
  qauto using fundamental_combined_aux, tm_typing_regular_basic_typing, value_typing_regular_basic_typing.
Qed.

(** Fundamental theorem for value typing *)
Theorem fundamental_value:
  well_formed_builtin_typing ->
  forall (Γ: listctx rty) (v: value) (ρ: rty),
    Γ ⊢ v ⋮v ρ ->
    forall Γv, ctxRst Γ Γv -> p⟦ m{Γv}p ρ ⟧ (m{Γv}v v).
Proof.
  qauto using fundamental_combined.
Qed.

(** Fundamental theorem (Theorem 4.8) *)
Theorem fundamental:
  well_formed_builtin_typing ->
  forall (Γ: listctx rty) (e: tm) (τ: rty),
    Γ ⊢ e ⋮t τ ->
    forall σ, ctxRst Γ σ -> ⟦ m{ σ }h τ ⟧ (m{ σ }t e).
Proof.
  qauto using fundamental_combined.
Qed.

Transparent msubst.

(** A general type soundness theorem *)
Corollary soundness' :
  well_formed_builtin_typing ->
  forall (e : tm) (ρ : rty) (A : am),
    [] ⊢ e ⋮t (<[ A ] ρ [ A ]>) ->
    forall (v : value) α α',
      a⟦ A ⟧ α ->
      α ⊧ e ↪*{ α' } v ->
      p⟦ ρ ⟧ v /\ a⟦ A ⟧ (α ++ α').
Proof.
  intros HWF * HT * HDα Hstepv.
  eapply fundamental in HT; eauto using ctxRst.
  unfold msubst in HT. rewrite !map_fold_empty in HT.
  qauto using HT.
Qed.

(** Type soundness (Corollary 4.9) *)
Corollary soundness :
  well_formed_builtin_typing ->
  forall (f: value) (b_x b_y: base_ty) (t: rty) (A: am),
    [] ⊢ f ⋮v (b_x⇢(mk_top b_y)⇨(<[ A ] t [ A ]>)) ->
    forall v_x v_y,
      ∅ ⊢t v_x ⋮v b_x ->
      ∅ ⊢t v_y ⋮v b_y ->
      forall (v : value) α α',
        a⟦ {0 ~a> v_y} ({1 ~a> v_x} A) ⟧ α ->
        α ⊧ (mk_app_e_v f v_y) ↪*{ α' } v ->
        a⟦ {0 ~a> v_y} ({1 ~a> v_x} A) ⟧ (α ++ α') /\
          p⟦ {0 ~p> v_y} ({1 ~p> v_x} t) ⟧ v.
Proof.
  intros HWF * HT * HTv_x HTv_y * HDα Hstepv.
  eapply fundamental_value in HT; eauto using ctxRst.
  unfold msubst in HT. rewrite !map_fold_empty in HT.
  destruct HT as (_&_&HD); eauto.
  repeat rewrite_measure_irrelevant.
  specialize (HD _ HTv_x).
  simpl rty_open in HD.
  destruct HD as (_&_&HD).
  repeat rewrite_measure_irrelevant.
  apply and_comm.
  eapply HD; eauto using mk_top_denote_rty.
Qed.

Print Assumptions soundness.
