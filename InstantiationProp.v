From stdpp Require Import mapset fin_maps.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import Qualifier.
From CT Require Import TransducerProp.
From CT Require Import RefinementTypeProp.
From CT Require Import Denotation.
From CT Require Import Instantiation.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import OperationalSemantics.
Import BasicTyping.
Import Trace.
Import ListCtx.
Import Qualifier.
Import Transducer.
Import Denotation.
Import RefinementType.

(** This file proves auxiliary lemmas about multi-substitution and provides
  handy tactics. *)

Lemma closed_env_insert env x v :
  env !! x = None ->
  closed_env (<[x:=v]>env) ->
  closed_value v /\ closed_env env.
Proof.
  intro.
  unfold closed_env.
  rewrite map_Forall_insert; eauto.
Qed.

Ltac apply_msubst_ind :=
  unfold msubst;
  match goal with
  | |- ?T =>
      match T with
      | context [map_fold ?a ?b ?m] => revert m; eapply fin_maps.map_fold_ind; eauto
      end
  end.

Ltac gen_closed_env :=
  repeat
    match goal with
    | H : closed_env (<[?i:=_]> ?m), H' : ?m !! ?i = None |- _ =>
        let H1 := fresh "H" in
        let H2 := fresh "H" in
        destruct (closed_env_insert _ _ _ H' H) as [H1 H2];
        uniq_hyp H1; uniq_hyp H2
    | H : closed_env ?m, H' : ?m !! _ = Some ?v |- _ =>
        let T := fresh "H" in
        assert (closed_value v) as T by eauto;
        uniq_hyp T
    (* | H : ctxRst _ ?env |- _ => *)
    (*     let T := fresh "H" in *)
    (*     assert (closed_env env) as T by eauto using ctxRst_closed_env; *)
    (*     uniq_hyp T *)
    end.

Lemma msubst_insert {T: Type}
  (f_subst: atom -> value -> T -> T)
  (subst_commute: forall x u_x y u_y e,
      x <> y -> x ∉ fv_value u_y -> y ∉ fv_value u_x ->
      f_subst x u_x (f_subst y u_y e) =
        f_subst y u_y (f_subst x u_x e))
  :
  forall (Γv: env) (x: atom) (v_x: value) (e: T),
    closed_env Γv ->
    closed_value v_x ->
    Γv !! x = None ->
    msubst f_subst (<[x:=v_x]> Γv) e = f_subst x v_x (msubst f_subst Γv e).
Proof.
  intros.
  apply map_fold_insert_L; eauto.
  intros.
  assert (closed_env (<[x:=v_x]>Γv)). {
    apply map_Forall_insert; eauto.
  }
  gen_closed_env.
  apply subst_commute; eauto; my_set_solver.
Qed.

Ltac msubst_tac :=
  intros *; apply_msubst_ind; intros; subst; simpl; eauto;
  gen_closed_env; simp_hyps; subst.

Ltac fold_msubst := change (map_fold ?s ?e ?m) with (msubst s m e) in *.

Ltac rewrite_msubst_insert :=
  cbn; fold_msubst; rewrite !msubst_insert;
  eauto using subst_commute_value, subst_commute_tm, subst_commute_qualifier,
    subst_commute_rty, subst_commute_td.

Lemma rty_erase_msubst_eq ρ Γv :
  rty_erase ρ = rty_erase (m{Γv}r ρ).
Proof.
  msubst_tac.
  qauto using rty_erase_subst_eq.
Qed.

Lemma msubst_qualifier: forall Γv ϕ,
    closed_env Γv ->
    (m{Γv}q) ϕ =
      match ϕ with
      | qual vals prop =>
          qual (vmap (m{Γv}v) vals) prop
      end.
Proof.
  msubst_tac.
  - destruct ϕ. simpl.
Admitted.
(*     f_equal. *)
(*     erewrite Vector.map_ext. *)
(*     by rewrite Vector.map_id. *)
(*     intros. simpl. *)
(*     by rewrite map_fold_empty. *)
(*   - destruct ϕ. simpl. f_equal. *)
(*     rewrite Vector.map_map. *)
(*     apply Vector.map_ext. *)
(*     intros; rewrite_msubst_insert. *)
(* Qed. *)

Lemma msubst_qualifier_and Γv q1 q2 :
  closed_env Γv ->
  m{Γv}q (q1 & q2) = (m{Γv}q q1) & (m{Γv}q q2).
Proof.
  msubst_tac.
Admitted.
(*   rewrite_msubst_insert. *)
(*   apply qualifier_and_subst. *)
(* Qed. *)

(* Lemma msubst_aany: forall (Γv: env), *)
(*     m{Γv}a aany = aany. *)
(* Proof. *)
(*   msubst_tac. *)
(* Qed. *)

Lemma msubst_tdComp: forall (Γv: env) A1 A2,
    closed_env Γv ->
    m{Γv}a (tdComp A1 A2) = (tdComp (m{Γv}a A1) (m{Γv}a A2)).
Proof.
  msubst_tac.
Admitted.
(*   rewrite_msubst_insert. *)
(* Qed. *)

Lemma msubst_tdLitId: forall (Γv: env) op ϕ,
    closed_env Γv ->
    m{Γv}a ⟨op|ϕ⟩/id = ⟨op| m{Γv}q ϕ⟩/id.
Admitted.
(* Proof. *)
(*   msubst_tac. rewrite_msubst_insert. *)
(* Qed. *)

Lemma msubst_tdLitOut: forall (Γv: env) op1 ϕ op2 v_arg v_ret,
    closed_env Γv ->
    m{Γv}a ⟨op1|ϕ⟩/⟨op2|v_arg|v_ret⟩ = ⟨op1| m{Γv}q ϕ⟩/⟨op2|m{Γv}v v_arg| m{Γv}v v_ret⟩.
Admitted.
(* Proof. *)
(*   msubst_tac. rewrite_msubst_insert. *)
(* Qed. *)

Lemma msubst_constant: forall Γv (c: constant), (m{Γv}v) c = c.
Proof.
  msubst_tac.
Admitted.

Lemma msubst_bvar: forall Γv n, (m{Γv}v) (vbvar n) = vbvar n.
Proof.
  msubst_tac.
Admitted.

Lemma msubst_fvar: forall Γv (x : atom),
    closed_env Γv ->
    (m{Γv}v) x = match Γv !! x with
                 | Some v => v
                 | None => x
                 end.
Proof.
Admitted.
(*   msubst_tac. *)
(*   destruct (decide (x = i)); subst; simplify_map_eq. reflexivity. *)
(*   case_match. *)
(*   apply subst_fresh_value. *)
(*   gen_closed_env. my_set_solver. *)
(*   simpl. rewrite decide_False; eauto. *)
(* Qed. *)

Lemma msubst_lam: forall Γv T e,
    closed_env Γv ->
    ((m{Γv}v) (vlam T e)) = (vlam T ((m{Γv}t) e)).
Proof.
Admitted.
(*   msubst_tac. rewrite_msubst_insert. *)
(* Qed. *)

Lemma msubst_fix: forall Γv T e,
    closed_env Γv ->
    ((m{Γv}v) (vfix T e)) = (vfix T ((m{Γv}t) e)).
Proof.
Admitted.
(*   msubst_tac. rewrite_msubst_insert. *)
(* Qed. *)

Lemma msubst_value: forall Γv (v:value),
    closed_env Γv ->
    (m{Γv}t) (treturn v) = (m{Γv}v) v.
Proof.
Admitted.
(*   msubst_tac. rewrite_msubst_insert. *)
(* Qed. *)

Lemma msubst_match: forall Γv (v: value) e1 e2,
    closed_env Γv ->
    ((m{Γv}t) (tmatchb v e1 e2)) = tmatchb (m{Γv}v v) (m{Γv}t e1) (m{Γv}t e2).
Proof.
Admitted.
(*   msubst_tac. rewrite_msubst_insert. *)
(* Qed. *)

Lemma msubst_lete: forall (Γv: env) e_x e,
    closed_env Γv ->
    (m{Γv}t (tlete e_x e) = tlete ((m{Γv}t) e_x) ((m{Γv}t) e)).
Proof.
Admitted.
(*   msubst_tac. rewrite_msubst_insert. *)
(* Qed. *)

Lemma msubst_tleteffop: forall Γv op (v2: value) e,
    closed_env Γv ->
    (m{Γv}t) (tleteffop op v2 e) = (tleteffop op (m{Γv}v v2) (m{Γv}t e)).
Proof.
Admitted.
(*   msubst_tac. rewrite_msubst_insert. *)
(* Qed. *)

Lemma msubst_tletapp: forall Γv (v1 v2: value) e,
    closed_env Γv ->
    (m{Γv}t) (tletapp v1 v2 e) = (tletapp (m{Γv}v v1) (m{Γv}v v2) (m{Γv}t e)).
Proof.
Admitted.
(*   msubst_tac. rewrite_msubst_insert. *)
(* Qed. *)

Lemma msubst_overrty: forall Γv b ϕ,
    closed_env Γv ->
    (m{Γv}r) {:b|ϕ} = {:b| (m{Γv}q) ϕ}.
Proof.
Admitted.
(*   msubst_tac. rewrite_msubst_insert. *)
(* Qed. *)

Lemma msubst_underrty: forall Γv b ϕ,
    closed_env Γv ->
    ((m{Γv}r) ([:b|ϕ])) = ([:b|(m{Γv}q) ϕ]).
Proof.
Admitted.

Lemma msubst_arrrty: forall Γv ρ τ,
    closed_env Γv ->
    ((m{Γv}r) (ρ⇨τ)) = ((m{Γv}r ρ)⇨(m{Γv}r τ)).
Proof.
Admitted.

Lemma msubst_tdrty: forall Γv ρ a,
    closed_env Γv ->
    ((m{Γv}r) (ρ!<[a]>)) = ((m{Γv}r ρ)!<[ m{Γv}a a ]>).
Proof.
Admitted.
(*   msubst_tac. rewrite_msubst_insert. *)
(* Qed. *)

Tactic Notation "rewrite_msubst" constr(lem) "in" hyp(H) :=
  rewrite lem in H; eauto using ctxRst_closed_env.

Tactic Notation "rewrite_msubst" constr(lem) :=
  rewrite lem in *; eauto using ctxRst_closed_env.

Lemma msubst_mk_top: forall (Γv: env) b,
    closed_env Γv ->
    m{Γv}r (mk_top b) = mk_top b.
Proof.
  intros.
  unfold mk_top, mk_q_under_top.
  rewrite_msubst msubst_underrty.
  rewrite_msubst msubst_qualifier.
Qed.

Lemma msubst_mk_eq_constant: forall (Γv: env) c,
    closed_env Γv ->
    (m{Γv}r) (mk_eq_constant c) = (mk_eq_constant c).
Proof.
  intros.
  unfold mk_eq_constant, mk_q_bvar_eq_val.
  repeat rewrite_msubst msubst_underrty.
  repeat rewrite_msubst msubst_qualifier.
  simpl.
  repeat rewrite_msubst msubst_bvar.
  repeat rewrite_msubst msubst_constant.
Qed.

Lemma msubst_mk_eq_var: forall (Γv: env) b x v,
    closed_env Γv ->
    Γv !! x = Some v ->
    (m{Γv}r) (mk_eq_var b x) = [:b | b0:v= v].
Proof.
  intros.
  unfold mk_eq_var.
  repeat rewrite_msubst msubst_underrty.
  repeat rewrite_msubst msubst_qualifier.
  simpl.
  repeat rewrite_msubst msubst_bvar.
  repeat rewrite_msubst msubst_fvar.
  rewrite H0.
  eauto.
Qed.

Ltac msubst_simp :=
  match goal with
  | H: context [ m{ _ }a (tdComp _ _) ] |- _ => rewrite msubst_tdComp in H
  | |- context [ m{ _ }a (tdComp _ _) ] => rewrite msubst_tdComp
  | H: context [ m{ _ }a (tdLitId _ _) ] |- _ => rewrite msubst_tdLitId in H
  | |- context [ m{ _ }a (tdLitId _ _) ] => rewrite msubst_tdLitId
  | H: context [ m{ _ }a (tdLitOut _ _ _ _ _) ] |- _ => rewrite msubst_tdLitOut in H
  | |- context [ m{ _ }a (tdLitOut _ _ _ _ _) ] => rewrite msubst_tdLitOut
  | H: context [ m{ _ }t (tlete _ _) ] |- _ => rewrite msubst_lete in H
  | |- context [ m{ _ }t (tlete _ _) ] => rewrite msubst_lete
  | H: context [ m{ _ }t (tleteffop _ _ _) ] |- _ => rewrite msubst_tleteffop in H
  | |- context [ m{ _ }t (tleteffop _ _ _) ] => rewrite msubst_tleteffop
  | H: context [ m{ _ }t (tletapp _ _ _) ] |- _ => rewrite msubst_tletapp in H
  | |- context [ m{ _ }t (tletapp _ _ _) ] => rewrite msubst_tletapp
  | H: context [ m{ _ }v (vfix _ _) ] |- _ => rewrite msubst_fix in H
  | |- context [ m{ _ }v (vfix _ _) ] => rewrite msubst_fix
  | H: context [ m{ _ }t (treturn _) ] |- _ => rewrite msubst_value in H
  | |- context [ m{ _ }t (treturn _) ] => rewrite msubst_value
  | H: context [ m{ _ }v (vlam _ _) ] |- _ => rewrite msubst_lam in H
  | |- context [ m{ _ }v (vlam _ _) ] => rewrite msubst_lam
  | H: context [ m{ _ }t (tmatchb _ _ _) ] |- _ => rewrite msubst_match in H
  | |- context [ m{ _ }t (tmatchb _ _ _) ] => rewrite msubst_match
  | H: context [ m{ _ }v (vbvar _) ] |- _ => rewrite msubst_bvar in H
  | |- context [ m{ _ }v (vbvar _) ] => rewrite msubst_bvar
  | H: context [ m{ _ }v (vfvar _) ] |- _ => rewrite msubst_fvar in H
  | |- context [ m{ _ }v (vfvar _) ] => rewrite msubst_fvar
  | H: context [ m{ _ }v (vconst _) ] |- _ => rewrite msubst_constant in H
  | |- context [ m{ _ }v (vconst _) ] => rewrite msubst_constant
  (* | H: context [ m{ _ }q _ ] |- _ => rewrite msubst_qualifier in H *)
  (* | |- context [ m{ _ }q _ ] => rewrite msubst_qualifier *)
  | H: context [ m{ _ }q (_ & _) ] |- _ => rewrite msubst_qualifier_and in H
  | |- context [ m{ _ }q (_ & _) ] => rewrite msubst_qualifier_and
  | H: context [ m{ _ }r {: _ | _ } ] |- _ => rewrite msubst_overrty in H
  | |- context [ m{ _ }r {: _ | _ } ] => rewrite msubst_overrty
  | H: context [ m{ _ }r [: _ | _ ] ] |- _ => rewrite msubst_underrty in H
  | |- context [ m{ _ }r [: _ | _ ] ] => rewrite msubst_underrty
  | H: context [ m{ _ }r (_ ⇨ _) ] |- _ => rewrite msubst_arrrty in H
  | |- context [ m{ _ }r (_ ⇨ _ ) ] => rewrite msubst_arrrty
  | H: context [ m{ _ }r (_ !<[_]>) ] |- _ => rewrite msubst_tdrty in H
  | |- context [ m{ _ }r (_ !<[_]>) ] => rewrite msubst_tdrty
  | H: context [ m{ _ }r (mk_top _) ] |- _ => rewrite msubst_mk_top in H
  | |- context [ m{ _ }r (mk_top _) ] => rewrite msubst_mk_top
  | H: context [ m{ _ }r (mk_eq_constant _) ] |- _ => rewrite msubst_mk_eq_constant in H
  | |- context [ m{ _ }r (mk_eq_constant _) ] => rewrite msubst_mk_eq_constant
  | H: context [ m{ _ }r (mk_eq_var _ ?x) ], H': _ !! ?x = Some ?v |- _ => rewrite msubst_mk_eq_var with (v:=v) in H
  | H': _ !! ?x = Some ?v |- context [ m{ _ }r (mk_eq_var _ ?x) ] => rewrite msubst_mk_eq_var with (v:=v)
  end; eauto using ctxRst_closed_env.

(* Most lemmas here are generalization of the corresponding lemmas about
single-substitution. *)

Lemma msubst_open_var_tm: forall (Γv: env) e k (x: atom),
    closed_env Γv ->
    map_Forall (fun _ v => lc (treturn v)) Γv ->
    x ∉ dom Γv ->
    (m{Γv}t) ({k ~t> x} e) = {k ~t> x} ((m{Γv}t) e).
Proof.
Admitted.
(*   msubst_tac. *)
(*   rewrite_msubst_insert. *)
(*   apply map_Forall_insert in H2; eauto. *)
(*   rewrite H6; eauto. *)
(*   apply subst_open_var_tm. my_set_solver. *)
(*   qauto. qauto. *)
(*   my_set_solver. *)
(* Qed. *)

Lemma msubst_open_td: forall (Γv: env) (a: transducer) k (v_x: value),
    closed_env Γv ->
    map_Forall (fun _ v => lc (treturn v)) Γv ->
    (m{Γv}a) ({k ~a> v_x} a) = {k ~a> (m{Γv}v v_x)} (m{Γv}a a).
Proof.
Admitted.
(*   msubst_tac. *)
(*   rewrite_msubst_insert. *)
(*   apply map_Forall_insert in H2; eauto. simp_hyps. *)
(*   subst. *)
(*   by apply subst_open_td. *)
(* Qed. *)

Lemma msubst_open_rty: forall (Γv: env) (ρ: rty) k (v_x: value),
    closed_env Γv ->
    map_Forall (fun _ v => lc (treturn v)) Γv ->
    (m{Γv}r) ({k ~r> v_x} ρ) = {k ~r> (m{Γv}v v_x)} (m{Γv}r ρ).
Proof.
Admitted.
(*   msubst_tac. *)
(*   rewrite_msubst_insert. *)
(*   apply map_Forall_insert in H2; eauto. simp_hyps. *)
(*   subst. *)
(*   by apply subst_open_rty. *)
(* Qed. *)

(* Lemma msubst_open_hty: forall (Γv: env) (τ: hty) k (v_x: value), *)
(*     closed_env Γv -> *)
(*     map_Forall (fun _ v => lc (treturn v)) Γv -> *)
(*     (m{Γv}h) ({k ~h> v_x} τ) = {k ~h> (m{Γv}v v_x)} (m{Γv}h τ). *)
(* Proof. *)
(*   msubst_tac. *)
(*   rewrite_msubst_insert. *)
(*   apply map_Forall_insert in H2; eauto. simp_hyps. *)
(*   subst. *)
(*   by apply subst_open_hty. *)
(* Qed. *)

Lemma msubst_fresh_qualifier Γv ϕ :
  dom Γv ## qualifier_fv ϕ ->
  (m{Γv}q) ϕ = ϕ.
Proof.
Admitted.
(*   msubst_tac. *)
(*   rewrite H0. *)
(*   apply subst_fresh_qualifier. *)
(*   my_set_solver. *)
(*   my_set_solver. *)
(* Qed. *)

Lemma msubst_fresh_rty Γv ρ :
  dom Γv ## rty_fv ρ ->
  (m{Γv}r) ρ = ρ.
Proof.
Admitted.
(*   msubst_tac. *)
(*   rewrite H0. *)
(*   apply subst_fresh_rty. *)
(*   my_set_solver. *)
(*   my_set_solver. *)
(* Qed. *)

Lemma msubst_fresh_td Γv a :
  dom Γv ## td_fv a ->
  (m{Γv}a) a = a.
Proof.
Admitted.
(*   msubst_tac. *)
(*   rewrite H0. *)
(*   apply subst_fresh_td. *)
(*   my_set_solver. *)
(*   my_set_solver. *)
(* Qed. *)

Lemma msubst_fresh_value Γv v :
  dom Γv ## fv_value v ->
  (m{Γv}v) v = v.
Proof.
Admitted.
(*   msubst_tac. *)
(*   rewrite H0. *)
(*   apply subst_fresh_value. *)
(*   my_set_solver. *)
(*   my_set_solver. *)
(* Qed. *)

(* The proof can be reduced to [msubst_open_var_tm] and [msubst_fresh_tm]
(haven't defined yet; see [msubst_fresh_rty] for example). It's a pain to define
those for every [msubst_intro_*]. Don't bother yet. *)
Lemma msubst_intro_tm: forall (Γv: env) e k (v_x: value) (x: atom),
    closed_env Γv ->
    closed_value v_x ->
    map_Forall (fun _ v => lc (treturn v)) Γv ->
    x ∉ dom Γv ∪ stale e ->
    {k ~t> v_x} ((m{Γv}t) e) = (m{<[x:=v_x]> Γv}t) ({k ~t> x} e).
Proof.
Admitted.
(*   intros. *)
(*   rewrite_msubst_insert. *)
(*   2 : apply not_elem_of_dom; my_set_solver. *)
(*   revert_all. *)
(*   intros *. *)
(*   msubst_tac. *)
(*   rewrite map_fold_empty. rewrite open_subst_same_tm. auto. my_set_solver. *)
(*   rewrite_msubst_insert. *)
(*   apply map_Forall_insert in H3; eauto. *)
(*   rewrite subst_commute_tm by my_set_solver. *)
(*   rewrite <- H0 by my_set_solver. *)
(*   by rewrite subst_open_tm_closed by qauto. *)
(* Qed. *)

Lemma msubst_intro_value: forall (Γv: env) (v: value) k (v_x: value) (x: atom),
    closed_env Γv ->
    closed_value v_x ->
    map_Forall (fun _ v => lc (treturn v)) Γv ->
    x ∉ dom Γv ∪ stale v ->
    {k ~v> v_x} ((m{Γv}v) v) = (m{<[x:=v_x]> Γv}v) ({k ~v> x} v).
Proof.
  intros.
  rewrite_msubst_insert.
  2 : apply not_elem_of_dom; my_set_solver.
  revert_all.
  intros *.
Admitted.
(*   msubst_tac. *)
(*   rewrite map_fold_empty. rewrite open_subst_same_value. auto. my_set_solver. *)
(*   rewrite_msubst_insert. *)
(*   apply map_Forall_insert in H3; eauto. *)
(*   rewrite subst_commute_value by my_set_solver. *)
(*   rewrite <- H0 by my_set_solver. *)
(*   by rewrite subst_open_value_closed by qauto. *)
(* Qed. *)

(* Lemma msubst_intro_hty: forall (Γv: env) e k (v_x: value) (x: atom), *)
(*     closed_env Γv -> *)
(*     closed_value v_x -> *)
(*     map_Forall (fun _ v => lc (treturn v)) Γv -> *)
(*     x ∉ dom Γv ∪ stale e -> *)
(*     {k ~h> v_x} ((m{Γv}h) e) = (m{<[x:=v_x]> Γv}h) ({k ~h> x} e). *)
(* Proof. *)
(*   intros. *)
(*   rewrite_msubst_insert. *)
(*   2 : apply not_elem_of_dom; my_set_solver. *)
(*   revert_all. *)
(*   intros *. *)
(*   msubst_tac. *)
(*   rewrite map_fold_empty. *)
(*   rewrite open_subst_same_hty. auto. my_set_solver. *)
(*   rewrite_msubst_insert. *)
(*   apply map_Forall_insert in H3; eauto. *)
(*   rewrite subst_commute_hty by my_set_solver. *)
(*   rewrite <- H0 by my_set_solver. *)
(*   by rewrite subst_open_hty_closed by qauto. *)
(* Qed. *)

Lemma msubst_intro_rty: forall (Γv: env) e k (v_x: value) (x: atom),
    closed_env Γv ->
    closed_value v_x ->
    map_Forall (fun _ v => lc (treturn v)) Γv ->
    x ∉ dom Γv ∪ stale e ->
    {k ~r> v_x} ((m{Γv}r) e) = (m{<[x:=v_x]> Γv}r) ({k ~r> x} e).
Proof.
  intros.
  rewrite_msubst_insert.
  2 : apply not_elem_of_dom; my_set_solver.
  revert_all.
  intros *.
Admitted.
(*   msubst_tac. *)
(*   rewrite map_fold_empty. *)
(*   rewrite open_subst_same_rty. auto. my_set_solver. *)
(*   rewrite_msubst_insert. *)
(*   apply map_Forall_insert in H3; eauto. *)
(*   rewrite subst_commute_rty by my_set_solver. *)
(*   rewrite <- H0 by my_set_solver. *)
(*   by rewrite subst_open_rty_closed by qauto. *)
(* Qed. *)

Lemma msubst_intro_qualifier: forall (Γv: env) e k (v_x: value) (x: atom),
    closed_env Γv ->
    closed_value v_x ->
    map_Forall (fun _ v => lc (treturn v)) Γv ->
    x ∉ dom Γv ∪ stale e ->
    {k ~q> v_x} ((m{Γv}q) e) = (m{<[x:=v_x]> Γv}q) ({k ~q> x} e).
Proof.
  intros.
  rewrite_msubst_insert.
  2 : apply not_elem_of_dom; my_set_solver.
  revert_all.
  intros *.
Admitted.
(*   msubst_tac. *)
(*   rewrite map_fold_empty. rewrite open_subst_same_qualifier. auto. my_set_solver. *)
(*   rewrite_msubst_insert. *)
(*   apply map_Forall_insert in H3; eauto. *)
(*   rewrite subst_commute_qualifier by my_set_solver. *)
(*   rewrite <- H0 by my_set_solver. *)
(*   by rewrite subst_open_qualifier_closed by qauto. *)
(* Qed. *)

Lemma msubst_intro_td: forall (Γv: env) e k (v_x: value) (x: atom),
    closed_env Γv ->
    closed_value v_x ->
    map_Forall (fun _ v => lc (treturn v)) Γv ->
    x ∉ dom Γv ∪ stale e ->
    {k ~a> v_x} ((m{Γv}a) e) = (m{<[x:=v_x]> Γv}a) ({k ~a> x} e).
Proof.
  intros.
  rewrite_msubst_insert.
  2 : apply not_elem_of_dom; my_set_solver.
  revert_all.
  intros *.
Admitted.
(*   msubst_tac. *)
(*   rewrite map_fold_empty. *)
(*   rewrite open_subst_same_td. auto. my_set_solver. *)
(*   rewrite_msubst_insert. *)
(*   apply map_Forall_insert in H3; eauto. *)
(*   rewrite subst_commute_td by my_set_solver. *)
(*   rewrite <- H0 by my_set_solver. *)
(*   by rewrite subst_open_td_closed by qauto. *)
(* Qed. *)

Lemma msubst_rty_fv_subseteq Γv v_x ρ:
  closed_env Γv ->
  closed_value v_x ->
  rty_fv (m{Γv}r ρ) ⊆ rty_fv ρ.
Proof.
Admitted.
(*   msubst_tac. *)
(*   rewrite fv_of_subst_rty_closed by eauto. my_set_solver. *)
(* Qed. *)

Lemma msubst_qualifier_fv_subseteq Γv v_x ϕ:
  closed_env Γv ->
  closed_value v_x ->
  qualifier_fv (m{Γv}q ϕ) ⊆ qualifier_fv ϕ.
Proof.
Admitted.
(*   msubst_tac. *)
(*   rewrite fv_of_subst_qualifier_closed by eauto. my_set_solver. *)
(* Qed. *)

Lemma msubst_td_fv_subseteq Γv v_x a:
  closed_env Γv ->
  closed_value v_x ->
  td_fv (m{Γv}a a) ⊆ td_fv a.
Proof.
Admitted.
(*   msubst_tac. *)
(*   rewrite fv_of_subst_td_closed by eauto. my_set_solver. *)
(* Qed. *)

Lemma msubst_tm_fv_subseteq Γv v_x t:
  closed_env Γv ->
  closed_value v_x ->
  fv_tm (m{Γv}t t) ⊆ fv_tm t.
Proof.
Admitted.
(*   msubst_tac. *)
(*   rewrite fv_of_subst_tm by eauto. my_set_solver. *)
(* Qed. *)

Lemma msubst_value_fv_subseteq Γv v_x (v : value):
  closed_env Γv ->
  closed_value v_x ->
  fv_value (m{Γv}v v) ⊆ fv_tm v.
Proof.
Admitted.
(*   msubst_tac. *)
(*   rewrite fv_of_subst_value by eauto. my_set_solver. *)
(* Qed. *)

Lemma msubst_insert_fresh_rty Γv x v_x ρ:
  closed_env Γv ->
  closed_value v_x ->
  x ∉ dom Γv ∪ rty_fv ρ ->
  (m{<[x:=v_x]> Γv}r) ρ = (m{Γv}r) ρ.
Proof.
  intros.
  rewrite_msubst_insert. 2: apply not_elem_of_dom; my_set_solver.
  apply subst_fresh_rty.
  eapply not_elem_of_weaken; eauto.
  rewrite msubst_rty_fv_subseteq by eauto. my_set_solver.
Qed.

Lemma msubst_insert_fresh_qualifier Γv x v_x ϕ:
  closed_env Γv ->
  closed_value v_x ->
  x ∉ dom Γv ∪ qualifier_fv ϕ ->
  (m{<[x:=v_x]> Γv}q) ϕ = (m{Γv}q) ϕ.
Proof.
  intros.
  rewrite_msubst_insert. 2: apply not_elem_of_dom; my_set_solver.
  apply subst_fresh_qualifier.
  eapply not_elem_of_weaken; eauto.
  rewrite msubst_qualifier_fv_subseteq by eauto. my_set_solver.
Qed.

Lemma msubst_insert_fresh_td Γv x v_x a:
  closed_env Γv ->
  closed_value v_x ->
  x ∉ dom Γv ∪ td_fv a ->
  (m{<[x:=v_x]> Γv}a) a = (m{Γv}a) a.
Proof.
  intros.
  rewrite_msubst_insert. 2: apply not_elem_of_dom; my_set_solver.
  apply subst_fresh_td.
  eapply not_elem_of_weaken; eauto.
  rewrite msubst_td_fv_subseteq by eauto. my_set_solver.
Qed.

Lemma msubst_insert_fresh_tm Γv x v_x t:
  closed_env Γv ->
  closed_value v_x ->
  x ∉ dom Γv ∪ fv_tm t ->
  (m{<[x:=v_x]> Γv}t) t = (m{Γv}t) t.
Proof.
  intros.
  rewrite_msubst_insert. 2: apply not_elem_of_dom; my_set_solver.
  apply subst_fresh_tm.
  eapply not_elem_of_weaken; eauto.
  rewrite msubst_tm_fv_subseteq by eauto. my_set_solver.
Qed.

Lemma msubst_insert_fresh_value Γv x v_x (v : value):
  closed_env Γv ->
  closed_value v_x ->
  x ∉ dom Γv ∪ fv_tm v ->
  (m{<[x:=v_x]> Γv}v) v = (m{Γv}v) v.
Proof.
  intros.
  rewrite_msubst_insert. 2: apply not_elem_of_dom; my_set_solver.
  apply subst_fresh_value.
  eapply not_elem_of_weaken; eauto.
  rewrite msubst_value_fv_subseteq by eauto. my_set_solver.
Qed.

Lemma lc_msubst_rty Γv (ρ: rty):
  lc_rty (m{Γv}r ρ) ->
  map_Forall (fun _ v => lc (treturn v)) Γv ->
  lc_rty ρ.
Proof.
  msubst_tac.
Admitted.
(*   apply map_Forall_insert in H2; eauto. simp_hyps. *)
(*   eauto using lc_subst_rty. *)
(* Qed. *)

Lemma msubst_lc_rty Γv (ρ: rty):
  lc_rty ρ ->
  map_Forall (fun _ v => lc (treturn v)) Γv ->
  lc_rty (m{Γv}r ρ).
Proof.
  msubst_tac.
Admitted.
(*   apply map_Forall_insert in H2; eauto. simp_hyps. *)
(*   eauto using subst_lc_rty. *)
(* Qed. *)

(* Lemma lc_msubst_hty Γv (τ: hty): *)
(*   lc_hty (m{Γv}h τ) -> *)
(*   map_Forall (fun _ v => lc (treturn v)) Γv -> *)
(*   lc_hty τ. *)
(* Proof. *)
(*   msubst_tac. *)
(*   apply map_Forall_insert in H2; eauto. simp_hyps. *)
(*   eauto using lc_subst_hty. *)
(* Qed. *)

(* Lemma msubst_lc_hty Γv (τ: hty): *)
(*   lc_hty τ -> *)
(*   map_Forall (fun _ v => lc (treturn v)) Γv -> *)
(*   lc_hty (m{Γv}h τ). *)
(* Proof. *)
(*   msubst_tac. *)
(*   apply map_Forall_insert in H2; eauto. simp_hyps. *)
(*   eauto using subst_lc_hty. *)
(* Qed. *)

Lemma td_denotation_fv: forall Γv x v_x A,
    closed_env Γv ->
    closed_value v_x ->
    x ∉ dom Γv ->
    forall α β,
      a⟦(m{Γv}a) A⟧ α β -> a⟦(m{<[x:=v_x]> Γv}a) A⟧ α β.
Proof.
  intros. rewrite_msubst_insert.
  rewrite subst_fresh_td. auto.
  select (a⟦_⟧ _ _) (fun H => apply langA_closed in H).
  simp_hyps. select (closed_td _ _) (fun H => sinvert H). my_set_solver.
  apply not_elem_of_dom. eauto.
Qed.

Lemma rtyR_msubst_insert_eq Γv ρ v x u :
  closed_env Γv ->
  closed_value u ->
  Γv !! x = None ->
  (⟦(m{ Γv }r) ρ⟧) v ->
  (⟦(m{ <[x:=u]> Γv }r) ρ⟧) v.
Proof.
  intros. rewrite_msubst_insert.
  rewrite subst_fresh_rty. auto.
  select (⟦_⟧ _) (fun H => apply rtyR_typed_closed in H).
  simp_hyps. select (closed_rty _ _) (fun H => sinvert H). my_set_solver.
Qed.

Lemma fv_of_msubst_rty_closed Γv ρ:
  closed_env Γv ->
  rty_fv (m{Γv}r ρ) = rty_fv ρ ∖ dom Γv.
Proof.
  revert Γv.
  msubst_tac.
Admitted.
(*  my_set_solver. *)
(*   rewrite fv_of_subst_rty_closed by eauto. *)
(*   rewrite dom_insert_L. my_set_solver. *)
(* Qed. *)

Lemma msubst_preserves_closed_rty Γ Γv Γ' ρ :
  ctxRst Γ Γv ->
  closed_rty (ctxdom (Γ ++ Γ')) ρ ->
  closed_rty (ctxdom (Γ')) (m{Γv}r ρ).
Proof.
  intros HΓv H.
  sinvert H.
  econstructor. eauto using msubst_lc_rty, ctxRst_lc.
  rewrite fv_of_msubst_rty_closed by eauto using ctxRst_closed_env.
  rewrite ctxdom_app_union in *.
  rewrite ctxRst_dom in * by eauto.
  my_set_solver.
Qed.

Lemma msubst_preserves_closed_rty_empty Γ Γv ρ :
  ctxRst Γ Γv ->
  closed_rty (ctxdom Γ) ρ ->
  closed_rty ∅ (m{Γv}r ρ).
Proof.
  intros. eapply msubst_preserves_closed_rty with (Γ':=[]); eauto.
  by simplify_list_eq.
Qed.

Lemma msubst_preserves_rty_measure ρ Γv:
  rty_measure ρ = rty_measure (m{Γv}r ρ).
Proof.
  msubst_tac. qauto using subst_preserves_rty_measure.
Qed.

Lemma msubst_preserves_basic_typing_tm Γ Γv :
  ctxRst Γ Γv ->
  forall Γ' e T,
    (⌊Γ⌋* ∪ Γ') ⊢t e ⋮t T ->
    Γ' ⊢t m{Γv}t e ⋮t T.
Proof.
  induction 1; intros; eauto.
  apply_eq H. cbn. apply map_empty_union.
  rewrite ctx_erase_app in H2.
  rewrite <- map_union_assoc in H2.
  apply IHctxRst in H2.
  rewrite msubst_insert;
    eauto using subst_commute_tm, ctxRst_closed_env,
                rtyR_closed_value, ctxRst_ok_insert.
  eapply basic_typing_subst_tm; cycle 1.
  eapply_eq H2.
  cbn. rewrite map_union_empty. rewrite insert_empty.
  rewrite <- insert_union_singleton_l. reflexivity.
  eapply basic_typing_weaken_value. apply map_empty_subseteq.
  apply rtyR_typed_closed in H1. simp_hyps.
  sinvert H1. apply_eq H6. eauto using rty_erase_msubst_eq.
Qed.

Lemma msubst_preserves_basic_typing_tm_empty Γ Γv :
  ctxRst Γ Γv ->
  forall e T,
    ( ⌊Γ⌋* ) ⊢t e ⋮t T ->
    ∅ ⊢t m{Γv}t e ⋮t T.
Proof.
  intros. eapply msubst_preserves_basic_typing_tm; eauto.
  rewrite map_union_empty. eauto.
Qed.

Lemma msubst_preserves_basic_typing_value Γ Γv :
  ctxRst Γ Γv ->
  forall Γ' v T,
    (⌊Γ⌋* ∪ Γ') ⊢t v ⋮v T ->
    Γ' ⊢t m{Γv}v v ⋮v T.
Proof.
  induction 1; intros; eauto.
  apply_eq H. cbn. apply map_empty_union.
  rewrite ctx_erase_app in H2.
  rewrite <- map_union_assoc in H2.
  apply IHctxRst in H2.
  rewrite msubst_insert;
    eauto using subst_commute_value, ctxRst_closed_env,
                rtyR_closed_value, ctxRst_ok_insert.
  eapply basic_typing_subst_value; cycle 1.
  eapply_eq H2.
  cbn. rewrite map_union_empty. rewrite insert_empty.
  rewrite <- insert_union_singleton_l. reflexivity.
  eapply basic_typing_weaken_value. apply map_empty_subseteq.
  apply rtyR_typed_closed in H1. simp_hyps.
  sinvert H1. apply_eq H6. eauto using rty_erase_msubst_eq.
Qed.

Lemma msubst_preserves_basic_typing_value_empty Γ Γv :
  ctxRst Γ Γv ->
  forall v T,
    ( ⌊Γ⌋* ) ⊢t v ⋮v T ->
    ∅ ⊢t m{Γv}v v ⋮v T.
Proof.
  intros. eapply msubst_preserves_basic_typing_value; eauto.
  rewrite map_union_empty. eauto.
Qed.

Lemma msubst_fvar_inv (Γv : env) v (x : atom) :
  closed_env Γv ->
  m{Γv}v v = x ->
  v = x /\ x ∉ dom Γv.
Proof.
Admitted.
(*   msubst_tac. my_set_solver. *)
(*   destruct r; simpl in H2; simplify_eq. *)
(*   case_decide; simplify_eq. exfalso. *)
(*   apply map_Forall_insert in H1; eauto. simp_hyps. *)
(*   unfold closed_value in *. *)
(*   cbn in *. qauto using non_empty_singleton. *)
(*   simp_hyps. split; eauto. subst. *)
(*   rewrite dom_insert. my_set_solver. *)
(* Qed. *)
