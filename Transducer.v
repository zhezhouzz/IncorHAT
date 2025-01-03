From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import CoreLangProp.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingProp.
From CT Require Import Qualifier.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import OperationalSemantics.
Import BasicTyping.
Import Qualifier.
Import Trace.

(** This file defines the λᴱ refinement type syntax (Fig. 4). Like λᴱ term
  syntax, the type syntax also uses locally nameless representation. *)

(** Symbolic finite automata (A, B in Fig. 4). Only a minimal set of SFAs
  relevant to metatheory are formalized. The complete set of SFAs can be
  straightforwardly added, but it is orthogonal to the formal development. *)
  (** Qualifier [ϕ] may refer to two bound variables: [bvar 1] is the argument
  variable, [bvar 0] is result variable. *)

(** The transducer supports
    - l/epsilon
    - l/id
    - l1/l2
    - T . T
    - T \/ T
    - T*
    - Ex x:b. T
 *)
Inductive transducer : Type :=
| tdLitEps (op: effop) (ϕ: qualifier)
| tdLitId (op: effop) (ϕ: qualifier)
| tdLitPair (op1: effop) (ϕ1: qualifier) (op2: effop) (ϕ2: qualifier)
| tdConcat (td1: transducer) (td2: transducer)
| tdUnion (td1: transducer) (td2: transducer)
(* | tdStar (td: transducer) *)
| tdEx (b: base_ty) (ϕ: qualifier) (td: transducer).

Notation "'⟨' op '|' ϕ '⟩/ϵ'" := (tdLitEps op ϕ) (at level 5, format "⟨ op | ϕ ⟩/ϵ", op constr, ϕ constr).
Notation "'⟨' op '|' ϕ '⟩/id'" := (tdLitId op ϕ) (at level 5, format "⟨ op | ϕ ⟩/id", op constr, ϕ constr).
Notation "'⟨' op1 '|' ϕ1 '⟩/⟨' op2 '|' ϕ2 '⟩'" := (tdLitPair op1 ϕ1 op2 ϕ2) (at level 5, format "⟨ op1 | ϕ1 ⟩/⟨ op2 | ϕ2 ⟩", op1 constr, ϕ1 constr, op2 constr, ϕ2 constr).

Notation " a ';+' b " := (tdConcat a b) (at level 5, format "a ;+ b", b constr, a constr, right associativity).

Global Hint Constructors transducer: core.

(** * Naming related definitions *)

(** free variables *)
Fixpoint td_fv a : aset :=
  match a with
  | tdLitEps _ ϕ | tdLitId _ ϕ => qualifier_fv ϕ
  | tdLitPair _ ϕ1 _ ϕ2 => qualifier_fv ϕ1 ∪ qualifier_fv ϕ2
  | tdConcat a1 a2 | tdUnion a1 a2 => td_fv a1 ∪ td_fv a2
  | tdEx _ ϕ a => qualifier_fv ϕ ∪ td_fv a
  end.

#[global]
  Instance td_stale : @Stale aset transducer := td_fv.
Arguments td_stale /.

(* The effect operator always has 2 bound variables *)
Fixpoint td_open (k: nat) (s: value) (a : transducer): transducer :=
  match a with
  | tdLitEps op ϕ => tdLitEps op (qualifier_open (S (S k)) s ϕ)
  | tdLitId op ϕ => tdLitId op (qualifier_open (S (S k)) s ϕ)
  | tdLitPair op1 ϕ1 op2 ϕ2 => tdLitPair op1 (qualifier_open (S (S k)) s ϕ1) op2 (qualifier_open (S (S k)) s ϕ2)
  | tdConcat a1 a2 => tdConcat (td_open k s a1) (td_open k s a2)
  | tdUnion a1 a2 => tdUnion (td_open k s a1) (td_open k s a2)
  | tdEx b ϕ a => tdEx b (qualifier_open (S k) s ϕ) (td_open (S k) s a)
  end.

Notation "'{' k '~a>' s '}' e" := (td_open k s e) (at level 20, k constr).
Notation "e '^a^' s" := (td_open 0 s e) (at level 20).

Fixpoint td_subst (k: atom) (s: value) (a : transducer): transducer :=
  match a with
  | tdLitEps op ϕ => tdLitEps op (qualifier_subst k s ϕ)
  | tdLitId op ϕ => tdLitId op (qualifier_subst k s ϕ)
  | tdLitPair op1 ϕ1 op2 ϕ2 => tdLitPair op1 (qualifier_subst k s ϕ1) op2 (qualifier_subst k s ϕ2)
  | tdConcat a1 a2 => tdConcat (td_subst k s a1) (td_subst k s a2)
  | tdUnion a1 a2 => tdUnion (td_subst k s a1) (td_subst k s a2)
  | tdEx b ϕ a => tdEx b (qualifier_subst k s ϕ) (td_subst k s a)
  end.

Notation "'{' x ':=' s '}a'" := (td_subst x s) (at level 20, format "{ x := s }a", x constr).

(** Local closure *)

Inductive lc_td : transducer -> Prop :=
| lc_tdLitEps: forall op ϕ, lc_phi2 ϕ -> lc_td (tdLitEps op ϕ)
| lc_tdLitId: forall op ϕ, lc_phi2 ϕ -> lc_td (tdLitId op ϕ)
| lc_tdLitPair: forall op1 ϕ1 op2 ϕ2, lc_phi2 ϕ1 -> lc_phi2 ϕ2 -> lc_td (tdLitPair op1 ϕ1 op2 ϕ2)
| lc_tdConcat : forall a1 a2, lc_td a1 -> lc_td a2 -> lc_td (tdConcat a1 a2)
| lc_tdUnion : forall a1 a2, lc_td a1 -> lc_td a2 -> lc_td (tdUnion a1 a2)
| lc_tdEx : forall b ϕ a (L : aset), lc_phi1 ϕ -> (forall x : atom, x ∉ L -> lc_td (a ^a^ x)) -> lc_td (tdEx b ϕ a)
.

(** Closed under free variable set *)

Inductive closed_td (d: aset) (a: transducer): Prop :=
| closed_td_: lc_td a -> td_fv a ⊆ d -> closed_td d a.

