From stdpp Require Import mapset.
From stdpp Require Import natmap.
From CT Require Import CoreLangClass.
From CT Require Import OperationalSemantics.
From CT Require Import BasicTypingClass.
From CT Require Import QualifierClass.

Import Atom.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import OperationalSemantics.
Import BasicTyping.
Import Qualifier.

(** Symbolic finite automata (A, B in Fig. 4). Only a minimal set of SFAs
  relevant to metatheory are formalized. The complete set of SFAs can be
  straightforwardly added, but it is orthogonal to the formal development. *)
Inductive am : Type :=
(** Qualifier [ϕ] may refer to two bound variables: [bvar 1] is the argument
  variable, [bvar 0] is result variable. *)
| aevent (op: effop) (ϕ: qualifier)
(* □⟨⊤⟩ in the paper, directly encoded as a primitive operator here for
convenience. *)
| aany
| aconcat (a: am) (b: am)
(* We only need the operations above for metatheory. Other connectives or
modality can be straightforwardly added, but not interesting. *)
| aunion (a: am) (b: am)
.

Inductive rty : Type :=
| overrty (b: base_ty) (ϕ: qualifier)
| underrty (b: base_ty) (ϕ: qualifier)
| arrrty (ρ: rty) (τ: rty).
