From stdpp Require Import mapset.
From CT Require Import Tactics.
From CT Require Import CoreLang.
From CT Require Import CoreLangProp.
Import CoreLang.
Import Tactics.
Import NamelessTactics.
Import Lists.List.

(** This file defines the syntax of traces and the trace reduction relation. *)

(** * Trace syntax *)

(** A single effect event *)
Inductive evop : Type :=
| evop_ (op: effop) (argv: constant) (retv: constant).

Notation " 'ev{' op '~' v1 ':=' v2 '}' " := (evop_ op v1 v2)
                                        (at level 20, format "ev{ op ~ v1 := v2 }",
                                          op constr, v1 constr, v2 constr, right associativity).

(** A trace is a list of effect events (α in Fig. 3). *)
Definition trace : Type := list evop.

Inductive read_reduction : trace -> constant -> Prop :=
| ReadRead: forall (α: trace) (n' n: nat), read_reduction (α ++ [ev{ op_read ~ n' := n }]) n
| WriteRead: forall (α: trace) (n: nat), read_reduction (α ++ [ev{ op_write ~ n := true }]) n
| ElseRead: forall (α: trace) op c c' (n: nat),
    op <> op_read ->
    (op <> op_write \/ c' = false) ->
    read_reduction α n -> read_reduction (α ++ [ev{ op ~ c := c' }]) n.

(** Trace reduction relation. Used in the premise of [STEffOp]. *)
Inductive tr_reduction : trace -> effop -> constant -> trace -> constant -> Prop :=
| TrPlus1: forall (α: trace) (n: nat), tr_reduction α op_plus_one n α (S n)
| TrMinus1: forall (α: trace) (n: nat), tr_reduction α op_minus_one (S n) α n
| TrEq0_0: forall (α: trace), tr_reduction α op_eq_zero 0 α true
| TrEq0_S: forall (α: trace) (n: nat), tr_reduction α op_eq_zero (S n) α false
| TrNatGen: forall (α: trace) (n: nat) (n': nat), tr_reduction α op_rannat n α n'
| TrBoolGen: forall (α: trace) (n: nat) (b: bool), tr_reduction α op_ranbool n α b
| TrWrite: forall (α: trace) (n: nat) (b: bool),
    tr_reduction α op_write n (α ++ [ev{ op_write ~ n := b }]) b
| TrRead: forall (α: trace) (n' n: nat),
    read_reduction α n -> tr_reduction α op_read n' (α ++ [ev{ op_read ~ n' := n }]) n.

Notation "α '⊧{' op '~' c1 '}⇓{' β '}{' c '}' " := (tr_reduction α op c1 β c)
                                                     (at level 30, format "α ⊧{ op ~ c1 }⇓{ β }{ c }", c1 constr, α constr, β constr).
