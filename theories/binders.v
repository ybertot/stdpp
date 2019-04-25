(* Copyright (c) 2012-2019, Coq-std++ developers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file implements a type [binder] with elements [BAnon] for the
anonymous binder, and [BNamed] for named binders. This type is isomorphic to
[option string], but we use a special type so that we can define [BNamed] as
a coercion.

This library is used in various Iris developments, like heap-lang, LambdaRust,
Iron, Fairis. *)
From stdpp Require Export strings.
From stdpp Require Import sets countable finite.

Inductive binder := BAnon | BNamed :> string → binder.
Bind Scope binder_scope with binder.
Delimit Scope binder_scope with binder.
Notation "<>" := BAnon : binder_scope.

Instance binder_dec_eq : EqDecision binder.
Proof. solve_decision. Defined.
Instance binder_inhabited : Inhabited binder := populate BAnon.
Instance binder_countable : Countable binder.
Proof.
 refine (inj_countable'
   (λ mx, match mx with BAnon => None | BNamed x => Some x end)
   (λ mx, match mx with None => BAnon | Some x => BNamed x end) _); by intros [].
Qed.

(** The functions [cons_binder mx X] and [app_binder mxs X] are typically used
to collect the free variables of an expression. Here [X] is the current list of
free variables, and [mx], respectively [mxs], are the binders that are being
added. *)
Definition cons_binder (mx : binder) (X : list string) : list string :=
  match mx with BAnon => X | BNamed x => x :: X end.
Infix ":b:" := cons_binder (at level 60, right associativity).
Fixpoint app_binder (mxs : list binder) (X : list string) : list string :=
  match mxs with [] => X | b :: mxs => b :b: app_binder mxs X end.
Infix "+b+" := app_binder (at level 60, right associativity).

Instance set_unfold_cons_binder x mx X P :
  SetUnfoldElemOf x X P → SetUnfoldElemOf x (mx :b: X) (BNamed x = mx ∨ P).
Proof.
  constructor. rewrite <-(set_unfold (x ∈ X) P).
  destruct mx; simpl; rewrite ?elem_of_cons; naive_solver.
Qed.
Instance set_unfold_app_binder x mxl X P :
  SetUnfoldElemOf x X P → SetUnfoldElemOf x (mxl +b+ X) (BNamed x ∈ mxl ∨ P).
Proof.
  constructor. rewrite <-(set_unfold (x ∈ X) P). induction mxl; set_solver.
Qed.
