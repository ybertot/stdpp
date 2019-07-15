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
   (λ b, match b with BAnon => None | BNamed s => Some s end)
   (λ b, match b with None => BAnon | Some s => BNamed s end) _); by intros [].
Qed.

(** The functions [cons_binder b ss] and [app_binder bs ss] are typically used
to collect the free variables of an expression. Here [ss] is the current list of
free variables, and [b], respectively [bs], are the binders that are being
added. *)
Definition cons_binder (b : binder) (ss : list string) : list string :=
  match b with BAnon => ss | BNamed s => s :: ss end.
Infix ":b:" := cons_binder (at level 60, right associativity).
Fixpoint app_binder (bs : list binder) (ss : list string) : list string :=
  match bs with [] => ss | b :: bs => b :b: app_binder bs ss end.
Infix "+b+" := app_binder (at level 60, right associativity).

Instance set_unfold_cons_binder s b ss P :
  SetUnfoldElemOf s ss P → SetUnfoldElemOf s (b :b: ss) (BNamed s = b ∨ P).
Proof.
  constructor. rewrite <-(set_unfold (s ∈ ss) P).
  destruct b; simpl; rewrite ?elem_of_cons; naive_solver.
Qed.
Instance set_unfold_app_binder s bs ss P Q :
  SetUnfoldElemOf (BNamed s) bs P → SetUnfoldElemOf s ss Q →
  SetUnfoldElemOf s (bs +b+ ss) (P ∨ Q).
Proof.
  intros HinP HinQ.
  constructor. rewrite <-(set_unfold (s ∈ ss) Q), <-(set_unfold (BNamed s ∈ bs) P).
  clear HinP HinQ.
  induction bs; set_solver.
Qed.

Lemma app_binder_named ss1 ss2 : (BNamed <$> ss1) +b+ ss2 = ss1 ++ ss2.
Proof. induction ss1; by f_equal/=. Qed.

Lemma app_binder_snoc bs s ss : bs +b+ (s :: ss) = (bs ++ [BNamed s]) +b+ ss.
Proof. induction bs; by f_equal/=. Qed.

Instance cons_binder_Permutation b : Proper ((≡ₚ) ==> (≡ₚ)) (cons_binder b).
Proof. intros ss1 ss2 Hss. destruct b; csimpl; by rewrite Hss. Qed.

Instance app_binder_Permutation : Proper ((≡ₚ) ==> (≡ₚ) ==> (≡ₚ)) app_binder.
Proof.
  assert (∀ bs, Proper ((≡ₚ) ==> (≡ₚ)) (app_binder bs)).
  { induction bs as [|[]]; intros ss1 ss2; simpl; by intros ->. }
  induction 1 as [|[]|[] []|]; intros ss1 ss2 Hss; simpl;
    first [by eauto using perm_trans|by rewrite 1?perm_swap, Hss].
Qed.
