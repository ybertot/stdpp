(* Copyright (c) 2012-2019, Coq-std++ developers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Export fin_collections.
From stdpp Require Import pretty relations.

(** The class [Infinite] axiomatizes types with infinitely many elements
by giving an injection from the natural numbers into the type. It is mostly
used to provide a generic [fresh] algorithm. *)
Class Infinite A := {
  inject: nat → A;
  inject_injective :> Inj (=) (=) inject;
}.

(** Instances *)
Program Definition inj_infinite `{Infinite A} {B} (f : A → B) `{!Inj (=) (=) f} :
  Infinite B := {| inject := f ∘ inject |}.

Instance string_infinite: Infinite string := {| inject := λ x, "~" +:+ pretty x |}.
Instance nat_infinite: Infinite nat := {| inject := id |}.
Instance N_infinite: Infinite N := {| inject_injective := Nat2N.inj |}.
Instance positive_infinite: Infinite positive := {| inject_injective := SuccNat2Pos.inj |}.
Instance Z_infinite: Infinite Z := {| inject_injective := Nat2Z.inj |}.

Instance option_infinite `{Infinite A} : Infinite (option A) := inj_infinite Some.
Instance sum_infinite_l `{Infinite A} {B} : Infinite (A + B) := inj_infinite inl.
Instance sum_infinite_r {A} `{Infinite B} : Infinite (A + B) := inj_infinite inr.
Instance prod_infinite_l `{Infinite A, Inhabited B} : Infinite (A * B) :=
  inj_infinite (,inhabitant).
Instance prod_infinite_r `{Inhabited A, Infinite B} : Infinite (A * B) :=
  inj_infinite (inhabitant,).

Program Instance list_infinite `{Inhabited A}: Infinite (list A) :=
  {| inject := λ i, replicate i inhabitant |}.
Next Obligation.
  intros A * i j Heqrep%(f_equal length).
  rewrite !replicate_length in Heqrep; done.
Qed.

(** * Fresh elements *)
(** We do not make [fresh_generic] an instance because it leads to overlap. For
various set implementations, e.g. [Pset] and [natset], we have an efficient
implementation of [Fresh], which should always be used. Only for specific set
implementations like [gset], which are not meant to be computationally
efficient in the first place, we make [fresh_generic] an instance.

Since [fresh_generic] is too inefficient for all practical purposes, we seal
off its definition. That way, Coq will not accidentally unfold it during
unification or other tactics. *)
Section fresh_generic.
  Context `{FinCollection A C, Infinite A, !RelDecision (∈@{C})}.

  Definition fresh_generic_body (s : C) (rec : ∀ s', s' ⊂ s → nat → A) (n : nat) : A :=
    let cand := inject n in
    match decide (cand ∈ s) with
    | left H => rec _ (subset_difference_elem_of H) (S n)
    | right _ => cand
    end.

  Definition fresh_generic_fix_aux :
    seal (Fix collection_wf (const (nat → A)) fresh_generic_body). by eexists. Qed.
  Definition fresh_generic_fix := fresh_generic_fix_aux.(unseal).

  Lemma fresh_generic_fixpoint_unfold s n:
    fresh_generic_fix s n = fresh_generic_body s (λ s' _, fresh_generic_fix s') n.
  Proof.
    unfold fresh_generic_fix. rewrite fresh_generic_fix_aux.(seal_eq).
    refine (Fix_unfold_rel _ _ (const (pointwise_relation nat (=))) _ _ s n).
    intros s' f g Hfg i. unfold fresh_generic_body. case_decide; naive_solver.
  Qed.

  Lemma fresh_generic_fixpoint_spec s n :
    ∃ m, n ≤ m ∧ fresh_generic_fix s n = inject m ∧ inject m ∉ s ∧
         ∀ i, n ≤ i < m → inject i ∈ s.
  Proof.
    revert n.
    induction s as [s IH] using (well_founded_ind collection_wf); intros n.
    setoid_rewrite fresh_generic_fixpoint_unfold; unfold fresh_generic_body.
    destruct decide as [Hcase|Hcase]; [|by eauto with lia].
    destruct (IH _ (subset_difference_elem_of Hcase) (S n))
      as (m & Hmbound & Heqfix & Hnotin & Hinbelow).
    exists m; repeat split; auto with lia.
    - rewrite not_elem_of_difference, elem_of_singleton in Hnotin.
      destruct Hnotin as [?|?%inject_injective]; auto with lia.
    - intros i Hibound.
      destruct (decide (i = n)) as [<-|Hneq]; [by auto|].
      assert (inject i ∈ s ∖ {[inject n]}) by auto with lia.
      set_solver.
  Qed.

  Instance fresh_generic : Fresh A C := λ s, fresh_generic_fix s 0.

  Instance fresh_generic_spec : FreshSpec A C.
  Proof.
    split.
    - apply _.
    - intros X Y HeqXY. unfold fresh, fresh_generic.
      destruct (fresh_generic_fixpoint_spec X 0)
        as (mX & _ & -> & HnotinX & HbelowinX).
      destruct (fresh_generic_fixpoint_spec Y 0)
        as (mY & _ & -> & HnotinY & HbelowinY).
      destruct (Nat.lt_trichotomy mX mY) as [case|[->|case]]; auto.
      + contradict HnotinX. rewrite HeqXY. apply HbelowinY; lia.
      + contradict HnotinY. rewrite <-HeqXY. apply HbelowinX; lia.
    - intros X. unfold fresh, fresh_generic.
      destruct (fresh_generic_fixpoint_spec X 0)
        as (m & _ & -> & HnotinX & HbelowinX); auto.
  Qed.
End fresh_generic.
