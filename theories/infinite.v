(* Copyright (c) 2012-2017, Coq-std++ developers. *)
(* This file is distributed under the terms of the BSD license. *)
From stdpp Require Import pretty fin_collections.

(** The class [Infinite] axiomatizes types with infinitely many elements
by giving an injection from the natural numbers into the type. It is mostly
used to provide a generic [fresh] algorithm. *)
Class Infinite A :=
  { inject: nat → A;
    inject_injective:> Inj (=) (=) inject }.

Instance string_infinite: Infinite string := {| inject := λ x, "~" +:+ pretty x |}.
Instance nat_infinite: Infinite nat := {| inject := id |}.
Instance N_infinite: Infinite N := {| inject_injective := Nat2N.inj |}.
Instance pos_infinite: Infinite positive := {| inject_injective := SuccNat2Pos.inj |}.
Instance Z_infinite: Infinite Z := {| inject_injective := Nat2Z.inj |}.
Instance option_infinite `{Infinite A}: Infinite (option A) := {| inject := Some ∘ inject |}.
Program Instance list_infinite `{Inhabited A}: Infinite (list A) :=
  {| inject := λ i, replicate i inhabitant |}.
Next Obligation.
Proof.
  intros * i j eqrep%(f_equal length).
  rewrite !replicate_length in eqrep; done.
Qed.

(** * Fresh elements *)
Section Fresh.
  Context `{Infinite A, ∀ (x: A) (s: C), Decision (x ∈ s)}.

  Lemma subset_difference_in {x: A} {s: C} (inx: x ∈ s): s ∖ {[ x ]} ⊂ s.
  Proof. set_solver. Qed.

  Definition fresh_generic_body (s: C) (rec: ∀ s', s' ⊂ s → nat → A) (n: nat) :=
    let cand := inject n in
    match decide (cand ∈ s) with
    | left H => rec _ (subset_difference_in H) (S n)
    | right _ => cand
    end.
  Lemma fresh_generic_body_proper s (f g: ∀ y, y ⊂ s → nat → A):
    (∀ y Hy Hy', pointwise_relation nat eq (f y Hy) (g y Hy')) →
    pointwise_relation nat eq (fresh_generic_body s f) (fresh_generic_body s g).
  Proof.
    intros relfg i.
    unfold fresh_generic_body.
    destruct decide.
    2: done.
    apply relfg.
  Qed.

  Definition fresh_generic_fix := Fix collection_wf (const (nat → A)) fresh_generic_body.

  Lemma fresh_generic_fixpoint_unfold s n:
    fresh_generic_fix s n = fresh_generic_body s (λ s' _ n, fresh_generic_fix s' n) n.
  Proof.
    apply (Fix_unfold_rel collection_wf (const (nat → A)) (const (pointwise_relation nat (=)))
                          fresh_generic_body fresh_generic_body_proper s n).
  Qed.

  Lemma fresh_generic_fixpoint_spec s n:
    ∃ m, n ≤ m ∧ fresh_generic_fix s n = inject m ∧ inject m ∉ s ∧ ∀ i, n ≤ i < m → inject i ∈ s.
  Proof.
    revert n.
    induction s as [s IH] using (well_founded_ind collection_wf); intro.
    setoid_rewrite fresh_generic_fixpoint_unfold; unfold fresh_generic_body.
    destruct decide as [case|case].
    - destruct (IH _ (subset_difference_in case) (S n)) as [m [mbound [eqfix [notin inbelow]]]].
      exists m; repeat split; auto.
      + omega.
      + rewrite not_elem_of_difference, elem_of_singleton in notin.
        destruct notin as [?|?%inject_injective]; auto; omega.
      + intros i ibound.
        destruct (decide (i = n)) as [<-|neq]; auto.
        enough (inject i ∈ s ∖ {[inject n]}) by set_solver.
        apply inbelow; omega.
    - exists n; repeat split; auto.
      intros; omega.
  Qed.

  Instance fresh_generic: Fresh A C | 20 := λ s, fresh_generic_fix s 0.

  Instance fresh_generic_spec: FreshSpec A C.
  Proof.
    split.
    - apply _.
    - intros * eqXY.
      unfold fresh, fresh_generic.
      destruct (fresh_generic_fixpoint_spec X 0) as [mX [_ [-> [notinX belowinX]]]].
      destruct (fresh_generic_fixpoint_spec Y 0) as [mY [_ [-> [notinY belowinY]]]].
      destruct (Nat.lt_trichotomy mX mY) as [case|[->|case]]; auto.
      + contradict notinX; rewrite eqXY; apply belowinY; omega.
      + contradict notinY; rewrite <- eqXY; apply belowinX; omega.
    - intro.
      unfold fresh, fresh_generic.
      destruct (fresh_generic_fixpoint_spec X 0) as [m [_ [-> [notinX belowinX]]]]; auto.
  Qed.
End Fresh.

(** Derive fresh instances. *)
Section StringFresh.
  Context `{FinCollection string C, ∀ (x: string) (s: C), Decision (x ∈ s)}.
  Global Instance string_fresh: Fresh string C := fresh_generic.
  Global Instance string_fresh_spec: FreshSpec string C := _.
End StringFresh.
