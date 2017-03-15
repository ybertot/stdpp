(* Copyright (c) 2012-2017, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This file collects general purpose definitions and theorems on the fin type
(bounded naturals). It uses the definitions from the standard library, but
renames or changes their notations, so that it becomes more consistent with the
naming conventions in this development. *)
From stdpp Require Export base tactics.
Set Default Proof Using "Type".

(** * The fin type *)
(** The type [fin n] represents natural numbers [i] with [0 ≤ i < n]. We
define a scope [fin], in which we declare notations for small literals of the
[fin] type. Whereas the standard library starts counting at [1], we start
counting at [0]. This way, the embedding [fin_to_nat] preserves [0], and allows
us to define [fin_to_nat] as a coercion without introducing notational
ambiguity. *)
Notation fin := Fin.t.
Notation FS := Fin.FS.

Delimit Scope fin_scope with fin.
Arguments Fin.FS _ _%fin.

Notation "0" := Fin.F1 : fin_scope. Notation "1" := (FS 0) : fin_scope.
Notation "2" := (FS 1) : fin_scope. Notation "3" := (FS 2) : fin_scope.
Notation "4" := (FS 3) : fin_scope. Notation "5" := (FS 4) : fin_scope.
Notation "6" := (FS 5) : fin_scope. Notation "7" := (FS 6) : fin_scope.
Notation "8" := (FS 7) : fin_scope. Notation "9" := (FS 8) : fin_scope.
Notation "10" := (FS 9) : fin_scope.

Fixpoint fin_to_nat {n} (i : fin n) : nat :=
  match i with 0%fin => 0 | FS _ i => S (fin_to_nat i) end.
Coercion fin_to_nat : fin >-> nat.

Notation fin_of_nat := Fin.of_nat_lt.
Notation fin_rect2 := Fin.rect2.

Instance fin_dec {n} : EqDecision (fin n).
Proof.
 refine (fin_rect2
  (λ n (i j : fin n), { i = j } + { i ≠ j })
  (λ _, left _)
  (λ _ _, right _)
  (λ _ _, right _)
  (λ _ _ _ H, cast_if H));
  abstract (f_equal; by auto using Fin.FS_inj).
Defined.

(** The inversion principle [fin_S_inv] is more convenient than its variant
[Fin.caseS] in the standard library, as we keep the parameter [n] fixed.
In the tactic [inv_fin i] to perform dependent case analysis on [i], we
therefore do not have to generalize over the index [n] and all assumptions
depending on it. Notice that contrary to [dependent destruction], which uses
the [JMeq_eq] axiom, the tactic [inv_fin] produces axiom free proofs.*)
Notation fin_0_inv := Fin.case0.

Definition fin_S_inv {n} (P : fin (S n) → Type)
  (H0 : P 0%fin) (HS : ∀ i, P (FS i)) (i : fin (S n)) : P i.
Proof.
  revert P H0 HS.
  refine match i with 0%fin => λ _ H0 _, H0 | FS _ i => λ _ _ HS, HS i end.
Defined.

Ltac inv_fin i :=
  let T := type of i in
  match eval hnf in T with
  | fin ?n =>
    match eval hnf in n with
    | 0 =>
      revert dependent i; match goal with |- ∀ i, @?P i => apply (fin_0_inv P) end
    | S ?n =>
      revert dependent i; match goal with |- ∀ i, @?P i => apply (fin_S_inv P) end
    end
  end.

Instance FS_inj: Inj (=) (=) (@FS n).
Proof. intros n i j. apply Fin.FS_inj. Qed.
Instance fin_to_nat_inj : Inj (=) (=) (@fin_to_nat n).
Proof.
  intros n i. induction i; intros j; inv_fin j; intros; f_equal/=; auto with lia.
Qed.

Lemma fin_to_nat_lt {n} (i : fin n) : fin_to_nat i < n.
Proof. induction i; simpl; lia. Qed.
Lemma fin_to_of_nat n m (H : n < m) : fin_to_nat (fin_of_nat H) = n.
Proof.
  revert m H. induction n; intros [|?]; simpl; auto; intros; exfalso; lia.
Qed.
Lemma fin_of_to_nat {n} (i : fin n) H : @fin_of_nat (fin_to_nat i) n H = i.
Proof. apply (inj fin_to_nat), fin_to_of_nat. Qed.

Fixpoint fin_plus_inv {n1 n2} : ∀ (P : fin (n1 + n2) → Type)
    (H1 : ∀ i1 : fin n1, P (Fin.L n2 i1))
    (H2 : ∀ i2, P (Fin.R n1 i2)) (i : fin (n1 + n2)), P i :=
  match n1 with
  | 0 => λ P H1 H2 i, H2 i
  | S n => λ P H1 H2, fin_S_inv P (H1 0%fin) (fin_plus_inv _ (λ i, H1 (FS i)) H2)
  end.

Lemma fin_plus_inv_L {n1 n2} (P : fin (n1 + n2) → Type)
    (H1: ∀ i1 : fin n1, P (Fin.L _ i1)) (H2: ∀ i2, P (Fin.R _ i2)) (i: fin n1) :
  fin_plus_inv P H1 H2 (Fin.L n2 i) = H1 i.
Proof.
  revert P H1 H2 i.
  induction n1 as [|n1 IH]; intros P H1 H2 i; inv_fin i; simpl; auto.
  intros i. apply (IH (λ i, P (FS i))).
Qed.

Lemma fin_plus_inv_R {n1 n2} (P : fin (n1 + n2) → Type)
    (H1: ∀ i1 : fin n1, P (Fin.L _ i1)) (H2: ∀ i2, P (Fin.R _ i2)) (i: fin n2) :
  fin_plus_inv P H1 H2 (Fin.R n1 i) = H2 i.
Proof.
  revert P H1 H2 i; induction n1 as [|n1 IH]; intros P H1 H2 i; simpl; auto.
  apply (IH (λ i, P (FS i))).
Qed.
