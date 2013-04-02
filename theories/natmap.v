(* Copyright (c) 2012-2013, Robbert Krebbers. *)
(* This file is distributed under the terms of the BSD license. *)
(** This files implements finite maps whose keys range over Coq's data type of
unary natural numbers [nat]. *)
Require Import fin_maps.

Notation natmap_raw A := (list (option A)).
Definition natmap_wf {A} (l : natmap_raw A) :=
  match last l with
  | None => True
  | Some x => is_Some x
  end.
Instance natmap_wf_pi {A} (l : natmap_raw A) : ProofIrrel (natmap_wf l).
Proof. unfold natmap_wf. case_match; apply _. Qed.

Lemma natmap_wf_inv {A} (o : option A) (l : natmap_raw A)  :
  natmap_wf (o :: l) → natmap_wf l.
Proof. by destruct l. Qed.
Lemma natmap_wf_lookup {A} (l : natmap_raw A) :
  natmap_wf l → l ≠ [] → ∃ i x, mjoin (l !! i) = Some x.
Proof.
  intros Hwf Hl. induction l as [|[x|] l IH]; simpl.
  * done.
  * exists 0. simpl. eauto.
  * destruct IH as (i&x&?); eauto using natmap_wf_inv.
    { intro. subst. inversion Hwf. }
    by exists (S i) x.
Qed.

Definition natmap (A : Type) : Type := sig (@natmap_wf A).

Instance natmap_empty {A} : Empty (natmap A) := [] ↾ I.
Instance natmap_lookup {A} : Lookup nat A (natmap A) :=
  λ i m, mjoin (`m !! i).

Fixpoint natmap_singleton_raw {A} (i : nat) (x : A) : natmap_raw A :=
  match i with
  | 0 => [Some x]
  | S i => None :: natmap_singleton_raw i x
  end.
Lemma natmap_singleton_wf {A} (i : nat) (x : A) :
  natmap_wf (natmap_singleton_raw i x).
Proof.
  unfold natmap_wf, last.
  induction i as [|i]; simpl; repeat case_match; simplify_equality; eauto.
  by destruct i.
Qed.
Lemma natmap_lookup_singleton_raw {A} (i : nat) (x : A) :
  mjoin (natmap_singleton_raw i x !! i) = Some x.
Proof. induction i; simpl; auto. Qed.
Lemma natmap_lookup_singleton_raw_ne {A} (i j : nat) (x : A) :
  i ≠ j → mjoin (natmap_singleton_raw i x !! j) = None.
Proof. revert j; induction i; intros [|?]; simpl; auto with congruence. Qed.
Hint Rewrite @natmap_lookup_singleton_raw : natmap.

Definition natmap_cons_canon {A} (o : option A) (l : natmap_raw A) :=
  match o, l with
  | None, [] => []
  | _, _ => o :: l
  end.
Lemma natmap_cons_canon_wf {A} (o : option A) (l : natmap_raw A) :
  natmap_wf l → natmap_wf (natmap_cons_canon o l).
Proof. unfold natmap_wf, last. destruct o, l; simpl; eauto. Qed.
Lemma natmap_cons_canon_O {A} (o : option A) (l : natmap_raw A) :
  mjoin (natmap_cons_canon o l !! 0) = o.
Proof. by destruct o, l. Qed.
Lemma natmap_cons_canon_S {A} (o : option A) (l : natmap_raw A) i :
  natmap_cons_canon o l !! S i = l !! i.
Proof. by destruct o, l. Qed.
Hint Rewrite @natmap_cons_canon_O @natmap_cons_canon_S : natmap.

Definition natmap_alter_raw {A} (f : option A → option A) :
    nat → natmap_raw A → natmap_raw A :=
  fix go i l {struct l} :=
  match l with
  | [] =>
     match f None with
     | Some x => natmap_singleton_raw i x
     | None => []
     end
  | o :: l =>
     match i with
     | 0 => natmap_cons_canon (f o) l
     | S i => natmap_cons_canon o (go i l)
     end
  end.
Lemma natmap_alter_wf {A} (f : option A → option A) i l :
  natmap_wf l → natmap_wf (natmap_alter_raw f i l).
Proof.
  revert i. induction l; [intro | intros [|?]]; simpl; repeat case_match;
    eauto using natmap_singleton_wf, natmap_cons_canon_wf, natmap_wf_inv.
Qed.
Instance natmap_alter {A} : PartialAlter nat A (natmap A) := λ f i m,
  natmap_alter_raw f i (`m)↾natmap_alter_wf _ _ _ (proj2_sig m).
Lemma natmap_lookup_alter_raw {A} (f : option A → option A) i l :
  mjoin (natmap_alter_raw f i l !! i) = f (mjoin (l !! i)).
Proof.
  revert i. induction l; intros [|?]; simpl; repeat case_match; simpl;
    autorewrite with natmap; auto.
Qed.
Lemma natmap_lookup_alter_raw_ne {A} (f : option A → option A) i j l :
  i ≠ j → mjoin (natmap_alter_raw f i l !! j) = mjoin (l !! j).
Proof.
  revert i j. induction l; intros [|?] [|?] ?; simpl;
    repeat case_match; simpl; autorewrite with natmap; auto with congruence.
  rewrite natmap_lookup_singleton_raw_ne; congruence.
Qed.

Definition natmap_merge_aux {A B} (f : option A → option B) :
    natmap_raw A → natmap_raw B :=
  fix go l :=
  match l with
  | [] => []
  | o :: l => natmap_cons_canon (f o) (go l)
  end.
Lemma natmap_merge_aux_wf {A B} (f : option A → option B) l :
  natmap_wf l → natmap_wf (natmap_merge_aux f l).
Proof. induction l; simpl; eauto using natmap_cons_canon_wf, natmap_wf_inv. Qed.
Lemma natmap_lookup_merge_aux {A B} (f : option A → option B) l i :
  f None = None →
  mjoin (natmap_merge_aux f l !! i) = f (mjoin (l !! i)).
Proof.
  revert i. induction l; intros [|?]; simpl; autorewrite with natmap; auto.
Qed.
Hint Rewrite @natmap_lookup_merge_aux : natmap.

Definition natmap_merge_raw {A B C} (f : option A → option B → option C) :
    natmap_raw A → natmap_raw B → natmap_raw C :=
  fix go l1 l2 :=
  match l1, l2 with
  | [], l2 => natmap_merge_aux (f None) l2
  | l1, [] => natmap_merge_aux (flip f None) l1
  | o1 :: l1, o2 :: l2 => natmap_cons_canon (f o1 o2) (go l1 l2)
  end.
Lemma natmap_merge_wf {A B C} (f : option A → option B → option C) l1 l2 :
  natmap_wf l1 → natmap_wf l2 → natmap_wf (natmap_merge_raw f l1 l2).
Proof.
  revert l2. induction l1; intros [|??]; simpl;
    eauto using natmap_merge_aux_wf, natmap_cons_canon_wf, natmap_wf_inv.
Qed.
Lemma natmap_lookup_merge_raw {A B C} (f : option A → option B → option C) l1 l2 i :
  f None None = None →
  mjoin (natmap_merge_raw f l1 l2 !! i) = f (mjoin (l1 !! i)) (mjoin (l2 !! i)).
Proof.
  intros. revert i l2. induction l1; intros [|?] [|??]; simpl;
    autorewrite with natmap; auto.
Qed.
Instance natmap_merge: Merge natmap := λ A B C f m1 m2,
  natmap_merge_raw f _ _ ↾ natmap_merge_wf _ _ _ (proj2_sig m1) (proj2_sig m2).

Fixpoint natmap_to_list_raw {A} (i : nat) (l : natmap_raw A) : list (nat * A) :=
  match l with
  | [] => []
  | None :: l => natmap_to_list_raw (S i) l
  | Some x :: l => (i,x) :: natmap_to_list_raw (S i) l
  end.
Lemma natmap_elem_of_to_list_raw_aux {A} j (l : natmap_raw A) i x :
  (i,x) ∈ natmap_to_list_raw j l ↔ ∃ i', i = i' + j ∧ mjoin (l !! i') = Some x.
Proof.
  split.
  * revert j. induction l as [|[y|] l IH]; intros j; simpl.
    + by rewrite elem_of_nil.
    + rewrite elem_of_cons. intros [?|?]; simplify_equality.
      - by exists 0.
      - destruct (IH (S j)) as (i'&?&?); auto.
        exists (S i'); simpl; auto with lia.
    + intros. destruct (IH (S j)) as (i'&?&?); auto.
      exists (S i'); simpl; auto with lia.
  * intros (i'&?&Hi'). subst. revert i' j Hi'.
    induction l as [|[y|] l IH]; intros i j ?; simpl.
    + done.
    + destruct i as [|i]; simplify_equality; [left|].
      right. rewrite NPeano.Nat.add_succ_comm. by apply (IH i (S j)).
    + destruct i as [|i]; simplify_equality.
      rewrite NPeano.Nat.add_succ_comm. by apply (IH i (S j)).
Qed.
Lemma natmap_elem_of_to_list_raw {A} (l : natmap_raw A) i x :
  (i,x) ∈ natmap_to_list_raw 0 l ↔ mjoin (l !! i) = Some x.
Proof.
  rewrite natmap_elem_of_to_list_raw_aux. setoid_rewrite plus_0_r. naive_solver.
Qed.
Lemma natmap_to_list_raw_nodup {A} i (l : natmap_raw A) :
  NoDup (natmap_to_list_raw i l).
Proof.
  revert i. induction l as [|[?|] ? IH]; simpl; try constructor; auto.
  rewrite natmap_elem_of_to_list_raw_aux. intros (?&?&?). lia.
Qed.
Instance natmap_to_list {A} : FinMapToList nat A (natmap A) := λ m,
  natmap_to_list_raw 0 (`m).

Definition natmap_map_raw {A B} (f : A → B) : natmap_raw A → natmap_raw B :=
  fmap (fmap f).
Lemma natmap_map_wf {A B} (f : A → B) l :
  natmap_wf l → natmap_wf (natmap_map_raw f l).
Proof.
  unfold natmap_wf, last.
  induction l; simpl; repeat case_match; simplify_equality; eauto.
  simpl. by rewrite fmap_is_Some.
Qed.
Lemma natmap_lookup_map_raw {A B} (f : A → B) i l :
  mjoin (natmap_map_raw f l !! i) = f <$> mjoin (l !! i).
Proof. unfold natmap_map_raw. rewrite list_lookup_fmap. by destruct (l !! i). Qed.
Instance natmap_map: FMap natmap := λ A B f m,
  natmap_map_raw f _ ↾ natmap_map_wf _ _ (proj2_sig m).

Instance: FinMap nat natmap.
Proof.
  split.
  * unfold lookup, natmap_lookup. intros A [l1 Hl1] [l2 Hl2] E.
    apply (sig_eq_pi _). revert l2 Hl1 Hl2 E. simpl.
    induction l1 as [|[x|] l1 IH]; intros [|[y|] l2] Hl1 Hl2 E; simpl in *.
    + done.
    + by specialize (E 0).
    + destruct (natmap_wf_lookup (None :: l2)) as [i [??]]; auto with congruence.
    + by specialize (E 0).
    + f_equal. apply (E 0). apply IH; eauto using natmap_wf_inv.
      intros i. apply (E (S i)).
    + by specialize (E 0).
    + destruct (natmap_wf_lookup (None :: l1)) as [i [??]]; auto with congruence.
    + by specialize (E 0).
    + f_equal. apply IH; eauto using natmap_wf_inv.
      intros i. apply (E (S i)).
  * done.
  * intros ?? [??] ?. apply natmap_lookup_alter_raw.
  * intros ?? [??] ??. apply natmap_lookup_alter_raw_ne.
  * intros ??? [??] ?. apply natmap_lookup_map_raw.
  * intros ? [??]. by apply natmap_to_list_raw_nodup.
  * intros ? [??] ??. by apply natmap_elem_of_to_list_raw.
  * intros ????? [??] [??] ?. by apply natmap_lookup_merge_raw.
Qed.