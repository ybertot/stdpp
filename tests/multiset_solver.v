From stdpp Require Import gmultiset.

Section test.
  Context `{Countable A}.
  Implicit Types x y : A.
  Implicit Types X Y : gmultiset A.

  Lemma test1 x y X : {[x]} ⊎ ({[y]} ⊎ X) ≠ ∅.
  Proof. multiset_solver. Qed.
  Lemma test2 x y X : {[x]} ⊎ ({[y]} ⊎ X) = {[y]} ⊎ ({[x]} ⊎ X).
  Proof. multiset_solver. Qed.
  Lemma test3 x : {[x]} ⊎ ∅ ≠@{gmultiset A} ∅.
  Proof. multiset_solver. Qed.
  Lemma test4 x y z X Y :
    {[z]} ⊎ X = {[y]} ⊎ Y →
    {[x]} ⊎ ({[z]} ⊎ X) = {[y]} ⊎ ({[x]} ⊎ Y).
  Proof. multiset_solver. Qed.
End test.
