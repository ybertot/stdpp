From stdpp Require Import base tactics.

(** Test parsing of variants of [(≡)] notation. *)
Lemma test_equiv_annot_sections `{!Equiv A, !Equivalence (≡@{A})} (x : A) :
  x ≡@{A} x ∧ (≡@{A}) x x ∧ (x ≡.) x ∧ (.≡ x) x ∧
  ((x ≡@{A} x)) ∧ ((≡@{A})) x x ∧ ((x ≡.)) x ∧ ((.≡ x)) x ∧
  ( x ≡@{A} x) ∧ ( x ≡.) x ∧
  (x ≡@{A} x ) ∧ (≡@{A} ) x x ∧ (.≡ x ) x.
Proof. naive_solver. Qed.
