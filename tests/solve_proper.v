From stdpp Require Import prelude.

(** Some tests for solve_proper. *)
Section tests.
  Context {A B : Type} `{!Equiv A, !Equiv B}.
  Context (foo : A → A) (bar : A → B) (baz : B → A → A).
  Context `{!Proper ((≡) ==> (≡)) foo,
            !Proper ((≡) ==> (≡)) bar,
            !Proper ((≡) ==> (≡) ==> (≡)) baz}.

  Definition test1 (x : A) := baz (bar (foo x)) x.
  Global Instance : Proper ((≡) ==> (≡)) test1.
  Proof. solve_proper. Qed.

  Definition test2 (b : bool) (x : A) :=
    if b then bar (foo x) else bar x.
  Global Instance : ∀ b, Proper ((≡) ==> (≡)) (test2 b).
  Proof. solve_proper. Qed.

  Definition test3 (f : nat → A) :=
    baz (bar (f 0)) (f 2).
  Global Instance : Proper (pointwise_relation nat (≡) ==> (≡)) test3.
  Proof. solve_proper. Qed.
End tests.
