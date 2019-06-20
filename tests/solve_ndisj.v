From stdpp Require Import namespaces strings.

Set Ltac Backtrace.

Lemma test1 (N1 N2 : namespace) :
  N1 ## N2 → ↑N1 ⊆@{coPset} ⊤ ∖ ↑N2.
Proof. solve_ndisj. Qed.

Lemma test2 (N1 N2 : namespace) :
  N1 ## N2 → ↑N1.@"x" ⊆@{coPset} ⊤ ∖ ↑N1.@"y" ∖ ↑N2.
Proof. solve_ndisj. Qed.

Lemma test3 (N : namespace) :
  ⊤ ∖ ↑N ⊆@{coPset} ⊤ ∖ ↑N.@"x".
Proof. solve_ndisj. Qed.

Lemma test4 (N : namespace) :
  ⊤ ∖ ↑N ⊆@{coPset} ⊤ ∖ ↑N.@"x" ∖ ↑N.@"y".
Proof. solve_ndisj. Qed.

Lemma test5 (N1 N2 : namespace) :
  ⊤ ∖ ↑N1 ∖ ↑N2 ⊆@{coPset} ⊤ ∖ ↑N1.@"x" ∖ ↑N2 ∖ ↑N1.@"y".
Proof.
  Fail solve_ndisj. (* FIXME: it should be able to solve this. *)
  apply namespace_subseteq_difference.
  { apply ndot_preserve_disjoint_r. set_solver. }
  solve_ndisj.
Qed.
