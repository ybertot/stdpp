From stdpp Require Import numbers.

(* The class [NatCancel m n m' n'] is a simple canceler for natural numbers
implemented using type classes.

Input: [m], [n]; output: [m'], [n'].

It turns an equality [n = m] into an equality [n' = m'] by canceling out terms
that appear on both sides of the equality. We provide instances to handle the
following connectives over natural numbers:

  n := 0 | t | n + m | S m

Here, [t] represents arbitrary terms that do not fit the grammar. The instances
the class perform a depth-first traversal (from left to right) through [n] and
try to cancel each leaf in [m]. This implies that the shape of the original
expressions [n] and [m] are preserved as much as possible. For example,
canceling:

  S (S m2) + (k1 + (S k2 + k3)) + n1 = 2 + S ((n1 + S n2) + S (S m1 + m2))

Results in:

  k1 + (k2 + k3) = S (n2 + S (S m1))

The instances are setup up so that canceling is performed in two stages.

- In the first stage, using the class [NatCancel], it traverses [m] w.r.t. [S]
  and [+].
- In the second stage, for each leaf (i.e. a constant or arbitrary term)
  obtained by the traversal in stage 1, it uses the class [NatCancelLeaf] to
  cancel the leaf in [n].

Be warned: Since the canceler is implemented using type classes it should only
be used it either of the inputs is relatively small. For bigger inputs, an
approach based on reflection would be better, but for small inputs, the overhead
of reification will probably not be worth it. *)
Class NatCancel (m n m' n' : nat) := nat_cancel : m' + n = m + n'.
Hint Mode NatCancel ! ! - - : typeclass_instances.
Class NatCancelLeaf (m n m' n' : nat) := nat_cancel_leaf : NatCancel m n m' n'.
Hint Mode NatCancelLeaf ! ! - - : typeclass_instances.

Global Existing Instance nat_cancel_leaf | 100.

Class MakeNatS (n1 n2 m : nat) := make_nat_S : m = n1 + n2.
Global Instance make_nat_S_0_l n : MakeNatS 0 n n.
Proof. done. Qed.
Global Instance make_nat_S_1 n : MakeNatS 1 n (S n).
Proof. done. Qed.

Class MakeNatPlus (n1 n2 m : nat) := make_nat_plus : m = n1 + n2.
Global Instance make_nat_plus_0_l n : MakeNatPlus 0 n n.
Proof. done. Qed.
Global Instance make_nat_plus_0_r n : MakeNatPlus n 0 n.
Proof. unfold MakeNatPlus. by rewrite Nat.add_0_r. Qed.
Global Instance make_nat_plus_default n1 n2 : MakeNatPlus n1 n2 (n1 + n2) | 100.
Proof. done. Qed.

Global Instance nat_cancel_leaf_here m : NatCancelLeaf m m 0 0 | 0.
Proof. by unfold NatCancelLeaf, NatCancel. Qed.
Global Instance nat_cancel_leaf_else m n : NatCancelLeaf m n m n | 100.
Proof. by unfold NatCancelLeaf, NatCancel. Qed.
Global Instance nat_cancel_leaf_plus m m' m'' n1 n2 n1' n2' n1'n2' :
  NatCancelLeaf m n1 m' n1' → NatCancelLeaf m' n2 m'' n2' →
  MakeNatPlus n1' n2' n1'n2' → NatCancelLeaf m (n1 + n2) m'' n1'n2' | 2.
Proof. unfold NatCancelLeaf, NatCancel, MakeNatPlus. omega. Qed.
Global Instance nat_cancel_leaf_S_here m n m' n' :
  NatCancelLeaf m n m' n' → NatCancelLeaf (S m) (S n) m' n' | 3.
Proof. unfold NatCancelLeaf, NatCancel. omega. Qed.
Global Instance nat_cancel_leaf_S_else m n m' n' :
  NatCancelLeaf m n m' n' → NatCancelLeaf m (S n) m' (S n') | 4.
Proof. unfold NatCancelLeaf, NatCancel. omega. Qed.

(* The instance [nat_cancel_S_both] is redundant, but may reduce proof search
quite a bit, e.g. when canceling constants in constants. *)
Global Instance nat_cancel_S_both m n m' n' :
  NatCancel m n m' n' → NatCancel (S m) (S n) m' n' | 1.
Proof. unfold NatCancel. omega. Qed.
Global Instance nat_cancel_plus m1 m2 m1' m2' m1'm2' n n' n'' :
  NatCancel m1 n m1' n' → NatCancel m2 n' m2' n'' →
  MakeNatPlus m1' m2' m1'm2' → NatCancel (m1 + m2) n m1'm2' n'' | 2.
Proof. unfold NatCancel, MakeNatPlus. omega. Qed.
Global Instance nat_cancel_S m m' m'' Sm' n n' n'' :
  NatCancel m n m' n' → NatCancelLeaf 1 n' m'' n'' →
  MakeNatS m'' m' Sm' → NatCancel (S m) n Sm' n'' | 3.
Proof. unfold NatCancelLeaf, NatCancel, MakeNatS. omega. Qed.