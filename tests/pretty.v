From stdpp Require Import pretty.

Section N.
  Local Open Scope N_scope.

  Lemma pretty_N_0 : pretty 0 = "0".
  Proof. reflexivity. Qed.
  Lemma pretty_N_1 : pretty 1 = "1".
  Proof. reflexivity. Qed.
  Lemma pretty_N_9 : pretty 9 = "9".
  Proof. reflexivity. Qed.
  Lemma pretty_N_10 : pretty 10 = "10".
  Proof. reflexivity. Qed.
  Lemma pretty_N_100 : pretty 100 = "100".
  Proof. reflexivity. Qed.
  Lemma pretty_N_123456789 : pretty 123456789 = "123456789".
  Proof. reflexivity. Qed.
End N.

Section nat.
  Local Open Scope nat_scope.

  Lemma pretty_nat_0 : pretty 0 = "0".
  Proof. reflexivity. Qed.
  Lemma pretty_nat_1 : pretty 1 = "1".
  Proof. reflexivity. Qed.
  Lemma pretty_nat_9 : pretty 9 = "9".
  Proof. reflexivity. Qed.
  Lemma pretty_nat_10 : pretty 10 = "10".
  Proof. reflexivity. Qed.
  Lemma pretty_nat_100 : pretty 100 = "100".
  Proof. reflexivity. Qed.
  Lemma pretty_nat_1234 : pretty 1234 = "1234".
  Proof. reflexivity. Qed.
End nat.

Section Z.
  Local Open Scope Z_scope.

  Lemma pretty_Z_0 : pretty 0 = "0".
  Proof. reflexivity. Qed.
  Lemma pretty_Z_1 : pretty 1 = "1".
  Proof. reflexivity. Qed.
  Lemma pretty_Z_9 : pretty 9 = "9".
  Proof. reflexivity. Qed.
  Lemma pretty_Z_10 : pretty 10 = "10".
  Proof. reflexivity. Qed.
  Lemma pretty_Z_100 : pretty 100 = "100".
  Proof. reflexivity. Qed.
  Lemma pretty_Z_123456789 : pretty 123456789 = "123456789".
  Proof. reflexivity. Qed.
  Lemma pretty_Z_opp_1 : pretty (-1) = "-1".
  Proof. reflexivity. Qed.
  Lemma pretty_Z_opp_9 : pretty (-9) = "-9".
  Proof. reflexivity. Qed.
  Lemma pretty_Z_opp_10 : pretty (-10) = "-10".
  Proof. reflexivity. Qed.
  Lemma pretty_Z_opp_100 : pretty (-100) = "-100".
  Proof. reflexivity. Qed.
  Lemma pretty_Z_opp_123456789 : pretty (-123456789) = "-123456789".
  Proof. reflexivity. Qed.
End Z.