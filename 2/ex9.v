Require Import Arith.

Goal forall n m p q : nat, (n + m) + (p + q) = (n + p) + (m + q).
Proof.
  intros n m p q.
  apply NPeano.Nat.add_shuffle1.  
Qed.

Goal forall n m : nat, (n + m) * (n + m) = n * n + m * m + 2 * n * m.
Proof.
  intros n m.
  rewrite mult_plus_distr_r, !mult_plus_distr_l.
  rewrite (plus_comm (m * n) (m * m)), plus_assoc.
  rewrite <-(plus_assoc (n * n)), (plus_comm _ (m * m)), plus_assoc. 
  rewrite <-plus_assoc. f_equal.
  simpl; rewrite !mult_plus_distr_r; simpl; rewrite plus_0_r.
  rewrite mult_comm at 3; reflexivity.
Qed.