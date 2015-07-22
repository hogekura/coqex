Require Import Arith Omega.

Theorem FF: ~exists f, forall n, f (f n) = S n.
Proof.
  intros [f H].
  assert (HSn : forall n, f (S n) = S (f n)).
  { induction n; congruence. }
  assert (Hn : forall n,  f n = n + f 0).
  { induction n; simpl; congruence. }
  specialize (H 0); rewrite Hn in H; omega.
Qed.
