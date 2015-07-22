Require Import Arith.

Goal forall x y, x < y -> x + 10 < y + 10.
Proof.
  intros x y.
  apply plus_lt_compat_r.
Qed.
