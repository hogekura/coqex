Require Import Omega.
Require Import ZArith.

(* Ex 26 *)
Goal (221 * 293 * 389 * 397 + 17 = 14 * 119 * 127 * 151 * 313)%nat.
Proof.
  apply Nat2Z.inj_iff.
  repeat first [rewrite Nat2Z.inj_mul | rewrite Nat2Z.inj_add].
  simpl. auto.
Qed.
