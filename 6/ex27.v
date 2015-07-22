Require Import ZArith.

Ltac lcutr P := let H := fresh in assert (H : P); [|rewrite H; clear H].
Tactic Notation "cutr" constr(P) "by" tactic1(ts) := lcutr P; [solve [ts]|].
   
(* Ex 27 *)
Lemma hoge : forall z : Z, (z ^ 4 - 4 * z ^ 2 + 4 > 0)%Z.
Proof.
  intros z.
  cutr (z ^ 4 - 4 * z ^ 2 + 4 = (z ^ 2 - 2) * (z ^ 2 - 2))%Z by ring.
  assert ((z ^ 2 - 2) * (z ^ 2 - 2) >= 0)%Z by (apply sqr_pos).
  assert ((z ^ 2 - 2) * (z ^ 2 - 2) > 0 \/ (z ^ 2 - 2) * (z ^ 2 - 2) = 0)%Z as [|] by omega; auto.
  apply ->Z.eq_square_0 in H0.
  assert (z * z = 2)%Z by (ring_simplify; omega).
  apply (f_equal Z.abs) in H1; rewrite Z.abs_mul in H1; simpl in H1.
  pose proof (Z.abs_nonneg z).
  assert (Z.abs z = 0 \/ Z.abs z = 1 \/ Z.abs z >= 2)%Z as [H' |[H'|]] by omega; 
    try (rewrite H' in *; simpl in *; try omega).
  assert (Z.abs z * Z.abs z >= 2 * 2)%Z by eauto with zarith.
  omega.
Qed.
