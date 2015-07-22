(* Ex 30 *)
Require Import Arith ZArith Reals QArith.

Lemma z_sq2 (m n : Z) : (0 < m -> 0 < n -> m * m = 2 * n * n -> False)%Z.
Proof.
  intros Hm; revert n; generalize Hm; pattern m; apply Zlt_0_ind; [|omega].
  intros x IHx _ Hx n Hn H.
  assert (exists x0, x = 2 * x0)%Z as [x0 H0].
  { destruct (Z_modulo_2 x) as [[x0 H0] | [x0 H0]]; [eexists; eauto|].
    rewrite H0 in H; ring_simplify in H; omega. }
  rewrite H0 in H; ring_simplify in H.
  assert (n * n = 2 * x0 * x0)%Z by (ring_simplify; omega).
  eapply IHx in H1; try omega.
  split; try omega.
  assert (2 * n * n = (2 * x0) * (2 * x0))%Z by (ring_simplify;eauto).
  rewrite <-H0 in H2.
  assert (x <= n \/ n < x)%Z as [|] by omega; eauto.
  assert (x * x <= n * n)%Z.
  apply Z.square_le_mono_nonneg; omega.
  rewrite H0,H1 in H4; ring_simplify in H4.
  assert (0 < x0)%Z by omega.
  assert (0 < x0 * x0)%Z.
  apply Z.mul_pos_pos; eauto.
  assert (0 < x0 ^ 2)%Z by (ring_simplify in H6; eauto).
  omega.
Qed.

Coercion inject_Z :  Z >-> Q.

Theorem sqrt_2_not_rat : forall q : Q, ~(q ^ 2 == 2%Z).
Proof.
  intros [m n] H.
  assert ((m # n) ^ 2 == m * m # n * n) as Heq; [|rewrite Heq in H; clear Heq].
  { apply Qeq_alt. unfold "?=". simpl.
    apply Z.compare_eq_iff; eauto. }
  apply Qeq_alt in H; unfold "?=" in H; simpl in H.
  apply Z.compare_eq_iff in H; eauto.
  rewrite Pos2Z.inj_xO, Pos2Z.inj_mul, Z.mul_1_r in H.
  assert (m < 0  \/ m = 0 \/ 0 < m)%Z as [|[|]] by omega.
  - assert (0 < - m)%Z by omega.
    assert (m * m = (- m) * (- m))%Z.
    { rewrite Z.mul_opp_opp; eauto. }
    rewrite H2 in H. apply (z_sq2 (-m) ('n)) in H; eauto with zarith.
  - subst; inversion H.
  - apply (z_sq2 m ('n)) in H; eauto with zarith.
Qed.