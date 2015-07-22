Require Import ZArith.

Definition prime1(z : Z) : Prop :=
  z <> 0%Z /\
  forall a b, ((z | a * b) -> (z | a) \/ (z | b))%Z.

Definition prime2(z : Z) : Prop :=
  forall a b, (z = a * b -> (a | 1) \/ (b | 1))%Z.

Require Import Znumtheory.

Lemma prime1_prime2_iff z : prime1 z <-> prime2 z.
Proof.
  unfold prime1, prime2; split.
  - intros [Hnz0 H] a b Hz.
    assert (z | a * b)%Z by (rewrite Hz; eauto with zarith).
    assert ((z | a) \/ (z | b))%Z as [? | ?] by auto; rewrite Hz in *.
    + assert (a * b | a * 1)%Z by (ring_simplify; auto).
      pose proof (Z.mul_divide_cancel_l b 1 a).
      assert (a <> 0)%Z by eauto with zarith.
      intuition.
    + assert (a * b | 1 * b)%Z by (ring_simplify; auto).
      pose proof (Z.mul_divide_cancel_r a 1 b).
      pose proof (Z.neq_mul_0 a b).
      intuition.
  - intros H.
    split; [intros ->; destruct (H 0 0 eq_refl)%Z; pose proof (Z.divide_0_l 1); intuition|].
    intros a b Hz.
    assert (Z.gcd z a | z)%Z as [z' Hz'] by (apply Z.gcd_divide_l).
    assert (Z.gcd z a | a)%Z as [a' Ha'] by (apply Z.gcd_divide_r).
    pose proof (H _ _ Hz') as [H0 | H0].
    + apply Z.divide_1_r in H0 as [|]; subst z'; rewrite Hz'; left; ring_simplify;
      [|apply <-Z.divide_opp_l]; apply Z.gcd_divide_r.
    + assert (Z.gcd z a = 1) by (pose proof (Z.divide_1_r (Z.gcd z a));
                               pose proof (Z.gcd_nonneg z a); intuition).
      assert (rel_prime z a) by (apply Zgcd_1_rel_prime; auto).
      eauto with zarith.
      right; eapply Gauss; eauto.
Qed.
