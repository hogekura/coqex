Goal forall P Q : nat -> Prop, P 0 -> (forall x, P x -> Q x) -> Q 0.
Proof.
  intros ? ? H H'; apply H' in H; exact H.
Qed.

Goal forall P : nat -> Prop, P 2 -> (exists y, P (1 + y)).
Proof.
  intros ? H2; exists 1; exact H2.
Qed.

Goal forall P : nat -> Prop, (forall n m, P n -> P m) -> (exists p, P p) -> forall q, P q.
Proof.
  intros ? Hnm [p Hp] q; eapply Hnm in Hp; exact Hp.
Qed.
