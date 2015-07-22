Parameter A : Set.
Definition Eq : Set -> Set -> Prop :=
  fun x y => forall p : Set -> Prop, p x -> p y.

Lemma Eq_eq : forall x y, Eq x y <-> x = y.
Proof.
  unfold Eq; intros x y; split; intros Heq.
  - pattern x; apply Heq; reflexivity.
  - intros p; rewrite Heq; auto.
Qed.
