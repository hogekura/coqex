(* Ex 01*)
Theorem Modas_ponens : forall (P Q : Prop), P -> (P -> Q) -> Q.
Proof.
  intros P Q H H'; apply H', H.
Qed.
