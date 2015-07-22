(* Ex 02 *)
Theorem Modus_tollens : forall P Q : Prop, ~Q /\ (P -> Q) -> ~P.
  intros P Q [Hnq Hpq] Hp; apply Hnq, Hpq, Hp.
Qed.
