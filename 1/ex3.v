(* Ex 03 *)
Theorem Disjunctive_syllogism : forall P Q : Prop, (P \/ Q) -> ~P -> Q.
Proof.
  intros P Q [Hp|Hp] Hnp.
  apply Hnp in Hp; destruct Hp.
  exact Hp.
Qed.
