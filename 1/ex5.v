(* Ex 05 *)
Theorem NotNot_Lem : forall P : Prop, ~ ~(P \/ ~P).
  intros P H.
  apply H; right.
  intros Hp.
  apply (H (or_introl Hp)).
Qed.
