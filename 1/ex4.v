(* Ex 04 *)
Theorem DeMorgan1 : forall P Q : Prop, ~P \/ ~Q -> ~(P /\ Q).
Proof.
  intros P Q H0 H1.
  destruct H1 as [Hp Hq], H0 as [H | H]; apply H; [exact Hp | exact Hq].
Qed.

Theorem DeMorgan2 : forall P Q : Prop, ~P /\ ~Q -> ~(P \/ Q).
Proof.
  intros P Q [Hnp Hnq] [Hp | Hq]; [ apply (Hnp Hp) | apply (Hnq Hq)]. 
Qed.

Theorem DeMorgan3 : forall P Q : Prop, ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros P Q Hnpq; split; intros H; apply Hnpq; ((left; exact H) || right; exact H).
Qed.
