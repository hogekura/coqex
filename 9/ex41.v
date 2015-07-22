(* ex 41 *)
Ltac split_all := repeat split.

(* 以下は動作確認用 *)

Lemma bar :
  forall P Q R S : Prop,
    R -> Q -> P -> S -> (P /\ R) /\ (S /\ Q).
Proof.
  intros P Q R S H0 H1 H2 H3.
  split_all.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma baz :
  forall P Q R S T : Prop,
    R -> Q -> P -> T -> S -> P /\ Q /\ R /\ S /\ T.
Proof.
  intros P Q R S T H0 H1 H2 H3 H4.
  split_all.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma quux :
  forall P Q : Type, P -> Q -> P * Q.
Proof.
  intros P Q H0 H1.
  split_all.
  - assumption.
  - assumption.
Qed.

Record foo := {
  x : (False -> False) /\ True /\ (False -> False);
  y : True;
  z : (False -> False) /\ True
}.

Lemma hogera : foo.
Proof.
  split_all.
  - intros H; exact H.
  - intros H; exact H.
  - intros H; exact H.
Qed.
