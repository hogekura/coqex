(* Ex 10*)
Parameter G : Set.
Parameter mult : G -> G -> G.
Notation "x * y" := (mult x y).
Parameter one : G.
Notation "1" := one.
Parameter inv : G -> G.
Notation "/ x" := (inv x).
(* Notation "x / y" := (mult x (inv y)). *) (* 使ってもよい *)

Axiom mult_assoc : forall x y z, x * (y * z) = (x * y) * z.
Axiom one_unit_l : forall x, 1 * x = x.
Axiom inv_l : forall x, /x * x = 1.

Lemma inv_r : forall x, x * / x = 1.
Proof.
  intros x.
  assert (x * (/x * x) * /x = x * /x).
  { rewrite inv_l, <-mult_assoc, one_unit_l; reflexivity. }
  assert (x * /x * (x * / x) = x * /x).
  { rewrite <-mult_assoc, (mult_assoc (/ x)), mult_assoc, H. reflexivity. }
  assert (/ (x * / x) * ((x * / x) * (x * / x)) = / (x * / x) * (x * / x)).
  { rewrite H0; reflexivity. }
  rewrite mult_assoc, inv_l, one_unit_l in H1; exact H1.
Qed.

Lemma one_unit_r : forall x, x * 1 = x.
Proof.
  intros x.
  rewrite <-(inv_l x), mult_assoc, inv_r, one_unit_l; reflexivity.
Qed.