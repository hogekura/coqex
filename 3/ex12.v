Require Import Lists.List.
Require Import Omega.

Fixpoint sum (xs: list nat) : nat :=
  match xs with
    | nil => 0
    | x :: xs => x + sum xs
  end.

Theorem Pigeon_Hole_Principle :
  forall (xs : list nat), length xs < sum xs -> (exists x, 1<x /\ In x xs).
Proof.
  induction xs; simpl; intros; [omega|].
  assert (a <= 1 \/ a > 1) as [Ha | Ha] by omega.
  - assert (length xs < sum xs) by omega; firstorder.
  - firstorder.
Qed.
