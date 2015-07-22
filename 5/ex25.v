Require Import FunctionalExtensionality ClassicalDescription Program.Equality.

Definition Nat : Type :=
  forall A : Type, (A -> A) -> (A -> A).

Definition NatMult(n m : Nat) : Nat :=
  fun A f => n _ (m _ f).

Definition n : Nat := fun A f x =>
  if excluded_middle_informative (f ~= S) then f x else x.

Lemma NatMult_not_comm: ~forall n m, NatMult n m = NatMult m n.
Proof.
  unfold Nat, NatMult; intros Hc.
  specialize (Hc n (fun A f x => f (f x))); simpl in *.
  pose proof (@f_equal (forall A : Type, (A -> A) -> A -> A) _ (fun x => x nat S 0) _ _ Hc); simpl in *.
  assert (S ~= S) by auto.
  assert (~(fun x : nat => S (S x)) ~= S).
  { intros Hq. simpl_JMeq.
    apply (@f_equal (nat -> nat) _ (fun x => x 0)) in Hq; congruence. }
  unfold n in H.
  repeat match goal with
           | [H : context [if ?x then _ else _] |- _ ] => destruct x; try tauto
         end; congruence.
Qed.