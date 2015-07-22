Require Import Arith.

Definition Nat : Type :=
  forall A : Type, (A -> A) -> (A -> A).

Definition NatPlus (n m : Nat) : Nat :=
  fun _ s z => n _ s (m _ s z).

Definition nat2Nat : nat -> Nat := nat_iter.

Definition Nat2nat(n : Nat) : nat := n _ S O.

Lemma NatPlus_plus :
  forall n m, Nat2nat (NatPlus (nat2Nat n) (nat2Nat m)) = n + m.
Proof.
  intros n m; induction n as [|n]; simpl.
  unfold Nat2nat, NatPlus, nat2Nat; simpl.
  - induction m; simpl; eauto.
  - unfold Nat2nat, NatPlus, nat2Nat in *; simpl; congruence.
Qed.
