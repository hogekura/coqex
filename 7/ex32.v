Require Import Arith.

Module Type SemiGroup.
  Parameter G : Type.
  Parameter mult : G -> G -> G.
  Axiom mult_assoc :
    forall x y z : G, mult x (mult y z) = mult (mult x y) z.
End SemiGroup.

Module NatMult_SemiGroup <: SemiGroup.
  Definition G := nat.
  Definition mult := mult.
  Definition mult_assoc : forall x y z : nat, x * (y * z) = x * y * z := mult_assoc.
End NatMult_SemiGroup.

Module NatMax_SemiGroup <: SemiGroup.
  Definition G := nat.
  Definition mult := max.
  Definition mult_assoc := Max.max_assoc.
End NatMax_SemiGroup.

Module SemiGroup_Product (G0 G1:SemiGroup) <: SemiGroup.
  Definition G := (G0.G * G1.G)%type.
  Definition mult ab cd :=
    (G0.mult (fst ab) (fst cd), G1.mult (snd ab) (snd cd)).
  Lemma mult_assoc : forall (ab cd ef : G), mult ab (mult cd ef) = mult (mult ab cd) ef.
  Proof.
    intros [a b] [c d] [e f]; simpl; unfold mult; simpl; f_equal;
      [apply G0.mult_assoc| apply G1.mult_assoc].
  Qed.
End SemiGroup_Product.
