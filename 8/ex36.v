(* ex 36 *)
Require Import ZArith.

Section Principal_Ideal.
  Variable a : Z.

  Definition pi : Set := { x : Z | ( a | x )%Z }.

  Program Definition plus(a b : pi) : pi := (a + b)%Z.
  Next Obligation.
    destruct a0 as [a0 Ha], b as [b Hb]; simpl.
    apply Z.divide_add_r; auto.
  Qed.

  Program Definition mult(a : Z) (b : pi) : pi := (a * b)%Z.
  Next Obligation.
    destruct b as [b Hb]; simpl.
    apply Z.divide_mul_r; auto.
  Qed.
End Principal_Ideal.
