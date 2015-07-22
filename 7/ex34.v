(* Ex 34 *)
Require Import Equalities.

Module Type SemiGroup_Eq.
  Include EqualityType.
  Parameter mult : t -> t -> t.
  Infix "==" := eq (at level 70, no associativity).
  Infix "*" := mult.
  Axiom mult_natural :
    forall x y z w : t, x == z -> y == w -> x * y == z * w.
  Axiom mult_assoc :
    forall x y z : t, x * (y * z) == x * y * z.
End SemiGroup_Eq.
