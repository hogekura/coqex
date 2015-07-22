Inductive pos_int : Set :=
| One : pos_int
| S : pos_int -> pos_int.

Fixpoint plus x y := 
  match x with
    | One => S y
    | S x => S (plus x y)
  end.

Infix "+" := plus.

Theorem plus_assoc : forall (x y z : pos_int), x + (y + z) = x + y + z.
Proof.
  induction x; simpl; eauto.
  intros; rewrite IHx; eauto.
Qed.

