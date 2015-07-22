Require Import List.

Inductive Tree:Set :=
| Node: list Tree -> Tree.

Inductive ForallSet (A : Type) (f : A -> Set) : list A -> Type :=
| Forall_nil : ForallSet A f nil
| Forall_cons : forall x xs,  f x -> ForallSet A f xs -> ForallSet A f (x :: xs).

Definition Tree_ind' (P : Tree -> Set)
  (Pt : forall l : list Tree, ForallSet Tree P l -> P (Node l)) :
  forall t : Tree, P t.
Proof.
  refine (fix f (t : Tree) :=
          match t return P t with
            | Node l =>
              let f := (fix f' (l : list Tree) :=
                          match l return ForallSet Tree P l with
                            | nil => _
                            | x :: xs => _
                          end) in
              _
          end); try constructor; [eauto | eauto | apply Pt; eauto].
Qed.

Theorem Tree_dec: forall a b:Tree, {a=b} + {a<>b}.
Proof.
  induction a as [l] using Tree_ind'.
  induction l; intros.
  - destruct b as [[|]]; [left | right]; congruence.
  - destruct b as [[|]]; [right; congruence|].
    inversion H; subst.
    destruct (IHl H3 (Node l0)), (H2 t); firstorder congruence.
Qed.
