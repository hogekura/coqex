Class Monoid(T:Type) := {
  mult : T -> T -> T
    where "x * y" := (mult x y);
  one : T
    where "1" := one;
  mult_assoc x y z : x * (y * z) = (x * y) * z;
  mult_1_l x : 1 * x = x;
  mult_1_r x : x * 1 = x
}.

Delimit Scope monoid_scope with monoid.
Local Open Scope monoid_scope.

Notation "x * y" := (mult x y) : monoid_scope.
Notation "1" := one : monoid_scope.

(* モノイドのリストの積。DefinitionをFixpointに変更するなどはOK *)
Definition product_of{T:Type} {M:Monoid T} : list T -> T :=
  fix prod xs :=
  match xs with
    | nil => 1
    | x :: xs => x * prod xs
  end%list.
      

Require Import Arith.

(* 自然数の最大値関数に関するモノイド。
 * InstanceをProgram Instanceにしてもよい *)
Instance MaxMonoid : Monoid nat := {
  mult := max;
  one := 0
}.
Proof.
  - apply Max.max_assoc.
  - intros [|?]; simpl; auto.
  - intros [|?]; simpl; auto.
Defined.
  
Require Import List.

Eval compute in product_of (3 :: 2 :: 6 :: 4 :: nil). (* => 6 *)
Eval compute in product_of (@nil nat). (* => 0 *)
