Require Import SetoidClass Omega.

Record int := {
  Ifst : nat;
  Isnd : nat
}.

Program Instance ISetoid : Setoid int := {|
  equiv x y := Ifst x + Isnd y = Ifst y + Isnd x
|}.
Next Obligation.
Proof.
  split; auto.
  intros x y z Hxy Hyz; omega.
Qed.

Definition zero : int := {|
  Ifst := 0;
  Isnd := 0
|}.

Definition int_minus(x y : int) : int := {|
  Ifst := Ifst x + Isnd y;
  Isnd := Isnd x + Ifst y
|}.

Lemma int_sub_diag : forall x, int_minus x x == zero.
Proof.
  intros [x y]; simpl; omega.
Qed.

(* まず、int_minus_compatを証明せずに、下の2つの証明を実行して、どちらも失敗することを確認せよ。*)
(* 次に、int_minus_compatを証明し、下の2つの証明を実行せよ。 *)

Instance int_minus_compat : Proper (equiv ==> equiv ==> equiv) int_minus.
Proof.
  intros [x0 x1] [y0 y1] Hxy [z0 z1] [w0 w1] Hzw; simpl.
  inversion Hxy; inversion Hzw; omega.
Qed.


Goal forall x y, int_minus x (int_minus y y) == int_minus x zero.
Proof.
  intros x y.
  rewrite int_sub_diag.
  reflexivity.
Qed.

Goal forall x y, int_minus x (int_minus y y) == int_minus x zero.
Proof.
  intros x y.
  setoid_rewrite int_sub_diag.
  reflexivity.
Qed.
