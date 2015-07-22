(* Ex 33 *)
(* 課題32の半群モジュール型を参考にして、モノイドを表すモジュール型 Monoid を定義せよ。*)
Module Type Monoid.
  Parameter M : Type.
  Parameter mult : M -> M -> M.
  Parameter one : M.
  Infix "*" := mult.
  Axiom mult_assoc : forall x y z, x * (y * z) = x * y * z.
  Axiom one_l : forall x, one * x = x.
  Axiom one_r : forall x, x * one = x.
End Monoid.

Require Import List.

(* list boolに自然なモノイドの構造を入れ、Monoid型をもつモジュールとして定義せよ。*)
Module ListBool_Monoid <: Monoid.
  Definition M := list bool.
  Definition mult := @app bool.
  Definition one := @nil bool.

  Lemma mult_assoc : forall xs ys zs, mult xs (mult ys zs) = mult (mult xs ys) zs.
  Proof.
    intros; unfold mult; rewrite List.app_assoc; reflexivity.
  Qed.

  Lemma one_l : forall x, mult one x = x.
  Proof.
    intros x; unfold mult; reflexivity.
  Qed.

  Lemma one_r : forall x, mult x one = x.
  Proof.
    apply List.app_nil_r.
  Qed.
End ListBool_Monoid.

(* モノイドの元の冪乗(指数は自然数)を定義し、指数法則を証明せよ。これを
   定義する際、定義済みのMonoidモジュールを直接変更するのではなく、Monoid
   モジュールMを引数にとる新たなモジュールを定義すること。*)
Module Power_Monoid (M : Monoid).
  Include M.
  Fixpoint power (n : nat) (x : M) :=
    match n with
      | 0 => one
      | S n => mult x (power n x)
    end.
End
Power_Monoid.

(* 2で定義したlist boolのモジュールと、3で定義した冪乗のモジュールを合成して、
   新たなモジュールを作成せよ。*)
Module ListBool_Monoid_Power := Power_Monoid ListBool_Monoid.
