(* bindの記法を予約 *)
Reserved Notation "x >>= y" (at level 110, left associativity).

(* モナド *)
Class Monad(M:Type -> Type) := {
  bind {A B} : M A -> (A -> M B) -> M B
    where "x >>= f" := (bind x f);
  ret {A} : A -> M A;
  ret_l : forall A B (x : A) (f : A -> M B), (ret x >>= f) = f x;
  ret_r : forall A (m : M A), (m >>= ret) = m;
  bind_assoc : forall A B C (m : M A) (f : A -> M B) (g : B -> M C),
                 ((m >>= f) >>= g) = (m >>= (fun x => f x >>= g))
}.

Notation "x >>= f" := (@bind _ _ _ _ x f).

Require Import List.

Lemma flat_map_app {A B : Type} (l1 l2 : list A) (f : A -> list B) :
  flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
  induction l1; simpl; [congruence|].
  rewrite IHl1, app_assoc; auto.
Qed.

Program Instance ListMonad : Monad list := {|
  bind A B m f := flat_map f m;
  ret A x := (x :: nil)%list
|}.
Next Obligation.
  rewrite app_nil_r; auto.
Qed.
Next Obligation.
  induction m; simpl; congruence.
Qed.
Next Obligation.
  induction m; simpl; [congruence|].
  rewrite flat_map_app; congruence.
Qed.  
    
(* 以下、ListMonadが定義できるまでNext Obligation -> Qed を繰り返す *)

(* モナドの使用例 *)

Definition foo : list nat := 1 :: 2 :: 3 :: nil.

(* 内包記法もどき *)
(*
  do x <- foo
     y <- foo
     (x, y)
*)
Definition bar := Eval lazy in
  foo >>= (fun x =>
  foo >>= (fun y =>
  ret (x, y))).

Print bar.
