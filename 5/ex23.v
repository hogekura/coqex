(* Ex 23*)
Definition compose {A B C} (f : A -> B) (g : B -> C) :=
  fun x => g (f x).

Parameter X Y : Type.
Parameter f : X -> Y.

Axiom epi : forall Z (g h : Y -> Z), compose f g = compose f h -> g = h.

(* 必要な公理を入れる *)
Require Import ClassicalDescription FunctionalExtensionality.

Lemma surj : forall y, exists x, f x = y.
Proof.
  intros y.
  assert (H : forall x, {x = y} + {x <> y}) by (intros x; apply excluded_middle_informative).
  set (g := fun x : Y => if H x then true else false).
  set (h := fun x : Y => false).
  assert ((exists x, f x = y) \/ (~exists x, f x = y)) as [H' | H'] by
    apply classic; auto.
  pose proof (epi _ g h).
  assert (compose f g = compose f h).
  { unfold compose, g, h.
    extensionality x.
    destruct (H (f x)); auto.
    contradiction H'; eexists; eauto. }
  assert (g y = h y) by (rewrite H0; auto).
  unfold g, h in *; destruct (H y); congruence.
Qed.

(* 必要な公理を入れる *)
Require Import IndefiniteDescription.
Lemma surj_constructive : forall y, {x | f x = y}.
Proof.
  intros; apply constructive_indefinite_description, surj.
Qed.

Lemma split_epi : exists g, compose g f = id.
Proof.
  exists (fun y => proj1_sig (surj_constructive y)); unfold compose.
  extensionality x; simpl.
  destruct (surj_constructive x); simpl; auto.
Qed.
