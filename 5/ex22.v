Require Import Coq.Logic.ClassicalDescription.

(* Ex 22 *)
Record isomorphism{A B : Type} (f : A -> B) : Prop := {
  inverse : B -> A;
  is_retraction b : f (inverse b) = b;
  is_section a : inverse (f a) = a
}.

Notation isomorphic A B :=
  (exists f, @isomorphism A B f).

Require Import IndefiniteDescription FunctionalExtensionality.

Lemma neg_unique :
  forall A,
    { isomorphic (A -> Empty_set) Empty_set } +
    { isomorphic (A -> Empty_set) unit }.
Proof.
  intros A.
  assert ({exists x : A, True} + {~ exists x : A, True}) as [H | H]
    by apply (excluded_middle_informative).
  - left.
    apply constructive_indefinite_description in H as [x _].
    assert (f : (A -> Empty_set) -> Empty_set).
    { intros f; destruct (f x). }
    exists f, (fun x : Empty_set => match x with end : A -> Empty_set).
    + intros b; destruct b.
    + intros a; destruct (f a).
  - right.
    set (f := fun (x : A -> Empty_set) => tt).
    set (g := fun (t : unit) (x : A) => match H (ex_intro _ x I) with end : Empty_set).
    exists f, g; intros.
    + destruct (f (g b)), b; auto.
    + extensionality x; unfold f, g; simpl.
      destruct (H (ex_intro _ x I)).
Qed.
