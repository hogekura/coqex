Require Import Equalities.
Require Import ex34.

(* Ex 35 *)
Module Centerizer (SG : SemiGroup_Eq) <: SemiGroup_Eq.
  Import SG.
  Definition t := {x : SG.t | forall y : SG.t, x * y == y * x}.
  Definition eq (x y : t) := proj1_sig x == proj1_sig y.  

  Lemma eq_equiv : Equivalence eq.
  Proof.
    destruct SG.eq_equiv; split.
    - intros [x ?]; unfold eq; simpl; eauto.
    - intros [x ?] [y ?]; unfold eq; simpl; eauto.
    - intros [x ?] [y ?] [z ?]; unfold eq; simpl; eauto.
  Qed.

  Definition mult (x y : t) : t.
  Proof.
    refine (exist _ (proj1_sig x * proj1_sig y) _).
    intros z.
    destruct SG.eq_equiv as [refl symm trans]; simpl in *.
    destruct x as [x Hx], y as [y Hy]; simpl.
    eapply trans; [eapply symm; eapply mult_assoc|].
    eapply trans; [eapply mult_natural; [apply refl | apply Hy] | ].
    eapply trans; [eapply mult_assoc|].
    eapply trans; [eapply mult_natural; [apply Hx | apply refl] | ].
    eapply trans; [|apply symm; eapply mult_assoc].
    apply refl.
  Defined.
  
  Lemma mult_natural : forall x y z w : t, eq x z -> eq y w -> eq (mult x y) (mult z w).
  Proof.
    intros [x Hx] [y Hy] [z Hz] [w Hw] Hxz Hyw; unfold eq,mult in *; simpl in *.
    apply mult_natural; auto.
  Qed.

  Lemma mult_assoc : forall x y z : t, eq (mult x (mult y z)) (mult (mult x y) z).
  Proof.
    intros [x Hx] [y Hy] [z Hz]; unfold eq,mult in *; simpl in *.
    apply mult_assoc.
  Qed.
End Centerizer.