Require Import Coq.Relations.Relations Coq.Classes.SetoidClass ProofIrrelevance ClassicalDescription.
Require Import IndefiniteDescription.

Parameter A : Type.
Parameter SetoidA : Setoid A.
Existing Instance SetoidA.

(* 必要な公理を入れる *)

Definition Q : Type := {R : A -> Prop | (exists z, R z) /\
                                        (forall x y, R x -> x == y -> R y) /\
                                        (forall x y, R x -> R y -> x == y)}.

Lemma pi_ok (a : A) : (exists z, z == a) /\ (forall x y : A, x == a -> x == y -> y == a) 
                                         /\ (forall x y : A, x == a -> y == a -> x == y).
Proof.
  split; [exists a; apply setoid_refl|].
  split; intros. 
  - apply setoid_sym in H. symmetry.
    apply setoid_trans with x; auto.
  - apply setoid_sym in H0.
    apply setoid_trans with a; auto.
Defined.

Definition pi(a : A) : Q := exist _ (fun x => x == a) (pi_ok a).

Lemma setoid_rel : forall x : Q, exists a : A, proj1_sig x a.
Proof.
  intros [R [[z H0] H1]]; simpl.
  exists z; auto.
Qed.

Lemma eq_exist {A : Type} (P : A -> Prop) (x y : A) (Hx : P x) (Hy : P y) :
  x = y -> exist P x Hx = exist P y Hy.
Proof.
  destruct 1; f_equal; apply proof_irrelevance.
Qed.

Require Import Ensembles.
Lemma pi_surj : forall x, exists a, pi a = x.
Proof.
  intros [R [[repl Hrepl] [Hrel0 Hrel1]]].
  exists repl; unfold pi.
  apply eq_exist; symmetry.
  { apply Extensionality_Ensembles; unfold Same_set, Included, In; split.
    - intros x Hrx.
      apply Hrel1; auto.
    - intros x Hxr.
      apply Hrel0 with repl; auto; symmetry; auto. }
Qed.

Lemma pi_ker : forall a b, pi a = pi b <-> a == b.
Proof.
  intros a b; split; unfold pi; intros Heq.
  - inversion Heq.
    apply (f_equal (fun x => x a)) in H0.
    rewrite <-H0; apply setoid_refl.
  - assert ((fun x : A => x == a) = (fun x : A => x == b)).
    { apply Extensionality_Ensembles; split; intros x H; unfold In in *; simpl in *.
      - eapply setoid_trans; eauto.
      - symmetry in H; symmetry; eapply setoid_trans; eauto. }
    apply eq_exist; auto.
Qed.

(* 必要な公理を入れる *)

Definition repr (x : A) : A.
  destruct (pi x) as [? [H _]].
  apply constructive_indefinite_description in H as [y H].
  exact y.
Defined.

Lemma representative_exists :
  exists f : A -> A, forall a b, f a = f b <-> a == b.
Proof.
  exists repr; intros a b; unfold repr; split; intros Heq.
  - case_eq (pi a); intros Pa Ha Heqa; rewrite Heqa in *.
    case_eq (pi b); intros Pb Hb Heqb; rewrite Heqb in *.
    inversion Heqa; inversion Heqb; subst.
    clear Heqa Heqb. destruct Ha as [[za Ha0] [Ha1 Ha2]], Hb as [[zb Hb0] [Hb1 Hb2]].
    destruct (constructive_indefinite_description (fun x : A => x == a)),
    (constructive_indefinite_description (fun x0 : A => x0 == b)).
    symmetry in e.
    apply setoid_trans with x; auto.
    apply setoid_trans with x0; auto.
    rewrite Heq; apply setoid_refl.
  - apply pi_ker in Heq. rewrite Heq; auto.
Qed.
