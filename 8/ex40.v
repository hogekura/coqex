Require Import SetoidClass.
Require Import List.
Import ListNotations.
(* モノイド *)
Class Monoid(T:Type) := {
  monoid_setoid : Setoid T;
  mult : T -> T -> T
    where "x * y" := (mult x y);
  mult_proper : Proper (equiv ==> equiv ==> equiv) mult;
  one : T
    where "1" := one;
  mult_assoc x y z : x * (y * z) == (x * y) * z;
  mult_1_l x : 1 * x == x;
  mult_1_r x : x * 1 == x
}.

Existing Instance monoid_setoid.
Existing Instance mult_proper.

Delimit Scope monoid_scope with monoid.
Local Open Scope monoid_scope.

Notation "x * y" := (mult x y) : monoid_scope.
Notation "1" := one : monoid_scope.

(* モノイド準同型 *)
Class MonoidHomomorphism{A B:Type}
  {monoid_A : Monoid A} {monoid_B : Monoid B}
  (f : A -> B) : Prop := {
  monoid_homomorphism_proper : Proper (equiv ==> equiv) f;
  monoid_homomorphism_preserves_mult x y:
    f (x * y) == f x * f y;
  monoid_homomorphism_preserves_one:
    f 1 == 1
}.

Existing Instance monoid_homomorphism_proper.

(* モノイドの直和 *)
Section MonoidCoproduct.
  (* A, B : モノイド *)
  Variable A B : Type.
  Context {monoid_A : Monoid A} {monoid_B : Monoid B}.

  (* http://blog.higher-order.com/blog/2014/03/19/monoid-morphisms-products-coproducts/ *)
    
  (* AとBのモノイド直和の台集合 *)
  Definition MonoidCoproduct : Type := (list (A + B))%type.

  (* モノイド直和の二項演算 *)
  Definition MCmult : MonoidCoproduct -> MonoidCoproduct -> MonoidCoproduct := @app (A+B)%type.
  Notation MC := MonoidCoproduct.
  Notation MH := MonoidHomomorphism.
  
  Section Fold.
    Variable Z : Type.
    Variable (f : A -> Z) (g : B -> Z).
    Context {mon : Monoid Z} {homAZ : MH f} {homBZ : MH g}.

    Fixpoint fold (x : MC) : Z :=
    match x with
      | nil => 1
      | inl x :: xs => f x * fold xs
      | inr x :: xs => g x * fold xs
    end.

    Lemma fold_app : forall (xs ys : MC),
      fold (MCmult xs ys) == (fold xs) * (fold ys).
    Proof.
       induction xs as [|[?|?] ?]; simpl; intros.
       - rewrite mult_1_l; reflexivity.
       - rewrite IHxs, mult_assoc; reflexivity.
       - rewrite IHxs, mult_assoc; reflexivity.
    Qed.
  End Fold.

  Section Equal.
    Definition MonoidEqual : MC -> MC -> Prop :=
    fun x y =>
      forall (Z : Type) (f : A -> Z) (g : B -> Z)
             {mon : Monoid Z} {homAZ : MH f} {homBZ : MH g},
        fold Z f g x == fold Z f g y.

    Program Instance MC_setoid : Setoid MonoidCoproduct := {|
      equiv := MonoidEqual
    |}.
    Next Obligation.
      split; unfold MonoidEqual.
      - intros x; reflexivity.
      - intros x y; symmetry; auto.
      - intros x y z; intros.
        eapply setoid_trans; [apply H | apply H0]; auto.
    Qed.

    Lemma fold_proper : forall (Z : Type) (f : A -> Z) (g : B -> Z)
                               {mon : Monoid Z} {homAZ : MH f} {homBZ : MH g},
                          Proper (equiv ==> equiv) (fold Z f g).
    Proof.
      intros; intros xs y Hxy;
      specialize (Hxy Z f g mon homAZ homBZ); auto. 
    Qed.      
  End Equal.

  Definition MC1 : MonoidCoproduct := [].
  
  (* 以上がモノイドになっていること *)
  Program Instance MonoidCoproductMonoid : Monoid MonoidCoproduct := {|
    monoid_setoid := MC_setoid;
    mult := MCmult;
    one := MC1
  |}.
  Next Obligation.
    intros x y Hxy z w Hzw; simpl; unfold MonoidEqual.
    intros; rewrite !fold_app.
    match goal with
        [|- ?x * ?y == ?z * ?w] => (assert (H1 : x == z); [|assert (H2 : y == w)])
    end; try (apply fold_proper; auto).
    rewrite H1, H2; reflexivity.
  Qed.
  Next Obligation.
    unfold MonoidEqual; intros.
    rewrite !fold_app; apply mult_assoc.
  Qed.
  Next Obligation.
    unfold MonoidEqual; reflexivity.
  Qed.
  Next Obligation.
    unfold MonoidEqual, MC1, MCmult; rewrite app_nil_r; reflexivity.
  Qed.

  (* A, Bから直和への標準的な埋め込み射 *)
  Definition emb_l : A -> MonoidCoproduct := fun x => (inl x :: nil).
  Definition emb_r : B -> MonoidCoproduct := fun x => (inr x :: nil).

  (* emb_lがモノイド準同型であること *)
  Instance emb_l_homomorphism : MonoidHomomorphism emb_l.
  Proof.
    split.
    - intros x y Hxy; unfold emb_l; simpl.
      unfold MonoidEqual; intros; simpl.
      rewrite !mult_1_r, Hxy; reflexivity.
    - intros x y; unfold emb_l; simpl; unfold MonoidEqual; simpl; intros.
      rewrite monoid_homomorphism_preserves_mult, mult_assoc; reflexivity.
    - unfold emb_l; simpl; unfold MonoidEqual; simpl; intros.
      rewrite mult_1_r, monoid_homomorphism_preserves_one; reflexivity.
  Qed.

  (* emb_rがモノイド準同型であること *)
  Instance emb_r_homomorphism : MonoidHomomorphism emb_r.
  Proof.
    split.
    - intros x y Hxy; unfold emb_r; simpl.
      unfold MonoidEqual; intros; simpl.
      rewrite !mult_1_r, Hxy; reflexivity.
    - intros x y; unfold emb_r; simpl; unfold MonoidEqual; simpl; intros.
      rewrite monoid_homomorphism_preserves_mult, mult_assoc; reflexivity.
    - unfold emb_r; simpl; unfold MonoidEqual; simpl; intros.
      rewrite mult_1_r, monoid_homomorphism_preserves_one; reflexivity.
  Qed.

  (* 普遍性 *)
  (* Universal Mapping Property *)
  Section UMP.
    (* X : モノイド *)
    Variable X : Type.
    Context {monoid_X : Monoid X}.
    (* f, g : モノイド準同型 *)
    Variable f : A -> X.
    Variable g : B -> X.
    Context {homomorphism_f : MonoidHomomorphism f}.
    Context {homomorphism_g : MonoidHomomorphism g}.

    (* 図式を可換にする射の存在 *)
    Section Existence.
      (* 図式を可換にする射 *)
      Definition h : MonoidCoproduct -> X := fun x => fold _ f g x.

      (* hがモノイド準同型であること *)
      Instance homomorphism_h : MonoidHomomorphism h.
      Proof.
        split.
        - intros x y Hxy; unfold h; apply fold_proper; auto.
        - intros x y.
          unfold h; rewrite fold_app; reflexivity.
        - unfold h; simpl; reflexivity.
      Qed.

      (* hの可換性1 *)
      Lemma h_commute_l : forall a, h (emb_l a) == f a.
      Proof.
        unfold h; simpl; intros; apply mult_1_r.
      Qed.

      (* hの可換性2 *)
      Lemma h_commute_r : forall a, h (emb_r a) == g a.
      Proof.
        unfold h; simpl; intros; apply mult_1_r.
      Qed.
    End Existence.

    (* 図式を可換にする射の一意性 *)
    Section Uniqueness.
      (* h' : モノイド準同型 *)
      Variable h' : MonoidCoproduct -> X.
      Context {homomorphism_h' : MonoidHomomorphism h'}.

      (* h' は上のhと同じ可換性をもつ *)
      Hypothesis h'_commute_l : forall a, h' (emb_l a) == f a.
      Hypothesis h'_commute_r : forall b, h' (emb_r b) == g b.

      (* このようなh'は結局hと同一である *)
      Lemma uniqueness : forall c, h' c == h c.
      Proof.
        intros c; induction c; simpl.
        fold MC1.
        rewrite (@monoid_homomorphism_preserves_one _ _ _ _ _ homomorphism_h'); reflexivity.
        cutrewrite (a :: c = MCmult [a] c); [|auto].
        rewrite (@monoid_homomorphism_preserves_mult _ _ _ _ _ homomorphism_h').
        destruct a as [a|a]; [fold (emb_l a) | fold (emb_r a)].
        - rewrite h'_commute_l, IHc; reflexivity.
        - rewrite h'_commute_r, IHc; reflexivity.
      Qed.
    End Uniqueness.
  End UMP.
End MonoidCoproduct.