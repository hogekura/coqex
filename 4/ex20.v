Lemma eq_biject (T1 T2 : Set) :
  T1 = T2 -> exists (f : T1 -> T2) (g : T2 -> T1),
               (forall x : T1, g (f x) = x) /\
               (forall x : T2, f (g x) = x).
Proof.
  intros ?; subst; exists (@id T2), (@id T2); eauto.
Qed.

Theorem bool_neq_nat : nat <> (nat -> bool).
Proof.
  intros H; destruct (eq_biject nat (nat -> bool) H) as (f & g & Hgf & Hfg).
  set (ff := fun (n : nat) => if f n n then false else true).
  assert (forall n, ff <> f n).
  { intros n Hc; unfold ff in Hc.
    apply (f_equal (fun x => x n)) in Hc; destruct (f n n); congruence. }
  specialize (Hfg ff); congruence.
Qed.
