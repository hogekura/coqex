Require Import Arith.
Require Import Omega.
Require Import Recdef.

Function log(n:nat) {wf lt n} :=
  if le_lt_dec n 1 then
    0
  else
    S (log (Div2.div2 n)).
Proof.
  intros n H H'.
  - apply Div2.lt_div2; omega.
  - apply lt_wf.
Qed.
(* ここまでは課題42 *)

Fixpoint pow(n:nat) :=
  match n with
  | O => 1
  | S n' => 2 * pow n'
  end.

Lemma log_pow_lb: forall n, 1 <= n -> pow (log n) <= n.
Proof.
  intros n H.
  functional induction (log n).
  - simpl; auto.
  - simpl.
    destruct n as [|[|n]]; simpl; try omega.
    assert (1 <= Div2.div2 (S (S n))) by (simpl; omega).
    apply IHn0 in H0; simpl in *.
    rewrite plus_0_r.
    assert (Div2.div2 n + Div2.div2 n <= n).
    { fold (Div2.double (Div2.div2 n)).
      destruct (Even.even_odd_dec n).
      rewrite Div2.even_double; auto; omega.
      rewrite Div2.odd_double; auto; omega. }
    omega.
Qed.
