(* Ex 28 *)
Require Import Reals.
Require Import Fourier.
Require Import Psatz.

Theorem PI_RGT_3_05 : (PI > 3 + 5/100)%R.
Proof.
  pose proof (PI_ineq 5) as [H _]. simpl in *.
  unfold tg_alt, PI_tg in H.
  ring_simplify in H. simpl in H. lra.
Qed.
