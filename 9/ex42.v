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
