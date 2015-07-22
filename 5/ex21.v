(* Ex 21 *)
Require Import Coq.Logic.Classical.

Lemma ABC_iff_iff :
    forall A B C : Prop, ((A <-> B) <-> C) <-> (A <-> (B <-> C)).
Proof.
  intros A B C.
  destruct (classic A), (classic B), (classic C); tauto.
Qed.

(* 必要な公理を入れる *)

Goal
  forall P Q R : Prop,
  (IF P then Q else R) ->
  exists b : bool,
  (if b then Q else R).
Proof.
  intros P Q R [[? ?]|[? ?]]; [exists true | exists false]; auto.
Qed.

(* 必要な公理を入れる *)
Require Import Coq.Logic.ClassicalDescription.

Goal
  forall P Q R : nat -> Prop,
  (forall n, IF P n then Q n else R n) ->
  exists f : nat -> bool,
  (forall n, if f n then Q n else R n).
Proof.
  intros.
  exists (fun n => if excluded_middle_informative (P n) then true else false).
  intros; destruct (excluded_middle_informative _); firstorder.
Qed.
