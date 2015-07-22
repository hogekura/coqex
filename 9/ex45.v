Require Import ZArith Omega.
Local Open Scope Z_scope.

Inductive Collatz: Z -> Prop :=
| CollatzOne: Collatz 1
| CollatzEven: forall x, Collatz x -> Collatz (2*x)
| CollatzOdd: forall x, Collatz (3*x+2) -> Collatz (2*x+1).

Definition option_out (P : Prop) (x : option P) :=
  match x return (match x with
                    | Some _ => P
                    | None => True
                  end) with 
    | Some x => x
    | None => I
  end.

Require Import List.
Import ListNotations.

Fixpoint ps_list n :=  
  match n with
    | 0 => []
    | S n => Pos.of_nat (S n) :: ps_list n
  end%nat.

Inductive MyCollatz: positive -> Prop :=
| C1: MyCollatz 1
| CE: forall x, MyCollatz x -> MyCollatz (x~0)
| CO: forall x, MyCollatz (3*x+2) -> MyCollatz (x~1).

Fixpoint mycollatz_calc (n : nat) (p : positive) : option (MyCollatz p) :=
  match n with
    | 0%nat => None
    | S n =>
      match p return option (MyCollatz p) with
        | 1%positive => Some C1
        | p~0 => match mycollatz_calc n p with
                   | None => None
                   | Some c => Some (CE _ c)
                 end
        | p~1 => match mycollatz_calc n (3 * p + 2) with
                   | None => None
                   | Some c => Some (CO _ c)
                 end
      end
  end%positive.

Lemma mycollatz_collatz (p : positive) : MyCollatz p -> Collatz (Zpos p).
Proof.
  Hint Constructors Collatz.
  induction 1; simpl; eauto.
  cutrewrite (Zpos x~0 = 2 * Zpos x); eauto.
  cutrewrite (Zpos x~1 = 2 * Zpos x + 1); eauto.
Qed.

Fixpoint collatzs_check (ps : list positive) : option (Forall MyCollatz ps) :=
  match ps return option (Forall MyCollatz ps) with
    | [] => Some (Forall_nil _)
    | p :: ps =>
      match mycollatz_calc 200 p with
        | Some cp => match collatzs_check ps with
                       | Some cps' => Some (Forall_cons _ cp cps')
                       | None => None
                     end
        | None => None
      end
  end.

Fixpoint zs_list (n : nat) :=
  match n with
    | O => []
    | S n' => Z.of_nat n :: zs_list n'
  end.

Lemma mycallatz_collatz_list (n : nat) :  Forall MyCollatz (ps_list n) -> Forall Collatz (zs_list n).
Proof.
  induction n; intros H; [constructor|].
  cutrewrite (ps_list (S n) = Pos.of_nat (S n) :: ps_list n) in H; [|eauto].
  remember (Pos.of_nat (S n)) as pn.
  inversion H; subst; simpl. apply IHn in H3.
  constructor; eauto.
  apply mycollatz_collatz.
  rewrite <-Pos.of_nat_succ in H2; eauto.
Qed.

Lemma forallZs (n : nat) (P : Z -> Prop) :
  List.Forall P (zs_list n) -> (forall x, 1 <= x <= Z.of_nat n -> P x).
Proof.
  induction n; intros H x Hr; [simpl in Hr; omega |]. 
  cutrewrite (Z.of_nat (S n) = Z.succ (Z.of_nat n)) in Hr; [| rewrite Nat2Z.inj_succ; eauto].
  simpl in H; inversion H; subst.
  assert (x = Z.succ (Z.of_nat n) \/ x <= Z.of_nat n) as [|] by omega; subst.
  rewrite Zpos_P_of_succ_nat in H2; eauto.
  apply IHn; eauto; split; tauto.
Qed.

Lemma MyCollatz_1000 : Forall MyCollatz (ps_list 1000).
  pose proof (option_out _ (collatzs_check (ps_list 1000))).
  Time cbv in *.
  exact X.
  Show Proof.
Time Qed. (* take about 30 sec*)

Theorem Collatz_1000: forall x : Z, 1 <= x <= 1000 -> Collatz x.
Proof.
  cutrewrite (1000 = Z.of_nat 1000); [|cbv; eauto].
  apply forallZs.
  apply mycallatz_collatz_list.
  apply MyCollatz_1000.
Qed.
