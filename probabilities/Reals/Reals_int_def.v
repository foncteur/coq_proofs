

(*Axioms*)
Require Import Classical.
Require Import ClassicalChoice.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Require Import Description.
Require Import ClassicalDescription.
Require Import List.
Require Import Psatz.
Require Import Rbase.
Require Import Rfunctions.
Require Import Sets_basics.

Require Import Measure_defs.

Open Scope R_scope.

Check R.


(***********)
(*Intervals*)
(***********)

Definition open_finite_int (a b : R) := fun x => a < x /\ x < b.
Definition closed_finite_int (a b : R) := fun x => a <= x /\ x <= b.
Definition semi_open_left_finite_int (a b : R) := fun x => a < x /\ x <= b.
Definition semi_open_right_finite_int (a b : R) := fun x => a <= x /\ x < b.
Definition left_infinite_open_int (a : R) := fun x => x < a.
Definition left_infinite_closed_int (a : R) := fun x => x <= a.
Definition right_infinite_open_int (a : R) := fun x => a < x.
Definition right_infinite_closed_int (a : R) := fun x => a <= x.

Lemma ineq_neg (a b : R) :
  0 < b -> a - b  < a.
Proof.
  intro Hb. apply Rminus_lt. nra.
Qed.

Lemma compl_left_infinite_open (a : R) :
  compl_in (left_infinite_open_int a) (fun x => True) = right_infinite_closed_int a.
Proof.
  unfold compl_in. unfold left_infinite_open_int. unfold right_infinite_closed_int.
  apply set_ext. intro x. firstorder ; nra.
Qed.


Lemma inter_right_infinite_closed_int (a : R) :
  right_infinite_closed_int a = inter_den (fun n => right_infinite_open_int (a - (/(INR (n+1))))).
Proof.
  unfold right_infinite_closed_int. unfold inter_den. apply set_ext. intro x. split.
  - intro Hax. intro n. unfold right_infinite_open_int.
    assert (a - (/ (INR (n+1))) < a).
    + apply ineq_neg.  apply Rinv_0_lt_compat. apply lt_0_INR. lia.
    + nra.
  - intro H.
    destruct (excluded_middle_informative (a <= x)).
    + assumption.
    + apply Rnot_le_lt in n. exfalso.
      specialize (H (Z.to_nat (up (/((a-x)))))).
      unfold right_infinite_open_int in H. rewrite INR_IZR_INZ in H.
       rewrite Nat2Z.inj_add, Z2Nat.id in H.
      * rewrite plus_IZR in H.
        enough ( / (a - x) < IZR (up (/ (a - x))) + IZR(Z.of_nat 1) ).
        -- enough (/ ((IZR (up (/ (a-x)))) + IZR (Z.of_nat 1) ) < a - x) by nra.
           apply Rinv_lt_contravar in H0.
           ++  rewrite Rinv_involutive in H0 ; nra.
           ++  apply Rmult_lt_0_compat.
              ** apply Rinv_0_lt_compat. nra.
              ** apply Rplus_le_lt_0_compat.
                 --- assert (0 < / (a-x)) by (apply Rinv_0_lt_compat ; nra).
                     generalize (archimed (/ (a-x))).
                     nra.
                 --- apply Rlt_0_1.
        -- apply (Rlt_trans _ (IZR (up (/(a-x))))).
           ++ generalize (archimed (/ (a-x))). nra.
           ++ generalize (Rlt_0_1).
              simpl. nra.
      *apply le_0_IZR. assert (0 < (/ (a-x))) by (apply Rinv_0_lt_compat ; nra).
        generalize (archimed (/ (a-x))). nra.
Qed.

Lemma open_both_is_inter_infinite (a b :R) :
  open_finite_int a b = inter (left_infinite_open_int b) (right_infinite_open_int a).
Proof.
  unfold open_finite_int. unfold inter. apply set_ext. intro x. split.
  - intro H. split.
    + unfold left_infinite_open_int. lra.
    + unfold right_infinite_open_int. lra.
  - intro H. destruct H as [H1 H2].
    unfold left_infinite_open_int in H1. unfold right_infinite_open_int in H2. lra.
Qed.





