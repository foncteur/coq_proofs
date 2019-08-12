
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

Load Measure_basics.

Open Scope R_scope.

Check R.



(***********)
(*Notations*)
(***********)

Definition is_open_R (A : R -> Prop) :=
  forall x, A x -> exists epsilon, 0 < epsilon /\ forall y, 0 < y -> y < epsilon -> A (x - y) /\ A (x + y).


Definition M_interesting :=
  generated_sig_alg (fun x => True) (fun A => exists (a : R), A = right_infinite_open_int a).
Definition M_reals_borelian :=
  generated_sig_alg (fun x => True) (fun A => is_open_R A).

(*We want to show that M_reals_borelian = M_interesting.*)


(*First, we want to show that any open set in R is a countable union of intervals
 of the form ]- \infty ; a [, ]a ; b[ and ]b ; + \infty[.
We will call this important_lemma.*)

(*****************)
(*Important lemma*)
(*****************)
