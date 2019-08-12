
(*********************************************************)
(*We try to implement a general version of measure theory*)
(*********************************************************)

(* This is based on https://www-fourier.ujf-grenoble.fr/~edumas/integration.pdf *)

(*This file defines a measurable space, and a topololgy.*)


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
Require Import Topo_defs.


(*******************)
(*Measurable spaces*)
(*******************)

Definition is_sigma_algebra {E} (X : E-> Prop) (M : (E -> Prop) -> Prop) :=
  (forall A, (M A) -> subset A X) /\
  (M X) /\
  (forall A, (M A) -> (M (compl_in A X))) /\
  (forall f : nat -> (E -> Prop), (forall (n : nat), M (f n)) -> M (union_den f)).

Definition is_measurable_space {E} (M : (E -> Prop) -> Prop) (X : E -> Prop) := is_sigma_algebra X M.

(*A few elementary properties.*)

(*The empty set is a measurable space.*)
Lemma empty_is_measurable_part {E} (M : (E -> Prop) -> Prop) (X : E -> Prop) :
  is_sigma_algebra X M -> M (empty_set).
Proof.
  intro H. destruct H as [H1 [H2 [H3 H4]]].
  specialize (H3 X). apply H3 in H2.
  assert (compl_in X X = empty_set).
  - unfold compl_in. unfold empty_set.
    apply set_ext. intro x. tauto.
  - rewrite H in H2 ; assumption.
Qed.

(*A measurable space is stable by countable intersection.*)
Lemma stable_den_inter {E} (M : (E -> Prop) -> Prop) (X : E -> Prop) (f : nat -> (E -> Prop)) :
  is_sigma_algebra X M -> (forall n, M (f n)) -> M (inter_den f).
Proof.
  intro H_sigma. intro H.  destruct H_sigma as [H_sigma1 [H_sigma2 [H_sigma3 H_sigma4]]].
  enough (M (compl_in (inter_den f) X)).
  - specialize (H_sigma3 (compl_in (inter_den f) X)). apply H_sigma3 in H0.
    rewrite compl_in_invol in H0.
    assert (inter (inter_den f) X = inter_den f).
    + unfold inter. unfold inter_den. apply set_ext.
      intro x. split.
      * intro A. destruct A as [A1 A2]. assumption.
      * intro A. split.
        -- assumption.
        -- specialize (H 0). specialize (A 0). specialize (H_sigma1 (f 0)).
           apply H_sigma1 in H. unfold subset in H. specialize (H x).
           apply H in A. assumption.
    + rewrite H1 in H0. assumption.
  - rewrite compl_inter_den_in.
    apply H_sigma4. intro n. apply H_sigma3. specialize (H n) ; assumption.
Qed.


(*A measurable space is stable by finite union and intersection.*)
Lemma stable_finite_union {E} (M : (E -> Prop) -> Prop) (X : E -> Prop) (l : list (E -> Prop)) :
  is_sigma_algebra X M ->(forall ens, In ens l -> M ens) -> M (finite_union l).
Proof.
  intros H H0. remember H as H_sig. clear HeqH_sig.
  rewrite <- finite_union_is_den. destruct H as [H1 [H2 [H3 H4]]].
  apply H4. intro n. unfold den_union_from_finite.
  destruct (excluded_middle_informative (n < length l)).
  - Search (In). apply (H0).  apply (nth_In). assumption.
  - rewrite nth_overflow.
    + apply (empty_is_measurable_part M X). assumption.
    + lia.
Qed.


Lemma stable_finite_inter {E} (M : (E -> Prop) -> Prop) (X : E -> Prop) (l : list (E -> Prop)) :
  is_sigma_algebra X M -> (forall ens, In ens l -> M ens) -> M (finite_inter l X).
Proof.
  intros H0 H. remember H0 as H_sig. destruct H0 as [H1 [H2 [H3 H4]]]. clear HeqH_sig.
  rewrite <- finite_inter_is_den.
  apply (stable_den_inter M X) ; try assumption.
  intros n. unfold den_inter_from_finite.
  destruct (excluded_middle_informative (n < length l)).
  - apply (nth_In l X) in l0. specialize (H (nth n l X)).
    apply H in l0. assumption.
  - rewrite nth_overflow.
    + assumption.
    + lia.
Qed.

Lemma stable_sym_diff {E} (M : (E -> Prop) -> Prop) (X : E -> Prop) (A B : E -> Prop) :
  is_sigma_algebra X M -> M A -> M B -> M (sym_diff A B X).
Proof.
  intro H. intros HA HB.
  unfold sym_diff. replace (inter A (compl_in B X)) with (finite_inter (A::(compl_in B X)::nil) X).
  - apply stable_finite_inter.
    + assumption.
    + intro ens. intro H_in.
      destruct H_in.
      * rewrite H0 in HA ; assumption.
      * destruct H0.
        -- destruct H as [H1 [H2 [H3 H4]]].
           specialize (H3 B). apply H3 in HB. rewrite H0 in HB. assumption.
        -- inversion H0.
  - unfold finite_inter. unfold inter. apply set_ext. intro x.
    simpl. split.
    + intro H'. destruct H'. split.
      * specialize (H0 A). firstorder.
      * specialize (H0 (compl_in B X)). firstorder.
    + intro H'.
      split.
      intro ens. intuition congruence. destruct H'.
      unfold compl_in in H1. destruct H1. assumption.
Qed.

Remark trivial_are_measurable {E} (X : E -> Prop):
  is_measurable_space (fun A => (A = empty_set) \/ A = X) X /\
  is_measurable_space (fun A => subset A X) X.
Proof.
  unfold is_measurable_space. split.
  - unfold is_sigma_algebra. split.
    + intro A. intro H. destruct H.
      * unfold empty_set in H. unfold subset. intro x.
        intro H'. rewrite H in H'. contradiction.
      * unfold subset. intro x. intro H'. rewrite H in H'. assumption.
    + split ; [|split].
      * right. reflexivity.
      * intro A. intro H. destruct H.
        -- right. unfold compl_in. rewrite H.
           apply set_ext. intro x. split.
           ++ intro H'. firstorder.
           ++ intro H'. split ; firstorder.
        -- left. unfold compl_in. rewrite H.
           apply set_ext. intro x. split ; firstorder.
      * intro f. intro H. 
        unfold union_den.
        destruct (excluded_middle_informative (forall n, f n = empty_set)).
        -- left. unfold empty_set. apply set_ext. intro x.
           firstorder. specialize (e x0). rewrite e in H0. contradiction H0.
        -- right.  apply set_ext ; intro x. split.
           ++ intro H'. destruct H'. specialize (H x0). destruct H.
              ** exfalso. rewrite H in H0. contradiction H0.
              ** rewrite H in H0 ; assumption.
           ++ intro H'. Search (~ forall _, _). apply not_all_ex_not in n.
              destruct n. destruct (H x0).
              ** congruence.
              ** exists x0. congruence.
  - unfold is_sigma_algebra. split ; [|split].
    + intro A. intro H. assumption.
    + unfold subset. firstorder.
    + split.
      * intro A. intro H. unfold subset. unfold compl_in. intro x. firstorder.
      * intro f. intro H. unfold subset. unfold union_den. intro x.
        intro H'. destruct H'. specialize (H x0). firstorder.
Qed.


(*A general intersection of measurable spaces is measurable*)
Lemma inter_index_is_measurable {E I} (i0 : I) (f : I -> (E -> Prop) -> Prop) (X : E -> Prop)  :
  (forall i, is_sigma_algebra X (f i) ) -> is_sigma_algebra X (inter_ind f).
Proof.
  intro H. unfold is_sigma_algebra.
  split ; [|split ; [|split]].
  - intro A. intro HA.
    unfold subset. intro x. intro Hx.
    unfold inter_ind in HA. specialize (HA i0).
    firstorder.
  - unfold inter_ind. intro i. specialize (H i).
    unfold is_sigma_algebra in H. destruct H. destruct H0. assumption.
  - intro A. intro HA.
    unfold inter_ind. intro i.
    specialize (H i). unfold is_sigma_algebra in H.
    destruct H as [H1 [H2 [H3 H4]]].
    specialize (H3 A). unfold inter_ind in HA. specialize (HA i).
    apply H3 in HA. assumption.
  - intro f0. intro Hf.
    unfold inter_ind. intro i. specialize (H i).
    destruct H as [H1 [H2 [H3 H4]]].
    specialize (H4 f0). unfold inter_ind in Hf.
    firstorder.
Qed.

(*The following definition lacks the condition that all sets in F are subsets of X.*)
Definition generated_sig_alg {E} (X : E -> Prop) (F : (E -> Prop) -> Prop) :=
  inter_ind (fun (M : { M | is_sigma_algebra X M /\ subset F M }) => proj1_sig M).

Remark generated_sig_alg_is_sig_alg {E} (X : E -> Prop) (F : (E -> Prop) -> Prop) :
  (forall A, F A -> subset A X) -> is_sigma_algebra X (generated_sig_alg X F).
Proof.
  intros.
  unfold generated_sig_alg. apply inter_index_is_measurable.
  - exists (fun A => subset A X). split.
    + apply trivial_are_measurable.
    + unfold subset. intro x. intro Hf. intro x0. intro Hx0.
      specialize (H x). apply H in Hf. unfold subset in Hf.
      firstorder.
  - intro i. apply (proj2_sig i).
Qed.

Remark generated_sig_alg_is_smallest {E} (X : E -> Prop) (F : (E -> Prop) -> Prop) :
  (forall A, F A -> subset A X) -> forall B, ((is_sigma_algebra X B) /\ subset F B) -> 
                                 subset ( generated_sig_alg X F) B.
Proof.
  intro H0. intro T. intro H. 
  unfold generated_sig_alg. unfold subset.  intro x. intro H'.
  unfold inter_ind in H'. specialize (H' (exist _ T H)).
  simpl in H'. assumption.
Qed.


(*The following definition doesn't verify that T is a topology on X.*)
Definition borel_sig_alg {E} (X : E -> Prop) (T : (E -> Prop) -> Prop) :=
  generated_sig_alg X T.

