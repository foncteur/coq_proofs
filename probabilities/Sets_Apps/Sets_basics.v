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



(***************)
(*Miscellaneous*)
(***************)


(*A little lemma that can be useful later.*)
Lemma set_ext {E} :
  forall (A B : E -> Prop), (forall x, A x <-> B x) -> A = B.
Proof.
  intros A B. intro H.
  extensionality x. apply propositional_extensionality.
  destruct (H x). split ; assumption.
Qed.

(*A few definitions on sets.*)

(*Subset X of Y.*)
Definition subset {E} (X Y : E -> Prop) := forall x, (X x) -> (Y x).
(*Complement of a set X.*)
Definition compl {E} (X : E -> Prop) := fun x => not (X x).
(*Complement of a set X in a set Y.*)
Definition compl_in {E} (X Y : E -> Prop) := fun x => (not (X x)) /\ Y x.
(*Union of two sets.*)
Definition union {E} (X Y : E -> Prop) := fun x => (X x) \/ (Y x).
(*Indexed union*)
Definition union_ind {E I} (f : I -> (E -> Prop)) := fun x => (exists n, (f n) x).
(*General union*)
Definition union_gen {E} (A : (E -> Prop) -> Prop) := fun x => (exists X, A X /\ X x).
(*Countable union of sets.*)
Definition union_den {E} (f : nat -> (E -> Prop)) := fun x => (exists n, (f n) x).
(*Intersection of two sets.*)
Definition inter {E} (X Y : E -> Prop) := fun x => (X x) /\ (Y x).
(*Countable intersection of sets.*)
Definition inter_den {E} (f : nat -> (E -> Prop)) := fun x => (forall n, (f n) x).
(*Indexed intersection*)
Definition inter_ind {E I} (f : I -> (E -> Prop)) := fun x => (forall i, (f i) x).
(*General intersection*)
Definition inter_gen {E} (A : (E -> Prop) -> Prop) := fun x => (forall X, A X -> X x).
(*The empty set.*)
Definition empty_set {E : Type} := fun (x : E) => False.
(*Symmetric difference*)
Definition sym_diff {E : Type} (A B : E -> Prop) (X : E -> Prop) := inter A (compl_in B X).
(*Finite union*)
Definition finite_union {E} (l : list (E -> Prop)) := fun x => exists ens, In ens l /\ ens x.
(*Finite intersection*)
Definition finite_inter {E} (l : list (E -> Prop)) X := fun x => (forall ens, In ens l -> ens x) /\ X x.

(*An indexed union is a general union*)
Lemma union_gen_is_ind {E I} (f : I -> (E -> Prop))  :
  union_ind f = union_gen (fun X => (exists i, f i = X)).
Proof.
  apply set_ext. split.
  - intro H. unfold union_gen. unfold union_ind in H. destruct H as [n Hn].
    exists (f n). split.
    + exists n. reflexivity.
    + exact Hn.
  - intro H. unfold union_ind. unfold union_gen in H. destruct H as [X HX].
    destruct HX as [HX1 HX2]. destruct HX1 as [i Hi]. exists i. congruence.
Qed.



(*Complements of a sequence of sets.*)
Definition compl_den {E} (f : nat -> (E -> Prop)) := fun n => (fun x => not ((f n) x)).
(*Complements of a sequence of sets in another set.*)
Definition compl_den_in {E} (f : nat -> (E -> Prop)) (Y : E -> Prop) := fun n => (fun x => (not ((f n) x)) /\ Y x).

(*A few lemmas on sets.*)
Lemma double_subset {E} (X Y : E -> Prop) : subset X Y -> subset Y X -> X = Y.
Proof.
  intros. unfold subset in *. apply set_ext. firstorder.
Qed.
Lemma compl_invol {E} (X : E -> Prop) : compl (compl X) = X.
Proof.
  unfold compl. apply set_ext. intro x. firstorder. apply NNPP. assumption.
Qed.
Lemma compl_in_invol {E} (X : E -> Prop) (Y : E -> Prop) : compl_in (compl_in X Y) Y = inter X Y.
Proof.
  unfold compl_in. apply set_ext. intro x. Search (~ _ /\ _). split.
  - intro H. destruct H as [H1 H2].
    destruct (excluded_middle_informative (X x)).
    + unfold inter ; split ; assumption.
    + exfalso. firstorder.
  - intro H. split.
    + firstorder.
    + unfold inter in H. firstorder.
Qed.

Lemma compl_union {E} (X Y : E -> Prop) : compl (union X Y) = inter (compl X) (compl Y).
Proof.
  unfold compl. unfold union. unfold inter. apply set_ext. intro x. firstorder.
Qed.
Lemma compl_inter {E} (X Y : E -> Prop) : compl (inter X Y) = union (compl X) (compl Y).
Proof.
  unfold compl. unfold union. unfold inter. apply set_ext. intro x. split.
  - intro H. assert (P := not_and_or). specialize (P (X x) (Y x)). apply P in H. assumption.
  - intro H. assert (P := or_not_and). specialize (P (X x) (Y x)). apply P in H. assumption.
Qed.
Lemma compl_union_den {E} (f : nat -> (E -> Prop)) : compl (union_den f) = inter_den (compl_den f).
Proof.
  unfold compl. unfold union_den. unfold inter_den.
  apply set_ext. intro x. unfold compl_den. firstorder.
Qed.
Lemma compl_union_in {E} (X Y : E -> Prop) (Z : E -> Prop) : compl_in (union X Y) Z = inter (compl_in X Z) (compl_in Y Z).
Proof.
  unfold compl_in. unfold union. unfold inter. apply set_ext. intro x. firstorder.
Qed.
Lemma compl_inter_in {E} (X Y : E -> Prop) (Z : E -> Prop) : compl_in (inter X Y) Z = union (compl_in X Z) (compl_in Y Z).
Proof.
  unfold compl_in. unfold union. unfold inter. apply set_ext. intro x. split.
  - intro H. assert (P := not_and_or). specialize (P (X x) (Y x)). destruct H as [H1 H2]. apply P in H1.
    destruct H1 as [H1 | H1].
    + apply or_introl ; split ; assumption.
    + apply or_intror ; split ; assumption.
  - intro H. assert (P := or_not_and). specialize (P (X x) (Y x)). split ; firstorder.
Qed.
Lemma compl_union_den_in {E} (f : nat -> (E -> Prop)) (Z : E -> Prop) :
  compl_in (union_den f) Z = inter_den (compl_den_in f Z).
Proof.
  unfold compl_in. unfold union_den. unfold inter_den. apply set_ext. intro x. unfold compl_den_in.
  split.
  - intro H. destruct H as [H1 H2]. intro n. split.
    + firstorder.
    + assumption.
  - intro H. split. 
    + firstorder.
    + specialize (H 0%nat). destruct H. assumption.
Qed.
Lemma compl_inter_den_in {E} (f : nat -> (E -> Prop)) (Z : E -> Prop) :
  compl_in (inter_den f) Z = union_den (compl_den_in f Z).
Proof.
  unfold compl_in. unfold inter_den. unfold union_den. apply set_ext. intro x.
  unfold compl_den_in. split.
  - intro H. destruct H as [H1 H2]. Print not_ex_all_not. apply (not_all_ex_not _) in H1.
    destruct H1 as [n1 Hn1].
    exists n1. split ; assumption.
  - intro H. destruct H as [n1 H1]. destruct H1 as [H1 H2]. split.
    + apply ex_not_not_all. exists n1. assumption.
    + assumption.
Qed.

(*The two following definitions and the two following lemmas prove that
 we can replace a finite union or intersection by a countable union or intersection.*)
Definition den_union_from_finite {E} (l : list (E -> Prop)) :=
  fun n => nth n l empty_set.
Definition den_inter_from_finite {E} (l : list (E -> Prop)) (X : E -> Prop) :=
  fun n => nth n l X.

Check den_union_from_finite.

Lemma finite_union_is_den {E} (l : list (E -> Prop)) :
  union_den (den_union_from_finite l) = finite_union l.
Proof.
  unfold union_den. unfold finite_union. apply set_ext. intro x.
  split.
  - intro H. destruct H as [n Hn].
    destruct (excluded_middle_informative (n < length l)).
    + exists (nth n l empty_set). split.
      * Search (In (nth _ _ _) ). apply nth_In. assumption.
      * unfold den_union_from_finite in Hn. assumption.
    + exfalso. unfold den_union_from_finite in Hn. Search (nth). rewrite nth_overflow in Hn.
      * exact Hn.
      * lia.
  - intro H. destruct H as [ens [H1 H2]].
    Search (nth). eapply In_nth in H1.
    destruct H1 as [n [H3 H4]].
    exists n. unfold den_union_from_finite. rewrite H4. assumption.
Qed.

Lemma finite_inter_is_den {E} (l : list (E -> Prop)) (X : E -> Prop):
  inter_den (den_inter_from_finite l X) = finite_inter l X.
Proof.
  unfold inter_den. unfold finite_inter.   apply set_ext. intro x.
  split.
  - intro H. split.
    + intro ens. intro H_in. apply (In_nth  l ens X) in H_in.
      destruct H_in as [n Hn]. destruct Hn as [Hn1 Hn2]. unfold den_inter_from_finite in H.
      specialize (H n). rewrite Hn2 in H. assumption.
    + specialize (H (length l)). unfold den_inter_from_finite in H.
      rewrite nth_overflow in H; [assumption | lia].
  - intro H. intro n. unfold den_inter_from_finite.
    destruct (excluded_middle_informative (n < length l)).
    + apply (nth_In l X) in l0.
      unfold inter in H. destruct H as [H H']. specialize (H (nth n l X)).
      apply H in l0. assumption.
    + rewrite nth_overflow.
      * destruct H. assumption.
      * lia.
Qed.

