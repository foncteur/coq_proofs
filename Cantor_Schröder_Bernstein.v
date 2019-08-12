Require Import Classical.
Require Import ClassicalChoice.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Require Import Description.
Require Import ClassicalDescription.



Lemma set_ext {E} :
  forall (A B : E -> Prop), (forall x, A x <-> B x) -> A = B.
Proof.
  intros A B. intro H.
  extensionality x. apply propositional_extensionality.
  destruct (H x). split ; assumption.
Qed.

Definition compl {E} (A : E -> Prop) := (fun x => ~ (A x)).

Definition subset {E} (A B : E -> Prop) := forall x, (B x) -> (A x).
Check subset.

Lemma compl_decreasing {E} : forall X Y : E -> Prop, subset X Y -> subset (compl Y) (compl X).
Proof.
  firstorder.
Qed.
(*intros X Y. intro H. unfold subset in *. unfold compl. intro x. specialize (H x). tauto. *)

Definition union {E} (A B : E -> Prop) := (fun x => (A x) \/ (B x)).
Definition union_gen {E} (X : (E -> Prop) -> Prop) := (fun x => exists A, X A /\ A x).
Check union_gen. 


Definition set_of_subsets {E} (A : E -> Prop) := (fun x => (subset A x)).
Definition image_set {E F} (f : E -> F) (A : E -> Prop) := (fun y => (exists x, (A x) /\ (f x) = y)).
Definition pre_image {E F} (f : E -> F) (B : F -> Prop) := (fun x => B (f x)).



Lemma image_increasing {E F} : forall X Y : E -> Prop, forall f : E -> F, subset X Y -> subset (image_set f X) (image_set f Y).
Proof.
  firstorder.
Qed.

Definition inj {E F} (f : E -> F) := forall x y, f x = f y -> x = y.
Definition surj {E F} (f : E -> F) := forall y, exists x, f x = y.
Definition bij {E F} (f : E -> F)  := (inj f) /\ (surj f).

Definition is_recip {E F} (f : E -> F) (g : F -> E) :=
  (forall x, (g (f x)) = x) /\ (forall y, (f (g y)) = y).

Lemma bij_exists_recip {E F} (f : E -> F) :
  (bij f) -> exists (g : F -> E), (is_recip f g).
Proof.
  intro H. unfold bij in H. destruct H as [H1 H2].
  unfold surj in H2.
  assert (exists g, forall x, x = f (g x)).
  - apply unique_choice with (R := fun x gx => x = f gx).
    intro y. destruct (H2 y). exists x. unfold unique. split.
    + symmetry ; assumption.
    + intro x'. intro H0. symmetry in H.
      unfold inj in H1. destruct (H1 x x').
      * rewrite <- H. rewrite H0. reflexivity.
      * reflexivity.
  - destruct H as [g0]. exists g0.
    unfold is_recip. split.
    + intro x. unfold inj in H1. destruct (H1 x (g0 (f x))).
      * rewrite <- H. reflexivity.
      * reflexivity.
    + intro y. symmetry. rewrite <- H. reflexivity.
Qed.

Lemma is_in_image {E F} (f : E -> F) (A : E -> Prop) (x : E) : (A x) -> (image_set f A) (f x).
Proof.
  intro H. unfold image_set. exists x. split ; [assumption |reflexivity].
Qed.

Lemma is_in_image_all {E F} (f : E -> F) (x : E) : image_set f (fun _ => True) (f x).
Proof.
  apply is_in_image. constructor.
Qed.


Definition is_fixpoint {E} (f : (E -> Prop) -> (E -> Prop)) (A : E -> Prop) := f A = A.
Definition is_increasing {E} (f : (E -> Prop) -> (E -> Prop)) := forall X Y, subset X Y -> subset (f X) (f Y).
Check is_increasing.

Lemma union_increasing {E} (f : (E -> Prop) -> (E -> Prop)) :
  is_increasing f -> forall A, subset (f (union_gen A)) (union_gen (image_set f A)).
Proof.
  intro H_inc. intro A. intro x. intro Hx.
  unfold union_gen in *.
  destruct Hx as [A0 [H1 H2]]. unfold image_set in H1. destruct H1 as [A1 [ H3 H4]].
  apply (H_inc _  A1).
  - intro x'. intro H0.
    exists A1. split ; assumption.
  - rewrite H4 ; assumption.
Qed.


Lemma proj1_inj : forall (E : Type) (P : E -> Prop) (x y : sig P), proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros E P x y. intro H_eq.
  destruct x as [x Px]. destruct y as [y Py]. simpl in H_eq.
  subst. f_equal. apply proof_irrelevance.
Qed.


Lemma bij_on_image {E F : Type} (h : E -> F)  :
  (inj h) -> bij (fun x => exist (image_set h (fun _ => True)) (h x) (is_in_image_all h x)).
Proof.
  intro H_inj. unfold bij. split.
  - unfold inj.
    intros x y H_eq.
    injection H_eq. apply H_inj.
  - unfold surj. intro y. destruct y as [y Py]. destruct Py as [x Hx].
    exists x. apply proj1_inj. simpl. apply Hx.
Qed.


Definition potential_fixpoint {E} (f : (E -> Prop) -> (E -> Prop)) := union_gen (fun A => (subset (f A) A)).

Lemma first_inclusion {E} (f : (E -> Prop) -> ( E -> Prop)) :
  (is_increasing f) -> subset (f (potential_fixpoint f)) (potential_fixpoint f).
Proof.
  intros H_inc x H.
  unfold potential_fixpoint in *. apply union_increasing.
  - exact H_inc.
  - unfold union_gen in H. destruct H as [A [H0]].
    unfold union_gen. exists (f A). unfold image_set. split.
    + exists A. split.
      * assumption.
      * reflexivity.
    + apply H0 ; assumption.
Qed.

Lemma second_inclusion {E} (f : (E -> Prop) -> (E -> Prop)) :
  (is_increasing f) -> subset (potential_fixpoint f) (f (potential_fixpoint f)).
Proof.
  intros H_inc x H.
  assert (subset (f (f (potential_fixpoint f))) (f (potential_fixpoint f))).
  - apply H_inc. apply first_inclusion. assumption.
  - unfold potential_fixpoint. unfold union_gen. exists (f (potential_fixpoint f)).
    split ; assumption.
Qed.

Lemma exists_fixpoint {E} (f : ((E -> Prop) -> (E -> Prop))) :
  (is_increasing f) -> exists U, (is_fixpoint f U). 
Proof.
  intro H_inc. exists (potential_fixpoint f). unfold is_fixpoint.
  apply set_ext. intro x. split.
  - apply second_inclusion ; assumption.
  - apply first_inclusion ; assumption.
Qed.

Definition interesting_function {E F} (f : E -> F) (g : F -> E) (X : E -> Prop) :=
  compl (image_set g (compl (image_set f X))).


Theorem Cantor_Schröder_Bernstein {E F} (f : E -> F) (g : F -> E) :
  (inj f) -> (inj g) -> exists h : E -> F, bij h.
Proof.
  intros Hf Hg. assert (exists U, is_fixpoint (interesting_function f g) U).
  {
    apply exists_fixpoint. intros X Y. intro H. apply compl_decreasing.
    apply image_increasing. apply compl_decreasing. apply image_increasing. assumption.
  }
  destruct H as [U Hu].
  assert (Hg2 := bij_on_image g Hg).
  apply bij_exists_recip in Hg2. destruct Hg2 as [g' [Hg'1 Hg'2]].
  assert (H_excl_mid : forall x, ~ (U x) -> image_set g (fun _ => True) x).
  - intros x H. unfold is_fixpoint in Hu. rewrite <- Hu in H.
    unfold interesting_function in H.
    apply NNPP in H.
    destruct H as [y Py]. exists y ; tauto.
  - exists (fun x => match (excluded_middle_informative (U x)) with | left _ => (f x) | right H => g' (exist _ x (H_excl_mid x H)) end).
    split.
    + intros x y.
      destruct (excluded_middle_informative (U x)) as [Hx | Hx] ; destruct (excluded_middle_informative (U y)) as [Hy | Hy].
      * apply Hf.
      * intro H_eq. exfalso.
        assert (H_eq2 := f_equal g H_eq).
        specialize (Hg'2 (exist (image_set g (fun _ => True)) y (H_excl_mid y Hy))).
        injection Hg'2. intro H_eq3. rewrite H_eq3 in H_eq2.
        clear Hg'2 H_eq H_eq3.
        rewrite <- H_eq2 in Hy.
        unfold is_fixpoint in Hu. rewrite <- Hu in Hy. unfold interesting_function in Hy.
        apply NNPP in Hy. destruct Hy as [z [Hz1 Hz2]].
        apply Hg in Hz2. apply Hz1. exists x. split.
        -- assumption.
        -- symmetry ; assumption.
      *  intro H_eq. exfalso.
        assert (H_eq2 := f_equal g H_eq).
        specialize (Hg'2 (exist (image_set g (fun _ => True)) x (H_excl_mid x Hx))).
        injection Hg'2. intro H_eq3. rewrite H_eq3 in H_eq2.
        clear Hg'2 H_eq H_eq3.
        rewrite H_eq2 in Hx.
        unfold is_fixpoint in Hu. rewrite <- Hu in Hx. unfold interesting_function in Hx.
        apply NNPP in Hx. destruct Hx as [z [Hz1 Hz2]].
        apply Hg in Hz2. apply Hz1. exists y. split.
        -- assumption.
        -- symmetry ; assumption.
      * intro H_eq.
        assert (H_eq2 := f_equal (fun z => exist (image_set g (fun _ => True)) (g z) (is_in_image_all g z)) H_eq). simpl in H_eq2. rewrite !Hg'2 in H_eq2. injection H_eq2. tauto.
    + intro y.
      destruct (excluded_middle_informative (image_set f U y)) as [Hy | Hy].
      * destruct Hy as [x [Hx1 Hx2]].
        exists x. destruct (excluded_middle_informative (U x)).
        -- assumption.
        -- exfalso. tauto.
      * exists (g y). destruct (excluded_middle_informative (U (g y))) as [Hgy | Hgy].
        -- exfalso.
           unfold is_fixpoint in Hu. rewrite <- Hu in Hgy.
           unfold interesting_function in Hgy.
           apply Hgy. exists y. split.
           ++ exact Hy.
           ++ reflexivity.
        -- rewrite <- Hg'1. f_equal. apply proj1_inj. simpl. reflexivity.
Qed.
