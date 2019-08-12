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


(*Here, we try to formalize the topology lesson here :
http://perso.eleves.ens-rennes.fr/~tpier758/cours/topo.pdf
 *)



(***********************************)
(*Topological spaces, metric spaces*)
(***********************************)

(*Topological spaces : generalities*)

(*Topological spaces*)


Definition is_topo {E} (X : E -> Prop) (T : (E -> Prop) -> Prop) :=
  T empty_set /\
  T X /\
  (forall (l : list (E -> Prop)), (forall x, In x l -> T x) -> T (finite_inter l X)) /\
  forall (A : (E -> Prop) -> Prop), (forall X, A X -> T X) -> T (union_gen A).

Definition is_open {E} (T : (E -> Prop) -> Prop) o :=
  T o.

Definition is_finer_than {E} (X : E -> Prop) (T1 T2 : (E -> Prop) -> Prop) :=
  subset T1 T2.

(*Notion of neighborhood*)

Definition is_neighbh {E} (X : E -> Prop) (T : (E -> Prop) -> Prop) (x : E) (V : E -> Prop) :=
  subset V X /\ exists o, is_open T o /\ o x /\ subset o V.

Definition neigbh_sets {E} (X : E -> Prop) (T : (E -> Prop) -> Prop) x  := fun A => (is_neighbh X T x A).

Lemma bigger_is_neibgh {E} (X : E -> Prop) (T : (E -> Prop) -> Prop) (V V' : E -> Prop) x :
  (is_neighbh X T x V) -> subset V V'-> subset V' X -> (is_neighbh X T x V').
Proof.
  intros. unfold is_neighbh in *. split.
  - assumption.
  - destruct H.  destruct H2 as [o Ho]. exists o. firstorder.
Qed.

Lemma finite_inter_is_neibh {E} (X : E -> Prop) (T : (E -> Prop) -> Prop) x l :
  is_topo X T -> X x -> (forall V, In V l -> is_neighbh X T x V) -> (is_neighbh X T x (finite_inter l X)).
Proof.
  intros. induction l as [|t q Hind].
  - unfold finite_inter.  unfold is_neighbh. split.
    + unfold subset. intros. destruct H2. assumption.
    + exists X. split ; [|split].
      * unfold is_topo in H. destruct H as [Hyp1 [Hyp2 [ Hyp3 Hyp4]]].
        apply Hyp2.
      * assumption.
      * firstorder.
  - unfold is_neighbh. split.
    + unfold subset. intros. unfold finite_inter in H2. firstorder.
    + assert (H2 := H1 t).
      destruct H2 as  [L1 L2]. { firstorder. }
                               destruct Hind.
      * intro V. intro H'. apply H1. simpl. right. assumption.
      * destruct H3 as [o H']. destruct L2 as [o' H''].
        exists (inter o o'). split.
        -- replace (inter o o') with (finite_inter (o::o'::nil) X).
           ++ apply H. intro x0. simpl. intros [<- | [<- | []]]. apply H'. apply H''.
           ++ apply set_ext. intro x0. firstorder congruence.
        -- firstorder congruence.
Qed.

Theorem caract_open_neibh {E} (X : E -> Prop) (T : (E -> Prop) -> Prop) o :
  is_topo X T -> subset o X -> ( (is_open T o) <-> (forall x, (o x -> (is_neighbh X T x o)))).
Proof.
  intros H H'. split.
  - intro H_open. intro x. intro H1.
    unfold is_neighbh. split.
    + exact H'.
    + exists o. split.
      * exact H_open.
      * split.
        -- exact H1.
        -- firstorder.
  - intro Hyp.
    assert (forall x : sig o, exists o', is_open T o' /\  o' (proj1_sig x) /\ subset o' o ).
    + intro x. specialize (Hyp (proj1_sig x)).
      specialize (Hyp (proj2_sig x)).
      unfold is_neighbh in Hyp. destruct Hyp as [Hyp1 Hyp2].
      assumption.
    + apply choice in H0.
      destruct H0 as [f H0].
      assert (o = union_ind f).
      * apply set_ext. intro x. split.
        -- intro H1. unfold union_ind. exists (exist _ x H1).
           specialize (H0 (exist _ x H1)). apply H0.
        -- intro Hu. unfold union_ind in Hu. destruct Hu as [n Hu].
           destruct (H0 n) as [H1 [H2 H3]]. apply H3. assumption.
      * rewrite H1. rewrite union_gen_is_ind.
        apply H. intro X0. intro H''.
        destruct H''. specialize (H0 x). rewrite <- H2. apply H0.
Qed.
