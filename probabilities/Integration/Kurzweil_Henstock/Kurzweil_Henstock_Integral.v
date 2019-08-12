(*Reals*)
Require Import Rbase.
Require Import Rfunctions.
Require Import Psatz.
(*Require Export SeqSeries.
Require Export Rtrigo.
Require Export Ranalysis.
Require Export Integration.
Require Import Fourier.*)
Open Scope R_scope.


(*Axioms*)
Require Import Classical.
Require Import ClassicalChoice.
Require Import FunctionalExtensionality.
Require Import PropExtensionality.
Require Import Description.
Require Import ClassicalDescription.

(*Lists*)
Require Import List.

(***************)
(*Miscellaneous*)
(***************)

Lemma sup_caract : forall (X : R -> Prop), forall (s : R), is_lub X s <-> (forall epsilon, epsilon > 0 -> exists y, X y /\ s - epsilon < y) /\ is_upper_bound X s.
Proof.
  intros X s. split.
  - intro H. split.
    + intro epsilon. intro H_pos. unfold is_lub in H. Search (~ (forall _, (~ _))).
      apply not_all_not_ex.
      intro H_false. destruct H as [H1 H2].
      unfold is_upper_bound in H2. specialize (H2 (s - epsilon)).
      enough (s <= s - epsilon) by lra.
      apply H2.
      intro x. specialize (H_false x). Search (~ ( _ /\ _)).
      apply not_and_or in H_false. destruct H_false as [H_false | H_false].
      * tauto.
      * lra.
    + unfold is_lub in H. apply H.
  - intros [He H_maj].
    unfold is_lub. split.
    + assumption.
    + intro b. unfold is_upper_bound. intro H.
      clear H_maj.
      apply NNPP. intro H0. specialize (He (s-b)).
      destruct He as [y Hy].
      * lra.
      * specialize (H y). destruct Hy. specialize (H H1). lra.
Qed.

Lemma min_or : forall (x y : R), (Rmin x y) = x \/ (Rmin x y) = y.
Proof.
  intros x y.
  apply Rmin_case ; auto.
Qed.

Lemma le_epsilon_0 : forall (r1 : R), (forall epsilon :R, 0 < epsilon -> r1 <= epsilon) -> r1 <= 0.
Proof.
  intro r1. intro H. apply le_epsilon. intro eps. intro H_ineq.
  specialize (H eps). lra.
Qed.

Lemma Rabs_zero : forall (r : R), Rabs r = 0 -> r = 0.
Proof.
  intros r H.
  apply NNPP. intro H1. apply Rabs_no_R0 in H1. auto.
Qed.

Lemma le_k_epsilon_0 : forall (k : R), forall (r : R), (forall epsilon, 0 < epsilon -> r <= k * epsilon) -> r <= 0.
Proof.
  intros k r. intro H.
  apply le_epsilon_0.
  destruct (excluded_middle_informative (0 < k)).
  - intro eps. intro H_pos_eps. specialize (H (eps/k)).
    replace (k * (eps / k)) with eps in H.
    + assert (0 < eps / k).
      * apply Rinv_0_lt_compat in r0. nra. 
      * auto. 
    + Search ( _ / _). Search (Rinv). Search (Rmult). 
      unfold Rdiv. rewrite <- Rmult_assoc. rewrite Rinv_r_simpl_m. reflexivity. lra.
  - destruct (excluded_middle_informative (0 = k)).
    + intro eps. intro e'. Search ( ~ _ < _). apply Rnot_lt_le in n.
      specialize (H eps e'). nra.
    + exfalso. assert (r < 0).
      * specialize (H 1). nra.
      * specialize (H (2*r/k  )). assert (0 < 2*r/k).
        -- enough (0 < (-r)/(-k)) by ( unfold Rdiv in *; rewrite <- Ropp_inv_permute in H1 ; nra).
           apply Rdiv_lt_0_compat ; nra.
        -- apply H in H1. unfold Rdiv in *. generalize (Rinv_r k). nra.
Qed.



(*Functions*)

Definition sum (f g : R -> R) := fun x => f x + g x.
Definition mult_scalar (f : R -> R) (alpha : R) := fun x => alpha * f x.


(******************************)
(*P-paritions and Riemann sums*)
(******************************)

(*Based on https://dmi.units.it/~fonda/p2017_book_KH.pdf *)

(*We don't care about closed/open intervals*)
Record bounded_interval := mk_bounded_interval {interval_inf : R ; interval_sup : R}.
Definition is_ordered (i : bounded_interval) := i.(interval_inf) <= i.(interval_sup).

Record triplet := mk_triplet {inf_bound : R ; sup_bound : R ; value : R}.
Definition valid_triplet a b t := a = t.(inf_bound) /\ b = t.(sup_bound) /\ a <= t.(value) /\ t.(value) <= b.
Definition partition : Type := list triplet.

Fixpoint is_p_partition (i : bounded_interval) (p : partition) :=
  match p with
  | nil => (i.(interval_inf) = i.(interval_sup))
  | t :: q => (valid_triplet  i.(interval_inf) t.(sup_bound) t) /\
             (is_p_partition {| interval_inf := t.(sup_bound) ; interval_sup := i.(interval_sup)|} q)
  end.

Definition concat_partitions (p1 p2 : partition) := p1 ++ p2.

Lemma is_concat_partition : forall (p1 p2 : partition),  forall (i1 i2 : bounded_interval),
      (is_p_partition i1 p1) -> (is_p_partition i2 p2) -> i1.(interval_sup) = i2.(interval_inf) ->
      (is_p_partition {|interval_inf := i1.(interval_inf) ; interval_sup := i2.(interval_sup) |}
                      (concat_partitions p1 p2)).
Proof.
  induction p1 as [|t1 q1 Hp1].
  - simpl. intro p2. intros i1 i2.
    intros -> H1 -> . destruct i2. simpl. assumption.
  - simpl. intro p2. intros i1 i2. intros [H_triplet H_q1].
    intro H_p2. intro H_int. split.
    + assumption.
    + apply (Hp1 _ _ _ H_q1 H_p2). simpl. assumption.
Qed.


Definition value_triplet_function t f := (f t.(value)) * (t.(sup_bound) - t.(inf_bound)).

Fixpoint riemann_sum_partition (f : R -> R) (p : partition) :=
  match p with
  | nil => 0
  | t :: q => (value_triplet_function t f) +
             (riemann_sum_partition f q)
  end.

Lemma value_triplet_sum (t : triplet) (f g : R -> R) :
  (value_triplet_function t (sum f g)) = (value_triplet_function t f) + (value_triplet_function t g).
Proof.
  unfold value_triplet_function. unfold sum. lra.
Qed.

Lemma riemann_sum_sum  (f g : R -> R) (p : partition) :
  (riemann_sum_partition  (sum f g) p) = (riemann_sum_partition  f p) + (riemann_sum_partition  g p).
Proof.
  induction p as [|t q Hp].
  - simpl. lra.
  - simpl. rewrite Hp. rewrite value_triplet_sum. lra.
Qed.

(******************************)
(*The notion of delta-fineness*)
(******************************)

(*We suppose that I = [a,b].*)
Definition is_gauge (i : bounded_interval) (delta : R -> R) := forall x, i.(interval_inf) <= x -> x <= i.(interval_sup) -> 0 < delta x.

Definition is_delta_fine_triplet (delta : R -> R) (t : triplet) :=
  t.(value) - t.(inf_bound) <= delta t.(value) /\ t.(sup_bound) - t.(value) <= delta t.(value).


Definition is_delta_fine (delta : R -> R) (p : partition) :=
  forall t, In t p -> is_delta_fine_triplet delta t.

Definition is_gauge_finer (delta delta' : R -> R) := forall x, delta x <= delta' x.

Lemma is_delta_fine_concat (delta : R -> R) :
  forall (p1 : partition), is_delta_fine delta p1 -> ( forall (p2 : partition), is_delta_fine delta p2 -> is_delta_fine delta (concat_partitions p1 p2)).
Proof.
  destruct  p1 as [| t1 q1].
  - simpl. intro H. intro p2. firstorder.
  - intro H1. intro p2. intro H_p2. 
    unfold is_delta_fine. intro t. intro H_in.
    apply in_app_or in H_in. destruct H_in as [H_in | H_in].
    + unfold is_delta_fine in H1. specialize (H1 t). apply H1 in H_in. assumption.
    + unfold is_delta_fine in H_p2. specialize (H_p2 t). apply H_p2 in H_in. assumption.
Qed.

Lemma is_finer_triplet : forall (t : triplet), forall (delta delta' : R -> R), (forall x, delta x <= delta' x) -> is_delta_fine_triplet delta t -> is_delta_fine_triplet delta' t.
Proof.
  intro t. intros delta delta'.
  intro H. intro H_fine. unfold is_delta_fine_triplet in *.
  specialize (H (t.(value))). lra.
Qed.


Lemma is_finer : forall (p : partition), forall (delta delta' : R -> R), (is_gauge_finer delta delta') -> is_delta_fine delta p -> is_delta_fine delta' p.
Proof.
  intro p. intros delta delta'. intros H H_fine.
  unfold is_delta_fine in *. intro t. specialize (H_fine t). intro H_t. apply H_fine in H_t.
  eapply is_finer_triplet ; eassumption.
Qed.

(*Let's prove a lemma about the minimum of two gauges, as we use this later*)
Definition min_gauge (delta delta' : R -> R) := fun x => Rmin (delta x) (delta' x).

Lemma min_gauge_is_gauge : forall (delta delta' : R -> R), forall (i : bounded_interval),
      is_gauge i delta -> is_gauge i delta' -> is_gauge i (min_gauge delta delta').
Proof.
  intros delta delta'. intro i.
  intros H_delta H_delta'. unfold is_gauge in *. intro x.
  specialize (H_delta x). specialize (H_delta' x).
  intros H1 H2. unfold min_gauge. apply Rmin_glb_lt ; [apply (H_delta H1) | apply (H_delta' H1)] ; assumption.
Qed.


(*Here is the Cousin's theorem !*)
Theorem arbitrary_fine_partition :
  forall (i : bounded_interval), forall (delta : R -> R), is_gauge i delta -> is_ordered i -> exists (p : partition), is_delta_fine delta p
                                                            /\ is_p_partition i p.
Proof.
  intros i delta. intros H1 H2.
  set (U := (fun x => (exists (p : partition), is_delta_fine  delta p
                                      /\ is_p_partition {|interval_inf := i.(interval_inf) ; interval_sup := x|} p
                                      /\  x <= i.(interval_sup)))).
  assert (U i.(interval_inf)).
  { set (t := {| inf_bound := i.(interval_inf) ; sup_bound := i.(interval_inf) ; value := i.(interval_inf) |}).
    exists (t :: nil). split.
    - simpl. unfold is_delta_fine_triplet. simpl. specialize (H1 i.(interval_inf)).
      unfold is_ordered in H2. intros t1 H_in. simpl in H_in. destruct H_in as [H_in1 | []]. rewrite <- H_in1.
      unfold is_delta_fine_triplet. simpl. lra.
    - simpl. split ; [|exact H2].
      unfold valid_triplet ; simpl. lra.
  }
  assert (is_upper_bound U i.(interval_sup)).
  {
    unfold is_upper_bound. intro x. intro H0. destruct H0 as [p [Hp1 [Hp2 Hp3]]] ; assumption.

  }
  destruct (completeness U) as [sup Hsup].
  - unfold bound. exists i.(interval_sup). assumption.
  - exists i.(interval_inf). assumption.
  - assert (i.(interval_inf) <= sup /\ sup <= i.(interval_sup)).
    {
      split.
      - destruct Hsup as [Hsup1 Hsup2]. apply Hsup1. assumption.
      - destruct Hsup as [Hsup1 Hsup2]. apply Hsup2. assumption.
    }
    rewrite -> sup_caract in Hsup. destruct Hsup as [Hsup1 Hsup2].
    specialize (Hsup1 (delta sup)). destruct Hsup1 as [y Hy].
    {
      apply H1 ; tauto. 
    }
    set (i1 := {| interval_inf := interval_inf i; interval_sup := y |} ).
    set (i2 := {|interval_inf := y ; interval_sup := Rmin (sup + delta sup) (i.(interval_sup))|} ).
    destruct Hy as [Hy1 Hy2]. remember Hy1 as Hy1'. clear HeqHy1'. destruct Hy1 as [p [Hp1 [Hp2 Hp3]]].
    set (t := {|inf_bound := y ; sup_bound := Rmin (sup + (delta sup)) (i.(interval_sup)) ; value := sup |}).
    exists (p ++ (t :: nil)). split.
    + apply is_delta_fine_concat.
      * assumption.
      * unfold is_delta_fine. intro t0. intro H_in_triplet. simpl in H_in_triplet.
        destruct H_in_triplet as [H_in_triplet | H_in_triplet].
        -- unfold is_delta_fine_triplet. split.
           ++ rewrite <- H_in_triplet. simpl. lra.
           ++ rewrite <- H_in_triplet. simpl.
              assert (A := Rmin_l (sup + delta sup) (i.(interval_sup))). lra.
        -- exfalso. assumption. 
    + assert (A1 :is_p_partition i2  (t :: nil)  ).
      { - simpl. split.
          + unfold valid_triplet. simpl. repeat (split ; try lra).
            * apply Hsup2. assumption.
            *  apply Rmin_glb.
              -- specialize (H1 sup). lra.
              -- lra.
          + reflexivity.
      }
      assert (A2 : i1.(interval_sup) = i2.(interval_inf)).
      {
        simpl. reflexivity.
      }
      assert (B := is_concat_partition p (t :: nil) i1 i2 Hp2 A1 A2).
      unfold concat_partitions in B.
      assert (A3 : U (Rmin (sup + delta sup) (i.(interval_sup)))).
      * exists (p ++ t :: nil). split.
        -- apply is_delta_fine_concat. 
           ++ assumption.
           ++ unfold is_delta_fine. intro t0. intro H_temp.
              destruct H_temp.
              ** rewrite <- H4. unfold is_delta_fine_triplet. simpl. split.
                 --- lra.
                 --- assert (D := Rmin_l (sup + delta sup) (i.(interval_sup))). lra.
              ** destruct H4.
        -- split.
           ++ assumption.
           ++ apply Rmin_r. 
      * assert (A4 : Rmin (sup + delta sup) (i.(interval_sup)) = sup).
        -- apply Rle_antisym.
           ++ apply Hsup2. assumption.
           ++ apply Rmin_glb.
              ** specialize (H1 sup). lra.
              ** tauto. 
        -- replace i with {| interval_inf := interval_inf i1; interval_sup := interval_sup i2 |}.
           ++ assumption.
           ++ simpl. rewrite A4. destruct (min_or (sup + delta sup) (i.(interval_sup))) in A4.
              ** rewrite A4 in H4. specialize (H1 sup). exfalso. lra.
              ** rewrite A4 in H4. rewrite H4. destruct i. simpl. reflexivity.
Qed.


(********************************************)
(*Integrable functions on a compact interval*)
(********************************************)

Definition has_integral (f : R -> R) (i : bounded_interval) (A : R) :=
  forall (epsilon : R), 0 < epsilon -> exists (delta : R -> R), is_gauge i delta /\ forall (p : partition), is_delta_fine delta p -> is_p_partition i p -> Rabs (A - (riemann_sum_partition  f p)) <= epsilon.

Definition is_integrable (f : R -> R) (i : bounded_interval) :=
  exists (A : R), has_integral f i A.

Lemma unique_integral (f : R -> R) (i : bounded_interval) :
  (is_ordered i) -> forall (A A' : R), has_integral f i A -> has_integral f i A' -> A = A'.
Proof.
  intro H_order.
  intros A A'. intros HA HA'.
  unfold has_integral in HA. unfold has_integral in HA'.
  assert (forall epsilon, 0 < epsilon -> Rabs (A - A') <= 2 * epsilon).
  - intro eps. intro H_ineq.
    specialize (HA eps). specialize (HA' eps).
    remember H_ineq as H_ineq'. clear HeqH_ineq'.
    apply HA in H_ineq. apply HA' in H_ineq'.
    clear HA HA'.
    destruct H_ineq as [delta H_delta]. destruct H_ineq' as [delta' H_delta'].
    set (delta'' := fun x => Rmin (delta x) (delta' x)).
    assert (is_gauge i delta'').
    + apply min_gauge_is_gauge ; destruct H_delta ; destruct H_delta' ; assumption.
    + assert (E := arbitrary_fine_partition i delta'' H H_order ).
      destruct E as [p [Hp1 Hp2]].
      assert (forall x, delta'' x <= delta x) by (intro x ; apply Rmin_l). 
      assert (forall x, delta'' x <= delta' x) by (intro x ; apply Rmin_r).
      assert (is_delta_fine delta p) by (apply (is_finer p delta'' delta H0 Hp1)).
      assert (is_delta_fine delta' p) by (apply (is_finer p delta'' delta' H1 Hp1)).
      destruct H_delta as [H_delta1 H_delta2].
      destruct H_delta' as [H_delta'1 H_delta'2].
      specialize (H_delta2 p). specialize (H_delta'2 p).
      specialize (H_delta2 H2 Hp2). specialize (H_delta'2 H3 Hp2).
      replace (A - A') with (A -  (riemann_sum_partition f p) + (riemann_sum_partition f p - A')) by lra.
      assert ((Rabs (A - riemann_sum_partition f p + (riemann_sum_partition f p - A'))) <=
              Rabs (A - riemann_sum_partition f p) + Rabs (riemann_sum_partition f p - A'))
             by apply (Rabs_triang). eapply Rle_trans ; [exact H4|]. rewrite Rabs_minus_sym in H_delta'2. lra.
  - assert (Rabs (A - A') = 0).
    + apply le_k_epsilon_0 in H.
      assert (0 <= Rabs (A - A') ).
      * apply (Rabs_pos  (A - A')).
      * lra.
    + assert (A - A' = 0).
      * apply Rabs_zero in H0 ; assumption.
      * lra.
Qed.


(***************************************)
(*Elementary properties of the integral*)
(***************************************)

Lemma sum_integrals :
  forall (i : bounded_interval), forall (f g : R -> R), forall (Lf Lg : R),
        (has_integral f i Lf) -> (has_integral g i Lg) -> (has_integral (sum f g) i (Lf + Lg)).
Proof.
  intro i. intros f g. intros Lf Lg.
  intros Hf Hg. unfold has_integral in *.
  intro eps. intro H_pos_eps.
  specialize (Hf (eps/2)). specialize (Hg (eps/2)).
  assert (H_eq : 0 < eps/2) by lra. 
  remember H_eq as H_eq'. clear HeqH_eq'.
  apply Hf in H_eq. apply Hg in H_eq'. clear Hf Hg.
  destruct H_eq as [delta_f Hf]. destruct H_eq' as [delta_g Hg].
  destruct Hf as [Hf1 Hf2]. destruct Hg as [Hg1 Hg2].
  set (delta := fun x => Rmin (delta_f x) (delta_g x)).
  exists delta. split.
  - apply min_gauge_is_gauge ; assumption.
  - assert (A1 : forall x, delta x <= delta_f x) by (intro x ;apply Rmin_l).
    assert (A2 : forall x, delta x <= delta_g x) by (intro x ; apply Rmin_r).
    intro p. intro H_fine. intro H_part.
    specialize (Hf2 p). specialize (Hg2 p).
    assert (E1 : is_delta_fine delta_f p) by (apply (is_finer p delta delta_f A1 H_fine)).
    assert (E2 : is_delta_fine delta_g p) by (apply (is_finer p delta delta_g A2 H_fine)).
    assert (F1 := Hf2 E1 H_part). assert (F2 := Hg2 E2 H_part).
    rewrite (riemann_sum_sum).
    replace (Lf + Lg - (riemann_sum_partition f p + riemann_sum_partition g p)) with
        ((Lf - riemann_sum_partition f p) + (Lg - riemann_sum_partition g p)) by lra.
    eapply Rle_trans ; [apply Rabs_triang|]. lra.
Qed.

Lemma sum_integrable :
  forall (i : bounded_interval), forall (f g : R -> R), (is_integrable f i) -> (is_integrable g i) ->
                                             (is_integrable (fun x => f x + g x) i).
Proof.
  intro i. intros f g.
  intros Hf Hg.
  unfold is_integrable in *.
  destruct Hf as [Lf Hf]. destruct Hg as [Lg Hg].
  exists (Lf + Lg). apply sum_integrals ; assumption.
Qed.

Lemma mult_by_scalar_integral :
  forall (i : bounded_interval), forall (f : R -> R), forall (Lf : R), forall (alpha : R),
          (has_integral f i Lf) -> (has_integral (mult_scalar f alpha) i (alpha * Lf)).
Proof.
  intro i. intro f. intro Lf. intro alpha.
  intro H.
  
