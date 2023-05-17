(*
Copyright © 2008 Russell O’Connor

Permission is hereby granted, free of charge, to any person obtaining a copy of
this proof and associated documentation files (the "Proof"), to deal in
the Proof without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Proof, and to permit persons to whom the Proof is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Proof.

THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
*)
Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Export CoRN.raster.Raster.
Require Import CoRN.reals.fast.Interval.
Require Export CoRN.metric2.FinEnum.
Require Export CoRN.metric2.ProductMetric.
Require Import CoRN.logic.Classic.

Set Implicit Arguments.
(**
** Rasters on Planes
By attaching coordinates to the top-left and bottom-right corners of
a raster, it can be interpreted as a finite set in [Q]^2. *)
Definition Q2 := (ProductMS Q_as_MetricSpace Q_as_MetricSpace).

(** For [Q2], classical membership in a finite enumeration is the
same as a constructive membership. *)
Lemma InStrengthen : forall x (l:FinEnum Q2),
    InFinEnumC x l -> exists y : Q2, In y l /\ msp_eq x y.
Proof.
 induction l.
 intro abs. exfalso; exact (FinSubset_ball_nil abs).
 intros H.
 assert (L:msp_eq x a \/ ~msp_eq x a).
  destruct (Qeq_dec (fst x) (fst a)).
   destruct (Qeq_dec (snd x) (snd a)).
    left.
    split; apply Qball_0; auto.
   right; intros [_ B].
   apply Qball_0 in B. contradiction.
  right; intros [B _].
   apply Qball_0 in B. contradiction.
 destruct L.
  exists a.
  split; auto with *.
 destruct (IHl) as [y [Hy0 Hy1]].
 apply FinSubset_ball_orC in H.
  destruct H as [G | H | H] using orC_ind.
  intro abs. contradict G; intro G. contradiction.
   elim H0; auto.
   exact H.
 exists y.
 split; auto with *.
Qed.

Definition InterpRow (up : list Q) (v:list bool) : list Q :=
 map (@fst _ _ ) (filter (@snd _ _) (combine up v)).

(* TODO define on sparse rasters directly. *)
Definition CentersOfPixels (n m:positive) (pixels : raster n m) (tl br:Q2)
  : FinEnum Q2 :=
 let (l,t) := tl in
 let (r,b) := br in
 let up := (UniformPartition l r n) in
 flat_map (fun (p:Q*list bool) => let (y,r):=p in map (fun x => (x,y)) (InterpRow up r))
          (combine (UniformPartition t b m) (let (d):=pixels in d)).

(** Notation for the interpretation of a raster. *)
Notation "a ⇱ b ⇲ c" := (CentersOfPixels b a c) (at level 1,
 format "a ⇱ '[v' '/' b ']' '[v' '/' ⇲ c ']'") : raster.

(*
Local Open Scope raster.
Local Open Scope raster_parsing.

Example ex5 :=
(0, 1)⇱
         ⎥█░█⎢
         ⎥░█░⎢
         ⎥░░█⎢
             ⇲(1, 0).

Eval compute in (ex5).
*)

Lemma In_map_snd_const
  : forall A (v : list A) f (a b : Q),
    In a (map f v)
    -> In (a,b) (map (fun x => (f x, b)) v).
Proof.
  induction v.
  - intros. contradiction H.
  - intros. simpl. destruct H.
    subst a0. left. reflexivity.
    right. apply IHv, H.
Qed.

Lemma In_filtered_list
  : forall (l : list Q) (q : Q) (filterList : list bool) (j : nat),
    (length filterList <= length l)%nat
    -> Is_true (nth j filterList false)
    -> In (nth j l q)
         (map fst (filter snd (combine l filterList))).
Proof.
  induction l.
  - intros. destruct filterList. 2: exfalso; inversion H.
    exfalso. simpl in H0. destruct j; contradiction.
  - intros. destruct filterList.
    destruct j; contradiction.
    simpl in H. apply le_S_n in H.
    simpl. destruct j.
    + simpl in H0. destruct b. 2: contradiction.
      left. reflexivity.
    + destruct b.
      right. exact (IHl q _ _ H H0).
      exact (IHl q _ _ H H0).
Qed.

Lemma In_filter_list
  : forall (filterList : list bool) (j : nat),
    Is_true (nth j filterList false)
    -> (j < length filterList)%nat.
Proof.
  induction filterList.
  - intros. destruct j; contradiction.
  - intros. destruct j. simpl. apply le_n_S, Nat.le_0_l.
    simpl. apply le_n_S. apply IHfilterList, H.
Qed.

Lemma Vector_bool_in
  : forall (v : list bool) j,
    Is_true (nth j v false) -> (j < length v)%nat.
Proof.
  induction v.
  - intros j H. destruct j; contradiction H.
  - intros j H. simpl in H.
    destruct j. apply le_n_S, Nat.le_0_l.
    simpl. apply le_n_S, IHv, H.
Qed.

Lemma RasterIndex_in
  : forall m n i j (r : raster n m),
    raster_well_formed r ->
    Is_true (RasterIndex r i j) -> (i < Pos.to_nat m /\ j < Pos.to_nat n)%nat.
Proof.
  intros. destruct r as [l].
  destruct H. rewrite <- H.
  simpl in H0.
  clear H m.
  simpl in H0.
  revert H0. revert i j. induction l as [|a l].
  - intros. exfalso. simpl in H0.
    destruct i; destruct j; contradiction.
  - intros.
    inversion H1. subst l0. subst x. clear H1.
    specialize (IHl H4).
    destruct i.
    + split. apply le_n_S, Nat.le_0_l.
      apply Vector_bool_in in H0.
      rewrite <- H3. exact H0.
    + specialize (IHl i j H0).
      split. apply le_n_S, IHl. apply IHl.
Qed.

(** Correctness properties of our interpretation. *)
Section InterpRasterCorrect.

Let f := fun l r (n:positive) (i:Z) => l + (r - l) * (2 * i + 1 # 1) / (2 * Zpos n # 1).

Lemma InterpRaster_correct1
  : forall n m (t l b r:Q) (bitmap: raster n m) i j,
    raster_well_formed bitmap
    -> Is_true (RasterIndex bitmap i j)
    -> In (f l r n (Z.of_nat j), f t b m (Z.of_nat i))
         (CentersOfPixels bitmap (l,t) (r,b)).
Proof.
  intros n m t l b r bitmap.
  unfold CentersOfPixels, InterpRow, UniformPartition.
  fold (f l r n).
  fold (f t b m).
  generalize (f l r n) (f t b m).
  clear t l b r f.
  unfold RasterIndex.
  intros.
  pose proof (RasterIndex_in i j _ H H0) as [iin jin]. 
  destruct bitmap as [bitmap], H.
  apply in_flat_map.
  exists (nth i (map q0 (iterateN_succ 0 m)) (q0 0%Z), nth i bitmap nil).
  split.
  - rewrite <- (combine_nth (map q0 (iterateN_succ 0 m)) bitmap i (q0 0%Z) nil).
    apply nth_In.
    rewrite combine_length, map_length, iterateN_succ_length.
    apply Nat.min_case. exact iin.
    rewrite H. exact iin.
    rewrite map_length, iterateN_succ_length, H.
    reflexivity.
  - rewrite map_map.
    replace (q0 (Z.of_nat i))
      with (nth i (map q0 (iterateN_succ 0 m)) (q0 0%Z)).
    apply In_map_snd_const.
    replace (q (Z.of_nat j))
      with (nth j (map q (iterateN_succ 0 n)) (q 0%Z)).
    apply In_filtered_list. 
    2: exact H0.
    rewrite map_length, iterateN_succ_length.
    rewrite Forall_forall in H1.
    rewrite (H1 (nth i bitmap nil)).
    apply Nat.le_refl.
    apply nth_In. rewrite H. exact iin.
    rewrite map_nth. apply f_equal.
    apply iterateN_succ_nth, jin.
    rewrite map_nth. apply f_equal.
    apply iterateN_succ_nth, iin.
Qed.

Lemma InterpRaster_correct2 : forall n m (t l b r:Q) x y (bitmap: raster n m),
raster_well_formed bitmap ->
In (x,y) (CentersOfPixels bitmap (l,t) (r,b)) ->
exists p, Is_true (RasterIndex bitmap (fst p) (snd p)) /\ x=f l r n (Z.of_nat (snd p))
     /\ y=f t b m (Z.of_nat (fst p)).
Proof.
 intros n m t l b r x y bitmap.
 unfold CentersOfPixels, InterpRow, UniformPartition.
 fold (f l r n).
 fold (f t b m).
 generalize (f l r n) (f t b m).
 clear t l b r f.
 intros q q0 wf H. apply in_flat_map in H.
 destruct H as [[s v] [H H0]].
 destruct bitmap as [bitmap]. simpl.
 destruct wf.
 apply In_nth with (d:=(q0 0%Z, nth 0 bitmap nil)) in H.
 destruct H as [i [ilt H]].
 rewrite combine_length, map_length, iterateN_succ_length in ilt.
 assert (i < Pos.to_nat m)%nat.
 { apply (Nat.lt_le_trans _ _ _ ilt), Nat.le_min_l. }
 clear ilt.
 rewrite combine_nth in H.
 2: rewrite map_length, iterateN_succ_length, H1; reflexivity.
 inversion H. clear H. subst s. subst v. simpl in H0.
 rewrite map_map in H0.
 apply in_map_iff in H0.
 destruct H0 as [[s b] [H H0]].
 unfold fst in H.
 inversion H. clear H.
 subst s. clear H6 y.
 apply filter_In in H0.
 destruct H0. unfold snd in H0. subst b.
 apply In_nth with (d:= (q 0%Z,true)) in H.
 destruct H as [j [jlt H]].
 rewrite Forall_forall in H2. 
 rewrite combine_nth in H.
 inversion H. clear H H4 x.
 rewrite combine_length, map_length, iterateN_succ_length in jlt.
 assert (j < Pos.to_nat n)%nat.
 { apply (Nat.lt_le_trans _ _ _ jlt). apply Nat.le_min_l. }
 clear jlt.
 exists (i,j). split.
 - simpl.
   rewrite (nth_indep _ false true). 
   rewrite (nth_indep _ nil (nth 0 bitmap nil)). 
   unfold Is_true. rewrite H5. trivial.
   rewrite H1. exact H3.
   rewrite H2. exact H.
   apply nth_In. rewrite H1. exact H3.
 - simpl. split.
   rewrite map_nth.
   apply f_equal.
   apply iterateN_succ_nth.
   exact H.
   rewrite map_nth.
   apply f_equal.
   apply iterateN_succ_nth, H3.
 - rewrite map_length, iterateN_succ_length.
   rewrite H2. reflexivity.
   apply nth_In. rewrite H1. exact H3.
Qed.

End InterpRasterCorrect.
(* begin hide *)
Add Parametric Morphism n m (bm:raster n m) (bmWf : raster_well_formed bm)
  : (@CentersOfPixels n m bm)
    with signature (@msp_eq _) ==> (@msp_eq _) ==> (@msp_eq _) as InterpRaster_wd.
Proof.
 cut (forall (x1 x2 : Q2), msp_eq x1 x2 -> forall x3 x4 : Q2,
   msp_eq x3 x4 -> forall y,
     InFinEnumC y (CentersOfPixels bm x1 x3) ->
       InFinEnumC y (CentersOfPixels bm x2 x4)).
 { intro L. split. discriminate. split.
   intros q H1 abs.
   contradiction (abs q). split. exact (L x y H x0 y0 H0 q H1).
   reflexivity.
   intros q H1 abs.
   contradiction (abs q). split.
   symmetry in H, H0.
   exact (L y x H y0 x0 H0 q H1).
   reflexivity. }
 intros [x1l x1r] x2 Hx [y1l y1r] y2 Hy z Hz.
 destruct (@InStrengthen _ _ Hz) as [[ax ay] [Ha0 Ha1]].
 destruct (InterpRaster_correct2 _ _ _ _ _ _ _ bmWf Ha0)
   as [[bx by'] [Hb0 [Hb1 Hb2]]].
 rewrite Hb1 in Ha1.
 rewrite Hb2 in Ha1.
 unfold snd, fst in Ha1.
 destruct x2 as [x2l x2r].
 destruct y2 as [y2l y2r].
 assert (L0:msp_eq z ((x2l + (y2l - x2l) * (2 * Z.of_nat by' + 1 # 1) / (2 * Zpos n # 1)),
   (x2r + (y2r - x2r) * (2 * Z.of_nat bx + 1 # 1) / (2 * Zpos m # 1)))).
  transitivity ((x1l + (y1l - x1l) * (2 * Z.of_nat by' + 1 # 1) / (2 * Zpos n # 1)),
    (x1r + (y1r - x1r) * (2 * Z.of_nat bx + 1 # 1) / (2 * Zpos m # 1))).
   auto.
  clear - Hx Hy.
  destruct Hx as [Hx1 Hx2].
  destruct Hy as [Hy1 Hy2].
  split; unfold fst,snd in *.
  apply Qball_0 in Hx1.
  apply Qball_0 in Hy1.
   rewrite -> Hx1, Hy1.
   reflexivity.
  apply Qball_0 in Hx2.
  apply Qball_0 in Hy2. 
  rewrite -> Hx2, Hy2.
  reflexivity.
  unfold InFinEnumC.
  rewrite -> (@FinSubset_ball_wd _ z _ 0 0 
                                (CentersOfPixels bm (x2l, x2r) (y2l, y2r))
                                (reflexivity _) L0).
 apply InFinEnumC_weaken.
 auto using InterpRaster_correct1.
Qed.
(* end hide *)
