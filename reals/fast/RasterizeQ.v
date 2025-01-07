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
From Coq Require Import ZArith.
Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Export CoRN.reals.fast.RasterQ.
Require Import CoRN.reals.fast.Interval.
Require Import CoRN.logic.Classic.
Require Import CoRN.model.totalorder.QposMinMax.
From Coq Require Import Qabs.
From Coq Require Import Qround.

Local Open Scope Q_scope.

Set Implicit Arguments.

(**
** Rasterization
Rasterization takes finite enumeration of points in [Q2] and moves them
around a little so that they lie on a raster.  Thus rasterization produces
a raster object that when interpreted as a finite enumeration of [Q2] is
close to the original enumeration of points.  How close depends on how
fine a raster is chosen.

There is a choice as to how to treat points that lie outside of the bound
of a chosen rectangle for rasterization.  In this implemenation I choose
to push all points inside the raster.  In typical applications a rectangle
is chosen that contains all the points, so that this doesn't matter. *)

(* [Rasterize Point] adds a single point [p] into a raster.
The raster is inside the rectanle t l b r, meaning top, left, bottom and right.
It has n points horizontally and m points vertically. The indexes (0,0)
correspond to the point (l,t) ie the top left corner. That yields the correct
printing order of the raster, which is a vector of lines. *)
Definition rasterize2 (n m:positive) (t l b r:Q) (p:Q*Q) : Z*Z
  := pair (Zpos m -1 - (Z.min (Zpos m -1) (Z.max 0 (rasterize1 b t m (snd p)))))%Z
          (Z.min (Zpos n -1) (Z.max 0 (rasterize1 l r n (fst p)))).
           
Lemma rasterize2_bound :
  forall n z, (0 <= Z.min (Zpos n -1) (Z.max 0 z) < Zpos n)%Z.
Proof.
  split.
  - apply Z.min_case.
    apply Z.le_0_sub, Pos.le_1_l.
    apply Z.le_max_l.
  - apply (Z.le_lt_trans _ _ _ (Z.le_min_l _ _)).
    rewrite <- (Z.add_0_r (Z.pos n)) at 2.
    apply Z.add_lt_mono_l. reflexivity.
Qed. 

Lemma rasterize1_origin : forall l r n, rasterize1 l r n l = 0%Z.
Proof.
  intros.
  unfold rasterize1.
  unfold Qminus.
  rewrite Qplus_opp_r, Qmult_0_r.
  unfold Qdiv. rewrite Qmult_0_l.
  reflexivity.
Qed.

Lemma rasterize2_origin
  : forall n m (t l b r : Q),
    b < t -> rasterize2 n m t l b r (pair l t) = pair 0%Z 0%Z.
Proof.
  assert (forall n:positive, 0 <= Zpos n -1)%Z.
  { intro n.
    change 0%Z with (1-1)%Z.
    apply Z.add_le_mono_r.
    apply Pos.le_1_l. }
  intros. unfold rasterize2, fst, snd.
  rewrite rasterize1_origin.
  replace (rasterize1 b t m t) with (Zpos m)%Z.
  change (Z.max 0 0) with 0%Z.
  rewrite Z.max_r. 2: discriminate.
  rewrite Z.min_l.
  rewrite Z.min_r.
  rewrite Z.sub_diag. reflexivity.
  apply H.
  rewrite <- (Z.add_0_r (Zpos m)) at 2.
  apply Z.add_le_mono_l. discriminate.
  unfold rasterize1.
  unfold Qdiv.
  rewrite <- Qmult_assoc, Qmult_inv_r, Qmult_1_r.
  rewrite Qfloor_Z. reflexivity.
  intro abs. apply Qlt_minus_iff in H0.
  unfold Qminus in abs. rewrite abs in H0.
  exact (Qlt_irrefl 0 H0).
Qed.

(* Adding a point to a raster preserves all the points that were
   already in it. *)
Lemma setRaster_carry : forall l r n m (bm:raster n m) i j,
    raster_well_formed bm
    -> Is_true (RasterIndex bm i j)
    -> Is_true (RasterIndex (setRaster bm true l r) i j).
Proof.
 intros l r m n bm i j rWf H.
 destruct (le_lt_dec (Pos.to_nat n) l).
  rewrite setRaster_overflow; auto.
 destruct (le_lt_dec (Pos.to_nat m) r).
  rewrite setRaster_overflow; auto.
 destruct (eq_nat_dec i l).
  destruct (eq_nat_dec j r).
   rewrite e, e0.
   rewrite setRaster_correct1; try constructor; congruence.
  rewrite setRaster_correct2; auto.
 rewrite setRaster_correct2; auto.
Qed.

Lemma setRaster_uncarry : forall n m (r:raster n m) i j ax ay,
    raster_well_formed r
    -> Is_true (RasterIndex (setRaster r true ax ay) i j)
    -> (Is_true (RasterIndex r i j) \/ (ax, ay) = (i,j)).
Proof.
  intros.
  destruct (Nat.eq_dec ax i).
  - destruct (Nat.eq_dec ay j).
    right. f_equal; assumption.
    left.
    rewrite (setRaster_correct2 r) in H0.
    exact H0. exact H.
    right. intro abs. subst j. contradiction.
  - left.
    rewrite (setRaster_correct2 r) in H0.
    exact H0. exact H.
    left. intro abs. subst i. contradiction.
Qed.

(* Sparse rasters are faster than boolean matrices when the number of
   points to plot is small with respect to the total number of pixels.
   Each lit pixel of a sparse raster stores 2 positive numbers. For
   a 1000x1000 image that's 20 allocations per pixel instead of 1
   allocation for boolean matrices. *)
Variant sparse_raster (columns lines : positive) : Set :=
| sparse_raster_data : list (Z*Z) -> sparse_raster columns lines. 

(** This function is slow to compute in Coq.
    It is faster to plot a sparse raster with DumpGrayMap. *)
Definition PixelizeQ2 {columns lines:positive} (points:sparse_raster columns lines)
  : raster columns lines :=
  fold_left (fun (rast:raster columns lines) (p:Z*Z)
             => setRaster rast true (Z.to_nat (fst p)) (Z.to_nat (snd p)))
            (let (p) := points in p)
            (emptyRaster columns lines).

Definition RasterizeQ2 (points:list Q2) (n m:positive) (t l b r:Q)
  : sparse_raster n m :=
  sparse_raster_data n m (map (fun p => rasterize2 n m t l b r p) points).

Lemma RasterizeQ2_wf : forall points n m t l b r,
    raster_well_formed (PixelizeQ2 (RasterizeQ2 points n m t l b r)).
Proof.
  intros. unfold PixelizeQ2, RasterizeQ2.
  pose proof (emptyRaster_wf n m).
  revert H. generalize (emptyRaster n m).
  induction points.
  - intros. exact H.
  - intros. simpl. apply IHpoints.
    apply setRaster_wf, H.
Qed.

Lemma RasterizeQ2_in : forall points (i j : Z) n m (r:raster n m),
    In (i,j) points
    -> raster_well_formed r
    -> (Z.to_nat i < Pos.to_nat m)%nat
    -> (Z.to_nat j < Pos.to_nat n)%nat
    -> Is_true (RasterIndex
                 (fold_left (fun (rast:raster n m) (p:Z*Z)
                 => setRaster rast true (Z.to_nat (fst p)) (Z.to_nat (snd p)))
                points r)
                 (Z.to_nat i) (Z.to_nat j)).
Proof.
  assert (forall points i j n m (r:raster n m),
    Is_true (RasterIndex r (Z.to_nat i) (Z.to_nat j))
    -> raster_well_formed r
    -> Is_true (RasterIndex
                 (fold_left (fun (rast:raster n m) (p:Z*Z)
                 => setRaster rast true (Z.to_nat (fst p)) (Z.to_nat (snd p)))
                points r)
                 (Z.to_nat i) (Z.to_nat j))).
  { induction points.
    - intros. exact H.
    - intros. simpl. apply IHpoints.
      apply setRaster_carry. exact H0. exact H.
      apply setRaster_wf, H0. }
  induction points.
  - intros. exfalso. inversion H0.
  - intros. simpl. destruct H0.
    + subst a. simpl.
      apply H. apply Is_true_eq_left, setRaster_correct1.
      exact H1. exact H2. exact H3.
      apply setRaster_wf, H1.
    + apply IHpoints. exact H0.
      apply setRaster_wf, H1.
      exact H2. exact H3.
Qed.

Lemma RasterizeQ2_in_recip : forall (points : list (Z*Z)) (i j : nat) n m (r:raster n m),
    raster_well_formed r
    -> Is_true (RasterIndex
                 (fold_left (fun (rast:raster n m) (p:Z*Z)
                 => setRaster rast true (Z.to_nat (fst p)) (Z.to_nat (snd p)))
                points r) i j)
    -> (In (i, j) (map (fun p => (Z.to_nat (fst p), Z.to_nat (snd p))) points)
       \/ Is_true (RasterIndex r i j)).
Proof.
  induction points as [|[ax ay] points].
  - intros. right. exact H0.
  - intros. simpl in H0.
    destruct (RasterIndex r i j) eqn:des.
    right. reflexivity. left.
    destruct (IHpoints i j n m
                         (setRaster r true (Z.to_nat ax) (Z.to_nat ay)) ).
    apply setRaster_wf, H.
    exact H0.
    right. exact H1.
    destruct (Nat.eq_dec (Z.to_nat ax) i).
    + destruct (Nat.eq_dec (Z.to_nat ay) j). 
      left. f_equal; assumption.
      exfalso. apply setRaster_uncarry in H1.
      destruct H1. unfold Is_true in H1.
      rewrite des in H1. contradiction.
      inversion H1. contradiction. exact H.
    + exfalso. apply setRaster_uncarry in H1.
      destruct H1. unfold Is_true in H1.
      rewrite des in H1. contradiction.
      inversion H1. contradiction. exact H.
Qed. 

Lemma InFinEnumC_Qepsilon : forall (x y : Q) points,
    @InFinEnumC (ProductMS _ _) (x,y) points
    -> exists q, In q points /\ msp_eq q (x,y).
Proof.
  intros. induction points as [|[i j] points].
  - exfalso. unfold InFinEnumC, FinSubset_ball in H.
    contradict H; intros [z [H _]]. inversion H.
  - destruct (Qeq_dec x i).
    + destruct (Qeq_dec y j).
      exists (i,j). split. left. reflexivity.
      split; apply Qball_0; symmetry; assumption.
      destruct IHpoints. 
      intro abs.
      unfold InFinEnumC, FinSubset_ball in H.
      contradict H; intros [z [zin H0]].
      destruct zin. subst z.
      destruct H0. simpl in H0.
      apply Qball_0 in H0. contradiction.
      contradict abs. exists z. split.
      exact H. exact H0.
      exists x0. split. right. apply H0. apply H0.
    + destruct IHpoints.
      intro abs.
      unfold InFinEnumC, FinSubset_ball in H.
      contradict H; intros [z [zin H0]].
      destruct zin. subst z.
      destruct H0. simpl in H.
      apply Qball_0 in H. contradiction.
      contradict abs. exists z. split.
      exact H. exact H0.
      exists x0. split. right. apply H0. apply H0.
Qed.

(* end hide *)
Section RasterizeCorrect.

(* Middles of the horizontal subdivision of the segment [[l, r]].
Instead of l, l + (r-l)/n, ...
it is l + (r-l)/2n, l + (r-l)*3/2n, ... *)
Let C : Q -> Q -> positive -> Z -> Q
  := fun l r (n:positive) (i:Z) => l + (r - l) * (2 * i + 1 # 1) / (2 * Z.pos n # 1).

(* rasterize1 is used in both horizontally and vertically,
   so it will be called for left,width and also for bottom,height. *)
Lemma rasterize1_error : forall l (w:Qpos) n x,
(l <= x <= l + proj1_sig w) ->
Qball ((1 #2*n) * proj1_sig w)
      (C l (l + proj1_sig w) n (Z.min (Z.pos n -1)
                  (Z.max 0 (rasterize1 l (l+proj1_sig w) n x))))
      x.
Proof.
 clear - C.
 intros l w n x H0.
 destruct (Qlt_le_dec x (l+proj1_sig w)).
 - replace (Z.min (Z.pos n -1)
          (Z.max 0 (rasterize1 l (l + proj1_sig w) n x)))
    with (rasterize1 l (l + proj1_sig w) n x).
   + apply ball_sym.
   simpl.
   rewrite -> Qball_Qabs.
   assert (l < l + proj1_sig w).
   { rewrite -> Qlt_minus_iff.
    ring_simplify.
    exact (Qpos_ispos w). }
   eapply Qle_trans.
    unfold C.
    apply (rasterize1_close H).
    setoid_replace (l + proj1_sig w - l) with (proj1_sig w) 
     by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
    unfold Qdiv. rewrite Qmult_comm.
    apply Qmult_le_compat_r. apply Qle_refl.
    apply Qpos_nonneg.
   + rewrite Z.max_r.
   apply Z.min_case_strong.
    intros H.
    apply Zle_antisym; auto.
    apply Zlt_succ_le.
    rewrite <- Z.add_1_r.
    replace (Z.pos n - 1 + 1)%Z with (Z.pos n) by ring.
    apply rasterize1_boundR; auto.
    rewrite -> Qle_minus_iff.
    ring_simplify.
    exact (Qpos_nonneg w).
   reflexivity.
  destruct H0.
  apply rasterize1_boundL; auto.
  apply Qle_trans with x; auto.
 - rewrite Z.min_l.
  setoid_replace x with (l + proj1_sig w).
   apply ball_sym.
   rewrite ->  Qball_Qabs.
   unfold C.
   rewrite <- (Qmult_comm (proj1_sig w)).
   change (1 # 2*n) with (/((2#1)*inject_Z (Z.pos n))).
   change (2*Z.pos n #1) with ((2#1)*inject_Z (Z.pos n)).
   replace (2 * (Z.pos n - 1) + 1)%Z with (2*Z.pos n + - 1)%Z by ring.
   change (2*Z.pos n + -1#1) with (inject_Z (2*Z.pos n + - 1)).
   rewrite -> Q.Zplus_Qplus.
   rewrite -> Q.Zmult_Qmult.
   change (inject_Z 2) with (2#1).
   change (inject_Z (-1)) with (-1#1)%Q.
   setoid_replace (l + proj1_sig w - (l + (l + proj1_sig w - l) * ((2#1) * inject_Z (Z.pos n) + (-1#1)) / ((2#1) * (inject_Z (Z.pos n)))))
     with ((proj1_sig w / ((2#1) * (inject_Z (Z.pos n)))))
     by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; field; unfold Qeq; simpl; auto with *).
   rewrite -> Qabs_pos;[apply Qle_refl|].
   apply Qle_shift_div_l.
   rewrite <- (Qmult_0_r (2#1)). apply Qmult_lt_l. reflexivity.
   simpl; auto with *; unfold Qlt; simpl; auto with *.
   rewrite Qmult_0_l.
   exact (Qpos_nonneg w).
  destruct H0.
  apply Qle_antisym; auto.
 eapply Z.le_trans;[|apply Z.le_max_r].
 unfold rasterize1.
 rewrite <- (Qfloor_Z (Z.pos n -1)).
 apply Qfloor_resp_le.
 setoid_replace x with (l+proj1_sig w).
 setoid_replace (l + proj1_sig w - l) with (proj1_sig w)
   by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
 unfold Qdiv.
 rewrite <- Qmult_assoc, Qmult_inv_r, Qmult_1_r.
 2: apply Qpos_nonzero.
 rewrite <- Zle_Qle.
 rewrite <- (Z.add_0_r (Z.pos n)) at 2.
 apply Z.add_le_mono_l. discriminate.
  apply Qle_antisym.
  apply H0. exact q.
Qed.

(* Strange, we should always have b <= t in rasterize1. *)
Lemma switch_line_interp : forall (t b : Q) (m : positive) (j : Z),
     (j < Z.pos m)%Z
     -> C t b m (Z.pos m - 1- j) == C b t m j.
Proof.
 intros t b m j H.
 unfold C.
 replace (2 * (Z.pos m -1 - j) + 1)%Z with (2 * (Z.pos m - j) - 1)%Z by ring.
 change (2 * (Z.pos m - j) - 1 # 1)
   with (inject_Z (2 * (Z.pos m - j) + - 1)%Z).
 change (2*Z.pos m#1) with ((2#1)*inject_Z (Z.pos m)).
 change ((2*j +1)#1) with (inject_Z (2*j+1)%Z).
 do 2 rewrite -> Q.Zplus_Qplus.
 rewrite -> Q.Zmult_Qmult.
 change (inject_Z (-1)) with (-1#1).
 rewrite -> Q.Zmult_Qmult.
 change (inject_Z 2) with (2#1).
 unfold Zminus.
 rewrite -> Q.Zplus_Qplus.
 change (inject_Z (-j)) with (-inject_Z j).
 field.
 apply Q.positive_nonzero_in_Q.
Qed.

Variable b l:Q.
Variable w h:Qpos.

Let r:=l+proj1_sig w.
Let t:=b+proj1_sig h.

Variable points:FinEnum Q2.

Variable n m : positive.

Let errX : Qpos := ((1#2*n)*w)%Qpos.
Let errY : Qpos := ((1#2*m)*h)%Qpos.
Let err : Qpos := Qpos_max errX errY.

Hypothesis Hf : forall (x y : Q), InFinEnumC ((x,y):ProductMS _ _) points ->
 (l<= x <= r) /\ (b <= y <= t).

 
(** The Rasterization is close to the original enumeration,
ie each one is approximately included in the other,
within error err (Hausdorff distance).
To measure closeness, we use the product metric on Q2, which has
square balls aligned with the 2 axes. *)
Lemma RasterizeQ2_correct1 : forall (x y:Q),
    @InFinEnumC (ProductMS _ _) (x,y) points ->
    exists p, In p (CentersOfPixels (PixelizeQ2 (RasterizeQ2 points n m t l b r))
                               (l,t) (r,b))
         /\ ball (proj1_sig err) p (x,y).
Proof.
  intros x y H.
  pose proof (Hf H) as xybound.
  apply InFinEnumC_Qepsilon in H.
  destruct H as [q [H H0]].
  assert (let (i,j) := rasterize2 n m t l b r q in
          Is_true (RasterIndex (PixelizeQ2 (RasterizeQ2 points n m t l b r))
                               (Z.to_nat i) (Z.to_nat j))).
  { apply RasterizeQ2_in.
    apply (in_map (fun p : Q * Q => rasterize2 n m t l b r p) points).
    exact H. apply emptyRaster_wf.
    apply Nat2Z.inj_lt.
    rewrite positive_nat_Z, Z2Nat.id.
    apply Z.lt_0_sub. ring_simplify.
    apply (Z.lt_le_trans _ (0+1)).
    reflexivity.
    apply Z.add_le_mono_r.
    apply rasterize2_bound.
    apply Z.le_0_sub. apply Z.le_min_l.
    apply Nat2Z.inj_lt.
    rewrite positive_nat_Z, Z2Nat.id.
    apply rasterize2_bound. 
    apply rasterize2_bound. }
  pose (Z.pos m - 1 - Z.min (Z.pos m - 1) (Z.max 0 (rasterize1 b t m (snd q))))%Z
    as i.
  pose (Z.min (Z.pos n - 1) (Z.max 0 (rasterize1 l r n (fst q)))) as j.
  exists ((fun (l r : Q) (n : positive) (i : Z) =>
           l + (r - l) * (2 * i + 1 # 1) / (2 * Z.pos n # 1)) l r n
            (Z.of_nat (Z.to_nat j)),
         (fun (l r : Q) (n : positive) (i : Z) =>
          l + (r - l) * (2 * i + 1 # 1) / (2 * Z.pos n # 1)) t b m
           (Z.of_nat (Z.to_nat i))).
  split. apply InterpRaster_correct1.
  apply RasterizeQ2_wf. exact H1.
  rewrite Z2Nat.id.
  rewrite Z2Nat.id.
  destruct H0, q.
  split.
  - unfold fst. 
    destruct xybound.
    apply Qball_0 in H0.
    unfold fst in H0. clear H2.
    rewrite <- H0 in H3.
    unfold j, r. rewrite <- H0. unfold fst.
    apply ball_weak_le with (e:=((1 # 2 * n) * proj1_sig w)).
    apply (Qpos_max_ub_l errX errY).
    apply (@rasterize1_error l w n _ H3).
  - unfold snd.
    destruct xybound.
    apply Qball_0 in H2.
    unfold snd in H2. clear H0.
    rewrite <- H2 in H4.
    unfold i, t. rewrite <- H2. unfold snd.
    apply ball_weak_le with (e:=((1 # 2 * m) * proj1_sig h)).
    apply (Qpos_max_ub_r errX errY).
    pose proof (@rasterize1_error b h m _ H4).
    rewrite <- switch_line_interp in H0.
    apply H0.
    apply rasterize2_bound.
  - unfold i. apply Z.le_0_sub.
    apply Z.le_min_l.
  - apply rasterize2_bound.
Qed.

Lemma RasterizeQ2_correct2 : forall (x y : Q),
    @InFinEnumC (ProductMS _ _) (x,y)
                (CentersOfPixels (PixelizeQ2 (RasterizeQ2 points n m t l b r))
                                 (l,t) (r,b))
    -> exists p, In p points /\ ball (proj1_sig err) p (x,y).
Proof.
  intros x y H.
  apply InFinEnumC_Qepsilon in H.
  destruct H as [q [qin qeq]].
  destruct q as [qx qy].
  destruct (InterpRaster_correct2
             _ _ _ _ _ _ _ (RasterizeQ2_wf points n m t l b r) qin)
   as [[j i] [Hij [Hx' Hy']]].
  unfold fst, snd in Hij.
  apply RasterizeQ2_in_recip in Hij.
  2: apply emptyRaster_wf.
  destruct Hij.
  2: unfold Is_true in H; rewrite (emptyRasterEmpty n m j i) in H; contradiction.
  unfold RasterizeQ2 in H.
  rewrite map_map in H.
  apply In_nth with (d:=(fun x : Q * Q =>
            (Z.to_nat (fst (rasterize2 n m t l b r x)),
            Z.to_nat (snd (rasterize2 n m t l b r x))))(0,0)) in H.
  destruct H as [k [kin H]].
  rewrite map_length in kin.
  rewrite (map_nth (fun x : Q * Q =>
            (Z.to_nat (fst (rasterize2 n m t l b r x)),
            Z.to_nat (snd (rasterize2 n m t l b r x))))) in H.
  exists (nth k points (0,0)). split.
  apply nth_In. exact kin.
  unfold snd in Hx'.
  unfold fst in Hy'.
  assert (Z.to_nat (fst (rasterize2 n m t l b r (nth k points (0, 0)))) = j
          /\ Z.to_nat (snd (rasterize2 n m t l b r (nth k points (0, 0)))) = i).
  { inversion H. split; reflexivity. }
  clear H. destruct H0.
  rewrite <- qeq. clear qeq x y.
  specialize (@Hf (fst (nth k points (0,0))) (snd (nth k points (0,0)))). 
  rewrite <- surjective_pairing in Hf.
  specialize (@Hf (InFinEnumC_weaken _ _ points (nth_In _ _ kin))).
  split.
  - unfold rasterize2, snd in H0. clear H.
    simpl (fst (qx,qy)).
    rewrite Hx', <- H0.
    rewrite Z2Nat.id.
    apply ball_weak_le with (e:=((1 # 2 * n) * proj1_sig w)).
    apply (Qpos_max_ub_l errX errY). 
    apply ball_sym.
    apply rasterize1_error.
    apply Hf. apply rasterize2_bound.
  - unfold rasterize2, fst in H. clear H0 Hx'.
    simpl (snd (qx,qy)).
    rewrite Hy', <- H.
    apply ball_weak_le with (e:=((1 # 2 * m) * proj1_sig h)).
    apply (Qpos_max_ub_r errX errY).
    pose proof (@rasterize1_error b h m _ (proj2 Hf)).
    rewrite <- switch_line_interp in H0.
    apply ball_sym.
    rewrite Z2Nat.id.
    apply H0.
    apply Z.le_0_sub, Z.le_min_l.
    apply (Z.le_lt_trans _ _ _ (Z.le_min_l _ _)).
    rewrite <- (Z.add_0_r (Z.pos m)) at 2.
    apply Z.add_lt_mono_l. reflexivity. 
Qed.

Lemma RasterizeQ2_correct :
  ball (proj1_sig err)
       (CentersOfPixels (PixelizeQ2 (RasterizeQ2 points n m t l b r)) (l,t) (r,b))
       points.
Proof.
  split. apply Qpos_nonneg.
  split; intros [x y] Hx.
  - pose proof (RasterizeQ2_correct2 Hx).
    intro abs.
    contradict H; intros [z [Hz0 Hz1]].
    specialize (abs z). contradict abs.
    split.
    apply InFinEnumC_weaken, Hz0.
    apply ball_sym, Hz1.
  - intro abs.
    pose proof (RasterizeQ2_correct1 Hx).
    contradict H; intros [z [Hz0 Hz1]].
    specialize (abs z). contradict abs.
    split.
    apply InFinEnumC_weaken, Hz0.
    apply ball_sym, Hz1.
Qed.

End RasterizeCorrect.
