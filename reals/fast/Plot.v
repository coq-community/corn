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
Require Import QArith.Qround.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.ProductMetric.
Require Import CoRN.metric2.UniformContinuity.
Require Export CoRN.reals.fast.RasterizeQ.
Require Import CoRN.reals.fast.Interval.
Require Export CoRN.metric2.Graph.
Require Import CoRN.model.totalorder.QMinMax.
Require Export CoRN.model.totalorder.QposMinMax.

(**
* Plotting
Plotting a uniformly continuous function on a finite interval consists
of producing the graph of a function as a compact set, approximating that
graph, and finally rasterizing that approximation.

A range for the plot must be provided. We choose to clamp the plotted
function so that it lies inside the specified range.  Thus we plot
[compose (clip b t) f] rather than [f].

Afterwards we will plot more general located subsets of the plane:
- Each blank pixels is correct, meaning there are no points of the subset
  inside the rectangular regions it represents. In other words, filled
  pixels cover the subset.
- Each filled pixel means there exists a point of the subset inside its
  rectangular region, or inside one of the adjacent pixels. Thus when we
  zoom in the filled pixels, we will see more structure.
- The pixels overlap, meaning each edge belongs to the 2 pixels that
  touch it, and each corner belongs to the 4 pixels that touch it.
 
*)

Local Open Scope uc_scope.

Section PlotPath.
Variable (from to:Q).
Hypothesis Hfromto:from<=to.

Variable (l r:Q).
Hypothesis Hlr : l < r.

Variable (b t:Q).
Hypothesis Hbt : b < t.

Variable n : positive.

Let w := r - l.
Let h := t - b.

Lemma wpos : 0 < w.
Proof.
  apply Qlt_minus_iff in Hlr. exact Hlr.
Qed.

Lemma hpos : 0 < h.
Proof.
  apply Qlt_minus_iff in Hbt. exact Hbt.
Qed.

(* Compute the number of pixels on the Y-axis to make square pixels. *)
Let m : positive := Z.to_pos (Qceiling ((t-b) * inject_Z (Z.pos n) / (r-l))).

(**
Half the error in the Plot example, since we need to approximate twice.
*)
Let err := Qpos_max ((1 # 8 * n) * (exist _ _ wpos))
                    ((1 # 8 * m) * (exist _ _ hpos)).

Variable path:Q_as_MetricSpace --> Complete Q2.

(** The actual plot function.
    The approximation of PathImage make a list (Complete Q2), ie a list
    of points in the real plane. Those points still need to be approximated
    by rational numbers, which map approximate does. *)
Definition PlotPath : positive * positive * Q * sparse_raster n m
  := (n, m, 2#1,
      sparse_raster_data n m
    (map
       (fun x : Z =>
        rasterize2 n m t l b r
          ((let (approximate, _) :=
              path
                (from +
                 (to - from) * (2 * x + 1 # 1) /
                 (2 *
                  Z.pos
                    (Z.to_pos
                       (Qceiling
                          ((to - from) /
                           (inject_Z 2 *
                            proj1_sig (FinEnum_map_modulus (1 # 1) (mu path) err)))))
                  # 1)) in
            approximate) err))
       (iterateN_succ 0
          (Z.to_pos
             (Qceiling
                ((to - from) /
                 (inject_Z 2 * proj1_sig (FinEnum_map_modulus (1 # 1) (mu path) err)))))))).

Definition PlotPath_slow : positive * positive * Q * sparse_raster n m
  := (n, m, 2#1,
      RasterizeQ2 
        (map (fun x : Q_as_MetricSpace => approximate (path x) err)
             (approximate (CompactIntervalQ Hfromto)
                          (FinEnum_map_modulus (1 # 1) (mu path) err)))
        n m t l b r).

Lemma PlotPath_correct : eq PlotPath PlotPath_slow.
Proof.
  unfold PlotPath, PlotPath_slow, RasterizeQ2.
  rewrite map_map.
  unfold CompactIntervalQ, approximate.
  unfold CompactIntervalQ_raw, UniformPartition.
  rewrite map_map.
  reflexivity.
Qed.

End PlotPath.


Lemma plFEQ : PrelengthSpace (FinEnum Q_as_MetricSpace).
Proof.
 apply FinEnum_prelength.
  apply locatedQ.
 apply QPrelengthSpace.
Qed.


Section Plot.

Variable (l b:Q).
Variable w h:Qpos.

Let r:=l+proj1_sig w.
Let t:=b+proj1_sig h.

Let clip := uc_compose (boundBelow b) (boundAbove t).

Variable f : Q_as_MetricSpace --> CR.

Lemma lrle : l <= r.
Proof.
  rewrite <- (Qplus_0_r l).
  unfold r. apply Qplus_le_r, Qpos_nonneg.
Qed.

Definition graphQ f : Compact Q2
  := CompactGraph_b f plFEQ (CompactIntervalQ lrle).

Lemma graphQ_bonus : forall e x y,
    In (x, y) (approximate (graphQ (uc_compose clip f)) e)
    -> l <= x <= r /\ b <= y <= t.
Proof.
 intros [e|] x y;[|intros; contradiction].
 simpl.
 unfold Cjoin_raw.
 Opaque CompactIntervalQ.
 simpl.
 unfold FinCompact_raw.
 rewrite map_map.
 rewrite -> in_map_iff.
 unfold graphPoint_b_raw; simpl.
 unfold Couple_raw; simpl.
 intros [z [Hz0 Hz1]].
 inversion Hz0.
 subst x. subst y.
 clear Hz0.
 split.
 eapply CompactIntervalQ_bonus_correct.
 apply Hz1.
 split. apply Qmax_ub_l.
 apply Qmax_lub.
 rewrite <- (Qplus_0_r b).
 unfold t. apply Qplus_le_r, Qpos_nonneg.
 apply Qmin_lb_l.
Qed.

Variable n m : positive. (* Number of horizontal and vertical pixels *)

Let err := Qpos_max ((1 # 4 * n) * w)
                    ((1 # 4 * m) * h).

(** [PlotQ] is the function that computes the pixels. *)
Definition PlotQ : sparse_raster n m
  := RasterizeQ2 (approximate (graphQ (uc_compose clip f)) err) n m t l b r.

Local Open Scope raster.

(** The resulting plot is close to the graph of [f] *)
Theorem Plot_correct :
  @ball (Compact Q2)
        (proj1_sig (err + Qpos_max ((1 # 2 * n) * w) ((1 # 2 * m) * h))%Qpos)
        (graphQ (uc_compose clip f))
        (Cunit (CentersOfPixels (PixelizeQ2 PlotQ) (l,t) (r,b))).
Proof.
 apply ball_triangle with (Cunit (approximate (graphQ (uc_compose clip f)) err)).
  apply ball_approx_r.
 unfold Compact.
 rewrite -> ball_Cunit.
 apply ball_sym.
  split. apply Qpos_nonneg.
  apply RasterizeQ2_correct.
  intros. 
  destruct (InStrengthen H) as [[zx xy] [Hz0 [Hz1 Hz2]]].
  simpl in Hz1, Hz2.
  apply Qball_0 in Hz1.
  apply Qball_0 in Hz2.
  rewrite -> Hz1, Hz2.
  eapply graphQ_bonus.
  apply Hz0.
Qed.

End Plot.

(** Some nice notation for the graph of f. *)
Notation "'graphCR' f [ l '..' r ]" :=
 (graphQ l r (refl_equal _) f) (f at level 0) : raster.

(*
(* Some graph examples *)
Local Open Scope raster. (* enables pretty printing of rasters *)
Definition id_raster : raster _ _
  := PlotQ 0 1 eq_refl 0 1 eq_refl (@Cunit Q_as_MetricSpace) 30 30.
Compute id_raster.

Require Import CoRN.reals.fast.CRexp.
Definition exp_raster
  := PlotQ (-2) 1 eq_refl 0 3 eq_refl (exp_bound_uc 3) 30 30.
Compute exp_raster.
*)

(* Difficult to make tail-recursive, because the current vector
   has no clear size to declare. Vector.map is not tail-recursive either. *)
Fixpoint PlotLine (A : CR*CR -> Prop) (i:nat)
           (r step:Q) (y : CR) (d e:Q) (ltde : d < e)
           (loc : LocatedSubset (ProductMS CR CR) A)
           { struct i }
  : list bool :=
  match i with
  | O => nil
  | S p =>
    cons (let xi := inject_Q_CR (r - inject_Z (Z.of_nat i) * step)%Q in
          if loc d e (xi,y) ltde then false else true)
         (PlotLine A p r step y d e ltde loc)
  end.

Fixpoint PlotSubset_fix (A : CR*CR -> Prop) (n j:nat)
         (b r stepX stepY:Q) (d e:Q) (ltde : d < e)
         (loc : LocatedSubset (ProductMS CR CR) A)
         { struct j }
  : list (list bool) :=
  match j with
  | O => nil
  | S p => let yj := inject_Q_CR (b + inject_Z (Z.of_nat j) * stepY)%Q in
          cons (PlotLine A n r stepX yj d e ltde loc)
               (PlotSubset_fix A n p b r stepX stepY d e ltde loc)
  end. 

Definition PlotRadius (n m : positive) (t l b r : Q) : Q
  := Qmax ((r-l) * (1#n))%Q
          ((t-b) * (1#m))%Q.

Lemma PlotRadiusInc
  : forall n m t l b r,
    l < r -> (1#2) * PlotRadius n m t l b r < PlotRadius n m t l b r.
Proof.
  intros. rewrite <- (Qmult_1_l (PlotRadius n m t l b r)) at 2.
  apply Qmult_lt_r.
  2: reflexivity. apply (Qlt_le_trans _ ((r-l) * (1#n))%Q).
  apply Qlt_minus_iff in H.
  apply (Qpos_ispos (exist _ _ H * (1 # n))).
  apply Qmax_ub_l.
Qed.
 
Definition PlotSubset {A : CR*CR -> Prop} (n m : positive) (t l b r : Q) 
           (ltlr : l < r) (loc : LocatedSubset (ProductMS CR CR) A)
  : raster n m
  := let stepX := ((r-l) * (1#n))%Q in
     let stepY := ((t-b) * (1#m))%Q in
     (* A pixel is a square ball and its radius it half its side. *)
     raster_data
       _ _
       (PlotSubset_fix A (Pos.to_nat n) (Pos.to_nat m) (b-(1#2)*stepY) (r+(1#2)*stepX)
                       stepX stepY _ _
                       (PlotRadiusInc n m t l b r ltlr) loc).

(*
Definition PlotDiagLocated := (PlotSubset
         10 10 (1#1) (0#1) (0#1) (1#1) eq_refl
         (undistrib_Located (CompactIsLocated
         _ (graphQ 0 1 eq_refl (@Cunit Q_as_MetricSpace))
         (ProductMS_located locatedQ locatedQ)))).
Local Open Scope raster. (* enables pretty printing of rasters *)
Time Eval vm_compute in PlotDiagLocated.
*)


(* The blank pixels have no points of the subset, in other words
   the filled pixels cover the subset. *)
Lemma PlotLine_blank
  : forall (A : CR*CR -> Prop) (n i:nat) (ltni : (n < i)%nat)
      (r step:Q) (x y z : CR) (d e:Q) (ltde : d < e)
      (loc : LocatedSubset (ProductMS CR CR) A),
    ball d x (inject_Q_CR (r - inject_Z (Z.of_nat (i-n)) * step)%Q)
    -> ball d y z
    -> nth n (PlotLine A i r step y d e ltde loc) false = false
    -> ~A (x,z).
Proof.
  induction n.
  - intros. intro abs.
    destruct i. exfalso; inversion ltni.
    simpl in H1.
    destruct (loc d e
             (@pair (@RegularFunction Q Qball) (@RegularFunction Q Qball)
                (inject_Q_CR
                   (Qminus r (Qmult (inject_Z (Zpos (Pos.of_succ_nat i))) step))) y)
             ltde).
    2: discriminate. clear H1.
    specialize (n (x,z) abs).
    contradict n. split.
    + unfold fst.
      apply ball_sym.
      exact H.
    + exact H0.
  - intros. intro abs. 
    destruct i. inversion ltni. simpl in H1.
    revert abs.
    refine (IHn i (proj2 (Nat.succ_lt_mono n i) ltni) r step x y z d e
                ltde loc _ H0 H1).
    replace (i-n)%nat with (S i - S n)%nat by reflexivity.
    exact H.
Qed.

Lemma PlotSubset_fix_blank
  : forall (A : CR*CR -> Prop) (x y : CR) (i j n m:nat)
      (ltin : (i < n)%nat) (ltjm : (j < m)%nat)
      (b r stepX stepY:Q) (d e:Q) (ltde : d < e)
      (loc : LocatedSubset (ProductMS CR CR) A),
    ball d x (inject_Q_CR (r - inject_Z (Z.of_nat (n-i)) * stepX)%Q)
    -> ball d y (inject_Q_CR (b + inject_Z (Z.of_nat (m-j)) * stepY)%Q)
    -> nth i
        (nth j (PlotSubset_fix A n m b r stepX stepY
                                    d e ltde loc) 
             nil)
        false = false
    -> ~A (x,y).
Proof.
  induction j.
  - intros. intro abs.
    destruct m. exfalso; inversion ltjm.
    simpl in H1.
    refine (PlotLine_blank
              A i n ltin r stepX x
              (' (b + inject_Z (Z.pos (Pos.of_succ_nat m)) * stepY)%Q)%CR
              y d e ltde loc H _ H1 abs).
    apply ball_sym.
    exact H0.
  - intros. intro abs.
    destruct m. inversion ltjm.
    simpl in H1.
    apply (IHj n m ltin (proj2 (Nat.succ_lt_mono j m) ltjm) b r stepX stepY
                    d e ltde loc H H0 H1 abs).
Qed.

Lemma PlotSubset_blank
  : forall {A : CR*CR -> Prop} (i j : nat) (n m : positive) (t l b r : Q) (x y : CR)
      (ltin : (i < Pos.to_nat n)%nat) (ltjm : (j < Pos.to_nat m)%nat) (ltlr : l < r)
      (loc : LocatedSubset (ProductMS CR CR) A),
    RasterIndex (PlotSubset n m t l b r ltlr loc) j i = false
    -> let stepX := ((r-l) * (1#n))%Q in
      let stepY := ((t-b) * (1#m))%Q in 
      ball ((1#2)*(Qmax stepX stepY)) x
           (inject_Q_CR (l + (inject_Z (Z.of_nat i) + (1#2)) * stepX)%Q)
      -> ball ((1#2)*(Qmax stepX stepY)) y
             (inject_Q_CR (t - (inject_Z (Z.of_nat j) + (1#2)) * stepY)%Q)
      -> ~A (x,y).
Proof.
  intros. 
  setoid_replace (l + (inject_Z (Z.of_nat i)+(1#2)) * stepX)%Q
    with ((r + (1#2)*stepX) - inject_Z (Z.of_nat (Pos.to_nat n - i)) * stepX)%Q
    in H0. 
  setoid_replace (t - (inject_Z (Z.of_nat j) + (1#2)) * stepY)%Q
    with ((b-(1#2)*stepY) + inject_Z (Z.of_nat (Pos.to_nat m - j)) * stepY)%Q
    in H1. 
  exact (PlotSubset_fix_blank
           A x y i j (Pos.to_nat n) (Pos.to_nat m) ltin ltjm
           _ _ stepX stepY
           ((1#2)*(Qmax stepX stepY)) 
           (Qmax stepX stepY)
           (PlotRadiusInc n m t l b r ltlr) loc
           H0 H1 H).
  - unfold canonical_names.equiv, stdlib_rationals.Q_eq.
    rewrite Nat2Z.inj_sub.
    unfold Zminus. rewrite Q.Zplus_Qplus, inject_Z_opp.
    rewrite <- (Qplus_inj_r _ _ ((inject_Z (Z.of_nat j)+(1#2)) * stepY)).
    ring_simplify.
    rewrite positive_nat_Z.
    unfold stepY.
    rewrite <- Qmult_assoc.
    setoid_replace ((1 # m) * inject_Z (Z.pos m)) with 1%Q by reflexivity.
    rewrite Qmult_1_r. ring.
    apply (Nat.le_trans _ (S j)).
    apply le_S, Nat.le_refl. exact ltjm. 
  - unfold canonical_names.equiv, stdlib_rationals.Q_eq.
    rewrite Nat2Z.inj_sub.
    unfold Zminus. rewrite Q.Zplus_Qplus, inject_Z_opp.
    rewrite positive_nat_Z.
    rewrite <- (Qplus_inj_r _ _ (stepX * inject_Z (Z.pos n)
                                -inject_Z (Z.of_nat i) * stepX
                                - (1#2)*stepX)).
    ring_simplify.
    unfold stepX.
    rewrite <- Qmult_assoc.
    setoid_replace ((1 # n) * inject_Z (Z.pos n)) with 1%Q by reflexivity.
    rewrite Qmult_1_r. ring.
    apply (Nat.le_trans _ (S i)).
    apply le_S, Nat.le_refl. exact ltin.
Qed.
