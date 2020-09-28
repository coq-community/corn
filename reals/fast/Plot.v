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

Lemma plFEQ : PrelengthSpace (FinEnum Q_as_MetricSpace).
Proof.
 apply FinEnum_prelength.
  apply locatedQ.
 apply QPrelengthSpace.
Qed.

Section PlotPath.
Variable (from to:Q).
Hypothesis Hfromto:from<=to.

Variable (l r:Q).
Hypothesis Hlr : l < r.

Variable (b t:Q).
Hypothesis Hbt : b < t.

Variable n m : positive.

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
Definition PlotPath : positive * positive * Q * raster (Pos.to_nat n) (Pos.to_nat m)
  := (n, m, 2#1,
      RasterizeQ2 
        (map (fun x => approximate x err)
             (map path (approximate (CompactIntervalQ Hfromto)
                                    (FinEnum_map_modulus (1 # 1) (mu path) err))))
        n m t l b r).

End PlotPath.



Section Plot.

Variable (l r:Q).
Hypothesis Hlr : l < r.

Variable (b t:Q).
Hypothesis Hbt : b < t.


Let clip := uc_compose (boundBelow b) (boundAbove t).

Variable f : Q_as_MetricSpace --> CR.

Definition graphQ f : Compact Q2
  := CompactGraph_b f plFEQ (CompactIntervalQ (Qlt_le_weak _ _ Hlr)).

Lemma graphQ_bonus : forall e x y,
 In (x, y) (approximate (graphQ (uc_compose clip f)) e) -> l <= x <= r /\ b <= y <= t.
Proof.
 intros [e|] x y;[|intros; contradiction].
 simpl.
 unfold Cjoin_raw.
 Opaque  CompactIntervalQ.
 simpl.
 unfold FinCompact_raw.
 rewrite map_map.
 rewrite -> in_map_iff.
 unfold graphPoint_b_raw.
 simpl.
 unfold Couple_raw.
 simpl.
 intros [z [Hz0 Hz1]].
 inversion Hz0.
 rewrite <- H0.
 clear Hz0 x y H0 H1.
 split; auto with *.
 eapply CompactIntervalQ_bonus_correct.
 apply Hz1.
Qed.

Variable n m : positive. (* Number of horizontal and vertical pixels *)

Let w := proj1_sig (Qpos_sub _ _ Hlr).
Let h := proj1_sig (Qpos_sub _ _ Hbt).

Let err := Qpos_max ((1 # 4 * n) * w)
                    ((1 # 4 * m) * h).

(** [PlotQ] is the function that computes the pixels. *)
Definition PlotQ : raster (Pos.to_nat n) (Pos.to_nat m)
  := RasterizeQ2 (approximate (graphQ (uc_compose clip f)) err) n m t l b r.

Local Open Scope raster.

(** The resulting plot is close to the graph of [f] *)
Theorem Plot_correct :
ball (proj1_sig (err + Qpos_max ((1 # 2 * n) * w)
        ((1 # 2 * m) * h))%Qpos)
 (graphQ (uc_compose clip f))
 (Cunit (InterpRaster _ _ PlotQ (l,t) (r,b))).
Proof.
 assert (Hw:=(proj2_sig (Qpos_sub _ _ Hlr))).
 assert (Hh:=(proj2_sig (Qpos_sub _ _ Hbt))).
 fold w in Hw.
 fold h in Hh.
 change (r == l + proj1_sig w) in Hw.
 change (t == b + proj1_sig h) in Hh.
 apply ball_triangle with (Cunit (approximate (graphQ (uc_compose clip f)) err)).
  apply ball_approx_r.
 unfold Compact.
 rewrite -> ball_Cunit.
 apply ball_sym.
 assert (L:msp_eq ((l,t):Q2) (l,b + proj1_sig h)).
  split; simpl.
   reflexivity.
  apply Qball_0; ring.
 set (Z0:=(l, t):Q2) in *.
 set (Z1:=(r, b):Q2) in *.
 set (Z:=(l, (b + proj1_sig h)):Q2) in *.
 rewrite -> L.
 setoid_replace Z1 with (l+proj1_sig w,b).
  unfold Z, PlotQ.
  (* TODO: figure out why rewrite Hw, Hh hangs *)
  replace (RasterizeQ2 (approximate (graphQ (uc_compose clip f)) err) n m t l b r)
    with (RasterizeQ2 (approximate (graphQ (uc_compose clip f)) err) n m (b + proj1_sig h) l b (l + proj1_sig w)) by now rewrite Hw, Hh.
  split. apply Qpos_nonneg.
  apply RasterizeQ2_correct.
  intros.
  rewrite <- Hw.
  rewrite <- Hh.
  destruct (InStrengthen H) as [[zx xy] [Hz0 [Hz1 Hz2]]].
  simpl in Hz1, Hz2.
  apply Qball_0 in Hz1.
  apply Qball_0 in Hz2.
  rewrite -> Hz1, Hz2.
  eapply graphQ_bonus.
  apply Hz0.
  split; simpl.
  apply Qball_0; ring.
  reflexivity. 
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
  : (Vector.t bool i) :=
  match i with
  | O => Vector.nil bool
  | S p =>
  Vector.cons bool (let xi := inject_Q_CR (r - inject_Z (Z.of_nat i) * step)%Q in
                 if loc d e (xi,y) ltde then false else true)
              p (PlotLine A p r step y d e ltde loc)
  end.

Fixpoint PlotSubset_fix (A : CR*CR -> Prop) (n j:nat)
         (b r stepX stepY:Q) (d e:Q) (ltde : d < e)
         (loc : LocatedSubset (ProductMS CR CR) A)
         { struct j }
  : raster n j :=
  match j with
  | O => emptyRaster n O
  | S p => let yj := inject_Q_CR (b + inject_Z (Z.of_nat j) * stepY)%Q in
          Vector.cons (Vector.t bool n)
                      (PlotLine A n r stepX yj d e ltde loc)
                      p (PlotSubset_fix A n p b r stepX stepY d e ltde loc)
  end. 

Definition PlotRadius (n m : nat) (t l b r : Q) : Q
  := Qmax ((r-l) * (1#Pos.of_nat n))%Q
          ((t-b) * (1#Pos.of_nat m))%Q.

Lemma PlotRadiusInc
  : forall n m t l b r,
    l < r -> (1#2) * PlotRadius n m t l b r < PlotRadius n m t l b r.
Proof.
  intros. rewrite <- (Qmult_1_l (PlotRadius n m t l b r)) at 2.
  apply Qmult_lt_r.
  2: reflexivity. apply (Qlt_le_trans _ ((r-l) * (1#Pos.of_nat n))%Q).
  apply Qlt_minus_iff in H.
  apply (Qpos_ispos (exist _ _ H * (1 # Pos.of_nat n))).
  apply Qmax_ub_l.
Qed.
 
Definition PlotSubset {A : CR*CR -> Prop} (n m : nat) (t l b r : Q) 
           (ltlr : l < r) (loc : LocatedSubset (ProductMS CR CR) A) : raster n m
  := let stepX := ((r-l) * (1#Pos.of_nat n))%Q in
     let stepY := ((t-b) * (1#Pos.of_nat m))%Q in
     (* A pixel is a square ball and its radius it half its side. *)
     PlotSubset_fix A n m (b-(1#2)*stepY) (r+(1#2)*stepX)
                    stepX stepY _ _
                    (PlotRadiusInc n m t l b r ltlr) loc.

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
    -> Vector.nth (PlotLine A i r step y d e ltde loc) 
                 (Fin.of_nat_lt ltni) = false
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
    refine (IHn i (lt_S_n n i ltni) r step x y z d e
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
    -> Vector.nth
        (Vector.nth (PlotSubset_fix A n m b r stepX stepY
                                    d e ltde loc) 
                    (Fin.of_nat_lt ltjm))
        (Fin.of_nat_lt ltin) = false
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
    apply (IHj n m ltin (lt_S_n j m ltjm) b r stepX stepY
                    d e ltde loc H H0 H1 abs).
Qed.

Lemma PlotSubset_blank
  : forall {A : CR*CR -> Prop} (i j n m : nat) (t l b r : Q) (x y : CR)
      (ltin : (i < n)%nat) (ltjm : (j < m)%nat) (ltlr : l < r)
      (loc : LocatedSubset (ProductMS CR CR) A),
    Vector.nth (Vector.nth (PlotSubset n m t l b r ltlr loc) (Fin.of_nat_lt ltjm))
               (Fin.of_nat_lt ltin) = false
    -> let stepX := ((r-l) * (1#Pos.of_nat n))%Q in
      let stepY := ((t-b) * (1#Pos.of_nat m))%Q in 
      ball ((1#2)*(Qmax stepX stepY)) x
           (inject_Q_CR (l + (inject_Z (Z.of_nat i) + (1#2)) * stepX)%Q)
      -> ball ((1#2)*(Qmax stepX stepY)) y
             (inject_Q_CR (t - (inject_Z (Z.of_nat j) + (1#2)) * stepY)%Q)
      -> ~A (x,y).
Proof.
  intros. 
  setoid_replace (' (l + (inject_Z (Z.of_nat i)+(1#2)) * stepX)%Q)%CR
    with (inject_Q_CR ((r + (1#2)*stepX) - inject_Z (Z.of_nat (n-i)) * stepX)%Q)
    in H0. 
  setoid_replace (' (t - (inject_Z (Z.of_nat j) + (1#2)) * stepY)%Q)%CR
    with (inject_Q_CR ((b-(1#2)*stepY) + inject_Z (Z.of_nat (m-j)) * stepY)%Q)
    in H1. 
  exact (PlotSubset_fix_blank A x y i j n m ltin ltjm
                              _ _ stepX stepY
                              ((1#2)*(Qmax stepX stepY)) 
                              (Qmax stepX stepY)
                              (PlotRadiusInc n m t l b r ltlr) loc
                              H0 H1 H).
  - apply inject_Q_CR_wd.
    unfold canonical_names.equiv, stdlib_rationals.Q_eq.
    rewrite Nat2Z.inj_sub.
    unfold Zminus. rewrite Q.Zplus_Qplus, inject_Z_opp.
    rewrite <- (Qplus_inj_r _ _ ((inject_Z (Z.of_nat j)+(1#2)) * stepY)).
    ring_simplify.
    unfold stepY.
    rewrite <- Qmult_assoc.
    setoid_replace ((1 # Pos.of_nat m) * inject_Z (Z.of_nat m)) with 1%Q.
    rewrite Qmult_1_r. ring.
    unfold canonical_names.equiv, stdlib_rationals.Q_eq, inject_Z.
    unfold Qeq, Qmult, Qnum, Qden.
    rewrite Z.mul_1_l, Z.mul_1_l, Z.mul_1_r, Pos.mul_1_r.
    destruct m.
    exfalso; inversion ltjm.
    rewrite <- Pos.of_nat_succ. reflexivity.
    apply (le_trans _ (S j)).
    apply le_S, le_refl. exact ltjm. 
  - apply inject_Q_CR_wd.
    unfold canonical_names.equiv, stdlib_rationals.Q_eq.
    rewrite Nat2Z.inj_sub.
    unfold Zminus. rewrite Q.Zplus_Qplus, inject_Z_opp.
    rewrite <- (Qplus_inj_r _ _ (stepX * inject_Z (Z.of_nat n)
                                -inject_Z (Z.of_nat i) * stepX
                                - (1#2)*stepX)).
    ring_simplify.
    unfold stepX.
    rewrite <- Qmult_assoc.
    setoid_replace ((1 # Pos.of_nat n) * inject_Z (Z.of_nat n)) with 1%Q.
    rewrite Qmult_1_r. ring.
    unfold canonical_names.equiv, stdlib_rationals.Q_eq, inject_Z.
    unfold Qeq, Qmult, Qnum, Qden.
    rewrite Z.mul_1_l, Z.mul_1_l, Z.mul_1_r, Pos.mul_1_r.
    destruct n.
    exfalso; inversion ltin.
    rewrite <- Pos.of_nat_succ. reflexivity.
    apply (le_trans _ (S i)).
    apply le_S, le_refl. exact ltin.
Qed.
  
