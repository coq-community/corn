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

Section Plot.
(**
* Plotting
Plotting a uniformly continuous function on a finite interval consists
of producing the graph of a function as a compact set, approximating that
graph, and finally rasterizing that approximation.

A range for the plot must be provided. We choose to clamp the plotted
function so that it lies inside the specified range.  Thus we plot
[compose (clip b t) f] rather than [f].

Afterwards we will plot more general located subsets of the plane:
- each blank pixels is correct, meaning there are no points of the subset
  inside the rectangular regions it represents
- each filled pixel means there exists a point of the subset inside its
  rectangular region, or inside one of the adjacent pixels. Thus filled
  pixels cover the subset and we can zoom in to see more structure.
- the pixels overlap, meaning each corner belong to the 4 pixels that touch it
 
*)
Variable (l r:Q).
Hypothesis Hlr : l < r.

Variable (b t:Q).
Hypothesis Hbt : b < t.

Local Open Scope uc_scope.

Let clip := uc_compose (boundBelow b) (boundAbove t).

Variable f : Q_as_MetricSpace --> CR.

Lemma plFEQ : PrelengthSpace (FinEnum Q_as_MetricSpace).
Proof.
 apply FinEnum_prelength.
  apply locatedQ.
 apply QPrelengthSpace.
Qed.

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

Variable n m : nat. (* Number of horizontal and vertical pixels *)
Hypothesis Hn : n <> O.
Hypothesis Hm : m <> O.

Let w := proj1_sig (Qpos_sub _ _ Hlr).
Let h := proj1_sig (Qpos_sub _ _ Hbt).

Let err := Qpos_max ((1 # 4 * P_of_succ_nat (pred n)) * w)
                    ((1 # 4 * P_of_succ_nat (pred m)) * h).

(** [PlotQ] is the function that computes the pixels. *)
Definition PlotQ : raster n m
  := RasterizeQ2 (approximate (graphQ (uc_compose clip f)) err) n m t l b r.

Local Open Scope raster.

(** The resulting plot is close to the graph of [f] *)
Theorem Plot_correct :
ball (proj1_sig (err + Qpos_max ((1 # 2 * P_of_succ_nat (pred n)) * w)
        ((1 # 2 * P_of_succ_nat (pred m)) * h))%Qpos)
 (graphQ (uc_compose clip f))
 (Cunit (InterpRaster PlotQ (l,t) (r,b))).
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
 assert (L:st_eq ((l,t):Q2) (l,b + proj1_sig h)).
  split; simpl.
   reflexivity.
  ring.
 set (Z0:=(l, t):Q2) in *.
 set (Z1:=(r, b):Q2) in *.
 set (Z:=(l, (b + proj1_sig h)):Q2) in *.
 rewrite -> L.
 setoid_replace Z1 with (l+proj1_sig w,b).
  unfold Z, PlotQ.
  (* TODO: figure out why rewrite Hw, Hh hangs *)
  replace (RasterizeQ2 (approximate (graphQ (uc_compose clip f)) err) n m t l b r)
    with (RasterizeQ2 (approximate (graphQ (uc_compose clip f)) err) n m (b + proj1_sig h) l b (l + proj1_sig w)) by now rewrite Hw, Hh.
  destruct n. contradict Hn; reflexivity.
  destruct m. contradict Hm; reflexivity.
  split. apply Qpos_nonneg.
  apply (RasterizeQ2_correct).
  intros.
  rewrite <- Hw.
  rewrite <- Hh.
  destruct (InStrengthen _ _ H) as [[zx xy] [Hz0 [Hz1 Hz2]]].
  simpl in Hz1, Hz2.
  rewrite -> Hz1, Hz2.
  eapply graphQ_bonus.
  apply Hz0.
 split; simpl; auto with *.
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

Definition PlotSubset {A : CR*CR -> Prop} (n m : nat) (t l b r : Q) :
  l < r -> LocatedSubset (ProductMS CR CR) A -> raster n m.
Proof.
  intros ltlr loc.
  pose ((r-l) * (1#Pos.of_nat n))%Q as stepX.
  pose ((t-b) * (1#Pos.of_nat m))%Q as stepY.
  pose (Qmax stepX stepY) as err.
  (* A pixel is a square ball and its radius it half its side. *)
  assert ((1#2)*err < err)%Q as ltde.
  { rewrite <- (Qmult_1_l err) at 2. apply Qmult_lt_r.
    2: reflexivity. apply (Qlt_le_trans _ stepX).
    apply Qlt_minus_iff in ltlr.
    apply (Qpos_ispos (exist _ _ ltlr * (1 # Pos.of_nat n))).
    apply Qmax_ub_l. }
  exact (PlotSubset_fix A n m b r stepX stepY _ _ ltde loc).
Defined.

(*
Definition PlotDiagLocated := (PlotSubset
         10 10 (1#1) (0#1) (0#1) (1#1) eq_refl
         (undistrib_Located (CompactIsLocated
         _ (graphQ 0 1 eq_refl (@Cunit Q_as_MetricSpace))
         (ProductMS_located locatedQ locatedQ)))).
Local Open Scope raster. (* enables pretty printing of rasters *)
Time Eval vm_compute in PlotDiagLocated.
*)
