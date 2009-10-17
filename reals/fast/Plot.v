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
Require Export RasterizeQ.
Require Import Interval.
Require Export Graph.
Require Import QMinMax.
Require Export QposMinMax.
Require Import CornTac.

Section Plot.
(**
* Plotting
Plotting a uniformly continuous function on a finite interval consists
of producing the graph of a function as a compact set, approximating that
graph, and finally rasterizing that approximation.

A range for the plot must be provided.  We choose to clamp the plotted
function so that it lies inside the specified range.  Thus we plot
[compose (clip b t) f] rather than [f].
*)
Variable (l r:Q).
Hypothesis Hlr : l < r.

Variable (b t:Q).
Hypothesis Hbt : b < t.

Open Local Scope uc_scope.

Let clip := uc_compose (boundBelow b) (boundAbove t).

Variable f : Q_as_MetricSpace --> CR.

Lemma plFEQ : PrelengthSpace (FinEnum stableQ).
Proof.
 apply FinEnum_prelength.
  apply locatedQ.
 apply QPrelengthSpace.
Qed.

Definition graphQ f := CompactGraph_b f stableQ2 plFEQ (CompactIntervalQ (Qlt_le_weak _ _ Hlr)).

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

Variable n m : nat.
Hypothesis Hn : eq_nat n 0 = false.
Hypothesis Hm : eq_nat m 0 = false.

Let w := proj1_sigT _ _ (Qpos_lt_plus Hlr).
Let h := proj1_sigT _ _ (Qpos_lt_plus Hbt).

(*
Variable err : Qpos.
*)
Let err := Qpos_max ((1 # 4 * P_of_succ_nat (pred n)) * w)
 ((1 # 4 * P_of_succ_nat (pred m)) * h).

(** [PlotQ] is the function that does all the work. *)
Definition PlotQ := RasterizeQ2 (approximate (graphQ (uc_compose clip f)) err) n m t l b r.

Open Local Scope raster.

(** The resulting plot is close to the graph of [f] *)
Theorem Plot_correct :
ball (err + Qpos_max ((1 # 2 * P_of_succ_nat (pred n)) * w)
        ((1 # 2 * P_of_succ_nat (pred m)) * h))
 (graphQ (uc_compose clip f))
 (Cunit (InterpRaster PlotQ (l,t) (r,b))).
Proof.
 assert (Hw:=(ProjT2 (Qpos_lt_plus Hlr))).
 assert (Hh:=(ProjT2 (Qpos_lt_plus Hbt))).
 fold w in Hw.
 fold h in Hh.
 simpl in Hw, Hh.
 apply ball_triangle with (Cunit (approximate (graphQ (uc_compose clip f)) err)).
  apply ball_approx_r.
 unfold Compact.
 rewrite -> ball_Cunit.
 apply ball_sym.
 assert (L:st_eq ((l,t):Q2) (l,b + h)).
  split; simpl.
   reflexivity.
  auto.
 set (Z0:=(l, t):Q2) in *.
 set (Z1:=(r, b):Q2) in *.
 set (Z:=(l, (b + h)):Q2) in *.
 rewrite -> L.
 setoid_replace Z1 with (l+w,b).
  unfold Z, PlotQ.
  rewrite -> Hw, Hh.
  destruct n; try discriminate.
  destruct m; try discriminate.
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
