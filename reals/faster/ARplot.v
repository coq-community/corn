Require Import CoRN.reals.fast.Plot.
Require Import CoRN.reals.faster.ARArith.
Require Import CoRN.reals.faster.ARinterval.
Require Import CoRN.model.metric2.Qmetric.

Local Open Scope uc_scope.

Section ARplot.
Context `{AppRationals AQ}.

Lemma plFEAQ : PrelengthSpace (FinEnum AQ_as_MetricSpace).
Proof.
 apply FinEnum_prelength.
 apply AQLocated.
 exact AQPrelengthSpace.
Qed.

(** The image of a path as a [Compact] subset of the plane.
    A path is usually defined as a continuous function from a
    real interval [l,r], but by continuity it is fully determined
    by its values on rational numbers, which are faster to plot. *)
Definition PathImage {X : MetricSpace} (path : AQ_as_MetricSpace --> X)
           (l r:Q) (Hlr : l <= r)
  : Compact X
  := CompactImage (1#1)%Qpos plFEAQ path (IabCompact l r Hlr). 

End ARplot.

Section PlotPath.
Context `{AppRationals AQ}.

Variable (from to:Q).
Hypothesis Hfromto:from<=to.

Variable (l r:Q).
Hypothesis Hlr : l < r.

Variable (b t:Q).
Hypothesis Hbt : b < t.

Variable n m : nat.

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
Let err := Qpos_max ((1 # 8 * P_of_succ_nat (pred n)) * (exist _ _ wpos))
                    ((1 # 8 * P_of_succ_nat (pred m)) * (exist _ _ hpos)).

Variable path:AQ_as_MetricSpace --> Complete Q2.
(** The actual plot function *)
Definition PlotPath : nat * nat * Q * raster n m
  := (n, m, 2#1, (RasterizeQ2 
(approximate 
(FinCompact Q2 (approximate (PathImage path from to Hfromto) err))
err) n m t l b r )).
End PlotPath.
