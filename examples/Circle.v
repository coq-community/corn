(** Plotting graphs in the plane *)
(* This file is based on examples/Plot.v *)
(* I define the image of a path, a [Compact] subset of the plane.*)
(* Finally, plot a hi-res Circle*)

Require Import Plot RasterQ Qmetric.
Require Import metric2.Classified.
Require Import Interval.

Local Open Scope uc_scope.

Section PathImage.
Variable path:Q_as_MetricSpace --> Complete Q2.
Variable CompleteMult:(Complete (Complete Q2) --> (Complete Q2)).
Variable (l r:Q).
Hypothesis Hlr : l < r.
(** The image of a path as a [Compact] subset of the plane.*)
Definition PathImage : Compact (Complete Q2)
  := CompactImage (1#1)%Qpos plFEQ path
                  (CompactIntervalQ (Qlt_le_weak _ _ Hlr)).
End PathImage.

Section PlotPath.
Variable (from to:Q).
Hypothesis Hfromto:from<to.

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

Variable path:Q_as_MetricSpace --> Complete Q2.
(** The actual plot function *)
Definition PlotPath : nat * nat * Q * raster n m
  := (n, m, 2, (RasterizeQ2 
(approximate 
(FinCompact Q2 (approximate (PathImage path from to Hfromto) err))
err) n m t l b r )).
End PlotPath.

Section PlotCirclePath.
Require Import CRtrans.

(* TODO faster reals instead of fast reals. *)
Definition CircleFunction_aux
  : ProductMS Q_as_MetricSpace Q_as_MetricSpace --> ProductMS CR CR
  := together cos_uc sin_uc.

Definition CirclePath:Q_as_MetricSpace --> Complete Q2:= 
  (Couple ∘ CircleFunction_aux ∘ (diag Q_as_MetricSpace)).
(* The following hangs:
Definition CirclePath': UCFunction Q R2:= 
  ucFunction (fun q:Q => Couple (cos_uc q, sin_uc q)).*)

Notation star := (@refl_equal _ Lt).
Local Open Scope raster.

(* 9 seconds :-( *)
(* The raster must be evaluated before being plotted by DumpGrayMap,
   here with vm_compute. *)
Definition Circle : raster _ _
  := Eval vm_compute in
      (let (_,r) := PlotPath 0 7 star (-(1)) 1 star (-(1)) 1 star 100 100 CirclePath
      in r). 

Require Import CoRN.dump.theories.Loader.
DumpGrayMap Circle.
(* Now have a look at plot.pgm *)
End PlotCirclePath.


(* We would really like to use the interval [0,2π]. However, real intervals are not yet supported.
Require Import CRpi.
Require Import CRsign.

Lemma H0pi2:('0<('2*CRpi))%CR.
Proof.
unfold CRlt.
Time CR_solve_pos ((6#1))%Qpos.
Qed.
*)
