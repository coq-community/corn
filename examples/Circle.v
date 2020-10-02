(** Plotting graphs in the plane *)
(* This file is based on examples/Plot.v *)
(* I define the image of a path, a [Compact] subset of the plane.*)
(* Finally, plot a hi-res Circle*)

Require Import Plot RasterQ Qmetric.
Require Import CoRN.reals.fast.Interval.
Require Import CoRN.metric2.MetricMorphisms.
Require Import CoRN.reals.faster.ARArith.
Require Import ARplot.
Require Import CoRN.reals.faster.ARcos
        CoRN.reals.faster.ARsin
        CoRN.reals.faster.ARexp
        CoRN.reals.faster.ARbigD
        CoRN.reals.faster.ARinterval.
Require Import CoRN.reals.fast.CRtrans.
Require Import CoRN.dump.theories.Loader.

Local Open Scope uc_scope.

Section PlotCirclePath.
Context `{AppRationals AQ}.

Definition CirclePath_faster
  : AQ_as_MetricSpace --> Complete (ProductMS AQ_as_MetricSpace AQ_as_MetricSpace) := 
  (uc_compose (uc_compose Couple (together ARcos_uc ARsin_uc))
              (diag AQ_as_MetricSpace)).

Definition CosPath_faster
  : AQ_as_MetricSpace --> Complete (ProductMS AQ_as_MetricSpace AQ_as_MetricSpace) := 
  (uc_compose (uc_compose Couple (together Cunit ARcos_uc))
              (diag AQ_as_MetricSpace)).

(* 7 is above 2 pi, which finishes a circle. *)
(* Lemma zeroSeven : (0 <= 7)%Q.
Proof. discriminate. Qed. *)

Definition Circle_faster : sparse_raster _ _
  := let (_,r) := ARplot.PlotPath 0 7 (-(1)) 1 (reflexivity _)
                             (-(1)) 1 (reflexivity _) 200 CirclePath_faster
      in r.

Definition Cos_faster : sparse_raster _ _
  := let (_,r) := ARplot.PlotPath 0 7 0 7 (reflexivity _)
                             (-(1)) 1 (reflexivity _) 800 CosPath_faster
      in r.

End PlotCirclePath.

(* 6 seconds *)
Time Definition Circle_bigD : sparse_raster _ _
  := Eval vm_compute in 
      @Circle_faster bigD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bigD_appRat.

DumpGrayMap Circle_bigD.
(* Now have a look at plot.pgm *)

Time Definition Cos_bigD : sparse_raster _ _
  := Eval vm_compute in 
      @Cos_faster bigD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bigD_appRat.

DumpGrayMap Cos_bigD.
(* Now have a look at plot.pgm *)


Definition CircleFunction_aux
  : ProductMS Q_as_MetricSpace Q_as_MetricSpace --> ProductMS CR CR
  := together cos_uc sin_uc.

Definition CirclePath : Q_as_MetricSpace --> Complete Q2:= 
  (uc_compose (uc_compose Couple CircleFunction_aux) (diag Q_as_MetricSpace)).
(* The following hangs:
Definition CirclePath': UCFunction Q R2:= 
  ucFunction (fun q:Q => Couple (cos_uc q, sin_uc q)).*)


(* 20 seconds *)
(* The raster must be evaluated before being plotted by DumpGrayMap,
   here with vm_compute. *)
Time Definition Circle : sparse_raster _ _
  := Eval vm_compute in
      (let (_,r) := Plot.PlotPath 0 7 (reflexivity _) (-(1)) 1 (reflexivity _)
                             (-(1)) 1 (reflexivity _) 200 200 CirclePath
      in r). 

DumpGrayMap Circle.
(* Now have a look at plot.pgm *)


