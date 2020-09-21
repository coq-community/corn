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

(* 7 is above 2 pi, which finishes a circle. *)
Lemma zeroSeven : (0 <= 7)%Q.
Proof. discriminate. Qed.

Definition Circle_faster : raster _ _
  := let (_,r) := ARplot.PlotPath 0 7 zeroSeven (-(1)) 1 (reflexivity _)
                             (-(1)) 1 (reflexivity _) 10 10 CirclePath_faster
      in r.

(* This is the approximation of the circle that will be rasterized.
   For a 10x10 pixel plot, the precision is 1/40.
   But we approximate by real numbers instead of rational numbers. *)
Definition Circle_approx : list (prod AQ_as_MetricSpace AQ_as_MetricSpace)
  := map (fun x => approximate x (Qpos2QposInf (1#40)%Qpos))
         (map CirclePath_faster
              (approximate (IabCompact _ _ zeroSeven)
                           (FinEnum_map_modulus (1 # 1) (mu CirclePath_faster)
                                                (1#40)%Qpos))).

End PlotCirclePath.

Definition Circle_approx_bigD
  := @Circle_approx bigD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bigD_appRat.
Time Compute Circle_approx_bigD.


(* 12 seconds :-( *)
Definition Circle_bigD : raster _ _
  := Eval vm_compute in
      @Circle_faster bigD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bigD_appRat.

Local Open Scope raster.
DumpGrayMap Circle_bigD.
(* Now have a look at plot.pgm *)


Definition CircleFunction_aux
  : ProductMS Q_as_MetricSpace Q_as_MetricSpace --> ProductMS CR CR
  := together cos_uc sin_uc.

Definition CirclePath : Q_as_MetricSpace --> Complete Q2:= 
  (uc_compose (uc_compose Couple CircleFunction_aux) (diag Q_as_MetricSpace)).
(* The following hangs:
Definition CirclePath': UCFunction Q R2:= 
  ucFunction (fun q:Q => Couple (cos_uc q, sin_uc q)).*)

Definition Circle_approx_fast : list Q2
  := map (fun x => approximate x (Qpos2QposInf (1#40)%Qpos))
         (approximate (Plot.PathImage CirclePath 0 7 zeroSeven)
                      (Qpos2QposInf (1#40)%Qpos)).
Time Compute Circle_approx_fast.


(* 9 seconds :-( *)
(* The raster must be evaluated before being plotted by DumpGrayMap,
   here with vm_compute. *)
Definition Circle : raster _ _
  := Eval vm_compute in
      (let (_,r) := Plot.PlotPath 0 7 (reflexivity _) (-(1)) 1 (reflexivity _)
                             (-(1)) 1 (reflexivity _) 100 100 CirclePath
      in r). 

DumpGrayMap Circle.
(* Now have a look at plot.pgm *)


