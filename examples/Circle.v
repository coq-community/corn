Require Import Plot RasterQ Qmetric.
(** Plotting graphs in the plane *)
(* This file is based on examples/Plot.v *)
(* I define the image of a path, a [Compact] subset of the plane.*)
(* Finally, plot a hi-res Circle*)

Notation Q:=Q_as_MetricSpace.
Notation R2:=(Complete Q2).

(* Should be moved *)
Lemma stableComplete(X:MetricSpace):stableMetric X -> stableMetric (Complete X).
Proof.
unfold stableMetric. simpl. unfold regFunBall. intuition.
Qed.

Definition stableR2:=(stableComplete Q2 stableQ2).

Open Local Scope uc_scope.

Require Import metric2.Classified.


(* Should be moved *)
Section diag.
Variable X:MetricSpace.
Definition diag_raw:X->(ProductMS X X):=fun x=>(x,x).
Lemma diag_uc:(is_UniformlyContinuousFunction diag_raw (fun e => e)%Qpos).
Proof.
unfold diag_raw, is_UniformlyContinuousFunction. simpl. unfold prod_ball. intuition.
Qed.
Definition diag:X-->(ProductMS X X):=Build_UniformlyContinuousFunction diag_uc.
End diag.

Require Import Interval.
Open Local Scope uc_scope.

Section PathImage.
Variable path:Q-->R2.
Variable CompleteMult:(Complete R2 -->R2).
Variable (l r:Q).
Hypothesis Hlr : l < r.
(** The image of a path as a [Compact] subset of the plane.*)
Definition PathImage:=(CompactImage (1#1)%Qpos stableR2 plFEQ path
(CompactIntervalQ (Qlt_le_weak _ _ Hlr))).
End PathImage.

Section PlotPath.
Variable (from to:Q).
Hypothesis Hfromto:from<to.

Variable (l r:Q).
Hypothesis Hlr : l < r.

Variable (b t:Q).
Hypothesis Hbt : b < t.

Variable n m : nat.

Let w := proj1_sigT _ _ (Qpos_lt_plus Hlr).
Let h := proj1_sigT _ _ (Qpos_lt_plus Hbt).

(**
Half the error in the Plot example, since we need to approximate twice.
*)
Let err := Qpos_max ((1 # 8 * P_of_succ_nat (pred n)) * w)
 ((1 # 8 * P_of_succ_nat (pred m)) * h).

Variable path:Q-->R2.
(** The actual plot function *)
Definition PlotPath := (n, m, 2, (RasterizeQ2 
(approximate 
(FinCompact stableQ2 stableR2 (approximate (PathImage path from to Hfromto) err))
err) n m t l b r )).
End PlotPath.

Section PlotCirclePath.
Require Import CRtrans.
Require Import Vector.
Export Vector.VectorNotations.

Definition CircleFunction_aux:=(together cos_uc sin_uc).

Definition CirclePath:Q --> R2:= 
  (Couple ∘ CircleFunction_aux ∘ (diag Q)).
(* The following hangs:
Definition CirclePath': UCFunction Q R2:= 
  ucFunction (fun q:Q => Couple (cos_uc q, sin_uc q)).*)

Notation star := (@refl_equal _ Lt).
Notation "∗" := star.
Local Open Scope raster.

Notation "'Vcons'" := Vector.cons.
Notation "'Vnil'" := Vector.nil.
Notation "#  a b" := (Vcons (Vector.t bool _) a _ b)
  (at level 0, a, b at level 0) : raster.

Notation "'#' a" := (Vcons (Vector.t bool _) a _ (Vnil _))
  (at level 0, a, b at level 0) : raster.

Notation "0 # a" := (Vcons bool true _ a) (at level 0, right associativity) : raster.
Notation " # " := (Vnil bool) (at level 0, right associativity) : raster.
Notation "1 # a" := (Vcons bool false _ a) (at level 0, right associativity) : raster.
(*
Notation "░ a" := (Vcons bool false _ a) (at level 0, right associativity, only parsing) : raster_parsing.
*)

Definition Circle:=Eval vm_compute in  (PlotPath 0 7 star (-(1)) 1 star (-(1)) 1 star 40 40 CirclePath).
Add ML Path "dump".
Declare ML Module "dump".
Dump Circle.
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