(* CRpi_fast is better for computation, but CRpi_slow is faster to compile,
and may be prefered for development. *)
(* Require Export CRpi_slow. *)
Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.model.totalorder.QposMinMax.
Require Export CoRN.reals.fast.CRpi_fast.
Require Import CoRN.reals.fast.CRsign.

Lemma CRpi_pos : (0 < CRpi)%CR.
Proof. CR_solve_pos (1#10)%Qpos. Qed.
