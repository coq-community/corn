(* CRpi_fast is better for computation, but CRpi_slow is faster to compile,
and may be prefered for development. *)
(* Require Export CRpi_slow. *)
Require Export CRpi_fast.
Require Import CRsign.

Lemma CRpi_pos : (0 < CRpi)%CR.
Proof. CR_solve_pos (1#10)%Qpos. Qed.
