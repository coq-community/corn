Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import
  Coq.Program.Program Coq.QArith.QArith CoRN.util.Qdlog Coq.ZArith.ZArith CoRN.reals.fast.Compress
  CoRN.metric2.MetricMorphisms CoRN.model.metric2.Qmetric CoRN.reals.faster.ARArith
  MathClasses.theory.int_pow MathClasses.theory.nat_pow
  MathClasses.implementations.stdlib_rationals MathClasses.implementations.stdlib_binary_integers.

Instance Q_approx: AppApprox Q := λ x k, 
  match k with
  | Zneg p => approximateQ x (2 ^ p)
  | _ => x
  end.

Lemma Q_approx_correct (x : Q) (k : Z) : Qball (2 ^ k) (app_approx x k) x.
Proof.
  destruct k as [|p|].
  - apply ball_refl. discriminate.
  - apply ball_refl. apply Qpower.Qpower_pos_positive. discriminate.
  - unfold app_approx, Q_approx.
  setoid_replace (2 ^ Zneg p)%Q with (1 # (2 ^ p))%Q.
   now apply ball_sym, approximateQ_correct.
  change (/ Qpower (inject_Z 2%Z) (Zpos p) == 1 # 2 ^ p).
  rewrite <-Qpower.Zpower_Qpower; auto with zarith.
  now rewrite <- Zpower_Ppow.
Qed.

Instance Q_approx_div: AppDiv Q := λ x y k, app_approx (x / y) k.

Instance inject_Q_Q: Cast Q Q_as_MetricSpace := Datatypes.id.
Instance inverse_Q_Q: AppInverse inject_Q_Q := λ x ε, app_approx x (Qdlog2 (proj1_sig ε)).

Instance: AppRationals Q.
Proof.
  split; try apply _.
     repeat (split; try apply _).
    (* regression in type_classes *) admit. admit. admit. admit. admit. admit.  
    split; try apply _.  Admitted. (*intros.
    apply ball_weak_le with (2 ^ Qdlog2 ε)%Qpos.
     now apply (Qpos_dlog2_spec ε).
    now apply Q_approx_correct.
   intros. now apply Q_approx_correct.
  intros. now apply Q_approx_correct.
Qed. *)

Notation ARQ := (AR (AQ:=Q)).
