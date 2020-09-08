Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import
  Coq.QArith.QArith CoRN.util.Qdlog Coq.ZArith.ZArith CoRN.reals.fast.Compress
  CoRN.metric2.MetricMorphisms CoRN.model.metric2.Qmetric CoRN.reals.faster.ARArith
  CoRN.model.totalorder.QposMinMax.

Instance Q_approx: AppApprox Q := λ (x : Q) (k : Z), 
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
  - repeat split; try apply _.
    + intros. rewrite <- H0, <- H. exact H1.
    + intros. rewrite H0, H. exact H1.
    + intros. rewrite <- H0, <- H. exact H1.
    + intros. rewrite H0, H. exact H1.
    + intros. exact H.
    + intros. rewrite <- H0, <- H. exact H1.
    + intros. rewrite H0, H. exact H1.
    + intros. rewrite <- H0, <- H. exact H1.
    + intros. rewrite H0, H. exact H1.
    + intros. exact H.
  - repeat split; try apply _.
    + intros. rewrite <- H0, <- H. exact H1.
    + intros. rewrite H0, H. exact H1.
    + intros. rewrite <- H0, <- H. exact H1.
    + intros. rewrite H0, H. exact H1.
    + intros. exact H.
    + intros. rewrite <- H0, <- H. exact H1.
    + intros. rewrite H0, H. exact H1.
    + intros. rewrite <- H0, <- H. exact H1.
    + intros. rewrite H0, H. exact H1.
    + intros. exact H.
  - repeat split; try apply _.
  - repeat split; try apply _.
    + intros. exact H.
    + intros.
      unfold inject_Q_Q, Datatypes.id.
      unfold app_inverse, inverse_Q_Q.
      pose proof (Q_approx_correct x (Qdlog2 (` ε))) as [H _].
      refine (Qle_trans _ _ _ _ H).
      apply Qopp_le_compat.
      apply (Qpos_dlog2_spec ε).
    + unfold inject_Q_Q, Datatypes.id.
      unfold app_inverse, inverse_Q_Q.
      pose proof (Q_approx_correct x (Qdlog2 (` ε))) as [_ H].
      apply (Qle_trans _ _ _ H).
      apply (Qpos_dlog2_spec ε). 
  - intros. apply Q_approx_correct.
  - intros. apply Q_approx_correct.
Qed.

Notation ARQ := (AR (AQ:=Q)).
