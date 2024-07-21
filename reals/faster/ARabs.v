Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
From Coq Require Import Qabs.
Require Import CoRN.model.metric2.Qmetric
  CoRN.model.totalorder.QposMinMax 
  CoRN.model.totalorder.QMinMax
  CoRN.reals.fast.CRabs 
  CoRN.reals.faster.ARArith.

(** Absolute Value *)

Section ARabs.
Context `{AppRationals AQ}.

Definition AQabs : AQ -> AQ
  := fun q => proj1_sig (abs_sig q). 

Lemma aq_abs : forall q:AQ, '(proj1_sig (abs_sig q)) == Qabs ('q).
Proof.
  intro q. destruct (abs_sig q). unfold proj1_sig.
  destruct a.
  destruct aq_ring_morphism.
  destruct aq_order_embed.
  destruct semiringmor_plus_mor.
  destruct monmor_sgmor.
  destruct sgmor_setmor. 
  assert (AQtoQ 0 == 0) by (apply rings.preserves_0).
  destruct (Qlt_le_dec ('q) 0).
  - rewrite Qabs_neg. rewrite <- aq_opp.
    apply sm_proper, H6. 
    apply order_embedding_reflecting.
    rewrite H7.
    apply Qlt_le_weak, q0.
    apply Qlt_le_weak, q0.
  - rewrite Qabs_pos. 2: exact q0.
    apply sm_proper, H5.
    apply order_embedding_reflecting.
    rewrite H7. exact q0.
Qed.

Lemma AQabs_triangle_reverse
  : forall a b : AQ, Qabs (' AQabs a - ' AQabs b) <= Qabs ('a - 'b).
Proof.
  intros a b. unfold AQabs.
  rewrite aq_abs, aq_abs.
  apply Qabs_case.
  - intros _. apply Qabs_triangle_reverse.
  - intros. 
    apply (Qle_trans _ (Qabs ('b) - Qabs ('a))).
    ring_simplify; apply Qle_refl.
    rewrite <- (Qabs_opp (' a - ' b)).
    setoid_replace (- (' a - ' b))%Q with (' b - ' a)%Q.
    apply Qabs_triangle_reverse.
    unfold equiv, stdlib_rationals.Q_eq. 
    ring.
Qed.

Lemma AQabs_uc_prf
  : is_UniformlyContinuousFunction
      (AQabs : AQ_as_MetricSpace -> AQ_as_MetricSpace) Qpos2QposInf.
Proof.
  intros d a b Hab.
  simpl in Hab.
  unfold Qball in Hab.
  rewrite <- AbsSmall_Qabs in Hab.
  simpl. unfold Qball.
  rewrite <- AbsSmall_Qabs.
  exact (Qle_trans _ _ _ (AQabs_triangle_reverse _ _) Hab).
Qed.

Local Open Scope uc_scope.

Definition AQabs_uc : AQ_as_MetricSpace --> AQ_as_MetricSpace
  := Build_UniformlyContinuousFunction AQabs_uc_prf.

Definition ARabs : AR --> AR := Cmap AQPrelengthSpace AQabs_uc.

(* The approximations of the absolute value are what we expect. *)
Lemma ARabs_approx : forall (e:Qpos) (x:AR),
    approximate (ARabs x) e = AQabs (approximate x e).
Proof.
  reflexivity.
Qed.

Lemma ARtoCR_preserves_abs
  : forall x : AR, cast AR CR (ARabs x) = CRabs (cast AR CR x).
Proof.
  intro x.
  unfold cast, ARtoCR, ARtoCR_uc.
  unfold MetricMorphisms.Eembed.
  unfold ARabs, CRabs.
  rewrite <- (fast_MonadLaw2
               AQPrelengthSpace
               (MetricMorphisms.EPrelengthSpace QPrelengthSpace (cast AQ Q_as_MetricSpace))
               (MetricMorphisms.metric_embed_uc (cast AQ Q_as_MetricSpace))
               AQabs_uc).
  rewrite <- (fast_MonadLaw2
               (MetricMorphisms.EPrelengthSpace QPrelengthSpace (cast AQ Q_as_MetricSpace))
               QPrelengthSpace Qabs_uc
               (MetricMorphisms.metric_embed_uc (cast AQ Q_as_MetricSpace)) x).
  apply Cmap_wd. 2: reflexivity.
  apply ucEq_equiv.
  intro d. simpl. apply Qball_0, aq_abs.
Qed. 

Lemma ARabs_AbsSmall : forall a b : AR, ARle (ARabs b) a <-> (ARle (-a) b /\ ARle b a).
Proof.
  intros a b. pose proof CRabs_AbsSmall. split.
  - intro H6.
    assert ((CRabs (cast AR CR b) <= (cast AR CR a))%CR).
    { apply ARtoCR_preserves_le in H6.
      rewrite ARtoCR_preserves_abs in H6. exact H6. }
    specialize (H5 ('a) ('b)) as [H5 _].
    specialize (H5 H7).
    split; apply ARtoCR_preserves_le.
    rewrite ARtoCR_preserves_opp.
    apply H5. apply H5.
  - intros [H6 H7].
    apply (ARtoCR_preserves_le (-a) b) in H6.
    apply (ARtoCR_preserves_le b a) in H7.
    specialize (H5 ('a) ('b)) as [_ H5].
    apply ARtoCR_preserves_le.
    rewrite ARtoCR_preserves_abs. apply H5.
    split. rewrite <- ARtoCR_preserves_opp.
    exact H6. exact H7. 
Qed. 

Lemma ARle_abs : forall x:AR, ARle x (ARabs x).
Proof.
  intro x. apply ARtoCR_preserves_le.
  rewrite ARtoCR_preserves_abs.
  apply CRle_abs.
Qed.

Lemma ARabs_opp : forall x:AR, ARabs (-x) = ARabs x.
Proof.
  intro x.
  apply (injective ARtoCR).
  pose proof (ARtoCR_preserves_abs (-x)).
  unfold cast in H5. rewrite H5. clear H5.
  pose proof (ARtoCR_preserves_abs x).
  unfold cast in H5. rewrite H5.
  rewrite (ARtoCR_preserves_opp x).
  apply CRabs_opp.
Qed.

Lemma ARabs_pos : forall x:AR, ARle 0 x -> ARabs x = x.
Proof.
  intros x xpos.
  apply (injective ARtoCR).
  pose proof (ARtoCR_preserves_abs x).
  unfold cast in H5. rewrite H5. clear H5.
  apply CRabs_pos.
  rewrite <- ARtoCR_preserves_0.
  apply (ARtoCR_preserves_le AR0 x), xpos.
Qed.

Lemma ARabs_neg : forall x:AR, ARle x 0 -> ARabs x = -x.
Proof.
  intros x xneg.
  apply (injective ARtoCR).
  pose proof (ARtoCR_preserves_abs x).
  unfold cast in H5. rewrite H5. clear H5.
  rewrite CRabs_neg.
  symmetry. apply ARtoCR_preserves_opp.
  rewrite <- ARtoCR_preserves_0.
  apply (ARtoCR_preserves_le x AR0), xneg.
Qed.

End ARabs.
