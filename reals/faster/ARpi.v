Require Import
  MathClasses.interfaces.abstract_algebra
  CoRN.stdlib_omissions.Q
  CoRN.algebra.RSetoid
  CoRN.metric2.Metric
  CoRN.metric2.UniformContinuity
  CoRN.reals.fast.CRpi_fast
  CoRN.reals.fast.CRarctan_small
  CoRN.reals.faster.ARarctan_small.

Section ARpi.
Context `{AppRationals AQ}.

Lemma AQpi_prf (x : Z) : 1 < x → -('x : AQ) < 1 < ('x : AQ).
Proof.
  split. 2: apply semirings.preserves_gt_1, H5.
  rewrite <- (rings.preserves_1 (f:=cast Z AQ)).
  rewrite <- (rings.preserves_negate (f:=cast Z AQ)).
  apply (strictly_order_preserving (cast Z AQ)).
  unfold one, stdlib_binary_integers.Z_1.
  rewrite <- (Z.opp_involutive 1).
  apply Z.gt_lt, CornBasics.Zlt_opp.
  apply (Z.lt_trans _ 1). reflexivity. exact H5.
Qed.

Lemma ZtoAQ_pos : forall (z:Z), 0 < z -> 0 < ('z : AQ).
Proof.
  intros z zpos.
  pose proof (rings.preserves_0 (f:=cast Z AQ)).
  rewrite <- H5.
  exact (strictly_order_preserving (cast Z AQ) 0 z zpos).
Qed.

Definition AQpi (x : AQ) : msp_car AR :=
  ucFun (ARscale (' 176%Z * x))
    (AQarctan_small (AQpi_prf 57 eq_refl) (ZtoAQ_pos 57 eq_refl)) +
  ucFun (ARscale (' 28%Z * x))
    (AQarctan_small (AQpi_prf 239 eq_refl) (ZtoAQ_pos 239 eq_refl)) +
  (ucFun (ARscale (' (-48)%Z * x))
     (AQarctan_small (AQpi_prf 682 eq_refl) (ZtoAQ_pos 682 eq_refl)) +
   ucFun (ARscale (' 96%Z * x))
     (AQarctan_small (AQpi_prf 12943 eq_refl) (ZtoAQ_pos 12943 eq_refl))).

Lemma ARtoCR_preserves_AQpi x : 'AQpi x = r_pi ('x).
Proof.
  unfold AQpi, r_pi.
  assert (∀ (k : Z) (d : positive)
            (Pnd: -(cast Z AQ (Zpos d)) < 1 < cast Z AQ (Zpos d))
            (dpos : 0 < cast Z AQ (Zpos d))
            (Pa : (-1 <= 1#d <= 1)%Q),
             ' ucFun (ARscale ('k * x)) (AQarctan_small Pnd dpos)
             = ucFun (scale (inject_Z k * 'x)) (rational_arctan_small Pa)) as PP.
  { intros.
    rewrite ARtoCR_preserves_scale.
    apply Cmap_wd.
    rewrite rings.preserves_mult, AQtoQ_ZtoAQ.
    reflexivity.
    rewrite AQarctan_small_correct.
    rewrite rational_arctan_small_wd.
    reflexivity.
    rewrite rings.preserves_1.
    pose proof (AQtoQ_ZtoAQ (Zpos d)). rewrite H5.
    reflexivity. }
  assert (forall x y : msp_car AR, ARtoCR (x+y) = 'x + 'y) as plusMorph.
  { intros x0 y. apply (rings.preserves_plus x0 y). }
  unfold cast. unfold cast in plusMorph.
  rewrite plusMorph. apply ucFun2_wd. 
  rewrite plusMorph. apply ucFun2_wd.
  apply PP. apply PP.
  rewrite plusMorph.
  apply ucFun2_wd. apply PP. apply PP.
Qed.

Definition ARpi := AQpi 1.

Lemma ARtoCR_preserves_pi : 'ARpi = CRpi.
Proof.
  unfold ARpi, CRpi.
  rewrite ARtoCR_preserves_AQpi.
  rewrite rings.preserves_1. 
  reflexivity.
Qed.

End ARpi.
