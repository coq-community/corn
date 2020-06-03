Require Import CoRN.algebra.RSetoid.
Require Import
  CoRN.stdlib_omissions.Q
  CoRN.reals.fast.CRpi_fast CoRN.reals.fast.CRarctan_small
  MathClasses.interfaces.abstract_algebra CoRN.reals.faster.ARarctan_small.

Section ARpi.
Context `{AppRationals AQ}.

Lemma AQpi_prf (x : Z) : 1 < x → 0 ≤ 1 < ('x : AQ).
Proof. split. now apply semirings.le_0_1. now apply semirings.preserves_gt_1. Qed.

Program Definition AQpi (x : AQ) : AR :=
  (ARscale ('176%Z * x) (AQarctan_small_pos (AQpi_prf (57%Z) _)) +
    ARscale ('28%Z * x) (AQarctan_small_pos (AQpi_prf (239%Z) _))) +
  (ARscale ('(-48)%Z * x) (AQarctan_small_pos (AQpi_prf (682%Z) _)) +
    ARscale ('96%Z * x) (AQarctan_small_pos (AQpi_prf (12943%Z) _))).
Obligation Tactic := compute; now split.
Solve Obligations. 

Lemma ARtoCR_preserves_AQpi x : 'AQpi x = r_pi ('x).
Proof.
  unfold AQpi, r_pi.
  assert (∀ (k : Z) (d : positive) (Pnd: 0 ≤ 1 < cast Z AQ d) (Pa : (0 <= 1#d < 1)%Q),
    'ARscale ('k * x) (AQarctan_small_pos Pnd) = scale (inject_Z k * 'x) (rational_arctan_small_pos Pa)) as P.
   intros.
   rewrite ARtoCR_preserves_scale.
   rewrite rings.preserves_mult, AQtoQ_ZtoAQ.
   rewrite ARtoCR_preserves_arctan_small_pos.
   rewrite rational_arctan_small_pos_wd.
    reflexivity.
   now rewrite rings.preserves_1, AQtoQ_ZtoAQ.
  rewrite !rings.preserves_plus.
  rewrite !P.
  apply reflexivity.
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
