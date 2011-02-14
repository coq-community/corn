Require Import
  CRpi_fast CRarctan_small
  abstract_algebra ARarctan_small.

Section ARpi.
Context `{AppRationals AQ}.

Program Definition AQpi (x : AQ) : AR :=
  (ARscale ('176%Z * x) (AQarctan_small_pos (num:=1) (den:='57%Z) _) +
    ARscale ('28%Z * x) (AQarctan_small_pos (num:=1) (den:='239%Z) _)) +
  (ARscale ('(-48)%Z * x) (AQarctan_small_pos (num:=1) (den:='682%Z) _) +
    ARscale ('96%Z * x) (AQarctan_small_pos (num:=1) (den:='12943%Z) _)).
Solve Obligations using split; now rewrite rings.preserves_1, AQtoQ_ZtoAQ.

Lemma ARtoCR_preserves_AQpi x : ARtoCR (AQpi x) = r_pi ('x).
Proof.
  unfold AQpi, r_pi.
  assert (∀ (k : Z) (d : positive) (p1 : 0 ≤ '1 / '('(d : Z) : AQ) ≤ 1) (p2 : 0 ≤ 1 # d ≤ 1), 
    ARtoCR (ARscale ('k * x) (AQarctan_small_pos p1)) = scale (k * 'x) (rational_arctan_small_pos (a:=1 # d) p2)) as P.
   intros.
   rewrite ARtoCR_preserves_scale.
   rewrite rings.preserves_mult, AQtoQ_ZtoAQ.
   rewrite ARtoCR_preserves_arctan_small_pos.
   rewrite rational_arctan_small_pos_wd.
    reflexivity.
   now rewrite rings.preserves_1, AQtoQ_ZtoAQ.
  rewrite ?ARtoCR_preserves_plus, ?P. 
  f_equiv; f_equiv.
Qed.

Definition ARpi := AQpi 1.

Lemma ARtoCR_preserves_pi: ARtoCR ARpi = CRpi.
Proof.
  unfold ARpi, CRpi.
  rewrite ARtoCR_preserves_AQpi.
  rewrite rings.preserves_1. reflexivity.
Qed.
End ARpi.
