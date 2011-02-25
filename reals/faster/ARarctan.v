Require Import
  CRarctan_small CRarctan CRpi_fast
  MetricMorphisms ARpi ARarctan_small.
Require Export
  ARArith.

Section ARarctan.
Context `{AppRationals AQ}.

Program Definition AQarctan_big_pos {a : AQ} `(Pa : 1 ≤ 'a) : AR := 
  AQpi (1 ≪ -(1 : Z)) - AQarctan_small_pos (num:=1) (den:=a) _.
Next Obligation.
  rewrite rings.preserves_1, left_identity.
  split.
   apply fields.nonneg_dec_mult_inv_compat.
   now transitivity (1:Q).
  apply fields.flip_dec_mult_inv_l.
   now apply semirings.sprecedes_0_1.
  now rewrite fields.dec_mult_inv_1.
Qed.

Lemma AQarctan_big_pos_correct {a : AQ} `(Pa : 1 ≤ 'a) : 
  ARtoCR (AQarctan_big_pos Pa) = rational_arctan_big_pos Pa.
Proof.
  unfold AQarctan_big_pos, rational_arctan_big_pos.
  rewrite rings.preserves_minus.
  rewrite ARtoCR_preserves_AQpi.
  rewrite Zshift_opp_1, rings.preserves_1.
  rewrite ARtoCR_preserves_arctan_small_pos.
Admitted.

Program Definition AQarctan_mid_pos {a : AQ} (Ha : 0 ≤ 'a) : AR :=
  AQpi (1 ≪ -(2 : Z)) - AQarctan_small_pos (num:=a - 1) (den:=a + 1) _.
Next Obligation.
Admitted.

Program Definition AQarctan_pos {a : AQ} (Ha : 0 ≤ 'a) : AR :=
  match decide_rel (≤) a (1 ≪ -(1 : Z)) with
  | left P1 => AQarctan_small_pos (num:=a) (den:=1) _
  | right P1 => match decide_rel (≤) a 2 with
     | left P2 => AQarctan_mid_pos (a:=a) _
     | right P2 => AQarctan_big_pos (a:=a) _
     end
  end.
Next Obligation. Admitted.
Next Obligation. Admitted.

Program Definition AQarctan (a : AQ) : AR :=
  match decide_rel (≤) 0 a with
  | left P => AQarctan_pos (a:=a) _
  | right P => -(AQarctan_pos (a:=-a) _)
  end.
Next Obligation. Admitted.
Next Obligation. Admitted.

Lemma AQarctan_correct (a : AQ) : 
  ARtoCR (AQarctan a) = rational_arctan ('a).
Proof. Admitted.

Local Obligation Tactic := idtac.
Program Definition ARarctan_uc := 
  unary_complete_uc Qmetric.QPrelengthSpace coerce AQarctan arctan_uc _.
Next Obligation. apply AQarctan_correct. Qed. 

Definition ARarctan := Cbind AQPrelengthSpace ARarctan_uc.

Lemma ARtoCR_preserves_exp x : ARtoCR (ARarctan x) = arctan (ARtoCR x).
Proof. apply preserves_unary_complete_fun. Qed.
End ARarctan.
