Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import
  CoRN.reals.fast.CRarctan_small CoRN.reals.fast.CRarctan CoRN.reals.fast.CRpi_fast
  CoRN.metric2.MetricMorphisms CoRN.reals.faster.ARpi CoRN.reals.faster.ARarctan_small.
Require Export
  CoRN.reals.faster.ARArith.

Section ARarctan.
Context `{AppRationals AQ}.

Program Definition AQarctan_big_pos {a : AQ} `(Pa : 1 < a) : AR := 
  AQpi (1 ≪ (-1)) - AQarctan_small_pos (num:=1) (den:=a) _.
Next Obligation. split. apply semirings.le_0_1. easy. Qed. 

Lemma AQarctan_big_pos_correct {a : AQ} `(Pa : 1 < a) : 
  'AQarctan_big_pos Pa = rational_arctan ('a).
Proof.
  unfold AQarctan_big_pos.
  rewrite rings.preserves_minus.
  rewrite ARtoCR_preserves_AQpi.
  rewrite aq_shift_opp_1, rings.preserves_1.
  rewrite AQarctan_small_pos_correct.
  mc_setoid_replace ('1 / 'a : Q) with (/'a).
   apply rational_arctan_half_pi.
   transitivity (1:Q).
    now apply (semirings.lt_0_1 (R:=Q)).
   now apply semirings.preserves_gt_1.
  now rewrite rings.preserves_1, rings.mult_1_l.
Qed.

Program Definition AQarctan_mid_pos {a : AQ} (Ha : 0 < a) : AR :=
  AQpi (1 ≪ (-2)) + AQarctan_small (num:=a - 1) (den:=a + 1) _.
Next Obligation.
  split.
   rewrite rings.negate_plus_distr.
   apply (strictly_order_preserving (+ _)).
   now apply rings.between_pos.
  apply (strictly_order_preserving (_ +)).
  apply rings.between_pos.
  apply semirings.lt_0_1.
Qed.

Lemma AQarctan_mid_pos_correct {a : AQ} `(Pa : 0 < a) : 
  'AQarctan_mid_pos Pa = rational_arctan ('a).
Proof.
  unfold AQarctan_mid_pos.
  rewrite rings.preserves_plus.
  rewrite ARtoCR_preserves_AQpi.
  rewrite AQarctan_small_correct.
  rewrite aq_shift_opp_2, rings.preserves_1.
  mc_setoid_replace ('(a - 1) / '(a + 1) : Q) with (('a - 1) / ('a + 1) : Q).
   apply rational_arctan_fourth_pi.
   now apply semirings.preserves_pos.
  rewrite rings.preserves_minus, rings.preserves_plus.
  now rewrite rings.preserves_1.
Qed.

Lemma AQarctan_pos_prf1 {a : AQ} : 0 ≤ a → a ≤ 1 ≪ (-1) → 0 ≤ a < 1.
Proof.
  split; trivial.
  apply orders.le_lt_trans with (1 ≪ (-1)); [easy |].
  apply (strictly_order_reflecting (cast AQ Q)).
  rewrite aq_shift_opp_1, rings.preserves_1.
  split; easy.
Qed.

Lemma AQarctan_pos_prf2 {a : AQ} : ¬a ≤ 1 ≪ (-1) → 0 < a.
Proof.
  intros. apply orders.lt_le_trans with (1 ≪ (-1)).
   apply (strictly_order_reflecting (cast AQ Q)).
   rewrite aq_shift_opp_1, rings.preserves_0, rings.preserves_1.
   split; easy.
  now apply orders.le_flip.
Qed.

Lemma AQarctan_pos_prf3 {a : AQ} : ¬a ≤ 2 → 1 < a.
Proof.
  intros. apply orders.lt_le_trans with 2.
   apply semirings.lt_1_2.
  now apply orders.le_flip.
Qed.

Definition AQarctan_pos {a : AQ} (Pa1 : 0 ≤ a) : AR :=
  match decide_rel (≤) a (1 ≪ (-1)) with
  | left Pa2 => AQarctan_small_pos (AQarctan_pos_prf1 Pa1 Pa2)
  | right Pa2 => match decide_rel (≤) a 2 with
     | left Pa3 => AQarctan_mid_pos (AQarctan_pos_prf2 Pa2)
     | right Pa3 => AQarctan_big_pos (AQarctan_pos_prf3 Pa3)
     end
  end.

Lemma AQarctan_pos_correct {a : AQ} `(Pa : 0 ≤ a) : 
  'AQarctan_pos Pa = rational_arctan ('a).
Proof.
  unfold AQarctan_pos.
  case (decide_rel _); intros.
   rewrite AQarctan_small_pos_correct.
   mc_setoid_replace ('a / '1 : Q) with ('a).
    reflexivity.
   rewrite rings.preserves_1.
   rewrite dec_fields.dec_recip_1.
   now apply rings.mult_1_r.
  case (decide_rel _); intros.
   apply AQarctan_mid_pos_correct.
  apply AQarctan_big_pos_correct.
Qed.

Lemma AQarctan_prf {a : AQ} : ¬0 ≤ a → 0 ≤ - a.
Proof. intros. apply rings.flip_nonpos_negate. now apply orders.le_flip. Qed.

Definition AQarctan (a : AQ) : AR :=
  match decide_rel (≤) 0 a with
  | left Pa => AQarctan_pos Pa
  | right Pa => -AQarctan_pos (AQarctan_prf Pa)
  end.

Lemma AQarctan_correct (a : AQ) : 
  'AQarctan a = rational_arctan ('a).
Proof.
  unfold AQarctan.
  case (decide_rel _); intros.
   apply AQarctan_pos_correct.
  rewrite rings.preserves_negate.
  rewrite AQarctan_pos_correct.
  rewrite rings.preserves_negate.
  apply rational_arctan_opp.
Qed.

Local Obligation Tactic := idtac.
Program Definition ARarctan_uc := unary_complete_uc 
  Qmetric.QPrelengthSpace (cast AQ Qmetric.Q_as_MetricSpace) AQarctan arctan_uc _.
Next Obligation. apply AQarctan_correct. Qed. 

Definition ARarctan := Cbind AQPrelengthSpace ARarctan_uc.

Lemma ARtoCR_preserves_arctan x : 'ARarctan x = arctan ('x).
Proof. apply preserves_unary_complete_fun. Qed.
End ARarctan.
