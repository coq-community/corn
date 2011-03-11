Require Import
  CRarctan_small CRarctan CRpi_fast
  MetricMorphisms ARpi ARarctan_small.
Require Export
  ARArith.

Section ARarctan.
Context `{AppRationals AQ}.

Program Definition AQarctan_big_pos {a : AQ} `(Pa : 1 < a) : AR := 
  AQpi (1 ≪ (-1)) - AQarctan_small_pos (num:=1) (den:=a) _.
Next Obligation. split. apply semirings.precedes_0_1. easy. Qed. 

Lemma AQarctan_big_pos_correct {a : AQ} `(Pa : 1 < a) : 
  ARtoCR (AQarctan_big_pos Pa) = rational_arctan ('a).
Proof.
  unfold AQarctan_big_pos.
  rewrite rings.preserves_minus.
  rewrite ARtoCR_preserves_AQpi.
  rewrite Zshift_opp_1, rings.preserves_1.
  rewrite AQarctan_small_pos_correct.
  ms_setoid_replace ('1 / 'a : Q) with (/'a).
   apply rational_arctan_half_pi.
   apply stdlib_rationals.Qlt_coincides.
   transitivity (1:Q).
    now apply semirings.sprecedes_0_1.
   now apply semirings.preserves_gt1.
  now rewrite rings.preserves_1, rings.mult_1_l.
Qed.

Program Definition AQarctan_mid_pos {a : AQ} (Ha : 0 < a) : AR :=
  AQpi (1 ≪ (-2)) + AQarctan_small (num:=a - 1) (den:=a + 1) _.
Next Obligation.
  split.
   rewrite rings.opp_distr.
   apply (strictly_order_preserving (+ _)).
   now apply rings.between_pos.
  apply (strictly_order_preserving (_ +)).
  apply rings.between_pos.
  apply semirings.sprecedes_0_1.
Qed.

Lemma AQarctan_mid_pos_correct {a : AQ} `(Pa : 0 < a) : 
  ARtoCR (AQarctan_mid_pos Pa) = rational_arctan ('a).
Proof.
  unfold AQarctan_mid_pos.
  rewrite rings.preserves_plus.
  rewrite ARtoCR_preserves_AQpi.
  rewrite AQarctan_small_correct.
  rewrite Zshift_opp_2, rings.preserves_1.
  ms_setoid_replace ('(a - 1) / '(a + 1) : Q) with (('a - 1) / ('a + 1)).
   apply rational_arctan_fourth_pi.
   apply stdlib_rationals.Qlt_coincides.
   now apply semirings.preserves_pos.
  rewrite rings.preserves_minus, rings.preserves_plus.
  now rewrite rings.preserves_1.
Qed.

Lemma AQarctan_pos_prf1 {a : AQ} : 0 ≤ a → a ≤ 1 ≪ (-1) → 0 ≤ a < 1.
Proof.
  split; trivial.
  apply orders.sprecedes_trans_r with (1 ≪ (-1)).
   easy.
  apply (maps.strictly_order_preserving_back (coerce : AQ → Q)).
  rewrite Zshift_opp_1, rings.preserves_1.
  split; easy.
Qed.

Lemma AQarctan_pos_prf2 {a : AQ} : ¬a ≤ 1 ≪ (-1) → 0 < a.
Proof.
  intros. apply orders.sprecedes_trans_l with (1 ≪ (-1)).
   apply (maps.strictly_order_preserving_back (coerce : AQ → Q)).
   rewrite Zshift_opp_1, rings.preserves_0, rings.preserves_1.
   split; easy.
  now apply orders.precedes_flip.
Qed.

Lemma AQarctan_pos_prf3 {a : AQ} : ¬a ≤ 2 → 1 < a.
Proof.
  intros. apply orders.sprecedes_trans_l with 2.
   apply semirings.sprecedes_1_2.
  now apply orders.precedes_flip.
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
  ARtoCR (AQarctan_pos Pa) = rational_arctan ('a).
Proof.
  unfold AQarctan_pos.
  case (decide_rel _); intros.
   rewrite AQarctan_small_pos_correct.
   ms_setoid_replace ('a / '1 : Q) with ('a).
    reflexivity.
   rewrite rings.preserves_1.
   rewrite fields.dec_mult_inv_1.
   now apply rings.mult_1_r.
  case (decide_rel _); intros.
   apply AQarctan_mid_pos_correct.
  apply AQarctan_big_pos_correct.
Qed.

Lemma AQarctan_prf {a : AQ} : ¬0 ≤ a → 0 ≤ - a.
Proof. intros. apply rings.flip_nonpos_opp. now apply orders.precedes_flip. Qed.

Definition AQarctan (a : AQ) : AR :=
  match decide_rel (≤) 0 a with
  | left Pa => AQarctan_pos Pa
  | right Pa => -AQarctan_pos (AQarctan_prf Pa)
  end.

Lemma AQarctan_correct (a : AQ) : 
  ARtoCR (AQarctan a) = rational_arctan ('a).
Proof.
  unfold AQarctan.
  case (decide_rel _); intros.
   apply AQarctan_pos_correct.
  rewrite rings.preserves_opp.
  rewrite AQarctan_pos_correct.
  rewrite rings.preserves_opp.
  apply rational_arctan_opp.
Qed.

Local Obligation Tactic := idtac.
Program Definition ARarctan_uc := 
  unary_complete_uc Qmetric.QPrelengthSpace coerce AQarctan arctan_uc _.
Next Obligation. apply AQarctan_correct. Qed. 

Definition ARarctan := Cbind AQPrelengthSpace ARarctan_uc.

Lemma ARtoCR_preserves_arctan x : ARtoCR (ARarctan x) = arctan (ARtoCR x).
Proof. apply preserves_unary_complete_fun. Qed.
End ARarctan.
