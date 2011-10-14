Require Import
  Field stdlib_omissions.Q
  CRarctan_small CRarctan CRseries CRAlternatingSum
  ARAlternatingSum abstract_algebra 
  nat_pow int_pow.
Require Export
  ARArith.

Section ARarctan_small.
Context `{AppRationals AQ}.

Add Field Q : (dec_fields.stdlib_field_theory Q).

Section arctan_small_pos.
Context {num den : AQ} (Pnd : 0 ≤ num < den).

Lemma ARarctanSequence : DivisionStream 
  (arctanSequence ('num / 'den)) 
  (powers_help (num ^ (2:N)) num)
  (mult_Streams (powers_help (den ^ (2:N)) den) (everyOther positives)).
Proof.
  apply DivisionStream_Str_nth.
  intros n.
  unfold arctanSequence, mult_Streams.
  rewrite ?Str_nth_zipWith.
  rewrite commutativity. 
  rewrite rings.preserves_mult, dec_fields.dec_recip_distr.
  rewrite associativity.
  apply sg_op_proper.
   rewrite 2!preserves_powers_help. 
   rewrite 3!(Str_nth_powers_help_int_pow _ (cast nat Z)).
   rewrite 2!(preserves_nat_pow (f:=cast AQ Q)).
   rewrite <-2!(int_pow_nat_pow (f:=cast N Z)).
   change (Qpower ('num / 'den) 2) with (('num / 'den) ^ ('(2 : N)) : Q).
   rewrite 2!int_pow_mult. 
   rewrite 2!int_pow_recip.
   change (Qdiv ('num) ('den)) with ('num / 'den : Q).
   assert (PropHolds ('den ≠ (0:Q))). 
    apply rings.injective_ne_0.
    apply orders.lt_ne_flip.
    now apply orders.le_lt_trans with num.
   field_simplify. reflexivity.
    solve_propholds.
   split; solve_propholds.
  rewrite 2!Str_nth_everyOther.
  rewrite Str_nth_Qrecip_positives'.
  now rewrite preserves_positives.
Qed.

Lemma AQarctan_small_pos_Qprf : 0 ≤ ('num / 'den : Q) < 1.
Proof.
  split.
   apply nonneg_mult_compat.
    now apply semirings.preserves_nonneg.
   apply dec_fields.nonneg_dec_recip_compat.
   apply semirings.preserves_nonneg.
   red. transitivity num; [easy |].
   now apply orders.lt_le.
  rewrite <-(dec_recip_inverse ('den : Q)).
   apply (maps.strictly_order_preserving_flip_pos (.*.) (/'den)).
    apply dec_fields.pos_dec_recip_compat.
    apply semirings.preserves_pos.
    now apply orders.le_lt_trans with num.
   now apply (strictly_order_preserving _).
  apply rings.injective_ne_0.
  apply orders.lt_ne_flip.
  now apply orders.le_lt_trans with num.
Qed.

Definition AQarctan_small_pos : AR := ARInfAltSum ARarctanSequence 
  (dnn:=arctanSequence_dnn AQarctan_small_pos_Qprf) (zl:=arctanSequence_zl AQarctan_small_pos_Qprf).

Lemma ARtoCR_preserves_arctan_small_pos : 
  'AQarctan_small_pos = rational_arctan_small_pos AQarctan_small_pos_Qprf.
Proof. apply ARInfAltSum_correct. Qed.

Lemma AQarctan_small_pos_correct : 
  'AQarctan_small_pos = rational_arctan ('num / 'den).
Proof. 
  rewrite ARtoCR_preserves_arctan_small_pos.
  rewrite rational_arctan_correct, rational_arctan_small_pos_correct.
  reflexivity.
Qed.
End arctan_small_pos.

Section arctan_small.
Context {num den : AQ} (Pnd : -den < num < den).

(* Program loops, so we state the obligations manually *)
Lemma AQarctan_small_prf1 : 0 ≤ num → 0 ≤ num < den.
Proof. split; easy. Qed.

Lemma AQarctan_small_prf2 : ¬0 ≤ num → 0 ≤ -num < den.
Proof. 
  split. 
   now apply rings.flip_nonpos_negate, orders.le_flip.
  apply rings.flip_lt_negate. now rewrite rings.negate_involutive.
Qed.

Definition AQarctan_small : AR :=
  match decide_rel (≤) 0 num with
  | left Pn => AQarctan_small_pos (AQarctan_small_prf1 Pn)
  | right Pn => -AQarctan_small_pos (AQarctan_small_prf2 Pn)
  end.

Lemma AQarctan_small_correct : 
  'AQarctan_small = rational_arctan ('num / 'den).
Proof.
  unfold AQarctan_small.
  case (decide_rel _); intros E.
   apply AQarctan_small_pos_correct.
  rewrite rings.preserves_negate.
  rewrite AQarctan_small_pos_correct.
  ms_setoid_replace ('(-num) / 'den : Q) with (-('num / 'den) : Q).
   apply rational_arctan_opp.
  rewrite rings.preserves_negate.
  now rewrite <-rings.negate_mult_distr_l.
Qed.
End arctan_small.
End ARarctan_small.
