Require Import
  Field stdlib_omissions.Q
  CRarctan_small CRarctan CRseries CRAlternatingSum
  ARAlternatingSum abstract_algebra 
  nat_pow int_pow.
Require Export
  ARArith.

Section ARarctan_small.
Context `{AppRationals AQ}.

Add Field Q : (fields.stdlib_field_theory Q).

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
  rewrite rings.preserves_mult, fields.dec_mult_inv_distr.
  rewrite associativity.
  apply sg_mor.
   rewrite 2!preserves_powers_help.
   rewrite 3!(Str_nth_powers_help_int_pow _ _).
   rewrite 2!(preserves_nat_pow (f:=coerce : AQ → Q)).
   rewrite <-2!(int_pow_nat_pow (f:=coerce : N → Z)).
   change (Qpower ('num / 'den) 2) with (('num / 'den) ^ ('(2 : N))).
   rewrite 2!int_pow_mult. 
   rewrite 2!int_pow_mult_inv.
   change (Qdiv ('num) ('den)) with ('num * / 'den).
   assert (PropHolds ('den ≠ (0:Q))). 
    apply rings.injective_ne_0.
    apply orders.sprecedes_ne_flip.
    now apply orders.sprecedes_trans_r with num.
   field_simplify. reflexivity.
    solve_propholds.
   split; solve_propholds.
  rewrite 2!Str_nth_everyOther.
  rewrite Str_nth_Qrecip_positives'.
  now rewrite preserves_positives.
Qed.

Lemma AQarctan_small_pos_Qprf : (0 <= 'num / 'den < 1)%Q.
Proof.
  split.
   change (0 ≤ ' num / ' den).
   apply semirings.nonneg_mult_compat.
    now apply semirings.preserves_nonneg.
   apply fields.nonneg_dec_mult_inv_compat.
   apply semirings.preserves_nonneg.
   red. transitivity num.
    easy.
   now apply orders.sprecedes_weaken.
  apply stdlib_rationals.Qlt_coincides.
  change ('num/'den < (1:Q)).
  rewrite <-(fields.dec_mult_inverse ('den : Q)).
   apply (maps.strictly_order_preserving_flip_gt_0 (.*.) (/'den)).
    apply fields.pos_dec_mult_inv_compat.
    apply semirings.preserves_pos.
    now apply orders.sprecedes_trans_r with num.
   now apply (strictly_order_preserving _).
  apply rings.injective_ne_0.
  apply orders.sprecedes_ne_flip.
  now apply orders.sprecedes_trans_r with num.
Qed.

Definition AQarctan_small_pos : AR := ARInfAltSum ARarctanSequence 
  (dnn:=arctanSequence_dnn AQarctan_small_pos_Qprf) (zl:=arctanSequence_zl AQarctan_small_pos_Qprf).

Lemma ARtoCR_preserves_arctan_small_pos : 
  ARtoCR AQarctan_small_pos = rational_arctan_small_pos AQarctan_small_pos_Qprf.
Proof. apply ARInfAltSum_correct. Qed.

Lemma AQarctan_small_pos_correct : 
  ARtoCR AQarctan_small_pos = rational_arctan ('num / 'den).
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
   now apply rings.flip_nonpos_opp, orders.precedes_flip.
  apply rings.flip_opp_strict. now rewrite rings.opp_involutive.
Qed.

Definition AQarctan_small : AR :=
  match decide_rel (≤) 0 num with
  | left Pn => AQarctan_small_pos (AQarctan_small_prf1 Pn)
  | right Pn => -AQarctan_small_pos (AQarctan_small_prf2 Pn)
  end.

Lemma AQarctan_small_correct : 
  ARtoCR AQarctan_small = rational_arctan ('num / 'den).
Proof.
  unfold AQarctan_small.
  case (decide_rel _); intros E.
   apply AQarctan_small_pos_correct.
  rewrite rings.preserves_opp.
  rewrite AQarctan_small_pos_correct.
  ms_setoid_replace ('(-num) / 'den) with (-('num / 'den)).
   apply rational_arctan_opp.
  rewrite rings.preserves_opp.
  now rewrite <-rings.opp_mult_distr_l.
Qed.
End arctan_small.
End ARarctan_small.
