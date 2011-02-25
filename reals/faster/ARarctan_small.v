Require Import
  CRarctan_small CRseries CRAlternatingSum
  ARAlternatingSum abstract_algebra 
  nat_pow int_pow.
Require Export
  ARArith.

Section ARarctan_small.
Context `{AppRationals AQ}.

Section arctan_small_pos.
Context {num den : AQ} (Pa : 0 ≤ 'num / 'den ≤ 1).

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
   rewrite <-2!(int_pow_nat_pow (f:=Z_of_N)).
   change (Qpower ('num / 'den) 2) with (('num / 'den) ^ Z_of_N 2).
   rewrite 2!int_pow_mult. 
   rewrite 2!int_pow_mult_inv.
   rewrite fields.dec_mult_inv_distr.
   (* ring refuses to work *)
   change (Qdiv ('num) ('den)) with ('num * / 'den).
   rewrite <-2!associativity.
   apply sg_mor; [reflexivity|].
   rewrite commutativity, <-associativity.
   apply sg_mor; [reflexivity|].
   apply commutativity.
  rewrite 2!Str_nth_everyOther.
  rewrite Str_nth_Qrecip_positives'.
  now rewrite preserves_positives.
Qed.

Definition AQarctan_small_pos : AR := ARInfAltSum ARarctanSequence 
  (dnn:=arctanSequence_dnn Pa) (zl:=arctanSequence_zl Pa).

Lemma ARtoCR_preserves_arctan_small_pos : ARtoCR AQarctan_small_pos = rational_arctan_small_pos Pa.
Proof. apply ARInfAltSum_correct. Qed.
End arctan_small_pos.
End ARarctan_small.