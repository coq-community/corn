Require Import
  Program workaround_tactics
  QMinMax Qround Qdlog stdlib_omissions.Q 
  CRsin CRseries CRAlternatingSum Compress
  MetricMorphisms ARAlternatingSum abstract_algebra 
  minmax nat_pow int_pow.
Require Export
  ARArith.

Section ARsin.
Context `{AppRationals AQ}.

Add Field Q : (dec_fields.stdlib_field_theory Q).

Section sin_small_pos.
Context {num den : AQ} (Pnd : 0 ≤ num ≤ den).

Lemma ARsinSequence : DivisionStream 
  (sinSequence ('num / 'den)) 
  (powers_help (num ^ (2:N)) num)
  (mult_Streams (powers_help (den ^ (2:N)) den) (everyOther (tl factorials))).
Proof.
  apply DivisionStream_Str_nth.
  intros n.
  unfold sinSequence, mult_Streams.
  rewrite ?Str_nth_zipWith.
  rewrite commutativity. 
  rewrite rings.preserves_mult, dec_fields.dec_mult_inv_distr.
  rewrite associativity.
  apply sg_op_proper.
   rewrite 2!preserves_powers_help.
   rewrite 3!(Str_nth_powers_help_int_pow _ (cast nat Z)).
   rewrite 2!(preserves_nat_pow (f:=cast AQ Q)).
   rewrite <-2!(int_pow_nat_pow (f:=cast N Z)).
   change (Qpower ('num / 'den) 2) with (('num / 'den) ^ ('(2 : N)) : Q).
   rewrite 2!int_pow_mult. 
   rewrite 2!int_pow_mult_inv.
   change (Qdiv ('num) ('den)) with ('num / 'den : Q).
   destruct (decide ('den = (0:Q))) as [Pden | Pden].
    rewrite ?Pden, rings.mult_0_l, dec_mult_inv_0. ring.
   assert (PropHolds ('den ≠ (0:Q))) by assumption. 
   field_simplify. reflexivity.
    solve_propholds.
   split; solve_propholds.
  rewrite 2!Str_nth_everyOther.
  change (@tl AQ) with (@Str_nth_tl AQ 1).
  change (@tl Q) with (@Str_nth_tl Q 1).
  rewrite ?Str_nth_plus.
  rewrite Str_nth_Qrecip_factorials'.
  now rewrite preserves_factorials.
Qed.

Lemma AQsin_small_pos_Qprf : 0 ≤ ('num / 'den : Q) ≤ 1.
Proof.
  split.
   apply nonneg_mult_compat.
    now apply semirings.preserves_nonneg.
   apply dec_fields.nonneg_dec_mult_inv_compat.
   apply semirings.preserves_nonneg.
   red. now transitivity num.
  destruct (decide ('den = (0:Q))) as [Pden | Pden].
    rewrite ?Pden, dec_mult_inv_0. now ring_simplify.
  rewrite <-(dec_mult_inverse ('den : Q)) by assumption.
  apply (maps.order_preserving_flip_nonneg (.*.) (/'den)).
   apply dec_fields.nonneg_dec_mult_inv_compat.
   apply semirings.preserves_nonneg.
   red. now transitivity num.
  now apply (order_preserving _).
Qed.

Definition AQsin_small_pos : AR := ARInfAltSum ARsinSequence 
  (dnn:=sinSequence_dnn AQsin_small_pos_Qprf) (zl:=sinSequence_zl AQsin_small_pos_Qprf).

Lemma AQsin_small_pos_correct : 'AQsin_small_pos = rational_sin ('num / 'den).
Proof.
  rewrite rational_sin_correct.
  rewrite <-rational_sin_small_pos_correct.
  now apply ARInfAltSum_correct.
Qed.
End sin_small_pos.

Definition AQsin_poly_fun (x : AQ) : AQ := x * (3 - 4 * x ^ (2:N)).

Lemma AQsin_poly_fun_correct (x : AQ) :
  'AQsin_poly_fun x = sin_poly_fun ('x).
Proof.
  unfold AQsin_poly_fun, sin_poly_fun.
  rewrite nat_pow_2.
  rewrite rings.preserves_mult, rings.preserves_minus, ?rings.preserves_mult.
  rewrite rings.preserves_3, rings.preserves_4.
  now rewrite <-(associativity 4 ('x) ('x : Q)).
Qed.

Program Definition AQsin_poly_uc := unary_uc (cast AQ Q_as_MetricSpace)
  (λ x : AQ_as_MetricSpace, AQsin_poly_fun (AQboundAbs_uc 1 x) : AQ_as_MetricSpace) sin_poly_uc _.
Next Obligation.
  rewrite AQsin_poly_fun_correct.
  change ('1) with (1:AQ).
  rewrite ?aq_preserves_max, ?aq_preserves_min.
  now rewrite ?rings.preserves_opp, ?rings.preserves_1.
Qed.

Definition ARsin_poly := uc_compose ARcompress (Cmap AQPrelengthSpace AQsin_poly_uc).

Lemma ARtoCR_preserves_sin_poly x : 'ARsin_poly x = sin_poly ('x).
Proof.
  change ('ARcompress (Cmap AQPrelengthSpace AQsin_poly_uc x) 
    = compress (Cmap QPrelengthSpace sin_poly_uc ('x))).
  rewrite ARcompress_correct, compress_correct.
  now apply preserves_unary_fun.
Qed.

Lemma AQsin_pos_bounded_prf1 {num den : AQ} (Pnd : 0 ≤ num ≤ den * 1) : 
  0 ≤ num ≤ den.
Proof. now rewrite rings.mult_1_r in Pnd. Qed.

Lemma AQsin_pos_bounded_prf2 {num den : AQ} {n : nat} (Pnd : 0 ≤ num ≤ den * 3^S n) :
  0 ≤ num ≤ (den * 3) * 3^n.
Proof. now rewrite <-associativity. Qed.

Fixpoint AQsin_pos_bounded {n : nat} {num den : AQ} : 0 ≤ num ≤ den * 3^n → AR :=
  match n with
  | O => λ Pnd, AQsin_small_pos (AQsin_pos_bounded_prf1 Pnd)
  | S n' => λ Pnd, ARsin_poly (AQsin_pos_bounded (AQsin_pos_bounded_prf2 Pnd))
  end.

Lemma AQsin_pos_bounded_correct {n : nat} {num den : AQ} (Pnd : 0 ≤ num ≤ den * 3^n) : 
  'AQsin_pos_bounded Pnd = rational_sin ('num / 'den).
Proof.
  revert num den Pnd.
  induction n; intros.
   apply AQsin_small_pos_correct.
  unfold AQsin_pos_bounded. fold (AQsin_pos_bounded (AQsin_pos_bounded_prf2 Pnd)).
  rewrite ARtoCR_preserves_sin_poly.
  rewrite IHn.
  change (Qdiv ('num) ('(den * 3))) with (('num : Q) / '(den * 3)).
  rewrite rings.preserves_mult, rings.preserves_3.
  rewrite dec_fields.dec_mult_inv_distr, associativity.
  now apply rational_sin_poly.
Qed.

Section sin_pos.
Context {a : AQ} (Pa : 0 ≤ a).

Definition AQsin_pos_bound : nat := Zabs_nat (1 + Qdlog 3 ('a)).

Lemma AQsin_pos_bound_correct : 0 ≤ a ≤ 3 ^ AQsin_pos_bound.
Proof.
  split; [assumption |].
  unfold AQsin_pos_bound.
  apply (order_reflecting (cast AQ Q)).
  rewrite preserves_nat_pow.
  rewrite rings.preserves_3.
  rewrite <-(int_pow_nat_pow (f:=cast nat Z)).
  destruct (total (≤) ('a : Q) 1).
   rewrite Qdlog2_le1; simpl; try easy.
   now transitivity (1:Q).
  rewrite inj_Zabs_nat, Z.abs_eq.
   now apply orders.lt_le, Qdlog_spec.
  change (0 ≤ 1 + Qdlog 3 ('a)).
  apply semirings.nonneg_plus_compat; [easy | now apply Qdlog_bounded_nonneg].
Qed.

(* We can also divide by any additional number of 3 powers. Doing this generally 
   improves the performance because the sequence diverges more quickly. *)
Lemma AQsin_pos_bound_weaken (n : nat) : 0 ≤ a ≤ 1 * 3 ^ (n + AQsin_pos_bound).
Proof.
  split; [assumption |].
  rewrite rings.mult_1_l.
  rewrite nat_pow_exp_plus.
  apply semirings.ge_1_mult_le_compat_l.
    apply nat_pow_ge_1. 
     now apply semirings.le_1_3.
    now apply naturals.naturals_nonneg.
   now apply nat_pow_nonneg; solve_propholds.
  now apply AQsin_pos_bound_correct.
Qed.

Definition AQsin_pos : AR := AQsin_pos_bounded (AQsin_pos_bound_weaken 75).

Lemma AQsin_pos_correct: 'AQsin_pos = rational_sin ('a).
Proof. 
  ms_setoid_replace ('a : Q) with ('a / '1 : Q).
   now apply AQsin_pos_bounded_correct.
  rewrite rings.preserves_1, dec_fields.dec_mult_inv_1. ring.
Qed.
End sin_pos.

Lemma AQsin_prf {a : AQ} (pA : ¬0 ≤ a) : 0 ≤ -a.
Proof. apply rings.flip_nonpos_opp. now apply orders.le_flip. Qed.

Definition AQsin (a : AQ) : AR := 
  match (decide_rel (≤) 0 a) with
  | left Pa => AQsin_pos Pa
  | right Pa => -AQsin_pos (AQsin_prf Pa)
  end.

Lemma AQsin_correct a : 'AQsin a = rational_sin ('a).
Proof.
  unfold AQsin.
  case (decide_rel _); intros.
   now apply AQsin_pos_correct.
  rewrite rings.preserves_opp, AQsin_pos_correct.
  rewrite rings.preserves_opp.
  now apply rational_sin_opp.
Qed.

Local Obligation Tactic := idtac.
Program Definition ARsin_uc := unary_complete_uc 
  QPrelengthSpace (cast AQ Q_as_MetricSpace) AQsin sin_uc _.
Next Obligation. intros. apply AQsin_correct. Qed.

Definition ARsin := Cbind AQPrelengthSpace ARsin_uc.

Lemma ARtoCR_preserves_sin x : 'ARsin x = sin_slow ('x).
Proof. apply preserves_unary_complete_fun. Qed.

End ARsin.
