Require Import
  Program workaround_tactics
  QMinMax Qround Qdlog stdlib_omissions.Q 
  CRexp CRseries CRAlternatingSum Compress
  MetricMorphisms ARAlternatingSum abstract_algebra 
  minmax nat_pow int_pow.
Require Export
  ARArith.

Section ARexp.
Context `{AppRationals AQ}.

Section exp_small_neg.
Context {a : AQ} (Pa : -1 ≤ a ≤ 0).

Lemma ARexpSequence : DivisionStream (expSequence (-'a)) (powers (-a)) factorials.
Proof.
  apply DivisionStream_Str_nth.
  intros n.
  unfold expSequence, mult_Streams.
  rewrite Str_nth_zipWith.
  rewrite commutativity.
  apply sg_mor.
   rewrite preserves_powers.
   now rewrite rings.preserves_opp.
  rewrite Str_nth_Qrecip_factorials'.
  now rewrite preserves_factorials.
Qed.

Definition AQexp_small_neg_prf : -1 ≤ 'a ≤ 0.
Proof.
  split.
   now apply rings.preserves_ge_opp1.
  now apply semirings.preserves_nonpos.
Qed.

Definition AQexp_small_neg : AR := ARInfAltSum ARexpSequence 
  (dnn:=expSequence_dnn (Qle_ZO_flip AQexp_small_neg_prf)) (zl:=expSequence_zl (Qle_ZO_flip AQexp_small_neg_prf)).

Lemma AQexp_small_neg_correct : ARtoCR AQexp_small_neg = rational_exp ('a).
Proof.
  rewrite rational_exp_correct.
  rewrite <-rational_exp_small_neg_correct.
  apply ARInfAltSum_correct.
Qed.
End exp_small_neg.

Lemma AQexp_neg_bounded_prf `(Pa : -2^S n ≤ a ≤ 0) : 
  -2^n ≤ a ≪ (-1) ≤ 0.
Proof.
  split.
   apply (order_preserving_back (2 *.)).
   rewrite <-shiftl_S, rings.plus_opp_r, shiftl_0.
   now rewrite <-rings.opp_mult_distr_r.
  apply (order_preserving_back (2 *.)).
  rewrite <-shiftl_S, rings.plus_opp_r, shiftl_0.
  now rewrite right_absorb.
Qed.

Fixpoint AQexp_neg_bounded {n : nat} {a : AQ} : -2^n ≤ a ≤ 0 → AR :=
  match n with
  | O => AQexp_small_neg
  | S n' => λ Pa, ARpower_positive_bounded 2 1 (ARcompress (AQexp_neg_bounded (AQexp_neg_bounded_prf Pa)))
  end.

Lemma AQexp_neg_bounded_correct {n : nat} {a : AQ} (Pa : -2^n ≤ a ≤ 0) : 
  ARtoCR (AQexp_neg_bounded Pa) = rational_exp ('a).
Proof.
  revert a Pa.
  induction n; intros a p.
   apply AQexp_small_neg_correct.
  unfold AQexp_neg_bounded. fold (AQexp_neg_bounded (AQexp_neg_bounded_prf p)).
  rewrite ARtoCR_preserves_power_positive_bounded.
  rewrite ARcompress_correct.
  setoid_replace ('1 : Qpos) with (1#1)%Qpos by now rewrite AQposAsQpos_preserves_1.
  rewrite rational_exp_correct.
  rewrite <-shrink_by_two_correct.
   rewrite <-rational_exp_correct.
   rewrite IHn.
   rewrite aq_shift_opp_1. 
   reflexivity.
  now apply semirings.preserves_nonpos.
Qed.

Section exp_neg.
Context {a : AQ} (Pa : a ≤ 0).

Definition AQexp_neg_bound : nat := 
  match decide_rel (≤) (-1) a with
  | left _ => 0
  | right _ => Zabs_nat (1 + Qdlog2 (-'a))
  end.

Lemma AQexp_neg_bound_correct : -2 ^ AQexp_neg_bound ≤ a ≤ 0.
Proof.
  split; [|trivial].
  unfold AQexp_neg_bound.
  case (decide_rel (≤)); intros E1.
   easy.
  apply orders.precedes_flip in E1.
  apply (order_preserving_back (coerce : AQ → Q)).
  rewrite rings.preserves_opp.
  rewrite preserves_nat_pow.
  rewrite rings.preserves_2.
  rewrite <-(int_pow_nat_pow (f:=Z_of_nat)).
  rewrite inj_Zabs_nat, Z.abs_eq.
   apply rings.flip_opp.
   rewrite rings.opp_involutive.
   apply Qdlog2_spec.
   apply rings.flip_neg_opp.
   apply orders.sprecedes_trans_r with (-1).
    now apply rings.preserves_le_opp1.
   apply rings.flip_pos_opp. solve_propholds.
  change (0 ≤ 1 + Qdlog2 (-'a)).
  apply integers.precedes_sprecedes_alt.
  rewrite commutativity. apply (order_preserving _).
  apply Qdlog2_nonneg. 
  change (- -1 ≤ -'a).
  apply rings.flip_opp.
  now apply rings.preserves_le_opp1.
Qed.

(* We can also divide by any additional number of 2 powers. Doing this generally 
   improves the performance because the sequence diverges more quickly. *)
Lemma AQexp_neg_bound_weaken (n : nat) : -2 ^ (n + AQexp_neg_bound) ≤ a ≤ 0.
Proof.
  split; [|trivial].
  transitivity (-2 ^ AQexp_neg_bound).
   apply rings.flip_opp.
   rewrite nat_pow_exp_plus.
   apply semirings.ge1_mult_compat_l.
     solve_propholds.
    apply nat_pow_ge1.
     apply semirings.precedes_1_2.
    apply naturals.naturals_nonneg.
   reflexivity.
  now apply AQexp_neg_bound_correct.
Qed.

Definition AQexp_neg : AR := AQexp_neg_bounded (AQexp_neg_bound_weaken 75).

Lemma AQexp_neg_correct: ARtoCR AQexp_neg = rational_exp ('a).
Proof. apply AQexp_neg_bounded_correct. Qed.

(* We could use a number closer to 1/exp 1, for example 11 $ -5, but in practice this seems
    to make it slower. *)
Program Definition AQexp_inv_pos_bound : AQ₊ :=
  let b := 'a in ((1 ≪ -(2 : Z)) ^ Zabs_N (Zdiv (Qnum b) (Qden b)))↾_.
Next Obligation. solve_propholds. Qed.

Lemma AQexp_inv_pos_bound_correct :
  '('AQexp_inv_pos_bound : Q) ≤ rational_exp ('a). 
Proof.
  change ('('((1 ≪ (-2)) ^ Zabs_N (Zdiv (Qnum ('a)) (Qden ('a)))) : Q) ≤ rational_exp (AQtoQ a)).
  rewrite preserves_nat_pow.
  rewrite aq_shift_correct.
  rewrite rings.preserves_1, rings.mult_1_l.
  rewrite <-int_pow_nat_pow.
  rewrite Z_of_N_abs, Z.abs_neq.
   rewrite rational_exp_correct.
   rewrite <-(rational_exp_neg_correct (semirings.preserves_nonpos (f:=coerce : AQ → Q) a Pa)).
   pose proof (@rational_exp_neg_posH' (1%positive * 2 ^ -2)) as P.
   apply P. clear. unfold CRle. apply CRpos_nonNeg.
   CRsign.CR_solve_pos (1#1)%Qpos.
  apply Zdiv_le_upper_bound.
   auto with *.
  rewrite left_absorb.
  apply Qnum_nonpos.
  change ('a ≤ 0).
  now apply semirings.preserves_nonpos.
Qed.
End exp_neg.

Lemma AQexp_prf1 {a : AQ} (pA : 0 ≤ a) : -a ≤ 0.
Proof. now apply rings.flip_nonneg_opp. Qed.

Lemma AQexp_prf2 {a : AQ} (pA : ¬0 ≤ a) : a ≤ 0.
Proof. now apply orders.precedes_flip. Qed.

Definition AQexp (a : AQ) : AR := 
  match (decide_rel (≤) 0 a) with
  | left Pa => ARinv_pos (AQexp_inv_pos_bound (a:=-a)) (AQexp_neg (AQexp_prf1 Pa))
  | right Pa => AQexp_neg (AQexp_prf2 Pa)
  end.

Lemma AQexp_correct a : ARtoCR (AQexp a) = rational_exp ('a).
Proof.
  unfold AQexp.
  case (decide_rel _); intros.
   rewrite ARtoCR_preserves_inv_pos.
   rewrite AQexp_neg_correct.
   rewrite rings.preserves_opp.
   rewrite 2!rational_exp_correct.
   apply rational_exp_pos_correct.
    now apply semirings.preserves_nonneg.
   rewrite <-rational_exp_correct.
   posed_rewrite <-(rings.preserves_opp (f:=coerce : AQ → Q)).
   apply: (AQexp_inv_pos_bound_correct (a:=-a)).
   now apply rings.flip_nonneg_opp.
  apply AQexp_neg_correct.
Qed.

Local Obligation Tactic := idtac.
Program Definition ARexp_bounded_uc (z : Z) := 
  unary_complete_uc QPrelengthSpace coerce (λ x, AQexp (min ('z) x)) (exp_bound_uc z) _.
Next Obligation. 
  intros. 
  rewrite AQexp_correct, aq_preserves_min, AQtoQ_ZtoAQ.
  reflexivity.
Qed.

Definition ARexp_bounded (z : Z) := Cbind AQPrelengthSpace (ARexp_bounded_uc z).

Lemma ARtoCR_preserves_exp_bounded z x : ARtoCR (ARexp_bounded z x) = exp_bounded z (ARtoCR x).
Proof. apply (preserves_unary_complete_fun QPrelengthSpace coerce (λ x, AQexp (min ('z) x))). Qed.

Definition ARexp (x : AR) : AR := ARexp_bounded (Qceiling ('approximate x (1#1)%Qpos + (1#1))) x.

Lemma ARtoCR_preserves_exp x : ARtoCR (ARexp x) = exp (ARtoCR x).
Proof. apply ARtoCR_preserves_exp_bounded. Qed.

End ARexp.
