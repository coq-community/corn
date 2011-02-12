Require Import
  Program workaround_tactics
  QMinMax Qround Qdlog2 stdlib_omissions.Q 
  CRexp CRseries CRAlternatingSum Compress
  MetricMorphisms ARAlternatingSum abstract_algebra 
  minmax nat_pow int_pow.
Require Export
  ARArith.

Section ARexp.
Context `{AppRationals AQ}.

Local Opaque AR CR ARtoCR ARpower_positive_bounded.
Close Scope uc_scope.

Section exp_small_neg.
Context {a : AQ} (Pa : -(1) ≤ 'a ≤ 0).

Lemma ARexpSequence : DivisionStream (expSequence (- 'a)) (powers (-a)) factorials.
Proof.
  apply DivisionStream_Str_nth.
  intros n.
  unfold expSequence, mult_Streams.
  rewrite Str_nth_zipWith.
  rewrite commutativity.
  apply sg_mor.
   rewrite 2!Str_nth_powers.
   rewrite preserves_nat_pow.
   now rewrite rings.preserves_opp.
  rewrite Str_nth_Qrecip_factorials'.
  now rewrite preserves_factorials.
Qed.

Definition AQexp_small_neg : AR := ARInfAltSum ARexpSequence 
  (dnn:=expSequence_dnn (Qle_ZO_flip Pa)) (zl:=expSequence_zl (Qle_ZO_flip Pa)).

Lemma ARexp_small_neg_correct : ARtoCR AQexp_small_neg = rational_exp ('a).
Proof.
  rewrite rational_exp_correct.
  rewrite <-rational_exp_small_neg_correct.
  apply ARInfAltSum_correct.
Qed.
End exp_small_neg.

Lemma AQexp_neg_bounded_prf `(Pa : inject_Z (-2^S n) ≤ 'a ≤ 0) : 
  inject_Z (- 2^n) ≤ '(a ≪ -(1)) ≤ 0.
Proof.
  rewrite Zshift_opp_1.
  now apply shrink_by_two.
Qed. 

Fixpoint AQexp_neg_bounded {n : nat} {a : AQ} : inject_Z (-2^n) ≤ 'a ≤ 0 → AR :=
  match n with
  | O => AQexp_small_neg
  | S n' => λ Pa, ARpower_positive_bounded 2 1 (ARcompress (AQexp_neg_bounded (AQexp_neg_bounded_prf Pa)))
  end.

Lemma AQexp_neg_bounded_correct {n : nat} {a : AQ} (Pa : inject_Z (-2^n) ≤ 'a ≤ 0) : 
  ARtoCR (AQexp_neg_bounded Pa) = rational_exp ('a).
Proof.
  revert a Pa.
  induction n; intros a p.
   apply ARexp_small_neg_correct.
  unfold AQexp_neg_bounded. fold (AQexp_neg_bounded (AQexp_neg_bounded_prf p)).
  rewrite ARtoCR_preserves_power_positive_bounded.
  rewrite ARcompress_correct.
  setoid_replace (AQposAsQpos 1) with (1#1)%Qpos by now rewrite AQposAsQpos_preserves_1.
  rewrite rational_exp_correct.
  rewrite <-shrink_by_two_correct; [|easy].
  rewrite <-rational_exp_correct.
  rewrite IHn.
  now rewrite Zshift_opp_1.
Qed.

Section exp_neg.
Context {a : AQ} (Pa : 'a ≤ 0).

Definition AQexp_neg_bound : nat := 
  match decide_rel (≤) (-(1)) a with
  | left _ => 0
  | right _ => Zabs_nat (Zsucc (Qdlog2 (-'a)))
  end.

Lemma AQexp_neg_bound_correct :
   inject_Z (-2 ^ AQexp_neg_bound) ≤ 'a ≤ 0.
Proof.
  split; [|trivial].
  unfold AQexp_neg_bound.
  case (decide_rel (≤)); intros E1.
   case (decide ('a = 0)); intros E2.
    now rewrite E2.
   transitivity (-(1):Q).
    easy.
   rewrite <-(rings.preserves_1 (f:=inject : AQ → Q)).
   rewrite <-rings.preserves_opp.
   now apply (order_preserving _).
  case (decide ('a = 0)); intros E2.
   now rewrite E2.
  rewrite inj_Zabs_nat.
  assert (0 ≤ Qdlog2 (-'a)).
   apply Qdlog2_nonneg. change (- -(1) ≤ -'a).
   apply (proj1 (rings.flip_opp _ _)).
   rewrite <-(rings.preserves_1 (f:=inject : AQ → Q)).
   rewrite <-rings.preserves_opp.
   apply (order_preserving _).
   now apply orders.precedes_flip.
  rewrite Z.abs_eq.
   rewrite <-(rings.opp_involutive ('a)) at 2.
   posed_rewrite (rings.preserves_opp (f:=inject_Z)).
   apply (proj1 (rings.flip_opp _ _)).
   rewrite Qpower.Zpower_Qpower.
    change (inject_Z 2) with (2:Q).
    apply stdlib_rationals.Qlt_coincides.
    apply Qdlog2_spec.
    apply stdlib_rationals.Qlt_coincides.
    apply rings.flip_neg_opp. now split.
   now apply_simplified (semirings.nonneg_plus_compat (R:=Z)).
  now apply Zle_le_succ.
Qed.

(* We can also divide by any additional number of 2 powers. Doing this generally 
   improves the performance because the sequence diverges more quickly. *)
Lemma AQexp_neg_bound_weaken (n : nat) :
   inject_Z (-2 ^ Z_of_nat (n + AQexp_neg_bound)) ≤ 'a ≤ 0.
Proof.
  split; [|trivial].
  transitivity (inject_Z (-2 ^ AQexp_neg_bound)).
   apply (order_preserving _).
   apply (proj1 (rings.flip_opp _ _)).
   rewrite rings.preserves_plus.
   rewrite Zpower_exp; auto with *.
   apply semirings.ge1_mult_compat_l.
     now apply Z.pow_nonneg.
    change (2 ^ 0 ≤ 2 ^ n)%Z.
    apply Z.pow_le_mono_r; auto with *.
   reflexivity.
  now apply AQexp_neg_bound_correct.
Qed.

Definition AQexp_neg : AR := AQexp_neg_bounded (AQexp_neg_bound_weaken 75).

Lemma ARexp_neg_correct: ARtoCR AQexp_neg = rational_exp ('a).
Proof. apply AQexp_neg_bounded_correct. Qed.

Program Definition AQexp_inv_pos_bound : AQ₊ :=
  let aQ := 'a in exist _ (('(1 : Z) ≪ -(2 : Z)) ^ Zabs_N (Zdiv (Qnum aQ) (Qden aQ))) _. (* 11 $ 5 *)
Next Obligation.
  apply nat_pow_pos.
  apply (maps.strictly_order_preserving_back (inject : AQ → Q)).
  rewrite rings.preserves_0.
  rewrite aq_shift_correct.
  apply semirings.pos_mult_scompat.
   rewrite AQtoQ_ZtoAQ.
   now apply stdlib_rationals.Qlt_coincides.
  apply int_pow_pos.
  now apply semirings.sprecedes_0_2.
Qed.

Lemma AQexp_inv_pos_bound_correct :
  '(AQposAsQpos AQexp_inv_pos_bound : Q) ≤ rational_exp ('a). 
Proof.
  unfold AQexp_inv_pos_bound.
  unfold AQposAsQpos. unfold inject at 3. unfold positive_semiring_elements.Pos_inject. simpl.
  rewrite preserves_nat_pow.
  rewrite aq_shift_correct.
  rewrite <-int_pow_nat_pow.
  rewrite AQtoQ_ZtoAQ.
  rewrite Z_of_N_abs Z.abs_neq.
   rewrite rational_exp_correct.
   rewrite <-(rational_exp_neg_correct Pa).
   pose proof (@rational_exp_neg_posH' (1%positive * 2 ^ -2)) as P.
   apply P. clear. unfold CRle. apply CRpos_nonNeg.
   CRsign.CR_solve_pos (1#1)%Qpos.
  apply Zdiv_le_upper_bound.
   auto with *.
  rewrite left_absorb.
  now apply Qnum_nonpos.
Qed.
End exp_neg.

Lemma AQexp_prf1 {a : AQ} (pA : 0 ≤ a) : '(-a) ≤ 0.
Proof.
  posed_rewrite <-(rings.preserves_0 (f:=inject : AQ → Q)).
  apply (order_preserving _).
  now apply rings.flip_nonneg_opp.
Qed.

Lemma AQexp_prf2 {a : AQ} (pA : ¬0 ≤ a) : 'a ≤ 0.
Proof.
  posed_rewrite <-(rings.preserves_0 (f:=inject : AQ → Q)).
  apply (order_preserving _).
  now apply orders.precedes_flip.
Qed.

Definition AQexp (a : AQ) : AR := 
  match (decide_rel (≤) 0 a) with
  | left Pa => ARinv_pos (AQexp_inv_pos_bound (a:=-a)) (AQexp_neg (AQexp_prf1 Pa))
  | right Pa => AQexp_neg (AQexp_prf2 Pa)
  end.

Lemma ARexp_correct a : ARtoCR (AQexp a) = rational_exp ('a).
Proof.
  unfold AQexp.
  case (decide_rel _); intros.
   rewrite ARtoCR_preserves_inv_pos.
   rewrite ARexp_neg_correct.
   rewrite rings.preserves_opp.
   rewrite 2!rational_exp_correct.
   apply rational_exp_pos_correct.
    posed_rewrite <-(rings.preserves_0 (f:=inject : AQ → Q)).
    now apply (order_preserving _).
   rewrite <-rational_exp_correct.
   posed_rewrite <-(rings.preserves_opp (f:=inject : AQ → Q)).
   apply AQexp_inv_pos_bound_correct.
   posed_rewrite <-(rings.preserves_0 (f:=inject : AQ → Q)).
   apply (order_preserving _).
   now apply rings.flip_nonneg_opp.
  apply ARexp_neg_correct.
Qed.

Local Obligation Tactic := idtac.
Program Definition ARexp_bounded_uc (z : Z) := 
  unary_complete_uc QPrelengthSpace inject (λ x, AQexp (min ('z : AQ) x)) (exp_bound_uc z) _.
Next Obligation. 
  intros. 
  rewrite ARexp_correct aq_preserves_min AQtoQ_ZtoAQ.
  reflexivity.
Qed.

Definition ARexp_bounded (z : Z) := Cbind AQPrelengthSpace (ARexp_bounded_uc z).

Lemma ARtoCR_preserves_exp_bounded z x : ARtoCR (ARexp_bounded z x) = exp_bounded z (ARtoCR x).
Proof. apply (preserves_unary_complete_fun QPrelengthSpace inject (λ x, AQexp (min ('z : AQ) x))). Qed.

Definition ARexp (x : AR) : AR := ARexp_bounded (Qceiling ('approximate x (1#1)%Qpos + (1#1))) x.

Lemma ARtoCR_preserves_exp x : ARtoCR (ARexp x) = exp (ARtoCR x).
Proof. apply ARtoCR_preserves_exp_bounded. Qed.

End ARexp.
