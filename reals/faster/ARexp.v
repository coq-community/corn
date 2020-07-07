Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import
  Coq.Program.Program MathClasses.misc.workaround_tactics
  CoRN.model.totalorder.QposMinMax 
  CoRN.model.totalorder.QMinMax Coq.QArith.Qround CoRN.util.Qdlog CoRN.stdlib_omissions.Q 
  CoRN.reals.fast.CRexp CoRN.reals.fast.CRstreams CoRN.reals.fast.CRAlternatingSum CoRN.reals.fast.Compress
  CoRN.metric2.MetricMorphisms CoRN.reals.faster.ARAlternatingSum MathClasses.interfaces.abstract_algebra 
  MathClasses.orders.minmax MathClasses.theory.nat_pow MathClasses.theory.int_pow.
Require Export
  CoRN.reals.faster.ARArith.

Section ARexp.
Context `{AppRationals AQ}.

Section exp_small_neg.
Context {a : AQ} (Pa : -1 ≤ a ≤ 0).

(*
Split the stream 
  (-a)^i / i! 
up into the streams
  (-a)^i    and    i!
because we do not have exact division
*)
Lemma ARexpSequence : DivisionStream (expSequence (-'a)) (powers (-a)) factorials.
Proof.
  apply DivisionStream_Str_nth.
  intros n.
  unfold expSequence, mult_Streams.
  rewrite Str_nth_zipWith.
  rewrite commutativity.
  apply sg_op_proper.
   rewrite preserves_powers.
   now rewrite rings.preserves_negate.
  rewrite Str_nth_Qrecip_factorials'.
  now rewrite preserves_factorials.
Qed.

Definition AQexp_small_neg_prf : -1 ≤ ('a : Q) ≤ 0.
Proof.
  split.
   now apply rings.preserves_ge_negate1.
  now apply semirings.preserves_nonpos.
Qed.

(*
The ARInfAltSum function computes the infinite alternating sum 
and takes care of:
- Computing the length of the partial sum
- Computing the precision of the approximate division
- The trick to avoid evaluation of termination proofs
*)
Definition AQexp_small_neg : AR := ARInfAltSum ARexpSequence 
  (dnn:=expSequence_dnn (Qle_ZO_flip AQexp_small_neg_prf)) (zl:=expSequence_zl (Qle_ZO_flip AQexp_small_neg_prf)).

Lemma AQexp_small_neg_correct : 'AQexp_small_neg = rational_exp ('a).
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
   apply (order_reflecting (2 *.)).
   rewrite <-shiftl_S, rings.plus_negate_r, shiftl_0.
   now rewrite <-rings.negate_mult_distr_r.
  apply (order_reflecting (2 *.)).
  rewrite <-shiftl_S, rings.plus_negate_r, shiftl_0.
  now rewrite right_absorb.
Qed.

(*
Implement the range reduction
  exp(x) = exp(x/2) ^ 2
*)
Fixpoint AQexp_neg_bounded {n : nat} {a : AQ} : -2^n ≤ a ≤ 0 → AR :=
  match n with
  | O => AQexp_small_neg
  | S n' => λ Pa, ARpower_N_bounded 2 1 (ARcompress (AQexp_neg_bounded (AQexp_neg_bounded_prf Pa)))
  end.

Lemma AQexp_neg_bounded_correct {n : nat} {a : AQ} (Pa : -2^n ≤ a ≤ 0) : 
  'AQexp_neg_bounded Pa = rational_exp ('a).
Proof.
  revert a Pa.
  induction n; intros a p.
   apply AQexp_small_neg_correct.
  unfold AQexp_neg_bounded. fold (AQexp_neg_bounded (AQexp_neg_bounded_prf p)).
  rewrite ARcompress_correct.
  rewrite ARtoCR_preserves_power_N_bounded.
  rewrite IHn.
  setoid_replace ('1 : Qpos) with (1#1)%Qpos by now rewrite AQposAsQpos_preserves_1.
  rewrite aq_shift_opp_1.
  apply rational_exp_square.
  now apply semirings.preserves_nonpos.
Qed.

Section exp_neg.
Context {a : AQ} (Pa : a ≤ 0).

Definition AQexp_neg_bound : nat := 
  match decide_rel (≤) (-1) a with
  | left _ => 0
  | right _ => Z.abs_nat (1 + Qdlog2 (-'a))
  end.

Lemma AQexp_neg_bound_correct : -2 ^ AQexp_neg_bound ≤ a ≤ 0.
Proof.
  split; [|trivial].
  unfold AQexp_neg_bound.
  case (decide_rel (≤)); intros E1.
   easy.
  apply orders.le_flip in E1.
  apply (order_reflecting (cast AQ Q)).
  rewrite rings.preserves_negate.
  rewrite preserves_nat_pow.
  rewrite rings.preserves_2.
  rewrite <-(int_pow_nat_pow (f:=Z_of_nat)).
  rewrite inj_Zabs_nat, Z.abs_eq.
   apply rings.flip_le_negate.
   rewrite rings.negate_involutive.
   apply orders.lt_le, Qdlog2_spec.
   apply rings.flip_neg_negate.
   apply orders.le_lt_trans with (-1).
    now apply rings.preserves_le_negate1.
   apply rings.flip_pos_negate. solve_propholds.
  change (0 ≤ 1 + Qdlog2 (-'a)).
  apply semirings.plus_le_compat_r; [| solve_propholds].
  apply Qdlog2_nonneg.
  change ((- -1 : Q) ≤ -'a).
  apply rings.flip_le_negate.
  now apply rings.preserves_le_negate1.
Qed.

(* We can also divide by any additional number of 2 powers. Doing this generally 
   improves the performance because the sequence diverges more quickly. *)
Lemma AQexp_neg_bound_weaken (n : nat) : -2 ^ (n + AQexp_neg_bound) ≤ a ≤ 0.
Proof.
  split; [|trivial].
  transitivity (-2 ^ AQexp_neg_bound).
   apply rings.flip_le_negate.
   rewrite nat_pow_exp_plus.
   apply semirings.ge_1_mult_le_compat_l.
     apply nat_pow_ge_1.
      now apply semirings.le_1_2.
     solve_propholds.
   reflexivity.
  now apply AQexp_neg_bound_correct.
Qed.

Definition AQexp_neg : AR := AQexp_neg_bounded (AQexp_neg_bound_weaken 75).

Lemma AQexp_neg_correct: 'AQexp_neg = rational_exp ('a).
Proof. apply AQexp_neg_bounded_correct. Qed.

(* We could use a number closer to 1/exp 1, for example 11 $ -5, but in practice this seems
    to make it slower. *)
Program Definition AQexp_inv_pos_bound : AQ₊ := ((1 ≪ (-2)) ^ Z.abs_N (Qfloor ('a)))↾_.
Next Obligation. solve_propholds. Qed.

Lemma AQexp_inv_pos_bound_correct :
  '(cast (AQ₊) Q AQexp_inv_pos_bound) ≤ rational_exp ('a). 
Proof.
  change (cast Q CR (cast AQ Q ((1 ≪ (-2)) ^ Z.abs_N (Qfloor ('a)))) ≤ rational_exp ('a)).
  rewrite preserves_nat_pow.
  rewrite aq_shift_opp_2.
  rewrite rings.preserves_1, rings.mult_1_l.
  rewrite <-(int_pow_nat_pow (f:=cast N Z)).
  rewrite Z_of_N_abs, Z.abs_neq.
   apply (rational_exp_lower_bound (1#4)).
    now apply semirings.preserves_nonpos.
   apply CRpos_nonNeg.
   now CRsign.CR_solve_pos (1#1)%Qpos.
  change (Qfloor ('a) ≤ 0).
  apply (order_reflecting (cast Z Q)).
  transitivity ('a : Q).
   now apply Qfloor_le.
  now apply semirings.preserves_nonpos.
Qed.
End exp_neg.

Lemma AQexp_prf1 {a : AQ} (pA : 0 ≤ a) : -a ≤ 0.
Proof. now apply rings.flip_nonneg_negate. Qed.

Lemma AQexp_prf2 {a : AQ} (pA : ¬0 ≤ a) : a ≤ 0.
Proof. now apply orders.le_flip. Qed.

(*
Extend it to the full domain.
*)
Definition AQexp (a : AQ) : AR := 
  match decide_rel (≤) 0 a with
  | left Pa => ARinv_pos (AQexp_inv_pos_bound (a:=-a)) (AQexp_neg (AQexp_prf1 Pa))
  | right Pa => AQexp_neg (AQexp_prf2 Pa)
  end.

Lemma AQexp_correct a : 'AQexp a = rational_exp ('a).
Proof.
  unfold AQexp.
  case (decide_rel _); intros.
   rewrite ARtoCR_preserves_inv_pos.
   rewrite AQexp_neg_correct.
   rewrite rings.preserves_negate.
   apply rational_exp_opp.
    now apply semirings.preserves_nonneg.
   posed_rewrite <-(rings.preserves_negate (f:=cast AQ Q)).
   apply (AQexp_inv_pos_bound_correct (a:=-a)).
   now apply rings.flip_nonneg_negate.
  apply AQexp_neg_correct.
Qed.

Local Obligation Tactic := idtac.
Program Definition ARexp_bounded_uc (z : Z) := unary_complete_uc 
  QPrelengthSpace (cast AQ Q_as_MetricSpace) (λ x, AQexp (('z) ⊓ x)) (exp_bound_uc z) _.
Next Obligation. 
  intros. 
  change ('AQexp ((' z) ⊓ x) = exp_bound_uc z (' x)).
  rewrite AQexp_correct, aq_preserves_min, AQtoQ_ZtoAQ.
  reflexivity.
Qed.

Definition ARexp_bounded (z : Z) := Cbind AQPrelengthSpace (ARexp_bounded_uc z).

Lemma ARtoCR_preserves_exp_bounded z x : 'ARexp_bounded z x = exp_bounded z ('x).
Proof. apply (preserves_unary_complete_fun QPrelengthSpace _ (λ x, AQexp (('z) ⊓ x))). Qed.

Definition ARexp (x : AR) : AR
  := ARexp_bounded (Qceiling ('approximate x (Qpos2QposInf (1#1)) + (1#1))) x.

Lemma ARtoCR_preserves_exp x : 'ARexp x = exp ('x).
Proof. unfold ARexp. apply ARtoCR_preserves_exp_bounded. Qed.
End ARexp.
