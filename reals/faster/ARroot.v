Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import
  Coq.setoid_ring.Ring CoRN.stdlib_omissions.Z
  CoRN.model.totalorder.QposMinMax 
  CoRN.metric2.Complete CoRN.model.metric2.Qmetric Coq.ZArith.ZArith CoRN.util.Qdlog
  CoRN.reals.fast.CRroot
  CoRN.reals.faster.ARabs
  MathClasses.interfaces.abstract_algebra MathClasses.theory.shiftl MathClasses.theory.nat_pow MathClasses.theory.int_pow.
Require Export 
  CoRN.reals.faster.ARArith.

Section ARsqrt.
Context `{AppRationals AQ}.

Add Ring AQ : (rings.stdlib_ring_theory AQ).
Add Ring Q : (rings.stdlib_ring_theory Q).
Add Ring Z : (rings.stdlib_ring_theory Z).
Add Ring AR : (rings.stdlib_ring_theory AR).

Section sqrt_mid.
Context `(Pa : 1 ≤ a ≤ 4).

Fixpoint AQsqrt_loop (n : nat) : AQ * AQ :=
  match n with
  | O => (a, 0)
  | S n => 
     let (r, s) := AQsqrt_loop n in
     if decide_rel (≤) (s + 1) r
     then ((r - (s + 1)) ≪ (2:Z), (s + 2) ≪ (1:Z))
     else (r ≪ (2:Z), s ≪ (1:Z))
  end.

Instance: Proper (=) AQsqrt_loop.
Proof. intros x y E. change (x ≡ y) in E. now rewrite E. Qed.

Lemma AQsqrt_loop_invariant1 (n : nat) : 
  snd (AQsqrt_loop n) ^ (2:N) + 4 * fst (AQsqrt_loop n) = 4 * 4 ^ n * a.
Proof.
  rewrite nat_pow_2.
  induction n; unfold pow; simpl.
   ring.
  revert IHn; case (AQsqrt_loop n); intros r s IHn.
  case (decide_rel (≤) (s + 1) r); intros; simpl in *;
   rewrite shiftl_1, shiftl_2, <-(associativity 4), <-IHn; ring.
Qed.

Lemma AQsqrt_loop_invariant2 (n : nat) : 
  fst (AQsqrt_loop n) ≤ 2 * snd (AQsqrt_loop n) + 4.
Proof.
  induction n; simpl.
   now setoid_replace (2 * 0 + 4) with 4 by ring.
  revert IHn; case (AQsqrt_loop n); intros r s IHn.
  case (decide_rel (≤) (s + 1) r); intros; simpl in *.
   rewrite shiftl_1, shiftl_2.
   setoid_replace (2 * (2 * (s + 2)) + 4) with (4 * ((2 * s + 4) - (s + 1))) by ring.
   apply (order_preserving (4 *.)).
   now apply (order_preserving (+ _)).
  rewrite shiftl_1, shiftl_2.
  setoid_replace (2 * (2 * s) + 4) with (4 * (s + 1)) by ring.
  apply (order_preserving (4 *.)).
  now apply orders.le_flip.
Qed.

Lemma AQsqrt_loop_snd_lower_bound (n z : nat) :
  snd (AQsqrt_loop n) * 2 ^ z ≤ snd (AQsqrt_loop (z + n)).
Proof.
  induction z; unfold pow; simpl.
   apply orders.eq_le. ring.
  revert IHz. case (AQsqrt_loop (z + n)); intros r s IHz.
  case (decide_rel (≤) _); intros; simpl in *.
   rewrite shiftl_1.
   setoid_replace (snd (AQsqrt_loop n) * (2 * 2 ^ z)) with (2 * (snd (AQsqrt_loop n) * 2 ^ z)) by ring.
   apply (order_preserving (2 *.)).
   apply semirings.plus_le_compat_r; [solve_propholds | assumption].
  rewrite shiftl_1.
  setoid_replace (snd (AQsqrt_loop n) * (2 * 2 ^ z)) with (2 * (snd (AQsqrt_loop n) * 2 ^ z)) by ring.
  now apply (order_preserving (2 *.)).
Qed.

Lemma AQsqrt_loop_snd_upper_bound (n z : nat) :
  snd (AQsqrt_loop (z + n)) ≤ (snd (AQsqrt_loop n) + 4) * 2 ^ z - 4.
Proof.
  induction z; unfold pow; simpl.
   apply orders.eq_le. ring.
  revert IHz. case (AQsqrt_loop (z + n)); intros r s IHz.
  case (decide_rel (≤)); simpl; intros E.
   rewrite shiftl_1.
   setoid_replace ((snd (AQsqrt_loop n) + 4) * (2 * 2 ^ z) - 4) with (2 * ((snd (AQsqrt_loop n) + 4) * 2 ^ z - 4 + 2)) by ring.
   apply (order_preserving (2 *.)).
   now apply (order_preserving (+2)).
  rewrite shiftl_1.
  setoid_replace ((snd (AQsqrt_loop n) + 4) * (2 * 2 ^ z) - 4) with (2 * ((snd (AQsqrt_loop n) + 4) * 2 ^ z - 4 + 2)) by ring.
  apply (order_preserving (2 *.)).
  apply semirings.plus_le_compat_r; [solve_propholds | assumption].
Qed.

Lemma AQsqrt_loop_snd_nonneg (n : nat) : 0 ≤ snd (AQsqrt_loop n).
Proof.
  rewrite <-(rings.plus_0_r n) at 1.
  etransitivity.
   2: apply AQsqrt_loop_snd_lower_bound.
  simpl. apply orders.eq_le. ring.
Qed.

Lemma AQsqrt_loop_fst_nonneg (n : nat) : 0 ≤ fst (AQsqrt_loop n).
Proof.
  induction n; simpl.
   transitivity 1; [solve_propholds | easy].
  revert IHn; case (AQsqrt_loop n); intros r s IHn.
  case (decide_rel (≤) (s + 1) r); intros; simpl in *.
   rewrite shiftl_2.
   apply nonneg_mult_compat; [solve_propholds |].
   now apply rings.flip_nonneg_minus.
  rewrite shiftl_2.
  now apply (nonneg_mult_compat _ _ _).
Qed.

Lemma AQsqrt_loop_fst_upper_bound (n : nat) :
  fst (AQsqrt_loop n) ≤ 2 ^ (3 + n).
Proof with auto.
  transitivity (2 * snd (AQsqrt_loop n) + 4).
   apply AQsqrt_loop_invariant2.
  change (2 ^ (3 + n)) with (2 * (2 * (2 * 2 ^ n))).
  setoid_replace (2 * snd (AQsqrt_loop n) + 4) with (2 * (snd (AQsqrt_loop n) + 2)) by ring.
  apply (order_preserving (2 *.)).
  setoid_replace (2 * (2 * 2 ^ n)) with ((4 * 2 ^ n - 2) + 2) by ring.
  apply (order_preserving (+ 2)).
  transitivity (4 * 2 ^ n - 4).
   rewrite <-(rings.plus_0_r n) at 1.
   rewrite <-(rings.plus_0_l 4) at 1.
   now apply AQsqrt_loop_snd_upper_bound.
  apply semirings.plus_le_compat.
   now rewrite commutativity.
  now apply rings.flip_le_negate, semirings.le_2_4.
Qed.

Definition AQsqrt_mid_bounded_raw (n : N) := snd (AQsqrt_loop ('n)) ≪ -(1 + 'n : Z).

Instance AQsqrt_mid_bounded_raw_proper: Proper ((=) ==> (=)) AQsqrt_mid_bounded_raw.
Proof. intros x y E. change (x ≡ y) in E. now subst. Qed.

Lemma AQsqrt_mid_bounded_raw_lower_bound (n : N) :
  0 ≤ AQsqrt_mid_bounded_raw n.
Proof. unfold AQsqrt_mid_bounded_raw. apply shiftl_nonneg, AQsqrt_loop_snd_nonneg. Qed.

Lemma AQsqrt_mid_bounded_raw_upper_bound (n : N) :
  AQsqrt_mid_bounded_raw n ≤ 4.
Proof.
  unfold AQsqrt_mid_bounded_raw.
  apply (order_reflecting (≪ 1 + 'n)).
  rewrite shiftl_reverse by ring.
  etransitivity.
   rewrite <-(rings.plus_0_r ('n)).
   now apply AQsqrt_loop_snd_upper_bound.
  simpl. 
  apply rings.nonneg_minus_compat; [solve_propholds|].
  rewrite rings.plus_0_l, shiftl_S.
  apply semirings.ge_1_mult_le_compat_l.
    now apply semirings.le_1_2.
   solve_propholds.
  apply orders.eq_le.
  now rewrite shiftl_nat_pow_alt, preserves_nat_pow_exp.
Qed.

Lemma AQsqrt_mid_bounded_regular_aux1 (n m : N) :
  m ≤ n → AQsqrt_mid_bounded_raw n - AQsqrt_mid_bounded_raw m ≤ 1 ≪ (1 - 'm : Z).
Proof.
  intros E.
  apply naturals.nat_le_plus in E.
  destruct E as [z E]. rewrite commutativity in E. 
  change (n ≡ z + m) in E. subst.
  unfold AQsqrt_mid_bounded_raw.
  rewrite rings.preserves_plus.
  etransitivity.
   apply semirings.plus_le_compat; [| reflexivity].
   apply (order_preserving (≪ _)).
   etransitivity.
    now apply AQsqrt_loop_snd_upper_bound.
   apply rings.nonneg_minus_compat; [solve_propholds | reflexivity].
  apply orders.eq_le.
  rewrite <-(shiftl_nat_pow_alt (f:=cast nat Z)).
  rewrite (naturals.to_semiring_twice _ _ (cast N Z)).
  rewrite <-shiftl_exp_plus, rings.preserves_plus.
  mc_setoid_replace ('z - (1 + ('z + 'm)) : Z) with (-(1 + 'm) : Z) by ring.
  rewrite shiftl_base_plus. ring_simplify.
  mc_setoid_replace (1 - ' m : Z) with (2 - (1 + 'm) : Z) by ring.
  now rewrite shiftl_exp_plus, shiftl_2, rings.mult_1_r.
Qed.

Lemma AQsqrt_mid_bounded_regular_aux2 (n m : N) :
  n ≤ m → AQsqrt_mid_bounded_raw n ≤ AQsqrt_mid_bounded_raw m.
Proof.
  intros E.
  apply naturals.nat_le_plus in E.
  destruct E as [z E]. rewrite commutativity in E. 
  change (m ≡ z + n) in E. subst.
  unfold AQsqrt_mid_bounded_raw.
  rewrite 2!rings.preserves_plus.
  mc_setoid_replace (-(1 + 'n) : Z) with ('z - (1 + ('z + 'n) : Z)) by ring.
  rewrite shiftl_exp_plus.
  apply (order_preserving (≪ _)).
  rewrite shiftl_nat_pow_alt, <-(preserves_nat_pow_exp (f:=cast N nat)).
  now apply AQsqrt_loop_snd_lower_bound.
Qed.

Lemma AQsqrt_mid_bounded_spec (n : N) : 
  (AQsqrt_mid_bounded_raw n ^ (2:N)) = a - fst (AQsqrt_loop ('n)) ≪ -(2 * 'n).
Proof.
  unfold AQsqrt_mid_bounded_raw.
  rewrite shiftl_base_nat_pow, rings.preserves_2.
  apply (injective (≪ (2 + 2 * 'n))).
  rewrite shiftl_reverse by ring.
  rewrite shiftl_base_plus, shiftl_negate, <-shiftl_exp_plus.
  mc_setoid_replace (-(2 * 'n) + (2 + 2 * 'n) : Z) with (2 : Z) by ring.
  rewrite shiftl_exp_plus, ?shiftl_2, <-shiftl_mult_l.
  rewrite <-(rings.preserves_2 (f:=cast N Z)), <-rings.preserves_mult.
  rewrite shiftl_nat_pow_alt, nat_pow_exp_mult.
  rewrite (commutativity a), associativity.
  rewrite <-(preserves_nat_pow_exp (f:=cast N nat) _ n).
  setoid_replace (2 ^ 2) with 4 by (rewrite nat_pow_2; ring).
  apply (right_cancellation (+) (4 * fst (AQsqrt_loop (' n)))).
  rewrite AQsqrt_loop_invariant1. ring.
Qed.

Lemma AQsqrt_mid_bounded_raw_square_upper_bound (n : N) :
  AQsqrt_mid_bounded_raw n ^ (2:N) ≤ a.
Proof.
  rewrite AQsqrt_mid_bounded_spec.
  apply rings.nonneg_minus_compat; [| reflexivity].
  now apply shiftl_nonneg, AQsqrt_loop_fst_nonneg.
Qed.

Definition AQsqrt_mid_raw (ε : Qpos)
  := AQsqrt_mid_bounded_raw (plus (N_of_Z (-Qdlog2 (proj1_sig ε))) 3).

Instance: Proper (QposEq ==> (=)) AQsqrt_mid_raw.
Proof. unfold AQsqrt_mid_raw. intros [x?] [y?] E. change (x = y) in E. simpl. now rewrite E. Qed.

Lemma AQsqrt_mid_bounded_prf: is_RegularFunction_noInf _ (AQsqrt_mid_raw : Qpos → AQ_as_MetricSpace).
Proof.
  assert (∀ n m, m ≤ n → ball (2 ^ (-cast N Z m - 2))
    (AQsqrt_mid_bounded_raw (n + 3) : AQ_as_MetricSpace) (AQsqrt_mid_bounded_raw (m + 3))).
   intros n m E.
   simpl. apply Qball_Qabs. rewrite Qabs.Qabs_pos. 
    change ('AQsqrt_mid_bounded_raw (n + 3) - 'AQsqrt_mid_bounded_raw (m + 3) ≤ (2 ^ (-'m - 2) : Q)).
    rewrite <-rings.preserves_minus, <-(rings.mult_1_l (2 ^ (-'m - 2))).
    rewrite <-shiftl_int_pow.
    rewrite <-(rings.preserves_1 (f:=cast AQ Q)), <-(preserves_shiftl (f:=cast AQ Q)).
    apply (order_preserving _).
    mc_setoid_replace (-'m - 2 : Z) with (1 - '(m + 3) : Z).
     apply AQsqrt_mid_bounded_regular_aux1.
     now refine (order_preserving (+ (3:N)) _ _ _).
    rewrite rings.preserves_plus, rings.preserves_3. ring.
   change (0 ≤ ('AQsqrt_mid_bounded_raw (n + 3) - 'AQsqrt_mid_bounded_raw (m + 3) : Q)).
   apply rings.flip_nonneg_minus.
   apply (order_preserving _).
   apply AQsqrt_mid_bounded_regular_aux2.
   now refine (order_preserving (+ (3:N)) _ _ _).
  assert (∀ ε1 ε2 : Qpos, N_of_Z (-Qdlog2 (proj1_sig ε2)) ≤ N_of_Z (-Qdlog2 (proj1_sig ε1)) → 
     ball (proj1_sig ε1 + proj1_sig ε2) (AQsqrt_mid_raw ε1 : AQ_as_MetricSpace) (AQsqrt_mid_raw ε2)).
  { intros ε1 ε2 E.
   unfold AQsqrt_mid_raw.
   eapply ball_weak_le; auto.
   change ((2:Q) ^ (-'N_of_Z (-Qdlog2 (proj1_sig ε2)) - 2)
                     ≤ proj1_sig ε1 + proj1_sig ε2).
   apply semirings.plus_le_compat_l.
   now apply orders.lt_le, Qpos_ispos.
   destruct (total (≤) (proj1_sig ε2) 1).
    rewrite N_of_Z_nonneg.
     change (- (-Qdlog2 (proj1_sig ε2))%Z) with (- -Qdlog2 (proj1_sig ε2)).
     rewrite rings.negate_involutive.
     rewrite int_pow_exp_plus by solve_propholds.
     transitivity (2 ^ Qdlog2 (proj1_sig ε2) : Q).
      2: now apply Qdlog2_spec, Qpos_ispos.
     rewrite <-(rings.mult_1_r (2 ^ Qdlog2 (proj1_sig ε2) : Q)) at 2.
     now apply (order_preserving (_ *.)).
     change (0 ≤ -Qdlog2 (proj1_sig ε2)).
     now apply rings.flip_nonpos_negate, Qdlog2_nonpos.
   transitivity (1:Q); auto.
   rewrite N_of_Z_nonpos; [easy|].
   change (-Qdlog2 (proj1_sig ε2) ≤ 0).
   now apply rings.flip_nonneg_negate, Qdlog2_nonneg. }
  intros ε1 ε2.
  destruct (total (≤) (N_of_Z (-Qdlog2 (proj1_sig ε1)))
                  (N_of_Z (-Qdlog2 (proj1_sig ε2)))); auto.
  apply ball_sym. 
  rewrite Qplus_comm. auto.
Qed.

Definition AQsqrt_mid : AR := mkRegularFunction (0 : AQ_as_MetricSpace) AQsqrt_mid_bounded_prf.

Lemma AQsqrt_mid_upper_bound : AQsqrt_mid ≤ 4.
Proof.
  intros ε.
  transitivity (0 : Q).
   apply rings.flip_nonneg_negate.
   now apply orders.lt_le, Qpos_ispos.
  change ((0:Q) ≤ '(4 - AQsqrt_mid_raw ((1#2) * ε))).
  apply semirings.preserves_nonneg, rings.flip_nonneg_minus.
  now apply AQsqrt_mid_bounded_raw_upper_bound.
Qed.

Lemma AQsqrt_mid_nonneg : 0 ≤ AQsqrt_mid.
Proof.
  intros ε.
  transitivity (0 : Q).
   apply rings.flip_nonneg_negate.
   now apply orders.lt_le, Qpos_ispos.
  change ((0:Q) ≤ '(AQsqrt_mid_raw ((1#2) * ε) - 0)).
  apply semirings.preserves_nonneg, rings.flip_nonneg_minus.
  now apply AQsqrt_mid_bounded_raw_lower_bound.
Qed.

Lemma AQsqrt_mid_spec : AQsqrt_mid ^ (2:N)= 'a.
Proof.
  assert (∀ ε, Qball (proj1_sig ε) ('(AQsqrt_mid_raw ε ^ (2:N))) ('a)) as P.
  { intros ε. apply Qball_Qabs. rewrite Qabs.Qabs_neg.
    eapply Qle_trans.
     2: now apply Qpos_dlog2_spec.
     change (-( '(AQsqrt_mid_raw ε ^ 2) - 'a) ≤ (2 ^ Qdlog2 (proj1_sig ε) : Q)).
    rewrite <-rings.negate_swap_r.
    unfold AQsqrt_mid_raw. rewrite AQsqrt_mid_bounded_spec.
    rewrite rings.preserves_minus, preserves_shiftl. ring_simplify.
    apply shiftl_le_flip_l.
    etransitivity.
     apply (order_preserving _).
     now apply AQsqrt_loop_fst_upper_bound.
    rewrite preserves_nat_pow, rings.preserves_2.
    rewrite <-(int_pow_nat_pow (f:=cast nat Z)).
    rewrite shiftl_int_pow, <-int_pow_exp_plus by solve_propholds.
    apply int_pow_exp_le; [apply semirings.le_1_2|].
    rewrite rings.preserves_plus, (naturals.to_semiring_twice _ _ (cast N Z)).
    rewrite (rings.preserves_plus _ 3), !rings.preserves_3.
    apply (order_reflecting (+ -(3 + 3))). ring_simplify.
    destruct (total (≤) (proj1_sig ε) 1).
     rewrite N_of_Z_nonneg.
      apply orders.eq_le. 
      change (-Qdlog2 (proj1_sig ε) = 2 * -Qdlog2 (proj1_sig ε) + Qdlog2 (proj1_sig ε)).
      ring.
      change (0 ≤ -Qdlog2 (proj1_sig ε)).
      now apply rings.flip_nonpos_negate, Qdlog2_nonpos.
    rewrite N_of_Z_nonpos.
     now apply Qdlog2_nonneg.
     change (-Qdlog2 (proj1_sig ε) ≤ 0).
     now apply rings.flip_nonneg_negate, Qdlog2_nonneg.
   change ('(AQsqrt_mid_raw ε ^ 2) - 'a ≤ (0:Q)).
   apply rings.flip_nonpos_minus.
   apply (order_preserving _).
   now apply AQsqrt_mid_bounded_raw_square_upper_bound. }
  rewrite <-(ARpower_N_bounded_N_power _ _ 4). 
  - intros ε1 ε2. simpl.
   rewrite lattices.meet_r, lattices.join_r.
    + apply ball_weak. apply Qpos_nonneg.
      apply ball_weak_le with (proj1_sig (ε1 * Qpos_inv (8 # 1))%Qpos).
      change ('ε1 / (8#1) ≤ 'ε1). 
      rewrite <-(rings.mult_1_r ('ε1)) at 2.
      apply Qmult_le_l. apply Qpos_ispos. discriminate.
      assert (QposEq (ε1 * Qpos_inv ((2#1) * Qpos_power (' 4) 1))
                     (ε1 * Qpos_inv (8#1))).
      unfold QposEq. simpl.
      pose proof AQposAsQpos_preserves_4.
      unfold equiv, sig_equiv, equiv, stdlib_rationals.Q_eq in H5.
      simpl. rewrite H5. reflexivity.
      rewrite H5. apply P.
    + transitivity (0:AQ).
     apply rings.flip_nonneg_negate. now apply semirings.le_0_4.
    now apply AQsqrt_mid_bounded_raw_lower_bound.
    + now apply AQsqrt_mid_bounded_raw_upper_bound.
  - split.
   transitivity (0:AR).
    apply rings.flip_nonneg_negate.
    apply (semirings.preserves_nonneg (f:=cast AQ AR)).
    now apply semirings.le_0_4.
   now apply AQsqrt_mid_nonneg.
  now apply AQsqrt_mid_upper_bound.
Qed.

Lemma AQsqrt_mid_correct : 'AQsqrt_mid = rational_sqrt ('a).
Proof.
  apply rational_sqrt_unique.
    apply semirings.preserves_nonneg.
    red. transitivity 1; [solve_propholds | intuition].
   change ('AQsqrt_mid ^ (2 : N) = cast Q CR (cast AQ Q a)).
   rewrite <-preserves_nat_pow.
   rewrite AQsqrt_mid_spec.
   now apply ARtoCR_inject.
  change (0%CR) with (0 : CR).
  rewrite <-(rings.preserves_0 (f:=cast AR CR)).
  apply (order_preserving _).
  now apply AQsqrt_mid_nonneg.
Qed.
End sqrt_mid.

Section sqrt_pos.
Context `(Pa : 0 < a).

Local Obligation Tactic := idtac.
Program Definition AQsqrt_pos :=
  let n := Qdlog4 ('a) in ARscale (1 ≪ n) (AQsqrt_mid (a:=a ≪ (2 * -n)) _).
Next Obligation.
  simpl. split.
   apply (order_reflecting (cast AQ Q)).
   rewrite rings.preserves_1, aq_shift_correct.
   rewrite int_pow_exp_mult.
   change (2 ^ 2 : Q) with (4 : Q).
   apply (order_reflecting (.* 4 ^ Qdlog4 ('a))).
   rewrite <-associativity, <-int_pow_exp_plus by (compute; discriminate).
   rewrite rings.mult_1_l, rings.plus_negate_l, int_pow_0, rings.mult_1_r.
   apply Qdlog4_spec.
   now apply semirings.preserves_pos.
  apply (order_reflecting (cast AQ Q)).
  rewrite aq_shift_correct, rings.preserves_4.
  rewrite int_pow_exp_mult.
  change (2 ^ 2 : Q) with (4 : Q).
  apply (order_reflecting (.* 4 ^ Qdlog4 ('a))).
  rewrite <-associativity, <-int_pow_exp_plus by (compute; discriminate).
  rewrite rings.plus_negate_l, int_pow_0, rings.mult_1_r.
  rewrite <-int_pow_S by (compute; discriminate).
  apply orders.lt_le, Qdlog4_spec.
  now apply semirings.preserves_pos.
Qed.

Lemma AQsqrt_pos_correct : 'AQsqrt_pos = rational_sqrt ('a).
Proof.
  unfold AQsqrt_pos.
  rewrite ARtoCR_preserves_scale, AQsqrt_mid_correct.
  rewrite 2!aq_shift_correct, rings.preserves_1, rings.mult_1_l.
  rewrite int_pow_exp_mult.
  apply rational_sqrt_scale.
  apply semirings.preserves_nonneg.
  now apply orders.lt_le.
Qed.
End sqrt_pos.

Program Definition AQsqrt (a : AQ) : AR := 
  if decide_rel (≤) a 0 then 0 else AQsqrt_pos (a:=a) _.
Next Obligation. now apply orders.not_le_lt_flip. Qed.

Lemma AQsqrt_correct (a : AQ) : 'AQsqrt a = rational_sqrt ('a).
Proof.
  unfold AQsqrt.
  case (decide_rel _); intros E.
   rewrite rational_sqrt_nonpos.
    now apply rings.preserves_0.
   now apply semirings.preserves_nonpos.
  now apply AQsqrt_pos_correct.
Qed.

Local Obligation Tactic := idtac.
Require Import CoRN.metric2.MetricMorphisms.

Program Definition ARsqrt_uc := unary_complete_uc 
  QPrelengthSpace (cast AQ Q_as_MetricSpace) AQsqrt sqrt_uc _.
Next Obligation. intros a. apply AQsqrt_correct. Qed.

Definition ARsqrt := Cbind AQPrelengthSpace ARsqrt_uc.

Lemma ARtoCR_preserves_sqrt (x : AR) : 'ARsqrt x = CRsqrt ('x).
Proof. apply preserves_unary_complete_fun. Qed.

Lemma ARsqrt_correct : forall (x : AR),
    ARle 0 x -> ARsqrt x * ARsqrt x = x.
Proof.
  intros x xpos.
  apply (injective (Eembed QPrelengthSpace (cast AQ Q_as_MetricSpace))).
  change (Eembed QPrelengthSpace (cast AQ Q_as_MetricSpace) x)
    with ('x).
  change (Eembed QPrelengthSpace (cast AQ Q_as_MetricSpace) (ARsqrt x * ARsqrt x))
    with ('(ARsqrt x * ARsqrt x)).
  rewrite (ARtoCR_preserves_mult (ARsqrt x) (ARsqrt x)).
  rewrite ARtoCR_preserves_sqrt.
  apply CRsqrt_sqr.
  rewrite <- ARtoCR_preserves_0.
  apply (ARtoCR_preserves_le 0 x), xpos.
Qed.

Lemma ARsqrt_mult : forall (x y : AR),
    ARle 0 x -> ARle 0 y -> ARsqrt (x*y) = ARsqrt x * ARsqrt y.
Proof.
  intros.
  apply (injective (Eembed QPrelengthSpace (cast AQ Q_as_MetricSpace))).
  change (Eembed QPrelengthSpace (cast AQ Q_as_MetricSpace) (ARsqrt (x*y)))
    with ('(ARsqrt (x*y))).
  change (Eembed QPrelengthSpace (cast AQ Q_as_MetricSpace) (ARsqrt x * ARsqrt y))
    with ('(ARsqrt x * ARsqrt y)).
  rewrite (ARtoCR_preserves_mult (ARsqrt x) (ARsqrt y)).
  rewrite ARtoCR_preserves_sqrt.
  rewrite ARtoCR_preserves_sqrt.
  rewrite ARtoCR_preserves_sqrt.
  rewrite <- CRsqrt_mult.
  rewrite ARtoCR_preserves_mult. reflexivity.
  rewrite <- ARtoCR_preserves_0.
  apply (ARtoCR_preserves_le 0 x), H5.
  rewrite <- ARtoCR_preserves_0.
  apply (ARtoCR_preserves_le 0 y), H6.
Qed.

Lemma ARsqrt_srq_abs :
  forall x : AR, ARsqrt (x*x) = ARabs x.
Proof.
  (* Goal is a negation, use excluded middle x is positive or not.
     When positive, ARsqrt(x*x) = ARsqrt x*ARsqrt x = x. *)
  assert (forall x : AR, ARle 0 x -> ARsqrt (x*x) = ARabs x) as posCase.
  { intros.
    rewrite ARsqrt_mult, ARsqrt_correct.
    rewrite ARabs_pos. reflexivity.
    exact H5. exact H5.
    exact H5. exact H5. } 
  intros. apply Metric_eq_stable.
  intro abs. assert (~(ARle 0 x)).
  - intro H5. contradict abs.
    apply posCase, H5.
  - contradict H5.
    apply ARle_not_lt. intro H5.
    contradict abs.
    change (ARsqrt (x*x) = ARabs x).
    rewrite <- ARabs_opp.
    setoid_replace (x * x) with (-x * -x) by ring.
    apply posCase.
    destruct (ARtoCR_preserves_ltT x 0) as [c _].
    specialize (c H5).
    apply ARtoCR_preserves_le.
    rewrite ARtoCR_preserves_0.
    rewrite <- CRopp_0.
    rewrite ARtoCR_preserves_opp.
    apply CRopp_le_compat.
    rewrite <- ARtoCR_preserves_0.
    apply CRlt_le_weak, c.
Qed.

Lemma ARsqrt_inc :
  forall x y : AR,
    ARle 0 x -> ARle x y -> ARle (ARsqrt x) (ARsqrt y).
Proof.
  intros. 
  apply ARtoCR_preserves_le.
  rewrite ARtoCR_preserves_sqrt.
  rewrite ARtoCR_preserves_sqrt.
  apply CRsqrt_inc.
  rewrite <- ARtoCR_preserves_0.
  apply (ARtoCR_preserves_le 0 x), H5.
  apply (ARtoCR_preserves_le x y), H6.
Qed.



End ARsqrt.
