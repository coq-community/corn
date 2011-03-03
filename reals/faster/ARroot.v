Require Import
  Ring Setoid 
  Complete Qmetric ZArith Qdlog2 Qpossec
  CRroot
  abstract_algebra theory.shiftl theory.nat_pow theory.int_pow.
Require Export 
  ARArith.

Section ARroot.
Context `{AppRationals AQ}.

Add Ring AQ : (rings.stdlib_ring_theory AQ).
Add Ring Q : (rings.stdlib_ring_theory Q).
Add Ring Z : (rings.stdlib_ring_theory Z).

Section root_mid.
Context `(Pa : 1 ≤ a ≤ 4).

Fixpoint AQroot_loop (n : nat) : AQ * AQ :=
  match n with
  | O => (a, 0)
  | S n => 
     let (r, s) := AQroot_loop n in
     if decide_rel (≤) (s + 1) r
     then ((r - (s + 1)) ≪ (2:Z), (s + 2) ≪ (1:Z))
     else (r ≪ (2:Z), s ≪ (1:Z))
  end.

Instance: Proper (=) AQroot_loop.
Proof. intros x y E. change (x ≡ y) in E. now rewrite E. Qed.

Lemma AQroot_loop_invariant1 (n : nat) : 
  snd (AQroot_loop n) * snd (AQroot_loop n) + 4 * fst (AQroot_loop n) = 4 * 4 ^ n * a.
Proof.
  induction n; unfold pow; simpl.
   ring.
  case_eq (AQroot_loop n); intros r s E. rewrite E in IHn. clear E.
  case (decide_rel (≤) (s + 1) r); intros Esr; simpl in *;
   rewrite shiftl_1, shiftl_2, <-(associativity 4), <-IHn; ring.
Qed.

Lemma AQroot_loop_invariant2 (n : nat) : 
  fst (AQroot_loop n) ≤ 2 * snd (AQroot_loop n) + 4.
Proof.
  induction n; simpl.
   now setoid_replace (2 * 0 + 4) with 4 by ring.
  case_eq (AQroot_loop n); intros r s E. rewrite E in IHn. clear E.
  case (decide_rel (≤) (s + 1) r); intros Esr; simpl in *.
   rewrite shiftl_1, shiftl_2.
   setoid_replace (2 * (2 * (s + 2)) + 4) with (4 * ((2 * s + 4) - (s + 1))) by ring.
   apply (order_preserving (4 *.)).
   now apply (order_preserving (+ _)).
  rewrite shiftl_1, shiftl_2.
  setoid_replace (2 * (2 * s) + 4) with (4 * (s + 1)) by ring.
  apply (order_preserving (4 *.)).
  now apply orders.precedes_flip.
Qed.

Lemma AQroot_loop_fst_nonneg (n : nat) : 0 ≤ fst (AQroot_loop n).
Proof.
  induction n; simpl.
   transitivity 1. apply (rings.ge_0 1). easy.
  case_eq (AQroot_loop n); intros r s E. rewrite E in IHn. clear E.
  case (decide_rel (≤) (s + 1) r); intros Esr; simpl in *.
   rewrite shiftl_2.
   apply semirings.nonneg_mult_compat.
    now apply (rings.ge_0 4).
   now apply rings.flip_nonneg_minus.
  rewrite shiftl_2.
  now apply (semirings.nonneg_mult_compat _ _ _).
Qed.

Lemma AQroot_loop_snd_nonneg (n : nat) : 0 ≤ snd (AQroot_loop n).
Proof.
  induction n; simpl.
   reflexivity.
  case_eq (AQroot_loop n); intros r s E. rewrite E in IHn. clear E.
  case (decide_rel (≤) (s + 1) r); intros Esr; simpl in *.
   rewrite shiftl_1.
   apply semirings.nonneg_mult_compat. now apply (rings.ge_0 2).
   apply semirings.nonneg_plus_compat. easy. now apply (rings.ge_0 2).
  rewrite shiftl_1.
  apply semirings.nonneg_mult_compat. now apply (rings.ge_0 2). easy.
Qed.

Lemma AQroot_loop_snd_bound (n z : nat) : (* snd (AQroot_loop n) * 2 ^ m ≤ *)
  snd (AQroot_loop (z + n)) ≤ 2 ^ z * (snd (AQroot_loop n) + 4) - 4.
Proof.
  induction z; unfold pow; simpl.
   apply orders.equiv_precedes. ring.
  revert IHz. case (AQroot_loop (z + n)); case (AQroot_loop n); simpl; intros r1 s1 r2 s2 IHz.
  case (decide_rel (≤) _); simpl; intros E.
   rewrite shiftl_1.
   setoid_replace (2 * 2 ^ z * (s1 + 4) - 4) with (2 * (2 ^ z * (s1 + 4) - 4 + 2)) by ring.
   apply (order_preserving (2 *.)).
   now apply (order_preserving (+2)).
  rewrite shiftl_1.
  setoid_replace (2 * 2 ^ z * (s1 + 4) - 4) with (2 * (2 ^ z * (s1 + 4) - 4 + 2)) by ring.
  apply (order_preserving (2 *.)).
  apply semirings.nonneg_plus_compat_r.
   easy.
  apply (rings.ge_0 2).
Qed.

Lemma AQroot_loop_fst_bound (n : nat) :
  fst (AQroot_loop n) ≤ 2 ^ (3 + n).
Proof with auto.
  transitivity (2 * snd (AQroot_loop n) + 4).
   apply AQroot_loop_invariant2.
  unfold pow. simpl.
  setoid_replace (2 * snd (AQroot_loop n) + 4) with (2 * (snd (AQroot_loop n) + 2)) by ring.
  apply (order_preserving (2 *.)).
  setoid_replace (2 * (2 * 2 ^ n)) with ((4 * 2 ^ n - 2) + 2) by ring.
  apply (order_preserving (+ 2)).
  transitivity (2 ^ n * 4 - 4).
   rewrite <-(rings.plus_0_r n) at 1.
   rewrite <-(rings.plus_0_l 4) at 1.
   now apply AQroot_loop_snd_bound.
  apply semirings.plus_compat.
   rewrite commutativity.
   reflexivity.
  apply rings.flip_opp.
  apply semirings.precedes_2_4.
Qed.

Definition AQroot_mid_bounded_raw (n : N) : AQ_as_MetricSpace := snd (AQroot_loop ('n)) ≪ -('n + 1 : Z).

Lemma AQroot_mid_bounded_regular_aux1 (n m : N) :
  m ≤ n → 'AQroot_mid_bounded_raw n - 'AQroot_mid_bounded_raw m ≤ 2 ^ (-'m + 1).
Proof.
  intros E.
  apply naturals.natural_precedes_plus in E.
  destruct E as [z E]. rewrite commutativity in E. 
  change (n ≡ z + m) in E. rewrite E. clear E n.
  unfold AQroot_mid_bounded_raw.
  rewrite 2!aq_shift_correct.
  rewrite 2!rings.preserves_plus.
  etransitivity.
   apply semirings.plus_compat; [| reflexivity].
   apply (order_preserving (.* _)).
   apply (order_preserving _).
   etransitivity.
    apply AQroot_loop_snd_bound.
   apply rings.nonneg_minus_compat. apply semirings.precedes_0_4. reflexivity.
  apply orders.equiv_precedes.
  rewrite rings.preserves_mult, rings.preserves_plus, rings.preserves_4.
  rewrite <-(associativity ('z)), rings.plus_opp_distr.
  rewrite int_pow_exp_plus by apply (rings.ne_0 (2:Q)).
  assert (∀ a b c d : Q, a * b * (c * d) = (a * c) * b * d) as E by (intros; ring). rewrite E.
  setoid_replace ('(2 ^ ('z : nat)) * 2 ^ (-'z) : Q) with (1 : Q) using relation (@equiv Q _).
   setoid_replace (-'m + 1) with (-('m + 1) + 2) using relation (@equiv Z _) by ring.
   rewrite int_pow_exp_plus by apply (rings.ne_0 (2:Q)).
   ring_simplify. now rewrite commutativity.
  rewrite preserves_nat_pow, rings.preserves_2.
  rewrite int_pow_opp, int_pow_nat_pow, preserves_nat_pow_exp.
  apply fields.dec_mult_inverse.
  apply _.
Qed.

Lemma AQroot_mid_bounded_regular_aux2 (n m : N) :
  n ≤ m → 'AQroot_mid_bounded_raw n ≤ 'AQroot_mid_bounded_raw m.
Proof.
  intros E.
  apply naturals.natural_precedes_plus in E.
  destruct E as [z E]. rewrite commutativity in E. 
  change (m ≡ z + n) in E. rewrite E. clear E m.
  unfold AQroot_mid_bounded_raw.
  rewrite 2!aq_shift_correct.
  rewrite 2!rings.preserves_plus.
Admitted.

Definition AQroot_mid_raw (ε : Qpos) : AQ_as_MetricSpace := AQroot_mid_bounded_raw (Zabs_N (Qdlog2 ε) + 3).

Lemma AQroot_mid_bounded_prf: is_RegularFunction_noInf _ AQroot_mid_raw.
Proof.
  assert (∀ n m, m ≤ n → ball (2 ^ (-coerce m - 2)) 
    (AQroot_mid_bounded_raw (n + 3)) (AQroot_mid_bounded_raw (m + 3))) as P.
   intros n m E.
   simpl. apply Qball_Qabs. change Qabs.Qabs with (abs : Q → Q). rewrite abs.abs_nonneg.
   setoid_replace (-'m - 2) with (-'(m + 3) + 1) using relation (@equiv Z _).
    apply AQroot_mid_bounded_regular_aux1.
    now apply (order_preserving (+3)) in E.
   rewrite rings.preserves_plus, rings.preserves_3. ring.
  unfold Qminus. apply rings.flip_nonneg_minus.
  apply AQroot_mid_bounded_regular_aux2.
  now apply (order_preserving (+3)) in E.
  intros ε1 ε2.
  unfold AQroot_mid_raw.
  destruct (total_order (Zabs_N (Qdlog2 ε1)) (Zabs_N (Qdlog2 ε2))).
   apply ball_sym.
   eapply ball_weak_le.
    2: now apply P.
   simpl. admit.
  eapply ball_weak_le.
   2: now apply P.
  admit.
Qed.

Definition AQroot_mid : AR := mkRegularFunction (0 : AQ_as_MetricSpace) AQroot_mid_bounded_prf.

Lemma AQroot_mid_spec : ARpower_positive 2 AQroot_mid = 'a.
Proof.
  intros ? ?. apply regFunEq_e. intros ε.
  simpl.
  unfold Prelength.Cap_raw, Prelength.Cmap. simpl.
  apply Qball_Qabs. change Qabs.Qabs with (abs : Q → Q). rewrite abs.abs_nonpos. 
Admitted.
End root_mid.

Section root_pos.
Context `(Pa : 0 < a).

Local Obligation Tactic := idtac.
Program Definition AQroot_pos :=
  let n := Zdiv (Qdlog2 ('a)) 2 in ARscale (1 ≪ n) (AQroot_mid (a:=a ≪ (2 * -n)) _).
Next Obligation.
  simpl. split.
   apply (order_preserving_back (coerce : AQ → Q)).
   rewrite rings.preserves_1, aq_shift_correct.
   admit.
  admit.
Qed.
End root_pos.

Program Definition AQroot (a : AQ) : AR := 
  match decide_rel (≤) a 0 with
  | left _ => 0
  | right _ => AQroot_pos (a:=a)
  end.

Lemma AQroot_correct (a : AQ) : ARtoCR (AQroot a) = rational_sqrt ('a).
Proof.
Admitted.

Local Obligation Tactic := idtac.
Require Import MetricMorphisms.

Program Definition ARroot_uc := 
  unary_complete_uc QPrelengthSpace coerce AQroot sqrt_uc _.
Next Obligation. intros a. apply AQroot_correct. Qed.

Definition ARroot := Cbind AQPrelengthSpace ARroot_uc.

End ARroot.
