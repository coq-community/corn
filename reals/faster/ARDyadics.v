Require Import
  Program QArith ZArith BigZ Qpossec
  MetricMorphisms Qmetric Qdlog
  ApproximateRationals ARArith
  interfaces.integers interfaces.rationals
  theory.int_pow theory.nat_pow
  stdlib_rationals stdlib_binary_integers fast_integers dyadics.

Add Field Q : (fields.stdlib_field_theory Q).

Notation fastD := (Dyadic fastZ).
Instance fastZtoQ : Coerce fastZ Q_as_MetricSpace := inject_Z ∘ BigZ.to_Z.
Instance ZtofastD : Coerce Z fastD := dy_inject ∘ BigZ.of_Z.
Instance NtofastZ : Coerce N fastZ := BigZ.of_Z ∘ Z_of_N.
Instance fastDtoQ : Coerce fastD Q_as_MetricSpace := DtoQ fastZtoQ.

Lemma fastDtoQ_correct x : fastDtoQ x = 'mant x * 2 ^ ('expo x : Z).
Proof.
  unfold fastDtoQ.
  rewrite (DtoQ_correct _ _ (reflexivity x)).
  unfold DtoQ_slow.
  now rewrite (preserves_int_pow_exp (f:=coerce : bigZ → Z)).
Qed.

(* 
  We use BigZ.div and BigZ.shiftl because we don't have any theory on euclid and shiftr
  in math-classes yet. Moreover, BigZ.shiftl behaves as shiftr on its negative domain,
  which is quite convenient here.
*)
Program Instance fastD_div : AppDiv fastD := λ x y k,
  BigZ.div (BigZ.shiftl (mant x) (-('k - 1) + expo x - expo y)) (mant y) $ ('k - 1).

Lemma Qdiv_bounded_Zdiv (x y : Z) :
  'Zdiv x y ≤ ('x / 'y : Q) < 'Zdiv x y + 1.
Proof.
  rewrite Qround.Zdiv_Qdiv.
  split.
   now apply Qround.Qfloor_le.
  rewrite <-(rings.preserves_1 (f:=coerce : Z → Q)).
  rewrite <-rings.preserves_plus.
  apply stdlib_rationals.Qlt_coincides.
  now apply Qround.Qlt_floor.
Qed.

Lemma Qpow_bounded_Zshiftl (x n : Z) : 
  'Zshiftl x n ≤ ('x * 2 ^ n : Q) < 'Zshiftl x n + 1.
Proof.
  destruct (total_order 0 n) as [En | En].
   rewrite Z.shiftl_mul_pow2 by trivial.
   rewrite inject_Z_mult.
   rewrite Qpower.Zpower_Qpower by trivial.
   split; try reflexivity.
   apply semirings.pos_plus_scompat_r; try reflexivity.
   apply semirings.sprecedes_0_1.
  rewrite Z.shiftl_div_pow2 by trivial.
  assert (('x * 2 ^ n : Q) = 'x / 'Zpower 2 (-n)).
   rewrite Qpower.Zpower_Qpower.
    rewrite <-Qpower.Qpower_opp, Zopp_involutive.
    reflexivity.
   now apply rings.flip_nonpos_opp in En.
  split.
   transitivity ('x / 'Zpower 2 (-n) : Q).
    now apply Qdiv_bounded_Zdiv.
   apply orders.equiv_precedes. now symmetry.
  apply orders.sprecedes_trans_r with ('x / 'Zpower 2 (-n) : Q).
   now apply orders.equiv_precedes.
  now apply Qdiv_bounded_Zdiv.
Qed.

Lemma fastD_div_correct (x y : fastD) (k : Z) : Qball (2 ^ k) ('app_div x y k) ('x / 'y).
Proof.
  assert (∀ xm xe ym ye : Z, 
      ('xm * 2 ^ xe : Q) / ('ym * 2 ^ ye : Q) = ('xm * 2 ^ (-(k - 1) + xe - ye)) / 'ym * 2 ^ (k - 1)) as E1.
   intros.
   rewrite 2!int_pow_exp_plus by solve_propholds.
   rewrite fields.dec_mult_inv_distr.
   rewrite 2!int_pow_opp.
   transitivity ('xm / 'ym * 2 ^ xe / 2 ^ ye * (2 ^ (k - 1) / 2 ^ (k - 1)) : Q); [| ring].
   rewrite fields.dec_mult_inverse by apply _. ring.
  assert (∀ xm xe ym ye : Z, 
      'Zdiv (Zshiftl xm (-(k - 1) + xe - ye)) ym * 2 ^ (k - 1) - 2 ^ k  ≤ ('xm * 2 ^ xe) / ('ym * 2 ^ ye : Q)) as Pleft.
   clear x y.
   assert (∀ z : Q, z * 2 ^ (k - 1) - 2 ^ k = ((z - 1) - 1) * 2 ^ (k - 1)) as E2.
    intros.
    ms_setoid_replace k with ((k - 1) + 1) at 2 by ring.
    rewrite (int_pow_exp_plus (k - 1)) by solve_propholds.
    ring_simplify. apply sg_mor; [reflexivity | now rewrite commutativity].
   intros. rewrite E1, E2.
   apply (order_preserving (.* _)).
   apply rings.flip_minus_l. apply semirings.nonneg_plus_compat_r; [| easy].
   transitivity ('Zshiftl xm (-(k - 1) + xe - ye) / 'ym - 1 : Q).
    apply (order_preserving (+ -1)). now apply Qdiv_bounded_Zdiv.
   destruct (orders.precedes_or_sprecedes 0 ym) as [E | E].
    apply rings.flip_minus_l. apply semirings.nonneg_plus_compat_r; [| easy].
    apply (maps.order_preserving_flip_ge_0 (.*.) (/ 'ym : Q)).
     apply fields.nonneg_dec_mult_inv_compat.
     now apply semirings.preserves_nonneg.
    now apply Qpow_bounded_Zshiftl.
   transitivity (('Zshiftl xm (-(k - 1) + xe - ye) + 1) / 'ym : Q).
    rewrite rings.plus_mul_distr_r.
    apply semirings.plus_compat; [reflexivity |].
    rewrite rings.mult_1_l.
    apply rings.flip_opp.
    rewrite rings.opp_involutive, fields.dec_mult_inv_opp.
    apply fields.flip_dec_mult_inv_l; [solve_propholds |].
    rewrite <-rings.preserves_opp.
    apply semirings.preserves_ge1.
    apply rings.flip_opp.
    rewrite rings.opp_involutive.
    now apply integers.precedes_sprecedes.
   apply rings.flip_nonpos_mult_r.
    apply fields.nonpos_dec_mult_inv_compat.
    apply semirings.preserves_nonpos.
    now apply orders.sprecedes_weaken. 
   now apply Qpow_bounded_Zshiftl.
  assert (∀ xm xe ym ye : Z, 
      ('xm * 2 ^ xe) / ('ym * 2 ^ ye : Q) ≤ '(Zdiv (Zshiftl xm (-(k - 1) + xe - ye)) ym) * 2 ^ (k - 1) + 2 ^ k) as Pright.
   clear x y.
   assert (∀ z : Q, z * 2 ^ (k - 1) + 2 ^ k = ((z + 1) + 1) * 2 ^ (k - 1)) as E2.
    intros.
    ms_setoid_replace k with ((k - 1) + 1) at 2 by ring.
    rewrite (int_pow_exp_plus (k - 1)) by solve_propholds.
    ring_simplify. apply sg_mor; [reflexivity| apply commutativity].
   intros. rewrite E1, E2.
   apply (order_preserving (.* _)).
   transitivity ('Zshiftl xm (-(k - 1) + xe - ye) / 'ym + 1 : Q).
    2: now apply (order_preserving (+1)), Qdiv_bounded_Zdiv.
   destruct (orders.precedes_or_sprecedes ym 0) as [E3 | E3].
    apply semirings.nonneg_plus_compat_r; [|easy].
    apply rings.flip_nonpos_mult_r.
     apply fields.nonpos_dec_mult_inv_compat.
     now apply semirings.preserves_nonpos.
    now apply Qpow_bounded_Zshiftl.
   transitivity (('Zshiftl xm (-(k - 1) + xe - ye) + 1) / ' ym : Q).
    apply (maps.order_preserving_flip_ge_0 (.*.) (/ 'ym : Q)).
     apply fields.nonneg_dec_mult_inv_compat.
     apply semirings.preserves_nonneg.
     now apply orders.sprecedes_weaken. 
    now apply Qpow_bounded_Zshiftl.
   rewrite rings.plus_mul_distr_r.
   apply semirings.plus_compat; [reflexivity |].
   rewrite rings.mult_1_l.
   apply fields.flip_dec_mult_inv_l; [solve_propholds |].
   apply semirings.preserves_ge1.
   now apply integers.precedes_sprecedes_alt in E3.
  unfold coerce. rewrite 3!fastDtoQ_correct.
  destruct x as [xm xe], y as [ym ye].
  unfold fastZtoQ, coerce, "∘". simpl. unfold coerce. BigZ.zify.
  apply in_Qball. split. apply Pleft. apply Pright.
Qed.

Instance QtofastD: AppInverse fastDtoQ := λ x ε, 
  app_div ('Qnum x) ('(Qden x : Z)) (Qdlog2 ε).

Instance fastD_approx : AppApprox fastD := λ x k,
  BigZ.shiftl (mant x) (-('k - 1) + expo x) $ ('k - 1).

Lemma fastD_approx_correct (x y : fastD) (k : Z) : Qball (2 ^ k) ('app_approx x k) ('x).
Proof.
  setoid_replace (app_approx x k) with (app_div x 1 k).
   setoid_replace ('x : Q) with ('x / '1 : Q).
    now apply fastD_div_correct.
   rewrite rings.preserves_1, fields.dec_mult_inv_1.
   now rewrite rings.mult_1_r.
  unfold app_div, fastD_div.
  simpl. rewrite BigZ.div_1_r.
  setoid_replace (-('k - 1) + expo x - 0) with (-('k - 1) + expo x); [reflexivity |].
  now rewrite rings.opp_0, rings.plus_0_r.
Qed.

Instance: DenseEmbedding fastDtoQ.
Proof.
  split; try apply _.
  intros [n d] ε.
  unfold app_inverse, QtofastD.
  apply ball_weak_le with (2 ^ Qdlog2 ε)%Qpos.
   now apply Qpos_dlog2_spec.
  simpl. rewrite Qmake_Qdiv.
  rewrite 2!(integers.to_ring_unique_alt inject_Z (fastDtoQ ∘ dy_inject ∘ BigZ.of_Z)).
  apply fastD_div_correct.
Qed.

Instance fastD_Zshiftl: ShiftL fastD Z := λ x n, x ≪ 'n.

Instance: Proper ((=) ==> (=) ==> (=)) fastD_Zshiftl.
Proof. unfold fastD_Zshiftl. solve_proper. Qed.

Instance: ShiftLSpec fastD Z fastD_Zshiftl.
Proof.
  split; try apply _; unfold shiftl, fastD_Zshiftl.
   intros x. rewrite rings.preserves_0. now apply shiftl_0.
  intros x n. rewrite rings.preserves_plus. now apply shiftl_S.
Qed.

(* 
  This function is more or less a copy of dy_pow, but uses [N] instead of [BigZ⁺] for the exponent. 
  An alternative definition would have been fastD_Npow x n = dy_pow x (N_to_BigZ_NonNeg n).
  However, then the exponent would be translated from [N] into [BigZ] and back again, due to the 
  definition of [BigZ.pow]. 
*) 
Instance fastD_Npow: Pow fastD N := λ x n, (mant x) ^ n $ 'n * expo x.

Instance: NatPowSpec fastD N fastD_Npow.
Proof.
  split; unfold "^", fastD_Npow, equiv, dy_equiv, DtoQ_slow.
    intros [xm xe] [ym ye] E1 e1 e2 E2. simpl in *.
    rewrite E2. clear e1 E2.
    rewrite 2!(preserves_nat_pow (f:=integers_to_ring fastZ Q)).
    rewrite 2!(commutativity ('e2 : fastZ)).
    rewrite 2!int_pow_exp_mult.
    rewrite 2!(int_pow_nat_pow (f:=coerce : N → fastZ)).
    rewrite <-2!nat_pow_base_mult.
    now rewrite E1.
   intros [xm xe]. simpl.
   rewrite rings.preserves_0, left_absorb.
   now rewrite nat_pow_0.
  intros [xm xe] n. simpl.
  rewrite nat_pow_S.
  rewrite rings.preserves_plus, rings.preserves_1.
  now rewrite distribute_r, left_identity.
Qed.

Instance: AppRationals fastD.
Proof.
  split; try apply _; intros.
   now apply fastD_div_correct.
  now apply fastD_approx_correct.
Qed.

Notation fastAR := (AR (AQ:=fastD)).
