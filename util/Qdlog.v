(* Discrete logarithm with base 2 and 4 on [Q] *)
Require Import 
  ZArith QArith Qround stdlib_omissions.Q Qposclasses
  abstract_algebra additional_operations 
  int_pow orders.rationals stdlib_rationals.

Definition Qdlog2 (x : Q) : Z :=
  match decide_rel (≤) x 1 with
  | left _ => -Z.log2_up (Qround.Qceiling (/x))
  | right _ => Z.log2 (Qround.Qfloor x)
  end.

Instance: Proper (=) Qdlog2.
Proof.
  intros ? ? E. unfold Qdlog2.
  do 2 case (decide_rel _); rewrite E; intros; easy.
Qed.

Lemma Qdlog2_spec (x : Q) : 
  0 < x → 2 ^ Qdlog2 x ≤ x ∧ x < 2 ^ (1 + Qdlog2 x).
Proof.
  intros E1. unfold Qdlog2.
  case (decide_rel _); intros E2.
   destruct (decide (x = 1)) as [E3|E3].
    rewrite E3. compute; repeat split; discriminate.
   assert (1 < Qceiling (/x))%Z.
    apply stdlib_binary_integers.Zlt_coincides.
    apply (maps.strictly_order_preserving_back (coerce : Z → Q)).
    apply orders.sprecedes_trans_l with (/x).
    apply fields.flip_dec_mult_inv_r_strict; [|split]; trivial.
    now apply Qle_ceiling.
   split.
    rewrite int_pow_opp. 
    apply fields.flip_dec_mult_inv_l; trivial.
    transitivity ('Qceiling (/x)).
     now apply Qle_ceiling.
    change 2 with ('(2 : Z)). rewrite <-Qpower.Zpower_Qpower.
     apply (order_preserving _).
     now apply Z.log2_up_spec.
    now apply Z.log2_up_nonneg.
   ms_setoid_replace (1 - Z.log2_up (Qceiling (/x))) with (-Zpred (Z.log2_up (Qceiling (/x)))).
    rewrite int_pow_opp.
    apply fields.flip_dec_mult_inv_r_strict.
     solve_propholds.
    apply orders.sprecedes_trans_r with ('Zpred (Qceiling (/x))).
     change 2 with ('(2 : Z)). rewrite <-Qpower.Zpower_Qpower.
      apply (order_preserving _).
      now apply Z.lt_le_pred, Z.log2_up_spec.
     now apply Z.lt_le_pred, Z.log2_up_pos.
    rewrite <-Z.sub_1_r. 
    now apply stdlib_rationals.Qlt_coincides, Qceiling_lt.
   rewrite <-Z.sub_1_r.
   change (1 - Z.log2_up (Qceiling (/ x)) = -(Z.log2_up (Qceiling (/ x)) - 1)).
   now rewrite <-rings.opp_swap_l, commutativity.
  split.
   transitivity ('Qfloor x).
    change 2 with ('(2 : Z)).
    rewrite <-Qpower.Zpower_Qpower.
     apply (order_preserving _).
     now apply Zlog2_spec, Qfloor_pos, orders.precedes_flip.
    now apply Z.log2_nonneg.
   now apply Qfloor_le.
  apply orders.sprecedes_trans_l with ('Zsucc (Qfloor x)).
   rewrite <-Z.add_1_r.
   now apply stdlib_rationals.Qlt_coincides, Qlt_floor.
  rewrite Z.add_1_l.
  change 2 with ('(2 : Z)).
  rewrite <-Qpower.Zpower_Qpower.
   apply (order_preserving _).
   now apply Zle_succ_l, Zlog2_spec, Qfloor_pos, orders.precedes_flip.
  now apply Zle_le_succ, Z.log2_nonneg.
Qed.

Lemma Qdlog2_nonneg (x : Q) : 
  1 ≤ x → 0 ≤ Qdlog2 x.
Proof.
  intros E. unfold Qdlog2.
  case (decide_rel _); intros.
   now ms_setoid_replace x with (1:Q) by now apply (antisymmetry (≤)).
  apply Z.log2_nonneg.
Qed.

Lemma Qdlog2_nonpos (x : Q) : 
  x ≤ 1 → Qdlog2 x ≤ 0.
Proof.
  intros E. unfold Qdlog2.
  case (decide_rel _); intros.
   apply Z.opp_nonpos_nonneg.
   now apply Z.log2_up_nonneg.
  contradiction.
Qed.

Lemma Qpos_dlog2_spec (x : Qpos) : 
  '(2 ^ Qdlog2 x) ≤ ('x : Q) ∧ 'x < '(2 ^ (1 + Qdlog2 x)).
Proof. unfold coerce. simpl. split; apply Qdlog2_spec; auto. Qed.

Lemma Qdlog2_unique (x : Q) (y : Z) : 
  0 < x → 2 ^ y ≤ x ∧ x < 2 ^ (1 + y) → y = Qdlog2 x.
Proof.
  intros.
  apply (antisymmetry (≤)).
   apply integers.precedes_sprecedes.
   rewrite commutativity.
   apply int_pow_exp_sprecedes_back with 2; [ apply semirings.sprecedes_1_2 |].
   apply orders.sprecedes_trans_r with x; [ intuition |].
   now apply Qdlog2_spec.
  apply integers.precedes_sprecedes.
  rewrite commutativity.
  apply int_pow_exp_sprecedes_back with 2; [ apply semirings.sprecedes_1_2 |].
  apply orders.sprecedes_trans_r with x; [|intuition].
  now apply Qdlog2_spec.
Qed.

Lemma Qdlog2_mult_pow2 (x : Q) (n : Z) : 
  0 < x → Qdlog2 x + n = Qdlog2 (ring_mult x (2 ^ n)).
Proof.
  intros E. apply Qdlog2_unique.
   apply semirings.pos_mult_scompat; [easy | solve_propholds].
  split.
   rewrite int_pow_exp_plus by solve_propholds.
   apply (order_preserving (.* 2 ^ n)).
   now apply Qdlog2_spec.
  rewrite associativity.
  rewrite int_pow_exp_plus by solve_propholds.
  apply (strictly_order_preserving (.* 2 ^ n)).
  now apply Qdlog2_spec.
Qed.

Lemma Qdlog2_half (x : Q) : 
  0 < x → Qdlog2 x - 1 = Qdlog2 (ring_mult x (/2)).
Proof. intros E. now rewrite Qdlog2_mult_pow2. Qed.

Lemma Qdlog2_double (x : Q) : 
  0 < x → Qdlog2 x + 1 = Qdlog2 (ring_mult x 2).
Proof. intros E. now rewrite Qdlog2_mult_pow2. Qed.

Definition Qdlog4 (x : Q) : Z := Zdiv (Qdlog2 x) 2.

Instance: Proper (=) Qdlog4.
Proof. unfold Qdlog4. intros ? ? E. now rewrite E. Qed.

Lemma Qdlog4_spec (x : Q) : 
  0 < x → 4 ^ Qdlog4 x ≤ x ∧ x < 4 ^ (1 + Qdlog4 x).
Proof.
  intros E1. unfold Qdlog4.
  change (4:Q) with (2 ^ 2 : Q).
  rewrite <-2!int_pow_exp_mult.
  split.
   etransitivity.
    2: now apply Qdlog2_spec.
   apply int_pow_exp_precedes; [easy|].
   now apply Z.mul_div_le.
  eapply orders.sprecedes_trans_l.
   now apply Qdlog2_spec.
  apply int_pow_exp_precedes; [apply semirings.sprecedes_1_2 |].
  apply integers.precedes_sprecedes.
  rewrite commutativity.
  apply (strictly_order_preserving (+1)).
  change (1 + (Qdlog2 x / 2)%Z) with (1 + Zdiv (Qdlog2 x) 2)%Z.
  rewrite (Z.add_1_l (Zdiv (Qdlog2 x) 2)).
  apply stdlib_binary_integers.Zlt_coincides.
  now apply Z.mul_succ_div_gt.
Qed.
