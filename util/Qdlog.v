(* Discrete logarithm with base 2 and 4 on [Q] *)
Require Import 
  Program ZArith QArith Qround stdlib_omissions.Q
  abstract_algebra additional_operations interfaces.orders
  int_pow orders.rationals stdlib_rationals positive_semiring_elements.

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
    apply (strictly_order_preserving_back (cast Z Q)).
    apply orders.lt_le_trans with (/x).
     apply dec_fields.flip_lt_dec_mult_inv_r; trivial.
     apply orders.lt_iff_le_ne. tauto.
    now apply Qle_ceiling.
   split.
    rewrite int_pow_opp. 
    apply dec_fields.flip_le_dec_mult_inv_l; trivial.
    transitivity ('Qceiling (/x)).
     now apply Qle_ceiling.
    change 2 with ('(2 : Z)). rewrite <-Qpower.Zpower_Qpower.
     apply (order_preserving _).
     now apply Z.log2_up_spec.
    now apply Z.log2_up_nonneg.
   ms_setoid_replace (1 - Z.log2_up (Qceiling (/x))) with (-Zpred (Z.log2_up (Qceiling (/x)))).
    rewrite int_pow_opp.
    apply dec_fields.flip_lt_dec_mult_inv_r.
     solve_propholds.
    apply orders.le_lt_trans with ('Zpred (Qceiling (/x))).
     change 2 with ('(2 : Z)). rewrite <-Qpower.Zpower_Qpower.
      apply (order_preserving _).
      now apply Z.lt_le_pred, Z.log2_up_spec.
     now apply Z.lt_le_pred, Z.log2_up_pos.
    rewrite <-Z.sub_1_r. 
    now apply Qceiling_lt.
   rewrite <-Z.sub_1_r.
   change (1 - Z.log2_up (Qceiling (/ x)) = -(Z.log2_up (Qceiling (/ x)) - 1)).
   now rewrite <-rings.opp_swap_l, commutativity.
  apply orders.le_flip in E2.
  split.
   transitivity ('Qfloor x).
    change 2 with ('(2 : Z)).
    rewrite <-Qpower.Zpower_Qpower.
     apply (order_preserving _).
     now apply Zlog2_spec, Qfloor_pos. 
    now apply Z.log2_nonneg.
   now apply Qfloor_le.
  apply orders.lt_le_trans with ('Zsucc (Qfloor x)).
   rewrite <-Z.add_1_r.
   now apply Qlt_floor.
  rewrite Z.add_1_l.
  change 2 with ('(2 : Z)).
  rewrite <-Qpower.Zpower_Qpower.
   apply (order_preserving _).
   now apply Zle_succ_l, Zlog2_spec, Qfloor_pos.
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

Lemma Qdlog2_0 (x : Q) :
  0 < x → Qdlog2 x = 0 → x < 2.
Proof.
  intros ? E.
  change (x < 2 ^ (1 + 0)). rewrite <-E.
  now apply Qdlog2_spec.
Qed.

Lemma Qpos_dlog2_spec (x : Q₊) : 
  '(2 ^ Qdlog2 ('x)) ≤ ('x : Q) ∧ 'x < '(2 ^ (1 + Qdlog2 ('x))).
Proof. unfold cast. simpl. split; apply Qdlog2_spec; now destruct x. Qed.

Lemma Qdlog2_unique (x : Q) (y : Z) : 
  0 < x → 2 ^ y ≤ x ∧ x < 2 ^ (1 + y) → y = Qdlog2 x.
Proof.
  intros.
  apply (antisymmetry (≤)).
   apply integers.le_iff_lt_plus_1.
   rewrite commutativity.
   apply int_pow_exp_lt_back with (2 : Q); [ apply semirings.lt_1_2 |].
   apply orders.le_lt_trans with x; [ intuition |].
   now apply Qdlog2_spec.
  apply integers.le_iff_lt_plus_1.
  rewrite commutativity.
  apply int_pow_exp_lt_back with (2 : Q); [ apply semirings.lt_1_2 |].
  apply orders.le_lt_trans with x; [|intuition].
  now apply Qdlog2_spec.
Qed.

Lemma Qdlog2_mult_pow2 (x : Q) (n : Z) : 
  0 < x → Qdlog2 x + n = Qdlog2 (ring_mult x (2 ^ n)).
Proof.
  intros E. apply Qdlog2_unique.
   apply pos_mult_compat; [easy | solve_propholds].
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

Lemma Qdlog2_preserving (x y : Q) :
  0 < x → x ≤ y → Qdlog2 x ≤ Qdlog2 y.
Proof.
  intros E1 E2.
  apply integers.le_iff_lt_plus_1. rewrite commutativity.
  apply int_pow_exp_lt_back with (2:Q); [ apply semirings.lt_1_2 |].
  apply orders.le_lt_trans with x; [now apply Qdlog2_spec | ].
  apply orders.le_lt_trans with y; [assumption |].
  apply Qdlog2_spec. 
  now apply orders.lt_le_trans with x.
Qed.

(* This function computes log n by repeatedly dividing by n. 
  Warning, it only works in case 1 ≤ x and 2 ≤ n. *)
Fixpoint Qdlog_bounded (b : nat) (n : Z) (x : Q) : Z := 
  match b with
  | O => 0
  | S c => if (decide_rel (<) x ('n:Q)) 
    then 0 
    else 1 + Qdlog_bounded c n (x / ('n:Q))
  end.

Definition Qdlog (n : Z) (x : Q) : Z := Qdlog_bounded (Zabs_nat (Qdlog2 x)) n x.

Lemma Qdlog_bounded_nonneg (b : nat) (n : Z) (x : Q) :
  0 ≤ Qdlog_bounded b n x.
Proof.
  revert x. induction b; simpl; [reflexivity |].
  intros. case (decide_rel _); intros; [reflexivity |].
  apply semirings.nonneg_plus_compat; [easy | apply IHb].
Qed.

Lemma Qdlog2_le1 (n : Z) (x : Q) : 
  2 ≤ n → x ≤ 1 → Qdlog n x = 0.
Proof.
  intros En Ex. unfold Qdlog.
  generalize (Zabs_nat (Qdlog2 x)). 
  intros b. induction b; simpl; [reflexivity |].
  case (decide_rel _); intros E; [reflexivity |].
  destruct E.
  apply orders.le_lt_trans with 1; try assumption.
  apply orders.lt_le_trans with 2.
   now apply semirings.lt_1_2.
  now apply (order_preserving (cast Z Q)) in En.
Qed.

Instance: Proper (=) Qdlog_bounded.
Proof.
  intros b1 b2 Eb n1 n2 En x1 x2 Ex.
  change (b1 ≡ b2) in Eb. change (n1 ≡ n2) in En. subst.
  revert x1 x2 Ex. induction b2; simpl; [reflexivity |].
  intros x1 x2 Ex.
  case (decide_rel _); case (decide_rel _); intros E1 E2.
     reflexivity.
    destruct E1. now rewrite <-Ex.
   destruct E2. now rewrite Ex.
  rewrite IHb2; [reflexivity| now rewrite Ex].
Qed.

Instance: Proper (=) Qdlog.
Proof. unfold Qdlog. intros ? ? E1 ? ? E2. now rewrite E1, E2. Qed.

Lemma Qdlog_spec_bounded (b : nat) (n : Z) (x : Q) : 
  2 ≤ n → Qdlog2 x ≤ ('b) → 1 ≤ x → 'n ^ Qdlog_bounded b n x ≤ x ∧ x < 'n ^ (1 + Qdlog_bounded b n x).
Proof.
  intros En Eb Ex.
  apply (order_preserving (cast Z Q)) in En.
  assert (PropHolds (0 < ('n : Q)))
    by (apply orders.lt_le_trans with 2; [solve_propholds | assumption]).
  revert x Eb Ex.
  induction b; simpl.
   intros x Eb Ex.
   split; [assumption|].
   apply orders.lt_le_trans with 2; try assumption.
   apply Qdlog2_0.
    apply orders.lt_le_trans with 1; [ solve_propholds | easy].
   apply (antisymmetry (≤)); try assumption.
   now apply Qdlog2_nonneg.
  intros x Eb Ex.
  case (decide_rel _); [intuition |]; intros E.
  apply orders.not_lt_le_flip in E.
  assert (x = 'n * (x / 'n)) as Ex2.
   rewrite (commutativity x), associativity.
   rewrite dec_mult_inverse, rings.mult_1_l; [reflexivity |].
   now apply orders.lt_ne_flip.
  rewrite peano_naturals.S_nat_plus_1, rings.preserves_plus, rings.preserves_1 in Eb.
  assert (1 ≤ x / 'n).
   apply (order_preserving_back (('n:Q) *.)).
   now rewrite <-Ex2, rings.mult_1_r.
  destruct IHb with (x / 'n) as [IHb1 IHb2]; trivial.
   transitivity (Qdlog2 (ring_mult x (/2))).
    apply Qdlog2_preserving.
     apply orders.lt_le_trans with 1; [solve_propholds | assumption].
    apply (maps.order_preserving_nonneg (.*.) x).
     now transitivity (1:Q).
    apply dec_fields.flip_le_dec_mult_inv; [solve_propholds | assumption].
   rewrite <-Qdlog2_half.
    now apply rings.flip_le_minus_l.
   now apply orders.lt_le_trans with 1; [solve_propholds | assumption].
  rewrite int_pow_S_nonneg by (now apply Qdlog_bounded_nonneg).
  rewrite int_pow_S_nonneg by (apply semirings.nonneg_plus_compat; [easy | now apply Qdlog_bounded_nonneg]).
  setoid_rewrite Ex2 at 2 3.
  split.
   now apply (order_preserving (('n:Q) *.)).
  now apply (strictly_order_preserving (('n:Q) *.)).
Qed.

Lemma Qdlog_spec (n : Z) (x : Q) : 
  2 ≤ n → 1 ≤ x → 'n ^ Qdlog n x ≤ x ∧ x < 'n ^ (1 + Qdlog n x).
Proof. 
  intros. apply Qdlog_spec_bounded; trivial.
  rewrite inj_Zabs_nat, Zabs_eq; [reflexivity |].
  now apply Qdlog2_nonneg.
Qed.

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
   apply int_pow_exp_le; [easy|].
   now apply Z.mul_div_le.
  eapply orders.lt_le_trans.
   now apply Qdlog2_spec.
  apply int_pow_exp_le; [apply semirings.le_1_2 |].
  apply integers.le_iff_lt_plus_1.
  rewrite commutativity.
  apply (strictly_order_preserving (+1)).
  change (1 + (Qdlog2 x / 2)%Z) with (1 + Zdiv (Qdlog2 x) 2)%Z.
  rewrite (Z.add_1_l (Zdiv (Qdlog2 x) 2)).
  now apply Z.mul_succ_div_gt.
Qed.
