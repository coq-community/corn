Require
  implementations.stdlib_rationals positive_semiring_elements.
Require Import 
  Program
  CornTac workaround_tactics
  stdlib_omissions.Q Qdlog2 Qmetric Qabs Qclasses QMinMax
  RSetoid CSetoids MetricMorphisms
  orders.minmax orders.fields theory.abs theory.int_pow.
Require Export
  abstract_algebra interfaces.additional_operations.

(* We describe the approximate rationals as a ring that is dense in the rationals *)

(* Because [Q] is ``hard-wired'' nearly everywhere in CoRN, we take the easy
    way and require all operations to be sound with respect to [Q]. *)
Class AppDiv AQ := app_div : AQ → AQ → Z → AQ.
Class AppCompress AQ := app_compress : AQ → Z → AQ.

Class AppRationals AQ {e plus mult zero one inv} `{!Order AQ} {AQtoQ : Coerce AQ Q_as_MetricSpace} 
    `{!AppInverse AQtoQ} {ZtoAQ : Coerce Z AQ} `{!AppDiv AQ} `{!AppCompress AQ} 
    `{!Abs AQ} `{!Pow AQ N} `{!ShiftL AQ Z} 
    `{∀ x y : AQ, Decision (x = y)} `{∀ x y : AQ, Decision (x ≤ y)} : Prop := {
  aq_ring :> @Ring AQ e plus mult zero one inv ;
  aq_order_embed :> OrderEmbedding AQtoQ ;
  aq_ring_morphism :> SemiRing_Morphism AQtoQ ;
  aq_dense_embedding :> DenseEmbedding AQtoQ ;
  aq_div : ∀ x y k, ball (2 ^ k) ('app_div x y k) ('x / 'y) ;
  aq_compress : ∀ x k, ball (2 ^ k) ('app_compress x k) ('x) ;
  aq_shift :> ShiftLSpec AQ Z (≪) ;
  aq_nat_pow :> NatPowSpec AQ N (^) ;
  aq_ints_mor :> SemiRing_Morphism ZtoAQ
}.

Lemma Qpos_dlog2_spec (x : Qpos) : 
  QposAsQ (2 ^ Qdlog2 x) ≤ QposAsQ x ∧ QposAsQ x < QposAsQ (2 ^ Zsucc (Qdlog2 x)).
Proof.
  simpl. split.
   apply Qdlog2_spec. auto. 
  apply stdlib_rationals.Qlt_coincides.
  apply Qdlog2_spec. auto.
Qed.

(* The proof of this lemma is horrifying. Also, it doesn't belong here but in [Qdlog2.v].
    However, proving it requires [int_pow_exp_sprecedes_back] for which no variant
    exists in the standard library. *)
Lemma Qdlog2_half (x : Qpos) : 
  Qdlog2 x - 1 = Qdlog2 ((1#2) * x).
Proof with auto.
  setoid_rewrite commutativity at 2.
  change (Qdlog2 x - 1 = Qdlog2 (x / 2)).
  pose proof semirings.sprecedes_1_2.
  pose proof semirings.precedes_1_2.
  pose proof (rings.ne_0 (2:Q)).
  assert (PropHolds (0 ≤ /2)). apply nonneg_dec_mult_inv_compat...
    assert (PropHolds (0 < /2)). apply pos_dec_mult_inv_compat, semirings.sprecedes_0_2.
  assert (0 < x / 2)%Q.
   apply stdlib_rationals.Qlt_coincides.
   apply_simplified (semirings.pos_mult_scompat (R:=Q))...
    apply stdlib_rationals.Qlt_coincides...
  apply (antisymmetry (≤)).
   apply integers.precedes_sprecedes.
   apply int_pow_exp_sprecedes_back with 2...
   rewrite int_pow_exp_plus... rewrite int_pow_opp, int_pow_1.
   apply sprecedes_trans_r with ((x : Q) / 2).
    apply_simplified (order_preserving (.* / 2)).
    apply Qdlog2_spec...
   setoid_rewrite Z.add_1_r.
   apply stdlib_rationals.Qlt_coincides.
   apply Qdlog2_spec...
  apply integers.precedes_sprecedes.
  apply int_pow_exp_sprecedes_back with 2...
  apply sprecedes_trans_r with ((x : Q) / 2).
   apply Qdlog2_spec...
  rewrite <-associativity. rewrite (commutativity (-1) 1), associativity.
  rewrite int_pow_exp_plus... rewrite int_pow_opp, int_pow_1.
  apply_simplified (strictly_order_preserving (.* / 2)).
  apply stdlib_rationals.Qlt_coincides.
  apply Qdlog2_spec...
Qed.

Section approximate_rationals_more.
  Context `{AppRationals AQ}.

  Lemma AQtoQ_ZtoAQ x : ' (' x) = inject_Z x.
  Proof.
    pose proof (integers.to_ring_unique_alt ((coerce : AQ → Q) ∘ (coerce : Z → AQ)) inject_Z) as P.
    apply P.
  Qed.

  Global Instance: Injective (coerce : AQ → Q). 
  Proof. change (Injective (coerce : AQ → Q_as_MetricSpace)). apply _. Qed.

  Global Instance: StrictlyOrderPreserving (coerce : AQ → Q).
  Proof. apply _. Qed. 

  Global Instance: Injective (coerce : Z → AQ).
  Proof.
    split; try apply _.
    intros x y E.
    apply (injective inject_Z).
    rewrite <-2!AQtoQ_ZtoAQ.
    now rewrite E.
  Qed.

  Global Instance: RingOrder (_ : Order AQ).
  Proof rings.embed_ringorder (coerce : AQ → Q).

  Global Instance: TotalOrder (_ : Order AQ).
  Proof maps.embed_totalorder (coerce : AQ → Q).

  Lemma aq_preserves_lt x y : x < y ↔ ('x < 'y)%Q.
  Proof with auto.
    split; intros E.
     apply Qlt_coincides. 
     apply (strictly_order_preserving _)...
    apply (strictly_order_preserving_back coerce).
    apply Qlt_coincides...
  Qed.

  Lemma aq_shift_correct (x : AQ) (k : Z) :  '(x ≪ k) = 'x * 2 ^ k.
  Proof.
    rewrite shiftl.preserves_shiftl_int.
    apply shiftl.shiftl_int_pow.
  Qed.

  Lemma aq_div_Qdlog2 (x y : AQ) (ε : Qpos) : 
    ball ε ('app_div x y (Qdlog2 ε)) ('x / 'y).
  Proof.
    eapply ball_weak_le.
     apply Qpos_dlog2_spec.
    apply aq_div.
  Qed.

  Lemma aq_compress_Qdlog2 (x : AQ) (ε : Qpos) : 
    ball ε ('app_compress x (Qdlog2 ε)) ('x).
  Proof.
    eapply ball_weak_le.
     apply Qpos_dlog2_spec.
    apply aq_compress.
  Qed.

  Definition app_div_above (x y : AQ) (k : Z) : AQ := app_div x y k + 1 ≪ k.
  
  Lemma aq_div_above (x y : AQ) (k : Z) : ('x / 'y : Q) ≤ 'app_div_above x y k.
  Proof.
    unfold app_div_above.
    pose proof (aq_div x y k) as P.
    apply in_Qball in P. destruct P as [_ P]. 
    rewrite rings.preserves_plus.
    rewrite aq_shift_correct.
    now rewrite rings.preserves_1, left_identity.
  Qed.

  Lemma Zshift_opp_1 (x : AQ) : '(x ≪ (-1 : Z)) = 'x / 2.
  Proof. now rewrite aq_shift_correct. Qed.

  Lemma Zshift_opp_2 (x : AQ) : '(x ≪ (-2 : Z)) = 'x / 4.
  Proof. now rewrite aq_shift_correct. Qed.

  Global Instance: IntegralDomain AQ.
  Proof.
    split; try apply _.
     intros E.
     destruct (rings.ne_0 (1:Q)).
     rewrite <-(rings.preserves_1 (f:=coerce : AQ → Q)).
     rewrite <-(rings.preserves_0 (f:=coerce : AQ → Q)).
     now rewrite E.
    intros x [? [y [? E]]].
    destruct (no_zero_divisors ('x : Q)). split.
     now apply rings.injective_ne_0.
    exists ('y : Q). split.
     now apply rings.injective_ne_0.
    rewrite <-rings.preserves_mult, E.
    apply rings.preserves_0.
  Qed.

  Lemma aq_lt_mid (x y : Q) : (x < y)%Q → { z : AQ | (x < 'z ∧ 'z < y)%Q }.
  Proof with auto with qarith.
    intros E.
    destruct (Qpos_lt_plus E) as [γ Eγ].
    (* We need to pick a rational [x] such that [x < 1#2]. Since we do not
        use this lemma for computations yet, we just pick [1#3]. However,
        whenever we will it might be worth to reconsider. *)
    exists (app_inverse coerce ((1#2) * (x + y)) ((1#3) * γ)%Qpos)%Q.
    split.
     apply Qlt_le_trans with (x + (1#6) * γ)%Q.
      rewrite <-(rings.plus_0_r x) at 1.
      apply Qplus_lt_r...
     replace LHS with ((1 # 2) * (x + y) - ((1 # 3) * γ)%Qpos)%Q...
      autorewrite with QposElim.
      apply (in_Qball ((1#3)*γ)), ball_sym, dense_inverse.
     rewrite Eγ. simpl. unfold Q_eq. ring.
    apply Qle_lt_trans with (y - (1#6) * γ)%Q.
     replace RHS with ((1 # 2) * (x + y) + ((1 # 3) * γ)%Qpos)%Q...
      autorewrite with QposElim. 
      apply (in_Qball ((1#3)*γ)), ball_sym, dense_inverse.
     rewrite Eγ. simpl. unfold Q_eq. ring.
    setoid_replace y with (y - 0)%Q at 2 by (unfold Q_eq; ring).
    apply Qplus_lt_r. 
    apply Qopp_Qlt_0_r...
  Defined.

  Definition AQball_bool (k : Z) (x y : AQ) := bool_decide_rel (≤) (abs (x - y)) (1 ≪ k).

  Lemma AQball_bool_true (k : Z) (x y : AQ) : 
    AQball_bool k x y ≡ true ↔ ball (2 ^ k) ('x) ('y).
  Proof.
    unfold AQball_bool. rewrite bool_decide_rel_true. rewrite ->Qball_Qabs.
    transitivity ('abs (x - y) ≤ ('(1 ≪ k) : Q)).
     split; intros.
      now apply (order_preserving _).
     now apply (order_preserving_back coerce).
    rewrite abs.preserves_abs, rings.preserves_minus.
    now rewrite aq_shift_correct, rings.preserves_1, left_identity.
  Qed.

  Lemma AQball_bool_true_eps (ε : Qpos) (x y : AQ) : 
    AQball_bool (Qdlog2 ε) x y ≡ true → ball ε ('x) ('y).
  Proof with auto.
    intros E.
    apply AQball_bool_true in E.
    apply Qball_Qabs in E. apply Qball_Qabs.
    transitivity (2 ^ (Qdlog2 ε) : Q)...
    apply (Qpos_dlog2_spec ε).
  Qed.

  Lemma aq_preserves_min x y : 'min x y = Qmin ('x) ('y).
  Proof.
    rewrite minmax.preserves_min.
    symmetry. apply Qmin_coincides.
  Qed.

  Lemma aq_preserves_max x y : 'max x y = Qmax ('x) ('y).
  Proof. 
    rewrite minmax.preserves_max.
    symmetry. apply Qmax_coincides.
  Qed.

  Global Program Instance AQposAsQpos: Coerce (AQ₊) Qpos := λ x, '('x : AQ) : Q.
  Next Obligation.
    destruct x as [x Ex]. simpl.
    posed_rewrite <-(rings.preserves_0 (f:=coerce : AQ → Q)).
    now apply aq_preserves_lt.
  Qed.

  Lemma AQposAsQpos_preserves_1 : AQposAsQpos 1 = 1.
  Proof.
    do 3 red. simpl.
    now posed_rewrite (rings.preserves_1 (f:=coerce : AQ → Q)).
  Qed.
End approximate_rationals_more.
