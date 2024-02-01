Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require
  MathClasses.implementations.stdlib_rationals MathClasses.implementations.positive_semiring_elements.
Require Import 
  Coq.Program.Program
  CoRN.model.totalorder.QposMinMax
  MathClasses.misc.workaround_tactics
  CoRN.stdlib_omissions.Q CoRN.util.Qdlog CoRN.model.metric2.Qmetric Coq.QArith.Qabs CoRN.classes.Qclasses CoRN.model.totalorder.QMinMax
  CoRN.algebra.RSetoid CoRN.metric2.MetricMorphisms
  MathClasses.orders.minmax MathClasses.orders.dec_fields MathClasses.theory.abs MathClasses.theory.shiftl MathClasses.theory.int_pow.
Require Export
  MathClasses.interfaces.abstract_algebra MathClasses.interfaces.additional_operations MathClasses.interfaces.orders.

(* We describe the approximate rationals as a ring that is dense in the rationals *)

(* Because [Q] is ``hard-wired'' nearly everywhere in CoRN, we take the easy
    way and require all operations to be sound with respect to [Q]. *)
Class AppDiv AQ := app_div : AQ → AQ → Z → AQ.
Class AppApprox AQ := app_approx : AQ → Z → AQ.

Class AppRationals AQ {e plus mult zero one inv} `{Apart AQ} `{Le AQ} `{Lt AQ}
     {AQtoQ : Cast AQ Q_as_MetricSpace} 
    `{!AppInverse AQtoQ} {ZtoAQ : Cast Z AQ} `{!AppDiv AQ} `{!AppApprox AQ} 
    `{!Abs AQ} `{!Pow AQ N} `{!ShiftL AQ Z} 
    `{∀ x y : AQ, Decision (x = y)} `{∀ x y : AQ, Decision (x ≤ y)} : Prop := {
  aq_ring :: @Ring AQ e plus mult zero one inv ;
  aq_trivial_apart :: TrivialApart AQ ;
  aq_order_embed :: OrderEmbedding AQtoQ ;
  aq_strict_order_embed :: StrictOrderEmbedding AQtoQ ;
  aq_ring_morphism :: SemiRing_Morphism AQtoQ ;
  aq_dense_embedding :: DenseEmbedding AQtoQ ;
  aq_div : ∀ x y k, ball (2 ^ k) ('app_div x y k) ('x / 'y) ;
  aq_compress : ∀ x k, ball (2 ^ k) ('app_approx x k) ('x) ;
  aq_shift :: ShiftLSpec AQ Z (≪) ;
  aq_nat_pow :: NatPowSpec AQ N (^) ;
  aq_ints_mor :: SemiRing_Morphism ZtoAQ
}.

Lemma order_embedding_iff `{OrderEmbedding A B f} x y : 
  x ≤ y ↔ f x ≤ f y.
Proof. firstorder. Qed.


Lemma strict_order_embedding_iff `{StrictOrderEmbedding A B f} x y : 
  x < y ↔ f x < f y.
Proof. firstorder. Qed.

Section approximate_rationals_more.
  Context `{AppRationals AQ}.

  Lemma AQtoQ_ZtoAQ (x : Z) : cast AQ Q (cast Z AQ x) = cast Z Q x.
  Proof. now apply (integers.to_ring_twice _ _ _). Qed.

  Global Instance: Injective (cast AQ Q). 
  Proof. 
    destruct dense_injective.
    split. 2: apply _.
    intros. apply (injective x y).
    unfold equiv. simpl.
    rewrite H5. reflexivity.
  Qed.

  Global Instance: StrongSetoid AQ.
  Proof strong_setoids.dec_strong_setoid.

  Global Instance: StrongSetoid_Morphism (cast AQ Q).
  Proof strong_setoids.dec_strong_morphism (cast AQ Q).

  Global Instance: StrongInjective (cast AQ Q). 
  Proof strong_setoids.dec_strong_injective (cast AQ Q).

  Global Instance: Injective (cast Z AQ).
  Proof.
    split; try apply _.
    intros x y E.
    apply (injective (cast Z Q)).
    rewrite <-2!AQtoQ_ZtoAQ.
    now rewrite E.
  Qed.

  Global Instance: FullPseudoSemiRingOrder (_ : Le AQ) (_ : Lt AQ).
  Proof. 
    apply (projected_full_pseudo_ring_order (cast AQ Q)).
     apply order_embedding_iff.
    apply strict_order_embedding_iff.
  Qed.

  Lemma aq_opp : forall (x : AQ), '(-x) = -'x.
  Proof.
    intro x.
    apply (Qplus_inj_l _ _ ('x)).
    rewrite Qplus_opp_r.
    assert ('zero0 = 0%Q) by (apply rings.preserves_0).
    rewrite <- H5.
    destruct aq_ring_morphism.
    destruct semiringmor_plus_mor.
    destruct monmor_sgmor.
    rewrite <- preserves_sg_op.
    destruct sgmor_setmor.
    apply sm_proper.
    unfold equiv.
    destruct aq_ring, ring_group.
    destruct abgroup_group.
    apply negate_r.
  Qed.
    
  Lemma aq_shift_correct (x : AQ) (k : Z) :  '(x ≪ k) = 'x * 2 ^ k.
  Proof. rewrite preserves_shiftl. apply shiftl_int_pow. Qed.

  Lemma aq_shift_1_correct (k : Z) :  '((1:AQ) ≪ k) = 2 ^ k.
  Proof. now rewrite aq_shift_correct, rings.preserves_1, rings.mult_1_l. Qed.

  Lemma aq_shift_opp_1 (x : AQ) : '(x ≪ (-1 : Z)) = 'x / 2.
  Proof. now rewrite aq_shift_correct. Qed.

  Lemma aq_shift_opp_2 (x : AQ) : '(x ≪ (-2 : Z)) = 'x / 4.
  Proof. now rewrite aq_shift_correct. Qed.

  Lemma aq_div_dlog2 (x y : AQ) (ε : Q₊) : 
    ball (proj1_sig ε) ('app_div x y (Qdlog2 ('ε))) ('x / 'y).
  Proof.
    eapply ball_weak_le.
     now apply Qpos_dlog2_spec.
    now apply aq_div.
  Qed.

  Lemma aq_approx_dlog2 (x : AQ) (ε : Q₊) : 
    ball (proj1_sig ε) ('app_approx x (Qdlog2 ('ε))) ('x).
  Proof.
    eapply ball_weak_le.
     now apply Qpos_dlog2_spec.
    now apply aq_compress.
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

  Global Instance: IntegralDomain AQ.
  Proof.
    split; try apply _.
     intros E.
     destruct (rings.is_ne_0 (1%mc:Q)).
     rewrite <-(rings.preserves_1 (f:=cast AQ Q)).
     rewrite <-(rings.preserves_0 (f:=cast AQ Q)).
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
    destruct (Qpos_sub _ _ E) as [γ Eγ].
    (* We need to pick a rational [x] such that [x < 1#2]. Since we do not
        use this lemma for computations yet, we just pick [1#3]. However,
        whenever we will it might be worth to reconsider. *)
    exists (app_inverse (cast AQ Q) ((1#2) * (x + y)) ((1#3) * γ)%Qpos)%Q.
    split.
     apply Qlt_le_trans with (x + (1#6) * proj1_sig γ)%Q.
      rewrite <-(rings.plus_0_r x) at 1.
      apply Qplus_lt_r...
      assert (Qeq (x + (1 # 6) * ` γ)
                  ((1 # 2) * (x + y) - proj1_sig ((1 # 3) * γ)%Qpos)%Q).
      { rewrite Eγ. simpl. ring. }
      rewrite H5. clear H5.
     simpl.
      apply (in_Qball (proj1_sig ((1#3)*γ)%Qpos)), ball_sym, dense_inverse.
    apply Qle_lt_trans with (y - (1#6) * proj1_sig γ)%Q.
    assert (Qeq (y - (1 # 6) * ` γ)
                ((1 # 2) * (x + y) + proj1_sig ((1 # 3) * γ)%Qpos)).
    { rewrite Eγ. simpl. ring. }
    rewrite H5. clear H5. simpl.
      apply (in_Qball (proj1_sig ((1#3)*γ)%Qpos)), ball_sym, dense_inverse.
      apply (Qlt_le_trans _ (y-0)).
    apply Qplus_lt_r.
    apply Qopp_Qlt_0_r...
    unfold Qminus. rewrite Qplus_0_r. apply Qle_refl.
  Defined.

  Instance: MeetSemiLattice_Morphism (cast AQ Q).
  Proof.
    split; try apply _; apply lattices.order_preserving_meet_sl_mor.
  Qed.

  Instance: JoinSemiLattice_Morphism (cast AQ Q).
  Proof.
    split; try apply _; apply lattices.order_preserving_join_sl_mor.
  Qed.

  Lemma aq_preserves_min x y : '(x ⊓ y) = Qmin ('x) ('y).
  Proof.
    rewrite lattices.preserves_meet; symmetry; apply Qmin_coincides.
  Qed.

  Lemma aq_preserves_max x y : '(x ⊔ y) = Qmax ('x) ('y).
  Proof. 
    rewrite lattices.preserves_join; symmetry; apply Qmax_coincides.
  Qed.

  Global Program Instance AQposAsQ: Cast (AQ₊) Q := cast AQ Q ∘ cast (AQ₊) AQ.

  Global Program Instance AQposAsQpos: Cast (AQ₊) (Q₊) := λ x, ('x : Q).
  Next Obligation.
    destruct x as [x Ex]. simpl.
    posed_rewrite <-(rings.preserves_0 (f:=cast AQ Q)).
    now apply (strictly_order_preserving (cast AQ Q)).
  Qed.

  Lemma AQposAsQpos_preserves_1 : cast (AQ₊) (Q₊) 1 = 1.
  Proof. change (cast AQ Q 1 = 1). apply rings.preserves_1. Qed.

  Lemma AQposAsQpos_preserves_4 : cast (AQ₊) (Q₊) 4 = 4. 
  Proof. change (cast AQ Q 4 = 4). apply rings.preserves_4. Qed.
End approximate_rationals_more.
