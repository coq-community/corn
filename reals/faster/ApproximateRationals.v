Require
  implementations.stdlib_rationals.
Require Import 
  Program
  CornTac
  stdlib_omissions.Q Qmetric Qabs Qclasses QMinMax
  RSetoid CSetoids MetricMorphisms
  abstract_algebra
  orders.minmax orders.fields.

Set Automatic Introduction.

(* We describe the approximate rationals as a ring that is dense in the rationals *)

(* Because [Q] is ``hard-wired'' nearly everywhere in CoRN, we take the easy
    way and require all operations to be sound with respect to [Q]. *)

Class AppFieldDiv AQ := app_field_div : AQ → AQ → Z → AQ.
Class AppFieldShift AQ := app_field_shift : AQ → Z → AQ.

Section approximate_rationals.
  Context `{e : Equiv AQ} {f : Inject AQ Q_as_MetricSpace} `{inverse : !AppInverse f}.

  Context {zero : RingZero AQ} {one : RingOne AQ} {plus : RingPlus AQ}
    {mult : RingMult AQ} {inv : GroupInv AQ} {div : AppFieldDiv AQ} {shift : AppFieldShift AQ}.

  Class AppRationals : Prop := {
    aq_ring :> @Ring AQ e plus mult zero one inv ;
    aq_ring_morphism :> Ring_Morphism f ;
    aq_dense_embedding :> DenseEmbedding f ;
    aq_div : ∀ x y k, ball (Qpos_inv (2 ^ k)) ('app_field_div x y k) ('x / 'y) ;
    aq_div_proper :> Proper ((=) ==> (=) ==> (=) ==> (=)) app_field_div ;
    aq_shift : ∀ x k, 'app_field_shift x k = ('x * 2 ^ k)%Q ;
    aq_shift_proper :> Proper ((=) ==> (=) ==> (=)) app_field_shift
  }.
End approximate_rationals.

Definition eps2pow (ε : Qpos) : Z := 
  match (QposAsQ ε) with
  | d # n => Z.log2_up (n / d + 1)%Z
  end.

Lemma eps2pow_nonneg (q : Qpos) : 0 ≤ eps2pow q.
Proof. 
  destruct q as [[? ?] ?]. 
  unfold eps2pow. simpl. 
  apply Z.log2_up_nonneg. 
Qed.

Lemma eps2pow_correct (q : Qpos) : QposAsQ (Qpos_inv (2 ^ (eps2pow q))) ≤ QposAsQ q.
Proof with auto with zarith qarith.
  destruct q as [[n d] pos].
  unfold eps2pow. simpl.
  pose proof fields.flip_dec_mult_inv_l as P. apply P; clear P.
   apply Qlt_coincides...
  rewrite Qmake_Qdiv. unfold Qdiv.
  pose proof fields.dec_mult_inv_swap_r as P. rewrite <-P; clear P.
  transitivity (d / n + 1)%Z.
   rewrite Zdiv_Qdiv. rewrite commutativity.
   apply orders.sprecedes_weaken, Qlt_coincides, Qround.Qlt_floor.
  replace (1 + 1)%Q with (inject_Z 2) by reflexivity.
  rewrite <-Qpower.Zpower_Qpower.
   rewrite <-Zle_Qle.
   destruct (decide (d / n = 0))%Z as [E|E].
    rewrite E. reflexivity.
   apply Z.log2_up_spec.
   apply signed_binary_positive_integers.Zlt_coincides.
   apply semirings.pos_plus_compat_l; try reflexivity.
   split.
    apply Z_div_pos...
    unfold Qlt in pos. simpl in pos. ring_simplify in pos...
   apply not_symmetry...
  apply Z.log2_up_nonneg. 
Qed.

Instance aq_precedes `{AppRationals AQ}: Order AQ | 1 := λ x y, 'x ≤ 'y. 
(* huh? *) Defined.

Class AppRationalsAbs AQ `{AppRationals AQ} 
  := aq_abs_sig : ∀ x : AQ, { y : AQ | 'y = Qabs ('x) }.

Section approximate_rationals_more.
  Context `{AppRationals AQ}.

  Lemma aq_div_eps2pow (x y : AQ) (ε : Qpos) : 
    ball ε ('app_field_div x y (eps2pow ε)) ('x / 'y).
  Proof.
    eapply ball_weak_le.
     apply eps2pow_correct.
    apply aq_div.
  Qed.

  Global Instance: Proper ((=) ==> (=) ==> iff) aq_precedes.
  Proof. intros ? ? E1 ? ? E2. unfold aq_precedes. rewrite E1 E2. reflexivity. Qed.
  
  Global Instance: PartialOrder aq_precedes.
  Proof with auto.
    unfold aq_precedes.
    repeat (split; try apply _).
      intros x. reflexivity.
     intros x y z ? ?. transitivity ('y)...
    intros x y ? ?. apply (injective (inject : AQ → Q_as_MetricSpace)). 
    apply (antisymmetry (≤))...
  Qed.

  Global Instance: TotalOrder aq_precedes.
  Proof. intros x y. destruct (total_order ('x) ('y)); intuition. Qed.

  Global Instance: RingOrder aq_precedes.
  Proof with auto.
    repeat (split; try apply _); unfold precedes, aq_precedes.
     intros x y ?. 
     do 2 rewrite rings.preserves_plus.
     apply ringorder_plus...
    intros x E1 y E2. 
    rewrite rings.preserves_mult. rewrite rings.preserves_0 in E1, E2 |- *; intros.
    apply ringorder_mult...
  Qed.

  Global Instance aq_preserves_le: OrderPreserving (inject : AQ → Q_as_MetricSpace).
  Proof. split; try apply _. intuition. Qed.

  Lemma aq_preserves_lt x y : x < y ↔ ('x < 'y)%Q.
  Proof with auto.
    split.
     intros [E1 E2]. 
     destruct (proj1 (Qle_lteq _ _) E1)... destruct E2. 
     apply (injective (inject : AQ → Q_as_MetricSpace))...
    intros E1; split.
     apply Qlt_le_weak...
    intros E2. apply (Qlt_not_eq ('x) ('y))...
    rewrite E2. reflexivity.
  Qed.

  Global Instance: NeZero (1:AQ).
  Proof. 
    intros E.
    destruct (ne_zero (1:Q)).
    rewrite <-(rings.preserves_1 (f:=inject : AQ → Q_as_MetricSpace)).
    rewrite <-(rings.preserves_0 (f:=inject : AQ → Q_as_MetricSpace)).
    rewrite E. reflexivity.
  Qed.

  Lemma aq_lt_mid (x y : Q) : (x < y)%Q → { z : AQ | (x < 'z ∧ 'z < y)%Q }.
  Proof with auto with qarith.
    intros E.
    destruct (Qpos_lt_plus E) as [γ Eγ].
    (* We need to pick a rational [x] such that [x < 1#2]. Since we do not
        use this lemma for computations yet, we just pick [1#3]. However,
        whenever we will it might be worth to reconsider. *)
    exists (app_inverse inject ((1#2) * (x + y)) ((1#3) * γ)%Qpos)%Q.
    split.
     apply Qlt_le_trans with (x + (1#6) * γ)%Q.
      replace LHS with (x + 0)%Q by ring.
      apply Qplus_lt_r...
     replace LHS with ((1 # 2) * (x + y) - ((1 # 3) * γ)%Qpos)%Q...
      autorewrite with QposElim. unfold inject. 
      apply (in_Qball ((1#3)*γ)), dense_inverse.
     rewrite Eγ. QposRing.
    apply Qle_lt_trans with (y - (1#6) * γ)%Q.
     replace RHS with ((1 # 2) * (x + y) + ((1 # 3) * γ)%Qpos)%Q...
      autorewrite with QposElim. 
      apply (in_Qball ((1#3)*γ)), dense_inverse.
     rewrite Eγ. QposRing.
    replace RHS with (y - 0)%Q by ring.
    apply Qplus_lt_r. 
    apply Qopp_Qlt_0_r...
  Defined.

  Lemma aq_preserves_min `{∀ x y : AQ, Decision (x ≤ y)} x y : 'min x y = Qmin ('x) ('y).
  Proof.
    rewrite minmax.preserves_min.
    symmetry. apply Qmin_coincides.
  Qed.

  Lemma aq_preserves_max `{∀ x y : AQ, Decision (x ≤ y)} x y : 'max x y = Qmax ('x) ('y).
  Proof. 
    rewrite minmax.preserves_max.
    symmetry. apply Qmax_coincides.
  Qed.

  Definition aq_abs `{!AppRationalsAbs AQ} := λ x, proj1_sig (aq_abs_sig x).

  Lemma aq_preserves_abs `{app_abs : !AppRationalsAbs AQ} x : '(aq_abs x) = Qabs ('x).
  Proof.
    unfold aq_abs, aq_abs_sig. 
    destruct app_abs. assumption.
  Qed.

  Definition AQposAsAQ: AQ₊ → AQ := @proj1_sig _ _.
  (* If we make this a coercion it will be gone after we close the section. Currently 
      there seems to be no proper way to handle this. See Coq bug #2455. *)

  Program Definition AQpos2Qpos (x : AQ₊) : Qpos := '(AQposAsAQ x) : Q.
  Next Obligation.
    destruct x as [x Ex]. simpl.
    pose proof (rings.preserves_0 (f:=inject : AQ → Q_as_MetricSpace)) as E. rewrite <-E.
    apply aq_preserves_lt. assumption.
  Qed.  
End approximate_rationals_more.
