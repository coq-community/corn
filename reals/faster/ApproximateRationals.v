Require
  implementations.stdlib_rationals.
Require Import 
  Program
  CornTac
  stdlib_omissions.Q Qmetric Qabs Qclasses QMinMax
  RSetoid CSetoids MetricMorphisms
  abstract_algebra
  orders.minmax.

Set Automatic Introduction.

(* We describe the approximate rationals as a ring that is dense in the rationals *)

(* Because [Q] is ``hard-wired'' nearly everywhere in CoRN, we take the easy
    way and require all operations to be sound with respect to [Q]. *)

Class AppMultInv AQ `{Equiv AQ} `{RingZero AQ} := app_mult_inv : {x | x ≠ 0} → Qpos → AQ.

Section approximate_rationals.
  Context `{e : Equiv AQ} {f : Inject AQ Q_as_MetricSpace} `{inverse : !AppInverse f}.

  Context {zero : RingZero AQ} {one : RingOne AQ} {plus : RingPlus AQ}
    {mult : RingMult AQ} {inv : GroupInv AQ} {mult_inv : AppMultInv AQ}.

  Class AppRationals : Prop := {
    aq_ring :> @Ring AQ e plus mult zero one inv ;
    aq_ring_morphism :> Ring_Morphism f ;
    aq_dense_embedding :> DenseEmbedding f ;
    aq_mult_inv : ∀ x ε, ball ε (f (app_mult_inv x ε)) (/ (f (`x))) ;
    aq_mult_inv_proper : Proper ((=) ==> (=) ==> (=)) app_mult_inv
  }.
End approximate_rationals.

Instance aq_precedes `{AppRationals AQ}: Order AQ | 1 := λ x y, 'x ≤ 'y.

Class AppRationalsAbs AQ `{AppRationals AQ} 
  := aq_abs_sig : ∀ x : AQ, { y : AQ | 'y = Qabs ('x) }.

Section approximate_rationals_more.
  Context `{@AppRationals AQ aq_eq f g aq_0 aq_1 aq_plus aq_mult aq_inv aq_minv}.

  Global Instance: Proper ((=) ==> (=) ==> iff) aq_precedes.
  Proof. intros ? ? E1 ? ? E2. unfold aq_precedes. rewrite E1 E2. reflexivity. Qed.
  
  Global Instance: PartialOrder aq_precedes.
  Proof with auto.
    unfold aq_precedes.
    repeat (split; try apply _).
      intros x. reflexivity.
     intros x y z ? ?. transitivity ('y)...
    intros x y ? ?. apply (injective f). apply (antisymmetry (≤))...
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
    
  Global Instance aq_preserves_le: OrderPreserving f.
  Proof. split; try apply _. intuition. Qed.

  Lemma aq_preserves_lt x y : x < y ↔ (f x < f y)%Q.
  Proof with auto.
    split.
     intros [E1 E2]. 
     destruct (proj1 (Qle_lteq _ _) E1)... destruct E2. apply (injective f)...
    intros E1; split.
     apply Qlt_le_weak...
    intros E2. apply (Qlt_not_eq (f x) (f y))...
    rewrite E2. reflexivity.
  Qed.

  Global Instance: NeZero (1:AQ).
  Proof. 
    intros E.
    destruct (ne_zero (1:Q)).
    rewrite <-(rings.preserves_1 (f:=f)).
    rewrite <-(rings.preserves_0 (f:=f)).
    rewrite E. reflexivity.
  Qed.

  Lemma aq_lt_mid (x y : Q) : (x < y)%Q → { z : AQ | (x < f z ∧ f z < y)%Q }.
  Proof with auto with qarith.
    intros E.
    destruct (Qpos_lt_plus E) as [γ Eγ].
    (* We need to pick a rational [x] such that [x < 1#2]. Since we do not
        use this lemma for computations yet, we just pick [1#3]. However,
        whenever we will it might be worth to reconsider. *)
    exists (app_inverse f ((1#2) * (x + y)) ((1#3) * γ)%Qpos)%Q.
    split.
     apply Qlt_le_trans with (x + (1#6) * γ)%Q.
      replace LHS with (x + 0)%Q by ring.
      apply Qplus_lt_r...
     replace LHS with ((1 # 2) * (x + y) - ((1 # 3) * γ)%Qpos)%Q...
      autorewrite with QposElim. rewrite Eγ.
      apply (in_Qball ((1#3)*γ)), dense_inverse.
     rewrite Eγ. QposRing.
    apply Qle_lt_trans with (y - (1#6) * γ)%Q.
     replace RHS with ((1 # 2) * (x + y) + ((1 # 3) * γ)%Qpos)%Q...
      autorewrite with QposElim. rewrite Eγ. 
      apply (in_Qball ((1#3)*γ)), dense_inverse.
     rewrite Eγ. QposRing.
    replace RHS with (y - 0)%Q by ring.
    apply Qplus_lt_r. 
    apply Qopp_Qlt_0_r...
  Defined.

  Lemma aq_preserves_min `{∀ x y : AQ, Decision (x ≤ y)} x y : f (min x y) = Qmin (f x) (f y).
  Proof.
    rewrite minmax.preserves_min.
    symmetry. apply Qmin_coincides.
  Qed.

  Lemma aq_preserves_max `{∀ x y : AQ, Decision (x ≤ y)} x y : f (max x y) = Qmax (f x) (f y).
  Proof. 
    rewrite minmax.preserves_max.
    symmetry. apply Qmax_coincides.
  Qed.

  Definition aq_abs `{!AppRationalsAbs AQ} := λ x, proj1_sig (aq_abs_sig x).

  Lemma aq_preserves_abs `{app_abs : !AppRationalsAbs AQ} x : f (aq_abs x) = Qabs (f x).
  Proof.
    unfold aq_abs, aq_abs_sig. 
    destruct app_abs. assumption.
  Qed.

  Definition AQposAsAQ: AQ₊ → AQ := @proj1_sig _ _.
  (* If we make this a coercion it will be gone after we close the section. Currently 
      there seems to be no proper way to handle this. See Coq bug #2455. *)

  Program Definition AQpos2Qpos (x : AQ₊) : Qpos := f (AQposAsAQ x).
  Next Obligation.
    destruct x as [x Ex]. simpl.
    pose proof (rings.preserves_0 (f:=f)) as E. rewrite <-E.
    apply aq_preserves_lt. assumption.
  Qed.  
End approximate_rationals_more.
