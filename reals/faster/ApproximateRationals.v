Require Import 
  Ring Relation_Definitions Unicode.Utf8
  CornTac
  stdlib_omissions.Q Qmetric Qabs QMinMax 
  RSetoid CSetoids MetricMorphisms.

Generalizable All Variables.
Set Automatic Introduction.

(* We describe the approximate rationals as a structure that is dense in the rationals *)

(* Because [Q] is ``hard-wired'' nearly everywhere in CoRN, we take the easy
    way and require all operations to be sound with respect to [Q]. *)

Section approximate_rationals.
  Context `{AQ : Setoid} {f : AQ → Q_as_MetricSpace} `{inverse : !AppInverse f}.

  Context {zero : st_car AQ} {one : st_car AQ} {plus : st_car AQ → st_car AQ → st_car AQ}
    {mult : st_car AQ → st_car AQ → st_car AQ} {opp : st_car AQ → st_car AQ}.

  Class AppRationals : Prop := {
    aq_preserves_0 : f zero == 0 ;
    aq_preserves_1 : f one == 1 ;
    aq_preserves_plus x y : f (plus x y) == f x + f y ;
    aq_preserves_mult x y : f (mult x y) == f x * f y ;
    aq_preserves_opp x : f (opp x) == - f x ;
    aq_dense_embedding :> DenseEmbedding f
  }.
End approximate_rationals.

Implicit Arguments AppRationals [[inverse]].

Definition aq_le `{AppRationals AQ f} : relation AQ := λ x y, (f x <= f y)%Q.
Definition aq_lt `{AppRationals AQ f} : relation AQ := λ x y, (f x < f y)%Q.
Definition AQpos `{AppRationals AQ f aq_0} := sig (aq_lt aq_0).

Section approximate_rationals_more.
  Context `{@AppRationals AQ f g aq_0 aq_1 aq_plus aq_mult aq_opp}.
  
  Lemma aq_preserves_le x y : aq_le x y ↔ f x <= f y.
  Proof. intuition. Qed.
  
  Lemma aq_preserves_lt x y : aq_lt x y ↔ f x < f y.
  Proof. intuition. Qed.

  Lemma aq_lt_mid (x y : Q) : x < y → { z : AQ | x < f z ∧ f z < y }.
  Proof with auto with qarith.
    intros E.
    destruct (Qpos_lt_plus E) as [γ Eγ].
    (* We need to pick a rational [x] such that [x < 1#2]. Since we do not
        use this lemma for computations yet, we have just picked [1#3]. However,
        whenever we will it might be worth to reconsider. *)
    exists (app_inverse f ((1#2) * (x + y))%Q ((1#3) * γ)%Qpos).
    unfold app_inverse, app_inverse_sig. destruct g as [z Ez]. simpl.
    apply in_Qball in Ez. destruct Ez as [Ez1 Ez2]. 
    split.
     apply Qlt_le_trans with (x + (1#6) * γ).
      replace LHS with (x + 0) by ring.
      apply Qplus_lt_r...
     replace LHS with ((1 # 2) * (x + y) - ((1 # 3) * γ)%Qpos)...
     autorewrite with QposElim. rewrite Eγ. ring.
    apply Qle_lt_trans with (y - (1#6) * γ).
     replace RHS with ((1 # 2) * (x + y) + ((1 # 3) * γ)%Qpos)...
     autorewrite with QposElim. rewrite Eγ. ring.
    replace RHS with (y - 0) by ring.
    apply Qplus_lt_r. 
    apply Qopp_Qlt_0_r...
  Defined.

  Class AppRationalsMin := aq_min_sig : ∀ x y : AQ, { z : AQ | f z == Qmin (f x) (f y) }.
  Definition aq_min `{AppRationalsMin} := λ x y, proj1_sig (aq_min_sig x y).

  Lemma aq_preserves_min `{app_min : AppRationalsMin} x y : f (aq_min x y) == Qmin (f x) (f y).
  Proof. 
    unfold aq_min, aq_min_sig. 
    destruct app_min. assumption.
  Qed.

  Class AppRationalsMax := aq_max_sig : ∀ x y : AQ, { z : AQ | f z == Qmax (f x) (f y) }.
  Definition aq_max `{AppRationalsMax} := λ x y, proj1_sig (aq_max_sig x y).

  Lemma aq_preserves_max `{app_max : AppRationalsMax} x y : f (aq_max x y) == Qmax (f x) (f y).
  Proof. 
    unfold aq_max, aq_max_sig. 
    destruct app_max. assumption.
  Qed.

  Class AppRationalsAbs := aq_abs_sig : ∀ x : AQ, { y : AQ | f y == Qabs (f x) }.
  Definition aq_abs `{AppRationalsAbs} := λ x, proj1_sig (aq_abs_sig x).

  Lemma aq_preserves_abs `{app_abs : AppRationalsAbs} x : f (aq_abs x) == Qabs (f x).
  Proof.
    unfold aq_abs, aq_abs_sig. 
    destruct app_abs. assumption.
  Qed.

  Class AppRationalsMultInv := aq_mult_inv_sig : ∀ x ε, { y | Qball ε (f y) (/(f x)) }.
  Definition aq_mult_inv `{AppRationalsMultInv} := λ x ε, proj1_sig (aq_mult_inv_sig x ε).

  Lemma aq_mult_inv_spec `{app_inv : AppRationalsMultInv} x ε : 
    Qball ε (f (aq_mult_inv x ε)) (/(f x)).
  Proof.
    unfold aq_mult_inv, aq_mult_inv_sig.
    destruct app_inv. assumption.
  Qed.
  
  Definition AQposAsAQ: AQpos → AQ := @proj1_sig _ _.
  (* If we make this a coercion it will be gone after we close the section. Currently 
      there seems to be no proper way to handle this. See Coq bug #2455. *)

  Program Definition AQpos2Qpos (x : AQpos) : Qpos := f (AQposAsAQ x).
  Next Obligation.
    destruct x as [x Ex]. simpl.
    unfold aq_lt in Ex. erewrite aq_preserves_0 in Ex. assumption.
  Qed.
 
  Hint Rewrite aq_preserves_0 : aq_preservation.
  Hint Rewrite aq_preserves_1 : aq_preservation.
  Hint Rewrite aq_preserves_plus : aq_preservation.
  Hint Rewrite aq_preserves_mult : aq_preservation.
  Hint Rewrite aq_preserves_opp : aq_preservation.

  Lemma aq_ring_theory : @ring_theory AQ aq_0 aq_1 aq_plus aq_mult (λ x y, aq_plus x (aq_opp y)) aq_opp (@st_eq _).
  Proof. 
    split; repeat intro; apply (injective f); autorewrite with aq_preservation; simpl; ring.
  Qed.

End approximate_rationals_more.

Implicit Arguments AppRationalsMax [].
Implicit Arguments AppRationalsMin [].
Implicit Arguments AppRationalsAbs [].
Implicit Arguments AppRationalsMultInv [].
