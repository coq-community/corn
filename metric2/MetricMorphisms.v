Require Import CoRN.metric2.Metric.
Require 
  MathClasses.theory.jections.
Require Import 
  CoRN.model.totalorder.QposMinMax
  Coq.Setoids.Setoid 
  CoRN.stdlib_omissions.Q CoRN.model.totalorder.QMinMax
  CoRN.metric2.Complete CoRN.metric2.Prelength
  MathClasses.interfaces.abstract_algebra.

Local Open Scope uc_scope.

(* Given an embedding of a setoid [X] into a metric space [Y] then [X] is also a 
   metric space. Moreover this embedding is uniformly continuous. *)
Section metric_embedding.
  Context `{Setoid X'} {Y : MetricSpace}.
  Context (f : X' -> Y) {inj : Injective f}.

  Definition Eball (q: Q) (x y: X'): Prop := ball q (f x) (f y).
  Local Existing Instance injective_mor.

  Global Instance Eball_wd : Proper (Qeq ==> (=) ==> (=) ==> iff) Eball.
  Proof.
    intros ?? E ?? F ?? G. unfold Eball.
    destruct inj.
    pose proof (@sm_proper _ _ _ _ f injective_mor x0 y0 F).
    pose proof (@sm_proper _ _ _ _ f injective_mor x1 y1 G).
    apply (ball_wd Y E _ _ H0 _ _ H1).
  Qed.

  Let is_MetricSpace: is_MetricSpace Eball.
  Proof.
    constructor; unfold ball.
    - intros e H0 x. apply ball_refl, H0.
    - intros e x y. apply ball_sym.
    - intros. now eapply ball_triangle; eauto.
    - intros. now apply ball_closed.
    - intros. 
      apply (msp_nonneg (msp Y)) in H0. exact H0.
    - intros. apply (msp_stable (msp Y)), H0.
  Qed.

  Program Definition Emetric: MetricSpace := Build_MetricSpace _ is_MetricSpace.
  Next Obligation. rewrite H0. reflexivity. Qed.
  Let X := Emetric.

  Lemma Eball_spec ε (x y : X) : ball ε x y ↔ ball ε (f x) (f y).
  Proof. intuition. Qed.

  Lemma Eball_ex_spec ε (x y : X) : ball_ex ε x y ↔ ball_ex ε (f x) (f y).
  Proof. destruct ε; intuition. Qed.

  Lemma metric_embed_uc_prf : is_UniformlyContinuousFunction (f : X → Y) Qpos2QposInf.
  Proof. now intros ε x y E. Qed.

  Definition metric_embed_uc : X --> Y 
    := Build_UniformlyContinuousFunction metric_embed_uc_prf.

End metric_embedding.

Class AppInverse `(f : X → Y) := app_inverse : Y → Qpos → X.
Arguments app_inverse {X Y} f {AppInverse}.

Class DenseEmbedding `{Equiv X} {Y : MetricSpace} (f : X → Y) `{!AppInverse f} := {
  dense_embed_setoid : Setoid X ;
  dense_injective :: Injective f ;
  dense_inverse : ∀ x (ε:Qpos), ball (proj1_sig ε) (f (app_inverse f x ε)) x
}.

(* Given a dense embedding of a setoid [X] into a prelength space [Y] then [X] 
   is also a prelength space. Moreover, the completion of [X] is isomorphic to 
   the completion of [Y]. *)
Section dense_prelength_embedding.
  Context `{Setoid X'} {Y : MetricSpace} (plY : PrelengthSpace Y) (f : X' → Y) 
    `{!AppInverse f} `{!DenseEmbedding f}.
  Let X := Emetric f.

  Lemma Qpos_lt_1_mult_l (x : Qpos) (y : Q)
    : (y < 1 → y * proj1_sig x < proj1_sig x)%Q.
  Proof with auto with qarith.
    intros E. destruct x; simpl.
    rewrite <-(Qmult_1_l x), Qmult_assoc. 
    apply Qmult_lt_compat_r. exact q.
    rewrite Qmult_1_r. exact E.
  Qed.

  Lemma EPrelengthSpace_aux (x y : Qpos) (z : Q) : 
    (z < 1 → 0 < proj1_sig x - z * proj1_sig (Qpos_min x y))%Q.
  Proof with auto.
    intros E. 
    apply (proj1 (Qlt_minus_iff _ _)).
    destruct (Qle_total (`y) (`x)) as [F|F]. 
    pose proof (proj1 (Qpos_le_min_r x y) F).
    unfold QposEq in H0. rewrite H0.
     apply Qlt_le_trans with (`y)... 
     apply Qpos_lt_1_mult_l...
    pose proof (proj1 (Qpos_le_min_l x y) F).
    unfold QposEq in H0. rewrite H0.
    apply Qpos_lt_1_mult_l...
  Qed.

  (* Luckily this lives in [Prop] because it looks very inefficient *)
  Lemma EPrelengthSpace : PrelengthSpace X.
  Proof with auto with qarith.
    intros x y ε δ1 δ2 E F.
    pose (exist (Qlt 0) (1#2) eq_refl) as half.
    pose (exist (Qlt 0) (1#3) eq_refl) as third.
    simpl in *. 
    assert (` ε < ` (δ1 + δ2)%Qpos)%Q as EE by (exact E).
    destruct (Qpos_sub _ _ EE) as [γ Eγ].
    assert (1#3 < 1)%Q as G...
    pose proof (EPrelengthSpace_aux δ1 γ (1#3) G) as E1.
    pose proof (EPrelengthSpace_aux δ2 γ (1#3) G) as E2.
    destruct (@plY (f x) (f y) ε (exist _ _ E1) (exist _ _ E2)) as [z Ez1 Ez2]...
    - simpl.
      apply (Qlt_le_trans
       _ (`ε + (`γ - (2 # 3) * proj1_sig (Qpos_min γ (Qpos_min
          (Qpos_min (half * δ1 + half * δ2) (half * γ + half * δ2))
          (half * δ1 + half * γ))))))%Q.
       rewrite <-(Qplus_0_r (`ε)) at 1. 
       apply Qplus_lt_r.
       apply EPrelengthSpace_aux...
       do 5 rewrite Q_Qpos_min. simpl.
       rewrite <-Qmin_plus_distr_l.
      rewrite (Qmin_comm (`γ)). rewrite <-Qmin_assoc.
      setoid_replace (Qmin ((1 # 2) * ` δ1 + (1 # 2) * ` γ) (` γ))
        with (Qmin ((1 # 2) * ` δ1 + (1 # 2) * ` γ) ((1#2) * ` γ + (1#2)*` γ)).
       rewrite <-Qmin_plus_distr_l.
       rewrite <-Qmin_plus_distr_r.
       repeat rewrite <-Qmin_mult_pos_distr_r...
       unfold Qminus. unfold QposEq in Eγ.
       rewrite (Qplus_assoc (` ε)), <- Eγ.
       simpl.
       ring_simplify.
       setoid_replace (-2#6) with (-1#3).
       apply Qle_refl. reflexivity.
       ring_simplify ((1 # 2) * ` γ + (1 # 2) * ` γ)%Q.
       reflexivity.
    - exists (app_inverse f z (exist (Qlt 0) (1#3) eq_refl * Qpos_min γ (Qpos_min δ1 δ2))). 
      assert (QposEq δ1 (exist _ _ E1 + (third * Qpos_min δ1 γ)))
        by (unfold QposEq; simpl; ring).
      apply (Eball_wd _ _ _ H0 _ _ (reflexivity _) _ _ (reflexivity _)). clear H0.
     eapply ball_triangle; eauto.
     eapply ball_weak_le. 2: now apply ball_sym, dense_inverse.
     simpl. autorewrite with QposElim.
     apply Qmult_le_compat_l; eauto with qarith.
     assert (QposEq δ2 (third * Qpos_min δ2 γ + exist _ _ E2))
       by (unfold QposEq; simpl; ring).
      apply (Eball_wd _ _ _ H0 _ _ (reflexivity _) _ _ (reflexivity _)). clear H0.
    eapply ball_triangle; eauto.
    eapply ball_weak_le. 2: now apply dense_inverse.
    simpl. autorewrite with QposElim.
    apply Qmult_le_compat_l; eauto with qarith.
  Qed.

  Let plX := EPrelengthSpace.
  
  (* Now we also have an embedding of the completion of [X] into the completion of [Y] *)
  Definition Eembed : Complete X --> Complete Y := Cmap plX (metric_embed_uc f).
  
  Instance: Setoid_Morphism Eembed := {}.

  Instance Eembed_injective: Injective Eembed.
  Proof.
    split; try apply _.
    intros x y E ε1 ε2. apply Eball_spec, E.
  Qed.

  (* And back... *)
  Lemma dense_regular_prf (y : Y) : is_RegularFunction_noInf _ (app_inverse f y : Qpos → X).
  Proof.
    intros ε1 ε2. simpl.
    eapply ball_triangle.
     now eapply dense_inverse.
    now eapply ball_sym, dense_inverse.
  Qed.
 
  Definition dense_regular (y : Y) : Complete X 
    := mkRegularFunction (app_inverse f y (exist (Qlt 0) (1#1) eq_refl) : X)
                         (dense_regular_prf y).

  Definition metric_embed_back_prf : is_UniformlyContinuousFunction dense_regular Qpos2QposInf.
  Proof.
    intros ε x y E δ1 δ2. 
    simpl in *. 
    eapply ball_triangle.
     eapply ball_triangle.
      now eapply dense_inverse.
     apply E.
    now eapply ball_sym, dense_inverse.
  Qed.

  Definition metric_embed_back_uc : Y --> Complete X 
    := Build_UniformlyContinuousFunction metric_embed_back_prf.

  Definition Eembed_inverse : Complete Y --> Complete X := Cbind plY metric_embed_back_uc.
  Global Instance: Inverse Eembed := Eembed_inverse.

  Instance: Setoid_Morphism Eembed_inverse := {}.

  Instance Eembed_surjective : Surjective Eembed.
  Proof.
    pose (exist (Qlt 0) (1#2) eq_refl) as half. 
    split; [| apply _].
    intros x y E. rewrite <-E. 
    intros ε1 ε2.
    simpl. unfold Cjoin_raw. simpl.
    rewrite Qplus_0_r.
    setoid_replace (proj1_sig ε1 + proj1_sig ε2)%Q
      with (proj1_sig (half * ε1 + (half * ε1 + ε2))%Qpos)
      by (simpl; ring).
    eapply ball_triangle.
     now eapply dense_inverse.
    now apply regFun_prf.
  Qed.

  Global Instance: Bijective Eembed := {}.

  Global Instance: Inverse Eembed_inverse := Eembed.
  Global Instance: Bijective Eembed_inverse.
  Proof. apply jections.flip_bijection. Qed.

  Let F := Eembed.

  (* Given a function [g : X → X] that agrees with a uniformly continious 
     function [h : Y → Y], then [g] is also uniformly continious. Moreover, [map g] 
     and [map h] agree. *)
  Section unary_functions.
    Context (g' : X' → X') (h : Y --> Y) (g_eq_h : ∀ x, f (g' x) = h (f x)).
    
    Lemma unary_uc_prf : is_UniformlyContinuousFunction (g' : X → X) (mu h).
    Proof.
      intros ε a b H0. apply Eball_spec.
      apply (ball_wd _ (QposEq_refl ε) _ _ (g_eq_h _) _ _ (g_eq_h _)). 
      eapply uc_prf. now destruct (mu h ε).
    Qed.

    Definition unary_uc : X --> X := Build_UniformlyContinuousFunction unary_uc_prf.
    Let g := unary_uc.

    Lemma preserves_unary_fun x : F (Cmap plX g x) = Cmap plY h (F x).
    Proof.
      intros e1 e2.
      apply regFunEq_equiv. 
      apply regFunEq_e. intros ε. 
      simpl. rewrite QposInf_bind_id.
      apply (ball_wd _ eq_refl _ _ (g_eq_h _) _ _ (reflexivity _)). 
      apply ball_refl.
      apply (Qpos_nonneg (ε + ε)).
    Qed.
  End unary_functions.

  (* And a similar result for binary functions *)
  Section binary_functions.
    Context (g' : X' → X → X) (h : Y --> Y --> Y) (g_eq_h : ∀ x y, f (g' x y) = h (f x) (f y)).
    
    Program Let g'' (x : X) := unary_uc (g' x) (h (f x)) _.

    Lemma binary_uc_prf : is_UniformlyContinuousFunction (g'' : X → (X --> X)) (mu h).
    Proof.
      intros ε x y E. split. apply Qpos_nonneg. intro z.
      apply Eball_spec. simpl.
      apply (ball_wd _ (QposEq_refl ε) _ _ (g_eq_h _ _) _ _ (g_eq_h _ _)). 
      apply (uc_prf h).
      now destruct (mu h ε).
    Qed.

    Definition binary_uc : X --> X --> X := Build_UniformlyContinuousFunction binary_uc_prf.
    Let g := binary_uc.

    Lemma preserves_binary_fun x y : F (Cmap2 plX plX g x y) = Cmap2 plY plY h (F x) (F y).
    Proof.
      intros e1 e2. apply regFunEq_equiv, regFunEq_e. intros ε. 
      simpl. unfold Cap_raw. simpl. 
      apply (ball_wd _ eq_refl _ _ (g_eq_h _ _) _ _ (reflexivity _)). 
      rewrite 2!QposInf_bind_id. 
      apply ball_refl.
      apply (Qpos_nonneg (ε + ε)).
    Qed.
  End binary_functions.

  (* Given a function [g : X → Complete X] that agrees with a uniformly continious 
     function [h : Y → Complete Y], then [g] is also uniformly continious. Moreover, [bind g] 
     and [bind h] agree. *)
  Section unary_complete_functions.
    Context (g' : X' → Complete X) (h : Y --> Complete Y) (g_eq_h : ∀ x, F (g' x) = h (f x)).
    
    Definition unary_complete_uc_prf : is_UniformlyContinuousFunction (g' : X → Complete X) (mu h).
    Proof.
      pose (exist (Qlt 0) (1#4) eq_refl) as quarter.
      intros ε x y E δ1 δ2. apply Eball_spec.
      apply ball_closed. intros δ3 dpos.
      setoid_replace (proj1_sig δ1 + proj1_sig ε + proj1_sig δ2 + δ3)%Q
        with (proj1_sig
                ((δ1 + quarter * exist _ _ dpos)
                 + (quarter * exist _ _ dpos + ε + quarter * exist _ _ dpos)
                 + (δ2 + quarter * exist _ _ dpos))%Qpos)
        by (simpl; ring).
      eapply ball_triangle.
      eapply ball_triangle.
       specialize (g_eq_h x).
       apply regFunEq_equiv in g_eq_h.
       apply g_eq_h.
      apply Eball_ex_spec in E.
      apply (uc_prf h). apply E.
      apply ball_sym.
      specialize (g_eq_h y).
       apply regFunEq_equiv in g_eq_h.
       apply g_eq_h. 
    Qed.

    Definition unary_complete_uc : X --> Complete X := Build_UniformlyContinuousFunction unary_complete_uc_prf.
    Let g := unary_complete_uc.

    Lemma preserves_unary_complete_fun x : F (Cbind plX g x) = Cbind plY h (F x).
    Proof.
      pose (exist (Qlt 0) (1#2) eq_refl) as half. 
      intros ? ?. rewrite Qplus_0_r. apply regFunEq_e. intros ε.
      simpl. unfold Cjoin_raw. simpl.
      rewrite QposInf_bind_id.
      apply ball_weak. apply Qpos_nonneg.
      assert (QposEq ε (half * ε + half * ε)) by (unfold QposEq; simpl; ring).
      apply (ball_wd _ H0 _ _ (reflexivity _) _ _ (reflexivity _)). clear H0. 
      pose proof (g_eq_h (approximate x (mu h (half * ε)))).
      apply regFunEq_equiv in H0.
      apply H0.
    Qed.
  End unary_complete_functions.
End dense_prelength_embedding.
