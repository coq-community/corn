Require 
  theory.jections.
Require Import 
  Setoid CornTac
  stdlib_omissions.Q QMinMax QposMinMax Qposclasses
  RSetoid CSetoids
  Complete Prelength
  abstract_algebra.

Set Automatic Introduction.
Open Local Scope uc_scope.

(* Given an embedding of a setoid [X] into a metric space [Y] then [X] is also a 
   metric space. Moreover this embedding is uniformly continuous. *)
Section metric_embedding.
  Context `{Setoid X'} {Y : MetricSpace}.
  Context (f : X' -> Y) {inj : Injective f}.

  Definition Eball (q: Qpos) (x y: X'): Prop := ball q (f x) (f y).

  Global Instance Eball_wd : Proper (QposEq ==> (=) ==> (=) ==> iff) Eball.
  Proof.
    intros ?? E ?? F ?? G. unfold Eball.
    now rewrite E F G.
  Qed.

  Let is_MetricSpace: is_MetricSpace (mcSetoid_as_RSetoid X') Eball.
  Proof.
    constructor; unfold ball; repeat intro.
        now apply ball_refl.
       now apply ball_sym.
      now eapply ball_triangle; eauto.
     now apply ball_closed.
    apply (injective f). now apply ball_eq.
  Qed.

  Program Definition Emetric: MetricSpace := Build_MetricSpace _ is_MetricSpace.
  Next Obligation. apply Eball_wd; assumption. Qed.
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
Implicit Arguments app_inverse [[X] [Y] [AppInverse]].

Class DenseEmbedding `{Equiv X} {Y : MetricSpace} (f : X → Y) `{!AppInverse f} := {
  dense_embed_setoid : Setoid X ;
  dense_injective :> Injective f ;
  dense_inverse_proper :> Proper ((=) ==> QposEq ==> (=)) (app_inverse f) ;
  dense_inverse : ∀ x ε, ball ε (f (app_inverse f x ε)) x
}.

(* Given a dense embedding of a setoid [X] into a prelength space [Y] then [X] 
   is also a prelength space. Moreover, the completion of [X] is isomorphic to 
   the completion of [Y]. *)
Section dense_prelength_embedding.
  Context `{Setoid X'} {Y : MetricSpace} (plY : PrelengthSpace Y) (f : X' → Y) 
    `{!AppInverse f} `{!DenseEmbedding f}.
  Let X := Emetric f.

  Lemma Qpos_lt_1_mult_l (x : Qpos) (y : Q) : (y < 1 → y * x < x)%Q.
  Proof with auto with qarith.
    intros E. autorewrite with QposElim.
    rewrite <-(Qmult_1_l x) at 2. 
    apply Qmult_lt_compat_r...
  Qed.

  Lemma EPrelengthSpace_aux (x y : Qpos) (z : Q) : 
    (z < 1 → 0 < x - z * Qpos_min x y)%Q.
  Proof with auto.
    intros E. 
    apply (proj1 (Qlt_minus_iff _ _)).
    destruct (Qle_total y x) as [F|F]. 
     rewrite (proj1 (Qpos_le_min_r x y) F).
     apply Qlt_le_trans with y... 
     apply Qpos_lt_1_mult_l...
    rewrite (proj1 (Qpos_le_min_l x y) F).
    apply Qpos_lt_1_mult_l...
  Qed.

  (* Luckily this lives in [Prop] because it looks very inefficient *)
  Lemma EPrelengthSpace : PrelengthSpace X.
  Proof with auto with qarith.
    intros x y ε δ1 δ2 E F.
    simpl in *. 
    destruct (Qpos_lt_plus E) as [γ Eγ].
    assert (1#3 < 1)%Q as G...
    pose proof (EPrelengthSpace_aux δ1 γ (1#3) G) as E1.
    pose proof (EPrelengthSpace_aux δ2 γ (1#3) G) as E2.
    destruct (@plY (f x) (f y) ε (mkQpos E1) (mkQpos E2)) as [z Ez1 Ez2]...
     simpl. 
     replace RHS with (ε + (γ - (2 # 3) * Qpos_min γ (Qpos_min
          (Qpos_min ((1 # 2) * δ1 + (1 # 2) * δ2) ((1 # 2) * γ + (1 # 2) * δ2))
          ((1 # 2) * δ1 + (1 # 2) * γ))))%Q.
       rewrite <-(Qplus_0_r ε) at 1. 
       apply Qplus_lt_r.
       apply EPrelengthSpace_aux...
      autorewrite with QposElim.
      rewrite (Qmin_comm γ). rewrite <-Qmin_assoc.
      setoid_replace (γ:Q) with ((1#2) * γ + (1#2) * γ)%Q at 6 by ring.
      repeat rewrite <-Qmin_plus_distr_l.
      repeat rewrite <-Qmin_plus_distr_r.
      repeat rewrite <-Qmin_mult_pos_distr_r...
      unfold Qminus at 3. rewrite Qplus_assoc. rewrite <-Eγ.
      ring.
    exists (app_inverse f z ((1#3) * Qpos_min γ (Qpos_min δ1 δ2))). 
     setoid_replace δ1 with (mkQpos E1 + ((1#3) * Qpos_min δ1 γ))%Qpos at 1 by (unfold QposEq; simpl; ring).
     eapply ball_triangle; eauto.
     eapply ball_weak_le. 2: now apply ball_sym, dense_inverse.
     simpl. autorewrite with QposElim.
     apply Qmult_le_compat_l; eauto with qarith.
    setoid_replace δ2 with (((1#3) * Qpos_min δ2 γ + mkQpos E2))%Qpos at 1 by (unfold QposEq; simpl; ring).
    eapply ball_triangle; eauto.
    eapply ball_weak_le. 2: now apply dense_inverse.
    simpl. autorewrite with QposElim.
    apply Qmult_le_compat_l; eauto with qarith.
  Qed.

  Let plX := EPrelengthSpace.
  
  (* Now we also have an embedding of the completion of [X] into the completion of [Y] *)
  Definition Eembed : Complete X --> Complete Y := Cmap plX (metric_embed_uc f).
  
  Instance: Setoid_Morphism Eembed.

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
    := mkRegularFunction (app_inverse f y 1 : X) (dense_regular_prf y).

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

  Instance: Setoid_Morphism Eembed_inverse.

  Instance Eembed_surjective : Surjective Eembed.
  Proof.
    split; [| apply _].
    intros x y E. rewrite <-E. 
    intros ε1 ε2.
    simpl. unfold Cjoin_raw. simpl.
    setoid_replace (ε1 + ε2)%Qpos with ((1#2) * ε1 + ((1#2) * ε1 + ε2))%Qpos by QposRing.
    eapply ball_triangle.
     now eapply dense_inverse.
    now apply regFun_prf.
  Qed.

  Global Instance: Bijective Eembed.

  Global Instance: Inverse Eembed_inverse := Eembed.
  Global Instance: Bijective Eembed_inverse.
  Proof. apply jections.flip_bijection_pseudoinstance. Qed.

  Let F := Eembed.

  (* Given a function [g : X → X] that agrees with a uniformly continious 
     function [h : Y → Y], then [g] is also uniformly continious. Moreover, [map g] 
     and [map h] agree. *)
  Section unary_functions.
    Context (g' : X' → X') (h : Y --> Y) (g_eq_h : ∀ x, f (g' x) = h (f x)).
    
    Lemma unary_uc_prf : is_UniformlyContinuousFunction (g' : X → X) (mu h).
    Proof.
      intros ε ? ? ?. apply Eball_spec. rewrite 2!g_eq_h.
      eapply uc_prf. now destruct (mu h ε).
    Qed.

    Definition unary_uc : X --> X := Build_UniformlyContinuousFunction unary_uc_prf.
    Let g := unary_uc.

    Lemma preserves_unary_fun x : F (Cmap plX g x) = Cmap plY h (F x).
    Proof.
      intros ? ?. apply regFunEq_e. intros ε. 
      simpl. rewrite QposInf_bind_id.
      rewrite g_eq_h. apply ball_refl.
    Qed.
  End unary_functions.

  (* And a similar result for binary functions *)
  Section binary_functions.
    Context (g' : X' → X → X) (h : Y --> Y --> Y) (g_eq_h : ∀ x y, f (g' x y) = h (f x) (f y)).
    
    Program Let g'' (x : X) := unary_uc (g' x) (h (f x)) _.

    Lemma binary_uc_prf : is_UniformlyContinuousFunction (g'' : X → (X --> X)) (mu h).
    Proof.
      intros ε x y E z.
      apply Eball_spec. rewrite 2!g_eq_h.
      apply (uc_prf h).
      now destruct (mu h ε).
    Qed.

    Definition binary_uc : X --> X --> X := Build_UniformlyContinuousFunction binary_uc_prf.
    Let g := binary_uc.

    Lemma preserves_binary_fun x y : F (Cmap2 plX plX g x y) = Cmap2 plY plY h (F x) (F y).
    Proof.
      intros ? ?. apply regFunEq_e. intros ε. 
      simpl. unfold Cap_raw. simpl. 
      rewrite g_eq_h. rewrite 2!QposInf_bind_id. 
      apply ball_refl.
    Qed.
  End binary_functions.

  (* Given a function [g : X → Complete X] that agrees with a uniformly continious 
     function [h : Y → Complete Y], then [g] is also uniformly continious. Moreover, [bind g] 
     and [bind h] agree. *)
  Section unary_complete_functions.
    Context (g' : X' → Complete X) (h : Y --> Complete Y) (g_eq_h : ∀ x, F (g' x) = h (f x)).
    
    Definition unary_complete_uc_prf : is_UniformlyContinuousFunction (g' : X → Complete X) (mu h).
    Proof.
      intros ε x y E δ1 δ2. apply Eball_spec.
      apply ball_closed. intros δ3.
      setoid_replace (δ1 + ε + δ2 + δ3) with ((δ1 + (1#4) * δ3) + ((1#4) * δ3 + ε + (1#4) * δ3) + (δ2 + (1#4) * δ3))%Qpos by QposRing.
      eapply ball_triangle.
       2: apply ball_sym, (g_eq_h y).
      eapply ball_triangle.
       apply (g_eq_h x).
      apply Eball_ex_spec in E.
      now apply (uc_prf h).
    Qed.

    Definition unary_complete_uc : X --> Complete X := Build_UniformlyContinuousFunction unary_complete_uc_prf.
    Let g := unary_complete_uc.

    Lemma preserves_unary_complete_fun x : F (Cbind plX g x) = Cbind plY h (F x).
    Proof.
      intros ? ?. apply regFunEq_e. intros ε.
      simpl. unfold Cjoin_raw. simpl.
      rewrite QposInf_bind_id.
      apply ball_weak.
      setoid_replace ε with ((1#2) * ε + (1#2) * ε)%Qpos at 1 by QposRing.
      now apply (g_eq_h (approximate x (mu h ((1 # 2) * ε)))).
    Qed.
  End unary_complete_functions.
End dense_prelength_embedding.
