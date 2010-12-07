Require Import 
  Program Ring 
  Qabs stdlib_omissions.Q
  QMinMax QposMinMax
  Complete Prelength Qmetric 
  CRGroupOps CRFieldOps CRArith
  interfaces.abstract_algebra theory.rings implementations.stdlib_rationals
  orders.minmax.

Lemma QposInf_bind_compose (f : Qpos -> QposInf) (g : Qpos -> Qpos) x :  
  QposInf_bind f (QposInf_bind g x) ≡ QposInf_bind (fun y, f (g y)) x.
Proof. destruct x as [|x]; reflexivity. Qed.

Section cmap.
  Open Scope uc_scope. 

  Context {X : MetricSpace} {Y : MetricSpace} {plX : PrelengthSpace X} {plY : PrelengthSpace Y}.
  Context {f : X --> Y}.
  Let F := Cmap plX f.

  Lemma Cmap_uc_compose g1 g2 h1 h2 : 
        (∀ x, F (Cmap plX g1 x) [=] Cmap plY h1 (F x))
    → (∀ x, F (Cmap plX g2 x) [=] Cmap plY h2 (F x))
    → ∀ x, F (Cmap plX (g1 ∘ g2) x) [=] Cmap plY (h1 ∘ h2) (F x).
  Proof with auto.
    intros E1 E2 x.
    do 2 rewrite fast_MonadLaw2.
    rewrite <-E2. apply E1.
  Qed.

  (* Is this even true? I hope so, however... *)
  Lemma Cmap_Cmap2 (g : X --> X --> X) (h : Y --> Y --> Y) :
        (∀ x y, F (Cmap plX (g x) y) [=] Cmap plY (h (f x)) (F y))
(*    → (∀ e, mu g e ≡ mu h e) *)
    → ∀ x y, F (Cmap2 plX plX g x y) [=] Cmap2 plY plY h (F x) (F y).
  Proof with auto with qarith.
  Admitted.
End cmap.

(* TODO: move various parts to separate files *)

Section approximate_rationals.
  Context `(f : AQ → Q) (g : Qpos → Q → AQ) 
    {e : Equiv AQ} {plus : RingPlus AQ} {mult : RingMult AQ} 
    {zero : RingZero AQ} {one : RingOne AQ} `{opp : GroupInv AQ}.

  Class AppRationals := {
    app_rationals_ring :> @Ring AQ e plus mult zero one opp ;
    app_rationals_sur : ∀ x ε, Qball ε (f (g ε x)) x ;
    app_rationals_inj :> Injective f ;
    app_rationals_embed :> Ring_Morphism f ;
    app_rationals_mor :> Proper (QposEq ==> (=) ==> (=)) g
  }.

End approximate_rationals.

(* This is ugly.... *)
Global Instance app_rationals_order `{AppRationals AQ f g} : Order AQ | 3 := λ x y, (f x <= f y)%Q.

Class AppRationalsAbs `{AppRationals AQ f g} := app_rationals_abs_sig : ∀ x, 
  { y | (0 ≤ x → y = x) ∧ (x < 0 → y = -x) }.
Definition app_rationals_abs `{AppRationalsAbs} := λ x, proj1_sig (app_rationals_abs_sig x).

Class AppRationalsMultInv `{AppRationals AQ f g} := app_rationals_mult_inv_sig : ∀ ε x,
  { y | Qball ε (f y) (/(f x)) }.
Definition app_rationals_mult_inv `{AppRationalsMultInv} := λ ε x, proj1_sig (app_rationals_mult_inv_sig ε x).

Section approximate_rationals_order.
  Context `{AppRationals AQ f g}. 

  Global Instance app_rationals_precedes_dec : ∀ (x y : AQ), Decision (x ≤ y).
  Proof. 
    intros. unfold "≤", app_rationals_order.
    apply Qle_dec.
  Qed.

  Global Instance: TotalOrder app_rationals_order.
  Proof with auto. 
    repeat intro. unfold "≤", app_rationals_order.
    destruct (Qle_total (f x) (f y))...
  Qed.

  Instance: Proper ((=) ==> (=) ==> iff) app_rationals_order.
  Proof. 
    intros ? ? E1 ? ? E2. unfold app_rationals_order.
    rewrite E1. rewrite E2. reflexivity.
  Qed.

  Instance: Reflexive app_rationals_order.
  Proof. intros x. unfold app_rationals_order. apply Qle_refl. Qed.
  
  Instance: Transitive app_rationals_order.
  Proof. intros x y z. unfold app_rationals_order. apply Qle_trans. Qed.

  Instance: AntiSymmetric app_rationals_order.
  Proof with auto. 
    intros x y. unfold app_rationals_order. 
    intros. apply (injective f). apply Qle_antisym... 
  Qed.

  Global Instance: PartialOrder app_rationals_order.
  Proof. repeat (split; try apply _). Qed.

  Lemma preserves_max x y : f (max x y) = Qmax (f x) (f y).
  Proof with auto; try reflexivity.
    destruct (total_order x y) as [E|E].
     rewrite max_r... rewrite (proj1 (Qle_max_r (f x) (f y)))...
    rewrite max_l... rewrite (proj1 (Qle_max_l (f x) (f y)))...
  Qed.

  Lemma preserves_min x y : f (min x y) = Qmin (f x) (f y).
  Proof with auto; try reflexivity.
    destruct (total_order x y) as [E|E].
     rewrite min_l... rewrite (proj1 (Qle_min_l (f x) (f y)))...
    rewrite min_r... rewrite (proj1 (Qle_min_r (f x) (f y)))...
  Qed.

  Lemma strictly_precedes_Qlt x y : x < y ↔ (f x < f y)%Q.
  Proof with auto.
    split.
     intros [E1 E2].
     destruct (proj1 (Qle_lteq (f x) (f y)))...
     destruct E2. apply (injective f)...
    intros E. split.
     apply Qlt_le_weak...
    intros E2. apply (Qlt_not_eq (f x) (f y))...
    apply sm_proper...
  Qed.
  
  Context `{abs : !AppRationalsAbs}.
  Lemma preserves_abs x : f (app_rationals_abs x) = Qabs (f x).
  Proof with auto with qarith.
    unfold app_rationals_abs, app_rationals_abs_sig.
    destruct abs as [y [Ey1 Ey2]]. simpl.
    destruct (Qlt_le_dec (f x) 0) as [E|E].
     rewrite Ey2. 
      symmetry. rewrite preserves_opp. apply Qabs_neg... 
     apply strictly_precedes_Qlt. rewrite preserves_0... 
    rewrite Ey1. 
     symmetry. apply Qabs_pos...
    unfold "≤", app_rationals_order. rewrite preserves_0...
  Qed.

End approximate_rationals_order.

Section positive_approximate_rationals.
  Context `{AppRationals AQ f g}. 

  Definition AQpos := sig (λ x : AQ, 0 < x).

  Definition AQposAsAQ: AQpos → AQ := @proj1_sig _ _.
  
  Global Instance: Equiv AQpos := λ x y, AQposAsAQ x = AQposAsAQ y.
  Global Instance: Setoid AQpos.

  Program Definition AQpos2Qpos (x : AQpos) : Qpos := f (AQposAsAQ x).
  Next Obligation.
    destruct x as [x Ex]. simpl.
    apply strictly_precedes_Qlt in Ex.
    erewrite preserves_0 in Ex. assumption.
  Qed.
End positive_approximate_rationals.

Section rsetoid_is_setoid.
  Context {R : RSetoid.Setoid}.

  Global Instance: Equiv (st_car R) := @st_eq R.

  Global Instance: Setoid (st_car R).
End rsetoid_is_setoid.

Section setoid_is_rsetoid.
  Context R `{Setoid R}.

  Program Definition setoid_is_rsetoid: RSetoid.Setoid := {|
    st_car := R ;
    st_eq := equiv 
  |}.
End setoid_is_rsetoid.

Section injection_metric.
  Context {X : RSetoid.Setoid} {Y : MetricSpace}.
  Context (f : X → Y) {inj : Injective f}.

  Definition injection_ball (q: Qpos) (x y: X): Prop := ball q (f x) (f y).

  Instance injection_ball_wd : Proper (QposEq ==> @st_eq X ==> @st_eq X ==> iff) injection_ball.
  Proof.
    intros ?? E ?? F ?? G. unfold injection_ball.
    rewrite E F G. reflexivity. 
  Qed.

  Lemma is_MetricSpace: is_MetricSpace X injection_ball.
  Proof with eauto.
    constructor; unfold ball; repeat intro.
        apply ball_refl.
       apply ball_sym...
      eapply ball_triangle...
     apply ball_closed...
    apply (injective f). apply ball_eq...
  Qed.

  Definition injection_metric: MetricSpace.
   apply (@Build_MetricSpace X injection_ball).
    apply injection_ball_wd.
   apply is_MetricSpace.
  Defined.

  Lemma injection_metric_ball_spec ε (x y : injection_metric) : ball ε x y ↔ ball ε (f x) (f y).
  Proof. intuition. Qed.
End injection_metric.

Global Instance: RingPlus Qpos := Qpos_plus.
Global Instance: RingMult Qpos := Qpos_mult.

Global Instance: RingZero CR := ('0)%CR.
Global Instance: RingOne CR := ('1)%CR.
Global Instance: RingPlus CR := ucFun2 CRplus.
Global Instance: RingMult CR := CRmult.
Global Instance: GroupInv CR := CRopp.

Instance: Ring CR := rings.from_stdlib_ring_theory CR_ring_theory.

Section app_rationals_completion.
  Context `{AppRationals AQ f g}. 

  Definition AQ_as_MetricSpace := injection_metric (f : setoid_is_rsetoid AQ → Q_as_MetricSpace).
  Definition AR := Complete AQ_as_MetricSpace.

  Lemma AQball_fold ε (x y : AQ_as_MetricSpace) : ball ε x y → Qball ε (f x) (f y).
  Proof. intuition. Qed.

  Lemma Qpos_lt_1_mult_l (x : Qpos) (y : Q) : (y < 1 → y * x < x)%Q.
  Proof with auto with qarith.
    intros E. autorewrite with QposElim.
    rewrite <-(Qmult_1_l x) at 2. 
    apply Qmult_lt_compat_r...
  Qed.

  Lemma AQPrelengthSpace_aux (x y : Qpos) (z : Q) : (z < 1 → 0 < x - z * Qpos_min x y)%Q.
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

  (* Luckily this lives in Prop because it looks very inefficient *)
  Lemma AQPrelengthSpace : PrelengthSpace AQ_as_MetricSpace.
  Proof with auto with qarith.
    intros x y ε δ1 δ2 E F.
    simpl in *. 
    destruct (Qpos_lt_plus E) as [γ Eγ].
    assert (1#3 < 1)%Q as G...
    pose proof (AQPrelengthSpace_aux δ1 γ (1#3) G) as E1.
    pose proof (AQPrelengthSpace_aux δ2 γ (1#3) G) as E2.
    destruct (@QPrelengthSpace (f x) (f y) ε (mkQpos E1) (mkQpos E2)) as [z Ez1 Ez2]...
     simpl. 
     setoid_replace (δ1 - (1#3) * Qpos_min δ1 γ + (δ2 - (1#3) * Qpos_min δ2 γ))%Q
       with (ε + (γ - (2 # 3) * Qpos_min γ (Qpos_min
          (Qpos_min ((1 # 2) * δ1 + (1 # 2) * δ2) ((1 # 2) * γ + (1 # 2) * δ2))
          ((1 # 2) * δ1 + (1 # 2) * γ))))%Q.
       rewrite <-(Qplus_0_r ε) at 1. 
       apply Qplus_lt_r.
       apply AQPrelengthSpace_aux...
      unfold q_equiv. autorewrite with QposElim.
      rewrite (Qmin_comm γ). rewrite <-Qmin_assoc.
      setoid_replace (γ:Q) with ((1#2) * γ + (1#2) * γ)%Q at 6 by (unfold q_equiv; ring).
      repeat rewrite <-Qmin_plus_distr_l.
      repeat rewrite <-Qmin_plus_distr_r.
      repeat rewrite <-Qmin_mult_pos_distr_r...
      unfold Qminus at 3. rewrite associativity. rewrite <-Eγ.
      ring.
    exists (g ((1#3) * Qpos_min γ (Qpos_min δ1 δ2)) z). 
     setoid_replace δ1 with (mkQpos E1 + ((1#3) * Qpos_min δ1 γ)%Qpos) at 1 by (unfold QposEq; simpl; ring).
     eapply ball_triangle; eauto.
     eapply ball_weak_le. 2: symmetry; eapply app_rationals_sur...
     simpl. autorewrite with QposElim.
     apply Qmult_le_compat_l; eauto with qarith.
    setoid_replace δ2 with (((1#3) * Qpos_min δ2 γ + mkQpos E2)%Qpos) at 1 by (unfold QposEq; simpl; ring).
    eapply ball_triangle; eauto.
    eapply ball_weak_le. 2: eapply app_rationals_sur...
    simpl. autorewrite with QposElim.
    apply Qmult_le_compat_l; eauto with qarith.
  Qed.

  Open Scope uc_scope. 

  (* Embedding AR into CR *)
  Lemma ARtoCR_uc_prf : is_UniformlyContinuousFunction (f : AQ_as_MetricSpace → Q_as_MetricSpace) Qpos2QposInf.
  Proof. 
    intros ε x y E. auto.
  Qed.

  Definition ARtoCR_uc : AQ_as_MetricSpace --> Q_as_MetricSpace 
    := Build_UniformlyContinuousFunction ARtoCR_uc_prf.
  Definition ARtoCR : AR --> CR := Cmap AQPrelengthSpace ARtoCR_uc.

  Lemma ARtoCR_approximate (x : AR) (ε : Qpos) : f (approximate x ε) = approximate (ARtoCR x) ε.
  Proof. reflexivity. Qed.

  (* Constants *)
  Definition inject_AQ : AQ → AR := (@Cunit AQ_as_MetricSpace).
  Notation "' x" := (inject_AQ x).

  Lemma ARtoCR_inject x : ARtoCR (' x) = (inject_Q (f x))%CR.
  Proof. intros ? ?. apply ball_refl. Qed.

  Global Instance ARzero: RingZero AR := '0.
  Lemma ARtoCR_preserves_0 : ARtoCR 0 = 0.
  Proof. rewrite ARtoCR_inject. rewrite preserves_0. reflexivity. Qed.
  Hint Rewrite ARtoCR_preserves_0 : ARtoCR.

  Global Instance ARone: RingOne AR := '1.
  Lemma ARtoCR_preserves_1 : ARtoCR 1 = 1.
  Proof. rewrite ARtoCR_inject. rewrite preserves_1. reflexivity. Qed.
  Hint Rewrite ARtoCR_preserves_1 : ARtoCR.

  (* (* Todo: generalize *)
  Lemma ARtoCR_uc_compose fA fR gA gR : 
    (∀ x : AR, st_eq (ARtoCR (Cmap AQPrelengthSpace fA x)) (Cmap QPrelengthSpace fR (ARtoCR x)))
    → (∀ x : AR, st_eq (ARtoCR (Cmap AQPrelengthSpace gA x)) (Cmap QPrelengthSpace gR (ARtoCR x)))
    → (∀ x : AR, st_eq (ARtoCR (Cmap AQPrelengthSpace (uc_compose fA gA) x)) (Cmap QPrelengthSpace (uc_compose fR gR) (ARtoCR x))).
  Proof with auto.
    intros E1 E2 x.
    do 2 rewrite fast_MonadLaw2.
    rewrite <-E2. apply E1.
  Qed.

  Lemma ARtoCR_uc_map2 (fA : AQ_as_MetricSpace --> AQ_as_MetricSpace --> AQ_as_MetricSpace) 
      (fR : Q_as_MetricSpace --> Q_as_MetricSpace --> Q_as_MetricSpace) :
    (∀ (x : AQ) y, st_eq (ARtoCR (Cmap AQPrelengthSpace (fA x) y)) (Cmap QPrelengthSpace (fR (ARtoCR_uc x)) (ARtoCR y)))
    → (∀ ε, mu fA ε ≡ mu fR ε)
    → (∀ x y, st_eq (ARtoCR (Cmap2 AQPrelengthSpace AQPrelengthSpace fA x y)) (Cmap2 QPrelengthSpace QPrelengthSpace fR (ARtoCR x) (ARtoCR y))).
  Proof with auto with qarith.
    intros E F x y ? ?. apply regFunEq_e. intro ε.
    specialize (E (approximate x (mu fA ((1#2) * ε))) y ((1#2) * ε) ((1 # 2) * ε))%Qpos.
    simpl in *. unfold Cap_raw. simpl. 
    repeat rewrite QposInf_bind_id. repeat rewrite QposInf_bind_id in E.
    rewrite <-F.
    apply ball_weak_le with ((1#2) * ε + (1#2) * ε)%Qpos.
     autorewrite with QposElim.
     setoid_replace (ε + ε)%Q with (1 * ε + 1 * ε)%Q by (unfold q_equiv; ring). 
     apply Qplus_le_compat; apply Qmult_le_compat_r...
    apply E.
  Qed. *)

  (* Plus *)
  Lemma AQtranslate_uc_prf (x : AQ_as_MetricSpace) : is_UniformlyContinuousFunction ((+) x) Qpos2QposInf.
  Proof with auto.
    repeat intro. 
    simpl in *.
    do 2 rewrite rings.preserves_plus. 
    apply Qtranslate_uc_prf...
  Qed.

  Definition AQtranslate_uc (x : AQ_as_MetricSpace) : AQ_as_MetricSpace --> AQ_as_MetricSpace 
    := Build_UniformlyContinuousFunction (AQtranslate_uc_prf x).

  Definition ARtranslate (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQtranslate_uc x).
  
  Lemma ARtoCR_preserves_translate x y : ARtoCR (ARtranslate x y) = translate (ARtoCR_uc x) (ARtoCR y).
  Proof.
    intros ε1 ε2. simpl. 
    rewrite preserves_plus.
    apply Qball_plus_r, AQball_fold, regFun_prf.
  Qed.
  Hint Rewrite ARtoCR_preserves_translate : ARtoCR.

  Lemma AQplus_uc_prf : is_UniformlyContinuousFunction AQtranslate_uc Qpos2QposInf.
  Proof with auto.
    intros ε x y E z.
    simpl in *.
    rewrite commutativity. rewrite (commutativity y z).
    apply AQtranslate_uc_prf...
  Qed.

  Definition AQplus_uc : AQ_as_MetricSpace --> AQ_as_MetricSpace --> AQ_as_MetricSpace 
    := Build_UniformlyContinuousFunction AQplus_uc_prf.

  Definition ARplus : AR --> AR --> AR := Cmap2 AQPrelengthSpace AQPrelengthSpace AQplus_uc.
  Global Instance: RingPlus AR := ucFun2 ARplus.

  Lemma ARtoCR_preserves_plus x y : ARtoCR (x + y) = ARtoCR x + ARtoCR y.
  Proof.
    apply Cmap_Cmap2. apply ARtoCR_preserves_translate. 
  Qed.
  Hint Rewrite ARtoCR_preserves_plus : ARtoCR.

  (* Inverse *)
  Lemma AQopp_uc_prf : is_UniformlyContinuousFunction (group_inv : AQ_as_MetricSpace → AQ_as_MetricSpace) Qpos2QposInf.
  Proof with auto.
    repeat intro.
    simpl in *.
    do 2 rewrite preserves_opp.
    apply Qopp_uc_prf...
  Qed.

  Definition AQopp_uc : AQ_as_MetricSpace --> AQ_as_MetricSpace := Build_UniformlyContinuousFunction AQopp_uc_prf.

  Definition ARopp : AR --> AR := Cmap AQPrelengthSpace AQopp_uc.
  Global Instance: GroupInv AR := ucFun ARopp.

  Lemma ARtoCR_preserves_opp x : ARtoCR (- x) = -(ARtoCR x).
  Proof.
    intros ε1 ε2. simpl.
    rewrite preserves_opp.
    apply Qball_opp.
    apply AQball_fold, regFun_prf.
  Qed.
  Hint Rewrite ARtoCR_preserves_opp : ARtoCR.

  (* mult *)
  Lemma AQboundBelow_uc_prf (x : AQ_as_MetricSpace) : is_UniformlyContinuousFunction (max x) Qpos2QposInf.
  Proof with auto.
    repeat intro.
    simpl in *.
    do 2 rewrite preserves_max.
    apply QboundBelow_uc_prf...
  Qed.
  
  Definition AQboundBelow_uc (x : AQ_as_MetricSpace) : AQ_as_MetricSpace --> AQ_as_MetricSpace 
    := Build_UniformlyContinuousFunction (AQboundBelow_uc_prf x).

  Definition ARboundBelow (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQboundBelow_uc x).

  Lemma ARtoCR_preserves_boundBelow x y : ARtoCR (ARboundBelow x y) = boundBelow (f x) (ARtoCR y).
  Proof with auto.
    repeat intro. apply regFunEq_e. intro ε. simpl.
    rewrite preserves_max.
    destruct (Qle_total (f x) (f (approximate y ε))).
     rewrite (proj1 (Qle_max_r _ _))... apply AQball_fold, regFun_prf.
    rewrite (proj1 (Qle_max_l _ _))... apply ball_refl.
  Qed.
  Hint Rewrite ARtoCR_preserves_boundBelow : ARtoCR.

  Lemma AQboundAbove_uc_prf (x : AQ_as_MetricSpace) : is_UniformlyContinuousFunction (min x) Qpos2QposInf.
  Proof with auto.
    repeat intro.
    simpl in *.
    do 2 rewrite preserves_min.
    apply QboundAbove_uc_prf...
  Qed.
  
  Definition AQboundAbove_uc (x : AQ_as_MetricSpace) : AQ_as_MetricSpace --> AQ_as_MetricSpace 
    := Build_UniformlyContinuousFunction (AQboundAbove_uc_prf x).
 
  Definition ARboundAbove (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQboundAbove_uc x).

  Lemma ARtoCR_preserves_boundAbove x y : ARtoCR (ARboundAbove x y) = boundAbove (f x) (ARtoCR y).
  Proof with auto.
    repeat intro. apply regFunEq_e. intro ε. simpl.
    rewrite preserves_min.
    destruct (Qle_total (f x) (f (approximate y ε))).
     rewrite (proj1 (Qle_min_l _ _))... apply ball_refl.
    rewrite (proj1 (Qle_min_r _ _))... apply AQball_fold, regFun_prf.
  Qed.
  Hint Rewrite ARtoCR_preserves_boundAbove : ARtoCR.

  Definition AQboundAbs_uc (c : AQpos) : AQ_as_MetricSpace --> AQ_as_MetricSpace
    := uc_compose (AQboundBelow_uc (-AQposAsAQ c)) (AQboundAbove_uc (AQposAsAQ c)).

  Definition ARboundAbs (c : AQpos) : AR --> AR := Cmap AQPrelengthSpace (AQboundAbs_uc c).

  Lemma ARtoCR_preserves_bound_abs c x : ARtoCR (ARboundAbs c x) = CRboundAbs (AQpos2Qpos c) (ARtoCR x).
  Proof with auto.
    apply Cmap_uc_compose.
     intros y ε1 ε2. simpl. setoid_replace (- f (AQposAsAQ c)) with (f (- AQposAsAQ c)).
      pose proof (ARtoCR_preserves_boundBelow (- AQposAsAQ c) y) as P. apply P.
     rewrite preserves_opp. reflexivity.
    apply ARtoCR_preserves_boundAbove.
  Qed.
  Hint Rewrite ARtoCR_preserves_bound_abs : ARtoCR.

  Lemma AQscale_uc_prf (x : AQ_as_MetricSpace) :  is_UniformlyContinuousFunction (ring_mult x) (Qscale_modulus (f x)).
  Proof with auto.
    repeat intro.
    simpl in *.
    do 2 rewrite preserves_mult.
    apply Qscale_uc_prf...
  Qed.

  Definition AQscale_uc (x : AQ_as_MetricSpace) : AQ_as_MetricSpace --> AQ_as_MetricSpace 
    := Build_UniformlyContinuousFunction (AQscale_uc_prf x).

  Definition ARscale (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQscale_uc x).

  Lemma ARtoCR_preserves_scale x y : ARtoCR (ARscale x y) = scale (f x) (ARtoCR y).
  Proof.
    intros ? ?. apply regFunEq_e. intro ε. simpl.
    rewrite QposInf_bind_id.
    rewrite preserves_mult.
    assert (∀ (n d : positive), QposEq ((ε + ε) / QabsQpos (n # d)) ((d # n) * ε + (d # n) * ε)) as E.
     intros n d. unfold QposEq. autorewrite with QposElim. unfold Qinv. simpl. ring.
    generalize (f x). clear x. intros [[|n|n] d]; simpl.
      apply ball_refl.
     apply Qball_Qmult_Q_l. rewrite E. apply AQball_fold, regFun_prf.
    apply Qball_Qmult_Q_l. rewrite E. apply AQball_fold, regFun_prf.
  Qed.
  Hint Rewrite ARtoCR_preserves_scale : ARtoCR.

  Lemma AQmult_uc_prf (c : AQpos) : is_UniformlyContinuousFunction 
    (λ x, uc_compose (AQscale_uc x) (AQboundAbs_uc c)) (Qmult_modulus (AQpos2Qpos c)).
  Proof.
    intros ε x y E z.
    simpl in *.
    do 2 rewrite preserves_mult.
    rewrite preserves_max. rewrite preserves_min.
    rewrite preserves_inv.
    pose proof (Qmult_uc_prf (AQpos2Qpos c) ε (f x) (f y) E) as P. 
    simpl in P. unfold ucBall in P. simpl in P. apply P. (* apply needs help here... *)
  Qed.

  Definition AQmult_uc (c : AQpos) :  AQ_as_MetricSpace --> AQ_as_MetricSpace --> AQ_as_MetricSpace
    := Build_UniformlyContinuousFunction (AQmult_uc_prf c).

  Definition ARmult_bounded (c : AQpos) : AR --> AR --> AR 
    := Cmap2 AQPrelengthSpace AQPrelengthSpace (AQmult_uc c).

  Lemma ARtoCR_preserves_mult_bounded x y c : 
    ARtoCR (ARmult_bounded c x y) = CRmult_bounded (AQpos2Qpos c) (ARtoCR x) (ARtoCR y).
  Proof with auto.
    apply Cmap_Cmap2. clear x y. intros x y.
    assert (st_eq (ARtoCR (Cmap AQPrelengthSpace (uc_compose (AQscale_uc x) (AQboundAbs_uc c)) y))
      (Cmap QPrelengthSpace (uc_compose (Qscale_uc (f x)) (QboundAbs (AQpos2Qpos c))) (ARtoCR y))) as P.
     apply Cmap_uc_compose.
     apply ARtoCR_preserves_scale.
     apply ARtoCR_preserves_bound_abs.
    apply P.
  Qed.
  Hint Rewrite ARtoCR_preserves_mult_bounded : ARtoCR.

  Context `{abs : !AppRationalsAbs}.
  Lemma AR_b_correct (x : AR) : 
    f (app_rationals_abs (approximate x (1#1)%Qpos) + 1) = Qabs (approximate (ARtoCR x) (1#1)%Qpos) + (1#1)%Qpos.
  Proof with auto.
    rewrite preserves_plus. rewrite preserves_1. rewrite preserves_abs.
    rewrite ARtoCR_approximate. reflexivity.
  Qed.

  Program Definition AR_b (x : AR) : AQpos := exist _ (app_rationals_abs (approximate x (1#1)%Qpos) + 1) _.
  Next Obligation with auto with qarith.
    apply strictly_precedes_Qlt.
    rewrite AR_b_correct. rewrite preserves_0. apply CR_b_pos.
  Qed.

  Global Instance ARmult: RingMult AR := λ x y, ucFun2 (ARmult_bounded (AR_b y)) x y.

  Lemma ARtoCR_preserves_mult x y : ARtoCR (x * y) = ARtoCR x * ARtoCR y.
  Proof.
    rewrite ARtoCR_preserves_mult_bounded.
    setoid_replace (AQpos2Qpos (AR_b y)) with (CR_b (1 # 1) (ARtoCR y)). 
     reflexivity.
    unfold QposEq. simpl. rewrite AR_b_correct. reflexivity. 
  Qed. 
  Hint Rewrite ARtoCR_preserves_mult : ARtoCR.

  (* Embedding Q into X *)
  Lemma flip_g_is_regular (q : Q_as_MetricSpace) : is_RegularFunction_noInf _ (Basics.flip g q : Qpos → AQ_as_MetricSpace).
  Proof with auto.
    intros ε1 ε2. unfold Basics.flip. simpl.
    eapply ball_triangle.
     eapply app_rationals_sur...
    eapply ball_sym, app_rationals_sur...
  Qed.
 
  Definition flip_g (q : Q_as_MetricSpace) : AR := mkRegularFunction 0 (flip_g_is_regular q).

  Definition CRtoAR_prf : is_UniformlyContinuousFunction flip_g Qpos2QposInf.
  Proof with auto.
    intros ε x y E. intros δ1 δ2. 
    simpl in *. unfold Basics.flip.
    eapply ball_triangle.
     eapply ball_triangle.
      eapply app_rationals_sur...
     apply E.
    eapply ball_sym, app_rationals_sur...
  Qed.

  Definition CRtoAR_uc : Q_as_MetricSpace --> AR := Build_UniformlyContinuousFunction CRtoAR_prf.

  Definition CRtoAR : CR --> AR := Cbind QPrelengthSpace CRtoAR_uc.
  
  Lemma CRtoAR_ARtoCR x : CRtoAR (ARtoCR x) = x.
  Proof with auto.
    intros ε1 ε2. simpl. unfold Cjoin_raw. simpl.
    unfold Basics.flip.
    setoid_replace (ε1 + ε2) with ((1#2) * ε1 + ((1#2) * ε1 + ε2))%Qpos by QposRing.
    eapply ball_triangle.
     eapply app_rationals_sur...
    eapply AQball_fold, regFun_prf.
  Qed.

  Lemma ARtoCR_CRtoAR x : ARtoCR (CRtoAR x) = x.
  Proof with auto.
    intros ε1 ε2. simpl. unfold Cjoin_raw. simpl.
    unfold Basics.flip.
    setoid_replace (ε1 + ε2) with ((1#2) * ε1 + ((1#2) * ε1 + ε2))%Qpos by QposRing.
    eapply ball_triangle.
     eapply app_rationals_sur...
    eapply regFun_prf.
  Qed.

  Global Instance: Inverse ARtoCR := CRtoAR.

  Instance: Injective ARtoCR. 
  Proof. 
    split; try apply _. 2: split; apply _.
    intros x y E. 
    rewrite <-(CRtoAR_ARtoCR x). rewrite E. rewrite CRtoAR_ARtoCR. reflexivity.
  Qed.
 
  Instance: Surjective ARtoCR.
  Proof with auto. 
    split; try apply _.
    intros x y E. transitivity x...
    apply ARtoCR_CRtoAR.
  Qed.

  Global Instance: Bijective ARtoCR.

  (* The approximate reals form a ring *)
  Add Ring CR: (rings.stdlib_ring_theory CR).
  Opaque CR AR.

  Instance: Proper (@st_eq _ ==> @st_eq _ ==> @st_eq _) ARmult. 
  Proof. 
    intros ? ? E1 ? ? E2. 
    apply (injective ARtoCR). autorewrite with ARtoCR.
    rewrite E1. rewrite E2. reflexivity.
  Qed.

  Global Instance: Ring AR.
  Proof. 
    repeat (split; try apply _); 
     repeat intro; apply (injective ARtoCR); autorewrite with ARtoCR; ring.
  Qed.

  Global Instance: Ring_Morphism ARtoCR.
  Proof. repeat (split; try apply _); intros; autorewrite with ARtoCR; reflexivity. Qed.
 
  Global Instance: Ring_Morphism CRtoAR.
  Proof. change (Ring_Morphism (inverse ARtoCR)). apply _. Qed.

  Lemma ARtoCR_preserves_minus x y : ARtoCR (x - y) = ARtoCR x - ARtoCR y.
  Proof.
    do 2 rewrite ring_minus_correct. autorewrite with ARtoCR. reflexivity.
  Qed.
  Hint Rewrite ARtoCR_preserves_minus : ARtoCR.

  (* Order *)
  Definition ARnonNeg (x : AR) := ∀ ε : Qpos, (-ε <= f (approximate x ε))%Q.
  
  Lemma ARtoCR_preserves_nonNeg x : ARnonNeg x ↔ CRnonNeg (ARtoCR x).
  Proof. reflexivity. Qed.
  
  Definition ARnonPos (x : AR) := ∀ ε : Qpos, (f (approximate x ε) <= ε)%Q.

  Lemma ARtoCR_preserves_nonPos x : ARnonPos x ↔ CRnonPos (ARtoCR x).
  Proof. reflexivity. Qed.

  Definition ARle x y := ARnonNeg (y - x).
  
  Lemma ARtoCR_preserves_le x y : ARle x y ↔ CRle (ARtoCR x) (ARtoCR y).
  Proof.
    unfold ARle, CRle.
    replace (ARtoCR y - ARtoCR x)%CR with (ARtoCR y - ARtoCR x) by reflexivity.
    rewrite <-ARtoCR_preserves_minus. reflexivity.
  Qed.

  Definition ARpos (x : AR) := sig (λ ε : AQpos, ARle (' AQposAsAQ ε) x).

  Lemma yada (x ε : Qpos) : { y : AQpos | AQpos2Qpos y <= x ∧ Qball ε (AQpos2Qpos y) x }.
  Proof. Admitted.

  Lemma ARtoCR_preserves_pos x : ARpos x IFF CRpos (ARtoCR x).
  Proof.
    split; intros [ε E].
     exists (AQpos2Qpos ε). simpl. rewrite <-ARtoCR_inject.
     apply ARtoCR_preserves_le in E. apply E.
    destruct (yada ε ε) as [δ Eδ1 Eδ2].
    admit.
  Qed.

  Definition ARlt (x y : AR) := ARpos (y - x).

  Lemma ARtoCR_preserves_lt x y : ARlt x y IFF CRlt (ARtoCR x) (ARtoCR y).
  Proof.
    unfold ARlt, CRlt.
    replace (ARtoCR y - ARtoCR x)%CR with (ARtoCR y - ARtoCR x) by reflexivity.
    stepl (CRpos (ARtoCR (y - x))). 
     split; intros; eapply CRpos_wd; eauto. 
      apply ARtoCR_preserves_minus.
     symmetry. apply ARtoCR_preserves_minus.
    split; apply ARtoCR_preserves_pos.
  Qed.
  
  (* Apartness *)
  Definition ARapart (x y : AR) := (ARlt x y or ARlt y x).
  Notation "x >< y" := (ARapart x y).

  Lemma ARtoCR_preserves_apart x y : (x >< y) IFF ((ARtoCR x) >< (ARtoCR y))%CR.
  Proof. 
    split; (intros [|]; [left|right]; apply ARtoCR_preserves_lt; assumption).
  Qed.

  (* Multiplicate inverse *)
  Context `{app_inv : !AppRationalsMultInv}.

  Lemma app_rationals_mult_inv_correct x ε : Qball ε (f (app_rationals_mult_inv ε x)) (/(f x)).
  Proof.
    unfold app_rationals_mult_inv, app_rationals_mult_inv_sig.
    destruct app_inv as [y Ey]. assumption.
  Qed.

  Lemma flip_app_rationals_mult_inv_is_regular (q : AQ_as_MetricSpace) : 
    is_RegularFunction_noInf _ (Basics.flip app_rationals_mult_inv q : Qpos → AQ_as_MetricSpace).
  Proof with auto.
    intros ε1 ε2. unfold Basics.flip. simpl.
    eapply ball_triangle.
     eapply app_rationals_mult_inv_correct.
    eapply ball_sym, app_rationals_mult_inv_correct.
  Qed.
 
  Definition flip_app_rationals_mult_inv (q : AQ_as_MetricSpace) : AR := 
    mkRegularFunction 0 (flip_app_rationals_mult_inv_is_regular q).

  (*
  Lemma AQinv_pos_uc_prf (c : AQpos) :  is_UniformlyContinuousFunction 
    ((λ x : AQ_as_MetricSpace, app_rationals_mult_inv ((1#3) * AQpos2Qpos c) (max (AQposAsAQ c) x) : AQ_as_MetricSpace)) 
    (Qinv_modulus ((2 # 3) * AQpos2Qpos c)).
  *)  

End app_rationals_completion.
