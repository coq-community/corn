Require Import 
  Program Ring CLogic
  Qabs stdlib_omissions.Q workaround_tactics
  QMinMax QposMinMax Qdlog
  Complete Prelength Qmetric MetricMorphisms 
  CRGroupOps CRFieldOps CRpower CRclasses Qposclasses
  stdlib_binary_naturals minmax.
Require Export
  ApproximateRationals.

Section ARarith.
Context `{AppRationals AQ}.

Open Local Scope uc_scope. 
Local Opaque regFunEq.

Definition AQ_as_MetricSpace := Emetric (coerce : AQ → Q_as_MetricSpace).
Definition AQPrelengthSpace := EPrelengthSpace QPrelengthSpace (coerce : AQ → Q_as_MetricSpace).
Definition AR := Complete AQ_as_MetricSpace.
Definition ARtoCR_uc : AQ_as_MetricSpace --> Q_as_MetricSpace := metric_embed_uc (coerce : AQ → Q_as_MetricSpace).
Definition ARtoCR : AR --> CR := Eembed QPrelengthSpace (coerce : AQ → Q_as_MetricSpace). 
Definition CRtoAR : CR --> AR := Eembed_inverse QPrelengthSpace (coerce : AQ → Q_as_MetricSpace).

Hint Rewrite (rings.preserves_0 (f:=coerce : AQ → Q)) : aq_preservation.
Hint Rewrite (rings.preserves_1 (f:=coerce : AQ → Q)) : aq_preservation.
Hint Rewrite (rings.preserves_plus (f:=coerce : AQ → Q)) : aq_preservation.
Hint Rewrite (rings.preserves_mult (f:=coerce : AQ → Q)) : aq_preservation.
Hint Rewrite (rings.preserves_opp (f:=coerce : AQ → Q)) : aq_preservation.
Hint Rewrite aq_preserves_max : aq_preservation.
Hint Rewrite aq_preserves_min : aq_preservation.
Hint Rewrite (abs.preserves_abs (f:=coerce : AQ → Q)): aq_preservation.
Ltac aq_preservation := autorewrite with aq_preservation; try reflexivity.
Local Obligation Tactic := program_simpl; aq_preservation.

Lemma AQball_fold ε (x y : AQ_as_MetricSpace) : ball ε x y → Qball ε ('x) ('y).
Proof. intuition. Qed.

(* Compress *)
Lemma aq_approx_regular_prf x : 
  is_RegularFunction_noInf _ (λ ε : Qpos, app_approx x (Qdlog2 ε) : AQ_as_MetricSpace).
Proof.
  intros ε1 ε2. simpl.
  eapply ball_triangle. 
   apply aq_approx_dlog2.
  apply ball_sym, aq_approx_dlog2.
Qed.

Definition AQcompress (x : AQ_as_MetricSpace) : AR := 
  mkRegularFunction (0 : AQ_as_MetricSpace) (aq_approx_regular_prf x).

Lemma AQcompress_uc_prf : is_UniformlyContinuousFunction AQcompress Qpos2QposInf.
Proof.
  intros ε x y E δ1 δ2. simpl in *.
  eapply ball_triangle.
   2: apply ball_sym, aq_approx_dlog2.
  eapply ball_triangle; eauto.
  apply aq_approx_dlog2.
Qed.

Definition AQcompress_uc := Build_UniformlyContinuousFunction AQcompress_uc_prf.

Definition ARcompress : AR --> AR := Cbind AQPrelengthSpace AQcompress_uc.

Lemma ARcompress_correct (x : AR) : ARcompress x = x.
Proof.
  apply: regFunEq_e. intros ε.
  setoid_replace (ε + ε) with ((1#2) * ε + ((1#2) * ε + ε))%Qpos by QposRing.
  eapply ball_triangle.
   apply_simplified (aq_approx_dlog2 (approximate x ((1 # 2) * ε)%Qpos) ((1#2) * ε)).
  apply regFun_prf.
Qed.

(* Constants *)
Global Instance inject_AQ_AR: Coerce AQ AR := (@Cunit AQ_as_MetricSpace).
Global Instance inject_PosAQ_AR: Coerce (AQ₊) AR := Basics.compose inject_AQ_AR (coerce : AQ₊ → AQ).
Global Instance inject_Z_AR: Coerce Z AR := Basics.compose inject_AQ_AR (coerce : Z → AQ).

Instance: Proper ((=) ==> (=)) inject_AQ_AR := uc_wd (@Cunit AQ_as_MetricSpace).

Lemma ARtoCR_inject (x : AQ) : ARtoCR ('x) = '('x : Q).
Proof. apply: regFunEq_e. intros ε. apply ball_refl. Qed.

Global Instance AR_0: RingZero AR := '0 : AR.
Lemma ARtoCR_preserves_0 : ARtoCR 0 = 0.
Proof. unfold "0", AR_0. rewrite ARtoCR_inject. aq_preservation. Qed.
Hint Rewrite ARtoCR_preserves_0 : ARtoCR.

Global Instance AR_1: RingOne AR := '1 : AR.
Lemma ARtoCR_preserves_1 : ARtoCR 1 = 1.
Proof. unfold "1", AR_1. rewrite ARtoCR_inject. aq_preservation. Qed.
Hint Rewrite ARtoCR_preserves_1 : ARtoCR.

(* Plus *)
Program Definition AQtranslate_uc (x : AQ_as_MetricSpace) 
  := unary_uc coerce ((x +) : AQ_as_MetricSpace → AQ_as_MetricSpace) (Qtranslate_uc ('x)) _.
Definition ARtranslate (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQtranslate_uc x).

Lemma ARtoCR_preserves_translate x y : ARtoCR (ARtranslate x y) = translate (ARtoCR_uc x) (ARtoCR y).
Proof. apply preserves_unary_fun. Qed.
Hint Rewrite ARtoCR_preserves_translate : ARtoCR.

Program Definition AQplus_uc
  := binary_uc coerce ((+) : AQ_as_MetricSpace →  AQ_as_MetricSpace → AQ_as_MetricSpace) Qplus_uc _.

Definition ARplus_uc : AR --> AR --> AR := Cmap2 AQPrelengthSpace AQPrelengthSpace AQplus_uc.
Global Instance AR_plus: RingPlus AR := ucFun2 ARplus_uc.

Lemma ARtoCR_preserves_plus x y : ARtoCR (x + y) = ARtoCR x + ARtoCR y.
Proof. apply preserves_binary_fun. Qed.
Hint Rewrite ARtoCR_preserves_plus : ARtoCR.

(* Inverse *)
Program Definition AQopp_uc
  := unary_uc coerce ((-) : AQ_as_MetricSpace → AQ_as_MetricSpace) Qopp_uc _.
Definition ARopp_uc : AR --> AR := Cmap AQPrelengthSpace AQopp_uc.
Global Instance AR_opp: GroupInv AR := ARopp_uc.

Lemma ARtoCR_preserves_opp x : ARtoCR (-x) = -ARtoCR x.
Proof. apply preserves_unary_fun. Qed.
Hint Rewrite ARtoCR_preserves_opp : ARtoCR.

(* Mult *) 
Program Definition AQboundBelow_uc (x : AQ_as_MetricSpace) : AQ_as_MetricSpace --> AQ_as_MetricSpace 
  := unary_uc coerce (max x  : AQ_as_MetricSpace → AQ_as_MetricSpace) (QboundBelow_uc ('x)) _.

Definition ARboundBelow (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQboundBelow_uc x).

Lemma ARtoCR_preserves_boundBelow x y : ARtoCR (ARboundBelow x y) = boundBelow ('x) (ARtoCR y).
Proof. apply preserves_unary_fun. Qed.
Hint Rewrite ARtoCR_preserves_boundBelow : ARtoCR.

Program Definition AQboundAbove_uc (x : AQ_as_MetricSpace) : AQ_as_MetricSpace --> AQ_as_MetricSpace 
  := unary_uc coerce (min x : AQ_as_MetricSpace → AQ_as_MetricSpace) (QboundAbove_uc ('x)) _.

Definition ARboundAbove (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQboundAbove_uc x).

Lemma ARtoCR_preserves_boundAbove x y : ARtoCR (ARboundAbove x y) = boundAbove ('x) (ARtoCR y).
Proof. apply preserves_unary_fun. Qed.
Hint Rewrite ARtoCR_preserves_boundAbove : ARtoCR.

Program Definition AQboundAbs_uc (c : AQ₊) : AQ_as_MetricSpace --> AQ_as_MetricSpace 
  := unary_uc coerce (λ x : AQ_as_MetricSpace, max (-'c) (min ('c) x) : AQ_as_MetricSpace) (QboundAbs ('c)) _.

Definition ARboundAbs (c : AQ₊) : AR --> AR := Cmap AQPrelengthSpace (AQboundAbs_uc c).

Lemma ARtoCR_preserves_bound_abs c x : ARtoCR (ARboundAbs c x) = CRboundAbs ('c) (ARtoCR x).
Proof. apply preserves_unary_fun. Qed.
Hint Rewrite ARtoCR_preserves_bound_abs : ARtoCR.

Program Definition AQscale_uc (x : AQ_as_MetricSpace) : AQ_as_MetricSpace --> AQ_as_MetricSpace 
  := unary_uc coerce ((x *.)  : AQ_as_MetricSpace → AQ_as_MetricSpace) (Qscale_uc ('x)) _.

Definition ARscale (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQscale_uc x).

Lemma ARtoCR_preserves_scale x y : ARtoCR (ARscale x y) = scale ('x) (ARtoCR y).
Proof. apply preserves_unary_fun. Qed.
Hint Rewrite ARtoCR_preserves_scale : ARtoCR.

Program Definition AQmult_uc (c : AQ₊) : AQ_as_MetricSpace --> AQ_as_MetricSpace --> AQ_as_MetricSpace 
  := binary_uc coerce (λ x y : AQ_as_MetricSpace, x * AQboundAbs_uc c y : AQ_as_MetricSpace) (Qmult_uc ('c)) _.

Definition ARmult_bounded (c : AQ₊) : AR --> AR --> AR 
  := Cmap2 AQPrelengthSpace AQPrelengthSpace (AQmult_uc c).

Lemma ARtoCR_preserves_mult_bounded x y c : 
  ARtoCR (ARmult_bounded c x y) = CRmult_bounded ('c) (ARtoCR x) (ARtoCR y).
Proof. apply preserves_binary_fun. Qed.
Hint Rewrite ARtoCR_preserves_mult_bounded : ARtoCR.

Lemma ARtoCR_approximate (x : AR) (ε : Qpos) : '(approximate x ε) = approximate (ARtoCR x) ε.
Proof. reflexivity. Qed.

Lemma AR_b_correct (x : AR) :
  '(abs (approximate x (1#1)%Qpos) + 1) = Qabs (approximate (ARtoCR x) (1#1)%Qpos) + (1#1)%Qpos.
Proof. aq_preservation. Qed.

Program Definition AR_b (x : AR) : AQ₊ := exist _ (abs (approximate x (1#1)%Qpos) + 1) _.
Next Obligation.
  apply aq_preserves_lt. rewrite AR_b_correct. aq_preservation.
  apply CR_b_pos.
Qed.

Global Instance AR_mult: RingMult AR := λ x y, ARmult_bounded (AR_b y) x y.

Lemma ARtoCR_preserves_mult x y : ARtoCR (x * y) = ARtoCR x * ARtoCR y.
Proof.
  unfold "*", AR_mult at 1. rewrite ARtoCR_preserves_mult_bounded.
  setoid_replace ('AR_b y : Qpos) with (CR_b (1 # 1) (ARtoCR y)). 
   reflexivity.
  unfold QposEq. simpl.
  now rewrite ARtoCR_approximate, <-AR_b_correct.
Qed.

Lemma ARmult_scale (x : AQ) (y : AR) :
  'x * y = ARscale x y.
Proof.
  apply (injective ARtoCR).
  rewrite ARtoCR_preserves_mult, ARtoCR_preserves_scale, ARtoCR_inject.
  now apply CRmult_scale.
Qed.

Hint Rewrite ARtoCR_preserves_mult : ARtoCR.

(* The approximate reals form a ring *)
Global Instance: Ring AR.
Proof.
  apply (rings.embed_ring ARtoCR).
      exact ARtoCR_preserves_plus.
     exact ARtoCR_preserves_0.
    exact ARtoCR_preserves_mult.
   exact ARtoCR_preserves_1.
  exact ARtoCR_preserves_opp.
Qed.

Global Instance: SemiRing_Morphism ARtoCR.
Proof.
  repeat (split; try apply _).
     exact ARtoCR_preserves_plus.
    exact ARtoCR_preserves_0.
   exact ARtoCR_preserves_mult.
  exact ARtoCR_preserves_1.
Qed.

Global Instance: SemiRing_Morphism CRtoAR.
Proof. change (SemiRing_Morphism (inverse ARtoCR)). split; apply _. Qed.

Global Instance: SemiRing_Morphism (coerce : AQ → AR).
Proof.
  repeat (split; try apply _); intros; try reflexivity.
   apply: regFunEq_e. intros ε. now apply ball_refl. 
  rewrite ARmult_scale. apply: regFunEq_e. intros ε. now apply ball_refl.
Qed.

Add Ring CR : (rings.stdlib_ring_theory CR).
Add Ring AR : (rings.stdlib_ring_theory AR).

(* Order *) 
Definition ARnonNeg (x : AR) : Prop := ∀ ε : Qpos, (-'ε : Q) ≤ 'approximate x ε.

Lemma ARtoCR_preserves_nonNeg x : ARnonNeg x ↔ CRnonNeg (ARtoCR x).
Proof. reflexivity. Qed. 
Hint Resolve ARtoCR_preserves_nonNeg.

Global Instance: Proper ((=) ==> iff) ARnonNeg.
Proof.
  intros x1 x2 E.
  split; intros; apply ARtoCR_preserves_nonNeg; [rewrite <-E | rewrite E]; auto.
Qed.

Definition ARnonPos (x : AR) := ∀ ε : Qpos, 'approximate x ε ≤ (ε : Q).

Lemma ARtoCR_preserves_nonPos x : ARnonPos x ↔ CRnonPos (ARtoCR x).
Proof. reflexivity. Qed.
Hint Resolve ARtoCR_preserves_nonPos.

Global Instance AR_le: Order AR := λ x y, ARnonNeg (y - x).

Global Instance: Proper ((=) ==> (=) ==> iff) AR_le.
Proof.
  intros x1 x2 E y1 y2 F. unfold AR_le in *.
  now rewrite E, F.
Qed.

Global Instance ARtoCR_preserves_le: OrderEmbedding ARtoCR.
Proof.
  repeat (split; try apply _); unfold precedes, AR_le, CR_le, CRle.
   intros. change (CRnonNeg (ARtoCR y - ARtoCR x)). now rewrite <-rings.preserves_minus.
  intros. apply ARtoCR_preserves_nonNeg. now rewrite rings.preserves_minus.
Qed.

Global Instance: RingOrder AR_le.
Proof rings.embed_ringorder ARtoCR.

Global Instance: OrderEmbedding (coerce : AQ → AR).
Proof.
  repeat (split; try apply _); intros x y E.
   apply (order_preserving_back ARtoCR).
   rewrite 2!ARtoCR_inject.
   now do 2 apply (order_preserving _).
  apply (order_preserving_back (coerce : AQ → Q)).
  apply (order_preserving_back (coerce : Q → CR)).
  rewrite <-2!ARtoCR_inject.
  now apply (order_preserving _).
Qed.

Global Instance: PropHolds ((0:AR) ≤ (1:AR)).
Proof. apply (order_preserving (coerce : AQ → AR)). solve_propholds. Qed.

Definition ARpos (x : AR) : CProp := sig (λ y : AQ₊, 'y ≤ x).

Program Definition ARpos_char (ε : AQ₊) (x : AR) (Pε : 2 * 'ε ≤ approximate x ('ε : Qpos)) : ARpos x := ε ↾ _.
Next Obligation.
  intros δ.
  change (-('δ : Q) ≤ '(approximate x ((1 # 2) * δ)%Qpos - 'ε)).
  transitivity (-'((1 # 2) * δ)%Qpos).
   apply rings.flip_opp.
   change ((1 # 2) * δ ≤ δ).
   rewrite <-(rings.mult_1_l (δ:Q)) at 2.
   now apply (order_preserving (.* (δ:Q))).
  apply rings.flip_nonneg_minus.
  transitivity ('approximate x ('ε : Qpos) - 2 * 'ε : Q).
   apply (order_preserving (coerce : AQ → Q)) in Pε.
   rewrite rings.preserves_mult, rings.preserves_2 in Pε.
   now apply rings.flip_nonneg_minus.
  apply rings.flip_minus_l.
  transitivity (('ε + (1 # 2) * δ) + 'approximate x ((1 # 2) * δ)%Qpos).
   apply rings.flip_minus_l.
   now destruct (regFun_prf x ('ε : Qpos) ((1#2) * δ)%Qpos).
  rewrite rings.preserves_minus.
  apply orders.equiv_precedes.
  change ('ε + (1 # 2) * δ + 'approximate x ((1 # 2) * δ)%Qpos ==
    'approximate x ((1 # 2) * δ)%Qpos - 'ε - - ((1 # 2) * δ) + (2#1) * ' ε)%Q. ring.
Qed.  

Lemma ARtoCR_preserves_pos x : ARpos x IFF CRpos (ARtoCR x).
Proof with auto with qarith.
  split; intros [y E].
   exists ('y : Qpos).
   change ('('('y : AQ) : Q) ≤ ARtoCR x). 
   rewrite <-ARtoCR_inject.
   now apply (order_preserving _).
  destruct (aq_lt_mid 0 y) as [z [Ez1 Ez2]]...
  assert (0 < z) as F. apply aq_preserves_lt. aq_preservation...
  exists (exist _ z F). simpl.
  change ('('(z ↾ F) : AQ) ≤ x).
  apply (order_preserving_back ARtoCR).
  rewrite ARtoCR_inject.
  apply CRle_trans with (''y); trivial.
  apply CRArith.CRle_Qle...
Defined.

Lemma ARpos_wd : ∀ x1 x2, x1 = x2 → ARpos x1 → ARpos x2.
Proof.
  intros x1 x2 E G.
  apply ARtoCR_preserves_pos.
  apply CRpos_wd with (ARtoCR x1).
   rewrite E. reflexivity.
  now apply ARtoCR_preserves_pos.
Qed.

Global Instance AR_lt: CSOrder AR := λ x y, ARpos (y - x).

Lemma ARtoCR_preserves_lt x y : x ⋖ y IFF ARtoCR x ⋖ ARtoCR y.
Proof with reflexivity.
  stepl (CRpos (ARtoCR (y - x))). 
   split; intros; eapply CRpos_wd; eauto. 
    autorewrite with ARtoCR... 
   autorewrite with ARtoCR...
  split; apply ARtoCR_preserves_pos.
Defined.

Lemma ARlt_wd : ∀ x1 x2 : AR, x1 = x2 → ∀ y1 y2, y1 = y2 → x1 ⋖ y1 → x2 ⋖ y2.
Proof.
  intros x1 x2 E y1 y2 F G. 
  apply ARpos_wd with (y1 + - x1); trivial.
  rewrite E, F. reflexivity.
Qed.

Lemma ARtoCR_preserves_lt_0 x : 0 ⋖ x IFF 0 ⋖ ARtoCR x.
Proof with eauto; try reflexivity.
  stepl (ARtoCR 0 ⋖ ARtoCR x).
   split; apply CRlt_wd; autorewrite with ARtoCR... 
  split; intros; eapply ARtoCR_preserves_lt...
Defined.

Lemma ARtoCR_preserves_0_lt x : x ⋖ 0 IFF ARtoCR x ⋖ 0.
Proof with eauto; try reflexivity.
  stepl (ARtoCR x ⋖ ARtoCR 0).
   split; apply CRlt_wd; autorewrite with ARtoCR... 
  split; intros; eapply ARtoCR_preserves_lt...
Defined.

(* Apartness *)
Global Instance AR_apart: Apart AR := λ x y, x ⋖ y or y ⋖ x.

Lemma ARtoCR_preserves_apart x y : x >< y IFF ARtoCR x >< ARtoCR y.
Proof. 
  split; (intros [|]; [left|right]; apply ARtoCR_preserves_lt; assumption).
Defined.

Lemma ARtoCR_preserves_apart_0 x : x >< 0 IFF ARtoCR x >< 0.
Proof.
  stepr (ARtoCR x >< ARtoCR 0).
   split; apply ARtoCR_preserves_apart. 
  split; apply CRapart_wd; try rewrite ARtoCR_preserves_0; reflexivity. 
Defined.

Lemma aq_mult_inv_regular_prf x : 
  is_RegularFunction_noInf _ (λ ε : Qpos, app_div 1 x (Qdlog2 ε) : AQ_as_MetricSpace).
Proof.
  intros ε1 ε2. simpl.
  eapply ball_triangle. 
   eapply aq_div_dlog2.
  eapply ball_sym, aq_div_dlog2.
Qed.

Definition AQinv (x : AQ) : AR := mkRegularFunction (0 : AQ_as_MetricSpace) (aq_mult_inv_regular_prf x).

Definition AQinv_bounded (c : AQ₊) (x : AQ_as_MetricSpace) : AR := AQinv (max ('c) x).

Lemma AQinv_pos_uc_prf (c : AQ₊) : is_UniformlyContinuousFunction 
  (AQinv_bounded c) (Qinv_modulus ('c)).
Proof.
  intros ε x y E δ1 δ2. simpl in *.
  eapply ball_triangle.
   2: eapply ball_sym, aq_div_dlog2.
  eapply ball_triangle.
   eapply aq_div_dlog2.
  simpl. aq_preservation. apply Qinv_pos_uc_prf in E.
  rewrite 2!left_identity. apply E.
Qed.

Definition AQinv_pos_uc (c : AQ₊) := Build_UniformlyContinuousFunction (AQinv_pos_uc_prf c).

Definition ARinv_pos (c : AQ₊) : AR --> AR := Cbind AQPrelengthSpace (AQinv_pos_uc c).

Lemma ARtoCR_preserves_inv_pos_aux c (x : AR) : is_RegularFunction_noInf _
   (λ γ, / Qmax (''c) ('approximate x (Qinv_modulus ('c) γ)) : Q_as_MetricSpace).
Proof.
  intros ε1 ε2.
  apply_simplified (Qinv_pos_uc_prf ('c)).
  apply AQball_fold. 
  setoid_replace (Qinv_modulus ('c) (ε1 + ε2)) with (Qinv_modulus ('c) ε1 + Qinv_modulus ('c) ε2).
   apply regFun_prf.
  unfold QposEq. simpl. ring.
Qed.

Lemma ARtoCR_preserves_inv_pos x c : ARtoCR (ARinv_pos c x) = CRinv_pos ('c) (ARtoCR x).
Proof.
  apply: regFunEq_e. intros ε. 
  simpl. unfold Cjoin_raw. simpl.
  setoid_replace (ε + ε) with ((1#2) * ε + ((1#2) * ε + ε))%Qpos by QposRing.
  eapply ball_triangle.
   apply aq_div_dlog2.
  rewrite aq_preserves_max. 
  rewrite rings.preserves_1. rewrite left_identity.
  apply ARtoCR_preserves_inv_pos_aux.
Qed.
Hint Rewrite ARtoCR_preserves_inv_pos : ARtoCR.

Definition ARinv (x : AR) (x_ : x >< 0) : AR := 
  match x_ with
  | inl (exist c _) => - ARinv_pos c (- x)
  | inr (exist c _) => ARinv_pos c x
  end.

Lemma ARtoCR_preserves_inv x x_ x__: ARtoCR (ARinv x x_) = CRinv (ARtoCR x) x__. 
Proof with auto with qarith; try reflexivity.
  unfold ARinv.
  destruct x_ as [Ec | Ec].
   pose proof (fst (ARtoCR_preserves_0_lt _) Ec) as Px.
   rewrite (CRinv_irrelvent _ (inl Px)). 
   unfold CRinv.
   destruct Ec as [c Ec], Px as [d Ed].
   autorewrite with ARtoCR.
   destruct (Qlt_le_dec d ('c : Qpos)).
    rewrite (CRinv_pos_weaken d ('c))...
    change ('('('c : AQ) : Q) ≤ -ARtoCR x).
    rewrite <-ARtoCR_inject, <-rings.preserves_opp.
    apply (order_preserving _).
    rewrite <-(rings.plus_0_l (-x))...
   rewrite (CRinv_pos_weaken ('c) d)...
   rewrite <-(rings.plus_0_l (-ARtoCR x))...
  pose proof (fst (ARtoCR_preserves_lt_0 _) Ec) as Px.
  rewrite (CRinv_irrelvent _ (inr Px)). 
  unfold CRinv.
  destruct Ec as [c Ec], Px as [d Ed].
  autorewrite with ARtoCR.
  destruct (Qlt_le_dec d ('c : Qpos)).
   rewrite (CRinv_pos_weaken d ('c))...
   change ('('('c : AQ) : Q) ≤ ARtoCR x).
   rewrite <-ARtoCR_inject. 
   apply (order_preserving _).
   setoid_replace x with (x - 0 : AR) by ring...
  rewrite (CRinv_pos_weaken ('c) d)...
  rewrite <-(rings.plus_0_r (ARtoCR x))...
Qed.

Lemma ARtoCR_preserves_inv_l x x_ : {x__ | ARtoCR (ARinv x x_) = CRinv (ARtoCR x) x__}.
Proof.
  exists (fst (ARtoCR_preserves_apart_0 x) x_).
  apply ARtoCR_preserves_inv.
Qed.

Lemma ARtoCR_preserves_inv_r x x__ : {x_ | ARtoCR (ARinv x x_) = CRinv (ARtoCR x) x__}.
Proof.
  exists (snd (ARtoCR_preserves_apart_0 x) x__).
  apply ARtoCR_preserves_inv.
Qed.

Lemma ARinv_wd x y x_ y_ : x = y → ARinv x x_ = ARinv y y_.
Proof.
  intros E.
  apply (injective ARtoCR). 
  destruct (ARtoCR_preserves_inv_l x x_) as [x__ Ex], (ARtoCR_preserves_inv_l y y_) as [y__ Ey].
  rewrite Ex, Ey. 
  now apply CRinv_wd.
Qed.

Lemma ARinv_irrelevent x x_ x__ : ARinv x x_ = ARinv x x__.
Proof. apply ARinv_wd. reflexivity. Qed.

Program Definition AQpower_N_uc (n : N) (c : AQ₊) : AQ_as_MetricSpace --> AQ_as_MetricSpace
  := unary_uc coerce (λ x : AQ_as_MetricSpace, (AQboundAbs_uc c x) ^ n : AQ_as_MetricSpace)
           (Qpower_N_uc n ('c)) _.
Next Obligation.
  assert (∀ y : AQ, '(y ^ n) = 'y ^ 'n) as preserves_pow_pos.
   intros y.
   rewrite nat_pow.preserves_nat_pow.
   now rewrite (int_pow.int_pow_nat_pow (f:=coerce : N → Z)).
  rewrite preserves_pow_pos. aq_preservation. 
Qed.

Definition ARpower_N_bounded (n : N) (c : AQ₊) : AR --> AR := Cmap AQPrelengthSpace (AQpower_N_uc n c).

Lemma ARtoCR_preserves_power_N_bounded x n c : 
  ARtoCR (ARpower_N_bounded n c x) = CRpower_N_bounded n ('c) (ARtoCR x).
Proof. apply preserves_unary_fun. Qed.

Global Instance AR_power_N: Pow AR N := λ x n, ucFun (ARpower_N_bounded n (AR_b x)) x.

Lemma ARtoCR_preserves_power_N (x : AR) (n : N) : 
  ARtoCR (x ^ n) = (ARtoCR x) ^ n.
Proof.
  unfold pow, CR_power_N, AR_power_N.
  rewrite ARtoCR_preserves_power_N_bounded.
  setoid_replace ('AR_b x : Qpos) with (CR_b (1#1) (ARtoCR x)). 
   reflexivity.
  unfold QposEq. simpl.
  now rewrite ARtoCR_approximate, <-AR_b_correct.
Qed. 

Hint Rewrite ARtoCR_preserves_power_N : ARtoCR.

Global Instance: NatPowSpec AR N _.
Proof.
  split.
    intros ? ? Ex ? ? En.
    apply (injective ARtoCR). autorewrite with ARtoCR.
    now rewrite Ex, En.
   intros. apply (injective ARtoCR). autorewrite with ARtoCR.
   now rewrite nat_pow_0.
  intros. apply (injective ARtoCR). autorewrite with ARtoCR.
  now rewrite nat_pow_S.
Qed.

(* Misc properties *)
Lemma ARmult_bounded_mult (x y : AR) c : 
  -'c ≤ y ≤ 'c → ARmult_bounded c x y = x * y.
Proof.
  intros. 
  apply (injective ARtoCR).
  rewrite ARtoCR_preserves_mult, ARtoCR_preserves_mult_bounded.
  destruct c as [c Pc].
  apply CRmult_bounded_mult.
   change ('(-'c : Q) ≤ ARtoCR y).
   rewrite <-rings.preserves_opp.
   rewrite <-ARtoCR_inject.
   apply (order_preserving _). intuition.
  change (ARtoCR y ≤ '('c : Q)).
  rewrite <-ARtoCR_inject.
  apply (order_preserving _). intuition.
Qed.

Lemma ARpower_N_bounded_N_power (n : N) (x : AR) (c : AQ₊) : 
  -'c ≤ x ≤ 'c → ARpower_N_bounded n c x = x ^ n.
Proof.
  intros.
  apply (injective ARtoCR).
  rewrite ARtoCR_preserves_power_N, ARtoCR_preserves_power_N_bounded.
  destruct c as [c Pc].
  apply CRpower_N_bounded_N_power. split.
   change ('(-'c : Q) ≤ ARtoCR x).
   rewrite <-rings.preserves_opp.
   rewrite <-ARtoCR_inject.
   apply (order_preserving _). intuition.
  change (ARtoCR x ≤ '('c : Q)).
  rewrite <-ARtoCR_inject.
  apply (order_preserving _). intuition.
Qed.
End ARarith.
