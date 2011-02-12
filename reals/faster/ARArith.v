Require Import 
  Program Ring CLogic
  Qabs stdlib_omissions.Q workaround_tactics
  QMinMax QposMinMax Qdlog2
  Complete Prelength Qmetric MetricMorphisms 
  CRGroupOps CRFieldOps CRpower CRclasses Qposclasses
  stdlib_binary_naturals minmax.
Require Export
  ApproximateRationals.

Section ARarith.
Context `{AppRationals AQ}.

Open Local Scope uc_scope. 

Definition AQ_as_MetricSpace := Emetric inject.
Definition AQPrelengthSpace := EPrelengthSpace QPrelengthSpace inject.
Definition AR := Complete AQ_as_MetricSpace.
Definition ARtoCR_uc : AQ_as_MetricSpace --> Q_as_MetricSpace := metric_embed_uc inject.
Definition ARtoCR : AR --> CR := Eembed QPrelengthSpace inject.
Definition CRtoAR : CR --> AR := Eembed_inverse QPrelengthSpace inject.

Hint Rewrite (rings.preserves_0 (f:=inject)) : aq_preservation.
Hint Rewrite (rings.preserves_1 (f:=inject)) : aq_preservation.
Hint Rewrite (rings.preserves_plus (f:=inject)) : aq_preservation.
Hint Rewrite (rings.preserves_mult (f:=inject)) : aq_preservation.
Hint Rewrite (rings.preserves_opp (f:=inject)) : aq_preservation.
Hint Rewrite aq_preserves_max : aq_preservation.
Hint Rewrite aq_preserves_min : aq_preservation.
Hint Rewrite (abs.preserves_abs (f:=inject)): aq_preservation.
Ltac aq_preservation := autorewrite with aq_preservation; try reflexivity.
Local Obligation Tactic := program_simpl; aq_preservation.

Lemma AQball_fold ε (x y : AQ_as_MetricSpace) : ball ε x y → Qball ε ('x) ('y).
Proof. intuition. Qed.

(* Compress *)
Lemma aq_compress_regular_prf x : 
  is_RegularFunction_noInf _ (λ ε : Qpos, app_compress x (Qdlog2 ε) : AQ_as_MetricSpace).
Proof.
  intros ε1 ε2. simpl.
  eapply ball_triangle. 
   apply aq_compress_Qdlog2.
  apply ball_sym, aq_compress_Qdlog2.
Qed.

Definition AQcompress (x : AQ_as_MetricSpace) : AR := 
  mkRegularFunction (0 : AQ_as_MetricSpace) (aq_compress_regular_prf x).

Lemma AQcompress_uc_prf : is_UniformlyContinuousFunction AQcompress Qpos2QposInf.
Proof.
  intros ε x y E δ1 δ2. simpl in *.
  eapply ball_triangle.
   2: apply ball_sym, aq_compress_Qdlog2.
  eapply ball_triangle; eauto.
  apply aq_compress_Qdlog2.
Qed.

Definition AQcompress_uc := Build_UniformlyContinuousFunction AQcompress_uc_prf.

Definition ARcompress : AR --> AR := Cbind AQPrelengthSpace AQcompress_uc.

Lemma ARcompress_correct (x : AR) : ARcompress x = x.
Proof.
  intros ? ?. apply regFunEq_e. intros ε.
  setoid_replace (ε + ε) with ((1#2) * ε + ((1#2) * ε + ε))%Qpos by QposRing.
  eapply ball_triangle.
   apply_simplified (aq_compress_Qdlog2 (approximate x ((1 # 2) * ε)%Qpos) ((1#2) * ε)).
  apply regFun_prf.
Qed.

(* Constants *)
Global Instance inject_AQ : Inject AQ AR := (@Cunit AQ_as_MetricSpace).

Lemma ARtoCR_inject x : ARtoCR ('x) = ''x.
Proof. intros ? ?. apply ball_refl. Qed.

Global Instance AR_0: RingZero AR := inject_AQ (0:AQ).
Lemma ARtoCR_preserves_0 : ARtoCR 0 = 0.
Proof. rewrite ARtoCR_inject. aq_preservation. Qed.
Hint Rewrite ARtoCR_preserves_0 : ARtoCR.

Global Instance AR_1: RingOne AR := inject_AQ 1.
Lemma ARtoCR_preserves_1 : ARtoCR 1 = 1.
Proof. rewrite ARtoCR_inject. aq_preservation. Qed.
Hint Rewrite ARtoCR_preserves_1 : ARtoCR.

(* Plus *)
Program Definition AQtranslate_uc (x : AQ_as_MetricSpace) 
  := unary_uc inject ((x +) : AQ_as_MetricSpace → AQ_as_MetricSpace) (Qtranslate_uc ('x)) _.
Definition ARtranslate (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQtranslate_uc x).

Lemma ARtoCR_preserves_translate x y : ARtoCR (ARtranslate x y) = translate (ARtoCR_uc x) (ARtoCR y).
Proof. apply preserves_unary_fun. Qed.
Hint Rewrite ARtoCR_preserves_translate : ARtoCR.

Program Definition AQplus_uc
  := binary_uc inject ((+) : AQ_as_MetricSpace →  AQ_as_MetricSpace → AQ_as_MetricSpace) Qplus_uc _.

Definition ARplus_uc : AR --> AR --> AR := Cmap2 AQPrelengthSpace AQPrelengthSpace AQplus_uc.
Global Instance AR_plus: RingPlus AR := ucFun2 ARplus_uc.

Lemma ARtoCR_preserves_plus x y : ARtoCR (x + y) = ARtoCR x + ARtoCR y.
Proof. apply preserves_binary_fun. Qed.
Hint Rewrite ARtoCR_preserves_plus : ARtoCR.

(* Inverse *)
Program Definition AQopp_uc
  := unary_uc inject ((-) : AQ_as_MetricSpace → AQ_as_MetricSpace) Qopp_uc _.
Definition ARopp_uc : AR --> AR := Cmap AQPrelengthSpace AQopp_uc.
Global Instance AR_opp: GroupInv AR := ARopp_uc.

Lemma ARtoCR_preserves_opp x : ARtoCR (-x) = -ARtoCR x.
Proof. apply preserves_unary_fun. Qed.
Hint Rewrite ARtoCR_preserves_opp : ARtoCR.

(* Mult *) 
Program Definition AQboundBelow_uc (x : AQ_as_MetricSpace) : AQ_as_MetricSpace --> AQ_as_MetricSpace 
  := unary_uc inject (max x  : AQ_as_MetricSpace → AQ_as_MetricSpace) (QboundBelow_uc ('x)) _.

Definition ARboundBelow (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQboundBelow_uc x).

Lemma ARtoCR_preserves_boundBelow x y : ARtoCR (ARboundBelow x y) = boundBelow ('x) (ARtoCR y).
Proof. apply preserves_unary_fun. Qed.
Hint Rewrite ARtoCR_preserves_boundBelow : ARtoCR.

Program Definition AQboundAbove_uc (x : AQ_as_MetricSpace) : AQ_as_MetricSpace --> AQ_as_MetricSpace 
  := unary_uc inject (min x : AQ_as_MetricSpace → AQ_as_MetricSpace) (QboundAbove_uc ('x)) _.

Definition ARboundAbove (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQboundAbove_uc x).

Lemma ARtoCR_preserves_boundAbove x y : ARtoCR (ARboundAbove x y) = boundAbove ('x) (ARtoCR y).
Proof. apply preserves_unary_fun. Qed.
Hint Rewrite ARtoCR_preserves_boundAbove : ARtoCR.

Program Definition AQboundAbs_uc (c : AQ₊) : AQ_as_MetricSpace --> AQ_as_MetricSpace 
  := unary_uc inject (λ x : AQ_as_MetricSpace, max (-'c) (min ('c) x) : AQ_as_MetricSpace)
           (QboundAbs (AQposAsQpos c)) _.

Definition ARboundAbs (c : AQ₊) : AR --> AR := Cmap AQPrelengthSpace (AQboundAbs_uc c).

Lemma ARtoCR_preserves_bound_abs c x : ARtoCR (ARboundAbs c x) = CRboundAbs (AQposAsQpos c) (ARtoCR x).
Proof. apply preserves_unary_fun. Qed.
Hint Rewrite ARtoCR_preserves_bound_abs : ARtoCR.

Program Definition AQscale_uc (x : AQ_as_MetricSpace) : AQ_as_MetricSpace --> AQ_as_MetricSpace 
  := unary_uc inject ((x *.)  : AQ_as_MetricSpace → AQ_as_MetricSpace) (Qscale_uc ('x)) _.

Definition ARscale (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQscale_uc x).

Lemma ARtoCR_preserves_scale x y : ARtoCR (ARscale x y) = scale ('x) (ARtoCR y).
Proof. apply preserves_unary_fun. Qed.
Hint Rewrite ARtoCR_preserves_scale : ARtoCR.

Program Definition AQmult_uc (c : AQ₊) : AQ_as_MetricSpace --> AQ_as_MetricSpace --> AQ_as_MetricSpace 
  := binary_uc inject (λ x y : AQ_as_MetricSpace, x * AQboundAbs_uc c y : AQ_as_MetricSpace) 
          (Qmult_uc (AQposAsQpos c)) _.

Definition ARmult_bounded (c : AQ₊) : AR --> AR --> AR 
  := Cmap2 AQPrelengthSpace AQPrelengthSpace (AQmult_uc c).

Lemma ARtoCR_preserves_mult_bounded x y c : 
  ARtoCR (ARmult_bounded c x y) = CRmult_bounded (AQposAsQpos c) (ARtoCR x) (ARtoCR y).
Proof. apply preserves_binary_fun. Qed.
Hint Rewrite ARtoCR_preserves_mult_bounded : ARtoCR.

Lemma ARtoCR_approximate (x : AR) (ε : Qpos) : '(approximate x ε) = approximate (ARtoCR x) ε.
Proof. reflexivity. Qed.

Lemma AR_b_correct (x : AR) :
  '(abs (approximate x (1#1)%Qpos) + 1) = Qabs (approximate (ARtoCR x) (1#1)%Qpos) + (1#1)%Qpos.
Proof. aq_preservation. Qed.

Program Definition AR_b (x : AR) : AQ₊ := exist _ (abs (approximate x (1#1)%Qpos) + 1) _.
Next Obligation with auto with qarith.
  apply aq_preserves_lt. rewrite AR_b_correct. aq_preservation.
  apply CR_b_pos.
Qed.

Global Instance AR_mult: RingMult AR := λ x y, ucFun2 (ARmult_bounded (AR_b y)) x y.

Lemma ARtoCR_preserves_mult x y : ARtoCR (x * y) = ARtoCR x * ARtoCR y.
Proof.
  rewrite ARtoCR_preserves_mult_bounded.
  setoid_replace (AQposAsQpos (AR_b y)) with (CR_b (1 # 1) (ARtoCR y)). 
   reflexivity.
  unfold QposEq. simpl. rewrite AR_b_correct. reflexivity. 
Qed. 
Hint Rewrite ARtoCR_preserves_mult : ARtoCR.

(* The approximate reals form a ring *)
Local Opaque equiv.

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

Local Transparent equiv.
Add Ring CR : (rings.stdlib_ring_theory CR).
Add Ring AR : (rings.stdlib_ring_theory AR).

(* Order *)
Definition ARnonNeg (x : AR) : Prop := ∀ ε : Qpos, (-ε <= '(approximate x ε))%Q.

Lemma ARtoCR_preserves_nonNeg x : ARnonNeg x ↔ CRnonNeg (ARtoCR x).
Proof. reflexivity. Qed.
Hint Resolve ARtoCR_preserves_nonNeg.

Global Instance: Proper ((=) ==> iff) ARnonNeg.
Proof.
  intros x1 x2 E.
  split; intros; apply ARtoCR_preserves_nonNeg; [rewrite <-E | rewrite E]; auto.
Qed.

Definition ARnonPos (x : AR) := ∀ ε : Qpos, ('(approximate x ε) <= ε)%Q.

Lemma ARtoCR_preserves_nonPos x : ARnonPos x ↔ CRnonPos (ARtoCR x).
Proof. reflexivity. Qed.
Hint Resolve ARtoCR_preserves_nonPos.

Global Instance AR_le: Order AR := λ x y, ARnonNeg (y + - x).

Global Instance: Proper ((=) ==> (=) ==> iff) AR_le.
Proof.
  intros x1 x2 E y1 y2 F. unfold AR_le in *.
  now rewrite E F.
Qed.

Lemma ARtoCR_preserves_le x y : x ≤ y ↔ ARtoCR x ≤ ARtoCR y.
Proof.
  unfold precedes, AR_le, CR_le, CRle.
  change (ARnonNeg (y - x) ↔ CRnonNeg (ARtoCR y + -ARtoCR x)).
  rewrite <-rings.preserves_opp.
  now rewrite <-rings.preserves_plus.
Qed.
Hint Resolve ARtoCR_preserves_le.

Global Instance: OrderEmbedding ARtoCR.
Proof.
  repeat (split; try apply _); intros; apply ARtoCR_preserves_le; assumption.
Qed.

Definition ARpos (x : AR) : CProp := sig (λ y : AQ₊, '('y) ≤ x).

Lemma ARtoCR_preserves_pos x : ARpos x IFF CRpos (ARtoCR x).
Proof with auto with qarith.
  split; intros [y E].
   exists (AQposAsQpos y). simpl. rewrite <-ARtoCR_inject.
   apply ARtoCR_preserves_le in E. apply E.
  destruct (aq_lt_mid 0 y) as [z [Ez1 Ez2]]...
  assert (0 < z) as F. apply aq_preserves_lt. aq_preservation...
  exists (exist _ z F). simpl. 
  apply ARtoCR_preserves_le.
  rewrite ARtoCR_inject.
  apply CRle_trans with ('y)%CR...
  apply CRArith.CRle_Qle...
Defined.
Hint Resolve ARtoCR_preserves_pos.

Lemma ARpos_wd : ∀ x1 x2, x1 = x2 → ARpos x1 → ARpos x2.
Proof.
  intros x1 x2 E G.
  apply ARtoCR_preserves_pos.
  apply CRpos_wd with (ARtoCR x1).
   rewrite E. reflexivity.
  apply ARtoCR_preserves_pos. assumption.
Qed.

Global Instance AR_lt: CSOrder AR := λ x y, ARpos (y + -x).

Lemma ARtoCR_preserves_lt x y : x ⋖ y IFF ARtoCR x ⋖ ARtoCR y.
Proof with reflexivity.
  stepl (CRpos (ARtoCR (y + - x))). 
   split; intros; eapply CRpos_wd; eauto. 
    autorewrite with ARtoCR... 
   autorewrite with ARtoCR...
  split; apply ARtoCR_preserves_pos.
Defined.
Hint Resolve ARtoCR_preserves_lt.

Lemma ARlt_wd : ∀ x1 x2 : AR, x1 = x2 → ∀ y1 y2, y1 = y2 → x1 ⋖ y1 → x2 ⋖ y2.
Proof.
  intros x1 x2 E y1 y2 F G. 
  apply ARpos_wd with (y1 + - x1); trivial.
  rewrite E F. reflexivity.
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
  split; apply CRapart_wd; try reflexivity; rewrite ARtoCR_inject rings.preserves_0; reflexivity.
Defined.

Lemma aq_mult_inv_regular_prf x : 
  is_RegularFunction_noInf _ (λ ε : Qpos, app_div 1 x (Qdlog2 ε) : AQ_as_MetricSpace).
Proof.
  intros ε1 ε2. simpl.
  eapply ball_triangle. 
   eapply aq_div_Qdlog2.
  eapply ball_sym, aq_div_Qdlog2.
Qed.

Definition AQinv (x : AQ) : AR := mkRegularFunction (0 : AQ_as_MetricSpace) (aq_mult_inv_regular_prf x).

Definition AQinv_bounded (c : AQ₊) (x : AQ_as_MetricSpace) : AR := AQinv (max ('c) x).

Lemma AQinv_pos_uc_prf (c : AQ₊) : is_UniformlyContinuousFunction 
  (AQinv_bounded c) (Qinv_modulus (AQposAsQpos c)).
Proof.
  intros ε x y E δ1 δ2. simpl in *.
  eapply ball_triangle.
   2: eapply ball_sym, aq_div_Qdlog2.
  eapply ball_triangle.
   eapply aq_div_Qdlog2.
  simpl. aq_preservation. apply Qinv_pos_uc_prf in E.
  rewrite 2!left_identity. apply E.
Qed.

Definition AQinv_pos_uc (c : AQ₊) := Build_UniformlyContinuousFunction (AQinv_pos_uc_prf c).

Definition ARinv_pos (c : AQ₊) : AR --> AR := Cbind AQPrelengthSpace (AQinv_pos_uc c).

Lemma ARtoCR_preserves_inv_pos_aux c (x : AR) : is_RegularFunction_noInf _
   (λ γ, / Qmax (''c) ('(approximate x (Qinv_modulus (AQposAsQpos c) γ))) : Q_as_MetricSpace).
Proof.
  intros ε1 ε2.
  apply_simplified (Qinv_pos_uc_prf (AQposAsQpos c)).
  apply AQball_fold. 
  setoid_replace (Qinv_modulus (AQposAsQpos c) (ε1 + ε2)) 
     with (Qinv_modulus (AQposAsQpos c) ε1 + Qinv_modulus (AQposAsQpos c) ε2).
   apply regFun_prf.
   unfold QposEq. simpl. ring.
Qed.

Lemma ARtoCR_preserves_inv_pos x c : ARtoCR (ARinv_pos c x) = CRinv_pos (AQposAsQpos c) (ARtoCR x).
Proof.
  intros ? ?. apply regFunEq_e. intros ε. 
  simpl. unfold Cjoin_raw. simpl.
  setoid_replace (ε + ε) with ((1#2) * ε + ((1#2) * ε + ε))%Qpos by QposRing.
  eapply ball_triangle.
   apply aq_div_Qdlog2.
  rewrite aq_preserves_max. 
  rewrite rings.preserves_1. rewrite left_identity.
  apply ARtoCR_preserves_inv_pos_aux.
Qed.
Hint Rewrite ARtoCR_preserves_inv_pos : ARtoCR.

Definition ARinv (x : AR) (x_ : (x >< 0)) : AR := 
  match x_ with
  | inl (exist c _) => - (ARinv_pos c) (- x)
  | inr (exist c _) => (ARinv_pos c) x
  end.

Opaque ARtoCR.
Lemma ARtoCR_preserves_inv x x_ x__: ARtoCR (ARinv x x_) = CRinv (ARtoCR x) x__. 
Proof with auto with qarith; try reflexivity.
  unfold ARinv.
  destruct x_ as [Ec | Ec].
   pose proof (fst (ARtoCR_preserves_0_lt _) Ec) as Px.
   rewrite (CRinv_irrelvent _ (inl Px)). 
   unfold CRinv.
   destruct Ec as [c Ec], Px as [d Ed].
   autorewrite with ARtoCR.
   destruct (Qlt_le_dec d (AQposAsQpos c)).
    rewrite (CRinv_pos_weaken d (AQposAsQpos c))...
    simpl. rewrite <-ARtoCR_inject. rewrite <-ARtoCR_preserves_opp.
    apply ARtoCR_preserves_le. 
    rewrite <-(rings.plus_0_l (-x))...
   rewrite (CRinv_pos_weaken (AQposAsQpos c) d)...
   rewrite <-(rings.plus_0_l (-ARtoCR x))...
  pose proof (fst (ARtoCR_preserves_lt_0 _) Ec) as Px.
  rewrite (CRinv_irrelvent _ (inr Px)). 
  unfold CRinv.
  destruct Ec as [c Ec], Px as [d Ed].
  autorewrite with ARtoCR.
  destruct (Qlt_le_dec d (AQposAsQpos c)).
   rewrite (CRinv_pos_weaken d (AQposAsQpos c))...
   simpl. rewrite <-ARtoCR_inject. 
   apply ARtoCR_preserves_le. 
   setoid_replace (x:AR) with (x + -0 : AR)...
   change (x = x + - 0).
   ring.
  rewrite (CRinv_pos_weaken (AQposAsQpos c) d)...
  rewrite <-(rings.plus_0_r (ARtoCR x))...
Qed.
Transparent ARtoCR.

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
  rewrite Ex Ey. 
  now apply CRinv_wd.
Qed.

Lemma ARinv_irrelevent x x_ x__ : ARinv x x_ = ARinv x x__.
Proof. apply ARinv_wd. reflexivity. Qed.

Program Definition AQpower_positive_uc (p : positive) (c : AQ₊) : AQ_as_MetricSpace --> AQ_as_MetricSpace
  := unary_uc inject (λ x : AQ_as_MetricSpace, (AQboundAbs_uc c x) ^ (Npos p) : AQ_as_MetricSpace)
           (Qpower_positive_uc p (AQposAsQpos c)) _.
Next Obligation.
  assert (∀ x : AQ, '(x ^ Npos p) = Qpower_positive ('x) p) as preserves_pow_pos.
   intros y. 
   rewrite nat_pow.preserves_nat_pow.
   now rewrite <-(int_pow.int_pow_nat_pow (f:=Z_of_N)).
  rewrite preserves_pow_pos. aq_preservation. 
Qed.

Definition ARpower_positive_bounded (p : positive) (c : AQ₊) : AR --> AR := Cmap AQPrelengthSpace (AQpower_positive_uc p c).

Lemma ARtoCR_preserves_power_positive_bounded x p c : 
  ARtoCR (ARpower_positive_bounded p c x) = CRpower_positive_bounded p (AQposAsQpos c) (ARtoCR x).
Proof. apply preserves_unary_fun. Qed.

Definition ARpower_positive (p : positive) (x : AR) : AR := ucFun (ARpower_positive_bounded p (AR_b x)) x.

Lemma ARtoCR_preserves_power_positive x p : 
  ARtoCR (ARpower_positive p x) = CRpower_positive p (ARtoCR x).
Proof.
  rewrite ARtoCR_preserves_power_positive_bounded.
  setoid_replace (AQposAsQpos (AR_b x)) with (CR_b (1#1) (ARtoCR x)). 
   reflexivity.
  unfold QposEq. simpl. now rewrite AR_b_correct.
Qed. 
End ARarith.
