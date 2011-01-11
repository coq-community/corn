Require Import 
  Program Ring CLogic
  Qabs stdlib_omissions.Q
  QMinMax QposMinMax
  Complete Prelength Qmetric MetricMorphisms ApproximateRationals
  CRGroupOps CRFieldOps CRclasses Qposclasses
  abstract_algebra minmax.

Section app_rationals_completion.
  Context `{AppRationals AQ}
    {abs : AppRationalsAbs AQ}.

  Open Scope uc_scope. 

  Definition AQ_as_MetricSpace := Emetric f.
  Definition AQPrelengthSpace := EPrelengthSpace QPrelengthSpace f.
  Definition AR := Complete AQ_as_MetricSpace.
  Definition ARtoCR_uc : AQ_as_MetricSpace --> Q_as_MetricSpace := metric_embed_uc f.
  Definition ARtoCR : AR --> CR := Eembed QPrelengthSpace f.
  Definition CRtoAR : CR --> AR := Eembed_inverse QPrelengthSpace f.

  Hint Rewrite (rings.preserves_0 (f:=f)) : aq_preservation.
  Hint Rewrite (rings.preserves_1 (f:=f)) : aq_preservation.
  Hint Rewrite (rings.preserves_plus (f:=f)) : aq_preservation.
  Hint Rewrite (rings.preserves_mult (f:=f)) : aq_preservation.
  Hint Rewrite (rings.preserves_opp (f:=f)) : aq_preservation.
  Hint Rewrite aq_preserves_max : aq_preservation.
  Hint Rewrite aq_preserves_min : aq_preservation.
  Hint Rewrite aq_preserves_abs : aq_preservation.
  Ltac aq_preservation := autorewrite with aq_preservation; try reflexivity.

  Lemma AQball_fold ε (x y : AQ_as_MetricSpace) : ball ε x y → Qball ε (f x) (f y).
  Proof. intuition. Qed.

  (* Constants *)
  Global Instance inject_AQ : Inject AQ AR := (@Cunit AQ_as_MetricSpace).
  
  Lemma ARtoCR_inject x : ARtoCR ('x) = '(f x).
  Proof. intros ? ?. apply ball_refl. Qed.

  Global Instance AR_0: RingZero AR := inject_AQ 0.
  Lemma ARtoCR_preserves_0 : ARtoCR 0 = 0.
  Proof. rewrite ARtoCR_inject. aq_preservation. Qed.
  Hint Rewrite ARtoCR_preserves_0 : ARtoCR.

  Global Instance AR_1: RingOne AR := inject_AQ 1.
  Lemma ARtoCR_preserves_1 : ARtoCR 1 = 1.
  Proof. rewrite ARtoCR_inject. aq_preservation. Qed.
  Hint Rewrite ARtoCR_preserves_1 : ARtoCR.

  (* Plus *)
  Program Definition AQtranslate_uc (x : AQ_as_MetricSpace) 
    := unary_uc f ((+) x  : AQ_as_MetricSpace → AQ_as_MetricSpace) (Qtranslate_uc (f x)) _.
  Next Obligation. aq_preservation. Qed.

  Definition ARtranslate (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQtranslate_uc x).
  
  Lemma ARtoCR_preserves_translate x y : ARtoCR (ARtranslate x y) = translate (ARtoCR_uc x) (ARtoCR y).
  Proof. apply preserves_unary_fun. Qed.
  Hint Rewrite ARtoCR_preserves_translate : ARtoCR.

  Program Definition AQplus_uc
    := binary_uc f ((+)  : AQ_as_MetricSpace →  AQ_as_MetricSpace → AQ_as_MetricSpace) Qplus_uc _.
  Next Obligation. aq_preservation. Qed.

  Definition ARplus_uc : AR --> AR --> AR := Cmap2 AQPrelengthSpace AQPrelengthSpace AQplus_uc.
  Global Instance AR_plus: RingPlus AR := ucFun2 ARplus_uc.

  Lemma ARtoCR_preserves_plus x y : ARtoCR (x + y) = ARtoCR x + ARtoCR y.
  Proof. apply preserves_binary_fun. Qed.
  Hint Rewrite ARtoCR_preserves_plus : ARtoCR.

  (* Inverse *)
  Program Definition AQopp_uc
    := unary_uc f (group_inv : AQ_as_MetricSpace → AQ_as_MetricSpace) Qopp_uc _.
  Next Obligation. aq_preservation.  Qed.
  Definition ARopp_uc : AR --> AR := Cmap AQPrelengthSpace AQopp_uc.
  Global Instance AR_opp: GroupInv AR := ARopp_uc.

  Lemma ARtoCR_preserves_opp x : ARtoCR (-x) = -ARtoCR x.
  Proof. apply preserves_unary_fun. Qed.
  Hint Rewrite ARtoCR_preserves_opp : ARtoCR.

  (* Mult *) 
  Program Definition AQboundBelow_uc (x : AQ_as_MetricSpace) : AQ_as_MetricSpace --> AQ_as_MetricSpace 
    := unary_uc f (max x  : AQ_as_MetricSpace → AQ_as_MetricSpace) (QboundBelow_uc (f x)) _.
  Next Obligation. aq_preservation. Qed.

  Definition ARboundBelow (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQboundBelow_uc x).

  Lemma ARtoCR_preserves_boundBelow x y : ARtoCR (ARboundBelow x y) = boundBelow (f x) (ARtoCR y).
  Proof. apply preserves_unary_fun. Qed.
  Hint Rewrite ARtoCR_preserves_boundBelow : ARtoCR.

  Program Definition AQboundAbove_uc (x : AQ_as_MetricSpace) : AQ_as_MetricSpace --> AQ_as_MetricSpace 
    := unary_uc f (min x  : AQ_as_MetricSpace → AQ_as_MetricSpace) (QboundAbove_uc (f x)) _.
  Next Obligation. aq_preservation. Qed.
 
  Definition ARboundAbove (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQboundAbove_uc x).

  Lemma ARtoCR_preserves_boundAbove x y : ARtoCR (ARboundAbove x y) = boundAbove (f x) (ARtoCR y).
  Proof. apply preserves_unary_fun. Qed.
  Hint Rewrite ARtoCR_preserves_boundAbove : ARtoCR.

  Program Definition AQboundAbs_uc (c : AQ₊) : AQ_as_MetricSpace --> AQ_as_MetricSpace 
    := unary_uc f (λ x : AQ_as_MetricSpace, max (-AQposAsAQ c) (min (AQposAsAQ c) x) : AQ_as_MetricSpace)
             (QboundAbs (AQpos2Qpos c)) _.
  Next Obligation. aq_preservation. Qed. 
 
  Definition ARboundAbs (c : AQ₊) : AR --> AR := Cmap AQPrelengthSpace (AQboundAbs_uc c).

  Lemma ARtoCR_preserves_bound_abs c x : ARtoCR (ARboundAbs c x) = CRboundAbs (AQpos2Qpos c) (ARtoCR x).
  Proof. apply preserves_unary_fun. Qed.
  Hint Rewrite ARtoCR_preserves_bound_abs : ARtoCR.

  Program Definition AQscale_uc (x : AQ_as_MetricSpace) : AQ_as_MetricSpace --> AQ_as_MetricSpace 
    := unary_uc f (ring_mult x  : AQ_as_MetricSpace → AQ_as_MetricSpace) (Qscale_uc (f x)) _.
  Next Obligation. aq_preservation. Qed.
 
  Definition ARscale (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQscale_uc x).

  Lemma ARtoCR_preserves_scale x y : ARtoCR (ARscale x y) = scale (f x) (ARtoCR y).
  Proof. apply preserves_unary_fun. Qed.
  Hint Rewrite ARtoCR_preserves_scale : ARtoCR.

  Program Definition AQmult_uc (c : AQ₊) : AQ_as_MetricSpace --> AQ_as_MetricSpace --> AQ_as_MetricSpace 
    := binary_uc f (λ x y : AQ_as_MetricSpace, x * AQboundAbs_uc c y : AQ_as_MetricSpace) 
            (Qmult_uc (AQpos2Qpos c)) _.
  Next Obligation. aq_preservation. Qed. 

  Definition ARmult_bounded (c : AQ₊) : AR --> AR --> AR 
    := Cmap2 AQPrelengthSpace AQPrelengthSpace (AQmult_uc c).

  Lemma ARtoCR_preserves_mult_bounded x y c : 
    ARtoCR (ARmult_bounded c x y) = CRmult_bounded (AQpos2Qpos c) (ARtoCR x) (ARtoCR y).
  Proof. apply preserves_binary_fun. Qed.
  Hint Rewrite ARtoCR_preserves_mult_bounded : ARtoCR.

  Lemma ARtoCR_approximate (x : AR) (ε : Qpos) : f (approximate x ε) = approximate (ARtoCR x) ε.
  Proof. reflexivity. Qed.

  Lemma AR_b_correct (x : AR) :
    f (aq_abs (approximate x (1#1)%Qpos) + 1) = Qabs (approximate (ARtoCR x) (1#1)%Qpos) + (1#1)%Qpos.
  Proof. aq_preservation. Qed.

  Program Definition AR_b (x : AR) : AQ₊ := exist _ (aq_abs (approximate x (1#1)%Qpos) + 1) _.
  Next Obligation with auto with qarith.
    apply aq_preserves_lt. rewrite AR_b_correct. aq_preservation.
    apply CR_b_pos.
  Qed.

  Global Instance AR_mult: RingMult AR := λ x y, ucFun2 (ARmult_bounded (AR_b y)) x y.

  Lemma ARtoCR_preserves_mult x y : ARtoCR (x * y) = ARtoCR x * ARtoCR y.
  Proof.
    rewrite ARtoCR_preserves_mult_bounded.
    setoid_replace (AQpos2Qpos (AR_b y)) with (CR_b (1 # 1) (ARtoCR y)). 
     reflexivity.
    unfold QposEq. simpl. rewrite AR_b_correct. reflexivity. 
  Qed. 
  Hint Rewrite ARtoCR_preserves_mult : ARtoCR.

  Instance: Proper ((=) ==> (=) ==> (=)) AR_mult. 
  Proof. 
    intros ? ? E1 ? ? E2.
    apply (injective ARtoCR). autorewrite with ARtoCR.
    rewrite E1. rewrite E2. reflexivity.
  Qed. 

  (* The approximate reals form a ring *)
  Opaque equiv.
  Add Ring CR : (rings.stdlib_ring_theory CR).

  Global Instance: Ring AR.
  Proof.
    repeat (split; try apply _); repeat intro; apply (injective ARtoCR); autorewrite with ARtoCR; ring.
  Qed.

  Global Instance: Ring_Morphism ARtoCR.
  Proof.
    repeat (split; try apply _); repeat intro; autorewrite with ARtoCR; reflexivity.
  Qed.

  Global Instance: Ring_Morphism CRtoAR.
  Proof.
    change (Ring_Morphism (inverse ARtoCR)). apply _.
  Qed.

  Add Ring AR : (rings.stdlib_ring_theory AR).
  Transparent equiv.

  (* Order *)
  Definition ARnonNeg (x : AR) : Prop := ∀ ε : Qpos, (-ε <= f (approximate x ε))%Q.
  
  Lemma ARtoCR_preserves_nonNeg x : ARnonNeg x ↔ CRnonNeg (ARtoCR x).
  Proof. reflexivity. Qed.
  Hint Resolve ARtoCR_preserves_nonNeg.

  Global Instance: Proper ((=) ==> iff) ARnonNeg.
  Proof.
    intros x1 x2 E.
    split; intros; apply ARtoCR_preserves_nonNeg; [rewrite <-E | rewrite E]; auto.
  Qed.
  
  Definition ARnonPos (x : AR) := ∀ ε : Qpos, (f (approximate x ε) <= ε)%Q.

  Lemma ARtoCR_preserves_nonPos x : ARnonPos x ↔ CRnonPos (ARtoCR x).
  Proof. reflexivity. Qed.
  Hint Resolve ARtoCR_preserves_nonPos.

  Global Instance AR_le: Order AR := λ x y, ARnonNeg (y + - x).

  Global Instance: Proper ((=) ==> (=) ==> iff) AR_le.
  Proof.
    intros x1 x2 E y1 y2 F. unfold AR_le in *.
    rewrite E F. reflexivity.
  Qed.

  Lemma ARtoCR_preserves_le x y : x ≤ y ↔ ARtoCR x ≤ ARtoCR y.
  Proof.
    unfold precedes, AR_le, CR_le, CRle.
    change (ARnonNeg (y - x) ↔ CRnonNeg (ARtoCR y + -ARtoCR x)).
    rewrite <-preserves_inv.
    rewrite <-rings.preserves_plus.
    reflexivity.
  Qed.
  Hint Resolve ARtoCR_preserves_le.

  Global Instance: OrderEmbedding ARtoCR.
  Proof.
    repeat (split; try apply _); intros; apply ARtoCR_preserves_le; assumption.
  Qed.

  Definition ARpos (x : AR) : CProp := sig (λ y : AQ₊, 'AQposAsAQ y ≤ x).

  Lemma ARtoCR_preserves_pos x : ARpos x IFF CRpos (ARtoCR x).
  Proof with auto with qarith.
    split; intros [y E].
     exists (AQpos2Qpos y). simpl. rewrite <-ARtoCR_inject.
     apply ARtoCR_preserves_le in E. apply E.
    destruct (aq_lt_mid 0 y) as [z [Ez1 Ez2]]...
    assert (0 < z) as F. apply aq_preserves_lt. aq_preservation...
    exists (exist _ z F). simpl. 
    apply ARtoCR_preserves_le.
    rewrite ARtoCR_inject.
    apply CRle_trans with (' y)%CR...
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

  (* Multiplicative inverse *)
  Lemma aq_mult_inv_regular_prf (x : {x | x ≠ 0}) : 
    is_RegularFunction_noInf _ (app_mult_inv x : Qpos → AQ_as_MetricSpace).
  Proof.
    intros ε1 ε2. simpl.
    eapply ball_triangle.
     eapply aq_mult_inv.
    eapply ball_sym, aq_mult_inv.
  Qed.
 
  Definition aq_mult_inv_regular (x : {x | x ≠0}) : AR := 
    mkRegularFunction (0 : AQ_as_MetricSpace) (aq_mult_inv_regular_prf x).

  Program Definition aq_mult_inv_bounded (c : AQ₊) (x : AQ_as_MetricSpace) : AR
    := aq_mult_inv_regular (max (AQposAsAQ c) x).
  Next Obligation.
    intros E. destruct c as [c Ec].
    apply (Qle_not_lt (f c) (f 0)).
     rewrite <-E. rewrite aq_preserves_max. simpl. apply Qmax_ub_l.
    apply aq_preserves_lt. assumption.
  Qed.
   
  Lemma AQinv_pos_uc_prf (c : AQ₊) : is_UniformlyContinuousFunction 
    (aq_mult_inv_bounded c) (Qinv_modulus (AQpos2Qpos c)).
  Proof.
    intros ε x y E δ1 δ2. simpl in *.
    eapply ball_triangle.
     2: eapply ball_sym, aq_mult_inv.
    eapply ball_triangle.
     eapply aq_mult_inv.
    simpl. aq_preservation. apply Qinv_pos_uc_prf in E. apply E. 
  Qed.

  Definition AQinv_pos_uc (c : AQ₊) :=
    Build_UniformlyContinuousFunction (AQinv_pos_uc_prf c).

  Definition ARinv_pos (c : AQ₊) : AR --> AR := Cbind AQPrelengthSpace (AQinv_pos_uc c).
 
  Lemma ARtoCR_preserves_inv_pos_aux c (x : AR) : is_RegularFunction_noInf _
     (λ γ, / Qmax (f (AQposAsAQ c)) (f (approximate x (Qinv_modulus (AQpos2Qpos c) γ))) : Q_as_MetricSpace).
  Proof.
    intros ε1 ε2. 
    apply (Qinv_pos_uc_prf (AQpos2Qpos c)).
    apply AQball_fold. 
    setoid_replace (Qinv_modulus (AQpos2Qpos c) (ε1 + ε2)) 
       with (Qinv_modulus (AQpos2Qpos c) ε1 + Qinv_modulus (AQpos2Qpos c) ε2).
     apply regFun_prf.
     unfold QposEq. simpl. ring.
  Qed.

  Lemma ARtoCR_preserves_inv_pos x c : ARtoCR (ARinv_pos c x) = CRinv_pos (AQpos2Qpos c) (ARtoCR x).
  Proof.
    intros ? ?. apply regFunEq_e. intros ε. 
    simpl. unfold Cjoin_raw. simpl.
    setoid_replace (ε + ε) with ((1#2) * ε + ((1#2) * ε + ε))%Qpos by QposRing.
    eapply ball_triangle.
     apply aq_mult_inv.
    rewrite aq_preserves_max. 
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
     destruct (Qlt_le_dec d (AQpos2Qpos c)).
      rewrite (CRinv_pos_weaken d (AQpos2Qpos c))...
      simpl. rewrite <-ARtoCR_inject. rewrite <-ARtoCR_preserves_opp.
      apply ARtoCR_preserves_le. 
      rewrite <-(rings.plus_0_l (-x))...
     rewrite (CRinv_pos_weaken (AQpos2Qpos c) d)...
     rewrite <-(rings.plus_0_l (-ARtoCR x))...
    pose proof (fst (ARtoCR_preserves_lt_0 _) Ec) as Px.
    rewrite (CRinv_irrelvent _ (inr Px)). 
    unfold CRinv.
    destruct Ec as [c Ec], Px as [d Ed].
    autorewrite with ARtoCR.
    destruct (Qlt_le_dec d (AQpos2Qpos c)).
      rewrite (CRinv_pos_weaken d (AQpos2Qpos c))...
      simpl. rewrite <-ARtoCR_inject. 
      apply ARtoCR_preserves_le. 
      setoid_replace (x:AR) with (x + -0 : AR)...
      change (x = x + - 0).
      ring.
     rewrite (CRinv_pos_weaken (AQpos2Qpos c) d)...
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
    apply (_ : Injective ARtoCR).
    destruct (ARtoCR_preserves_inv_l x x_) as [x__ Ex], (ARtoCR_preserves_inv_l y y_) as [y__ Ey].
    rewrite Ex Ey. 
    apply CRinv_wd. rewrite E. reflexivity.
  Qed.

  Lemma ARinv_irrelevent x x_ x__ : ARinv x x_ = ARinv x x__.
  Proof. apply ARinv_wd. reflexivity. Qed.

End app_rationals_completion.
