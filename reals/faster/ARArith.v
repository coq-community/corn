Require Import 
  Unicode.Utf8
  Program Ring 
  Qabs stdlib_omissions.Q
  QMinMax QposMinMax
  Complete Prelength Qmetric MetricMorphisms ApproximateRationals
  CRGroupOps CRFieldOps CRArith.

Generalizable All Variables.
Set Automatic Introduction.

Section app_rationals_completion.
  Context `{AppRationals AQ f aq_0 aq_1 aq_plus aq_mult aq_opp}
    {min : AppRationalsMin AQ f} 
    {max : AppRationalsMax AQ f} 
    {abs : AppRationalsAbs AQ f} 
    {app_inv : AppRationalsMultInv AQ f}.

  Open Scope uc_scope. 

  Definition AQ_as_MetricSpace := Emetric f.
  Definition AQPrelengthSpace := EPrelengthSpace QPrelengthSpace f.
  Definition AR := Complete AQ_as_MetricSpace.
  Definition ARtoCR_uc : AQ_as_MetricSpace --> Q_as_MetricSpace := metric_embed_uc f.
  Definition ARtoCR : AR --> CR := Eembed QPrelengthSpace f.
  Definition CRtoAR : CR --> AR := Eembed_back QPrelengthSpace f.

  Hint Rewrite aq_preserves_0 : aq_preservation.
  Hint Rewrite aq_preserves_1 : aq_preservation.
  Hint Rewrite aq_preserves_plus : aq_preservation.
  Hint Rewrite aq_preserves_mult : aq_preservation.
  Hint Rewrite aq_preserves_opp : aq_preservation.
  Hint Rewrite aq_preserves_max : aq_preservation.
  Hint Rewrite aq_preserves_min : aq_preservation.
  Hint Rewrite aq_preserves_abs : aq_preservation.
  Ltac aq_preservation := autorewrite with aq_preservation; try reflexivity.

  Lemma AQball_fold ε (x y : AQ_as_MetricSpace) : ball ε x y → Qball ε (f x) (f y).
  Proof. intuition. Qed.

  (* Constants *)
  Definition inject_AQ : AQ → AR := (@Cunit AQ_as_MetricSpace).
  
  Notation "' x" := (inject_AQ x).

  Lemma ARtoCR_inject x : ARtoCR (' x) [=] (inject_Q (f x))%CR.
  Proof. intros ? ?. apply ball_refl. Qed.

  Notation "0" := (' aq_0).
  Lemma ARtoCR_preserves_0 : ARtoCR 0 [=] ('0)%CR.
  Proof. rewrite ARtoCR_inject. aq_preservation. Qed.
  Hint Rewrite ARtoCR_preserves_0 : ARtoCR.

  Notation "1" := (' aq_1).
  Lemma ARtoCR_preserves_1 : ARtoCR 1 [=] ('1)%CR.
  Proof. rewrite ARtoCR_inject. aq_preservation. Qed.
  Hint Rewrite ARtoCR_preserves_1 : ARtoCR.

  (* Plus *)
  Program Definition AQtranslate_uc (x : AQ_as_MetricSpace) 
    := unary_uc f (aq_plus x  : AQ_as_MetricSpace → AQ_as_MetricSpace) (Qtranslate_uc (f x)) _.
  Next Obligation. aq_preservation. Qed.

  Definition ARtranslate (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQtranslate_uc x).
  
  Lemma ARtoCR_preserves_translate x y : ARtoCR (ARtranslate x y) [=] translate (ARtoCR_uc x) (ARtoCR y).
  Proof. apply preserves_unary_fun. Qed.
  Hint Rewrite ARtoCR_preserves_translate : ARtoCR.

  Program Definition AQplus_uc
    := binary_uc f (aq_plus  : AQ_as_MetricSpace →  AQ_as_MetricSpace → AQ_as_MetricSpace) Qplus_uc _.
  Next Obligation. aq_preservation. Qed.

  Definition ARplus : AR --> AR --> AR := Cmap2 AQPrelengthSpace AQPrelengthSpace AQplus_uc.
  Infix "+" := (ucFun2 ARplus).

  Lemma ARtoCR_preserves_plus x y : ARtoCR (x + y) [=] (ARtoCR x + ARtoCR y)%CR.
  Proof. apply preserves_binary_fun. Qed.
  Hint Rewrite ARtoCR_preserves_plus : ARtoCR.

  (* Inverse *)
  Program Definition AQopp_uc
    := unary_uc f (aq_opp : AQ_as_MetricSpace → AQ_as_MetricSpace) Qopp_uc _.
  Next Obligation. aq_preservation.  Qed.
  Definition ARopp : AR --> AR := Cmap AQPrelengthSpace AQopp_uc.
  Notation "- x" := (ARopp x).

  Lemma ARtoCR_preserves_opp x : ARtoCR (- x) [=] CRopp (ARtoCR x).
  Proof. apply preserves_unary_fun. Qed.
  Hint Rewrite ARtoCR_preserves_opp : ARtoCR.

  Infix "-" := (λ x y, x + - y).

  (* Mult *) 
  Program Definition AQboundBelow_uc (x : AQ_as_MetricSpace) : AQ_as_MetricSpace --> AQ_as_MetricSpace 
    := unary_uc f (aq_max x  : AQ_as_MetricSpace → AQ_as_MetricSpace) (QboundBelow_uc (f x)) _.
  Next Obligation. aq_preservation. Qed.

  Definition ARboundBelow (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQboundBelow_uc x).

  Lemma ARtoCR_preserves_boundBelow x y : ARtoCR (ARboundBelow x y) [=] boundBelow (f x) (ARtoCR y).
  Proof. apply preserves_unary_fun. Qed.
  Hint Rewrite ARtoCR_preserves_boundBelow : ARtoCR.

  Program Definition AQboundAbove_uc (x : AQ_as_MetricSpace) : AQ_as_MetricSpace --> AQ_as_MetricSpace 
    := unary_uc f (aq_min x  : AQ_as_MetricSpace → AQ_as_MetricSpace) (QboundAbove_uc (f x)) _.
  Next Obligation. aq_preservation. Qed.
 
  Definition ARboundAbove (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQboundAbove_uc x).

  Lemma ARtoCR_preserves_boundAbove x y : ARtoCR (ARboundAbove x y) [=] boundAbove (f x) (ARtoCR y).
  Proof. apply preserves_unary_fun. Qed.
  Hint Rewrite ARtoCR_preserves_boundAbove : ARtoCR.

  Program Definition AQboundAbs_uc (c : AQpos) : AQ_as_MetricSpace --> AQ_as_MetricSpace 
    := unary_uc f (λ x : AQ_as_MetricSpace, aq_max (aq_opp (AQposAsAQ c)) (aq_min (AQposAsAQ c) x) : AQ_as_MetricSpace)
             (QboundAbs (AQpos2Qpos c)) _.
  Next Obligation. aq_preservation. Qed. 
 
  Definition ARboundAbs (c : AQpos) : AR --> AR := Cmap AQPrelengthSpace (AQboundAbs_uc c).

  Lemma ARtoCR_preserves_bound_abs c x : ARtoCR (ARboundAbs c x) [=] CRboundAbs (AQpos2Qpos c) (ARtoCR x).
  Proof. apply preserves_unary_fun. Qed.
  Hint Rewrite ARtoCR_preserves_bound_abs : ARtoCR.

  Program Definition AQscale_uc (x : AQ_as_MetricSpace) : AQ_as_MetricSpace --> AQ_as_MetricSpace 
    := unary_uc f (aq_mult x  : AQ_as_MetricSpace → AQ_as_MetricSpace) (Qscale_uc (f x)) _.
  Next Obligation. aq_preservation. Qed.
 
  Definition ARscale (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQscale_uc x).

  Lemma ARtoCR_preserves_scale x y : ARtoCR (ARscale x y) [=] scale (f x) (ARtoCR y).
  Proof. apply preserves_unary_fun. Qed.
  Hint Rewrite ARtoCR_preserves_scale : ARtoCR.

  Program Definition AQmult_uc (c : AQpos) : AQ_as_MetricSpace --> AQ_as_MetricSpace --> AQ_as_MetricSpace 
    := binary_uc f (λ x y : AQ_as_MetricSpace, aq_mult x (AQboundAbs_uc c y) : AQ_as_MetricSpace) 
            (Qmult_uc (AQpos2Qpos c)) _.
  Next Obligation. aq_preservation. Qed. 

  Definition ARmult_bounded (c : AQpos) : AR --> AR --> AR 
    := Cmap2 AQPrelengthSpace AQPrelengthSpace (AQmult_uc c).

  Lemma ARtoCR_preserves_mult_bounded x y c : 
    ARtoCR (ARmult_bounded c x y) [=] CRmult_bounded (AQpos2Qpos c) (ARtoCR x) (ARtoCR y).
  Proof. apply preserves_binary_fun. Qed.
  Hint Rewrite ARtoCR_preserves_mult_bounded : ARtoCR.

  Lemma ARtoCR_approximate (x : AR) (ε : Qpos) : f (approximate x ε) = approximate (ARtoCR x) ε.
  Proof. reflexivity. Qed.

  Lemma AR_b_correct (x : AR) :
    f (aq_plus (aq_abs (approximate x (1#1)%Qpos)) aq_1) == Qabs (approximate (ARtoCR x) (1#1)%Qpos) + (1#1)%Qpos.
  Proof. aq_preservation. Qed.

  Program Definition AR_b (x : AR) : AQpos := exist _ (aq_plus (aq_abs (approximate x (1#1)%Qpos)) aq_1) _.
  Next Obligation with auto with qarith.
    apply aq_preserves_lt. rewrite AR_b_correct. aq_preservation.
    apply CR_b_pos.
  Qed.

  Definition ARmult (x y : AR) : AR := ucFun2 (ARmult_bounded (AR_b y)) x y.
  Infix "*" := ARmult.

  Lemma ARtoCR_preserves_mult x y : ARtoCR (x * y) [=] (ARtoCR x * ARtoCR y)%CR.
  Proof.
    rewrite ARtoCR_preserves_mult_bounded.
    setoid_replace (AQpos2Qpos (AR_b y)) with (CR_b (1 # 1) (ARtoCR y)). 
     reflexivity.
    unfold QposEq. simpl. rewrite AR_b_correct. reflexivity. 
  Qed. 
  Hint Rewrite ARtoCR_preserves_mult : ARtoCR.

  Instance: Proper (@st_eq _ ==> @st_eq _ ==> @st_eq _) ARmult. 
  Proof. 
    intros ? ? E1 ? ? E2.
    apply (MetricMorphisms.injective ARtoCR). autorewrite with ARtoCR.
    rewrite E1. rewrite E2. reflexivity.
  Qed. 

  (* The approximate reals form a ring *)
  Lemma AR_ring_theory : @ring_theory AR 0 1 (ucFun2 ARplus) ARmult (λ x y, x + - y) ARopp (@st_eq _).
  Proof. 
    split; repeat intro; apply (MetricMorphisms.injective ARtoCR); autorewrite with ARtoCR; ring.
  Qed.

  Add Ring AR : AR_ring_theory.
  
  (* Order *)
  Definition ARnonNeg (x : AR) : Prop := ∀ ε : Qpos, (-ε <= f (approximate x ε))%Q.
  
  Lemma ARtoCR_preserves_nonNeg x : ARnonNeg x ↔ CRnonNeg (ARtoCR x).
  Proof. reflexivity. Qed.
  Hint Resolve ARtoCR_preserves_nonNeg.

  Global Instance: Proper (@st_eq _ ==> iff) ARnonNeg.
  Proof.
    intros x1 x2 E.
    split; intros; apply ARtoCR_preserves_nonNeg; [rewrite <-E | rewrite E]; auto.
  Qed.
  
  Definition ARnonPos (x : AR) := ∀ ε : Qpos, (f (approximate x ε) <= ε)%Q.

  Lemma ARtoCR_preserves_nonPos x : ARnonPos x ↔ CRnonPos (ARtoCR x).
  Proof. reflexivity. Qed.
  Hint Resolve ARtoCR_preserves_nonPos.

  Definition ARle x y := ARnonNeg (y - x).
  Infix "<=" := ARle.
 
  Global Instance: Proper (@st_eq _ ==> @st_eq _ ==> iff) ARle.
  Proof.
    intros x1 x2 E y1 y2 F. unfold ARle in *.
    rewrite E F. reflexivity.
  Qed.

  Lemma ARtoCR_preserves_le x y : x <= y ↔ (ARtoCR x <= ARtoCR y)%CR.
  Proof.
    unfold ARle, CRle.
    rewrite <-ARtoCR_preserves_opp.
    rewrite <-ARtoCR_preserves_plus.
    reflexivity.
  Qed.
  Hint Resolve ARtoCR_preserves_le.

  Definition ARpos (x : AR) : CProp := sig (λ y : AQpos, ' AQposAsAQ y <= x).

  Lemma ARtoCR_preserves_pos x : ARpos x IFF CRpos (ARtoCR x).
  Proof with auto with qarith.
    split; intros [y E].
     exists (AQpos2Qpos y). simpl. rewrite <-ARtoCR_inject.
     apply ARtoCR_preserves_le in E. apply E.
    destruct (aq_lt_mid 0 y) as [z [Ez1 Ez2]]...
    assert (aq_lt aq_0 z) as F. unfold aq_lt. aq_preservation...
    exists (exist _ z F). simpl. 
    apply ARtoCR_preserves_le.
    rewrite ARtoCR_inject.
    apply CRle_trans with (' y)%CR...
    apply CRle_Qle...
  Defined.
  Hint Resolve ARtoCR_preserves_pos.

  Lemma ARpos_wd : ∀ x1 x2, x1 [=] x2 → ARpos x1 → ARpos x2.
  Proof.
    intros x1 x2 E G.
    apply ARtoCR_preserves_pos.
    apply CRpos_wd with (ARtoCR x1).
     rewrite E. reflexivity.
    apply ARtoCR_preserves_pos. assumption.
  Qed.

  Definition ARlt (x y : AR) : CProp := ARpos (y - x).
  Infix "<" := ARlt.

  Lemma ARtoCR_preserves_lt x y : x < y IFF (ARtoCR x < ARtoCR y)%CR.
  Proof with reflexivity.
    unfold ARlt, CRlt.
    stepl (CRpos (ARtoCR (y + - x))). 
     split; intros; eapply CRpos_wd; eauto. 
      autorewrite with ARtoCR... 
     autorewrite with ARtoCR...
    split; apply ARtoCR_preserves_pos.
  Defined.
  Hint Resolve ARtoCR_preserves_lt.

  Lemma ARlt_wd : ∀ x1 x2, x1 [=] x2 → ∀ y1 y2, y1 [=] y2 → x1 < y1 → x2 < y2.
  Proof.
    intros x1 x2 E y1 y2 F G. unfold ARlt. 
    apply ARpos_wd with (y1 + - x1); trivial.
    rewrite E F. reflexivity.
  Qed.

  Lemma ARtoCR_preserves_lt_0 x : (0 < x) IFF ('0 < ARtoCR x)%CR.
  Proof with eauto; try reflexivity.
    stepl (ARtoCR 0 < ARtoCR x)%CR.
     split; apply CRlt_wd; autorewrite with ARtoCR... 
    split; intros; eapply ARtoCR_preserves_lt...
  Defined.

  Lemma ARtoCR_preserves_0_lt x : (x < 0) IFF (ARtoCR x < '0)%CR.
  Proof with eauto; try reflexivity.
    stepl (ARtoCR x < ARtoCR 0)%CR.
     split; apply CRlt_wd; autorewrite with ARtoCR... 
    split; intros; eapply ARtoCR_preserves_lt...
  Defined.

  (* Apartness *)
  Definition ARapart (x y : AR) : CProp := (x < y or y < x).
  Notation "x >< y" := (ARapart x y).

  Lemma ARtoCR_preserves_apart x y : (x >< y) IFF ((ARtoCR x) >< (ARtoCR y))%CR.
  Proof. 
    split; (intros [|]; [left|right]; apply ARtoCR_preserves_lt; assumption).
  Defined.

  Lemma ARtoCR_preserves_apart_0 x : (x >< 0) IFF ((ARtoCR x) >< '0)%CR.
  Proof.
    stepr (ARtoCR x >< ARtoCR 0)%CR.
     split; apply ARtoCR_preserves_apart. 
    split; apply CRapart_wd; try reflexivity; rewrite ARtoCR_inject aq_preserves_0; reflexivity.
  Defined.

  (* Multiplicative inverse *)
  Lemma aq_mult_inv_regular_prf (x : AQ_as_MetricSpace) : 
    is_RegularFunction_noInf _ (aq_mult_inv x : Qpos → AQ_as_MetricSpace).
  Proof.
    intros ε1 ε2. simpl.
    eapply ball_triangle.
     eapply aq_mult_inv_spec.
    eapply ball_sym, aq_mult_inv_spec.
  Qed.
 
  Definition aq_mult_inv_regular (x : AQ_as_MetricSpace) : AR := 
    mkRegularFunction (aq_0 : AQ_as_MetricSpace) (aq_mult_inv_regular_prf x).

  Lemma AQinv_pos_uc_prf (c : AQpos) : is_UniformlyContinuousFunction 
    (λ x : AQ_as_MetricSpace, aq_mult_inv_regular (aq_max (AQposAsAQ c) x)) (Qinv_modulus (AQpos2Qpos c)).
  Proof.
    intros ε x y E δ1 δ2. simpl in *.
    eapply ball_triangle.
     2: eapply ball_sym, aq_mult_inv_spec.
    eapply ball_triangle.
     eapply aq_mult_inv_spec.
    aq_preservation.
    apply Qinv_pos_uc_prf in E. apply E.
  Qed.

  Definition AQinv_pos_uc (c : AQpos) :=
    Build_UniformlyContinuousFunction (AQinv_pos_uc_prf c).

  Definition ARinv_pos (c : AQpos) : AR --> AR := Cbind AQPrelengthSpace (AQinv_pos_uc c).
 
  Lemma ARtoCR_preserves_inv_pos_aux c (x : AR) : is_RegularFunction_noInf _
     (λ γ, / Qmax (f (AQposAsAQ c)) (f (approximate x (Qinv_modulus (AQpos2Qpos c) γ))) : Q_as_MetricSpace).
  Proof.
    intros ε1 ε2. 
    apply (Qinv_pos_uc_prf (AQpos2Qpos c)).
    apply AQball_fold. 
    setoid_replace (Qinv_modulus (AQpos2Qpos c) (ε1 + ε2))%Qpos 
       with (Qinv_modulus (AQpos2Qpos c) ε1 + Qinv_modulus (AQpos2Qpos c) ε2)%Qpos.
     apply regFun_prf.
     unfold QposEq. simpl. ring.
  Qed.

  Lemma ARtoCR_preserves_inv_pos x c : ARtoCR (ARinv_pos c x) [=] CRinv_pos (AQpos2Qpos c) (ARtoCR x).
  Proof.
    intros ? ?. apply regFunEq_e. intros ε. 
    simpl. unfold Cjoin_raw. simpl.
    setoid_replace (ε + ε)%Qpos with ((1#2) * ε + ((1#2) * ε + ε))%Qpos by QposRing.
    eapply ball_triangle.
     apply aq_mult_inv_spec.
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
  Lemma ARtoCR_preserves_inv x x_ x__: ARtoCR (ARinv x x_) [=] CRinv (ARtoCR x) x__. 
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
      setoid_replace (-x) with (0 + -x) by ring...
     rewrite (CRinv_pos_weaken (AQpos2Qpos c) d)...
     rewrite <-(CRplus_0_l (-ARtoCR x))%CR...
    pose proof (fst (ARtoCR_preserves_lt_0 _) Ec) as Px.
    rewrite (CRinv_irrelvent _ (inr Px)). 
    unfold CRinv.
    destruct Ec as [c Ec], Px as [d Ed].
    autorewrite with ARtoCR.
    destruct (Qlt_le_dec d (AQpos2Qpos c)).
      rewrite (CRinv_pos_weaken d (AQpos2Qpos c))...
      simpl. rewrite <-ARtoCR_inject. 
      apply ARtoCR_preserves_le. 
      setoid_replace x with (x + -0) by ring...
     rewrite (CRinv_pos_weaken (AQpos2Qpos c) d)...
     rewrite <-(CRplus_0_r (ARtoCR x))%CR...
  Qed.
  Transparent ARtoCR.

  Lemma ARtoCR_preserves_inv_l x x_ : {x__ | ARtoCR (ARinv x x_) [=] CRinv (ARtoCR x) x__}.
  Proof.
    exists (fst (ARtoCR_preserves_apart_0 x) x_).
    apply ARtoCR_preserves_inv.
  Qed.

  Lemma ARtoCR_preserves_inv_r x x__ : {x_ | ARtoCR (ARinv x x_) [=] CRinv (ARtoCR x) x__}.
  Proof.
    exists (snd (ARtoCR_preserves_apart_0 x) x__).
    apply ARtoCR_preserves_inv.
  Qed.

  Lemma ARinv_wd x y x_ y_ : x [=] y → ARinv x x_ [=] ARinv y y_.
  Proof.
    intros E. 
    apply (_ : Injective ARtoCR).
    destruct (ARtoCR_preserves_inv_l x x_) as [x__ Ex], (ARtoCR_preserves_inv_l y y_) as [y__ Ey].
    rewrite Ex Ey. 
    apply CRinv_wd. rewrite E. reflexivity.
  Qed.

  Lemma ARinv_irrelevent x x_ x__ : ARinv x x_ [=] ARinv x x__.
  Proof. apply ARinv_wd. reflexivity. Qed.

End app_rationals_completion.
