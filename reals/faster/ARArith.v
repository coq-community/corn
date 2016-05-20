Require Import 
  Coq.Program.Program Coq.setoid_ring.Ring CoRN.logic.CLogic
  Coq.QArith.Qabs CoRN.stdlib_omissions.Q MathClasses.misc.workaround_tactics
  CoRN.model.totalorder.QMinMax CoRN.model.totalorder.QposMinMax CoRN.util.Qdlog
  CoRN.metric2.Complete CoRN.metric2.Prelength CoRN.model.metric2.Qmetric CoRN.metric2.MetricMorphisms 
  CoRN.reals.fast.CRArith CoRN.reals.fast.CRpower CoRN.classes.Qposclasses
  MathClasses.implementations.stdlib_binary_naturals MathClasses.orders.minmax MathClasses.implementations.positive_semiring_elements.
Require Export
  CoRN.reals.faster.ApproximateRationals
  CoRN.reals.faster.AQmetric.

Section ARarith.
Context `{AppRationals AQ}.

Add Ring AQ : (rings.stdlib_ring_theory AQ).
Add Ring Z : (rings.stdlib_ring_theory Z).

Open Local Scope uc_scope. 
Local Opaque regFunEq.

Hint Rewrite (rings.preserves_0 (f:=cast AQ Q)) : aq_preservation.
Hint Rewrite (rings.preserves_1 (f:=cast AQ Q)) : aq_preservation.
Hint Rewrite (rings.preserves_plus (f:=cast AQ Q)) : aq_preservation.
Hint Rewrite (rings.preserves_mult (f:=cast AQ Q)) : aq_preservation.
Hint Rewrite (rings.preserves_negate (f:=cast AQ Q)) : aq_preservation.
Hint Rewrite aq_preserves_max : aq_preservation.
Hint Rewrite aq_preserves_min : aq_preservation.
Hint Rewrite (abs.preserves_abs (f:=cast AQ Q)): aq_preservation.
Ltac aq_preservation := autorewrite with aq_preservation; try reflexivity.
Local Obligation Tactic := program_simpl; aq_preservation.

(* Compress *)
Lemma aq_approx_regular_prf (x : AQ) : 
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
   apply_simplified (aq_approx_dlog2 (approximate x ((1 # 2) * ε)%Qpos) ((1#2) * ε)%Qpos).
  apply regFun_prf.
Qed.

(* Constants *)
Global Instance inject_PosAQ_AR: Cast (AQ₊) AR := (cast AQ AR ∘ cast (AQ₊) AQ)%prg.
Global Instance inject_Z_AR: Cast Z AR := (cast AQ AR ∘ cast Z AQ)%prg.

Lemma ARtoCR_inject (x : AQ) : cast AR CR (cast AQ AR x) = cast Q CR (cast AQ Q x).
Proof. apply: regFunEq_e. intros ε. apply ball_refl. Qed.

Global Instance AR0: Zero AR := cast AQ AR 0.
Lemma ARtoCR_preserves_0 : cast AR CR 0 = 0.
Proof. unfold "0", AR0. rewrite ARtoCR_inject. aq_preservation. Qed.
Hint Rewrite ARtoCR_preserves_0 : ARtoCR.

Global Instance AR1: One AR := cast AQ AR 1.
Lemma ARtoCR_preserves_1 : cast AR CR 1 = 1.
Proof. unfold "1", AR1. rewrite ARtoCR_inject. aq_preservation. Qed.
Hint Rewrite ARtoCR_preserves_1 : ARtoCR.

(* Plus *)
Program Definition AQtranslate_uc (x : AQ_as_MetricSpace) := unary_uc 
  (cast AQ Q_as_MetricSpace)
  ((x +) : AQ_as_MetricSpace → AQ_as_MetricSpace) (Qtranslate_uc ('x)) _.
Definition ARtranslate (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQtranslate_uc x).

Lemma ARtoCR_preserves_translate x y : 'ARtranslate x y = translate ('x) ('y).
Proof. apply preserves_unary_fun. Qed.
Hint Rewrite ARtoCR_preserves_translate : ARtoCR.

Program Definition AQplus_uc := binary_uc
  (cast AQ Q_as_MetricSpace) 
  ((+) : AQ_as_MetricSpace →  AQ_as_MetricSpace → AQ_as_MetricSpace) Qplus_uc _.

Definition ARplus_uc : AR --> AR --> AR := Cmap2 AQPrelengthSpace AQPrelengthSpace AQplus_uc.
Global Instance ARplus: Plus AR := ucFun2 ARplus_uc.

Lemma ARtoCR_preserves_plus x y : cast AR CR (x + y) = 'x + 'y.
Proof. apply preserves_binary_fun. Qed.
Hint Rewrite ARtoCR_preserves_plus : ARtoCR.

(* Inverse *)
Program Definition AQopp_uc := unary_uc (cast AQ Q_as_MetricSpace)  ((-) : AQ → AQ) Qopp_uc _.
Definition ARopp_uc : AR --> AR := Cmap AQPrelengthSpace AQopp_uc.
Global Instance ARopp: Negate AR := ARopp_uc.

Lemma ARtoCR_preserves_opp x : cast AR CR (-x) = -'x.
Proof. apply preserves_unary_fun. Qed.
Hint Rewrite ARtoCR_preserves_opp : ARtoCR.

(* Mult *) 
Program Definition AQboundBelow_uc (x : AQ_as_MetricSpace) : 
    AQ_as_MetricSpace --> AQ_as_MetricSpace := 
  unary_uc (cast AQ Q_as_MetricSpace)
  ((x ⊔) : AQ_as_MetricSpace → AQ_as_MetricSpace) (QboundBelow_uc ('x)) _.
  
Definition ARboundBelow (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQboundBelow_uc x).

Lemma ARtoCR_preserves_boundBelow x y : 'ARboundBelow x y = boundBelow ('x) ('y).
Proof. apply preserves_unary_fun. Qed.
Hint Rewrite ARtoCR_preserves_boundBelow : ARtoCR.

Program Definition AQboundAbove_uc (x : AQ_as_MetricSpace) : 
    AQ_as_MetricSpace --> AQ_as_MetricSpace := unary_uc 
  (cast AQ Q_as_MetricSpace)
  ((x ⊓) : AQ_as_MetricSpace → AQ_as_MetricSpace) (QboundAbove_uc ('x)) _.

Definition ARboundAbove (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQboundAbove_uc x).

Lemma ARtoCR_preserves_boundAbove x y : 'ARboundAbove x y = boundAbove ('x) ('y).
Proof. apply preserves_unary_fun. Qed.
Hint Rewrite ARtoCR_preserves_boundAbove : ARtoCR.

Program Definition AQboundAbs_uc (c : AQ₊) : 
    AQ_as_MetricSpace --> AQ_as_MetricSpace := unary_uc 
  (cast AQ Q_as_MetricSpace) 
  (λ x : AQ_as_MetricSpace, (-'c) ⊔ (('c) ⊓ x) : AQ_as_MetricSpace) (QboundAbs ('c)) _.

Definition ARboundAbs (c : AQ₊) : AR --> AR := Cmap AQPrelengthSpace (AQboundAbs_uc c).

Lemma ARtoCR_preserves_bound_abs c x : 'ARboundAbs c x = CRboundAbs ('c) ('x).
Proof. apply preserves_unary_fun. Qed.
Hint Rewrite ARtoCR_preserves_bound_abs : ARtoCR.

Program Definition AQscale_uc (x : AQ_as_MetricSpace) : 
    AQ_as_MetricSpace --> AQ_as_MetricSpace := unary_uc 
  (cast AQ Q_as_MetricSpace)
  ((x *.)  : AQ_as_MetricSpace → AQ_as_MetricSpace) (Qscale_uc ('x)) _.

Definition ARscale (x : AQ_as_MetricSpace) : AR --> AR := Cmap AQPrelengthSpace (AQscale_uc x).

Lemma ARtoCR_preserves_scale x y : 'ARscale x y = scale ('x) ('y).
Proof. apply preserves_unary_fun. Qed.
Hint Rewrite ARtoCR_preserves_scale : ARtoCR.

Program Definition AQmult_uc (c : AQ₊) : 
    AQ_as_MetricSpace --> AQ_as_MetricSpace --> AQ_as_MetricSpace := binary_uc 
  (cast AQ Q_as_MetricSpace)
  (λ x y : AQ_as_MetricSpace, x * AQboundAbs_uc c y : AQ_as_MetricSpace) (Qmult_uc ('c)) _.

Definition ARmult_bounded (c : AQ₊) : AR --> AR --> AR 
  := Cmap2 AQPrelengthSpace AQPrelengthSpace (AQmult_uc c).

Lemma ARtoCR_preserves_mult_bounded x y c : 
  'ARmult_bounded c x y = CRmult_bounded ('c) ('x) ('y).
Proof. apply @preserves_binary_fun. Qed.
Hint Rewrite ARtoCR_preserves_mult_bounded : ARtoCR.

Lemma ARtoCR_approximate (x : AR) (ε : Qpos) : '(approximate x ε) = approximate ('x) ε.
Proof. reflexivity. Qed.

Lemma AR_b_correct (x : AR) :
  cast AQ Q (abs (approximate x (1#1)%Qpos) + 1) = Qabs (approximate (cast AR CR x) (1#1)%Qpos) + (1#1)%Qpos.
Proof. aq_preservation. Qed.

Program Definition AR_b (x : AR) : AQ₊ := exist _ (abs (approximate x (1#1)%Qpos) + 1) _.
Next Obligation.
  apply (strictly_order_reflecting (cast AQ Q)). 
  rewrite AR_b_correct. aq_preservation.
  apply CR_b_pos.
Qed.

Global Instance ARmult: Mult AR := λ x y, ARmult_bounded (AR_b y) x y.

Lemma ARtoCR_preserves_mult x y : cast AR CR (x * y) = 'x * 'y.
Proof.
  unfold "*", ARmult at 1. rewrite ARtoCR_preserves_mult_bounded.
  setoid_replace ('AR_b y : Qpos) with (CR_b (1 # 1) ('y)). 
   reflexivity.
  unfold QposEq. simpl.
  now rewrite ARtoCR_approximate, <-AR_b_correct.
Qed.

Lemma ARmult_scale (x : AQ) (y : AR) :
  'x * y = ARscale x y.
Proof.
  apply (injective (cast AR CR)).
  rewrite ARtoCR_preserves_mult, ARtoCR_preserves_scale, ARtoCR_inject.
  now apply CRmult_scale.
Qed.

Hint Rewrite ARtoCR_preserves_mult : ARtoCR.

(* The approximate reals form a ring *)
Instance: Ring AR.
Proof.
  apply (rings.projected_ring (cast AR CR)).
      exact ARtoCR_preserves_plus.
     exact ARtoCR_preserves_0.
    exact ARtoCR_preserves_mult.
   exact ARtoCR_preserves_1.
  exact ARtoCR_preserves_opp.
Qed.

Instance: SemiRing_Morphism (cast AR CR).
Proof.
  repeat (split; try apply _).
     exact ARtoCR_preserves_plus.
    exact ARtoCR_preserves_0.
   exact ARtoCR_preserves_mult.
  exact ARtoCR_preserves_1.
Qed.

Instance: SemiRing_Morphism (cast CR AR).
Proof. change (SemiRing_Morphism (inverse (cast AR CR))). split; apply _. Qed.

Instance: SemiRing_Morphism (cast AQ AR).
Proof.
  repeat (split; try apply _); intros; try reflexivity.
   apply: regFunEq_e. intros ε. now apply ball_refl. 
  rewrite ARmult_scale. apply: regFunEq_e. intros ε. now apply ball_refl.
Qed.

Add Ring CR : (rings.stdlib_ring_theory CR).
Add Ring AR : (rings.stdlib_ring_theory AR).

(* Non strict order *) 
Definition ARnonNeg (x : AR) : Prop := ∀ ε : Qpos, -cast Qpos Q ε ≤ cast AQ Q (approximate x ε).

Lemma ARtoCR_preserves_nonNeg x : ARnonNeg x ↔ CRnonNeg ('x).
Proof. reflexivity. Qed. 
Hint Resolve ARtoCR_preserves_nonNeg.

Global Instance: Proper ((=) ==> iff) ARnonNeg.
Proof.
  intros x1 x2 E.
  split; intros; apply ARtoCR_preserves_nonNeg; [rewrite <-E | rewrite E]; auto.
Qed.

Global Instance ARle: Le AR := λ x y, ARnonNeg (y - x).

Global Instance: Proper ((=) ==> (=) ==> iff) ARle.
Proof. unfold ARle. solve_proper. Qed.

Lemma ARtoCR_preserves_le (x y : AR) : x ≤ y ↔ ' x ≤ ' y.
Proof.
  unfold le, ARle, CRle.
  now rewrite ARtoCR_preserves_nonNeg, rings.preserves_minus.
Qed.

Instance: PartialOrder ARle.
Proof.
  apply (maps.projected_partial_order (cast AR CR)).
  apply ARtoCR_preserves_le.
Qed.

Global Instance: OrderEmbedding ARtoCR.
Proof. repeat (split; try apply _); apply ARtoCR_preserves_le. Qed.

(* Strict order in Type *)
Global Instance: OrderEmbedding (cast AQ AR).
Proof.
  repeat (split; try apply _); intros x y E.
   apply (order_reflecting (cast AR CR)).
   rewrite 2!ARtoCR_inject.
   now do 2 apply (order_preserving _).
  apply (order_reflecting (cast AQ Q)).
  apply (order_reflecting (cast Q CR)).
  rewrite <-2!ARtoCR_inject.
  now apply (order_preserving _).
Qed.

Definition ARpos (x : AR) : Type := sig (λ y : AQ₊, 'y ≤ x).

Program Definition ARpos_char (ε : AQ₊) (x : AR) 
  (Pε : 'ε ≤ approximate x ((1#2) * 'ε)%Qpos) : ARpos x := Pos_shiftl ε (-1 : Z) ↾ _.
Next Obligation.
  intros δ.
  change (-('δ : Q) ≤ '(approximate x ((1 # 2) * δ)%Qpos - ('ε : AQ) ≪ (-1))).
  transitivity (-'((1 # 2) * δ)%Qpos).
   apply rings.flip_le_negate.
   change ((1 # 2) * δ ≤ δ).
   rewrite <-(rings.mult_1_l (δ:Q)) at 2.
   now apply (order_preserving (.* (δ:Q))).
  apply rings.flip_nonneg_minus.
  transitivity ('approximate x ((1#2) * 'ε)%Qpos - 'ε : Q).
   apply (order_preserving (cast AQ Q)) in Pε.
   now apply rings.flip_nonneg_minus.
  apply rings.flip_le_minus_l.
  transitivity (((1 # 2) * 'ε + (1 # 2) * δ) + 'approximate x ((1 # 2) * δ)%Qpos).
   apply rings.flip_le_minus_l.
   now destruct (regFun_prf x ((1#2) * 'ε)%Qpos ((1#2) * δ)%Qpos).
  rewrite rings.preserves_minus, aq_shift_opp_1.
  apply orders.eq_le.
  change ((1 # 2) * 'ε + (1 # 2) * δ + 'approximate x ((1 # 2) * δ)%Qpos ==
    'approximate x ((1 # 2) * δ)%Qpos - 'ε * (1#2) - - ((1 # 2) * δ) + 'ε)%Q. ring.
Qed.

Lemma ARtoCR_preserves_pos x : ARpos x IFF CRpos ('x).
Proof with auto with qarith.
  split; intros [y E].
   exists (cast (AQ₊) (Q₊) y).
   change (cast Q CR (cast AQ Q (cast (AQ₊) AQ y)) ≤ cast AR CR x). 
   rewrite <-ARtoCR_inject.
   now apply (order_preserving _).
  destruct (aq_lt_mid 0 y) as [z [Ez1 Ez2]]...
  assert (0 < z) as F. 
   apply (strictly_order_reflecting (cast AQ Q)). now aq_preservation...
  exists (exist _ z F). simpl.
  change (cast AQ AR (cast (AQ₊) AQ (z ↾ F)) ≤ x).
  apply (order_reflecting (cast AR CR)).
  rewrite ARtoCR_inject.
  transitivity (cast Q CR (cast Qpos Q y)); trivial.
  apply CRArith.CRle_Qle...
Defined.

Lemma ARpos_wd : ∀ x1 x2, x1 = x2 → ARpos x1 → ARpos x2.
Proof.
  intros x1 x2 E G.
  apply ARtoCR_preserves_pos.
  apply CRpos_wd with ('x1).
   now rewrite E.
  now apply ARtoCR_preserves_pos.
Qed.

Definition ARltT: AR → AR → Type := λ x y, ARpos (y - x).

Lemma ARtoCR_preserves_ltT x y : ARltT x y IFF CRltT ('x) ('y).
Proof.
  stepl (CRpos ('(y - x))). 
   split; intros; eapply CRpos_wd; eauto. 
    now autorewrite with ARtoCR.
   now autorewrite with ARtoCR.
  now split; apply ARtoCR_preserves_pos.
Defined.

Lemma ARltT_wd : ∀ x1 x2 : AR, x1 = x2 → ∀ y1 y2, y1 = y2 → ARltT x1 y1 → ARltT x2 y2.
Proof.
  intros x1 x2 E y1 y2 F G. 
  apply ARpos_wd with (y1 + - x1); trivial.
  rewrite E, F. reflexivity.
Qed.

(* Apartness in Type *)
Definition ARapartT: AR → AR → Type := λ x y, ARltT x y or ARltT y x.

Lemma ARtoCR_preserves_apartT x y : ARapartT x y IFF CRapartT ('x) ('y).
Proof. split; (intros [|]; [left|right]; now apply ARtoCR_preserves_ltT). Defined.

Lemma ARtoCR_preserves_apartT_0 x : ARapartT x 0 IFF CRapartT ('x) 0.
Proof.
  stepr (CRapartT ('x) (cast AR CR 0)).
   split; apply ARtoCR_preserves_apartT.
  split; apply CRapartT_wd; try rewrite ARtoCR_preserves_0; reflexivity.
Defined.

(* Strict order in Prop *)

(* Yields Gt if x is certainly greater than 2 ^ k, Lt if x is certainly greater than -2 ^ k, 
  Eq otherwise. *)
Definition AR_epsilon_sign_dec (k : Z) (x : AR) : comparison :=
  let ε : AQ₊ := Pos_shiftl 1 k in
  let z : AQ := approximate x ((1#2) * 'ε)%Qpos in
  if decide_rel (≤) ('ε) z 
    then Gt 
    else if decide_rel (≤) z (-'ε) then Datatypes.Lt else Eq.

Program Definition AR_epsilon_sign_dec_pos (x : AR)
  (k : Z) (Pk : AR_epsilon_sign_dec k x ≡ Gt) : ARpos x := ARpos_char (Pos_shiftl 1 k) x _.
Next Obligation.
  revert Pk. unfold AR_epsilon_sign_dec.
  case (decide_rel (≤)); [ intros; assumption |].
  case (decide_rel (≤)); discriminate.
Qed.

Program Definition AR_epsilon_sign_dec_neg (x : AR)
  (k : Z) (Pk : AR_epsilon_sign_dec k x ≡ Datatypes.Lt) : ARpos (-x) := ARpos_char (Pos_shiftl 1 k) (-x) _.
Next Obligation.
  revert Pk. unfold AR_epsilon_sign_dec.
  case (decide_rel (≤)); [discriminate |].
  case (decide_rel (≤)); [| discriminate].
  intros. apply rings.flip_le_negate.
  now rewrite rings.negate_involutive.
Qed.

Definition AR_epsilon_sign_dec_apartT (x y : AR)
  (k : Z) (Pk : ¬AR_epsilon_sign_dec k (x - y) ≡ Eq) : ARapartT x y.
Proof.
  revert Pk.
  case_eq (AR_epsilon_sign_dec k (x - y)); intros E ?.
    now destruct Pk.
   left. apply ARpos_wd with (-(x - y)).
    ring.
   now apply AR_epsilon_sign_dec_neg with k.
  right. now apply AR_epsilon_sign_dec_pos with k.
Defined.

Lemma AR_epsilon_sign_dec_Gt (k : Z) (x : AR) : 
  1 ≪ k ≤ approximate x (Qpos_mult (1#2) ('Pos_shiftl (1:AQ₊) k)) → AR_epsilon_sign_dec k x ≡ Gt.
Proof.
  intros.
  unfold AR_epsilon_sign_dec.
  case (decide_rel _); intuition.
Qed.

Lemma AR_epsilon_sign_dec_pos_rev (x : AR) (k : Z) :
  cast AQ AR (1 ≪ (1 + k)) ≤ x → AR_epsilon_sign_dec k x ≡ Gt.
Proof.
  intros E.
  apply AR_epsilon_sign_dec_Gt.
  apply (order_reflecting (+ -1 ≪ (1 + k))).
  transitivity (-1 ≪ k).
   apply orders.eq_le.
   rewrite (commutativity _ k), shiftl.shiftl_exp_plus, shiftl.shiftl_1. 
   rewrite rings.plus_mult_distr_r, rings.mult_1_l.
   rewrite rings.negate_plus_distr, associativity, rings.plus_negate_r.  simpl. ring.
  apply (order_reflecting (cast AQ Q)).
  rewrite rings.preserves_negate.
  exact (E ('Pos_shiftl (1 : AQ₊) k)).
Qed.

(* Hack: we write [-1 - cast nat Z n] instead of [cast nat Z n] because
   approximate is not Proper. *)
Global Instance ARlt: Lt AR := λ x y, 
  ∃ n : nat, AR_epsilon_sign_dec (-1 - cast nat Z n) (y - x) ≡ Gt.

Lemma AR_lt_ltT x y : x < y IFF ARltT x y.
Proof.
  split.
   intros E.
   apply ConstructiveEpsilon.constructive_indefinite_description_nat in E. 
    destruct E as [n En].
    now apply AR_epsilon_sign_dec_pos with (-1 - cast nat Z n).
   intros. now apply comparison_eq_dec.
  intros [ε Eε].
  exists (Z.nat_of_Z (-Qdlog2 ('ε))).
  apply AR_epsilon_sign_dec_pos_rev.
  transitivity ('ε : AR); [| assumption].
  rapply (order_preserving (cast AQ AR)).
  apply (order_reflecting (cast AQ Q)).
  rewrite aq_shift_correct, rings.preserves_1, rings.mult_1_l.
  destruct (decide (('ε : Q) ≤ 1)).
   rewrite Z.nat_of_Z_nonneg.
    mc_setoid_replace (1 + (-1 - - Qdlog2 ('ε))) with (Qdlog2 ('ε)) by ring.
    apply Qdlog2_spec.
    apply semirings.preserves_pos.
    now destruct ε.
   change (0 ≤ -Qdlog2 ('ε)).
   apply rings.flip_nonpos_negate.
   now apply Qdlog2_nonpos.
  rewrite Z.nat_of_Z_nonpos.
   now apply orders.le_flip.
  change (-Qdlog2 ('ε) ≤ 0).
  apply rings.flip_nonneg_negate.
  apply Qdlog2_nonneg.
  now apply orders.le_flip.
Qed.

Instance: Proper ((=) ==> (=) ==> iff) ARlt.
Proof. split; intro E; apply AR_lt_ltT; apply AR_lt_ltT in E; 
  eapply ARltT_wd; eauto; now symmetry. Qed.

(* Apartness in Prop *)
Global Instance ARapart: Apart AR := λ x y, x < y ∨ y < x.

Lemma ARtoCR_preserves_lt (x y : AR) : x < y ↔ 'x < 'y.
Proof.
  split; intros E.  
   now apply CR_lt_ltT, ARtoCR_preserves_ltT, AR_lt_ltT.
  now apply AR_lt_ltT, ARtoCR_preserves_ltT, CR_lt_ltT.
Qed.

Lemma AR_apart_apartT x y : x ≶ y IFF ARapartT x y.
Proof.
  split.
   intros E.
   set (f (n : nat) := AR_epsilon_sign_dec (-1 - cast nat Z n)).
   assert (∃ n, f n (y - x) ≡ Gt ∨ f n (x - y) ≡ Gt) as E2.
    now destruct E as [[n En] | [n En]]; exists n; [left | right].
   apply ConstructiveEpsilon.constructive_indefinite_description_nat in E2.
    destruct E2 as [n E2].
    destruct (comparison_eq_dec (f n (y - x)) Gt) as [En|En].
     left. now apply AR_epsilon_sign_dec_pos with (-1 - cast nat Z n). 
    right. apply AR_epsilon_sign_dec_pos with (-1 - cast nat Z n).
    destruct E2; tauto.
   intros n. 
   destruct (comparison_eq_dec (f n (y - x)) Gt); auto.
   destruct (comparison_eq_dec (f n (x - y)) Gt); tauto.
  intros [E|E].
   left. now apply AR_lt_ltT.
  right. now apply AR_lt_ltT.
Qed.

Let ARtoCR_preserves_apart x y : x ≶ y ↔ cast AR CR x ≶ cast AR CR y.
Proof.
  unfold apart, ARapart, CRapart.
  now rewrite !ARtoCR_preserves_lt.
Qed.

Instance: StrongSetoid AR.
Proof.
  apply (strong_setoids.projected_strong_setoid (cast AR CR)).
   split; intros E; [now rewrite E | now apply (injective (cast AR CR))].
  now apply ARtoCR_preserves_apart.
Qed.

Instance: StrongSetoid_Morphism (cast AR CR).
Proof. split; try apply _; now apply ARtoCR_preserves_apart. Qed.

Global Instance: StrongInjective (cast AR CR).
Proof. split; try apply _; now apply ARtoCR_preserves_apart. Qed.

Global Instance: StrongSemiRing_Morphism (cast AR CR).
Proof. split; try apply _. Qed.

Global Instance: StrongSemiRing_Morphism (cast AQ AR).
Proof.
  repeat (split; try apply _). intros.
  apply (strong_extensionality (cast AQ Q)).
  apply (strong_extensionality (cast Q CR)).
  rewrite <-2!ARtoCR_inject.
  now apply (strong_injective _).
Qed.

Global Instance: StrongInjective (cast AQ AR).
Proof.
  repeat (split; try apply _). intros.
  apply (strong_extensionality (cast AR CR)).
  rewrite 2!ARtoCR_inject.
  apply (strong_injective _).
  now apply (strong_injective _).
Qed.

Global Instance: FullPseudoSemiRingOrder ARle ARlt.
Proof. 
  apply (rings.projected_full_pseudo_ring_order (cast AR CR)).
   apply ARtoCR_preserves_le.
  apply ARtoCR_preserves_lt.
Qed.

Global Instance: StrictOrderEmbedding (cast AR CR).
Proof. repeat (split; try apply _); apply ARtoCR_preserves_lt. Qed.

(* Division *)
Lemma aq_mult_inv_regular_prf (x : AQ) : 
  is_RegularFunction_noInf _ (λ ε : Qpos, app_div 1 x (Qdlog2 ε) : AQ_as_MetricSpace).
Proof.
  intros ε1 ε2. simpl.
  eapply ball_triangle. 
   now eapply aq_div_dlog2.
  now eapply ball_sym, aq_div_dlog2.
Qed.

Definition AQinv (x : AQ) : AR := mkRegularFunction (0 : AQ_as_MetricSpace) (aq_mult_inv_regular_prf x).

Definition AQinv_bounded (c : AQ₊) (x : AQ_as_MetricSpace) : AR := AQinv (('c) ⊔ x).

Lemma AQinv_pos_uc_prf (c : AQ₊) : is_UniformlyContinuousFunction 
  (AQinv_bounded c) (Qinv_modulus ('c)).
Proof.
  intros ε x y E δ1 δ2. simpl in *.
  eapply ball_triangle.
   2: now eapply ball_sym, aq_div_dlog2.
  eapply ball_triangle.
   now eapply aq_div_dlog2.
  simpl. aq_preservation. apply Qinv_pos_uc_prf in E.
  rewrite 2!left_identity.
  apply E.
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
   now apply regFun_prf.
  unfold QposEq. simpl. ring.
Qed.

Lemma ARtoCR_preserves_inv_pos x c : 'ARinv_pos c x = CRinv_pos ('c) ('x).
Proof.
  apply: regFunEq_e. intros ε. 
  simpl. unfold Cjoin_raw. simpl.
  setoid_replace (ε + ε) with ((1#2) * ε + ((1#2) * ε + ε))%Qpos by QposRing.
  eapply ball_triangle.
   now apply aq_div_dlog2.
  rewrite aq_preserves_max. 
  rewrite rings.preserves_1. rewrite left_identity.
  now apply ARtoCR_preserves_inv_pos_aux.
Qed.
Hint Rewrite ARtoCR_preserves_inv_pos : ARtoCR.

Definition ARinvT (x : AR) (x_ : ARapartT x 0) : AR := 
  match x_ with
  | inl (exist _ c _) => - ARinv_pos c (- x)
  | inr (exist _ c _) => ARinv_pos c x
  end.

Lemma ARtoCR_preserves_invT x x_ x__: 
  'ARinvT x x_ = CRinvT ('x) x__. 
Proof with auto with qarith; try reflexivity.
  unfold ARinvT.
  destruct x_ as [Ec | Ec].
   assert (CRltT ('x) 0) as Px.
    apply CRltT_wd with ('x) (cast AR CR 0).
      reflexivity.
     now apply rings.preserves_0.
    now apply ARtoCR_preserves_ltT.
   rewrite (CRinvT_irrelevant _ (inl Px)). 
   unfold CRinvT.
   destruct Ec as [c Ec], Px as [d Ed].
   autorewrite with ARtoCR.
   destruct (Qlt_le_dec d ('c : Qpos)).
    rewrite (CRinv_pos_weaken d ('c))...
    change (cast Q CR (cast AQ Q (cast (AQ₊) AQ c)) ≤ -cast AR CR x).
    rewrite <-ARtoCR_inject, <-rings.preserves_negate.
    apply (order_preserving _).
    rewrite <-(rings.plus_0_l (-x))...
   rewrite (CRinv_pos_weaken ('c) d)...
   rewrite <-(rings.plus_0_l (-cast AR CR x))...
  assert (CRltT 0 ('x)) as Px.
   apply CRltT_wd with (cast AR CR 0) ('x).
     now apply rings.preserves_0.
    reflexivity.
   now apply ARtoCR_preserves_ltT.
  rewrite (CRinvT_irrelevant _ (inr Px)). 
  unfold CRinvT.
  destruct Ec as [c Ec], Px as [d Ed].
  autorewrite with ARtoCR.
  destruct (Qlt_le_dec d ('c : Qpos)).
   rewrite (CRinv_pos_weaken d ('c))...
   change (cast Q CR (cast AQ Q (cast (AQ₊) AQ c)) ≤ cast AR CR x).
   rewrite <-ARtoCR_inject. 
   apply (order_preserving _).
   setoid_replace x with (x - 0) by ring...
  rewrite (CRinv_pos_weaken ('c) d)...
  rewrite <-(rings.plus_0_r (cast AR CR x))...
Qed.

Lemma ARtoCR_preserves_invT_l x x_ : {x__ | 'ARinvT x x_ = CRinvT ('x) x__}.
Proof.
  exists (fst (ARtoCR_preserves_apartT_0 x) x_).
  apply ARtoCR_preserves_invT.
Qed.

Lemma ARtoCR_preserves_invT_r x x__ : {x_ | 'ARinvT x x_ = CRinvT ('x) x__}.
Proof.
  exists (snd (ARtoCR_preserves_apartT_0 x) x__).
  apply ARtoCR_preserves_invT.
Qed.

Lemma AR_inverseT (x : AR) x_ : x * ARinvT x x_ = 1.
Proof.
  apply (injective (cast AR CR)).
  rewrite rings.preserves_mult, rings.preserves_1.
  destruct (ARtoCR_preserves_invT_l x x_) as [x__ E]. rewrite E.
  apply: field_mult_inv.
Qed.

Lemma ARinvT_wd x y x_ y_ : x = y → ARinvT x x_ = ARinvT y y_.
Proof.
  intros E.
  apply (injective (cast AR CR)). 
  destruct (ARtoCR_preserves_invT_l x x_) as [x__ Ex], 
    (ARtoCR_preserves_invT_l y y_) as [y__ Ey].
  rewrite Ex, Ey. 
  now apply CRinvT_wd.
Qed.

Lemma ARinvT_irrelevant x x_ x__ : ARinvT x x_ = ARinvT x x__.
Proof. now apply ARinvT_wd. Qed.

(* Division with apartness in Prop *)
Program Instance ARinv: Recip AR := λ x, ARinvT x _.
Next Obligation. apply AR_apart_apartT. now destruct x. Qed.

Global Instance: Field AR.
Proof.
  repeat (split; try apply _).
    apply (strong_injective (cast AQ AR)).
    solve_propholds.
   intros [x Px] [y Py] E.
   now apply: ARinvT_wd.
  intros x.
  now apply: AR_inverseT.
Qed.

(* Nat pow *)
Program Definition AQpower_N_uc (n : N) (c : AQ₊) : 
    AQ_as_MetricSpace --> AQ_as_MetricSpace := unary_uc 
  (cast AQ Q_as_MetricSpace)
  (λ x : AQ_as_MetricSpace, (AQboundAbs_uc c x) ^ n : AQ_as_MetricSpace) (Qpower_N_uc n ('c)) _.
Next Obligation.
  assert (∀ y : AQ, cast AQ Q (y ^ n) = 'y ^ 'n) as preserves_pow_pos.
   intros y.
   rewrite nat_pow.preserves_nat_pow.
   now rewrite (int_pow.int_pow_nat_pow (f:=cast N Z)).
  rewrite preserves_pow_pos. aq_preservation. 
Qed.

Definition ARpower_N_bounded (n : N) (c : AQ₊) : AR --> AR := Cmap AQPrelengthSpace (AQpower_N_uc n c).

Lemma ARtoCR_preserves_power_N_bounded x n c : 
  'ARpower_N_bounded n c x = CRpower_N_bounded n ('c) ('x).
Proof. apply preserves_unary_fun. Qed.

Global Instance ARpower_N: Pow AR N := λ x n, ucFun (ARpower_N_bounded n (AR_b x)) x.

Lemma ARtoCR_preserves_power_N (x : AR) (n : N) : 
  cast AR CR (x ^ n) = ('x) ^ n.
Proof.
  unfold pow, CRpower_N, ARpower_N.
  rewrite ARtoCR_preserves_power_N_bounded.
  setoid_replace (cast (AQ₊) (Q₊) (AR_b x)) with (CR_b (1#1) ('x)). 
   reflexivity.
  unfold QposEq. simpl.
  now rewrite ARtoCR_approximate, <-AR_b_correct.
Qed. 

Hint Rewrite ARtoCR_preserves_power_N : ARtoCR.

Global Instance: NatPowSpec AR N _.
Proof.
  split.
    intros ? ? Ex ? ? En.
    apply (injective (cast AR CR)). autorewrite with ARtoCR.
    now rewrite Ex, En.
   intros. apply (injective (cast AR CR)). autorewrite with ARtoCR.
   now rewrite nat_pow_0.
  intros. apply (injective (cast AR CR)). autorewrite with ARtoCR.
  now rewrite nat_pow_S.
Qed.

(* Misc properties *)
Lemma ARmult_bounded_mult (x y : AR) c : 
  -'c ≤ y ≤ 'c → ARmult_bounded c x y = x * y.
Proof.
  intros. 
  apply (injective (cast AR CR)).
  rewrite ARtoCR_preserves_mult, ARtoCR_preserves_mult_bounded.
  destruct c as [c Pc].
  apply CRmult_bounded_mult.
   change (cast Q CR (-cast AQ Q c) ≤ cast AR CR y).
   rewrite <-rings.preserves_negate.
   rewrite <-ARtoCR_inject.
   apply (order_preserving _). intuition.
  change (cast AR CR y ≤ cast Q CR (cast AQ Q c)).
  rewrite <-ARtoCR_inject.
  apply (order_preserving _). intuition.
Qed.

Lemma ARpower_N_bounded_N_power (n : N) (x : AR) (c : AQ₊) : 
  -'c ≤ x ≤ 'c → ARpower_N_bounded n c x = x ^ n.
Proof.
  intros.
  apply (injective (cast AR CR)).
  rewrite ARtoCR_preserves_power_N, ARtoCR_preserves_power_N_bounded.
  destruct c as [c Pc].
  apply CRpower_N_bounded_N_power. split.
   change (cast Q CR (-cast AQ Q c) ≤ cast AR CR x).
   rewrite <-rings.preserves_negate.
   rewrite <-ARtoCR_inject.
   apply (order_preserving _). intuition.
  change (cast AR CR x ≤ cast Q CR (cast AQ Q c)).
  rewrite <-ARtoCR_inject.
  apply (order_preserving _). intuition.
Qed.
End ARarith.
