Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import 
  Coq.Program.Program Coq.setoid_ring.Ring CoRN.util.Qdlog
  CoRN.model.totalorder.QposMinMax
  CoRN.metric2.Complete CoRN.metric2.Prelength CoRN.model.metric2.Qmetric CoRN.model.metric2.CRmetric CoRN.metric2.MetricMorphisms.
Require Export
  CoRN.reals.faster.ApproximateRationals.

Section AQmetric.
Context `{AppRationals AQ}.

Add Ring AQ : (rings.stdlib_ring_theory AQ).

Local Open Scope uc_scope. 

(* To ensure the definitions below don't use sg_setoid instead *)
Existing Instance strong_setoids.Setoid_instance_0.
Definition AQ_as_MetricSpace := Emetric (cast AQ Q_as_MetricSpace).
Definition AQPrelengthSpace := EPrelengthSpace QPrelengthSpace (cast AQ Q_as_MetricSpace).
Definition AQLocated : locatedMetric AQ_as_MetricSpace.
Proof.
  intros e1 e2 x y lte.
  apply (@locatedQ e1 e2 (AQtoQ x) (AQtoQ y) lte).
Defined.

Definition AR := Complete AQ_as_MetricSpace.

Definition AQtoQ_uc : AQ_as_MetricSpace --> Q_as_MetricSpace := metric_embed_uc (cast AQ Q_as_MetricSpace).

Definition ARtoCR_uc : AR --> CR := Eembed QPrelengthSpace (cast AQ Q_as_MetricSpace).
Global Instance ARtoCR: Cast AR CR := ARtoCR_uc.
Definition CRtoAR_uc : CR --> AR := Eembed_inverse QPrelengthSpace (cast AQ Q_as_MetricSpace).
Global Instance CRtoAR: Cast CR AR := CRtoAR_uc.

Global Instance inject_AQ_AR: Cast AQ AR := (@Cunit AQ_as_MetricSpace).
Global Instance: Proper ((=) ==> (@msp_eq _)) inject_AQ_AR.
Proof.
  intros x y xyeq.
  apply (uc_wd (@Cunit AQ_as_MetricSpace)).
  simpl. 
  rewrite xyeq. reflexivity.
Qed.

Lemma ARtoCR_approx : forall (d : QposInf) (x : AR),
    approximate (ARtoCR x) d ≡ AQtoQ (approximate x d).
Proof. intros. destruct d; reflexivity. Qed.

Lemma inject_Q_AR_prf :
  forall (q:Q), is_RegularFunction (@ball AQ_as_MetricSpace)
             (fun e:QposInf => 
                match e with
                | Qpos2QposInf d => app_inverse (cast AQ Q) q d
                | QposInfinity => 0
                end).
Proof.
  intros q e1 e2. simpl.
  destruct aq_dense_embedding.
  simpl in dense_inverse.
  unfold cast.
  apply (ball_triangle _ _ _ _ q).
  apply dense_inverse.
  apply ball_sym, dense_inverse.
Qed. 

Definition inject_Q_AR (q : Q) : AR
  := Build_RegularFunction (inject_Q_AR_prf q).

(* inject_Q_AR is twice faster than the cast *)
Lemma inject_Q_AR_CR : forall (q : Q),
  inject_Q_AR q = cast CR AR (inject_Q_CR q).
Proof.
  intro q.
  rewrite <- doubleSpeed_Eq.
  intros e1 e2.
  rewrite Qplus_0_r.
  pose proof (regFun_prf (cast CR AR (inject_Q_CR q)) e1 e2) as H5.
  apply H5.
Qed.

Lemma inject_Q_AR_uc : is_UniformlyContinuousFunction
                         inject_Q_AR Qpos2QposInf.
Proof.
  intros d e1 e2 bd x y.
  simpl. unfold cast.
  unfold MetricMorphisms.app_inverse.
  destruct aq_dense_embedding.
  unfold MetricMorphisms.app_inverse in dense_inverse.
  rewrite <- (Qplus_assoc (`x) (`d) (`y)).
  apply ball_triangle with (b:=e1).
  apply dense_inverse.
  apply ball_triangle with (b:=e2).
  apply bd.
  apply ball_sym, dense_inverse.
Qed.

Lemma CRAR_id : forall x : CR,
    msp_eq (cast AR CR (cast CR AR x)) x.
Proof.
  intro x.
  apply (surjective (Eembed QPrelengthSpace (cast AQ Q_as_MetricSpace)) x x).
  reflexivity.
Qed. 

Lemma AQball_fold ε (x y : AQ_as_MetricSpace) : ball ε x y → Qball ε ('x) ('y).
Proof. easy. Qed.

Lemma AQball_abs (ε : Q) (x y : AQ_as_MetricSpace) : 
  ball ε x y ↔ 'abs (x - y) ≤ ε.
Proof.
  simpl. rewrite Qball_Qabs.
  now rewrite abs.preserves_abs, rings.preserves_minus.
Qed.

Definition AQball_bool (k : Z) (x y : AQ) : bool
  := bool_decide_rel (≤) (abs (x - y)) (1 ≪ k).

Lemma AQball_bool_true (k : Z) (x y : AQ_as_MetricSpace) : 
  AQball_bool k x y ≡ true ↔ ball (2 ^ k) x y.
Proof.
  rewrite AQball_abs.
  unfold AQball_bool. rewrite bool_decide_rel_true.
  transitivity ('abs (x - y) ≤ ('(1 ≪ k) : Q)).
   split; intros.
    now apply (order_preserving _).
   now apply (order_reflecting (cast AQ Q)).
  now rewrite aq_shift_correct, rings.preserves_1, left_identity.
Qed.

Global Instance: Proper ((=) ==> (=) ==> (=) ==> (≡)) AQball_bool | 1.
Proof.
  intros ε1 ε2 E1 x1 x2 E2 y1 y2 E3.
  case_eq (AQball_bool ε2 x2 y2). 
   intro. apply AQball_bool_true. rewrite E1, E2, E3. now apply AQball_bool_true.
  rewrite <-2!not_true_iff_false. intros E4 ?. apply E4.
  apply AQball_bool_true. rewrite <-E1, <-E2, <-E3. now apply AQball_bool_true.
Qed.

Lemma AQball_bool_true_eps (ε : Qpos) (x y : AQ_as_MetricSpace) : 
  AQball_bool (Qdlog2 (proj1_sig ε)) x y ≡ true
  → ball (proj1_sig ε) x y.
Proof.
  intros E.
  apply AQball_abs.
  transitivity (2 ^ (Qdlog2 (proj1_sig ε)) : Q).
   apply AQball_bool_true in E.
   now apply AQball_abs in E.
  now apply (Qpos_dlog2_spec ε).
Qed.

Lemma AQball_plus (ε1 ε2 : Qpos) (x1 x2 y1 y2 : AQ_as_MetricSpace) : 
  ball (proj1_sig ε1) x1 y1
  → ball (proj1_sig ε2) x2 y2 → ball (proj1_sig ε1 + proj1_sig ε2) (x1 + x2) (y1 + y2).
Proof.
  intros.
  apply ball_triangle with (x2 + y1); apply AQball_abs.
   setoid_replace (x1 + x2 - (x2 + y1)) with (x1 - y1) by (simpl; ring).
   now apply AQball_abs.
  setoid_replace (x2 + y1 - (y1 + y2)) with (x2 - y2) by (simpl; ring).
  now apply AQball_abs.
Qed.

Lemma AQball_plus_l (ε : Qpos) (x y z : AQ_as_MetricSpace) :
  ball (proj1_sig ε) x y → ball (proj1_sig ε) (z + x) (z + y).
Proof.
  intros E.
  apply AQball_abs.
  setoid_replace (z + x - (z + y)) with (x - y) by (simpl; ring).
  now apply AQball_abs.
Qed.

Lemma AQball_plus_r (ε : Qpos) (x y z : AQ_as_MetricSpace) :
  ball (proj1_sig ε) x y → ball (proj1_sig ε) (x + z) (y + z).
Proof.
  intros E.
  apply AQball_abs.
  setoid_replace (x + z - (y + z)) with (x - y) by (simpl; ring).
  now apply AQball_abs.
Qed.

Lemma AQball_opp (ε : Qpos) (x y : AQ_as_MetricSpace) :
  ball (proj1_sig ε) x y → ball (proj1_sig ε) (-x) (-y).
Proof.
  intros.
  apply AQball_abs.
  setoid_replace (-x - -y) with (y - x) by (simpl; ring).
  apply AQball_abs. 
  now apply ball_sym.
Qed.
End AQmetric.
