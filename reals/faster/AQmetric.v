Require Import CoRN.algebra.RSetoid.
Require Import 
  Coq.Program.Program Coq.setoid_ring.Ring CoRN.util.Qdlog
  CoRN.metric2.Complete CoRN.metric2.Prelength CoRN.model.metric2.Qmetric CoRN.model.metric2.CRmetric CoRN.metric2.MetricMorphisms.
Require Export
  CoRN.reals.faster.ApproximateRationals.

Section AQmetric.
Context `{AppRationals AQ}.

Add Ring AQ : (rings.stdlib_ring_theory AQ).

Local Open Scope uc_scope. 

Definition AQ_as_MetricSpace := Emetric (cast AQ Q_as_MetricSpace).
Definition AQPrelengthSpace := EPrelengthSpace QPrelengthSpace (cast AQ Q_as_MetricSpace).
Definition AR := Complete AQ_as_MetricSpace.

Definition AQtoQ_uc : AQ_as_MetricSpace --> Q_as_MetricSpace := metric_embed_uc (cast AQ Q_as_MetricSpace).

Definition ARtoCR_uc : AR --> CR := Eembed QPrelengthSpace (cast AQ Q_as_MetricSpace).
Global Instance ARtoCR: Cast AR CR := ARtoCR_uc.
Definition CRtoAR_uc : CR --> AR := Eembed_inverse QPrelengthSpace (cast AQ Q_as_MetricSpace).
Global Instance CRtoAR: Cast CR AR := CRtoAR_uc.

Global Instance inject_AQ_AR: Cast AQ AR := (@Cunit AQ_as_MetricSpace).
Global Instance: Proper ((=) ==> (=)) inject_AQ_AR := uc_wd (@Cunit AQ_as_MetricSpace).

Lemma AQball_fold ε (x y : AQ_as_MetricSpace) : ball ε x y → Qball ε ('x) ('y).
Proof. easy. Qed.

Lemma AQball_abs (ε : Qpos) (x y : AQ_as_MetricSpace) : 
  ball ε x y ↔ 'abs (x - y) ≤ ('ε : Q).
Proof.
  simpl. rewrite Qball_Qabs.
  now rewrite abs.preserves_abs, rings.preserves_minus.
Qed.

Definition AQball_bool (k : Z) (x y : AQ) := bool_decide_rel (≤) (abs (x - y)) (1 ≪ k).

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
  AQball_bool (Qdlog2 ε) x y ≡ true → ball ε x y.
Proof.
  intros E.
  apply AQball_abs.
  transitivity (2 ^ (Qdlog2 ε) : Q).
   apply AQball_bool_true in E.
   now apply AQball_abs in E.
  now apply (Qpos_dlog2_spec ε).
Qed.

Lemma AQball_plus (ε1 ε2 : Qpos) (x1 x2 y1 y2 : AQ_as_MetricSpace) : 
  ball ε1 x1 y1 → ball ε2 x2 y2 → ball (ε1 + ε2) (x1 + x2) (y1 + y2).
Proof.
  intros.
  apply ball_triangle with (x2 + y1); apply AQball_abs.
   setoid_replace (x1 + x2 - (x2 + y1)) with (x1 - y1) by (simpl; ring).
   now apply AQball_abs.
  setoid_replace (x2 + y1 - (y1 + y2)) with (x2 - y2) by (simpl; ring).
  now apply AQball_abs.
Qed.

Lemma AQball_plus_l (ε : Qpos) (x y z : AQ_as_MetricSpace) :
  ball ε x y → ball ε (z + x) (z + y).
Proof.
  intros E.
  apply AQball_abs.
  setoid_replace (z + x - (z + y)) with (x - y) by (simpl; ring).
  now apply AQball_abs.
Qed.

Lemma AQball_plus_r (ε : Qpos) (x y z : AQ_as_MetricSpace) :
  ball ε x y → ball ε (x + z) (y + z).
Proof.
  intros E.
  apply AQball_abs.
  setoid_replace (x + z - (y + z)) with (x - y) by (simpl; ring).
  now apply AQball_abs.
Qed.

Lemma AQball_opp (ε : Qpos) (x y : AQ_as_MetricSpace) :
  ball ε x y → ball ε (-x) (-y).
Proof.
  intros.
  apply AQball_abs.
  setoid_replace (-x - -y) with (y - x) by (simpl; ring).
  apply AQball_abs. 
  now apply ball_sym.
Qed.
End AQmetric.
