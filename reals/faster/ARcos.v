Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.model.metric2.Qmetric.
Require Import
  MathClasses.misc.workaround_tactics
  CoRN.reals.fast.CRsin CoRN.reals.fast.CRcos CoRN.metric2.MetricMorphisms CoRN.metric2.Complete CoRN.reals.faster.ARsin MathClasses.interfaces.abstract_algebra.
Require Export
  CoRN.reals.faster.ARArith.

Section ARcos.
Context `{AppRationals AQ}.

Local Open Scope uc_scope.

Add Field Q : (dec_fields.stdlib_field_theory Q).

Definition AQcos_poly_fun (x : AQ) : AQ := 1 - 2 * x ^ (2:N).

Lemma AQcos_poly_fun_correct (x : AQ) :
  'AQcos_poly_fun x = cos_poly_fun ('x).
Proof.
  unfold AQcos_poly_fun, cos_poly_fun.
  rewrite nat_pow.nat_pow_2.
  rewrite rings.preserves_minus, ?rings.preserves_mult.
  rewrite rings.preserves_1, rings.preserves_2.
  now rewrite associativity.
Qed.

Program Definition AQcos_poly_uc := unary_uc (cast AQ Qmetric.Q_as_MetricSpace)
  (λ x : AQ_as_MetricSpace, AQcos_poly_fun (AQboundAbs_uc 1 x) : AQ_as_MetricSpace) cos_poly_uc _.
Next Obligation.
  apply Qball_0.
  rewrite AQcos_poly_fun_correct.
  change ('1) with (1:AQ).
  rewrite ?aq_preserves_max, ?aq_preserves_min.
  now rewrite ?rings.preserves_negate, ?rings.preserves_1.
Qed.

Definition ARcos_poly := uc_compose ARcompress (Cmap AQPrelengthSpace AQcos_poly_uc).

Lemma ARtoCR_preserves_cos_poly x : 
  'ARcos_poly x = cos_poly ('x).
Proof.
  change ('ARcompress (Cmap AQPrelengthSpace AQcos_poly_uc x) = cos_poly ('x)).
  rewrite ARcompress_correct.
  now apply preserves_unary_fun.
Qed.

Definition AQcos (x : AQ) : AR := ARcos_poly (AQsin (x ≪ (-1))).

Lemma AQcos_correct a : 'AQcos a = rational_cos ('a).
Proof.
  unfold AQcos.
  rewrite ARtoCR_preserves_cos_poly. 
  posed_rewrite AQsin_correct.
  rewrite aq_shift_opp_1.
  now apply rational_cos_sin.
Qed.

Definition ARcos_uc : AQ_as_MetricSpace --> AR
  := unary_complete_uc QPrelengthSpace AQtoQ AQcos cos_uc AQcos_correct.

Lemma ARcos_uc_eval : forall q : AQ_as_MetricSpace,
    ARcos_uc q ≡ AQcos q.
Proof. reflexivity. Qed.

Definition ARcos : AR --> AR := Cbind AQPrelengthSpace ARcos_uc.

Lemma ARtoCR_preserves_cos x : 'ARcos x = cos_slow ('x).
Proof. apply preserves_unary_complete_fun. Qed.
End ARcos.
