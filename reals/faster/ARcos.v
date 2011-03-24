Require Import
  CRsin CRcos MetricMorphisms Complete ARsin abstract_algebra.
Require Export
  ARArith.

Section ARcos.
Context `{AppRationals AQ}.

Add Field Q : (fields.stdlib_field_theory Q).

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

Program Definition AQcos_poly_uc := unary_uc coerce 
  (λ x : AQ_as_MetricSpace, AQcos_poly_fun (AQboundAbs_uc 1 x) : AQ_as_MetricSpace) cos_poly_uc _.
Next Obligation.
  rewrite AQcos_poly_fun_correct.
  change ('1) with (1:AQ).
  rewrite ?aq_preserves_max, ?aq_preserves_min.
  now rewrite ?rings.preserves_opp, ?rings.preserves_1.
Qed.

Definition ARcos_poly := uc_compose ARcompress (Cmap AQPrelengthSpace AQcos_poly_uc).

Lemma ARtoCR_preserves_cos_poly x : 
  ARtoCR (ARcos_poly x) = cos_poly (ARtoCR x).
Proof.
  change (ARtoCR (ARcompress (Cmap AQPrelengthSpace AQcos_poly_uc x)) = cos_poly (ARtoCR x)).
  rewrite ARcompress_correct.
  now apply preserves_unary_fun.
Qed.

Definition AQcos (x : AQ) := ARcos_poly (AQsin (x ≪ (-1))).

Lemma AQcos_correct a : ARtoCR (AQcos a) = rational_cos ('a).
Proof.
  unfold AQcos.
  rewrite ARtoCR_preserves_cos_poly, AQsin_correct.
  rewrite aq_shift_opp_1.
  now apply rational_cos_sin.
Qed.

Local Obligation Tactic := idtac.
Program Definition ARcos_uc := 
  unary_complete_uc Qmetric.QPrelengthSpace coerce AQcos cos_uc _.
Next Obligation. intros. apply AQcos_correct. Qed.

Definition ARcos := Cbind AQPrelengthSpace ARcos_uc.

Lemma ARtoCR_preserves_cos x : ARtoCR (ARcos x) = cos_slow (ARtoCR x).
Proof. apply preserves_unary_complete_fun. Qed.
End ARcos.
