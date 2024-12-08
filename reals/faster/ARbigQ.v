Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
From Coq Require Import Program QArith ZArith.
Require Import Bignums.BigZ.BigZ Bignums.BigQ.BigQ 
  CoRN.reals.fast.Compress CoRN.reals.faster.ARQ
  CoRN.metric2.MetricMorphisms CoRN.model.metric2.Qmetric CoRN.reals.faster.ARArith
  MathClasses.implementations.stdlib_rationals MathClasses.implementations.stdlib_binary_integers MathClasses.implementations.field_of_fractions
  MathClasses.implementations.fast_rationals MathClasses.implementations.fast_integers.

#[global]
Instance inject_Z_bigQ: Cast Z bigQ := cast bigZ bigQ ∘ cast Z bigZ.

#[global]
Instance bigQ_approx: AppApprox bigQ := λ x k,
  match k with
  | Zneg p => 
    let k' := BigN.of_N (Npos p) in
    match x with
    | BigQ.Qz z => BigQ.Qz z
    | BigQ.Qq n d => BigQ.Qq (BigZ.div (BigZ.shiftl n (BigZ.Pos k')) (BigZ.Pos d)) (BigN.shiftl 1 k')
    end
  | _ => x
  end.

Lemma bigQ_approx_Q_approx (x : bigQ) (k : Z) : 
  'app_approx x k = app_approx ('x) k.
Proof.
  unfold app_approx, Q_approx, approximateQ, bigQ_approx.
  destruct k as [|p|]; try reflexivity.
  destruct x as [n|n d]; simpl.
   rewrite Z.div_1_r, Qmake_Qdiv. simpl.
   now rewrite Q.Zmult_Qmult, Qdiv_mult_l by auto with zarith.
  unfold cast, BigQ_Rationals.inject_QType_Q, BigQ.to_Q.
  case_eq (BigN.shiftl 1 (BigN.of_pos p) =? BigN.zero)%bigN; intros Ep.
   apply BigNeqb_correct, BigN.shiftl_eq_0_iff in Ep.
   discriminate.
  case_eq (d =? BigN.zero)%bigN; intros Ed.
   apply BigNeqb_correct in Ed.
   setoid_replace (BigZ.Pos d) with 0%bigZ by assumption.
   now rewrite BigZ.spec_div, Zdiv_0_r, Zmult_0_l.
  rewrite BigZ.spec_div, BigZ.spec_shiftl, Z.shiftl_mul_pow2 by apply BigN.spec_pos.
  rewrite BigN.spec_shiftl, Z.shiftl_1_l.
  replace (BigZ.to_Z (BigZ.Pos (BigN.of_pos p))) with (Zpos p) by (symmetry; apply BigN.spec_of_pos).
  rewrite BigN.spec_of_pos.
  replace (Z2P (2 ^ Zpos p)) with (2 ^ p)%positive by now rewrite <- Zpower_Ppow.
  rewrite <-Zpower_Ppow.
  rewrite Z2P_correct.
   reflexivity.
  apply orders.lt_iff_le_ne. split.
   now apply BigN.spec_pos.
  intros E. symmetry in E.
  change (d == BigN.zero)%bigN in E.
  apply BigN.eqb_eq in E.
  rewrite E in Ed. discriminate.
Qed.

Lemma bigQ_approx_correct (x : bigQ) (k : Z) : Qball (2 ^ k) ('app_approx x k) ('x).
Proof.
  rewrite bigQ_approx_Q_approx.
  now apply Q_approx_correct.
Qed.

#[global]
Instance bigQ_div: AppDiv bigQ := λ x y, app_approx (x / y).

Lemma bigQ_div_correct (x y : bigQ) (k : Z) : Qball (2 ^ k) ('app_div x y k) ('x / 'y).
Proof.
  mc_setoid_replace ('x / 'y : Q) with ('(x / y) : Q).
   now apply bigQ_approx_correct.
  now rewrite rings.preserves_mult, dec_fields.preserves_dec_recip.
Qed.

#[global]
Instance inverse_Q_bigQ: AppInverse (cast bigQ Q_as_MetricSpace) := λ x ε, 'x.

#[global]
Instance: DenseEmbedding (cast bigQ Q_as_MetricSpace).
Proof.
  split; try apply _.
  - Set Printing Implicit.
    assert ( @Injective bigQ Q_as_MetricSpace BigQ_Rationals.QType_equiv
                        Qeq
    (@cast bigQ Q_as_MetricSpace BigQ_Rationals.inject_QType_Q)).
    { apply _. }
    destruct H. split. 
    intros. apply Qball_0 in H. apply injective, H.
    split. apply _. apply _. 
    intros x y xyeq. apply Qball_0.
    destruct injective_mor. apply sm_proper, xyeq.
  - intros. unfold app_inverse, inverse_Q_bigQ.
  rewrite (rationals.morphisms_involutive _ _).
  apply ball_refl. apply QposMinMax.Qpos_nonneg.
Qed.

#[global]
Instance: AppRationals bigQ.
Proof.
  split; try apply _.
    split; try apply _.
   intros. now apply bigQ_div_correct.
  intros. now apply bigQ_approx_correct.
Qed.

Notation ARbigQ := (AR (AQ:=bigQ)).
