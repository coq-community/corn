Require Import
  Program QArith ZArith BigZ BigQ Qpossec
  Compress ARQ
  MetricMorphisms Qmetric ARArith
  stdlib_rationals stdlib_binary_integers field_of_fractions
  fast_rationals fast_integers.

Instance inject_Z_bigQ: Cast Z bigQ := cast bigZ bigQ ∘ cast Z bigZ.

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
  case_eq (BigN.eq_bool (BigN.shiftl 1 (BigN.of_pos p)) BigN.zero); intros Ep.
   apply BigNeqb_correct, BigN.shiftl_eq_0_iff in Ep.
   discriminate.
  case_eq (BigN.eq_bool d BigN.zero); intros Ed.
   apply BigNeqb_correct in Ed.
   setoid_replace (BigZ.Pos d) with 0%bigZ by assumption.
   now rewrite BigZ.spec_div, Zdiv_0_r, Zmult_0_l.
  rewrite BigZ.spec_div, BigZ.spec_shiftl, Z.shiftl_mul_pow2 by apply BigN.spec_pos.
  rewrite BigN.spec_shiftl, Z.shiftl_1_l.
  replace (BigZ.to_Z (BigZ.Pos (BigN.of_pos p))) with (Zpos p) by (symmetry; apply BigN.spec_of_pos).
  rewrite BigN.spec_of_pos.
  replace (Z2P (2 ^ p)) with (2 ^ p)%positive by now rewrite Zpower_Ppow.
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

Instance bigQ_div: AppDiv bigQ := λ x y, app_approx (x / y).

Lemma bigQ_div_correct (x y : bigQ) (k : Z) : Qball (2 ^ k) ('app_div x y k) ('x / 'y).
Proof.
  ms_setoid_replace ('x / 'y : Q) with ('(x / y) : Q).
   now apply bigQ_approx_correct.
  now rewrite rings.preserves_mult, dec_fields.preserves_dec_mult_inv.
Qed.

Instance inverse_Q_bigQ: AppInverse (cast bigQ Q_as_MetricSpace) := λ x ε, 'x.

Instance: DenseEmbedding (cast bigQ Q_as_MetricSpace).
Proof.
  split; try apply _.
  intros. unfold app_inverse, inverse_Q_bigQ.
  now rewrite (rationals.morphisms_involutive _ _).
Qed.

Instance: AppRationals bigQ.
Proof.
  split; try apply _.
    split; try apply _.
   intros. now apply bigQ_div_correct.
  intros. now apply bigQ_approx_correct.
Qed.

Notation ARbigQ := (AR (AQ:=bigQ)).
