Require Import
  Program QArith ZArith BigZ Qpossec
  MetricMorphisms Qmetric Qdlog2
  ApproximateRationals ARArith
  interfaces.integers interfaces.rationals
  stdlib_rationals stdlib_binary_integers fast_integers
  dyadics nonneg_integers_naturals.

Notation fastD := (Dyadic fastZ).

Definition fastZtoQ : fastZ → Q_as_MetricSpace := inject_Z ∘ BigZ.to_Z.
Instance fastDtoQ: Coerce fastD Q_as_MetricSpace := DtoQ fastZtoQ.

Program Instance fastD_compress : AppCompress fastD := λ x k,
  let s := BigZ.of_Z k - expo x
  in if decide_rel (≤) 0 s
  then (mant x ≫ exist _ s _) $ BigZ.of_Z k
  else x.

Instance: Proper ((=) ==> (=) ==> (=)) fastD_compress.
Proof.
  assert (∀ x1 x2 k, x1 = x2 → expo x1 ≤ expo x2 → fastD_compress x1 k = fastD_compress x2 k).
   intros [x1m x1e] [x2m x2e] k Ex Ee.
   apply rings.flip_nonneg_minus in Ee.
   pose proof (proj2 (dy_eq_dec_aux (x1m $ x1e) (x2m $ x2e) Ee) Ex) as Ex'.
   unfold equiv, dy_equiv, DtoQ_slow, fastD_compress.
   case (decide_rel _); case (decide_rel _); intros E1 E2; simpl in *.
      apply sg_mor; [| reflexivity].
      apply sm_proper.
      unfold shiftr, BigZ_Integers.ShiftR_instance_0. simpl.
      rewrite Ex'. unfold shiftl, BigZ_Integers.ZType_shiftl. simpl.
      rewrite BigZ.shiftr_shiftl_r; [|easy].
      admit.
     admit.
    rewrite Ex'.
    rewrite ZtoQ_shift.
    admit.
   easy.
  intros x1 x2 Ex k1 k2 Ek.
  unfold equiv, Z_equiv in Ek. rewrite Ek.
  destruct (total_order (expo x1) (expo x2)).
   auto.
  symmetry. symmetry in Ex. auto.
Qed.

Lemma fastD_compress_correct (x : fastD) (k : Z) : Qball (2 ^ k) ('app_compress x k) ('x).
Proof.
  unfold app_compress, fastD_compress.
  case (decide_rel _); intros E; simpl in *.
   admit.
  apply ball_refl.
Qed.

Program Instance fastD_div : AppDiv fastD := λ x y k,
  let s := -BigZ.of_Z k + expo x - expo y
  in if decide_rel (≤) 0 s 
  then (mant x ≪ exist _ s _) `div` (mant y) $ BigZ.of_Z k
  else (mant x ≫ exist _ (-s) _) `div` (mant y) $ BigZ.of_Z k.
Next Obligation.
  apply rings.flip_nonpos_opp.
  now apply orders.precedes_flip. 
Qed.

Instance: Proper ((=) ==> (=) ==> (=) ==> (=)) fastD_div.
Proof.
  intros [x1m x1e] [x2m x2e] Ex [y1m y1e] [y2m y2e] Ey k1 k2 Ek.
  unfold equiv, dy_equiv, DtoQ_slow in Ex, Ey |- *.
  unfold fastD_div.
  case (decide_rel _); case (decide_rel _); intros E1 E2; simpl in *.
Admitted.

Lemma fastD_div_correct (x y : fastD) (k : Z) : Qball (2 ^ k) ('app_div x y k) ('x / 'y).
Proof.
Admitted.

Instance QtofastD: AppInverse fastDtoQ := λ x ε, 
  app_div ('BigZ.of_Z (Qnum x)) ('BigZ.of_Z (Qden x)) (Qdlog2 ε).

Instance: Proper ((=) ==> (=) ==> (=)) QtofastD.
Proof.
Admitted.

Instance: DenseEmbedding fastDtoQ.
Proof.
  split; try apply _.
  intros [n d] ε.
  unfold app_inverse, QtofastD.
  apply ball_weak_le with (2 ^ Qdlog2 ε)%Qpos.
   now apply Qpos_dlog2_spec.
  simpl. rewrite Qmake_Qdiv.
  rewrite 2!(integers.to_ring_unique_alt inject_Z (fastDtoQ ∘ dy_inject ∘ BigZ.of_Z)).
  apply fastD_div_correct.
Qed.

Instance fastD_Zshiftl: ShiftL fastD Z := λ x n, x ≪ BigZ.of_Z n.

Instance: Proper ((=) ==> (=) ==> (=)) fastD_Zshiftl.
Proof. unfold fastD_Zshiftl. solve_proper. Qed.

Instance: ShiftLSpec fastD Z fastD_Zshiftl.
Proof.
  split; try apply _; unfold shiftl, fastD_Zshiftl.
   intros x. rewrite rings.preserves_0. now apply shiftl_0.
  intros x n. rewrite rings.preserves_plus. now apply shiftl_S.
Qed.

Instance fastD_Npow: Pow fastD N := λ x n, (mant x) ^ n $ BigZ.of_Z (Z_of_N n) * expo x.
Instance: NatPowSpec fastD N fastD_NPow.
Proof.
Admitted.

Instance ZtofastD: Coerce Z fastD := dy_inject ∘ BigZ.of_Z.

Instance: AppRationals fastD.
Proof.
  split; try apply _.
   apply fastD_div_correct.
  apply fastD_compress_correct.
Qed.

Definition fastAR := AR (AQ:=fastD).
