Require Import 
  Program CornTac workaround_tactics
  Qmetric CRAlternatingSum Qdlog2
  ApproximateRationals ARArith
  abstract_algebra int_pow theory.streams theory.series.

Add Ring Z : (rings.stdlib_ring_theory Z).
Local Coercion Is_true : bool >-> Sortclass.

Section alt_sum.
Context `{AppRationals AQ}.

CoInductive DivisionStream: Stream Q_as_MetricSpace → Stream AQ → Stream AQ → Prop :=
  division_stream_eq: ∀ sQ sN sD, 
      hd sQ = 'hd sN / 'hd sD → DivisionStream (tl sQ) (tl sN) (tl sD) → DivisionStream sQ sN sD.

Lemma DivisionStream_Str_nth (sQ : Stream Q_as_MetricSpace) (sN sD : Stream AQ) :
  (∀ n, Str_nth n sQ = 'Str_nth n sN / 'Str_nth n sD) ↔ DivisionStream sQ sN sD.
Proof.
  split.
   revert sQ sN sD.
   cofix FIX. intros sQ sN sD E.
   constructor.
    now apply (E O).
   apply FIX.
   intros n. apply (E (S n)).
  intros d n. revert sQ sN sD d.
  induction n; intros sQ sN sD d.
   now destruct d.
  apply IHn. now destruct d.
Qed.

Lemma DivisionStream_tl `(d : DivisionStream sQ sN sD) : DivisionStream (tl sQ) (tl sN) (tl sD).
Proof. now destruct d. Qed.

Definition DivisionStream_Str_nth_tl `(d : DivisionStream sQ sN sD) (n : nat) : 
  DivisionStream (Str_nth_tl n sQ) (Str_nth_tl n sN) (Str_nth_tl n sD).
Proof. 
  revert sQ sN sD d. 
  induction n; intros. 
   easy. 
  now apply IHn, DivisionStream_tl. 
Qed.

CoFixpoint ARInfAltSum_approx (sN sD : Stream AQ) (k l : Z) : Stream AQ := Cons 
  (app_div_above (hd sN) (hd sD) (k - Z.log2_up l))
  (ARInfAltSum_approx (tl sN) (tl sD) k (l + 1)).

Lemma ARInfAltSum_approx_ge `(d : DivisionStream sQ sN sD) {dnn : DecreasingNonNegative sQ} (ε : Qpos) (l : Z) :
  ForAllIf (λ s, AQball_bool (Qdlog2 ε) (hd s) 0) (λ s, Qball_ex_bool ε (hd s) 0) 
    (ARInfAltSum_approx sN sD (Qdlog2 ε) l) sQ.
Proof with auto.
  revert l sQ sN sD d dnn.
  cofix FIX; intros l sQ sN sD d dnn.
  constructor.
   intros E. 
   apply Is_true_eq_left. apply sumbool_eq_true.
   apply Is_true_eq_true in E. apply AQball_bool_true in E. 
   simpl in *.
   destruct d as [? ? ? E2]. rewrite E2. 
   apply Qball_Qabs. apply Qball_Qabs in E.
   unfold Qminus. rewrite Qplus_0_r.
   assert ((0:Q) ≤  'hd sN / 'hd sD).
    destruct dnn as [[? ?]].
    transitivity (hd (tl sQ))...
    now rewrite <-E2.
   rewrite Qabs.Qabs_pos...
   transitivity (2 ^ Qdlog2 ε)%Qpos.
    transitivity (Qabs.Qabs ('app_div_above (hd sN) (hd sD) (Qdlog2 ε - Z.log2_up l) - '0))...
    rewrite rings.preserves_0. unfold Qminus. rewrite Qplus_0_r.
    rewrite Qabs.Qabs_pos.
     now apply aq_div_above.
    transitivity ('hd sN / 'hd sD : Q)...
    now apply aq_div_above.
   now apply Qpos_dlog2_spec.
  simpl.
  apply FIX.
   now apply DivisionStream_tl.
  now apply _.
Qed.

Lemma ARInfAltSum_lazylength_Further `(d : DivisionStream sQ sN sD) (k : Z) `(Pl : 2 + 2 ≤ (l:Z)) :
  NearBy 0 (Qpos2QposInf (2 ^ (k - 1))) sQ → Is_true (AQball_bool k (hd (ARInfAltSum_approx sN sD k l)) 0).
Proof.
  intros E.
  apply Is_true_eq_left.
  apply_simplified AQball_bool_true.
  rewrite rings.preserves_0.
  apply ball_weak_le with ((2 ^ (k - Z.log2_up l)) + (2 ^ (k - Z.log2_up l)) + 2 ^ (k - 1))%Qpos.
   simpl.
   assert (∀ n : Z, (2:Q) ^ n = 2 ^ (n - 1) + 2 ^ (n - 1)) as G. 
    intros n. 
    ms_setoid_replace n with (1 + (n - 1)) at 1 by ring.
    rewrite int_pow_S.
     now rewrite rings.plus_mul_distr_r, left_identity.
    apply (rings.ne_0 (2:Q)).
   posed_rewrite (G k).
   apply_simplified (semirings.plus_compat (R:=Q)); [| reflexivity].
   posed_rewrite (G (k - 1)).
   assert ((2:Q) ^ (k - Z.log2_up l) ≤ 2 ^ (k - 1 - 1)).
    apply int_pow.int_pow_exp_precedes.
     now apply semirings.precedes_1_2.
    rewrite <-associativity.
    apply (order_preserving (k +)).
    rewrite <-rings.opp_distr.
    apply rings.flip_opp.
    replace (1 + 1:Z) with (Z.log2_up 4) by reflexivity.
    now apply Z.log2_up_le_mono.
   now apply semirings.plus_compat.
  eapply ball_triangle. 
   2: now apply E. 
  simpl. unfold app_div_above.
  rewrite <-(rings.plus_0_r (hd sQ)).
  destruct d as [? ? ? F]. rewrite F.
  unfold app_div_above. rewrite rings.preserves_plus.
  apply Qball_plus.
   now apply aq_div.
  rewrite aq_shift_correct, rings.preserves_1, left_identity.
  now apply Qball_0_r.
Qed.

Lemma ARInfAltSum_lazylength_aux `(d : DivisionStream sQ sN sD) {zl : Limit sQ 0} (k : Z) `(Pl : 2 + 2 ≤ (l : Z)) :
  LazyExists (λ s, AQball_bool k (hd s) 0) (ARInfAltSum_approx sN sD k l).
Proof.
  revert l Pl sN sD d.
  induction (zl (2 ^ (k - 1)))%Qpos as [sQ' E | ? ? IH]; intros l El sN sD d.
   left. now apply (ARInfAltSum_lazylength_Further d k El).
  right. intros _. 
  simpl. apply (IH tt).
   abstract (apply semirings.nonneg_plus_compat_r; [auto | apply semirings.precedes_0_1]).
  now destruct d.
Defined.

Definition ARInfAltSum_length `(d : DivisionStream sQ sN sD) {zl : Limit sQ 0} (k : Z)
  := 4 + takeUntil_length _ (ARInfAltSum_lazylength_aux (DivisionStream_Str_nth_tl d 4) k (reflexivity (2 + 2))).

Lemma ARInfAltSum_length_ge `(d : DivisionStream sQ sN sD) {dnn : DecreasingNonNegative sQ} {zl : Limit sQ 0} (ε : Qpos) :
  takeUntil_length _ (Limit_near sQ 0 ε) ≤ ARInfAltSum_length d (Qdlog2 ε).
Proof.
  transitivity (4 + takeUntil_length _ (LazyExists_Str_nth_tl (Limit_near sQ 0 ε) (dnn_in_Qball_0_EventuallyForall sQ ε) 4)).
   apply takeUntil_length_Str_nth_tl.
  unfold ARInfAltSum_length.
  apply (order_preserving (4 +)).
  apply takeUntil_length_ForAllIf.
  apply ARInfAltSum_approx_ge.
   now apply DivisionStream_Str_nth_tl.
  now apply _.
Qed.

Lemma ARInfAltSum_length_pos `(d : DivisionStream sQ sN sD) {dnn : DecreasingNonNegative sQ} {zl : Limit sQ 0} (k : Z) :
  0 < ARInfAltSum_length d k.
Proof.
  unfold ARInfAltSum_length.
  apply semirings.pos_plus_scompat_l.
   split; try discriminate.
   now do 4 apply le_S.
  apply naturals.naturals_nonneg.
Qed.

Fixpoint ARAltSum (sN sD : Stream AQ) (l : nat) (k : Z) :=
  match l with 
  | O => 0
  | S l' => app_div (hd sN) (hd sD) k - ARAltSum (tl sN) (tl sD) l' k
  end.

Lemma ARAltSum_correct_aux `(d : DivisionStream sQ sN sD) {dnn : DecreasingNonNegative sQ} {zl : Limit sQ 0} (l : positive) (k : Z) :
  ball (l * 2 ^ k) ('ARAltSum sN sD (nat_of_P l) k) (take sQ (nat_of_P l) Qminus' 0).
Proof.
  revert sQ sN sD d dnn zl.
  induction l using Pind; intros.
   simpl. 
   rewrite rings.opp_0, rings.plus_0_r.
   rewrite Qminus'_correct. unfold Qminus. rewrite Qplus_0_r.
   setoid_replace (1%positive * 2 ^ k)%Qpos with (2 ^ k)%Qpos.
    destruct d as [? ? ? E].
    rewrite E.
    now apply aq_div.
   unfold QposEq. simpl. now apply rings.mult_1_l.
  rewrite Psucc_S.
  simpl.
  rewrite rings.preserves_plus, rings.preserves_opp.
  rewrite Qminus'_correct. unfold Qminus.
  setoid_replace (Psucc l * 2 ^ k)%Qpos with (2 ^ k + l * 2 ^ k)%Qpos.
   apply Qball_plus.
    destruct d as [? ? ? E].
    rewrite E.
    now apply aq_div.
   apply Qball_opp. 
   apply IHl; try apply _.
   now destruct d.
  unfold QposEq. simpl. 
  rewrite Pplus_one_succ_l, Zpos_plus_distr, Q.Zplus_Qplus.
  now ring.
Qed.

Lemma ARAltSum_correct `(d : DivisionStream sQ sN sD) {dnn : DecreasingNonNegative sQ} {zl : Limit sQ 0} `(Pl : 0 < (l:nat)) (k : Z) :
  ball (2 ^ k) ('ARAltSum sN sD l (k - Z.log2_up l)) (take sQ l Qminus' 0).
Proof.
  destruct l.
   now destruct Pl as [_ []]. 
  apply ball_weak_le with (P_of_succ_nat l * 2 ^ (k - Z.log2_up (P_of_succ_nat l)))%Qpos.
   set (l':=P_of_succ_nat l).
   change ((l':Q) * 2 ^ (k - Z.log2_up l') ≤ 2 ^ k).
   rewrite int_pow_exp_plus; [| apply (rings.ne_0 (2:Q))].
   apply (order_preserving_back ((2:Q) ^ Z.log2_up l' *.)).
   ms_setoid_replace (2 ^ Z.log2_up l' * ((l':Q) * (2 ^ k * 2 ^ (- Z.log2_up l')))) with (2 ^ k * (l':Q)).
    rewrite (commutativity _ ((2:Q) ^ k)).
    apply (order_preserving (2 ^ k *.)).
    replace (2:Q) with (inject_Z 2) by reflexivity.
    rewrite <-Qpower.Zpower_Qpower.
     apply (order_preserving _).
     destruct (decide ((l':Z) = 1)) as [E|E].
      now rewrite E.
     apply Z.log2_up_spec. 
     auto with zarith.
    now apply Z.log2_up_nonneg.
   rewrite int_pow_opp.
   rewrite (commutativity (l' : Q)), (commutativity (2 ^ k)).
   rewrite <-associativity.
   rewrite associativity, fields.dec_mult_inverse.
    now apply left_identity.
   apply (_ : PropHolds (2 ^ Z.log2_up l' ≠ 0)).
  rewrite <-nat_of_P_of_succ_nat.
  rewrite convert_is_POS.
  now apply ARAltSum_correct_aux.
Qed.

Definition ARInfAltSum_raw `(d : DivisionStream sQ sN sD) {zl : Limit sQ 0} (ε : Qpos) : AQ_as_MetricSpace := 
  let εk:= Qdlog2 ε - 1 in 
  let l:= ARInfAltSum_length d εk
  in ARAltSum sN sD l (εk - Z.log2_up (Z_of_nat l)).

Lemma ARInfAltSum_raw_correct `(d : DivisionStream sQ sN sD) {dnn : DecreasingNonNegative sQ} {zl : Limit sQ 0} (ε1 ε2 : Qpos) :
  ball (ε1 + ε2) ('ARInfAltSum_raw d ε1) (InfiniteAlternatingSum_raw sQ ε2).
Proof.
  setoid_replace (ε1 + ε2)%Qpos with ((1#2) * ε1 + ((1#2) * ε1 + ε2))%Qpos by QposRing.
  eapply ball_triangle.
   apply ball_weak_le with (2 ^ (Qdlog2 ε1 - 1))%Qpos.
    change (2 ^ (Qdlog2 ε1 - 1) ≤ (1 # 2) * (ε1:Q)).
    rewrite Qdlog2_half.
    apply_simplified Qdlog2_spec. auto with *. 
   unfold ARInfAltSum_raw.
   apply (ARAltSum_correct d).
   now apply ARInfAltSum_length_pos.
  apply (InfiniteAlternatingSum_further_alt _).
  rewrite Qdlog2_half.
  apply (ARInfAltSum_length_ge d ((1 # 2) * ε1)).
Qed.

Lemma ARInfAltSum_prf `(d : DivisionStream sQ sN sD) {dnn : DecreasingNonNegative sQ} {zl : Limit sQ 0} :
  is_RegularFunction_noInf _ (ARInfAltSum_raw d).
Proof.
  intros ε1 ε2. simpl.
  apply ball_closed. intros δ.
  setoid_replace (ε1 + ε2 + δ)%Qpos with (ε1 + (1#4) * δ + ((1#4) * δ + (1#4) * δ + (ε2 + (1#4) * δ)))%Qpos by QposRing.
  eapply ball_triangle.
   now apply ARInfAltSum_raw_correct.
  eapply ball_triangle.
   now apply InfiniteAlternatingSum_prf.
  apply ball_sym.
  now apply ARInfAltSum_raw_correct.
Qed.

Definition ARInfAltSum `(d : DivisionStream sQ sN sD) {dnn : DecreasingNonNegative sQ} {zl : Limit sQ 0} 
  := mkRegularFunction (0 : AQ_as_MetricSpace) (ARInfAltSum_prf d).

Lemma ARInfAltSum_correct `(d : DivisionStream sQ sN sD) {dnn : DecreasingNonNegative sQ} {zl : Limit sQ 0} :
   ARtoCR (ARInfAltSum d) = InfiniteAlternatingSum sQ.
Proof.
  intros ? ?.
  unfold ARtoCR. simpl.
  now apply ARInfAltSum_raw_correct.
Qed.
End alt_sum.
