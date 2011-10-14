Require Import 
  Program CornTac workaround_tactics
  Qmetric CRAlternatingSum Qdlog
  ApproximateRationals ARArith
  abstract_algebra int_pow theory.streams theory.series.

Section alt_sum.
Context `{AppRationals AQ}.

Add Ring Z : (rings.stdlib_ring_theory Z).
Local Coercion Is_true : bool >-> Sortclass.

(*
The goal of this section is to compute the infinite alternating sum. Since 
we do not have a precise division operation, we want to postpone divisions as 
long as possible. Hence we parametrize our infinite sum by a stream [sN] 
of numerators and a stream [sD] of denominators.
*)
Fixpoint ARAltSum (sN sD : Stream AQ) (l : nat) (k : Z) :=
  match l with 
  | O => 0
  | S l' => app_div (hd sN) (hd sD) k - ARAltSum (tl sN) (tl sD) l' k
  end.
(* 
However, we have to determine both the length [l] and the required precision 
[2^k] of dividing [sN] by [sQ].

Since Russell has already done a lot of work on this, we aim to reuse that.
Hence we define the following predicate to describe that our streams [sN]
and [sD] correspond to a stream [sQ] of Russell.
*)
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

(* 
Now, [ARInfAltSum_stream sN sD k 0] represents a stream of estimates [sN / sD] 
with logarithmically increasing precision starting with precision [2^k]. We 
compute the length by walking through the stream [ARInfAltSum_stream sN sD k 0] 
until we have an element that has an upper estimate below the required precision.
*)
CoFixpoint ARInfAltSum_stream (sN sD : Stream AQ) (k l : Z) : Stream AQ := Cons 
  (app_div_above (hd sN) (hd sD) (k - Z.log2_up l))
  (ARInfAltSum_stream (tl sN) (tl sD) k (l + 1)).

(* Before we prove that this stream has limit 0, we state some auxiliary stuff. *)
Definition ARInfAltSum_stream_tl sN sD k l :
  tl (ARInfAltSum_stream sN sD k l) = ARInfAltSum_stream (tl sN) (tl sD) k (l + 1).
Proof.
  revert sN sD k l.
  now constructor.
Qed.

Definition ARInfAltSum_stream_Str_nth_tl sN sD k l n :
  Str_nth_tl n (ARInfAltSum_stream sN sD k l) = ARInfAltSum_stream (Str_nth_tl n sN) (Str_nth_tl n sD) k (l + n).
Proof.
  induction n.
   change (l + 0%nat)%Z with (l + 0). now rewrite rings.plus_0_r.
  rewrite !Str_nth_tl_S.
  replace (l + S n)%Z with ((l + n) + 1)%Z.
   rewrite IHn. now apply ARInfAltSum_stream_tl.
  change (l + 'n + 1 = l + '(1 + n)).
  rewrite rings.preserves_plus, rings.preserves_1. ring.
Qed.

(* 
If a certain coordinate of [ARInfAltSum_stream] is in the ball, then the 
corresponding coordinate in [sQ] is in the ball too.
*)
Lemma ARInfAltSum_stream_preserves_ball `(d : DivisionStream sQ sN sD) {dnn : DecreasingNonNegative sQ} (ε : Qpos) (l : Z) :
  ForAllIf (λ s, AQball_bool (Qdlog2 ε) (hd s) 0) (λ s, Qball_ex_bool ε (hd s) 0) 
    (ARInfAltSum_stream sN sD (Qdlog2 ε) l) sQ.
Proof with auto.
  revert l sQ sN sD d dnn.
  cofix FIX; intros l sQ sN sD d dnn.
  constructor.
   intros E. 
   apply Is_true_eq_left. apply sumbool_eq_true.
   apply Is_true_eq_true in E. apply AQball_bool_true in E. 
   simpl in *.
   destruct d as [sQ sN sD E2]. rewrite E2. 
   apply Qball_Qabs. apply Qball_Qabs in E.
   unfold Qminus. rewrite Qplus_0_r.
   assert ((0:Q) ≤  'hd sN / 'hd sD).
    destruct dnn as [[? ?]].
    transitivity (hd (tl sQ))...
    now rewrite <-E2.
   rewrite Qabs.Qabs_pos...
   apply Qle_trans with (2 ^ Qdlog2 ε)%Qpos.
    apply Qle_trans with (Qabs.Qabs ('app_div_above (hd sN) (hd sD) (Qdlog2 ε - Z.log2_up l) - '0))...
    rewrite rings.preserves_0. unfold Qminus. rewrite Qplus_0_r.
    rewrite Qabs.Qabs_pos.
     now apply aq_div_above.
    apply Qle_trans with ('hd sN / 'hd sD : Q)...
    now apply aq_div_above.
   now apply (Qpos_dlog2_spec ε).
  simpl.
  apply FIX.
   now apply DivisionStream_tl.
  now apply _.
Qed.

(* Helper lemma for the inductive step of ARInfAltSum_length_ex *)
Lemma ARInfAltSum_length_ball `(d : DivisionStream sQ sN sD) (k l : Z) `(Pl : 4 ≤ l) :
  NearBy 0 (Qpos2QposInf (2 ^ (k - 1))) sQ → AQball_bool k (hd (ARInfAltSum_stream sN sD k l)) 0.
Proof.
  intros E.
  apply Is_true_eq_left.
  apply_simplified AQball_bool_true.
  rewrite rings.preserves_0.
  apply ball_weak_le with ((2 ^ (k - Z.log2_up l)) + (2 ^ (k - Z.log2_up l)) + 2 ^ (k - 1))%Qpos.
   simpl.
   assert (∀ n : Z, (2:Q) ^ n = 2 ^ (n - 1) + 2 ^ (n - 1)) as G.
    intros n.
    mc_setoid_replace n with (1 + (n - 1)) at 1 by ring.
    rewrite int_pow_S.
     now rewrite rings.plus_mult_distr_r, left_identity.
    apply (rings.is_ne_0 (2:Q)).
   posed_rewrite (G k).
   apply_simplified (semirings.plus_le_compat (R:=Q)); [| reflexivity].
   posed_rewrite (G (k - 1)).
   assert ((2:Q) ^ (k - Z.log2_up l) ≤ 2 ^ (k - 1 - 1)).
    apply int_pow.int_pow_exp_le.
     now apply semirings.le_1_2.
    rewrite <-associativity.
    apply (order_preserving (k +)).
    rewrite <-rings.negate_plus_distr.
    apply rings.flip_le_negate.
    replace (1 + 1:Z) with (Z.log2_up 4) by reflexivity.
    now apply Z.log2_up_le_mono.
   now apply semirings.plus_le_compat.
  eapply ball_triangle.
   2: now apply E.
  simpl. unfold app_div_above.
  rewrite <-(rings.plus_0_r (hd sQ)).
  destruct d as [? ? ? F]. rewrite F.
  unfold app_div_above. rewrite rings.preserves_plus.
  apply Qball_plus.
   now apply aq_div.
  rewrite aq_shift_1_correct.
  now apply Qball_0_r.
Qed.

(* 
So, as required, [ARInfAltSum_stream] has limit [0]. That is, for each [k], 
there exists an [i] such that [ARInfAltSum_stream[i]] is smaller than [2^k]. 
*)
Lemma ARInfAltSum_length_ex `(d : DivisionStream sQ sN sD) {zl : Limit sQ 0} (k l : Z) (Pl : 4 ≤ l) :
  LazyExists (λ s, AQball_bool k (hd s) 0) (ARInfAltSum_stream sN sD k l).
Proof.
  revert l Pl sN sD d.
  induction (zl (2 ^ (k - 1)))%Qpos as [sQ' E | ? ? IH]; intros l El sN sD d.
   left. now apply (ARInfAltSum_length_ball d k l El).
  right. intros _.
  simpl. apply (IH tt).
   now apply semirings.plus_le_compat_r.
  now destruct d.
Defined.

Section main_part.
Context `(d : DivisionStream sQ sN sD) {dnn : DecreasingNonNegative sQ} {zl : Limit sQ 0}.

(* 
Now we can compute the required length of the stream that we have to sum
(using [ARAltSum]).

Instead of using the proof of termination right away, we perform [big] steps first. We 
pick [big] such that computation will suffer from the implementation limits of Coq 
(e.g. a stack overflow) or runs out of memory, before we ever refer to the proof.
*)
Definition big := Eval vm_compute in (Z.nat_of_Z 50000).
Obligation Tactic := idtac.
Program Definition ARInfAltSum_length (k : Z) : nat := 4 + takeUntil_length 
  (λ s, AQball_bool k (hd s) 0) 
  (LazyExists_inc big (ARInfAltSum_stream (Str_nth_tl 4 sN) (Str_nth_tl 4 sD) k 4) _).
Next Obligation.
  intros.
  assert (Proper ((=) ==> iff) (λ s, AQball_bool k (hd s) 0)) by solve_proper.
  rewrite ARInfAltSum_stream_Str_nth_tl.
  rewrite 2!Str_nth_tl_plus.
  eapply ARInfAltSum_length_ex.
    eapply DivisionStream_Str_nth_tl. now eexact d.
   now apply Limit_Str_nth_tl.
  now vm_compute.
Qed.

(* 
Since we are using approximate division, we obviously have to sum some extra
terms so as to compensate for the loss of precision.
*)
Lemma ARInfAltSum_length_ge (ε : Qpos) :
  takeUntil_length _ (Limit_near sQ 0 ε) ≤ ARInfAltSum_length (Qdlog2 ε).
Proof.
  transitivity (4 + takeUntil_length _ (LazyExists_Str_nth_tl (Limit_near sQ 0 ε) (dnn_in_Qball_0_EventuallyForall sQ ε) 4)).
   apply takeUntil_length_Str_nth_tl.
  unfold ARInfAltSum_length.
  apply (order_preserving (4 +)).
  apply takeUntil_length_ForAllIf.
  apply ARInfAltSum_stream_preserves_ball.
   now apply DivisionStream_Str_nth_tl.
  now apply _.
Qed.

Lemma ARInfAltSum_length_pos (k : Z) :
  0 < ARInfAltSum_length k.
Proof.
  unfold ARInfAltSum_length.
  apply semirings.nonneg_plus_lt_compat_r.
   apply naturals.nat_nonneg.
  apply: (semirings.lt_0_4 (R:=nat)).
Qed.

Lemma ARAltSum_correct_aux (l : positive) (k : Z) :
  ball (l * 2 ^ k) ('ARAltSum sN sD (nat_of_P l) k) (take sQ (nat_of_P l) Qminus' 0).
Proof.
  revert sQ sN sD d dnn zl.
  induction l using Pind; intros.
   simpl. 
   rewrite rings.negate_0, rings.plus_0_r.
   rewrite Qminus'_correct. unfold Qminus. rewrite Qplus_0_r.
   setoid_replace (1%positive * 2 ^ k)%Qpos with (2 ^ k)%Qpos.
    (* ugly: make a duplicate of [d] to avoid Coq errors due to [d] being a section variable. *)
    generalize d. intros d'. destruct d' as [? ? ? E].
    rewrite E.
    now apply aq_div.
   unfold QposEq. simpl. now apply rings.mult_1_l.
  rewrite Psucc_S.
  simpl.
  rewrite rings.preserves_plus, rings.preserves_negate.
  rewrite Qminus'_correct. unfold Qminus.
  setoid_replace (Psucc l * 2 ^ k)%Qpos with (2 ^ k + l * 2 ^ k)%Qpos.
   apply Qball_plus.
    generalize d. intros d'. destruct d' as [? ? ? E]. (* ugly *)
    rewrite E.
    now apply aq_div.
   apply Qball_opp. 
   apply IHl; try apply _.
   now apply DivisionStream_tl.
  unfold QposEq. simpl. 
  rewrite Pplus_one_succ_l, Zpos_plus_distr, Q.Zplus_Qplus.
  now ring.
Qed.

Lemma ARAltSum_correct {l : nat} `(Pl : 0 < l) (k : Z) :
  ball (2 ^ k) ('ARAltSum sN sD l (k - Z.log2_up l)) (take sQ l Qminus' 0).
Proof.
  destruct l.
   now destruct (irreflexivity (<) (0 : nat)).
  apply ball_weak_le with (P_of_succ_nat l * 2 ^ (k - Z.log2_up (P_of_succ_nat l)))%Qpos.
   set (l':=P_of_succ_nat l).
   change ((l':Q) * 2 ^ (k - Z.log2_up l') ≤ 2 ^ k).
   rewrite int_pow_exp_plus; [| apply (rings.is_ne_0 (2:Q))].
   apply (order_reflecting ((2:Q) ^ Z.log2_up l' *.)).
   mc_setoid_replace (2 ^ Z.log2_up l' * ((l':Q) * (2 ^ k * 2 ^ (- Z.log2_up l')))) with (2 ^ k * (l':Q)).
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
   rewrite int_pow_negate.
   rewrite (commutativity (l' : Q)), (commutativity (2 ^ k)).
   rewrite <-associativity.
   rewrite associativity, dec_recip_inverse by solve_propholds.
   now apply left_identity.
  rewrite <-nat_of_P_of_succ_nat.
  rewrite convert_is_POS.
  now apply ARAltSum_correct_aux.
Qed.

(* Now we can finally compute the infinite alternating sum! *)
Definition ARInfAltSum_raw (ε : Qpos) : AQ_as_MetricSpace := 
  let εk:= Qdlog2 ε - 1 in 
  let l:= ARInfAltSum_length εk
  in ARAltSum sN sD l (εk - Z.log2_up (Z_of_nat l)).

Lemma ARInfAltSum_raw_correct (ε1 ε2 : Qpos) :
  ball (ε1 + ε2) ('ARInfAltSum_raw ε1) (InfiniteAlternatingSum_raw sQ ε2).
Proof.
  setoid_replace (ε1 + ε2)%Qpos with (ε1 * (1#2) + (ε1 * (1#2) + ε2))%Qpos by QposRing.
  eapply ball_triangle.
   apply ball_weak_le with (2 ^ (Qdlog2 ε1 - 1))%Qpos.
    change (2 ^ (Qdlog2 ε1 - 1) ≤ (ε1:Q) * (1 # 2)).
    rewrite Qdlog2_half by apply Qpos_prf.
    apply Qdlog2_spec. 
    apply pos_mult_compat. apply Qpos_prf. easy.
   unfold ARInfAltSum_raw.
   apply ARAltSum_correct.
   now apply ARInfAltSum_length_pos.
  apply (InfiniteAlternatingSum_further_alt _).
  rewrite (Qdlog2_half ε1) by apply Qpos_prf.
  apply (ARInfAltSum_length_ge (ε1 * (1 # 2))).
Qed.

Lemma ARInfAltSum_prf: is_RegularFunction_noInf _ ARInfAltSum_raw.
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

Definition ARInfAltSum := mkRegularFunction (0 : AQ_as_MetricSpace) ARInfAltSum_prf.


Lemma ARInfAltSum_correct:
   'ARInfAltSum = InfiniteAlternatingSum sQ.
Proof.
  intros ? ?.
  unfold cast, ARtoCR. simpl.
  now apply ARInfAltSum_raw_correct.
Qed.
End main_part.

End alt_sum.
