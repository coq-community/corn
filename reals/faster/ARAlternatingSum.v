Require Import Coq.QArith.Qabs.
Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.model.reals.CRreal.
Require Import 
  Coq.Program.Program CoRN.tactics.CornTac MathClasses.misc.workaround_tactics
  CoRN.model.totalorder.QposMinMax
  CoRN.model.metric2.Qmetric
  CoRN.reals.fast.CRAlternatingSum
  CoRN.reals.fast.CRstreams
  CoRN.util.Qdlog
  CoRN.reals.faster.ApproximateRationals CoRN.reals.faster.ARArith
  MathClasses.interfaces.abstract_algebra MathClasses.theory.int_pow MathClasses.theory.streams MathClasses.theory.series.

Section alt_sum.
Context `{AppRationals AQ}.

Add Ring Z : (rings.stdlib_ring_theory Z).
Local Coercion Is_true : bool >-> Sortclass.

(**
The goal of this section is to compute the infinite alternating sum. Since 
we do not have a precise division operation, we want to postpone divisions as 
long as possible. Hence we parametrize our infinite sum by a stream [sN] 
of numerators and a stream [sD] of denominators.

To compute an infinite series at precision epsilon, the finite number n of
terms to sum can be computed exactly, because sN n / sD n < epsilon/2 is
equivalent to sN n < (sD n) * epsilon/2, which does not involve the approximate
division. In the other epsilon/2, we can approximate the n divisions at
precision 2^k such as n*2^k < epsilon/2.
*)

Fixpoint ARAltSum (sN sD : Stream AQ) (l : nat) (k : Z) : AQ :=
  match l with 
  | O => 0
  | S l' => app_div (hd sN) (hd sD) k - ARAltSum (tl sN) (tl sD) l' k
  end.

(** 
However, we have to determine both the length [l] and the required precision 
[2^k] of dividing [sN] by [sQ].

Since Russell has already done a lot of work on this, we aim to reuse that.
Hence we define the following predicate to describe that our streams [sN]
and [sD] correspond to a stream [sQ] of Russell.
*)

CoInductive DivisionStream: Stream Q_as_MetricSpace → Stream AQ → Stream AQ → Prop :=
  division_stream_eq: ∀ sQ sN sD, 
    hd sQ = 'hd sN / 'hd sD
    → DivisionStream (tl sQ) (tl sN) (tl sD) → DivisionStream sQ sN sD.

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

(** 
Now, [ARInfAltSum_stream sN sD k 0] represents a stream of estimates [sN / sD] 
with logarithmically increasing precision starting with precision [2^k]. We 
compute the length by walking through the stream [ARInfAltSum_stream sN sD k 0] 
until we have an element that has an upper estimate below the required precision.
*)

CoFixpoint ARInfAltSum_stream (sN sD : Stream AQ) (k l : Z) : Stream AQ := Cons 
  (app_div_above (hd sN) (hd sD) (k - Z.log2_up l))
  (ARInfAltSum_stream (tl sN) (tl sD) k (l + 1)).

(** Before we prove that this stream has limit 0, we state some auxiliary stuff. *)

Definition ARInfAltSum_stream_tl sN sD k l :
  tl (ARInfAltSum_stream sN sD k l) = ARInfAltSum_stream (tl sN) (tl sD) k (l + 1).
Proof.
  revert sN sD k l.
  now constructor.
Qed.

Definition ARInfAltSum_stream_Str_nth_tl sN sD k l n :
  Str_nth_tl n (ARInfAltSum_stream sN sD k l) = ARInfAltSum_stream (Str_nth_tl n sN) (Str_nth_tl n sD) k (l + Z.of_nat n).
Proof.
  induction n.
   change (l + Z.of_nat 0%nat)%Z with (l + 0). now rewrite rings.plus_0_r.
  rewrite !Str_nth_tl_S.
  replace (l + Z.of_nat (S n))%Z with ((l + Z.of_nat n) + 1)%Z.
   rewrite IHn. now apply ARInfAltSum_stream_tl.
  change (l + 'n + 1 = l + '(1 + n)).
  rewrite rings.preserves_plus, rings.preserves_1. ring.
Qed.

(** 
If a certain coordinate of [ARInfAltSum_stream] is in the ball, then the 
corresponding coordinate in [sQ] is in the ball too.
*)

Lemma ARInfAltSum_stream_preserves_ball
      `(d : DivisionStream sQ sN sD) {dnn : DecreasingNonNegative sQ}
      (ε : Qpos) (l : Z) :
  ForAllIf (λ s : ∞ AQ, AQball_bool (Qdlog2 (proj1_sig ε)) (hd s) 0)
           (λ s : ∞ Q, Qball_ex_bool ε (hd s) 0) 
           (ARInfAltSum_stream sN sD (Qdlog2 (proj1_sig ε)) l) sQ.
Proof with auto.
  revert l sQ sN sD d dnn.
  cofix FIX; intros l sQ sN sD d dnn.
  constructor.
   intros E. 
   unfold Qball_ex_bool.
   destruct (ball_ex_dec Q_as_MetricSpace Qmetric_dec (Qpos2QposInf ε) (@hd Q sQ) (0#1)).
   constructor.
   apply Is_true_eq_true in E. apply AQball_bool_true in E. 
   simpl in *.
   destruct d as [sQ sN sD E2]. contradict n. rewrite E2. 
   apply Qball_Qabs. apply Qball_Qabs in E.
   unfold Qminus. rewrite Qplus_0_r.
   assert ((0:Q) ≤  'hd sN / 'hd sD).
    destruct dnn as [[? ?]].
    transitivity (hd (tl sQ))...
    now rewrite <-E2.
   rewrite Qabs.Qabs_pos...
   apply Qle_trans with (2 ^ Qdlog2 (proj1_sig ε))%Qpos.
    apply Qle_trans with (Qabs.Qabs ('app_div_above (hd sN) (hd sD) (Qdlog2 (proj1_sig ε) - Z.log2_up l) - '0))...
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

(** Helper lemma for the inductive step of ARInfAltSum_length_ex *)

Lemma ARInfAltSum_length_ball `(d : DivisionStream sQ sN sD) (k l : Z) `(Pl : 4 ≤ l) :
  NearBy 0 (Qpos2QposInf (2 ^ (k - 1))) sQ → AQball_bool k (hd (ARInfAltSum_stream sN sD k l)) 0.
Proof.
  intros E.
  apply Is_true_eq_left.
  apply_simplified AQball_bool_true.
  rewrite rings.preserves_0.
  apply ball_weak_le
    with (proj1_sig ((2 ^ (k - Z.log2_up l)) + (2 ^ (k - Z.log2_up l)) + 2 ^ (k - 1))%Qpos).
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
  assert (0 < (2 ^ (k - Z.log2_up l)))%Q.
  { apply Q.Qpower_0_lt. reflexivity. }
  apply (Qball_0_r (exist _ _ H5)).
Qed.

(** 
So, as required, [ARInfAltSum_stream] has limit [0]. That is, for each [k], 
there exists an [i] such that [ARInfAltSum_stream[i]] is smaller than [2^k]. 
*)

Lemma ARInfAltSum_length_ex `(d : DivisionStream sQ sN sD) {zl : Limit sQ 0} (k l : Z) (Pl : 4 ≤ l) :
  LazyExists (λ s, AQball_bool k (hd s) 0) (ARInfAltSum_stream sN sD k l).
Proof.
  revert l Pl sN sD d.
  pose proof (zl (Qpos_power 2 (k - 1)))%Qpos as help.
  clear zl. induction help as [sQ' E | ? ? IH]; intros l El sN sD d.
   left. now apply (ARInfAltSum_length_ball d k l El).
  right. intros _.
  simpl. apply (IH tt).
   now apply semirings.plus_le_compat_r.
  now destruct d.
Defined.

Section main_part.
  Context `(d : DivisionStream sQ sN sD)
          {dnn : DecreasingNonNegative sQ} {zl : Limit sQ 0}.

(** 
Now we can compute the required length of the stream that we have to sum
(using [ARAltSum]).

Instead of using the proof of termination right away, we perform [big] steps first. We 
pick [big] such that computation will suffer from the implementation limits of Coq 
(e.g. a stack overflow) or runs out of memory, before we ever refer to the proof.
*)

Definition big : nat := Eval vm_compute in (Z.nat_of_Z 5000).
Lemma ARInfAltSum_length_aux : ∀ k : Z,
    LazyExists (λ s : ∞ AQ, AQball_bool k (hd s) 0)
               (Str_nth_tl big (ARInfAltSum_stream (Str_nth_tl 4 sN) (Str_nth_tl 4 sD) k 4)).
Proof.
  intro k.
  assert (Proper ((=) ==> iff) (λ s, AQball_bool k (hd s) 0)) by solve_proper.
  rewrite (ARInfAltSum_stream_Str_nth_tl _ _ k 4 big).
  rewrite 2!Str_nth_tl_plus.
  eapply ARInfAltSum_length_ex.
    eapply DivisionStream_Str_nth_tl. now eexact d.
   exact (Limit_Str_nth_tl zl (big + 4)).
  now vm_compute.
Qed. 

Definition ARInfAltSum_length (k : Z) : nat
  := 4 + takeUntil_length 
  (λ s, AQball_bool k (hd s) 0) 
  (LazyExists_inc big (ARInfAltSum_stream (Str_nth_tl 4 sN) (Str_nth_tl 4 sD) k 4)
  (ARInfAltSum_length_aux k)).

(**
Since we are using approximate division, we obviously have to sum some extra
terms so as to compensate for the loss of precision.
*)

Lemma ARInfAltSum_length_ge (ε : Qpos) :
  takeUntil_length _ (Limit_near_zero (zl ε))
  ≤ ARInfAltSum_length (Qdlog2 (proj1_sig ε)).
Proof.
  transitivity (4 + takeUntil_length _ (LazyExists_Str_nth_tl (Limit_near_zero (zl ε)) (dnn_in_Qball_0_EventuallyForall sQ ε) 4)).
   apply takeUntil_length_Str_nth_tl.
  unfold ARInfAltSum_length. 
  (* Regression, the following line was not necessary before. *)
  change (Init.Nat.add (S (S (S (S O))))) with (plus (plus one (plus one (plus one (S 0))))). 
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
   apply le_n_S, le_0_n.
Qed.

(* The approximations of divisions cause in total an error of l*2^k. *)
Lemma ARAltSum_correct_aux (l : positive) (k : Z) :
  ball (proj1_sig ((l#1) * Qpos_power 2 k)%Qpos)
       ('ARAltSum sN sD (nat_of_P l) k) (take sQ (nat_of_P l) Qminus' 0).
Proof.
  revert sQ sN sD d dnn zl.
  induction l using Pind; intros.
   simpl. 
   rewrite rings.negate_0, rings.plus_0_r.
   rewrite Qminus'_correct. unfold Qminus. rewrite Qplus_0_r.
   rewrite Qmult_1_l.
    (* ugly: make a duplicate of [d] to avoid Coq errors due to [d] being a section variable. *)
    generalize d. intros d'. destruct d' as [? ? ? E].
    rewrite E.
    now apply aq_div.
  rewrite Psucc_S.
  simpl.
  rewrite rings.preserves_plus, rings.preserves_negate.
  rewrite Qminus'_correct. unfold Qminus.
  assert (QposEq ((Pos.succ l #1) * Qpos_power 2 k)
                 (Qpos_power 2 k + (l#1) * Qpos_power 2 k)).
  { unfold QposEq. simpl. 
    rewrite <- Pos.add_1_l. 
    rewrite Zpos_plus_distr.
    setoid_replace (1 + Zpos l # 1) with (1 + (Zpos l # 1))%Q. ring.
    unfold Qplus, Qeq, Qnum, Qden. rewrite Pos.mul_1_l.
    do 4 rewrite Z.mul_1_r. reflexivity. }
  unfold QposEq in H5. rewrite H5. clear H5.
   apply Qball_plus.
    generalize d. intros d'. destruct d' as [? ? ? E]. (* ugly *)
    rewrite E.
    now apply aq_div.
   apply Qball_opp. 
   apply IHl; try apply _.
   now apply DivisionStream_tl.
Qed.

Lemma ARAltSum_correct {l : nat} `(Pl : 0 < l) (k : Z) :
  ball (2 ^ k) ('ARAltSum sN sD l (k - Z.log2_up (Z.of_nat l))) (take sQ l Qminus' 0).
Proof.
  destruct l.
   now destruct (irreflexivity (<) (0 : nat)).
   apply ball_weak_le
     with (proj1_sig ((P_of_succ_nat l#1)
                      * 2 ^ (k - Z.log2_up (Zpos (P_of_succ_nat l))))%Qpos).
   set (l':=P_of_succ_nat l).
   change ((inject_Z (Zpos l')) * 2 ^ (k - Z.log2_up (Zpos l')) ≤ 2 ^ k).
   rewrite int_pow_exp_plus; [| apply (rings.is_ne_0 (2:Q))].
   apply (order_reflecting ((2:Q) ^ Z.log2_up (Zpos l') *.)).
   mc_setoid_replace (2 ^ Z.log2_up (Zpos l') * ((inject_Z (Zpos l')) * (2 ^ k * 2 ^ (- Z.log2_up (Zpos l')))))
     with (2 ^ k * (inject_Z (Zpos l'))).
    rewrite (commutativity _ ((2:Q) ^ k)).
    apply (order_preserving (2 ^ k *.)).
    replace (2:Q) with (inject_Z 2) by reflexivity.
    rewrite <-Qpower.Zpower_Qpower.
     apply (order_preserving _).
     destruct (decide ((Zpos l') = 1)) as [E|E].
      now rewrite E.
     apply Z.log2_up_spec. 
     auto with zarith.
    now apply Z.log2_up_nonneg.
   rewrite int_pow_negate.
   rewrite (commutativity (inject_Z (Zpos l'))), (commutativity (2 ^ k)).
   rewrite <-associativity.
   rewrite associativity, dec_recip_inverse by solve_propholds.
   now apply left_identity.
  rewrite <-nat_of_P_of_succ_nat.
  rewrite convert_is_POS.
  now apply ARAltSum_correct_aux.
Qed.

(** Now we can finally compute the infinite alternating sum! *)

Definition ARInfAltSum_raw (ε : Qpos) : AQ_as_MetricSpace := 
  let εk:= Qdlog2 (proj1_sig ε) - 1 in 
  let l:= ARInfAltSum_length εk
  in ARAltSum sN sD l (εk - Z.log2_up (Z_of_nat l)).

Lemma ARInfAltSum_raw_correct (ε1 ε2 : Qpos) :
  ball (proj1_sig ε1 + proj1_sig ε2) ('ARInfAltSum_raw ε1) (InfiniteAlternatingSum_raw sQ ε2).
Proof.
  setoid_replace (proj1_sig ε1 + proj1_sig ε2)%Q
    with (proj1_sig (ε1 * (1#2) + (ε1 * (1#2) + ε2))%Qpos)
    by (simpl; ring).
  eapply ball_triangle.
   apply ball_weak_le with (2 ^ (Qdlog2 (proj1_sig ε1) - 1))%Qpos.
    change (2 ^ (Qdlog2 (proj1_sig ε1) - 1) ≤ (proj1_sig ε1) * (1 # 2)).
    rewrite Qdlog2_half by apply Qpos_ispos.
    apply Qdlog2_spec. 
    apply pos_mult_compat. apply Qpos_ispos. easy.
   unfold ARInfAltSum_raw.
   apply ARAltSum_correct.
   now apply ARInfAltSum_length_pos.
  apply (InfiniteAlternatingSum_further_alt _).
  rewrite (Qdlog2_half (proj1_sig ε1)) by apply Qpos_ispos.
  apply (ARInfAltSum_length_ge (ε1 * (1 # 2))).
Qed.

Lemma ARInfAltSum_prf: is_RegularFunction_noInf _ ARInfAltSum_raw.
Proof.
  intros ε1 ε2. simpl.
  apply ball_closed. intros δ dpos.
  setoid_replace (proj1_sig ε1 + proj1_sig ε2 + δ)%Q
    with (proj1_sig (ε1 + (1#4) * exist _ _ dpos
                     + ((1#4) * exist _ _ dpos + (1#4) * exist _ _ dpos
                        + (ε2 + (1#4) * exist _ _ dpos)))%Qpos)
    by (simpl; ring).
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
  rewrite Qplus_0_r.
  now apply ARInfAltSum_raw_correct.
Qed.
End main_part.
End alt_sum.


Section RationalStreamSum.

  Context `{AppRationals AQ}.

  (* For exponential, f p n d := (n*a, d*p).
     We might need to generalize positive to a more complicated
     state type later. *)
  Variable f : positive*(AQ*AQ) -> AQ*AQ.
  Definition fS x : positive*(AQ*AQ) := (Pos.succ (fst x), f x).
  Definition fSsum (k:Z) (x : positive*(AQ*AQ)*AQ) : positive*(AQ*AQ)*AQ
    := let (y,s) := x in
       let (a,b) := fS y in
       (a, b, s + app_div (fst b) (snd b) k).

  Hypothesis denomPos : forall x, 0 < snd (snd x) -> 0 < snd (f x).

  Lemma denomPos_iter : forall p x,
      0 < snd (snd x) -> 
      0 < snd (snd (CRstreams.iterate _ fS p x)).
  Proof.
    apply (Pos.peano_ind (fun p => forall x,
      0 < snd (snd x) -> 
      0 < snd (snd (CRstreams.iterate _ fS p x)))).
    - intros. simpl. apply denomPos, H5.
    - intros. rewrite iterate_succ, iterate_shift.
      apply H5. simpl. 
      apply denomPos, H6.
  Qed. 

  (* Find first index where num/denom <= e. *)
  Definition IsStopIndex x (e : AQ) (candidate : positive) : Prop
    := let (_,v) := CRstreams.iterate _ fS candidate (xH,x) in
       le (abs (fst v)) (snd v * e).
  Definition StopIndex x (e : AQ) (candidate : positive) : positive
    := Pos.pred (fst (iterate_stop
              _ fS (fun y : positive*(AQ*AQ)
                    => bool_decide_rel le (abs (fst (snd y))) ((snd (snd y))*e))
              candidate (xH, x))).

  Lemma fS_fst : forall (p:positive) x,
      fst (CRstreams.iterate (positive and AQ and AQ) fS p (1%positive, x))
          ≡ Pos.succ p.
  Proof.
    apply (Pos.peano_ind (fun p => forall (x : AQ and AQ),
    fst (CRstreams.iterate (positive and AQ and AQ) fS p (1%positive, x)) ≡ Pos.succ p)).
    - reflexivity.
    - intros. rewrite iterate_succ. simpl.
      apply f_equal, H5.
  Qed. 

  Lemma StopIndex_correct : forall x (e:AQ) (p r : positive),
      IsStopIndex x e p
      -> (forall q:positive, Pos.lt q p -> ~IsStopIndex x e q)
      -> Pos.le p r
      -> StopIndex x e r ≡ p.
  Proof.
    unfold IsStopIndex. intros.
    unfold StopIndex.
    destruct (iterate_stop_correct
                  _ fS (λ y : positive and AQ and AQ,
                              bool_decide_rel
                                le (abs (fst (snd y))) (snd (snd y) * e0))
               r (xH,x)) as [s [req [H8 H9]]].
    rewrite req, fS_fst, Pos.pred_succ. clear req.
    destruct H9.
    - subst r. apply Pos.le_lteq in H7.
      destruct H7. 2: symmetry; exact H7.
      exfalso. specialize (H8 p H7).
      apply bool_decide_rel_false in H8.
      contradict H8. 
      destruct (CRstreams.iterate _ fS p (1%positive, x)).
      exact H5.
    - destruct H9.
      apply bool_decide_rel_true in H10.
      clear H7 H9 r.
      destruct (Pos.lt_total s p).
      + exfalso. specialize (H6 s H7).
        contradict H6.
        destruct (CRstreams.iterate _ fS s (1%positive, x)).
        exact H10.
      + destruct H7. exact H7. exfalso.
        specialize (H8 p H7).
        apply bool_decide_rel_false in H8.
        contradict H8.
      destruct (CRstreams.iterate _ fS p (1%positive, x)).
      exact H5.
  Qed.

  Lemma StopIndex_stop_fuel : forall x (e:AQ) (candidate : positive),
      (forall p:positive, Pos.lt p candidate -> ~IsStopIndex x e p)
      -> StopIndex x e candidate ≡ candidate.
  Proof.
    intros. unfold StopIndex.
    destruct (iterate_stop_correct
                  _ fS (λ y : positive and AQ and AQ,
                              bool_decide_rel
                                le (abs (fst (snd y))) (snd (snd y) * e0))
               candidate (xH,x)) as [r [req [H6 H7]]].
    rewrite req, fS_fst, Pos.pred_succ. clear req.
    destruct H7. symmetry. exact H7.
    destruct H7. exfalso. clear H6.
    specialize (H5 r H7).
    apply bool_decide_rel_true in H8.
    contradict H5.
    unfold IsStopIndex.
    destruct (CRstreams.iterate _ fS r (1%positive, x)).
    exact H8.
  Qed. 

  (* Approximate the infinite series at precision e.
     The precision i:Z in fSum satisfies n*2^i <= e/2. *)
  Definition app_inverse_below (q : Qpos) : AQ
    := AppInverse0 ((3#4)*proj1_sig q) ((1#4)*q)%Qpos.

  Lemma app_inverse_below_pos : forall q:Qpos, 0 < app_inverse_below q.
  Proof.
    intros. unfold app_inverse_below.
    destruct aq_dense_embedding.
    specialize (dense_inverse ((3 # 4) * ` q)%Q ((1#4)*q)%Qpos).
    apply AbsSmall_Qabs, Qabs_Qle_condition in dense_inverse.
    destruct dense_inverse as [H5 _].
    simpl in H5.
    apply (Qplus_le_r _ _ ((3 # 4) * ` q)) in H5.
    ring_simplify in H5.
    destruct aq_strict_order_embed.
    apply strict_order_embedding_reflecting.
    refine (Qlt_le_trans _ ((8 # 16) * ` q) _ _ H5).
    rewrite rings.preserves_0.
    apply (Qpos_ispos ((8#16)*q)).
  Qed.

  Lemma app_inverse_below_correct : forall q:Qpos,
      AQtoQ (app_inverse_below q) <= proj1_sig q.
  Proof.
    intros. unfold app_inverse_below.
    destruct aq_dense_embedding.
    specialize (dense_inverse ((3 # 4) * ` q)%Q ((1#4)*q)%Qpos).
    apply AbsSmall_Qabs, Qabs_Qle_condition in dense_inverse.
    destruct dense_inverse as [_ H5].
    simpl in H5.
    apply (Qplus_le_r _ _ ((3 # 4) * ` q)) in H5.
    ring_simplify in H5. exact H5.
  Qed.

  (* cvmod : AQ->positive would not improve this definition, because an
     AQtoQ would be almost inevitable to produce a boxed positive.
     Besides, Q will allow an easier interaction with fast reals streams. *)
  Definition AltSeries_raw (x : AQ*AQ) (cvmod : Qpos -> positive) (e:QposInf) : AQ
    := match e with 
       | Qpos2QposInf d
         => let ae := app_inverse_below (d*(1#2)) in
           let n := StopIndex x ae (cvmod (d * (1#2))%Qpos) in
           snd (CRstreams.iterate _ (fSsum (Qdlog2 (proj1_sig d * (1#2*n)))) n (xH,x,0))
       | QposInfinity => 0
       end.

  (* To prove the correctness of the limit, convert the stream f into
     a stream g of exact rationals. g could be defined as the zip of
     f with the exact divisions, but it's more flexible to take g from
     outside, so that in addition we prove the equality of series. *)
  Variable X : Type.
  Variable g : X*Q -> X*Q.
  Variable fInit : AQ*AQ.
  Variable gInit : X*Q.

  Hypothesis g_pth : forall p:positive,
      Str_pth _ g p gInit
      == let (y,r) := CRstreams.iterate _ fS p (xH, fInit) in
         AQtoQ (fst r) / AQtoQ (snd r).

  Lemma abs_div_aqtoq_shift : forall (q r s : AQ),
      0 < r ->
      (Qabs (AQtoQ q / AQtoQ r) <= AQtoQ s
       <-> le (abs q) (r * s)).
  Proof.
    assert (forall q:AQ, Qabs (AQtoQ q) == AQtoQ (abs q)) as preserves_abs.
    { intros. rewrite abs.preserves_abs. reflexivity. } 
    assert (forall q r:AQ, AQtoQ (q*r) == AQtoQ q*AQtoQ r) as preserves_mult.
    { intros. rewrite rings.preserves_mult. reflexivity. } 
    intros.
    assert (0 < AQtoQ r).
    { rewrite <- rings.preserves_0.
      destruct aq_strict_order_embed.
      apply strict_order_embedding_preserving. exact H5. } 
    split.
    - intros. unfold Qdiv in H7.
      rewrite Qabs_Qmult, Q.Qabs_Qinv in H7.
      rewrite (Qabs_pos (AQtoQ r)) in H7.
      rewrite preserves_abs, Qmult_comm in H7.
      apply (Qmult_le_l _ _ (AQtoQ r)) in H7.
      2: exact H6.
      rewrite Qmult_assoc, Qmult_inv_r, Qmult_1_l in H7.
      rewrite <- preserves_mult in H7.
      destruct aq_order_embed, order_embedding_reflecting.
      apply order_reflecting in H7.
      exact H7.
      intro abs. rewrite abs in H6. exact (Qlt_irrefl 0 H6).
      apply Qlt_le_weak, H6. 
    - intros. unfold Qdiv.
      rewrite Qabs_Qmult, Q.Qabs_Qinv.
      rewrite (Qabs_pos (AQtoQ r)).
      rewrite preserves_abs.
      rewrite Qmult_comm.
      apply (Qmult_le_l _ _ (AQtoQ r)).
      exact H6.
      rewrite Qmult_assoc, Qmult_inv_r, Qmult_1_l. 
      rewrite <- preserves_mult.
      destruct aq_order_embed.
      apply order_embedding_preserving.
      exact H7.
      intro abs. rewrite abs in H6. exact (Qlt_irrefl 0 H6).
      apply Qlt_le_weak, H6. 
  Qed.

  Lemma fSsum_fst : forall p k,
      fst (CRstreams.iterate _ (fSsum k) p (1%positive, fInit, 0))
          ≡ CRstreams.iterate _ fS p (xH,fInit).
  Proof.
    apply (Pos.peano_ind (fun p => forall k,
      fst (CRstreams.iterate _ (fSsum k) p (1%positive, fInit, 0))
          ≡ CRstreams.iterate _ fS p (xH,fInit))).
    - reflexivity.
    - intros. rewrite iterate_succ, iterate_succ.
      rewrite <- (H5 k). unfold fSsum at 1.
      destruct (CRstreams.iterate ((positive and AQ and AQ) and AQ) 
                                  (fSsum k) p (1%positive, fInit, 0)).
      reflexivity.
  Qed.

  (* Sum p terms, the error between each is below e. *)
  Lemma div_approx_error : ∀ (p:positive) (e:Qpos),
    Qball (` e * inject_Z (Zpos p))
      (AQtoQ (snd (CRstreams.iterate
                     _ (fSsum (Qdlog2 (` e))) p (1%positive, fInit, 0))))
      (snd (CRstreams.iterate
              _ (λ y : X*Q*Q,
                       let (z, r) := g (fst y) in (z, r, Qred (r + snd y))) p
              (gInit, 0))).
  Proof.
    apply (Pos.peano_ind (fun p => forall (e:Qpos),
    Qball (` e * inject_Z (Zpos p))
      (AQtoQ (snd (CRstreams.iterate
                     _ (fSsum (Qdlog2 (` e))) p (1%positive, fInit, 0))))
      (snd (CRstreams.iterate
              _ (λ y : X*Q*Q,
                       let (z, r) := g (fst y) in (z, r, Qred (r + snd y))) p
              (gInit, 0))))).
    - intros. rewrite iterate_one, iterate_one.
      rewrite Qmult_1_r.
      unfold fSsum, fS.
      unfold snd at 1. unfold fst at 2.
      pose proof (g_pth 1).
      unfold Str_pth in H5. simpl in H5.
      unfold snd at 3.
      replace (snd (let (z, r) := g gInit in (z, r, Qred (r + zero))))
        with (Qred (snd (g gInit) + 0))
        by (destruct (g gInit); reflexivity).
      rewrite Qred_correct, Qplus_0_r, H5.
      clear H5.
      destruct (f (1%positive, fInit)) as [u v].
      unfold snd, fst.
      rewrite rings.plus_0_l.
      apply ball_weak_le with (e:= (2 ^ Qdlog2 (` e0))%Q).
      apply Qdlog2_spec, Qpos_ispos.
      apply aq_div.
    - intros.
      rewrite iterate_succ.
      unfold fSsum at 1.
      specialize (H5 e0).
      pose proof (fSsum_fst p (Qdlog2 (` e0))).
      destruct (CRstreams.iterate _ (fSsum (Qdlog2 (` e0))) p (1%positive, fInit, 0))
        as [u approx_sum].
      unfold snd in H5 at 1.
      unfold fst in H6.
      change (snd
          (let (a, b) := fS u in (a, b, approx_sum + app_div (fst b) (snd b) (Qdlog2 (` e0)))))
        with (approx_sum + app_div (fst (snd (fS u))) (snd (snd (fS u))) (Qdlog2 (` e0))).
      rewrite iterate_succ, SumStream_fst_red.
      unfold fst at 2.
      rewrite <- iterate_succ.
      pose proof (g_pth (Pos.succ p)) as H7.
      unfold Str_pth in H7.
      destruct (CRstreams.iterate (X and Q) g (Pos.succ p) gInit).
      unfold snd at 4. unfold snd in H7 at 1.
      rewrite Qred_correct, H7. clear H7 q x.
      rewrite iterate_succ.
      rewrite <- H6. clear H6.
      destruct (fS u) as [v w].
      change (snd (v,w)) with w.
      clear v.
      destruct (CRstreams.iterate _
          (λ y : (X and Q) and Q,
             let (z, r) := g (fst y) in (z, r, Qred (r + snd y))) p
          (gInit, 0))
        as [v exact_sum].
      unfold snd in H5.
      unfold snd at 3. clear v.
      destruct w as [v w].
      unfold fst, snd.
      rewrite rings.preserves_plus. 
      apply AbsSmall_Qabs.
      apply AbsSmall_Qabs in H5.
      setoid_replace ((AQtoQ approx_sum + AQtoQ (app_div v w (Qdlog2 (` e0)))) -
                      (AQtoQ v / AQtoQ w + exact_sum))%Q
        with (AQtoQ approx_sum - exact_sum
              + (AQtoQ (app_div v w (Qdlog2 (` e0))) - (AQtoQ v / AQtoQ w)))%Q
        by ring.
      apply (Qle_trans _ _ _ (Qabs_triangle _ _)).
      rewrite <- Pos.add_1_r, Pos2Z.inj_add, inject_Z_plus.
      rewrite Qmult_plus_distr_r, Qmult_1_r.
      apply Qplus_le_compat. exact H5.
      apply AbsSmall_Qabs.
      change (Qball (` e0) (AQtoQ (app_div v w (Qdlog2 (` e0)))) (AQtoQ v / AQtoQ w)).
      apply ball_weak_le with (e:= (2 ^ Qdlog2 (` e0))%Q).
      apply Qdlog2_spec, Qpos_ispos.
      apply aq_div.
  Qed.
   
  (* SumStream is the implementation of CRAlternatingSum.AltSeries_raw.
     Errors only come from approximate divisions here. *)
  Lemma AltSeries_raw_correct : forall (e:Qpos) (cvmod : Qpos -> positive),
      0 < snd fInit -> 
      Qball (` e * (1 # 2))
            (AQtoQ (AltSeries_raw fInit cvmod e))
            (SumStream
               _ g gInit
               (cvmod (e * (1 # 2))%Qpos) (* fuel *)
               (AQposAsQpos (exist _ _ (app_inverse_below_pos (e * (1 # 2))%Qpos)))).
  Proof. 
    intros e0 cvmod xpos.
    unfold SumStream.
    change (` (AQposAsQpos
                 (app_inverse_below (e0 * (1 # 2))%Qpos
                            ↾ app_inverse_below_pos (e0 * (1 # 2))%Qpos)))
      with (AQtoQ (app_inverse_below (e0 * (1 # 2))%Qpos)).
    pose proof (iterate_stop_correct
                  _ (λ y : (X and Q) and Q,
                           let (z, r) := g (fst y) in (z, r, Qred (r + snd y)))
                  (λ y : (X and Q) and Q,
             Qle_bool (Qabs (snd (fst y)))
               (AQtoQ (app_inverse_below (e0 * (1 # 2) ↾ eq_refl))))
              (cvmod (e0 * (1 # 2))%Qpos) (gInit,0))
      as [p [qeq [H5 H6]]].
    rewrite qeq. clear qeq.
    unfold AltSeries_raw.
    replace (StopIndex fInit (app_inverse_below (e0 * (1 # 2) ↾ eq_refl))
                       (cvmod (e0 * (1 # 2))%Qpos))
      with p.
    setoid_replace (` e0 * (1 # 2))%Q
      with (` e0 * (1 # 2 * p) * inject_Z (Zpos p))%Q.
    apply (div_approx_error p (e0*(1#2*p))).
    rewrite <- Qmult_assoc. apply Qmult_comp. reflexivity.
    unfold Qmult, Qeq; simpl.
    rewrite Pos.mul_1_r, Pos.mul_comm. reflexivity.
    rewrite SumStream_fst_red in H6.
    destruct H6 as [fuel | predicate].
    - (* The sum consumes all the fuel. *)
      subst p.
      symmetry. apply StopIndex_stop_fuel.
      intros. specialize (H5 p H6).
      rewrite SumStream_fst_red in H5.
      unfold fst in H5.
      unfold IsStopIndex. intro abs.
      pose proof (g_pth p). unfold Str_pth in H7.
      rewrite H7 in H5. clear H7.
      pose proof (denomPos_iter p (xH,fInit) xpos).
      destruct (CRstreams.iterate _ fS p (1%positive, fInit))
        as [u v].
      apply abs_div_aqtoq_shift in abs.
      apply Qle_bool_iff in abs.
      rewrite abs in H5. discriminate.
      exact H7.
    - (* The sum stops before the fuel, because of the predicate. *)
      assert (IsStopIndex fInit (app_inverse_below (e0 * (1 # 2))%Qpos) p) as pstop.
      { destruct predicate as [_ predicate]. unfold IsStopIndex.
        apply Qle_bool_iff in predicate.
        simpl in predicate.
        pose proof (g_pth p).
        unfold Str_pth in H6. rewrite H6 in predicate. clear H6.
        pose proof (denomPos_iter p (xH,fInit) xpos). 
        destruct (CRstreams.iterate _ fS p (1%positive, fInit)).
        apply abs_div_aqtoq_shift. exact H6.
        exact predicate. } 
      symmetry. apply StopIndex_correct.
      exact pstop. intros.
      unfold IsStopIndex.
      specialize (H5 q H6).
      rewrite SumStream_fst_red in H5. unfold fst in H5.
      pose proof (g_pth q).
      unfold Str_pth in H7. rewrite H7 in H5. clear H7.
      pose proof (denomPos_iter q (xH,fInit) xpos).
      destruct (CRstreams.iterate _ fS q (1%positive, fInit)).
      intro abs.
      apply abs_div_aqtoq_shift in abs.
      apply Qle_bool_iff in abs.
      rewrite abs in H5. discriminate.
      exact H7. apply Pos.lt_le_incl, predicate.
  Qed.

  Lemma AltSeries_raw_prf : forall (cvmod : Qpos -> positive),
      Str_alt_decr _ g gInit
      -> 0 < snd fInit
      -> Limit_zero _ g gInit cvmod -> 
      is_RegularFunction (@ball AQ_as_MetricSpace) (AltSeries_raw fInit cvmod).
  Proof.
    intros cvmod g_decr xpos lz e1 e2.
    setoid_replace (`e1 + `e2)%Q
      with (`e1*(1#2) + (`e1*(1#2) + `e2*(1#2) + `e2*(1#2)))%Q by ring.
    apply (ball_triangle Q_as_MetricSpace _ _ _
      (SumStream
                   _ g gInit
                   (cvmod (e1 * (1 # 2))%Qpos)
                   (AQposAsQpos (exist _ _ (app_inverse_below_pos (e1 * (1 # 2))%Qpos))))).
    2: apply (ball_triangle Q_as_MetricSpace _ _ _
      (SumStream
                   _ g gInit
                   (cvmod (e2 * (1 # 2))%Qpos)
                   (AQposAsQpos (exist _ _ (app_inverse_below_pos (e2 * (1 # 2))%Qpos))))).
    - exact (AltSeries_raw_correct _ _ xpos).
    - apply (AltSeries_further
               _ g gInit _ _ _ _
               (e1 * (1 # 2))%Qpos (e2 * (1 # 2))%Qpos g_decr).
      apply lz. apply lz.
      apply app_inverse_below_correct.
      apply app_inverse_below_correct.
    - apply ball_sym, (AltSeries_raw_correct _ _ xpos).
  Qed.

  Definition AltSeries (cvmod : Qpos -> positive)
      (decr : Str_alt_decr _ g gInit)
      (xpos : 0 < snd fInit)
      (lz : Limit_zero _ g gInit cvmod) : AR
    := Build_RegularFunction (AltSeries_raw_prf cvmod decr xpos lz).

  Lemma AltSeries_correct : forall (cvmod : Qpos -> positive)
      (decr : Str_alt_decr _ g gInit)
      (xpos : 0 < snd fInit)
      (lz : Limit_zero _ g gInit cvmod),
      (ARtoCR (AltSeries cvmod decr xpos lz)
       == CRAlternatingSum.AltSeries _ g gInit cvmod decr lz)%CR.
  Proof.
    intros.
    apply regFunEq_equiv, regFunEq_e.
    intro d.
    change (approximate (CRAlternatingSum.AltSeries X g gInit cvmod decr lz) d)
      with (SumStream X g gInit (cvmod d) d).
    setoid_replace (` d + ` d)%Q with (`d*(1#2) + (`d*(1#2)+` d))%Q by ring.
    apply (ball_triangle _ _ _ _ _ _ (AltSeries_raw_correct d cvmod xpos)).
    apply (AltSeries_further
             _ g gInit
             (cvmod (d * (1 # 2))%Qpos) (cvmod d)
             _ _ (d*(1#2))%Qpos d decr).
    apply lz. apply lz.
    apply app_inverse_below_correct.
    apply Qle_refl. 
  Qed.


End RationalStreamSum.
