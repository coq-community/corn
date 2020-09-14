(*
Copyright © 2006-2008 Russell O’Connor

Permission is hereby granted, free of charge, to any person obtaining a copy of
this proof and associated documentation files (the "Proof"), to deal in
the Proof without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Proof, and to permit persons to whom the Proof is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Proof.

THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
*)

Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import Coq.setoid_ring.ArithRing.
Require Export CoRN.reals.fast.CRArith.
Require Import Coq.Bool.Bool.
Require Export CoRN.model.metric2.Qmetric.
Require Import CoRN.reals.fast.LazyNat.
Require Export CoRN.metric2.Limit.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import Coq.QArith.Qpower.
Require Export MathClasses.theory.CoqStreams.
Require Import CoRN.classes.Qclasses.
Require Import MathClasses.interfaces.abstract_algebra MathClasses.interfaces.orders MathClasses.theory.series MathClasses.theory.streams.

Opaque CR.

(**
** Computing Alternating Series.
Alternating series are particularly nice to sum because each term is also
a bound on the error of the partial sum.
*)

Section InfiniteAlternatingSum.

(** Given a stream, we can compute its alternating partial sum up to
an point satifying a predicate, so long as that predicate eventually
exists.

By folding with Qminus we get an alternating sum
p0 - (p1 - (p2 - ... - (pn - 0))))
 *)

Definition PartialAlternatingSumUntil {P : Stream Q → bool}
           `(ex : LazyExists (fun x => Is_true (P x)) s) : Q
  := takeUntil P ex Qminus' 0.

(** The value of the partial sum is between 0 and the head of the
sequence if the sequence is decreasing and nonnegative. *)
Lemma PartialAlternatingSumUntil_take_small
      (s : Stream Q) {dnn : DecreasingNonNegative s} (n : nat) : 
  0 ≤ take s n Qminus' 0 ≤ hd s.
Proof.
  revert s dnn. induction n.
  - simpl.
   split... apply Qle_refl. now apply dnn_hd_nonneg.
  - intros s dnn. simpl.
  rewrite Qminus'_correct. unfold Qminus.
  split.
   apply rings.flip_nonneg_minus.
   transitivity (hd (tl s)).
    now apply (IHn _ _).
   now destruct dnn as [[? ?] ?].
  setoid_rewrite <-(rings.plus_0_r (hd s)) at 2.
  apply (order_preserving _).
  apply rings.flip_nonneg_negate. 
  now apply (IHn _ _).
Qed.

Lemma PartialAlternatingSumUntil_small {P : Stream Q → bool}
      `(ex : LazyExists (fun x => Is_true (P x)) s) {dnn : DecreasingNonNegative s} : 
  0 ≤ PartialAlternatingSumUntil ex ≤ hd s.
Proof.
  unfold PartialAlternatingSumUntil.
  rewrite takeUntil_correct.
  apply PartialAlternatingSumUntil_take_small, _.
Qed.

Lemma dnn_in_Qball_bool_0_tl (s : Stream Q) {dnn : DecreasingNonNegative s} (ε : Qpos)
  : Is_true (Qball_ex_bool ε (hd s) 0)
    → Is_true (Qball_ex_bool ε (hd (tl s)) 0).
Proof.
  intros E.
  apply Qball_ex_bool_correct.
  apply (nonneg_in_Qball_0 (dnn_hd_nonneg (dnn_tl dnn))).
  apply Qle_trans with (hd s).
   now destruct dnn as [[? ?] _].
  apply (nonneg_in_Qball_0 (dnn_hd_nonneg dnn)).
  now apply Qball_ex_bool_correct.
Qed.

Lemma dnn_in_Qball_bool_0_Str_nth_tl (seq:Stream Q) {dnn : DecreasingNonNegative seq}
      (n : nat) (ε : Qpos) :
  Is_true (Qball_ex_bool ε (hd seq) 0)
  → Is_true (Qball_ex_bool ε (hd (Str_nth_tl n seq)) 0).
Proof.
  induction n.
  - easy.
  - intros E. 
    simpl. rewrite <-tl_nth_tl.
    now apply (dnn_in_Qball_bool_0_tl _ _), IHn.
Qed.

Lemma dnn_in_Qball_0_EventuallyForall
      (s : Stream Q) {dnn : DecreasingNonNegative s} (ε : Qpos) :
  EventuallyForAll (λ s, Is_true (Qball_ex_bool ε (hd s) 0)) s.
Proof.
  revert s dnn.
  cofix FIX. intros dnn.
  constructor.
   apply (dnn_in_Qball_bool_0_tl _ _).
  simpl.
  apply (FIX _ _).
Qed.

(** If a sequence has a limit of 0, then there is a point
    arbitrarily close to 0. *)
Fixpoint Limit_near_zero {s : Stream Q} {ε:QposInf}
      (zl : LazyExists (NearBy 0 ε) s) { struct zl }
  : LazyExists (λ s, Is_true (Qball_ex_bool ε (hd s) 0)) s.
Proof.
 destruct zl as [nb | zl].
 - left.
  destruct nb as [nb _].
  unfold Qball_ex_bool.
  destruct (ball_ex_dec Q_as_MetricSpace Qmetric_dec ε (@hd Q s) (0#1)) as [|n].
   constructor.
  apply n; clear n.
  apply nb.
 - right. intro.
   apply (Limit_near_zero (tl s) ε (zl tt)).
Defined.

(** The infinte sum of an alternating series is the limit of the partial sums. *)
Definition InfiniteAlternatingSum_raw (s : Stream Q) `{zl : !@Limit Q_as_MetricSpace s 0} (ε : QposInf)
  := PartialAlternatingSumUntil (Limit_near_zero (zl ε)).

Lemma InfiniteAlternatingSum_raw_wd (s1 s2 : Stream Q) {zl1 : @Limit Q_as_MetricSpace s1 0} {zl2 : @Limit Q_as_MetricSpace s2 0} (ε : QposInf) : 
  s1 = s2 → InfiniteAlternatingSum_raw s1 ε = InfiniteAlternatingSum_raw s2 ε.
Proof. 
  assert (Proper ((=) ==> eq) (λ s, Qball_ex_bool ε (hd s) 0)).
  intros x y xyeq. destruct x,y.
  inversion xyeq as [H _]. unfold hd. unfold hd in H.
  unfold Qball_ex_bool, ball_ex_dec.
  destruct ε. 2: reflexivity. 
  destruct (Qmetric_dec (` q1) q 0%Q), (Qmetric_dec (` q1) q0 0%Q).
  reflexivity. 3: reflexivity.
  exfalso. simpl in b.
  rewrite H in b. contradiction.
  exfalso. simpl in b.
  rewrite <- H in b. contradiction.
  intros E.
  apply takeUntil_wd_alt. 
   now apply _. 
  easy.
Qed.

Definition InfiniteAlternatingSum_length (s : Stream Q)
           `{zl : !@Limit Q_as_MetricSpace s 0}
           (e:QposInf) := takeUntil_length _ (Limit_near_zero (zl e)).

Lemma InfiniteAlternatingSum_length_weak (s : Stream Q) {dnn:DecreasingNonNegative s}
      {zl : @Limit Q_as_MetricSpace s 0} (ε1 ε2 : Qpos) :
  proj1_sig ε1 ≤ proj1_sig ε2
  → InfiniteAlternatingSum_length s ε2 ≤ InfiniteAlternatingSum_length s ε1.
Proof.
  intros E.
  apply takeUntil_length_ForAllIf.
  revert s dnn zl.
  cofix FIX; intros.
  constructor.
   do 2 rewrite Qball_ex_bool_correct.
   now apply ball_weak_le.
  apply (FIX _ _ _).
Qed.

Lemma InfiniteAlternatingSum_further_aux (s : Stream Q) {dnn : DecreasingNonNegative s} (k l : nat) (ε : Qpos) :
  k ≤ l → Str_nth k s ≤ proj1_sig ε
  → @ball Q_as_MetricSpace (proj1_sig ε) (take s l Qminus' 0) (take s k Qminus' 0).
Proof.
  intros E.
  apply naturals.nat_le_plus in E.
  destruct E as [z E]. do 2 red in E. rewrite E. clear E l.
  revert z s dnn ε.
  induction k; intros.
   destruct z; intros.
    apply ball_refl, Qpos_nonneg.
   apply nonneg_in_Qball_0.
    now apply (PartialAlternatingSumUntil_take_small _).
   simpl. rewrite Qminus'_correct. unfold Qminus.
   apply Qle_trans with (hd s).
    change (hd s + - take (tl s) z Qminus' 0 ≤ hd s).
    setoid_rewrite <-(rings.plus_0_r (hd s)) at 2.
    apply (order_preserving _).
    apply rings.flip_nonneg_negate.
    now apply (PartialAlternatingSumUntil_take_small _).
   easy.
   simpl.
   do 2 rewrite Qminus'_correct. unfold Qminus.
  apply Qball_plus_r, Qball_opp.
  now apply (IHk _ _ _).
Qed.

Lemma InfiniteAlternatingSum_further (s : Stream Q) {dnn : DecreasingNonNegative s}
      {zl : @Limit Q_as_MetricSpace s 0} (l : nat) (ε : Qpos) :
  InfiniteAlternatingSum_length s ε ≤ l
  → @ball Q_as_MetricSpace (proj1_sig ε) (take s l Qminus' 0) (InfiniteAlternatingSum_raw s ε).
Proof.
  intros E.
  unfold InfiniteAlternatingSum_raw, PartialAlternatingSumUntil.
  rewrite takeUntil_correct.
  apply (InfiniteAlternatingSum_further_aux _).
   easy.
  apply (nonneg_in_Qball_0 (dnn_Str_nth_nonneg dnn _)).
  apply Qball_ex_bool_correct.
  unfold Str_nth.
  now apply (takeUntil_length_correct (λ s, Qball_ex_bool ε (hd s) 0)).
Qed.

Lemma InfiniteAlternatingSum_further_alt (s : Stream Q) {dnn : DecreasingNonNegative s}
      {zl : @Limit Q_as_MetricSpace s 0} (l : nat) (ε1 ε2 : Qpos) :
  InfiniteAlternatingSum_length s ε1 ≤ l
  → @ball Q_as_MetricSpace (proj1_sig ε1 + proj1_sig ε2) (take s l Qminus' 0) (InfiniteAlternatingSum_raw s ε2).
Proof.
  intros E1.
  unfold InfiniteAlternatingSum_raw at 1, PartialAlternatingSumUntil.
  rewrite takeUntil_correct.
  destruct (total (≤) l (takeUntil_length _ (Limit_near_zero (zl ε2))))
    as [E2|E2].
  - apply ball_sym.
   apply (InfiniteAlternatingSum_further_aux _ _ _ (ε1 + ε2)).
    easy.
   apply (nonneg_in_Qball_0 (dnn_Str_nth_nonneg dnn _)).
   apply naturals.nat_le_plus in E1.
   destruct E1 as [z E1].
   simpl.
   rewrite E1. rewrite <- Nat.add_comm.
   rewrite <-Str_nth_plus. 
   change (Qball (` ε1 + ` ε2) 
                 (Str_nth z (Str_nth_tl (InfiniteAlternatingSum_length s ε1) s)) 0).
   apply ball_weak, Qball_ex_bool_correct.
   apply Qpos_nonneg.
   apply (dnn_in_Qball_bool_0_Str_nth_tl _).
   apply (takeUntil_length_correct (λ s, Qball_ex_bool ε1 (hd s) 0)).
  - assert (QposEq (ε1 + ε2) (ε2+ε1)) by (unfold QposEq; simpl; ring).
 apply (ball_wd _ H _ _ (reflexivity _) _ _ (reflexivity _)). clear H.
  apply ball_weak. apply Qpos_nonneg.
  apply (InfiniteAlternatingSum_further_aux _).
   easy.
  apply (nonneg_in_Qball_0 (dnn_Str_nth_nonneg dnn _)).
  apply Qball_ex_bool_correct.
  apply (takeUntil_length_correct (λ s, Qball_ex_bool ε2 (hd s) 0)).
Qed.

Lemma InfiniteAlternatingSum_prf (s : Stream Q) {dnn : DecreasingNonNegative s}
      {zl : @Limit Q_as_MetricSpace s 0} :
  is_RegularFunction Qball (InfiniteAlternatingSum_raw s).
Proof.
  assert (∀ (ε1 ε2 : Qpos),
             (proj1_sig ε1) ≤ (proj1_sig ε2)
             → @ball Q_as_MetricSpace (proj1_sig ε1 + proj1_sig ε2) (InfiniteAlternatingSum_raw s ε1) (InfiniteAlternatingSum_raw s ε2)).
   intros ε1 ε2 E.
   unfold InfiniteAlternatingSum_raw at 1, PartialAlternatingSumUntil.
   rewrite takeUntil_correct.
  assert (QposEq (ε1 + ε2) (ε2+ε1)) by (unfold QposEq; simpl; ring).
  apply (ball_wd _ H _ _ (reflexivity _) _ _ (reflexivity _)). clear H.
   apply ball_weak. apply Qpos_nonneg.
   apply (InfiniteAlternatingSum_further _).
   now apply (InfiniteAlternatingSum_length_weak _).
  intros ε1 ε2.
  destruct (total (≤) (proj1_sig ε1) (proj1_sig ε2)).
  apply H, H0.
  assert (QposEq (ε1 + ε2) (ε2+ε1)) by (unfold QposEq; simpl; ring).
  apply (ball_wd _ H1 _ _ (reflexivity _) _ _ (reflexivity _)). clear H1.
  apply ball_sym. apply H, H0. 
Qed.

Definition InfiniteAlternatingSum (seq:Stream Q) {dnn:DecreasingNonNegative seq}
           {zl: @Limit Q_as_MetricSpace seq 0} : CR :=
  Build_RegularFunction (InfiniteAlternatingSum_prf seq).

Lemma InfiniteAlternatingSum_wd (s1 s2 : Stream Q) `{!DecreasingNonNegative s1} `{!DecreasingNonNegative s2} `{!@Limit Q_as_MetricSpace s1 0} `{!@Limit Q_as_MetricSpace s2 0} : 
  s1 = s2 → InfiniteAlternatingSum s1 = InfiniteAlternatingSum s2.
Proof.
  intros E. apply regFunEq_equiv, regFunEq_e. intros ε.
  unfold InfiniteAlternatingSum. simpl. 
  rewrite (InfiniteAlternatingSum_raw_wd s1 s2).
  apply Qball_Reflexive. apply (Qpos_nonneg (ε + ε)). exact E.
Qed.

Local Open Scope Q_scope.

Lemma InfiniteAlternatingSum_step (seq : Stream Q) {dnn:DecreasingNonNegative seq}
      {zl: @Limit Q_as_MetricSpace seq 0} : 
 (InfiniteAlternatingSum seq == '(hd seq) - InfiniteAlternatingSum (tl seq))%CR.
Proof.
 destruct seq as [hd seq], dnn as [dnn_hd dnn].
 rewrite -> CRplus_translate.
 apply regFunEq_equiv, regFunEq_e.
 intros e.
 simpl.
 unfold Cap_raw; simpl.
 unfold InfiniteAlternatingSum_raw.
 unfold PartialAlternatingSumUntil.
 simpl.
 set (P:=(fun s : Stream Q => Qball_ex_bool e (CoqStreams.hd s) 0)).
 case_eq (P (Cons hd seq)); intros H.
  rewrite takeUntil_end;[|apply Is_true_eq_left;assumption].
  case_eq (P seq); intros H0.
   rewrite takeUntil_end;[|apply Is_true_eq_left;assumption].
   simpl.
   change (Qball (proj1_sig e + proj1_sig e) 0 (hd + -0))%Q.
   rewrite Qplus_0_r.
   change (Qball (`e+`e) 0 hd).
   unfold P in H.
   apply ball_weak;simpl. apply Qpos_nonneg.
   apply ball_sym;simpl.
   unfold Qball_ex_bool in H.
   destruct (ball_ex_dec Q_as_MetricSpace Qmetric_dec e (CoqStreams.hd (Cons hd seq))) as [X|X];
     [apply X|discriminate H].
  unfold P in *.
  unfold Qball_ex_bool in *.
  destruct (ball_ex_dec Q_as_MetricSpace Qmetric_dec e (CoqStreams.hd (Cons hd seq))) as [X|X];
    [|discriminate H].
  destruct (ball_ex_dec Q_as_MetricSpace Qmetric_dec e (CoqStreams.hd seq)) as [Y|Y]; [discriminate H0|].
  elim Y.
  simpl in dnn_hd.
  destruct dnn_hd as [Z0 Z1].
  split;simpl.
   apply Qle_trans with 0.
   change (- proj1_sig e <= 0)%Q.
    rewrite -> Qle_minus_iff; ring_simplify; apply Qpos_nonneg.
   change (0 <= CoqStreams.hd seq - 0)%Q.
   ring_simplify.
   apply Z0.
  change (CoqStreams.hd seq - 0 <= proj1_sig e)%Q.
  ring_simplify.
  eapply Qle_trans.
   apply Z1.
  destruct X as [_ X].
  unfold Qminus in X. rewrite Qplus_0_r in X.
  exact X.
  destruct (takeUntil_step P (Limit_near_zero (zl e)) Qminus' 0)
    as [ex' rw]; [rewrite H;auto|].
 change zero with (0:Q).
 rewrite rw; clear rw.
 simpl.
 rewrite (@takeUntil_wd Q Q P _ ex' (Limit_near_zero (Limit_tl zl e))).
 rewrite -> Qminus'_correct.
 apply Qball_Reflexive. apply (Qpos_nonneg (e+e)).
Qed.

(** The infinite alternating series is always nonnegative. *)
Lemma InfiniteAlternatingSum_nonneg (seq : Stream Q) {dnn:DecreasingNonNegative seq}
      {zl:@Limit Q_as_MetricSpace seq 0} :
 (0 <= InfiniteAlternatingSum seq)%CR.
Proof.
 intros e.
 apply Qle_trans with 0.
  change (-proj1_sig e ≤ 0)%Q.
  rewrite -> Qle_minus_iff; ring_simplify; apply Qpos_nonneg.
 unfold InfiniteAlternatingSum.
 simpl.
 unfold Cap_raw.
 simpl.
 ring_simplify.
 unfold InfiniteAlternatingSum_raw.
 destruct (PartialAlternatingSumUntil_small
             (Limit_near_zero (zl ((1 # 2) * e)%Qpos))).
 exact H.
Qed.

(** The infinite alternating series is always bounded by the first term
in the series. *)
Lemma InfiniteAlternatingSum_bound (seq : Stream Q) {dnn:DecreasingNonNegative seq}
      {zl:@Limit Q_as_MetricSpace seq 0} :
 (InfiniteAlternatingSum seq <= inject_Q_CR (hd seq))%CR.
Proof.
 rewrite -> InfiniteAlternatingSum_step.
 rewrite <- (CRplus_0_r (' hd seq)%CR) at 2.
 rewrite <- CRopp_0.
 apply CRplus_le_l, CRopp_le_compat.
 apply InfiniteAlternatingSum_nonneg.
Qed.

End InfiniteAlternatingSum.
