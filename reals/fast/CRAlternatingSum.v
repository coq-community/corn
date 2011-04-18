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

Require Import iso_CReals.
Require Import Q_in_CReals.
Require Import ArithRing.
Require Export CRArith.
Require Import CRIR.
Require Import Bool.
Require Import COrdAbs.
Require Import Qordfield.
Require Export Qmetric.
Require Import LazyNat.
Require Export Limit.
Require Import QposMinMax.
Require Import Qpower.
Require Export Streams.
Require Import PowerSeries.
Require Import CornTac.
Require Import Qclasses.
Require Import abstract_algebra theory.series theory.streams.

Opaque CR.

(**
** Computing Alternating Series.
Alternating series are particularly nice to sum because each term is also
a bound on the error of the partial sum.
*)

Section InfiniteAlternatingSum.
(* begin hide *)
Coercion Local Is_true : bool >-> Sortclass.
(* end hide *)
(** Given a stream, we can compute its alternating partial sum up to
an point satifying a predicate, so long as that predicate eventually
exists. *)

Definition PartialAlternatingSumUntil {P : Stream Q → bool} `(ex : LazyExists P s) : Q := takeUntil P ex Qminus' 0.

(** The value of the partial sum is between 0 and the head of the
sequence if the sequence is decreasing and nonnegative. *)
Lemma PartialAlternatingSumUntil_take_small (s : Stream Q) {dnn : DecreasingNonNegative s} (n : nat) : 
  0 ≤ take s n Qminus' 0 ≤ hd s.
Proof with try easy.
  revert s dnn.
  induction n; simpl.
   split... now apply dnn_hd_nonneg.
  intros s dnn. 
  rewrite Qminus'_correct. unfold Qminus.
  split.
   apply rings.flip_nonneg_minus.
   transitivity (hd (tl s)).
    now apply (IHn _ _).
   now destruct dnn as [[? ?] ?].
  setoid_rewrite <-(rings.plus_0_r (hd s)) at 2.
  apply (order_preserving _).
  apply rings.flip_nonneg_opp. 
  now apply (IHn _ _).
Qed.

Lemma PartialAlternatingSumUntil_small {P : Stream Q → bool} `(ex : LazyExists P s) {dnn : DecreasingNonNegative s} : 
  0 ≤ PartialAlternatingSumUntil ex ≤ hd s.
Proof.
  unfold PartialAlternatingSumUntil.
  rewrite takeUntil_correct.
  apply PartialAlternatingSumUntil_take_small, _.
Qed.

Lemma dnn_in_Qball_bool_0_tl (s : Stream Q) {dnn : DecreasingNonNegative s} (ε : Qpos) :
  Qball_ex_bool ε (hd s) 0 → Qball_ex_bool ε (hd (tl s)) 0.
Proof.
  intros E.
  apply Qball_ex_bool_correct.
  apply (nonneg_in_Qball_0 (dnn_hd_nonneg (dnn_tl dnn))).
  transitivity (hd s).
   now destruct dnn as [[? ?] _].
  apply (nonneg_in_Qball_0 (dnn_hd_nonneg dnn)).
  now apply Qball_ex_bool_correct.
Qed.

Lemma dnn_in_Qball_bool_0_Str_nth_tl (seq:Stream Q) {dnn : DecreasingNonNegative seq} (n : nat) (ε : Qpos) :
  Qball_ex_bool ε (hd seq) 0 → Qball_ex_bool ε (hd (Str_nth_tl n seq)) 0.
Proof.
  induction n.
   easy.
  intros E. 
  simpl. rewrite <-tl_nth_tl.
  now apply (dnn_in_Qball_bool_0_tl _ _), IHn.
Qed.

Lemma dnn_in_Qball_0_EventuallyForall (s : Stream Q) {dnn : DecreasingNonNegative s} (ε : Qpos) :
  EventuallyForAll (λ s, Qball_ex_bool ε (hd s) 0) s.
Proof.
  revert s dnn.
  cofix FIX. intros dnn.
  constructor.
   apply (dnn_in_Qball_bool_0_tl _ _).
  simpl.
  apply (FIX _ _).
Qed.

(** If a sequence has a limit of [l], then there is a point that gets arbitrarily close to [l]. *)
Lemma Limit_near (s : Stream Q) (l:Q) {zl : Limit s l} ε : LazyExists (λ s, Qball_ex_bool ε (hd s) l) s.
Proof.
 assert (zl':=zl ε).
 induction zl' as [s nb | ? ? IH].
  left.
  destruct nb as [nb _].
  unfold Qball_ex_bool.
  destruct (ball_ex_dec Q_as_MetricSpace Qmetric_dec ε (hd s) l) as [|n].
   constructor.
  apply n; clear n.
  apply nb.
 right.
 intro.
 apply (IH tt _).
Defined.

(** The infinte sum of an alternating series is the limit of the partial sums. *)
Definition InfiniteAlternatingSum_raw (s : Stream Q) `{zl : !Limit s 0} (ε : QposInf) := PartialAlternatingSumUntil (Limit_near s 0 ε).

Lemma InfiniteAlternatingSum_raw_wd (s1 s2 : Stream Q) {zl1 : Limit s1 0} {zl2 : Limit s2 0} (ε : QposInf) : 
  s1 = s2 → InfiniteAlternatingSum_raw s1 ε = InfiniteAlternatingSum_raw s2 ε.
Proof. 
  assert (Proper ((=) ==> eq) (λ s, Qball_ex_bool ε (hd s) 0)).
   solve_proper.
  intros E.
  apply takeUntil_wd_alt. 
   now apply _. 
  easy.
Qed.

Definition InfiniteAlternatingSum_length (s : Stream Q) `{zl : !Limit s 0} (e:QposInf) := takeUntil_length _ (Limit_near s 0 e).

Lemma InfiniteAlternatingSum_length_weak (s : Stream Q) {dnn:DecreasingNonNegative s} {zl : Limit s 0} (ε1 ε2 : Qpos) :
  (ε1:Q) ≤ (ε2:Q) → InfiniteAlternatingSum_length s ε2 ≤ InfiniteAlternatingSum_length s ε1.
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
  k ≤ l → Str_nth k s ≤ ε → ball ε (take s l Qminus' 0) (take s k Qminus' 0).
Proof.
  intros E.
  apply naturals.natural_precedes_plus in E.
  destruct E as [z E]. rewrite E. clear E l.
  revert z s dnn ε.
  induction k; intros.
   destruct z; intros.
    now apply ball_refl.
   apply nonneg_in_Qball_0.
    now apply (PartialAlternatingSumUntil_take_small _).
   simpl. rewrite Qminus'_correct. unfold Qminus.
   transitivity (hd s).
    change (hd s + - take (tl s) z Qminus' 0 ≤ hd s).
    setoid_rewrite <-(rings.plus_0_r (hd s)) at 2.
    apply (order_preserving _).
    apply rings.flip_nonneg_opp.
    now apply (PartialAlternatingSumUntil_take_small _).
   easy.
  simpl. do 2 rewrite Qminus'_correct. unfold Qminus.
  apply Qball_plus_r, Qball_opp.
  now apply (IHk _ _ _).
Qed.

Lemma InfiniteAlternatingSum_further (s : Stream Q) {dnn : DecreasingNonNegative s} {zl : Limit s 0} (l : nat) (ε : Qpos) :
  InfiniteAlternatingSum_length s ε ≤ l → ball ε (take s l Qminus' 0) (InfiniteAlternatingSum_raw s ε).
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

Lemma InfiniteAlternatingSum_further_alt (s : Stream Q) {dnn : DecreasingNonNegative s} {zl : Limit s 0} (l : nat) (ε1 ε2 : Qpos) :
  InfiniteAlternatingSum_length s ε1 ≤ l → ball (ε1 + ε2) (take s l Qminus' 0) (InfiniteAlternatingSum_raw s ε2).
Proof.
  intros E1.
  unfold InfiniteAlternatingSum_raw at 1, PartialAlternatingSumUntil.
  rewrite takeUntil_correct.
  destruct (total_order l (takeUntil_length (λ s, Qball_ex_bool ε2 (hd s) 0) (Limit_near s 0 ε2))) as [E2|E2].
   apply ball_sym.
   apply (InfiniteAlternatingSum_further_aux _).
    easy.
   apply (nonneg_in_Qball_0 (dnn_Str_nth_nonneg dnn _)).
   apply naturals.natural_precedes_plus in E1.
   destruct E1 as [z E1]. rewrite E1. rewrite commutativity.
   rewrite <-Str_nth_plus. 
   apply ball_weak, Qball_ex_bool_correct.
   apply (dnn_in_Qball_bool_0_Str_nth_tl _).
   apply (takeUntil_length_correct (λ s, Qball_ex_bool ε1 (hd s) 0)).
  setoid_replace (ε1 + ε2)%Qpos with (ε2+ε1)%Qpos by QposRing.
  apply ball_weak.
  apply (InfiniteAlternatingSum_further_aux _).
   easy.
  apply (nonneg_in_Qball_0 (dnn_Str_nth_nonneg dnn _)).
  apply Qball_ex_bool_correct.
  apply (takeUntil_length_correct (λ s, Qball_ex_bool ε2 (hd s) 0)).
Qed.

Lemma InfiniteAlternatingSum_prf (s : Stream Q) {dnn : DecreasingNonNegative s} {zl : Limit s 0} :
  is_RegularFunction (InfiniteAlternatingSum_raw s).
Proof.
  assert (∀ (ε1 ε2 : Qpos), (ε1:Q) ≤ (ε2:Q) → ball (ε1 + ε2) (InfiniteAlternatingSum_raw s ε1) (InfiniteAlternatingSum_raw s ε2)).
   intros ε1 ε2 E.
   unfold InfiniteAlternatingSum_raw at 1, PartialAlternatingSumUntil.
   rewrite takeUntil_correct.
   setoid_replace (ε1 + ε2)%Qpos with (ε2+ε1)%Qpos by QposRing.
   apply ball_weak.
   apply (InfiniteAlternatingSum_further _).
   now apply (InfiniteAlternatingSum_length_weak _).
  intros ε1 ε2.
  destruct (total_order (ε1:Q) (ε2:Q)).
   now auto.
  setoid_replace (ε1 + ε2)%Qpos with (ε2+ε1)%Qpos by QposRing.
  apply ball_sym. now auto.
Qed.

Definition InfiniteAlternatingSum (seq:Stream Q) {dnn:DecreasingNonNegative seq} {zl:Limit seq 0} : CR :=
  Build_RegularFunction (InfiniteAlternatingSum_prf seq).

Lemma InfiniteAlternatingSum_wd (s1 s2 : Stream Q) `{!DecreasingNonNegative s1} `{!DecreasingNonNegative s2} `{!Limit s1 0} `{!Limit s2 0} : 
  s1 = s2 → InfiniteAlternatingSum s1 = InfiniteAlternatingSum s2.
Proof.
  intros E. apply: regFunEq_e. intros ε.
  unfold InfiniteAlternatingSum. simpl. 
  now rewrite (InfiniteAlternatingSum_raw_wd s1 s2).
Qed.

Open Local Scope Q_scope.

Lemma InfiniteAlternatingSum_step (seq : Stream Q) {dnn:DecreasingNonNegative seq} {zl:Limit seq 0} : 
 (InfiniteAlternatingSum seq == '(hd seq) - InfiniteAlternatingSum (tl seq))%CR.
Proof.
 destruct seq as [hd seq], dnn as [dnn_hd dnn].
 rewrite -> CRplus_translate.
 apply: regFunEq_e.
 intros e.
 simpl.
 unfold Cap_raw; simpl.
 unfold InfiniteAlternatingSum_raw.
 unfold PartialAlternatingSumUntil.
 simpl.
 set (P:=(fun s : Stream Q => Qball_ex_bool e (Streams.hd s) 0)).
 case_eq (P (Cons hd seq)); intros H.
  rewrite takeUntil_end;[|apply Is_true_eq_left;assumption].
  case_eq (P seq); intros H0.
   rewrite takeUntil_end;[|apply Is_true_eq_left;assumption].
   simpl.
   change (Qball (e + e) 0 (hd + -0))%Q.
   ring_simplify.
   unfold P in H.
   apply: ball_weak;simpl.
   apply: ball_sym;simpl.
   unfold Qball_ex_bool in H.
   destruct (ball_ex_dec Q_as_MetricSpace Qmetric_dec e (Streams.hd (Cons hd seq))) as [X|X];
     [apply X|discriminate H].
  unfold P in *.
  unfold Qball_ex_bool in *.
  destruct (ball_ex_dec Q_as_MetricSpace Qmetric_dec e (Streams.hd (Cons hd seq))) as [X|X];
    [|discriminate H].
  destruct (ball_ex_dec Q_as_MetricSpace Qmetric_dec e (Streams.hd seq)) as [Y|Y]; [discriminate H0|].
  elim Y.
  simpl in dnn_hd.
  destruct dnn_hd as [Z0 Z1].
  split;simpl.
   apply Qle_trans with 0.
   change (- e <= 0)%Q.
    rewrite -> Qle_minus_iff; ring_simplify; apply Qpos_nonneg.
   change (0 <= Streams.hd seq - 0)%Q.
   ring_simplify.
   apply Z0.
  change (Streams.hd seq - 0 <= e)%Q.
  ring_simplify.
  eapply Qle_trans.
   apply Z1.
  destruct X as [_ X].
  stepl (hd - 0)%Q; [| simpl; ring].
  apply X.
 destruct (takeUntil_step P (Limit_near (Cons hd seq) 0 e) Qminus' 0) as [ex' rw]; [rewrite H;auto|].
 change ring_zero with (0:Q).
 rewrite rw; clear rw.
 simpl.
 rewrite (@takeUntil_wd Q Q P _ ex' (Limit_near (tl (Cons hd seq)) 0 e)).
 rewrite -> Qminus'_correct.
 apply: ball_refl.
Qed.

(** The infinite alternating series is always nonnegative. *)
Lemma InfiniteAlternatingSum_nonneg (seq : Stream Q) {dnn:DecreasingNonNegative seq} {zl:Limit seq 0} :
 (inject_Q 0%Q <= InfiniteAlternatingSum seq)%CR.
Proof.
 intros e.
 apply Qle_trans with 0.
  change (-e ≤ 0)%Q.
  rewrite -> Qle_minus_iff; ring_simplify; apply Qpos_nonneg.
 unfold InfiniteAlternatingSum.
 simpl.
 unfold Cap_raw.
 simpl.
 ring_simplify.
 unfold InfiniteAlternatingSum_raw.
 simpl.
 destruct (PartialAlternatingSumUntil_small (Limit_near seq 0 ((1 # 2) * e)%Qpos)).
 assumption.
Qed.

(** The infinite alternating series is always bounded by the first term
in the series. *)
Lemma InfiniteAlternatingSum_bound (seq : Stream Q) {dnn:DecreasingNonNegative seq} {zl:Limit seq 0} :
 (InfiniteAlternatingSum seq <= inject_Q (hd seq))%CR.
Proof.
 rewrite -> InfiniteAlternatingSum_step.
 change (inject_Q (hd seq) - InfiniteAlternatingSum (tl seq) [<=]inject_Q (hd seq))%CR.
 stepr (inject_Q (hd seq) - inject_Q 0%Q)%CR.
  apply: minus_resp_leEq_rht.
  apply InfiniteAlternatingSum_nonneg.
 simpl.
 ring.
Qed.

(** [InfiniteAlternatingSum] is correct. *)
Lemma dnn_zl_convergent (seq : Stream Q) {dnn:DecreasingNonNegative seq} {zl:Limit seq 0} :
 convergent (fun n => inj_Q IR ((-(1))^n*Str_nth n seq))%Q.
Proof.
 cut (convergent (fun n : nat => [--]One[^]n[*]inj_Q IR (Str_nth n seq))).
  apply convergent_wd.
  intros n.
  stepr ((inj_Q IR ((-(1))^n))[*](inj_Q IR (Str_nth n seq)))%Q; [| now (apply eq_symmetric; apply inj_Q_mult)].
  apply mult_wdl.
  stepr ((inj_Q IR (-(1)))[^]n); [| now (apply eq_symmetric; apply inj_Q_power)].
  apply nexp_wd.
  stepr ([--](inj_Q IR 1)); [| now (apply eq_symmetric; apply inj_Q_inv)].
  apply un_op_wd_unfolded.
  rstepl ((nring 1):IR).
  apply eq_symmetric; apply (inj_Q_nring IR 1).
 apply alternate_series_conv.
   intros n.
   unfold Str_nth.
   change (Zero:IR) with (nring 0:IR).
   stepl (inj_Q IR (nring 0)); [| now apply inj_Q_nring].
   apply inj_Q_leEq.
   simpl. 
   pose proof (_ : DecreasingNonNegative (Str_nth_tl n seq)) as dnn_tl.
   apply (dnn_hd_nonneg (dnn_tl)).
  intros e He.
  destruct (Q_dense_in_CReals IR e He) as [c Hc].
  cut {N : nat | forall m : nat, (N <= m)%nat -> AbsSmall c ((Str_nth m seq))}.
   intros [N HN].
   exists N.
   intros m Hm.
   eapply AbsSmall_trans with (inj_Q IR c).
    assumption.
   rstepr (inj_Q IR (Str_nth m seq)).
   apply inj_Q_AbsSmall.
   apply HN.
   assumption.
  clear e He c0.
  assert (Hc':(0<c)%Q).
   apply less_inj_Q with IR.
   change (0:Q) with (nring 0:Q).
   stepl (nring 0:IR).
    assumption.
   apply eq_symmetric; apply inj_Q_nring.
  assert (L:=(Limit_near seq 0 (mkQpos Hc'))).
  exists (takeUntil _ L (fun _ => S) O).
  generalize dnn; clear dnn.
  set (Q:= (fun seq b => DecreasingNonNegative seq -> forall m : nat, (b <= m)%nat ->
    AbsSmall (R:=Q_as_COrdField) c (Str_nth m seq))).
  change (Q seq (takeUntil (fun s : Stream Q_as_MetricSpace =>
    Qball_ex_bool (mkQpos (a:=c) Hc') (hd s) 0) L (fun _ : Q_as_MetricSpace => S) 0%nat)).
  apply takeUntil_elim; unfold Q; clear seq zl L Q.
   intros seq H dnn m _.
   unfold Str_nth.
   unfold Qball_ex_bool in H.
   destruct (ball_ex_dec Q_as_MetricSpace Qmetric_dec (mkQpos (a:=c) Hc') (hd seq) 0) as [b|b]; try contradiction.
   simpl in b.
   apply leEq_imp_AbsSmall.
    pose proof (_ : DecreasingNonNegative (Str_nth_tl m seq)) as dnn_tl.
    apply (dnn_hd_nonneg dnn_tl).
   apply dnn_alt in dnn. 
   destruct dnn as [X _].
   destruct (ForAll_Str_nth_tl m X) as [[_ Y] _]. 
   simpl.
   eapply Qle_trans.
    apply Y.
   destruct b as [_ b].
   simpl in b.
   autorewrite with QposElim in b.
   ring_simplify in b.
   assumption.
  intros x b IH H dnn [|m] Hm.
   elimtype False; auto with *.
  apply IH; auto with *.
 intros n.
 apply inj_Q_leEq.
 destruct (ForAll_Str_nth_tl n dnn) as [[_ X] _].
 rewrite tl_nth_tl in X.
 assumption.
Qed.

Lemma InfiniteAlternatingSum_correct (seq:Stream Q) (x:nat -> IR)
 (Hx : forall n:nat, inj_Q IR (((-(1))^n)*Str_nth n seq)%Q[=]x n)
 {dnn : DecreasingNonNegative seq} {zl : Limit seq 0} H :
 (InfiniteAlternatingSum seq ==IRasCR (series_sum x H))%CR.
Proof.
 unfold series_sum.
 rewrite -> IR_Lim_as_CR.
 apply: SeqLimit_unique.
 intros e He.
 generalize (IR_Cauchy_prop_as_CR (Build_CauchySeq IR (seq_part_sum x) H)).
 intros C.
 destruct (C _ (pos_div_two _ _ He)) as [n Hn].
 exists n.
 intros m Hm.
 unfold CS_seq in *.
 clear C.
 unfold seq_part_sum in *.
 rstepr (((IRasCR (Sum0 (G:=IR) m x)[-](IRasCR (Sum0 (G:=IR) n x)))[+]
   ((IRasCR (Sum0 (G:=IR) n x)[-]InfiniteAlternatingSum seq)))).
 apply AbsSmall_eps_div_two;[apply Hn; assumption|].
 assert (X:AbsSmall (R:=CRasCReals) (e [/]TwoNZ) (('(((-(1))^n)*(Str_nth n seq)))%CR)).
  stepr (IRasCR (x n)).
   stepr (Sum n n (fun n => IRasCR (x n))); [| now apply: Sum_one].
   unfold Sum, Sum1.
   stepr (IRasCR (Sum0 (S n) x)[-]IRasCR (Sum0 n x )); [| now (apply cg_minus_wd; apply IR_Sum0_as_CR)].
   apply Hn.
   auto.
  simpl.
  symmetry.
  rewrite <- IR_inj_Q_as_CR.
  apply IRasCR_wd.
  apply Hx.
 stepr (('(Sum0 n (fun n => ((-(1))^n)*(Str_nth n seq))%Q))%CR[-]InfiniteAlternatingSum seq).
  clear - X.
  generalize seq dnn zl X.
  clear seq dnn zl X.
  generalize (e[/]TwoNZ).
  clear e.
  induction n; intros e seq dnn zl X.
   simpl in *.
   apply AbsSmall_minus.
   stepr (InfiniteAlternatingSum seq); [| now (unfold cg_minus;simpl;ring)].
   apply leEq_imp_AbsSmall;[apply InfiniteAlternatingSum_nonneg|].
   apply: leEq_transitive;simpl.
    apply InfiniteAlternatingSum_bound.
   assert ((hd seq)%CR == (1*hd seq)%Q). ring. rewrite -> H. clear H.
   destruct X; assumption.
  apply AbsSmall_minus.
  stepr (('(((Sum0 (G:=Q_as_CAbGroup) n (fun n0 : nat =>  ((- (1)) ^ n0 * Str_nth n0 (tl seq))%Q)))%CR)[-]
    InfiniteAlternatingSum (tl seq)))%CR; [apply IHn|].
   rewrite inj_S in X.
   rstepr ([--][--]('(((- (1)) ^ n * Str_nth n (tl seq))%Q))%CR).
   apply inv_resp_AbsSmall.
   stepr (' ((- (1)) ^ Zsucc n * Str_nth (S n) seq))%CR;[assumption|].
   simpl.
   change ((' ( (- (1)) ^ (n+1) * Str_nth n (tl seq)) == - ' ((- (1)) ^ n * Str_nth n (tl seq)))%CR).
   rewrite -> Qpower_plus;[|discriminate].
   simpl.
   ring.
  stepl (InfiniteAlternatingSum seq[-](('(((- (1)) ^ 0 * Str_nth 0 seq)%Q[+]
    ((Sum0 (G:=Q_as_CAbGroup) n
      (fun n0 : nat => ((- (1)) ^ (S n0) * Str_nth n0 (tl seq))%Q))):Q))%CR));[
        apply cg_minus_wd;[reflexivity| rewrite -> CReq_Qeq; apply: Sum0_shift;
          intros i; simpl; reflexivity]|].
  unfold cg_minus; simpl.
  rewrite -> InfiniteAlternatingSum_step.
  generalize (@InfiniteAlternatingSum (tl seq) _).
  intros x.
  change (Str_nth 0 seq) with (hd seq).
  setoid_replace ((Sum0 (G:=Q_as_CAbGroup) n
    (fun n0 : nat => Qpower_positive (- (1)) (P_of_succ_nat n0)  * Str_nth n0 (tl seq)))%Q:Q)
      with (-(Sum0 (G:=Q_as_CAbGroup) n
        (fun n0 : nat => ((- (1)) ^ n0 * Str_nth n0 (tl seq)))))%Q.
   simpl. ring.
  apply: eq_transitive;[|apply (inv_Sum0 Q_as_CAbGroup)].
  apply: Sum0_wd.
  intros i; simpl.
  change (Qpower_positive (- (1)) (P_of_succ_nat i)) with ((-(1))^ S i).
  rewrite inj_S.
  unfold Zsucc.
  rewrite -> Qpower_plus;[|discriminate].
  ring.
 apply cg_minus_wd;[rewrite -> IR_Sum0_as_CR|reflexivity].
 clear - Hx.
 induction n.
  reflexivity.
 change ((' (Sum0 (G:=Q_as_CAbGroup) n (fun n0 : nat => ((- (1)) ^ n0 * Str_nth n0 seq)%Q) +
   (- (1)) ^ n * Str_nth n seq) ==
     (Sum0 (G:=CRasCAbGroup) n (fun n0 : nat => IRasCR (x n0)):CR) + IRasCR (x n))%CR).
 rewrite <- CRplus_Qplus.
 apply ucFun2_wd;[apply IHn|].
 transitivity (IRasCR (inj_Q IR ((- (1)) ^ n * Str_nth n seq)%Q)); [symmetry;apply IR_inj_Q_as_CR|].
 apply IRasCR_wd.
 apply Hx.
Qed.

Lemma InfiniteAlternatingSum_correct' (seq:Stream Q)
 {dnn:DecreasingNonNegative seq} {zl : Limit seq 0} :
 (InfiniteAlternatingSum seq == IRasCR (series_sum _ (dnn_zl_convergent seq)))%CR.
Proof.
 apply InfiniteAlternatingSum_correct.
 intros; apply eq_reflexive.
Qed.

End InfiniteAlternatingSum.
