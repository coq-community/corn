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

Set Implicit Arguments.

Opaque CR.

Open Local Scope Q_scope.

(**
** Computing Alternating Series.
Alternating series are particularly nice to sum because each term is also
a bound on the error of the partial sum.
*** Decreasing and Nonnegative
*)

(** We characterize a decreasing nonnegative stream of rational numbers
by saying at every point in the stream s, then every
further point in the stream is in [[0,s]]. *)
Definition DecreasingNonNegative := ForAll (fun (s:Stream Q) => ForAll (fun (t:Stream Q) => 0 <= (hd t) <= (hd s)) s).

(** An alternative charactherization is that at every point in the stream
the second element is in between 0 and the head element. *)
Definition DecreasingNonNegative_alt := ForAll (fun (s:Stream Q) => 0 <= (hd (tl s)) <= (hd s)).

(** These two characterizations are equivalent. *)
Lemma dnn_alt_dnn : forall s, DecreasingNonNegative_alt s -> DecreasingNonNegative s.
Proof.
 cofix r1.
 intros s H.
 constructor.
  cut (hd s <= hd s);[|apply Qle_refl].
  set (x:=hd s).
  unfold x at 1.
  generalize s H x.
  clear s H x.
  cofix r2.
  intros s H x Hx.
  constructor.
   destruct H.
   split.
    apply Qle_trans with (hd (tl s)); firstorder.
   assumption.
  destruct H.
  apply r2.
   apply H0.
  apply Qle_trans with (hd s); firstorder.
 destruct H.
 apply r1.
 apply H0.
Qed.

Lemma dnn_dnn_alt : forall s, DecreasingNonNegative s -> DecreasingNonNegative_alt s.
Proof.
 cofix.
 intros s H.
 constructor.
  destruct H.
  destruct H.
  destruct H1.
  assumption.
 apply dnn_dnn_alt.
 destruct H; assumption.
Qed.

Lemma dnn_alt_iff_dnn : forall s, DecreasingNonNegative_alt s <-> DecreasingNonNegative s.
Proof.
 firstorder using dnn_alt_dnn dnn_dnn_alt.
Qed.

(** Every tail of a decreasing nonnegative stream is also decreasing and
nonnegative. *)
Lemma dnn_tl : forall s, DecreasingNonNegative s -> DecreasingNonNegative (tl s).
Proof.
 intros s [_ H].
 assumption.
Qed.
(* begin hide *)
Hint Resolve dnn_tl : dnn.
(* end hide *)
Lemma dnn_Str_nth_tl : forall n s, DecreasingNonNegative s -> DecreasingNonNegative (Str_nth_tl n s).
Proof.
 induction n.
  tauto.
 intros s X.
 simpl.
 apply IHn.
 apply dnn_tl.
 assumption.
Qed.

Section InfiniteAlternatingSum.
(* begin hide *)
Coercion Local Is_true : bool >-> Sortclass.
(* end hide *)
(** Given a stream, we can compute its alternating partial sum up to
an point satifying a predicate, so long as that predicate eventually
exists. *)
Definition PartialAlternatingSumUntil (P:Stream Q -> bool)(seq:Stream Q)(ex:LazyExists P seq) : Q :=
(takeUntil P ex Qminus' 0).

(** The value of the partial sum is between 0 and the head of the
sequence if the sequence is decreasing and nonnegative. *)
Lemma PartialAlternatingSumUntil_small : forall (P:Stream Q -> bool)(seq:Stream Q)(dnn:DecreasingNonNegative seq)(ex:LazyExists P seq), 0 <= (PartialAlternatingSumUntil P ex) <= (hd seq).
Proof.
 intros P seq dnn ex.
 unfold PartialAlternatingSumUntil.
 generalize dnn; clear dnn.
 set (Q := (fun seq b => DecreasingNonNegative seq -> 0 <= b <= hd seq)).
 change (Q seq (takeUntil P ex Qminus' 0)).
 apply takeUntil_elim; unfold Q; clear seq ex Q.
  intros seq _ [[[dnn _] _] _]; auto with *.
 intros seq b IH H [[[Za Zb] [[_ Zd] _]] dnn].
 destruct (IH dnn) as [H0 H1].
 split.
  rewrite -> Qminus'_correct.
  apply: shift_zero_leEq_minus.
  apply Qle_trans with (hd (tl seq)); auto.
 rewrite -> Qle_minus_iff.
 rewrite -> Qminus'_correct.
 ring_simplify.
 assumption.
Qed.

(** A boolean version of Qball. *)
Definition Qball_ex_bool e a b : bool :=
 match ball_ex_dec _ Qmetric_dec e a b with left _ => true | right _ => false end.

Lemma sumbool_eq_true : forall P (dec:{P}+{~P}), (match dec with left _ => true | right _ => false end) = true <-> P.
Proof.
 intros.
 destruct dec; simpl;split;auto.
 discriminate 1.
Qed.

(** If a sequence has a limit of l, then there is a point that gets
arbitrarily close to l. *)
Lemma Limit_near : forall (seq:Stream Q) (l:Q), Limit seq l -> forall e, LazyExists (fun s => Qball_ex_bool e (hd s) l) seq.
Proof.
 intros seq l H e.
 assert (H' := (H e)).
 induction H'.
  left.
  destruct H0 as [H0 _].
  unfold Qball_ex_bool.
  destruct (ball_ex_dec Q_as_MetricSpace Qmetric_dec e (hd x) l).
   constructor.
  apply n; clear n.
  apply H0.
 right.
 rename H1 into IHH'.
 intro.
 apply (IHH' tt).
 apply Limit_tl.
 assumption.
Defined.

(** The infinte sum of an alternating series is the limit of the
partial sums. *)
Definition InfiniteAlternatingSum_raw (seq:Stream Q)(zl:Limit seq 0)(e:QposInf) :=
PartialAlternatingSumUntil _ (Limit_near zl e).

Lemma InfiniteAlternatingSum_prf : forall seq (dnn:DecreasingNonNegative seq) (zl:Limit seq 0), is_RegularFunction (InfiniteAlternatingSum_raw zl).
Proof.
 Opaque Qmetric_dec.
 intros seq dnn zl.
 unfold is_RegularFunction, ball, Qball.
 simpl.
 (*WLOG e2 <= e1*)
 cut (forall e1 e2 : Qpos, e2 <= e1 -> Qball (e1 + e2) (InfiniteAlternatingSum_raw zl e1)
   (InfiniteAlternatingSum_raw zl e2)).
  intros H e1 e2.
  destruct (Qpos_le_total e1 e2).
   setoid_replace (e1+e2)%Qpos with (e2+e1)%Qpos by QposRing.
   apply: ball_sym;simpl.
   auto.
  auto.
 intros e1 e2 He.
 apply: ball_weak;simpl.
 unfold Qball.
 unfold InfiniteAlternatingSum_raw.
 unfold PartialAlternatingSumUntil.
 generalize (Limit_near zl e1) (Limit_near zl e2).
 clear zl.
 intros ex1 ex2.
 simpl in *.
 pose (F:= fun e => (fun s : Stream Q => Qball_ex_bool e (hd s) 0)).
 assert(case1: forall seq (dnn:DecreasingNonNegative seq) (ex2: LazyExists _ seq), (Qball e1 (hd seq) 0) ->
   AbsSmall (R:=Q_as_COrdField) (e1:Q) (0 - (takeUntil (F e2) ex2 Qminus' 0))).
  clear seq dnn ex1 ex2.
  intros seq dnn ex2 [Hseq1 Hseq2].
  apply: AbsSmall_minus;simpl.
  change (AbsSmall (e1:Q) ((PartialAlternatingSumUntil _ (ex2))-0)).
  stepr (PartialAlternatingSumUntil _ (ex2)); [| by (simpl; ring)].
  destruct (PartialAlternatingSumUntil_small _ dnn (ex2)) as [Hl1 Hl2].
  apply AbsSmall_leEq_trans with (hd seq).
   stepl (hd seq - 0);[assumption|simpl;ring].
  split;[|assumption].
  apply Qle_trans with 0;[|assumption].
  simpl.
  rewrite -> Qle_minus_iff; ring_simplify.
  destruct dnn as [[[X _] _] _]; assumption.
 assert(H:=ex1).
 induction H;
   case (ex1); unfold Qball_ex_bool in *; simpl in *; destruct (Qmetric_dec e1 (hd x) 0); try contradiction; auto.
 intros ex3.
 assert (case2:~(Qball e2 (hd x) 0)).
  intros q.
  apply n.
  simpl.
  unfold Qball.
  apply AbsSmall_leEq_trans with (e2:Q); assumption.
 Opaque Qred.
 case (ex2); unfold Qball_ex_bool in *; simpl; destruct (Qmetric_dec e2 (hd x) 0); try contradiction;
   try solve[intros; elim case2].
 intros ex4.
 simpl.
 set (a := (takeUntil (fun s : Stream Q => match Qmetric_dec e1 (hd s) 0 with left _ => true | right _ => false end)
   (ex3 tt)) Qminus' 0).
 set (b:=(takeUntil (fun s : Stream Q => match Qmetric_dec e2 (hd s) 0 with left _ => true | right _ => false end)
   (ex4 tt)) Qminus' 0).
 stepr (b-a); [| by (simpl; repeat rewrite -> Qminus'_correct;
   change (b - a == hd x - a - (hd x - b)); ring)].
 apply AbsSmall_minus.
 rename H0 into IHExists.
 apply (IHExists tt).
 clear - dnn.
 destruct dnn.
 assumption.
Transparent Qmetric_dec.
Qed.

Definition InfiniteAlternatingSum (seq:Stream Q)(dnn:DecreasingNonNegative seq)(zl:Limit seq 0) : CR :=
Build_RegularFunction (InfiniteAlternatingSum_prf dnn zl).

Lemma InfiniteAlternatingSum_step : forall seq (dnn:DecreasingNonNegative seq) (zl:Limit seq 0),
 (InfiniteAlternatingSum dnn zl ==
  ('(hd seq))-(InfiniteAlternatingSum (dnn_tl dnn) (Limit_tl zl)))%CR.
Proof.
 intros [hd seq] [dnn_hd dnn] zl.
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
  destruct dnn_hd as [_ [[Z0 Z1] dnn_hd0]].
  split;simpl.
   apply Qle_trans with 0.
    rewrite -> Qle_minus_iff; ring_simplify; apply Qpos_nonneg.
   ring_simplify.
   apply Z0.
  ring_simplify.
  eapply Qle_trans.
   apply Z1.
  destruct X as [_ X].
  stepl (hd - 0); [| simpl; ring].
  apply X.
 destruct (takeUntil_step P (Limit_near zl e) Qminus' 0) as [ex' rw]; [rewrite H;auto|].
 rewrite rw; clear rw.
 simpl.
 rewrite (@takeUntil_wd Q Q P _ ex' (Limit_near (Limit_tl zl) e)).
 rewrite -> Qminus'_correct.
 apply: ball_refl.
Qed.

(** The infinite alternating series is always nonnegative. *)
Lemma InfiniteAlternatingSum_nonneg : forall seq (dnn:DecreasingNonNegative seq) (zl:Limit seq 0),
 (inject_Q 0%Q <= InfiniteAlternatingSum dnn zl)%CR.
Proof.
 intros seq dnn zl e.
 apply Qle_trans with 0.
  rewrite -> Qle_minus_iff; ring_simplify; apply Qpos_nonneg.
 unfold InfiniteAlternatingSum.
 simpl.
 unfold Cap_raw.
 simpl.
 ring_simplify.
 unfold InfiniteAlternatingSum_raw.
 simpl.
 destruct (PartialAlternatingSumUntil_small _ dnn (Limit_near zl ((1 # 2) * e)%Qpos)).
 assumption.
Qed.

(** The infinite alternating series is always bounded by the first term
in the series. *)
Lemma InfiniteAlternatingSum_bound : forall seq (dnn:DecreasingNonNegative seq) (zl:Limit seq 0),
 (InfiniteAlternatingSum dnn zl <= inject_Q (hd seq))%CR.
Proof.
 intros seq dnn zl.
 rewrite -> InfiniteAlternatingSum_step.
 change (inject_Q (hd seq) - InfiniteAlternatingSum (dnn_tl dnn) (Limit_tl zl)[<=]inject_Q (hd seq))%CR.
 stepr (inject_Q (hd seq) - inject_Q 0%Q)%CR.
  apply: minus_resp_leEq_rht.
  apply InfiniteAlternatingSum_nonneg.
 simpl.
 ring.
Qed.

(** [InfiniteAlternatingSum] is correct. *)
Lemma dnn_zl_convergent : forall (seq:Stream Q),
 forall (dnn:DecreasingNonNegative seq) (zl:Limit seq 0),
 convergent (fun n => inj_Q IR ((-(1))^n*Str_nth n seq)).
Proof.
 intros seq dnn zl.
 cut (convergent (fun n : nat => [--]One[^]n[*]inj_Q IR (Str_nth n seq))).
  apply convergent_wd.
  intros n.
  stepr ((inj_Q IR ((-(1))^n))[*](inj_Q IR (Str_nth n seq))); [| by (apply eq_symmetric; apply inj_Q_mult)].
  apply mult_wdl.
  stepr ((inj_Q IR (-(1)))[^]n); [| by (apply eq_symmetric; apply inj_Q_power)].
  apply nexp_wd.
  stepr ([--](inj_Q IR 1)); [| by (apply eq_symmetric; apply inj_Q_inv)].
  apply un_op_wd_unfolded.
  rstepl ((nring 1):IR).
  apply eq_symmetric; apply (inj_Q_nring IR 1).
 apply alternate_series_conv.
   intros n.
   unfold Str_nth.
   change (Zero:IR) with (nring 0:IR).
   stepl (inj_Q IR (nring 0)); [| by apply inj_Q_nring].
   apply inj_Q_leEq.
   simpl.
   destruct (dnn_Str_nth_tl n dnn) as [[[H _] _] _].
   assumption.
  intros e He.
  destruct (Q_dense_in_CReals IR e He) as [c Hc].
  cut {N : nat & forall m : nat, (N <= m)%nat -> AbsSmall c ((Str_nth m seq))}.
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
  assert (Hc':0<c).
   apply less_inj_Q with IR.
   change (0:Q) with (nring 0:Q).
   stepl (nring 0:IR).
    assumption.
   apply eq_symmetric; apply inj_Q_nring.
  assert (L:=(Limit_near zl (mkQpos Hc'))).
  exists (takeUntil _ L (fun _ => S) O).
  generalize dnn; clear dnn.
  set (Q:= (fun seq b => DecreasingNonNegative seq -> forall m : nat, (b <= m)%nat ->
    AbsSmall (R:=Q_as_COrdField) c (Str_nth m seq))).
  change (Q seq (takeUntil (fun s : Stream Q_as_MetricSpace =>
    Qball_ex_bool (mkQpos (a:=c) Hc') (hd s) 0) L (fun _ : Q_as_MetricSpace => S) 0%nat)).
  apply takeUntil_elim; unfold Q; clear seq zl L Q.
   intros x H dnn m _.
   unfold Str_nth.
   unfold Qball_ex_bool in H.
   destruct (ball_ex_dec Q_as_MetricSpace Qmetric_dec (mkQpos (a:=c) Hc') (hd x) 0) as [b|b]; try contradiction.
   simpl in b.
   apply leEq_imp_AbsSmall.
    destruct (dnn_Str_nth_tl m dnn) as [[[X _] _] _];assumption.
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
 rewrite <- dnn_alt_iff_dnn in dnn.
 destruct (ForAll_Str_nth_tl n dnn) as [[_ X] _].
 rewrite tl_nth_tl in X.
 assumption.
Qed.

Lemma InfiniteAlternatingSum_correct : forall (seq:Stream Q) (x:nat -> IR),
 (forall n:nat, inj_Q IR (((-(1))^n)*Str_nth n seq)%Q[=]x n) ->
 forall (dnn:DecreasingNonNegative seq) zl H,
 (InfiniteAlternatingSum dnn zl==IRasCR (series_sum x H))%CR.
Proof.
 intros seq x Hx dnn zl H.
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
   ((IRasCR (Sum0 (G:=IR) n x)[-]InfiniteAlternatingSum dnn zl)))).
 apply AbsSmall_eps_div_two;[apply Hn; assumption|].
 assert (X:AbsSmall (R:=CRasCReals) (e [/]TwoNZ) (('(((-(1))^n)*(Str_nth n seq)))%CR)).
  stepr (IRasCR (x n)).
   stepr (Sum n n (fun n => IRasCR (x n))); [| by apply: Sum_one].
   unfold Sum, Sum1.
   stepr (IRasCR (Sum0 (S n) x)[-]IRasCR (Sum0 n x )); [| by (apply cg_minus_wd; apply IR_Sum0_as_CR)].
   apply Hn.
   auto.
  simpl.
  symmetry.
  rewrite <- IR_inj_Q_as_CR.
  apply IRasCR_wd.
  apply Hx.
 stepr (('(Sum0 n (fun n => ((-(1))^n)*(Str_nth n seq))%Q))%CR[-]InfiniteAlternatingSum dnn zl).
  clear - X.
  generalize seq dnn zl X.
  clear seq dnn zl X.
  generalize (e[/]TwoNZ).
  clear e.
  induction n; intros e seq dnn zl X.
   simpl in *.
   apply AbsSmall_minus.
   stepr (InfiniteAlternatingSum dnn zl); [| by (unfold cg_minus;simpl;ring)].
   apply leEq_imp_AbsSmall;[apply InfiniteAlternatingSum_nonneg|].
   apply: leEq_transitive;simpl.
    apply InfiniteAlternatingSum_bound.
   assert ((hd seq)%CR == (1*hd seq)%Q). ring. rewrite -> H. clear H.
   destruct X; assumption.
  apply AbsSmall_minus.
  stepr (('(((Sum0 (G:=Q_as_CAbGroup) n (fun n0 : nat =>  ((- (1)) ^ n0 * Str_nth n0 (tl seq))%Q)))%CR)[-]
    InfiniteAlternatingSum (dnn_tl dnn) (Limit_tl zl)))%CR; [apply IHn|].
   rewrite inj_S in X.
   rstepr ([--][--]('(((- (1)) ^ n * Str_nth n (tl seq))%Q))%CR).
   apply inv_resp_AbsSmall.
   stepr (' ((- (1)) ^ Zsucc n * Str_nth (S n) seq))%CR;[assumption|].
   simpl.
   change ((' ( (- (1)) ^ (n+1) * Str_nth n (tl seq)) == - ' ((- (1)) ^ n * Str_nth n (tl seq)))%CR).
   rewrite -> Qpower_plus;[|discriminate].
   simpl.
   ring.
  stepl (InfiniteAlternatingSum dnn zl[-](('(((- (1)) ^ 0 * Str_nth 0 seq)%Q[+]
    ((Sum0 (G:=Q_as_CAbGroup) n
      (fun n0 : nat => ((- (1)) ^ (S n0) * Str_nth n0 (tl seq))%Q))):Q))%CR));[
        apply cg_minus_wd;[reflexivity| rewrite -> CReq_Qeq; apply: Sum0_shift;
          intros i; simpl; reflexivity]|].
  unfold cg_minus; simpl.
  rewrite -> InfiniteAlternatingSum_step.
  generalize (InfiniteAlternatingSum (dnn_tl dnn) (Limit_tl zl)).
  intros x.
  change (Str_nth 0 seq) with (hd seq).
  setoid_replace ((Sum0 (G:=Q_as_CAbGroup) n
    (fun n0 : nat => Qpower_positive (- (1)) (P_of_succ_nat n0)  * Str_nth n0 (tl seq)))%Q:Q)
      with (-(Sum0 (G:=Q_as_CAbGroup) n
        (fun n0 : nat => ((- (1)) ^ n0 * Str_nth n0 (tl seq)))))%Q;[ring|].
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

Lemma InfiniteAlternatingSum_correct' : forall (seq:Stream Q),
 forall (dnn:DecreasingNonNegative seq) zl,
 (InfiniteAlternatingSum dnn zl==IRasCR (series_sum _ (dnn_zl_convergent dnn zl)))%CR.
Proof.
 intros seq dnn zl.
 apply InfiniteAlternatingSum_correct.
 intros; apply eq_reflexive.
Qed.
End InfiniteAlternatingSum.
