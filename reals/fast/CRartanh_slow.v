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
Require Import CoRN.reals.iso_CReals.
Require Import CoRN.reals.fast.CRAlternatingSum.
Require Import CoRN.reals.fast.CRGeometricSum.
Require Import CoRN.reals.fast.CRstreams.
Require Export CoRN.reals.fast.CRArith.
Require Import CoRN.reals.fast.CRIR.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qpower.
Require Import CoRN.model.ordfields.Qordfield.
Require Import CoRN.reals.Q_in_CReals.
Require Import CoRN.model.metric2.Qmetric.
Require Import CoRN.model.totalorder.QMinMax.
Require Import CoRN.transc.ArTanH.
Require Import CoRN.reals.fast.CRarctan_small.
Require Import CoRN.tactics.Qauto.
Require Import CoRN.tactics.CornTac.

Set Implicit Arguments.

Local Open Scope Q_scope.
Local Open Scope uc_scope.

Opaque inj_Q CR.

(**
** Area Tangens Hyperbolicus (artanh)
[artanh] is implemented by as the [GeometricSum] of it's taylor series.
*)

Lemma arctanSequence_Gs : forall a, GeometricSeries (a^2) (arctanSequence a).
Proof.
 intros a.
 apply mult_Streams_Gs.
  apply _.
 apply powers_help_Gs.
 apply Qsqr_nonneg.
Qed.

Lemma Qsqr_lt_one : forall (a:Q), (-(1) < a) -> a < 1 -> (a^2 < 1).
Proof.
 intros a H0 H1.
 rewrite -> Qlt_minus_iff in *.
 replace RHS with ((1 + - a)*(a + - -(1))) by simpl; ring.
 Qauto_pos.
Qed.

Lemma artanh_DomArTanH : forall a, (a^2 < 1) -> DomArTanH (inj_Q IR a).
Proof.
 intros a Ha.
 split.
  stepl (inj_Q IR (-(1))%Q).
   apply inj_Q_less; simpl.
   apply Qnot_le_lt.
   intros H.
   apply (Qlt_not_le _ _ Ha).
   rewrite ->  Qle_minus_iff in *.
   replace RHS with ((- (1) + - a + 2)*(-(1) +- a)) by simpl; ring.
   Qauto_nonneg.
  stepr ([--](inj_Q IR 1)).
   apply inj_Q_inv.
  apply un_op_wd_unfolded.
  rstepr (nring 1:IR).
  apply (inj_Q_nring IR 1).
 stepr (inj_Q IR (1)).
  apply inj_Q_less; simpl.
  apply Qnot_le_lt.
  intros H.
  apply (Qlt_not_le _ _ Ha).
  rewrite -> Qle_minus_iff in *.
  replace RHS with ((a + - (1) + 2)*(a +- (1))) by simpl; ring.
  Qauto_nonneg.
 rstepr (nring 1:IR).
 apply (inj_Q_nring IR 1).
Qed.

(** Although this function works on the entire domain of [artanh], it is
only reasonably fast for values close to 0, say [[-(2/3), 2/3]]. *)
Definition rational_artanh_slow (a:Q) (p1: a^2 < 1) : CR :=
 InfiniteGeometricSum (Qsqr_nonneg a) p1 (arctanSequence_Gs a).

Lemma GeometricSeries_convergent
  : forall (a : Q) (apos : 0 <= a) (aone : a < 1) (series:Stream Q),
 GeometricSeries a series ->
 convergent (fun n => inj_Q IR (Str_nth n series)).
Proof.
 intros a apos aone series H.
 apply ratio_test_conv.
 exists 0%nat.
 exists (inj_Q IR a).
  rstepr (nring 1:IR).
  stepr (inj_Q IR (nring 1)); [| now apply (inj_Q_nring IR 1)].
  apply inj_Q_less.
  assumption.
 assert (Ha0':[0][<=]inj_Q IR a).
  rstepl (nring 0:IR).
  stepl (inj_Q IR (nring 0)); [| now apply (inj_Q_nring IR 0)].
  apply inj_Q_leEq.
  assumption.
 split.
  assumption.
 intros n _.
 destruct (ForAll_Str_nth_tl n H) as [H0 _].
 stepr (inj_Q IR a[*](inj_Q IR (Qabs (Str_nth n series)))); [| now
   apply mult_wdr; apply eq_symmetric; apply AbsIR_Qabs].
 stepl (inj_Q IR (Qabs (Str_nth (S n) series))); [| now apply eq_symmetric; apply AbsIR_Qabs].
 rewrite <- inj_Q_mult.
 apply inj_Q_leEq.
 replace (S n) with (1+n)%nat by auto with *.
 rewrite <- Str_nth_plus.
 assumption.
Qed.

(* This is a horrendous proof.  I'm sure half of it isn't needed, but I don't care to make it better
 all proofs of this are extensionally equivalent anyway *)
Lemma InfiniteGeometricSum_correct
  : forall (a : Q) (apos : 0 <= a) (aone : a < 1) (series:Stream Q) (x:nat -> IR),
 (forall n:nat, inj_Q IR (Str_nth n series)%Q[=]x n) ->
 forall (Gs:GeometricSeries a series) H,
 (InfiniteGeometricSum apos aone Gs==IRasCR (series_sum x H))%CR.
Proof.
 intros a apos aone seq x Hx Gs H.
 unfold series_sum.
 rewrite -> IR_Lim_as_CR.
 apply (SeqLimit_unique CRasCReals).
 intros e He.
 generalize (IR_Cauchy_prop_as_CR (Build_CauchySeq IR (seq_part_sum x) H)).
 intros C.
 destruct (C _ (pos_div_two _ _ He)) as [n Hn].
 exists n.
 intros m Hm.
 unfold CS_seq in *.
 clear C.
 unfold seq_part_sum in *.
 setoid_replace (@cg_minus CRasCGroup (IRasCR (Sum0 m x)) (InfiniteGeometricSum apos aone Gs))
   with (((IRasCR (Sum0 (G:=IR) m x) - (IRasCR (Sum0 (G:=IR) n x))) + 
          ((IRasCR (Sum0 (G:=IR) n x) - InfiniteGeometricSum apos aone Gs))))%CR
   by (unfold cg_minus; simpl; ring).
 apply (AbsSmall_eps_div_two CRasCOrdField
          e (IRasCR (Sum0 m x) - IRasCR (Sum0 n x))
          (IRasCR (Sum0 n x) - InfiniteGeometricSum apos aone Gs))%CR.
 exact (Hn m Hm).
 clear m Hm.
 setoid_replace (IRasCR (Sum0 n x))
   with ('(@Sum0 Q_as_CAbGroup n (fun n => (Str_nth n seq))%Q))%CR.
  revert seq x H Hx Gs Hn.
  induction n.
   intros seq x H Hx Gs Hn.
   simpl (Sum0 0 (fun n : nat => Str_nth n seq)).
   apply (AbsSmall_minus CRasCOrdField (e [/]TwoNZ) (InfiniteGeometricSum apos aone Gs) 0%CR).
   setoid_replace (@cg_minus CRasCOrdField (InfiniteGeometricSum apos aone Gs) 0%CR)
     with (InfiniteGeometricSum apos aone Gs)
     by (unfold cg_minus; simpl; ring).
   assert (Hn' : forall m : nat, (0 <= m)%nat -> AbsSmall (R:=CRasCOrdField) (e [/]TwoNZ)
     (IRasCR (Sum0 (G:=IR) m x))).
   { intros m Hm.
     setoid_replace (IRasCR (Sum0 m x))
       with (@cg_minus CRasCOrdField (IRasCR (Sum0 (G:=IR) m x)) (IRasCR (Sum0 (G:=IR) 0 x))).
     apply Hn; assumption.
    unfold cg_minus.
    simpl.
    rewrite -> IR_Zero_as_CR.
    ring. }
   stepl (IRasCR (CRasIR (e[/]TwoNZ)))%CR; [| now apply CRasIRasCR_id].
   stepr (IRasCR (CRasIR (InfiniteGeometricSum apos aone Gs)))%CR; [| now apply CRasIRasCR_id].
   rewrite <- IR_AbsSmall_as_CR.
   apply AbsSmall_approach.
   intros d Hd.
   rewrite -> IR_AbsSmall_as_CR.
   stepr (InfiniteGeometricSum apos aone Gs); [| now apply eq_symmetric; apply CRasIRasCR_id].
   destruct (Q_dense_in_CReals IR d) as [q Hq0 Hq].
    assumption.
   assert (Hq0': 0 < q).
    apply (less_inj_Q IR).
    stepl ([0]:IR).
     assumption.
    apply eq_symmetric; apply (inj_Q_nring IR 0).
   destruct (InfiniteGeometricSum_small_tail apos aone (exist _ _ Hq0') Gs) as [m Hm].
   setoid_replace (InfiniteGeometricSum apos aone Gs)
     with ((IRasCR (Sum0 (G:=IR) m x)) + ((InfiniteGeometricSum apos aone Gs) - (IRasCR (Sum0 (G:=IR) m x))))%CR by ring.
   stepl (IRasCR (CRasIR (e [/]TwoNZ)) + (IRasCR d))%CR; [| now apply eq_symmetric; apply IR_plus_as_CR].
   apply (AbsSmall_plus CRasCOrdField (IRasCR (CRasIR (e [/]TwoNZ))) (IRasCR d)
                        (IRasCR (Sum0 m x))
                        (InfiniteGeometricSum apos aone Gs - IRasCR (Sum0 m x)))%CR. 
    stepl (e [/]TwoNZ); [| now apply eq_symmetric; apply CRasIRasCR_id].
    apply Hn'; auto with *.
   apply AbsSmall_leEq_trans with ('q)%CR.
    stepl (IRasCR (inj_Q IR q)); [| now apply IR_inj_Q_as_CR].
    rewrite <- IR_leEq_as_CR.
    apply less_leEq.
    assumption.
    simpl in Hm.
   clear - Hm Hx.
   revert seq x Hx Gs Hm.
   induction m.
    intros seq x Hx Gs Hm.
    stepr (InfiniteGeometricSum apos aone Gs).
     apply Hm.
    unfold cg_minus.
    simpl.
    rewrite -> IR_Zero_as_CR.
    unfold msp_Equiv; ring.
   intros seq x Hx Gs Hm.
   setoid_replace (InfiniteGeometricSum apos aone Gs - IRasCR (Sum0 (S m) x))%CR
     with (InfiniteGeometricSum apos aone (ForAll_Str_nth_tl 1 Gs) - IRasCR (Sum0 (G:=IR) m (fun n => (x (S n)))))%CR.
    apply IHm.
     intros n.
     stepl ((inj_Q IR (Str_nth (S n) seq)%Q)).
      apply Hx.
     apply eq_reflexive.
    intros.
    apply Hm.
   rewrite -> InfiniteGeometricSum_step.
   setoid_replace (IRasCR (Sum0 (G:=IR) (S m) x))
     with (IRasCR (inj_Q _ (CoqStreams.hd seq) [+](Sum0 (G:=IR) m (fun n0 : nat => (x (S n0)))%Q))).
    rewrite -> (IR_plus_as_CR).
    rewrite -> IR_inj_Q_as_CR.
    ring.
   apply IRasCR_wd.
   apply eq_symmetric.
   stepl (x O[+]Sum0 (G:=IR) m (fun n0 : nat => (x (S n0)))).
    apply Sum0_shift.
    intros i.
    apply eq_reflexive.
   apply bin_op_wd_unfolded.
    apply eq_symmetric.
    apply (Hx O).
   apply eq_reflexive.
  intros seq x H Hx Gs Hn.
  set (y:=(fun n => (x (n + 1)%nat))).
  setoid_replace (' Sum0 (S n) (fun n0 : nat => Str_nth n0 seq) -
     InfiniteGeometricSum apos aone Gs)%CR
    with (('(((Sum0 (G:=Q_as_CAbGroup) n (fun n0 : nat =>  Str_nth n0 (CoqStreams.tl seq))%Q)))%CR) -  InfiniteGeometricSum apos aone (ForAll_Str_nth_tl 1 Gs))%CR.
  apply (IHn (CoqStreams.tl seq) y ).
     apply tail_series with x.
      assumption.
     exists 1%nat.
     exists 0%nat.
     intros; apply eq_reflexive.
    intros m.
    unfold y.
    stepr ((inj_Q IR (Str_nth (m+1) seq))); [| now apply (Hx (m + 1)%nat)].
    rewrite <- Str_nth_plus.
    apply eq_reflexive.
   intros m Hm.
   setoid_replace (@cg_minus CRasCOrdField (IRasCR (Sum0 m y)) (IRasCR (Sum0 n y)))
     with (IRasCR (Sum0 (G:=IR) (S m) x) - IRasCR (Sum0 (G:=IR) (S n) x))%CR.
    apply (Hn (S m)).
    apply le_n_S, Hm.
    symmetry.
    change (@cg_minus CRasCOrdField (IRasCR (Sum0 m y)) (IRasCR (Sum0 n y)))
      with (IRasCR (Sum0 m y) - IRasCR (Sum0 n y))%CR.
   do 2 rewrite <- IR_minus_as_CR.
   apply IRasCR_wd.
   stepr ((x O[+]Sum0 (G:=IR) m y[-](x O[+]Sum0 (G:=IR) n y))).
    apply bin_op_wd_unfolded;[|apply un_op_wd_unfolded]; apply eq_symmetric; apply Sum0_shift;
      intros; unfold y;rewrite plus_comm; apply eq_reflexive.
   rational.
  rewrite -> InfiniteGeometricSum_step.
  set (z:=(fun n0 : nat => (Str_nth n0 seq)%Q)).
  setoid_replace ((Sum0 (G:=Q_as_CAbGroup) (S n) z):Q) with ((z O + (Sum0 (G:=Q_as_CAbGroup) n
    (fun n0 : nat => (Str_nth n0 (CoqStreams.tl seq))%Q)))).
   rewrite <- (CRplus_Qplus (z O)).
   unfold z, Str_nth.
   simpl.
   ring.
  symmetry.
  apply (@Sum0_shift Q_as_CAbGroup).
  intros i.
  reflexivity.
 clear - Hx.
 induction n.
  exact IR_Zero_as_CR.
  simpl.
  rewrite IR_plus_as_CR, IHn.
 rewrite <- CRplus_Qplus.
  apply CRplus_eq_r. 
  transitivity (IRasCR (inj_Q IR (Str_nth n seq)%Q)).
  apply IRasCR_wd; symmetry; apply Hx.
  apply IR_inj_Q_as_CR.
Qed.

Lemma InfiniteGeometricSum_correct'
  : forall (series:Stream Q) (a : Q) (apos : 0 <= a) (aone : a < 1),
 forall (Gs:GeometricSeries a series),
   (InfiniteGeometricSum apos aone Gs
    == IRasCR (series_sum _ (GeometricSeries_convergent apos aone Gs)))%CR.
Proof.
 intros series a apos aone Gs.
 apply InfiniteGeometricSum_correct.
 intros; apply eq_reflexive.
Qed.

Lemma rational_artanh_slow_correct : forall (a:Q) Ha Ha0,
 (@rational_artanh_slow a Ha == IRasCR (ArTanH (inj_Q IR a) Ha0))%CR.
Proof.
intros a Ha Ha0.
unfold rational_artanh_slow.
rewrite InfiniteGeometricSum_correct'.
apply IRasCR_wd.
 eapply eq_transitive_unfolded;
 [|apply (ArTanH_series (inj_Q IR a) (ArTanH_series_convergent_IR) (artanh_DomArTanH Ha) Ha0)].
simpl.
unfold series_sum.
apply Lim_seq_eq_Lim_subseq with double.
  unfold double; auto with *.
 intros n.
 exists (S n).
 unfold double; auto with *.
intros n.
simpl.
clear - n.
induction n.
 apply eq_reflexive.
simpl.
set (A:=nexp IR (Nat.add n (S n)) (inj_Q IR a[-][0])).
rewrite plus_comm.
simpl.
fold (double n).
csetoid_rewrite_rev IHn.
clear IHn.
csetoid_replace (ArTanH_series_coef (Nat.double n)[*]nexp IR (Nat.double n) (inj_Q IR a[-][0])) ([0]:IR).
csetoid_replace (ArTanH_series_coef (S (Nat.double n))[*]A) 
                (inj_Q IR (Str_nth n (arctanSequence a))).
  rational.
 unfold ArTanH_series_coef.
 case_eq (even_odd_dec (S (double n))); intros H.
  elim (not_even_and_odd _ H).
  constructor.
  apply even_plus_n_n.
 intros _.
 eapply eq_transitive;
  [|apply inj_Q_wd; simpl;symmetry;apply Str_nth_arctanSequence].
 eapply eq_transitive;
  [|apply eq_symmetric; apply inj_Q_mult].
 apply mult_wd.
  assert (X:(inj_Q IR (nring (S (double n))))[#][0]).
   stepr (inj_Q IR [0]).
    apply inj_Q_ap.
    apply nringS_ap_zero.
   apply (inj_Q_nring IR 0).
  stepr (inj_Q IR (nring 1)[/]_[//]X).
   apply div_wd.
    rstepl (nring 1:IR).
    apply eq_symmetric.
    apply (inj_Q_nring IR 1).
   apply eq_symmetric.
   apply (inj_Q_nring).
  assert (X0:inj_Q IR (inject_Z (P_of_succ_nat (2 * n)))[#][0]).
   stepr (inj_Q IR [0]).
    apply inj_Q_ap.
    discriminate.
   apply (inj_Q_nring IR 0).
  eapply eq_transitive;
   [|apply inj_Q_wd; symmetry; apply Qmake_Qdiv]. 
  eapply eq_transitive;
   [|apply eq_symmetric; apply (fun b => inj_Q_div _ b _ X0)].
  apply div_wd.
   apply eq_reflexive.
  apply inj_Q_wd.
  rewrite <- POS_anti_convert.
  eapply eq_transitive;[apply nring_Q|].
  unfold double.
  simpl.
  replace (n+0)%nat with n by ring.
  reflexivity.
 unfold A; clear A.
 eapply eq_transitive;[|apply eq_symmetric; apply inj_Q_power].
 change ((inj_Q IR a[-][0])[^](n+S n)[=]inj_Q IR a[^](1 + 2 * n)).
 replace (n + S n)%nat with (1 + 2*n)%nat by ring.
  apply nexp_wd.
 rational.
unfold ArTanH_series_coef.
case_eq (even_odd_dec (double n)).
 intros _ _.
 rational.
intros o.
elim (fun x=> not_even_and_odd _ x o).
apply even_plus_n_n.
Qed.

(* This development is incomplete.  At the moment only what is needed
for logorithm has been developed. *)
