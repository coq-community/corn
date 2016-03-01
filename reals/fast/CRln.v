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

Require Import CoRN.reals.fast.CRartanh_slow.
Require Export CoRN.reals.fast.CRArith.
Require Import CoRN.reals.fast.CRIR.
Require Import Coq.QArith.Qpower.
Require Import CoRN.model.ordfields.Qordfield.
Require Import CoRN.reals.fast.ModulusDerivative.
Require Import CoRN.reals.fast.ContinuousCorrect.
Require Import CoRN.model.metric2.Qmetric.
Require Import CoRN.tactics.Qauto.
Require Import CoRN.transc.Exponential.
Require Import CoRN.transc.ArTanH.
Require Import CoRN.tactics.CornTac.

Set Implicit Arguments.

Open Local Scope Q_scope.
Open Local Scope uc_scope.

Opaque inj_Q CR Logarithm.

(**
** Logarithm
Logarithm is defined in terms of artanh. [ln (n/d) = 2*artan((n-d)/(n+d))]
*)

Lemma lnDomainAdaptor : forall a, (0 < a) ->
(let (n,d) := a in (n - d)/(n + d))^2 < 1.
Proof.
 intros [[|n|n] d] Ha; try solve [elim (Qlt_not_le _ _ Ha); auto with *].
 simpl.
 replace LHS with ((n-d)*(n-d)/((n+d)*(n+d))) by simpl; field; auto with *.
 apply Qlt_shift_div_r.
  auto with *.
 rewrite -> Qlt_minus_iff.
 ring_simplify.
 Qauto_pos.
Qed.

(** Although [rational_ln_slow] works on the entire to domain, it is
only efficent for values close 1. *)
Definition rational_ln_slow (a:Q) (p: 0 < a) : CR :=
 scale 2 (rational_artanh_slow (lnDomainAdaptor p)).

Lemma Qpos_adaptor : forall q, 0 < q -> [0][<]inj_Q IR q.
Proof.
 intros q H.
 stepl (inj_Q IR 0).
  apply inj_Q_less.
  assumption.
 apply (inj_Q_nring IR 0).
Qed.

Lemma rational_ln_slow_correct : forall (a:Q) Ha Ha0,
 (@rational_ln_slow a Ha == IRasCR (Log (inj_Q IR a) Ha0))%CR.
Proof.
 intros a Ha Ha0.
 unfold rational_ln_slow.
 assert (X:=artanh_DomArTanH (lnDomainAdaptor Ha)).
 rewrite -> (fun x => rational_artanh_slow_correct x X).
 rewrite <- CRmult_scale.
 rewrite <- IR_inj_Q_as_CR.
 rewrite <- IR_mult_as_CR.
 apply IRasCR_wd.
 csetoid_replace (inj_Q IR (2:Q)) (Two:IR); [|apply (inj_Q_nring IR 2)].
 stepr (Two[*](Half[*]Log _ Ha0)); [|unfold Half; rational].
 do 2 apply: mult_wdr.
 unfold Log.
 simpl.
 apply cspf_wd.
 set (b:=let (n, d) := a in (n - d) / (n + d)).
 assert (Y:inj_Q IR a[+][1][#][0]).
  apply Greater_imp_ap.
  apply plus_resp_pos; try assumption.
  apply pos_one.
 assert (Z:[1][-](inj_Q IR a[-][1][/]_[//]Y)[#][0]).
  apply Greater_imp_ap.
  rstepr (Two[/]_[//]Y).
  apply div_resp_pos.
   apply plus_resp_pos; try assumption.
   apply pos_one.
  apply pos_two.
 rstepr ([1][+](inj_Q IR a[-][1][/]_[//]Y)[/]_[//]Z).
 cut (inj_Q IR b[=](inj_Q IR a[-][1][/]inj_Q IR a[+][1][//]Y)).
  intros.
  apply div_wd;
    apply bin_op_wd_unfolded; try apply eq_reflexive; try apply un_op_wd_unfolded; assumption.
 stepr (inj_Q IR ((a-1)/(a+1))).
  apply inj_Q_wd.
  clear - Ha.
  destruct a as [n d].
  simpl.
  unfold b.
  rewrite -> Qmake_Qdiv.
  field.
  split.
   unfold Qeq.
   auto with *.
  unfold Qeq, Qlt in *.
  simpl in *.
  intros H.
  apply (Zlt_not_le _ _ Ha).
  ring_simplify in H.
  ring_simplify.
  apply Zle_trans with (-(d*1))%Z; auto with *.
  apply Zle_left_rev.
  replace RHS with (-(n + (d*1)))%Z by ring.
  simpl.
  rewrite H.
  apply Zle_refl.
 clear - Y.
 assert (X:inj_Q IR (a + 1)[#][0]).
  stepl (inj_Q IR a [+]inj_Q IR (nring 1)); [| now apply eq_symmetric; apply inj_Q_plus].
  csetoid_rewrite (inj_Q_nring IR 1).
  rstepl (inj_Q IR a[+][1]).
  assumption.
 stepl (inj_Q IR (a - 1)[/]_[//]X); [| now apply eq_symmetric; apply inj_Q_div].
 apply div_wd.
  stepl (inj_Q IR a[-]inj_Q IR 1); [| now apply eq_symmetric; apply inj_Q_minus].
  apply bin_op_wd_unfolded.
   apply eq_reflexive.
  apply un_op_wd_unfolded.
  rstepr (nring 1:IR).
  apply (inj_Q_nring IR 1).
 stepl (inj_Q IR a[+]inj_Q IR 1); [| now apply eq_symmetric; apply inj_Q_plus].
 apply bin_op_wd_unfolded.
  apply eq_reflexive.
 rstepr (nring 1:IR).
 apply (inj_Q_nring IR 1).
Qed.

Lemma rational_ln_slow_correct' : forall (a:Q) Ha,
 (@rational_ln_slow a Ha == IRasCR (Log (inj_Q IR a) (Qpos_adaptor Ha)))%CR.
Proof.
 intros.
 apply rational_ln_slow_correct.
Qed.

(** Efficeny of ln is imporved by scaling the input by a power of two
and adding or subtracting a multiple of [ln 2]. *)
Definition ln2 : CR := rational_ln_slow (pos_two Q_as_COrdField).

Lemma ln2_correct : (ln2 == IRasCR (Log Two (pos_two IR)))%CR.
Proof.
 unfold ln2.
 rewrite -> rational_ln_slow_correct'.
 apply IRasCR_wd.
 apply Log_wd.
 apply (inj_Q_nring IR 2).
Qed.

Lemma ln_scale_by_two_power_adapt : forall (n:Z) q, 0 < q -> 0 < (2^n*q).
Proof.
 intros n q H.
 apply: mult_resp_pos; simpl; try assumption.
 assert (H2:0 < 2) by constructor.
 pose (twopos := mkQpos H2).
 setoid_replace (2%positive:Q) with (twopos:Q) by reflexivity.
 apply Qpos_power_pos.
Qed.

Lemma ln_scale_by_two_power : forall (n:Z) q (Hq:0 < q), (rational_ln_slow Hq + scale n ln2 == rational_ln_slow (ln_scale_by_two_power_adapt n Hq))%CR.
Proof.
 intros n q Hq.
 rewrite -> ln2_correct.
 do 2 rewrite -> rational_ln_slow_correct'.
 rewrite <- CRmult_scale.
 rewrite <- IR_inj_Q_as_CR.
 rewrite <- IR_mult_as_CR.
 rewrite <- IR_plus_as_CR.
 apply IRasCR_wd.
 assert (X:[0][<](Two[//](two_ap_zero IR))[^^]n).
  apply zexp_pos.
  apply pos_two.
 stepl (Log _ (Qpos_adaptor Hq)[+]Log _ X).
  assert (Y:[0][<](inj_Q IR q)[*](Two[//](two_ap_zero IR))[^^]n).
   apply mult_resp_pos.
    apply (Qpos_adaptor Hq).
   assumption.
  stepl (Log _ Y).
   apply Log_wd.
   assert (Z:(inj_Q IR (2:Q))[#][0]).
    stepr (inj_Q IR (0:Q)).
     apply inj_Q_ap.
     discriminate.
    apply (inj_Q_nring IR 0).
   csetoid_replace ((Two[//]two_ap_zero IR)[^^](n)) (((inj_Q IR (2:Q))[//]Z)[^^]n).
    stepr (inj_Q IR q[*]inj_Q IR (2^n)).
     apply mult_wdr.
     apply eq_symmetric.
     apply inj_Q_power_Z.
    rstepl (inj_Q IR (2 ^ n)[*]inj_Q IR q).
    apply eq_symmetric.
    apply (inj_Q_mult IR (2^n) q).
   apply zexp_wd.
   apply eq_symmetric.
   apply (inj_Q_nring IR 2).
  apply Log_mult.
 apply bin_op_wd_unfolded.
  apply eq_reflexive.
 astepl ((zring n)[*]Log Two (pos_two IR)).
 apply mult_wdl.
 Transparent inj_Q.
 unfold inj_Q.
 simpl.
 rational.
Qed.

Definition ln_scale_power_factor q (Hq:0 < q) : Z.
Proof.
 revert q Hq.
 intros [[|n|n] d] Hq; try abstract discriminate Hq.
 exact (Zpred (log_inf d - (log_sup n)))%Z.
Defined.

Definition rational_ln (a:Q) (p: 0 < a) : CR :=
 let n := ln_scale_power_factor p in
 (rational_ln_slow (ln_scale_by_two_power_adapt n p) + scale (-n)%Z ln2)%CR.

Lemma rational_ln_correct : forall (a:Q) Ha Ha0,
 (@rational_ln a Ha == IRasCR (Log (inj_Q IR a) Ha0))%CR.
Proof.
 intros a Ha Ha0.
 unfold rational_ln.
 rewrite <- ln_scale_by_two_power.
 do 2 rewrite <- CRmult_scale.
 change (((- ln_scale_power_factor Ha)%Z):Q) with ((- ln_scale_power_factor Ha)%Q).
 rewrite <- CRopp_Qopp.
 ring_simplify.
 apply rational_ln_slow_correct.
Qed.

Lemma rational_ln_correct' : forall (a:Q) Ha,
 (@rational_ln a Ha == IRasCR (Log (inj_Q IR a) (Qpos_adaptor Ha)))%CR.
Proof.
 intros.
 apply rational_ln_correct.
Qed.

(** [ln] is uniformly continuous on any close strictly positive interval. *)
Lemma ln_uc_prf_pos : forall (c:Qpos) (x:Q), (0 < Qmax c x).
Proof.
 intros c x.
 simpl.
 apply Qlt_le_trans with c; auto with *.
Qed.

Definition rational_ln_modulus (c:Qpos) (e:Qpos) : QposInf :=
Qpos2QposInf (c*e).

Lemma ln_pos_uc_prf (c:Qpos) : is_UniformlyContinuousFunction (fun x => rational_ln (ln_uc_prf_pos c x)) (rational_ln_modulus c).
Proof.
 set (lnf := fun x => match (Qlt_le_dec 0 x) with | left p => rational_ln p | right _ => 0%CR end).
 apply (is_UniformlyContinuousFunction_wd) with (fun x : Q_as_MetricSpace => lnf (QboundBelow_uc c x)) (Qscale_modulus (Qpos_inv c)).
   intros x.
   unfold lnf.
   destruct (Qlt_le_dec 0 (QboundBelow_uc c x)).
    do 2 rewrite -> rational_ln_correct'.
    apply IRasCR_wd.
    algebra.
   elim (Qle_not_lt _ _ q).
   apply: ln_uc_prf_pos.
  apply Qpos_positive_numerator_rect.
  intros xn xd.
  revert c.
  apply Qpos_positive_numerator_rect.
  intros.
  apply: Qle_refl.
 assert (Z:Derivative (closel (inj_Q IR (c:Q))) I Logarithm {1/}FId).
  apply (Included_imp_Derivative (openl [0]) I).
   Deriv.
  intros x Hx.
  simpl.
  apply less_leEq_trans with (inj_Q IR (c:Q)); try assumption.
  stepl (inj_Q IR 0).
   apply inj_Q_less.
   simpl; auto with *.
  apply (inj_Q_nring IR 0).
 apply (is_UniformlyContinuousD (Some (c:Q)) None I _ _ Z lnf).
  intros q Hq Hc.
  unfold lnf.
  destruct (Qlt_le_dec 0 q).
   apply rational_ln_correct.
  elim (Qle_not_lt _ _ q0).
  apply Qlt_le_trans with c; auto with *.
  apply leEq_inj_Q with IR.
  assumption.
 intros x Hx Hc.
 apply AbsSmall_imp_AbsIR.
 apply leEq_imp_AbsSmall.
  apply: shift_leEq_div.
   apply less_leEq_trans with (inj_Q IR (c:Q)); try assumption.
   stepl (inj_Q IR 0).
    apply inj_Q_less.
    simpl; auto with *.
   apply (inj_Q_nring IR 0).
  rstepl ([0]:IR).
  apply less_leEq.
  apply pos_one.
 stepr ([1][/]_[//](Greater_imp_ap _ _ _ (Qpos_adaptor (Qpos_prf c)))).
  apply: recip_resp_leEq; try assumption.
  stepl (inj_Q IR 0).
   apply inj_Q_less.
   simpl; auto with *.
  apply (inj_Q_nring IR 0).
 stepl (((inj_Q IR 1)[/]_[//] Greater_imp_ap IR (inj_Q IR (c:Q)) [0] (Qpos_adaptor (Qpos_prf c)))).
  clear.
  revert c.
  apply Qpos_positive_numerator_rect.
  intros.
  change (inj_Q IR ((Qpos_inv (a#b)):Q)) with (inj_Q IR (1/(a#b))).
  apply eq_symmetric.
  apply inj_Q_div.
 apply div_wd.
  rstepr (nring 1:IR).
  apply (inj_Q_nring IR 1).
 apply eq_reflexive.
Qed.

Definition ln_pos_uc (c:Qpos) :  Q_as_MetricSpace --> CR :=
Build_UniformlyContinuousFunction (@ln_pos_uc_prf c).

Definition CRln_pos (c:Qpos) : CR --> CR := (Cbind QPrelengthSpace (ln_pos_uc c)).

Lemma CRln_pos_correct : forall (c:Qpos) x Hx, closel (inj_Q _ (c:Q)) x -> (IRasCR (Log x Hx)==CRln_pos c (IRasCR x))%CR.
Proof.
 intros c x Hx Hx0.
 assert (Z:Continuous (closel (inj_Q IR (c:Q))) Logarithm).
  apply (Included_imp_Continuous (openl [0])).
   Contin.
  clear - c.
  intros x Hx.
  simpl.
  apply less_leEq_trans with (inj_Q IR (c:Q)); try assumption.
  stepl (inj_Q IR 0).
   apply inj_Q_less.
   simpl; auto with *.
  apply (inj_Q_nring IR 0).
 apply (fun x => @ContinuousCorrect _ x Logarithm Z); auto with *.
  constructor.
 intros q Hq H.
 change (CRln_pos c (' q) == IRasCR (Log (inj_Q IR q) Hq))%CR.
 transitivity (ln_pos_uc c q);[|].
  unfold CRln_pos.
  change (' q)%CR with (Cunit_fun _ q).
  rewrite -> (Cbind_correct QPrelengthSpace (ln_pos_uc c) (Cunit_fun Q_as_MetricSpace q)).
  apply: BindLaw1.
 simpl.
 rewrite -> rational_ln_correct'.
 apply IRasCR_wd.
 apply Log_wd.
 apply inj_Q_wd.
 simpl.
 rewrite <- Qle_max_r.
 apply leEq_inj_Q with IR.
 assumption.
Qed.

Definition CRln (x:CR) (Hx:(0 < x)%CR) : CR :=
let (c,_) := Hx in CRln_pos c x.
(* begin hide *)
Implicit Arguments CRln [].
(* end hide *)
Lemma CRln_correct : forall x Hx Hx0, (IRasCR (Log x Hx)==CRln (IRasCR x) Hx0)%CR.
Proof.
 intros x Hx [c Hc].
 apply CRln_pos_correct.
 change ((inj_Q IR (c:Q))[<=]x).
 rewrite -> IR_leEq_as_CR.
 rewrite -> IR_inj_Q_as_CR.
 setoid_replace (IRasCR x) with (IRasCR x - 0)%CR by (simpl; ring).
 assumption.
Qed.

Lemma CRln_pos_ln : forall (c:Qpos) (x:CR) Hx,
 ('c <= x ->
  CRln_pos c x == CRln x Hx)%CR.
Proof.
 intros c x Hx Hc.
 assert (X:[0][<](CRasIR x)).
  apply CR_less_as_IR.
  apply CRltT_wd with 0%CR x; try assumption.
   rewrite -> IR_Zero_as_CR.
   reflexivity.
  rewrite -> CRasIRasCR_id.
  reflexivity.
 destruct Hx as [d Hd].
 unfold CRln.
 rewrite <- (CRasIRasCR_id x).
 rewrite <- (CRln_pos_correct c _ X).
  rewrite <- (CRln_pos_correct d _ X).
   reflexivity.
  change (inj_Q IR (d:Q)[<=](CRasIR x)).
  rewrite -> IR_leEq_as_CR.
  autorewrite with IRtoCR.
  rewrite -> CRasIRasCR_id.
  ring_simplify in Hd.
  assumption.
 change (inj_Q IR (c:Q)[<=](CRasIR x)).
 rewrite -> IR_leEq_as_CR.
 autorewrite with IRtoCR.
 rewrite -> CRasIRasCR_id.
 assumption.
Qed.

Lemma CRln_wd : forall (x y:CR) Hx Hy, (x == y -> CRln x Hx == CRln y Hy)%CR.
Proof.
 intros x y [c Hc] Hy Hxy.
 unfold CRln at 1.
 rewrite -> Hxy.
 apply CRln_pos_ln.
 rewrite <- Hxy.
 ring_simplify in Hc.
 assumption.
Qed.

Lemma CRln_irrelvent : forall x Hx Hx0, (CRln x Hx == CRln x Hx0)%CR.
Proof.
 intros.
 apply CRln_wd.
 reflexivity.
Qed.
