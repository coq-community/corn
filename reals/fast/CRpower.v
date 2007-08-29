Require Export CRIR.
Require Import CRArith.
Require Import Qpower.
Require Import ModulusDerivative.
Require Import ContinuousCorrect.
Require Import Qmetric.
Require Import CornTac.

Opaque CR inj_Q.

Open Local Scope Q_scope.
Open Local Scope uc_scope.

Section CRpower_positive.

Variable p: positive.

Definition Qpower_positive_modulus (c:Qpos) (e:Qpos) : QposInf :=
Qpos2QposInf (e/((p#1)*c^(Zpred p))).

Lemma Qpower_positive_correct : forall p q, (inj_Q IR (Qpower_positive q p)[=]((FId{^}p) (inj_Q IR q) CI)).
Proof.
clear p.
intros p.
destruct (p_is_some_anti_convert p) as [n Hn].
simpl.
rewrite Hn.
clear Hn.
intros q.
induction n.
simpl.
algebra.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
rewrite nat_of_P_o_P_of_succ_nat_eq_succ in IHn.
change (P_of_succ_nat (S n)) with (Psucc (P_of_succ_nat n)).
unfold pos2Z.
simpl in *.
rewrite Pplus_one_succ_r.
stepl (inj_Q IR (Qpower_positive q (P_of_succ_nat n))[*](inj_Q IR q)).
csetoid_rewrite IHn.
apply eq_reflexive.
stepl (inj_Q IR (Qpower_positive q (P_of_succ_nat n)*q)).
apply inj_Q_wd.
simpl.
rewrite Qpower_plus_positive.
reflexivity.
apply inj_Q_mult.
Qed.

Let IRpower_p : PartFunct IR := FId{^}(nat_of_P p).

Lemma Qpower_positive_uc_prf (c:Qpos) :  is_UniformlyContinuousFunction (fun x => Qpower_positive (QboundAbs c x) p) (Qpower_positive_modulus c).
Proof.
intros c.
destruct (p_is_some_anti_convert p) as [n Hn].
assert (X:=(fun I pI => Derivative_nth I pI _ _ (Derivative_id I pI) n)).
assert (-c < c)%Q.
rewrite Qlt_minus_iff.
ring_simplify.
change (0 < ((2#1)*c)%Qpos).
rapply Qpos_prf.
rapply (is_UniformlyContinuousD_Q (Some (-c)) (Some (c:Q)) H _ _ (X _ _) (fun x => Qpower_positive x p)).
 simpl.
 intros q _ Hq.
 csetoid_rewrite (Qpower_positive_correct p q).
 simpl.
 rewrite Hn.
 simpl.
 rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
 apply eq_reflexive.
simpl.
intros x _ Hx.
change (AbsIR ((nring (R:=IR) (S n))[*](One[*]nexp IR n x))[<=]
inj_Q IR (((p # 1)[*]((c ^ Zpred p)%Qpos:Q)))).
stepr ((inj_Q IR ((p # 1))[*](inj_Q IR ((c ^ Zpred p)%Qpos:Q)))) by
(apply eq_symmetric; rapply inj_Q_mult).
stepl ((nring (R:=IR) (S n)[*]AbsIR (One[*]nexp IR n x))) by apply AbsIR_mult;apply nring_nonneg; auto with *.
rapply mult_resp_leEq_both.
   apply nring_nonneg; auto with *.
  apply AbsIR_nonneg.
 stepl (inj_Q IR (nring (S n))) by apply inj_Q_nring.
 apply inj_Q_leEq.
 rewrite Hn.
 unfold pos2Z.
 rewrite <- POS_anti_convert.
 stepl ((S n):Q) by apply eq_symmetric; rapply nring_Q.
 rapply leEq_reflexive.
stepl (One[*](AbsIR (nexp IR n x))) by apply AbsIR_mult; apply less_leEq; apply pos_one.
stepl (AbsIR (nexp IR n x)) by apply eq_symmetric; apply one_mult.
stepl (nexp IR n (AbsIR x)) by apply eq_symmetric; apply AbsIR_nexp.
stepr (inj_Q IR (c ^ Zpred p)) by apply inj_Q_wd; simpl; rewrite Q_Qpos_power; reflexivity.
rewrite Hn.
unfold pos2Z.
rewrite <- POS_anti_convert.
rewrite inj_S.
rewrite <- Zpred_succ.
destruct n.
 change (One[<=]inj_Q IR (nring 1)).
 stepr (nring (R:=IR) 1) by apply eq_symmetric; apply inj_Q_nring.
 stepr (One:IR).
  apply leEq_reflexive.
 simpl; algebra.
rewrite  <- (nat_of_P_o_P_of_succ_nat_eq_succ n).
rewrite convert_is_POS.
simpl.
stepr ((FId{^}(P_of_succ_nat n)) (inj_Q IR (c:Q)) CI) by apply eq_symmetric; apply Qpower_positive_correct.
simpl.
rapply power_resp_leEq.
 apply AbsIR_nonneg.
apply AbsSmall_imp_AbsIR.
destruct Hx; split; try assumption.
stepl (inj_Q IR (-c)).
 assumption.
apply inj_Q_inv.
Qed.

Definition Qpower_positive_uc (c:Qpos) :  Q_as_MetricSpace --> Q_as_MetricSpace :=
Build_UniformlyContinuousFunction (Qpower_positive_uc_prf c).

Definition CRpower_positive_bounded (c:Qpos) : CR --> CR :=
Cmap QPrelengthSpace (Qpower_positive_uc c).

Lemma CRpower_positive_bounded_correct : forall (c:Qpos) x, AbsSmall (inj_Q _ (c:Q)) x -> (IRasCR (x[^](nat_of_P p))==CRpower_positive_bounded c (IRasCR x))%CR.
Proof.
intros c x Hx.
pose (I:=(clcr [--](inj_Q IR (c:Q)) (inj_Q IR (c:Q)))).
assert (Hc: Zero[<]inj_Q IR (c:Q)).
 stepl (inj_Q IR Zero).
  apply inj_Q_less.
  apply Qpos_prf.
 rapply (inj_Q_nring IR 0).
assert (HI:proper I).
 simpl.
 apply shift_zero_less_minus'.
 rstepr (inj_Q IR (c:Q)[+]inj_Q IR (c:Q)).
 apply plus_resp_pos; assumption.
change (x[^]p) with ((FId{^}p) x CI).
destruct Hx as [Hx0 Hx1].
apply (ContinuousCorrect HI (Continuous_nth I FId (Continuous_id I)  (nat_of_P p)));[|split;assumption].
intros q [] Hq.
transitivity (IRasCR (inj_Q IR (Qpower_positive q p))).
 rewrite IR_inj_Q_as_CR.
 simpl.
 change (' q)%CR with (Cunit_fun _ q).
 rewrite MonadLaw3.
 rewrite CReq_Qeq.
 simpl.
 setoid_replace (Qmin c q) with q.
  setoid_replace (Qmax (- c) q) with q.
   reflexivity.
  rewrite <- Qle_max_r.
  apply leEq_inj_Q with IR.
  stepl [--](inj_Q IR (c:Q)) by apply eq_symmetric; apply inj_Q_inv.
  destruct Hq; assumption.
 rewrite <- Qle_min_r.
 apply leEq_inj_Q with IR.
 destruct Hq; assumption.
apply IRasCR_wd.
apply Qpower_positive_correct.
Qed.

Lemma CRpower_positive_bounded_weaken : forall (c1 c2:Qpos) x,
((AbsSmall ('c1) x) -> (c1 <= c2)%Q ->
CRpower_positive_bounded c1 x == CRpower_positive_bounded c2 x)%CR.
Proof.
intros c1 c2 x Hx Hc.
simpl in x.
rewrite <- (CRasIRasCR_id x).
transitivity (IRasCR ((CRasIR x)[^](nat_of_P p))).
 symmetry.
 apply CRpower_positive_bounded_correct.
 rewrite IR_AbsSmall_as_CR.
 stepl ('c1)%CR by simpl; symmetry; apply IR_inj_Q_as_CR.
 stepr x by simpl; symmetry; apply CRasIRasCR_id.
 assumption.
apply CRpower_positive_bounded_correct.
apply AbsSmall_leEq_trans with (inj_Q IR (c1:Q)).
 apply inj_Q_leEq.
 assumption.
rewrite IR_AbsSmall_as_CR.
stepl ('c1)%CR by simpl; symmetry; apply IR_inj_Q_as_CR.
stepr x by simpl; symmetry; apply CRasIRasCR_id.
assumption.
Qed.

Definition CRpower_positive (x:CR) : CR := ucFun (CRpower_positive_bounded (CR_b (1#1) x)) x.

Lemma CRpositive_power_bounded_positive_power : forall (c:Qpos) (x:CR),
((AbsSmall ('c) x) ->
CRpower_positive_bounded c x == CRpower_positive x)%CR.
Proof.
intros c x Hc.
assert (Hx:(AbsSmall ('(CR_b (1#1) x)) x)%CR).
 split; simpl.
  rewrite CRopp_Qopp.
  apply CR_b_lowerBound.
 apply CR_b_upperBound.
unfold CRpower_positive.
generalize (CR_b (1#1) x) Hx.
clear Hx.
intros d Hd.
destruct (Qle_total c d);[|symmetry]; apply CRpower_positive_bounded_weaken; assumption.
Qed.

Lemma CRpower_positive_correct : forall x, (IRasCR (x[^](nat_of_P p))==CRpower_positive (IRasCR x))%CR.
Proof.
intros x.
rapply CRpower_positive_bounded_correct.
rewrite IR_AbsSmall_as_CR.
stepl ('(CR_b (1#1) (IRasCR x)))%CR by simpl; symmetry; apply IR_inj_Q_as_CR.
split; simpl.
 rewrite CRopp_Qopp.
 apply CR_b_lowerBound.
apply CR_b_upperBound.
Qed.

End CRpower_positive.

Add Morphism CRpower_positive with signature ms_eq ==> ms_eq as CRpower_positive_wd.
Proof.
intros p x1 x2 Hx.
transitivity (CRpower_positive_bounded p (CR_b (1 # 1) x1) x2).
 change (ucFun (CRpower_positive_bounded p (CR_b (1#1) x1)) x1==ucFun (CRpower_positive_bounded p (CR_b (1#1) x1)) x2)%CR.
 apply uc_wd; assumption.
apply CRpositive_power_bounded_positive_power.
split; simpl; rewrite <- Hx.
 rewrite CRopp_Qopp.
 apply CR_b_lowerBound.
apply CR_b_upperBound.
Qed.



