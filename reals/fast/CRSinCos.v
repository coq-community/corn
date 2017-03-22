(** These are lemmas about IR versions of Sin and Cos
    ported to CR *)

Require Import CRcos.
Require Import CRpi.
Require Import CRsin.
Require Import CRIR.
Require Import MathClasses.interfaces.canonical_names.
Require Import MathClasses.interfaces.abstract_algebra.

Lemma sr_mult_associative `{SemiRing R} (x y z : R) : 
    (x * (y * z) = x * y * z).
Proof. apply sg_ass, _. Qed.

Lemma inject_Q_CR_one  : (inject_Q_CR (1#1) [=] 1)%CR.
ring.
Qed.

Lemma inject_Q_CR_two  : (inject_Q_CR (2#1) = 2)%CR.
  rewrite <- inject_Q_CR_one.
  destruct CR_Q_ring_morphism.
  idtac. unfold plus, CRplus. rewrite <- morph_add; eauto.
Qed.

Require Import CRpower.
Require Import  MathClasses.interfaces.additional_operations.
Lemma CRpower_N_asIR:
  ∀ (n: N) (x : CR), 
    CRasIR (x ^ n) = (((CRasIR x) [^] (N.to_nat n))%CR) .
Proof.
  intros ? ?.
  apply (injective IRasCR).
  rewrite CRpower_N_correct.
  rewrite CRasIRasCR_id.
  rewrite CRasIRasCR_id.
  reflexivity.
Qed.

Hint Rewrite CRasIR0 CRasIR_inv CR_mult_asIR 
  CR_plus_asIR CRpower_N_asIR: CRtoIR .


Lemma CREquiv_st_eq: forall a b : CR,
  st_eq (r:=CR) a  b <-> a = b.
Proof.
  reflexivity.
Qed.

Ltac prepareForCRRing := 
  unfold zero, one, CR1, stdlib_rationals.Q_0, mult, cast,
  plus, CRplus,
  canonical_names.negate;
  try apply (proj1 (CREquiv_st_eq _ _)).


Ltac CRRing :=
    prepareForCRRing; ring.

Definition QCRM := CR_Q_ring_morphism.

Lemma CRPiBy2Correct :
  (CRpi * ' (1 # 2))%CR = IRasCR (Pi.Pi [/]TwoNZ).
Proof.
  apply (right_cancellation mult 2).
  match goal with 
  [ |- ?l = _] => remember l as ll
  end.
  rewrite <- IR_One_as_CR.
  unfold plus. unfold CRplus.
  rewrite <- IR_plus_as_CR.
  rewrite <- IR_mult_as_CR.
  subst.
  apply (injective CRasIR).
  rewrite IRasCRasIR_id.
  rewrite one_plus_one.
  rewrite div_1.
  apply (injective IRasCR).
  rewrite CRasIRasCR_id.
  rewrite CRpi_correct.
  fold (mult).
  rewrite <- sr_mult_associative.
  match goal with 
  [ |- ?l = _] => remember l as ll
  end.
  assert (CRpi [=] CRpi * 1)%CR as Hr by ring.
  rewrite Hr.
  subst ll.
  fold (mult).
  simpl. apply sg_op_proper;[reflexivity|].
  rewrite <- inject_Q_CR_two.
  rewrite <- (morph_mul QCRM).
  apply (morph_eq QCRM).
  reflexivity.
Qed.

Lemma CR_Cos_HalfPi : (cos (CRpi * ' (1 # 2)) = 0 )%CR.
Proof.
  pose proof (Pi.Cos_HalfPi) as Hc.
  apply IRasCR_wd in Hc.
  autorewrite with IRtoCR in Hc.
  rewrite <- Hc.
  apply sm_proper.
  apply CRPiBy2Correct.
Qed.

Lemma CRCos_inv : forall x, (cos (-x) = cos x )%CR.
Proof.
  intros. rewrite <- cos_correct_CR, <- cos_correct_CR.
  apply IRasCR_wd.
  rewrite <- SinCos.Cos_inv.
  apply SinCos.Cos_wd.
  
  pose proof (Pi.Cos_HalfPi) as Hc.
  apply IRasCR_wd in Hc.
  autorewrite with IRtoCR in Hc.
  rewrite <-  CRasIR_inv.
  apply CRasIR_wd.
  ring.
Qed.


Lemma CR_Cos_Neg_HalfPi : (cos (CRpi * ' (-1 # 2)) = 0 )%CR.
Proof.
  rewrite <- CRCos_inv.
  rewrite <- CR_Cos_HalfPi.
  apply sm_proper.
  assert  (((-1#2)) = Qopp (1#2)) as Heq by reflexivity.
  rewrite Heq. clear Heq.
  rewrite (morph_opp QCRM).
  generalize (inject_Q_CR(1 # 2)).
  intros.  CRRing. 
Qed.

Lemma CR_Sin_HalfPi : (sin (CRpi * ' (1 # 2)) = 1 )%CR.
Proof.
  pose proof (Pi.Sin_HalfPi) as Hc.
  apply IRasCR_wd in Hc.
  autorewrite with IRtoCR in Hc.
  rewrite <- Hc.
  apply sm_proper.
  apply CRPiBy2Correct.
Qed.

Lemma CRSin_inv : forall x, (sin (-x) = - sin x )%CR.
Proof.
  intros. rewrite <- sin_correct_CR, <- sin_correct_CR.
  rewrite <- IR_opp_as_CR.
  apply IRasCR_wd.
  rewrite <- SinCos.Sin_inv.
  apply SinCos.Sin_wd.
  
  pose proof (Pi.Cos_HalfPi) as Hc.
  apply IRasCR_wd in Hc.
  autorewrite with IRtoCR in Hc.
  rewrite <-  CRasIR_inv.
  apply CRasIR_wd.
  ring.
Qed.



Lemma CRdivideToMul: 
  forall na da dap nb db dbp,
  na*db = nb*da -> na // (da ↾ dap) = nb // (db ↾ dbp).
Proof.
  simpl. intros ? ? ? ? ? ? Heq.
  apply  fields.equal_quotients.
  simpl.
  exact Heq.
Qed.

Definition mkCr0 (a : CR) (ap : (a >< 0)%CR)  : CR ₀.
  exists a. simpl. apply CR_apart_apartT in ap.
  exact ap.
Defined.

Lemma  CRinv_CRinvT : forall
  (a : CR) (ap : (a >< 0)%CR),
  CRinvT a ap = CRinv (mkCr0 a ap).
Proof.
  intros. unfold CRinv.
  simpl. apply CRinvT_wd.
  reflexivity.
Qed.



Lemma CRdivideToMulCRInvT: 
  forall na da dap nb db dbp,
  na*db = nb*da -> na * (CRinvT da  dap) = nb * (CRinvT db  dbp).
Proof.
  intros ? ? ? ? ? ? Heq.
  rewrite CRinv_CRinvT, CRinv_CRinvT.
  apply    fields.equal_quotients.
  simpl.
  exact Heq.
Qed.
Lemma CRpower_N_2 : forall y,
    CRpower_N y (N.of_nat 2) = y * y.
Proof.
  intros y.
  assert ((N.of_nat 2) = (1+(1+0))) as Hs by reflexivity.
  rewrite Hs.
  destruct NatPowSpec_instance_0.
  rewrite nat_pow_S.
  rewrite nat_pow_S.
  rewrite nat_pow_0.
  simpl. prepareForCRRing.
  unfold CR1. CRRing.
Qed.

Require Import CRarctan.
Require Import MoreArcTan.

Lemma sqr_o_cos_o_arctan : forall r p,
    (cos (arctan r)) ^2 = (1 //((1 + r^2) ↾ p)).
Proof.
  intros x p. simpl in p.
  pose proof (CosOfArcTan2 (CRasIR x)) as Hc.
  apply IRasCR_wd in Hc.
  autorewrite with IRtoCR in Hc.
  rewrite CRasIRasCR_id in Hc.
  rewrite Hc. clear Hc.
  rewrite IR_div_as_CR_1.
  simpl. unfold cf_div. unfold f_rcpcl, f_rcpcl'.
  simpl. unfold recip,CRinv. 
  apply CRdivideToMulCRInvT.
  autorewrite with IRtoCR.
  rewrite CRasIRasCR_id.
  simpl. rewrite CRpower_N_2.
  prepareForCRRing.
  simpl. CRRing.
Qed.

Lemma sqr_o_sin_o_arctan : forall r p,
    (sin (arctan r)) ^2 = (r^2 //((1 + r^2) ↾ p)).
Proof.
  intros x p. simpl in p.
  pose proof (SinOfArcTan2 (CRasIR x)) as Hc.
  apply IRasCR_wd in Hc.
  autorewrite with IRtoCR in Hc.
  rewrite CRasIRasCR_id in Hc.
  rewrite Hc. clear Hc.
  rewrite IR_div_as_CR_1.
  simpl. unfold cf_div. unfold f_rcpcl, f_rcpcl'.
  simpl. unfold recip,CRinv. 
  apply CRdivideToMulCRInvT.
  autorewrite with IRtoCR.
  rewrite CRasIRasCR_id.
  simpl. rewrite CRpower_N_2.
  prepareForCRRing.
  simpl.  CRRing.
Qed.

Lemma CRApart_wdl :forall a b c:CR, 
  a = b -> a ≶ c -> b ≶ c.
Proof.
  intros ? ? ? Heq.
  apply strong_setoids.apart_proper; auto.
Qed.


Lemma  OnePlusSqrPos : forall r:CR, (1 + r ^ 2) ≶ 0.
Proof.
  intros.
  symmetry.
  apply orders.lt_iff_le_apart.
  apply semirings.pos_plus_le_lt_compat_l; auto.
  simpl. apply semirings.lt_0_1.
  apply CR_leEq_as_IR.
  autorewrite with CRtoIR.
  apply sqr_nonneg.
Qed.

Definition mkCr0' (a : CR) (ap : (a ≶ 0)%CR)  : CR ₀ :=
   (a ↾ ap).

Lemma sqr_o_cos_o_arctan2 : forall r,
    (cos (arctan r)) ^2 = (1 //(mkCr0' (1 + r^2) (OnePlusSqrPos _))).
Proof.
  intros. apply sqr_o_cos_o_arctan.
Qed.

Lemma sqr_o_sin_o_arctan2 : forall r,
    (sin (arctan r)) ^2 = (r^2 //(mkCr0' (1 + r^2) (OnePlusSqrPos _))).
Proof.
  intros. apply sqr_o_sin_o_arctan.
Qed.

Lemma  CRltT_wdl : ∀ x1 x2 y : CR,
       x1 = x2  → (x1 < y)%CR → (x2 < y)%CR.
Proof.
  intros ? ? ? Heq.
  apply CRltT_wd; auto.
  reflexivity.
Qed.

Lemma  CRltT_wdr : ∀ x1 x2 y : CR,
       x1 = x2  → (y < x1)%CR → (y < x2)%CR.
Proof.
  intros ? ? ? Heq.
  apply CRltT_wd; auto.
  reflexivity.
Qed.

Class RealNumberPi (R : Type) := π : R.
Instance CRpi_RealNumberPi_instance : RealNumberPi CR := CRpi.

Class HalfNum (R : Type) := half_num : R.
Notation "½" := half_num.
Instance Q_Half_instance : HalfNum Q := (1#2)%Q.
Instance CR_Half_instance : HalfNum CR := (inject_Q_CR (1#2)%Q).

Close Scope Q_scope.

Lemma CRCos_plus_Pi: ∀θ , cos (θ + π) = - (cos θ).
  intros θ.
  pose proof (Pi.Cos_plus_Pi (CRasIR θ)) as Hc.
  apply IRasCR_wd in Hc.
  autorewrite with IRtoCR in Hc.
  rewrite CRasIRasCR_id in Hc.
  exact Hc.
Qed.

Lemma CRSin_plus_Pi: ∀ θ : CR, sin (θ + π) = (- sin θ).
  intros x.
  pose proof (Pi.Sin_plus_Pi (CRasIR x)) as Hc.
  apply IRasCR_wd in Hc.
  autorewrite with IRtoCR in Hc.
  rewrite CRasIRasCR_id in Hc.
  exact Hc.
Qed.

Lemma sin_correct_CR : ∀ θ,
  CRasIR (sin θ) = (PowerSeries.Sin (CRasIR θ)).
Proof.
  intros θ. apply (injective IRasCR). rewrite sin_correct.
  rewrite CRasIRasCR_id,CRasIRasCR_id. reflexivity.
Qed.

Lemma cos_correct_CR : ∀ θ,
  CRasIR (cos θ) = (PowerSeries.Cos (CRasIR θ)).
Proof.
  intros θ. apply (injective IRasCR). rewrite cos_correct.
  rewrite CRasIRasCR_id,CRasIRasCR_id. reflexivity.
Qed.

Lemma arctan_correct_CR : ∀ θ,
  CRasIR (arctan θ) = (ArcTan (CRasIR θ)).
Proof.
  intros θ. apply (injective IRasCR). rewrite arctan_correct.
  rewrite CRasIRasCR_id,CRasIRasCR_id. reflexivity.
Qed.


Hint Rewrite sin_correct_CR cos_correct_CR : CRtoIR.

(** One could also divide [π] by 2. However,
    division seems to be annoyingly difficult to deal with.
    For example, rewrite fails with an error about
    inability to handle dependence. Also, one has
    to carry around proofs of positivity *)

Lemma CRPiBy2Correct1 :
  ½ * π = IRasCR (Pi.Pi [/]TwoNZ).
Proof.
  rewrite <- CRPiBy2Correct.
  rewrite rings.mult_comm.
  reflexivity.
Qed.

Lemma MinusCRPiBy2Correct :
  - (½ * π) = IRasCR ([--] (Pi.Pi [/]TwoNZ)).
Proof.
  autorewrite with IRtoCR.
  rewrite <- CRPiBy2Correct.
  rewrite rings.mult_comm.
  reflexivity.
Qed.

Lemma CRCos_nonneg:
  ∀ θ, -(½ * π) ≤ θ ≤ ½ * π
        → 0 ≤ cos θ.
Proof.
  intros ? Hp. destruct Hp as [Hpt Htp].
  pose proof (TrigMon.Cos_nonneg (CRasIR θ)) as Hir.
  apply CR_leEq_as_IR.
  autorewrite with CRtoIR.
  rewrite CRPiBy2Correct1 in Htp.
  apply CR_leEq_as_IR in Htp.
  rewrite IRasCRasIR_id in Htp.
  apply Hir; trivial;[].
  clear Htp Hir.
  apply IR_leEq_as_CR.
  rewrite CRasIRasCR_id.
  rewrite  <- MinusCRPiBy2Correct.
  exact Hpt.
Qed.



Lemma CRarctan_range:
 ∀ r : CR, (-(½ * π) < arctan r < ½ * π).
Proof.
  intros r.
  pose proof (InvTrigonom.ArcTan_range (CRasIR r)) as Hir.
  destruct Hir as [Hirl Hirr].
  eapply less_wdl in Hirr;
    [|symmetry; apply arctan_correct_CR].
  eapply less_wdr in Hirl;
    [| symmetry; apply arctan_correct_CR].
  apply IRasCR_preserves_less in Hirr.
  apply IRasCR_preserves_less in Hirl.
  eapply CRltT_wdr in Hirl;
    [| apply CRasIRasCR_id].
  eapply CRltT_wdl in Hirr;
    [| apply CRasIRasCR_id].
  eapply CRltT_wdr in Hirr;
    [| symmetry; apply CRPiBy2Correct1].
  split; unfold lt; apply CR_lt_ltT; auto;[].
  clear Hirr.
  eapply CRltT_wdl in Hirl;
    [| symmetry; apply MinusCRPiBy2Correct].
  assumption.
Qed.


Lemma CRweakenLt :
  ∀ a t: CR, a < t -> a ≤ t.
Proof.
  intros ? ? Hlt.
  apply orders.full_pseudo_srorder_le_iff_not_lt_flip.
  intros Hc.
  pose proof (conj Hc Hlt) as Hr.
  apply orders.pseudo_order_antisym in Hr.
  assumption.
Qed.

Hint Resolve CRweakenLt : CRBasics.


Lemma CRweakenRange :
  ∀ a t b: CR,
    a < t < b
    -> a ≤ t ≤ b.
Proof.
  intros ? ? ? Hr.
  destruct Hr.
  split; eauto using CRweakenLt.
Qed.

Lemma cos_o_arctan_nonneg: 
  ∀ r : CR,  0 ≤ cos (arctan r).
Proof.
  intros ?.
  apply CRCos_nonneg.
  apply CRweakenRange.
  apply CRarctan_range.
Qed.
