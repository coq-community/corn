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
Require Export CRIR.
Require Import CRArith.
Require Import Qpower.
Require Import ModulusDerivative.
Require Import ContinuousCorrect.
Require Import Qmetric.
Require Import CornTac.
Require Import canonical_names.
Require Import additional_operations.

Opaque CR inj_Q.

Open Local Scope Q_scope.
Open Local Scope uc_scope.

(**
** Natural Integer Powers
Positive integer powers is faster than repeated multiplication.

It is uniformly continuous on an interval [[-c,c]].
*)
Section CRpower_N.

Variable n : N.

Definition Qpower_N_modulus (c:Qpos) (e:Qpos) : QposInf :=
  match n with 
  | N0 => QposInfinity
  | Npos p => Qpos2QposInf (e/((p#1)*c^(Zpred p)))
  end.

Lemma Qpower_positive_correct : forall p q, (inj_Q IR (Qpower_positive q p)[=]((FId{^}(nat_of_P p)) (inj_Q IR q) I)).
Proof.
 intros p.
 destruct (p_is_some_anti_convert p) as [m Hm].
 simpl.
 subst.
 intros q.
 induction m.
  simpl.
  algebra.
 rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
 rewrite nat_of_P_o_P_of_succ_nat_eq_succ in IHm.
 change (P_of_succ_nat (S m)) with (Psucc (P_of_succ_nat m)).
 simpl in *.
 rewrite Pplus_one_succ_r.
 stepl (inj_Q IR (Qpower_positive q (P_of_succ_nat m))[*](inj_Q IR q)).
  csetoid_rewrite IHm.
  apply eq_reflexive.
 stepl (inj_Q IR (Qpower_positive q (P_of_succ_nat m)*q)).
  apply inj_Q_wd.
  simpl.
  rewrite -> Qpower_plus_positive.
  reflexivity.
 apply inj_Q_mult.
Qed.

Let IRpower_p : PartFunct IR := FId{^}(nat_of_N n).

Lemma Qpower_N_uc_prf (c:Qpos) : 
  is_UniformlyContinuousFunction (fun x => Qpower (QboundAbs c x) (Z_of_N n)) (Qpower_N_modulus c).
Proof.
 unfold Qpower_N_modulus.
 destruct n as [|p].
  simpl. intros e x y E. now apply ball_refl.
 destruct (p_is_some_anti_convert p) as [m Hm].
 assert (X:=(fun I pI => Derivative_nth I pI _ _ (Derivative_id I pI) m)).
 assert (-c < c)%Q.
  rewrite -> Qlt_minus_iff.
  ring_simplify.
  change (0 < ((2#1)*c)%Qpos).
  apply Qpos_prf.
 apply (fun x => @is_UniformlyContinuousFunction_wd _ _ (fun x : Q_as_MetricSpace => Qpower_positive (QboundAbs c x) p) x (Qscale_modulus ((p#1)*c^(Zpred p))%Qpos)).
   reflexivity.
  intros x.
  generalize ((p # 1) * c ^ Zpred p)%Qpos.
  apply Qpos_positive_numerator_rect.
  intros qn qd.
  simpl.
  autorewrite with QposElim.
  rewrite -> Qmult_comm.
  apply Qle_refl.
 apply (is_UniformlyContinuousD_Q (Some (-c)) (Some (c:Q)) H _ _ (X _ _) (fun x => Qpower_positive x p)).
  simpl.
  intros q _ Hq.
  csetoid_rewrite (Qpower_positive_correct p q).
  simpl.
  rewrite Hm.
  simpl.
  rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
  apply eq_reflexive.
 simpl.
 intros x _ Hx.
 change (AbsIR ((nring (R:=IR) (S m))[*]([1][*]nexp IR m (inj_Q IR x)))[<=]
   inj_Q IR (((p # 1)[*]((c ^ Zpred p)%Qpos:Q)))).
 stepr ((inj_Q IR ((p # 1))[*](inj_Q IR ((c ^ Zpred p)%Qpos:Q)))); [| now
   (apply eq_symmetric; apply inj_Q_mult)].
 stepl ((nring (R:=IR) (S m)[*]AbsIR ([1][*]nexp IR m (inj_Q IR x)))); [| now apply AbsIR_mult;apply nring_nonneg; auto with *].
 apply mult_resp_leEq_both.
    apply nring_nonneg; auto with *.
   apply AbsIR_nonneg.
  stepl (inj_Q IR (nring (S m))); [| now apply inj_Q_nring].
  apply inj_Q_leEq.
  rewrite Hm.
  rewrite <- POS_anti_convert.
  stepl ((S m):Q); [| now apply eq_symmetric; apply nring_Q].
  apply leEq_reflexive.
 stepl ([1][*](AbsIR (nexp IR m (inj_Q IR x)))); [| now apply AbsIR_mult; apply less_leEq; apply pos_one].
 stepl (AbsIR (nexp IR m (inj_Q _ x))); [| now apply eq_symmetric; apply one_mult].
 stepl (nexp IR m (AbsIR (inj_Q _ x))); [| now apply eq_symmetric; apply AbsIR_nexp].
 stepr (inj_Q IR (c ^ Zpred p)); [| now apply inj_Q_wd; reflexivity].
 rewrite Hm.
 rewrite <- POS_anti_convert.
 rewrite inj_S.
 rewrite <- Zpred_succ.
 destruct m.
  change ([1][<=]inj_Q IR (nring 1)).
  stepr (nring (R:=IR) 1); [| now apply eq_symmetric; apply inj_Q_nring].
  stepr ([1]:IR).
   apply leEq_reflexive.
  simpl; algebra.
 rewrite  <- (nat_of_P_o_P_of_succ_nat_eq_succ m).
 rewrite convert_is_POS.
 simpl.
 stepr ((FId{^}(nat_of_P (P_of_succ_nat m))) (inj_Q IR (c:Q)) I); [| now apply eq_symmetric; apply Qpower_positive_correct].
 simpl.
 apply: power_resp_leEq.
  apply AbsIR_nonneg.
 apply AbsSmall_imp_AbsIR.
 destruct Hx; split; try assumption.
 stepl (inj_Q IR (-c)).
  assumption.
 apply inj_Q_inv.
Qed.

Definition Qpower_N_uc (c:Qpos) :  Q_as_MetricSpace --> Q_as_MetricSpace :=
Build_UniformlyContinuousFunction (Qpower_N_uc_prf c).

(** CRpower_positive_bounded works on [[-c,c]]. *)
Definition CRpower_N_bounded (c:Qpos) : CR --> CR :=
Cmap QPrelengthSpace (Qpower_N_uc c).

Lemma CRpower_N_bounded_correct : forall (c:Qpos) x, 
  AbsSmall (inj_Q _ (c:Q)) x -> (IRasCR (x[^](nat_of_N n))==CRpower_N_bounded c (IRasCR x))%CR.
Proof.
 intros c x Hx.
 pose (I:=(clcr [--](inj_Q IR (c:Q)) (inj_Q IR (c:Q)))).
 assert (Hc: [0][<]inj_Q IR (c:Q)).
  stepl (inj_Q IR [0]).
   apply inj_Q_less.
   apply Qpos_prf.
  apply (inj_Q_nring IR 0).
 assert (HI:proper I).
  simpl.
  apply shift_zero_less_minus'.
  rstepr (inj_Q IR (c:Q)[+]inj_Q IR (c:Q)).
  apply plus_resp_pos; assumption.
 rename I into temp.
 change (x[^](nat_of_N n)) with ((FId{^}(nat_of_N n)) x True_constr).
 rename temp into I.
 destruct Hx as [Hx0 Hx1].
 apply (ContinuousCorrect HI (Continuous_nth I FId (Continuous_id I)  (nat_of_N n)));[|split;assumption].
 intros q [] Hq.
 transitivity (IRasCR (inj_Q IR (Qpower q (Z_of_N n)))).
  rewrite -> IR_inj_Q_as_CR.
  simpl.
  change (' q)%CR with (Cunit_fun _ q).
  rewrite -> Cmap_fun_correct.
  rewrite -> MonadLaw3.
  rewrite -> CReq_Qeq.
  simpl.
  setoid_replace (Qmin c q) with q.
   setoid_replace (Qmax (- c) q) with q.
    reflexivity.
   rewrite <- Qle_max_r.
   apply leEq_inj_Q with IR.
   stepl [--](inj_Q IR (c:Q)); [| now apply eq_symmetric; apply inj_Q_inv].
   destruct Hq; assumption.
  rewrite <- Qle_min_r.
  apply leEq_inj_Q with IR.
  destruct Hq; assumption.
 apply IRasCR_wd.
 destruct n.
  simpl. now apply inj_Q_One.
 simpl. now apply Qpower_positive_correct.
Qed.

Lemma CRpower_N_bounded_weaken : forall (c1 c2:Qpos) x,
((AbsSmall ('c1) x) -> (c1 <= c2)%Q ->
CRpower_N_bounded c1 x == CRpower_N_bounded c2 x)%CR.
Proof.
 intros c1 c2 x Hx Hc.
 simpl in x.
 rewrite <- (CRasIRasCR_id x).
 transitivity (IRasCR ((CRasIR x)[^](nat_of_N n))).
  symmetry.
  apply CRpower_N_bounded_correct.
  rewrite -> IR_AbsSmall_as_CR.
  stepl ('c1)%CR; [| now simpl; symmetry; apply IR_inj_Q_as_CR].
  stepr x; [| now simpl; symmetry; apply CRasIRasCR_id].
  assumption.
 apply CRpower_N_bounded_correct.
 apply AbsSmall_leEq_trans with (inj_Q IR (c1:Q)).
  apply inj_Q_leEq.
  assumption.
 rewrite -> IR_AbsSmall_as_CR.
 stepl ('c1)%CR; [| now simpl; symmetry; apply IR_inj_Q_as_CR].
 stepr x; [| now simpl; symmetry; apply CRasIRasCR_id].
 assumption.
Qed.
End CRpower_N.

(** [CRpower_positive_bounded] is should be used when a known bound
on the absolute value of x is available. *)
Instance CRpower_N: Pow CR N := λ x n, ucFun (CRpower_N_bounded n (CR_b (1#1) x)) x.

Lemma CRpower_N_bounded_N_power : forall (n : N) (c:Qpos) (x:CR),
((AbsSmall ('c) x) ->
CRpower_N_bounded n c x == CRpower_N x n)%CR.
Proof.
 intros n c x Hc.
 assert (Hx:(AbsSmall ('(CR_b (1#1) x)) x)%CR).
  split.
   rewrite -> CRopp_Qopp.
   apply CR_b_lowerBound.
  apply CR_b_upperBound.
 unfold CRpower_N.
 generalize (CR_b (1#1) x) Hx.
 clear Hx.
 intros d Hd.
 destruct (Qle_total c d);[|symmetry]; apply CRpower_N_bounded_weaken; assumption.
Qed.

Lemma CRpower_N_correct : forall n x, (IRasCR (x[^](nat_of_N n))==CRpower_N (IRasCR x) n)%CR.
Proof.
 intros n x.
 apply CRpower_N_bounded_correct.
 rewrite -> IR_AbsSmall_as_CR.
 stepl ('(CR_b (1#1) (IRasCR x)))%CR; [| now simpl; symmetry; apply IR_inj_Q_as_CR].
 split.
  rewrite -> CRopp_Qopp.
  apply CR_b_lowerBound.
 apply CR_b_upperBound.
Qed.

Lemma CRpower_N_correct' : forall n x,
(IRasCR (x[^]n)==CRpower_N (IRasCR x) (N_of_nat n))%CR.
Proof.
 intros n x.
 etransitivity; [| apply CRpower_N_correct].
 now rewrite Nnat.nat_of_N_of_nat.
Qed.

Hint Rewrite CRpower_N_correct' : IRtoCR.

Instance: Proper (eq ==> QposEq ==> @st_eq _) Qpower_N_uc.
Proof.
 intros p1 p2 Ep e1 e2 Ee x.
 apply ball_eq_iff. intro e.
 simpl. unfold QposEq in Ee. rewrite Ep, Ee. reflexivity.
Qed.

Instance: Proper (eq ==> QposEq ==> @st_eq _) CRpower_N_bounded. 
Proof. 
 intros p1 p2 Ep e1 e2 Ee x. simpl. rewrite Ep, Ee. reflexivity.
Qed. 

Instance: Proper (@st_eq _ ==> eq ==> @st_eq _) CRpower_N.
Proof.
 intros x1 x2 Hx ? n Hn. subst.
 transitivity (CRpower_N_bounded n (CR_b (1 # 1) x1) x2).
  change (ucFun (CRpower_N_bounded n (CR_b (1#1) x1)) x1==ucFun (CRpower_N_bounded n (CR_b (1#1) x1)) x2)%CR.
  apply uc_wd; assumption.
 apply CRpower_N_bounded_N_power.
 split; rewrite <- Hx.
  rewrite -> CRopp_Qopp.
  apply CR_b_lowerBound.
 apply CR_b_upperBound.
Qed.
(* end hide *)

Instance: NatPowSpec CR N _.
Proof.
  split; unfold pow. 
    apply _.
   intros x. change (cast Q CR 1 = CR1). now apply rings.preserves_1.
  intros x n.
  rewrite <-(CRasIRasCR_id x).
  rewrite <-?CRpower_N_correct.
  rewrite <-IR_mult_as_CR.
  rewrite Nnat.nat_of_Nplus.
  apply IRasCR_wd. symmetry. now apply nexp_Sn.
Qed. 
