(* Copyright © 2008-2008
 * Cezary Kaliszyk
 * Russell O'Connor
 *
 * This work is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *)

Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qreals.
Require Import Coq.QArith.QArith_base.
Require Import CoRN.tactics.CornTac.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rcomplete.
Require Import Coq.Reals.Rlimit.
Require Import Coq.Reals.Rbasic_fun.
Require Import CoRN.coq_reals.Rreals.
Require Import CoRN.reals.iso_CReals.
Require Import CoRN.reals.CauchySeq.
Require Import Coq.Reals.Rtrigo_def.
Require Import CoRN.transc.PowerSeries.
Require Import Coq.Logic.ConstructiveEpsilon.
Require Import Coq.Reals.Rlogic.
Require Export Coq.Reals.Reals.
Require Import CoRN.transc.Pi.
Require Import CoRN.transc.MoreArcTan.
Require Import CoRN.logic.PropDecid.
Require Import CoRN.transc.Exponential.
From Coq Require Import Lra.

(* This changed in RLogic and should probably be moved there: *)
Lemma forall_dec : forall P:nat->Prop, (forall n, {P n} + {~ P n}) -> {forall n, P n} + {~forall n, P n}.
intros. 
case (sig_forall_dec _ H) as [[n H1] | H1];intuition.
Qed.

(** * Coq Real Numbers and IR isomorphisms

 Warning: The Coq real numbers depend on classical logic.  Importing this
 module will give you classical logic, the axioms of Coq's real number
 structure, plus all the logical consquences of these axioms.  To avoid
 these consequences, use CoRN's real number structure [IR] instead.

 All real number structures are isomorphic.  This module uses this
 isomorphis to create a rewrite database [RtoIR] for converting many
 problems over [R] into problems over [IR] where constructive methods
 may be employed.
*)

(** ** The isomorphism *)

Lemma RIR_iso : Isomorphism RReals IR.
Proof.
 exact (Canonic_Isomorphism_between_CReals RReals IR).
Qed.

Definition RasIR : R -> IR := iso_map_lft _ _ RIR_iso.
Definition IRasR : IR -> R := iso_map_rht _ _ RIR_iso.

Lemma RasIRasR_id : forall (x:R), (IRasR (RasIR x)=x).
Proof.
 apply (inversity_rht _ _ RIR_iso).
Qed.

Lemma IRasRasIR_id : forall (x:IR), (RasIR (IRasR x)[=]x).
Proof.
 apply (inversity_lft _ _ RIR_iso).
Qed.

(** equality *)

Lemma R_eq_as_IR : forall x y, (x = y -> RasIR x [=] RasIR y).
Proof.
 apply: map_wd_unfolded.
Qed.

(** apartness *)

Lemma R_eq_as_IR_back : forall x y, (RasIR x [=] RasIR y -> x = y).
Proof.
 intros x y H.
 replace x with (IRasR (RasIR x)) by apply RasIRasR_id.
 replace y with (IRasR (RasIR y)) by apply RasIRasR_id.
 apply: map_wd_unfolded; assumption.
Qed.

Lemma R_ap_as_IR : forall x y, (RasIR x [#] RasIR y -> x <> y).
Proof.
 intros x y H.
 replace x with (IRasR (RasIR x)) by apply RasIRasR_id.
 replace y with (IRasR (RasIR y)) by apply RasIRasR_id.
 change (IRasR (RasIR x) [#] IRasR (RasIR y)).
 apply: map_pres_apartness; assumption.
Qed.

Lemma R_ap_as_IR_back : forall x y, (x <> y -> RasIR x [#] RasIR y).
Proof.
 intros x y H.
 apply map_pres_apartness.
 assumption.
Qed.

Lemma IR_ap_as_R : forall x y, (x <> y -> RasIR x [#] RasIR y).
Proof.
 intro.
 apply: map_pres_apartness.
Qed.

(** less-than *)

Lemma R_lt_as_IR : forall x y, (RasIR x [<] RasIR y -> x < y).
Proof.
 intros x y H.
 replace x with (IRasR (RasIR x)) by apply RasIRasR_id.
 replace y with (IRasR (RasIR y)) by apply RasIRasR_id.
 change (IRasR (RasIR x) [<] IRasR (RasIR y)).
 apply: map_pres_less; assumption.
Qed.

Lemma R_lt_as_IR_back : forall x y, (x [<] y -> IRasR x < IRasR y).
Proof.
 intros x y H.
 change (IRasR x [<] IRasR y).
 apply: map_pres_less.
 assumption.
Qed.

Lemma IR_lt_as_R : forall x y, (x < y -> RasIR x [<] RasIR y).
Proof.
 intro.
 apply: map_pres_less.
Qed.

Lemma IR_lt_as_R_back : forall x y, (IRasR x < IRasR y -> x [<] y).
Proof.
 intros.
 stepl (RasIR (IRasR x)); [| now apply IRasRasIR_id].
 stepr (RasIR (IRasR y)); [| now apply IRasRasIR_id].
 apply map_pres_less.
 assumption.
Qed.

(** le *)

Lemma R_le_as_IR : forall x y, (RasIR x [<=] RasIR y -> x <= y).
Proof.
 intros x y H.
 cut (~ (y < x)).
  apply Rnot_lt_le.
 intro xy.
 revert H. rewrite -> leEq_def. intro H. apply H.
 apply IR_lt_as_R.
 assumption.
Qed.

Lemma IR_le_as_R : forall x y, (x <= y -> RasIR x [<=] RasIR y).
Proof.
 intros x y H.
 rewrite -> leEq_def.
 intro xy.
 assert (~ (y < x)).
  apply RIneq.Rle_not_lt; assumption .
 apply H0.
 apply R_lt_as_IR.
 assumption.
Qed.

Lemma IR_le_as_R_back : forall x y, (IRasR x <= IRasR y -> x [<=] y).
Proof.
 intros.
 rewrite -> leEq_def.
 intro xy.
 cut (~ (IRasR y < IRasR x)); intro.
  apply H0.
  apply R_lt_as_IR.
  stepl y; [| now rewrite -> IRasRasIR_id; reflexivity].
  stepr x; [| now rewrite -> IRasRasIR_id; reflexivity].
  assumption .
 apply (RIneq.Rle_not_lt (IRasR y) (IRasR x)).
  assumption.
 assumption.
Qed.

(** zero *)

Lemma R_Zero_as_IR : (RasIR R0 [=] [0]).
Proof.
 apply map_pres_zero_unfolded.
Qed.

Lemma IR_Zero_as_R : (IRasR [0] = 0).
Proof.
 apply: map_pres_zero_unfolded.
Qed.

Hint Rewrite R_Zero_as_IR : RtoIR.

(** one *)

Lemma R_One_as_IR : (RasIR R1 [=] [1]).
Proof.
 apply map_pres_one_unfolded.
Qed.

Hint Rewrite R_One_as_IR : RtoIR.

Lemma IR_One_as_R : (IRasR [1] = R1).
Proof.
 apply: map_pres_one_unfolded.
Qed.

(** addition *)

Lemma R_plus_as_IR : forall x y, (RasIR (x+y) [=] RasIR x [+] RasIR y).
Proof.
 apply: map_pres_plus.
Qed.

Hint Rewrite R_plus_as_IR : RtoIR.

Lemma IR_plus_as_R : forall x y, (IRasR (x[+]y) [=] IRasR x + IRasR y).
Proof.
 apply: map_pres_plus_unfolded.
Qed.

(** negation *)

Lemma R_opp_as_IR : forall x, (RasIR (- x) [=] ([--] (RasIR x))).
Proof.
 apply: map_pres_minus.
Qed.

Hint Rewrite R_opp_as_IR : RtoIR.

(** subtraction *)

Lemma R_minus_as_IR : forall x y, (RasIR (x-y) [=] RasIR x [-] RasIR y).
Proof.
 intros x y.
 unfold cg_minus.
 rewrite <- R_opp_as_IR.
 rewrite <- R_plus_as_IR.
 reflexivity.
Qed.

Hint Rewrite R_minus_as_IR : RtoIR.

(** multiplication *)

Lemma R_mult_as_IR : forall x y, (RasIR (x*y) [=] RasIR x [*] RasIR y).
Proof.
 apply: map_pres_mult.
Qed.
Hint Rewrite R_mult_as_IR : RtoIR.

(** reciprocal *)

Lemma R_recip_as_IR : forall y Hy, (RasIR (1 / y) [=] ([1] [/] RasIR y [//] Hy)).
Proof.
 intros y Hy.
 simpl in Hy.
 assert (y [#] 0)%R.
  apply: R_ap_as_IR.
  stepr ([0]:IR). assumption.
   symmetry.
  apply R_Zero_as_IR.
 change (1/y) with ([1] [/] y [//] X).
 eapply eq_transitive.
  unfold RasIR.
  apply (map_pres_inv_unfolded RReals IR).
 apply div_wd; reflexivity.
Qed.

Hint Rewrite R_recip_as_IR : RtoIR.

(** division *)

Lemma R_div_as_IR : forall x y Hy, (RasIR (x/y) [=] (RasIR x [/] RasIR y [//] Hy)).
Proof.
 intros x y Hy.
 unfold Rdiv.
 rewrite -> R_mult_as_IR.
 rstepr ((RasIR x) [*] ([1] [/]RasIR y[//]Hy)).
 replace (/ y) with (1 / y).
  rewrite <- R_recip_as_IR; reflexivity.
 unfold Rdiv.
 ring.
Qed.

(** absolute value *)

Lemma R_abs_as_IR : forall x, RasIR (Rabs x) [=] AbsIR (RasIR x).
Proof.
 intro x.
 unfold Rabs.
 destruct (Rcase_abs x) as [Hx | Hx].
  cut (RasIR x[<=][0]).
   intro Hxn.
   rewrite -> (AbsIR_eq_inv_x (RasIR x) Hxn).
   autorewrite with RtoIR; reflexivity.
  stepr (RasIR 0); [| now apply R_Zero_as_IR].
  apply less_leEq.
  apply IR_lt_as_R.
  assumption.
 cut ([0] [<=] RasIR x).
  intro Hxn.
  rewrite -> (AbsIR_eq_x _ Hxn).
  reflexivity.
 stepl (RasIR 0); [| now apply R_Zero_as_IR].
 apply IR_le_as_R.
 lra.
Qed.
Hint Rewrite R_abs_as_IR : RtoIR.

(** parital sum *)

Lemma R_sum_as_IR : forall a m,
    RasIR (sum_f_R0 a m) [=] (seq_part_sum (fun i : nat => RasIR (a i)) (S m)).
Proof.
 intros a m.
 induction m.
  simpl.
  rational.
 simpl.
 autorewrite with RtoIR.
 rewrite -> IHm.
 simpl.
 reflexivity.
Qed.

(** infinite sum *)

Lemma R_infsum_as_IR_convergent : forall (y: R) a,
  infinit_sum a y -> convergent (fun i : nat => RasIR (a i)).
Proof.
 unfold infinit_sum.
 unfold convergent.
 intros y a conv.
 assert (cauchy := CV_Cauchy _ (exist _ y conv)).
 clear conv.
 unfold Cauchy_crit in cauchy.
 unfold Cauchy_prop.
 intros e e0.
 pose (new_e0 := R_lt_as_IR_back _ _ e0).
 rewrite -> IR_Zero_as_R in new_e0.
 assert (sig (fun N => forall n m : nat, (n >= N)%nat ->
   (m >= N)%nat -> R_dist (sum_f_R0 a n) (sum_f_R0 a m) < IRasR e )).
  apply constructive_indefinite_description_nat.
   intros N.
   apply forall_dec.
    intros n0.
   apply forall_dec.
   intros n1.
   apply imp_dec.
    unfold ge.
    destruct (le_gt_dec N n0).
     left; auto with *.
    right; auto with *.
   apply imp_dec.
    destruct (le_gt_dec N n1).
     left; auto with *.
    right; auto with *.
   apply Rlt_dec.
  apply cauchy; auto with *.
 destruct H as [N HN].
 exists (S N).
 intros m Hm.
 assert (N <= pred m)%nat by  auto with *.
 assert (HH := HN (pred m) N H (le_refl N)).
 clear - HH Hm.
 destruct m.
  elimtype False.
  auto with *.
 rewrite <- R_sum_as_IR.
 rewrite <- R_sum_as_IR.
 rewrite <- R_minus_as_IR.
 apply AbsIR_imp_AbsSmall.
 stepl (RasIR (Rabs(sum_f_R0 a m - sum_f_R0 a N))); [| now apply R_abs_as_IR].
 apply less_leEq.
 unfold R_dist in HH.
 stepr (RasIR (IRasR e)); [| now apply IRasRasIR_id].
 apply IR_lt_as_R.
 assumption.
Qed.

Lemma R_infsum_as_IR : forall (y: R) a,
  Rfunctions.infinit_sum a y -> forall prf,
  RasIR y [=] series_sum (fun i : nat => RasIR (a i)) prf.
Proof.
 intros y a Hay prf.
 unfold series_sum.
 unfold infinit_sum in *.
 apply Limits_unique.
 unfold Cauchy_Lim_prop2.
 simpl.
 clear prf.
 intros e He.
 assert (sig (fun N => forall n : nat, (n >= N)%nat -> R_dist (sum_f_R0 a n) y < IRasR e )).
  apply constructive_indefinite_description_nat.
   intros N.
   apply forall_dec.
   intros n0.
   apply imp_dec.
    unfold ge.
    destruct (le_gt_dec N n0).
     left; auto with *.
    right; auto with *.
   apply Rlt_dec.
  apply (Hay).
  unfold Rgt.
  apply R_lt_as_IR.
  stepl ([0]:IR); [| now symmetry;apply R_Zero_as_IR].
  stepr (e); [| now symmetry; apply IRasRasIR_id].
  assumption.
 destruct H as [N HN].
 exists (S N).
 intros m Hm.
 assert (N <= pred m)%nat.
  auto with *.
 assert (HH := HN (pred m) H).
 clear - HH Hm.
 destruct m.
  elimtype False.
  auto with *.
 rewrite <- R_sum_as_IR.
 rewrite <- R_minus_as_IR.
 apply AbsIR_imp_AbsSmall.
 unfold R_dist in HH.
 simpl in HH.
 apply less_leEq.
 stepl (RasIR (Rabs(sum_f_R0 a m - y))); [| apply R_abs_as_IR].
 stepr (RasIR (IRasR e)); [| apply IRasRasIR_id].
 apply IR_lt_as_R.
 assumption.
Qed.

Lemma R_infsum_f_as_IR : forall (x y: R) f,
  Rfunctions.infinit_sum (f x) y -> forall prf,
  RasIR y [=] series_sum (fun i : nat => RasIR (f x i)) prf.
Proof.
 intros x y f cprf rprf.
 apply R_infsum_as_IR.
 assumption.
Qed.

(** factorial *)

Lemma R_nring_as_IR : forall i, RasIR (nring i) [=] nring i.
Proof.
 induction i.
  simpl.
  apply R_Zero_as_IR.
 simpl.
 autorewrite with RtoIR.
 rewrite -> IHi.
 reflexivity.
Qed.
Hint Rewrite R_nring_as_IR : RtoIR.

Add Morphism RasIR with signature (@cs_eq _) ==> (@cs_eq _) as R_as_IR_wd.
Proof.
 intros.
 rewrite H.
 reflexivity.
Qed.

(** integers *)

Lemma R_pring_as_IR : forall x, RasIR (pring _ x) [=] pring _ x.
Proof.
 intro x.
 (*rewrite pring_convert.*)
 stepr (nring (R := IR) (nat_of_P x)).
  stepl (RasIR (nring (R := RReals) (nat_of_P x))).
   apply R_nring_as_IR.
  apply R_as_IR_wd.
  symmetry.
  apply (pring_convert RReals x).
 symmetry.
 apply (pring_convert IR x).
Qed.

Lemma R_zring_as_IR : forall x, RasIR (zring x) [=] zring x.
Proof.
 induction x; simpl.
   apply R_Zero_as_IR.
  apply R_pring_as_IR.
 rewrite -> R_opp_as_IR.
 rewrite -> R_pring_as_IR.
 reflexivity.
Qed.

Lemma INR_as_nring : forall x, INR x = nring (R:=RRing) x.
Proof.
 induction x.
  reflexivity.
 simpl nring.
 rewrite <- IHx.
 apply S_INR.
Qed.

Lemma IZR_as_zring : forall x, IZR x = zring (R:=RRing) x.
Proof.
 induction x.
   reflexivity.
  rewrite <- positive_nat_Z, <- INR_IZR_INZ.
  rewrite INR_as_nring.
  (* rewrite pring_convert *)
  symmetry.
  rewrite positive_nat_Z.
  apply (pring_convert RRing p).
 change (IZR (Zneg p)) with (Ropp (IZR (Zpos p))).
 rewrite <- positive_nat_Z, <- INR_IZR_INZ.
 rewrite INR_as_nring.
 apply Ropp_eq_compat.
 symmetry.
 apply (pring_convert RRing p).
Qed.

Lemma R_IZR_as_IR : forall x, RasIR (IZR x) [=] zring x.
Proof.
 induction x.
   apply R_Zero_as_IR.
  rewrite <- positive_nat_Z, <- INR_IZR_INZ.
  rewrite R_INR_as_IR.
  rewrite -> R_nring_as_IR.
  auto with *.
 change (IZR (Zneg p)) with (Ropp (IZR (Zpos p))).
 rewrite <- positive_nat_Z, <- INR_IZR_INZ.
 rewrite -> R_opp_as_IR.
 rewrite R_INR_as_IR.
 rewrite -> R_nring_as_IR.
 simpl zring.
 auto with *.
Qed.

Hint Rewrite R_IZR_as_IR : RtoIR.

(** exponents *)

Lemma R_pow_as_IR : forall x i,
  RasIR (Rpow_def.pow x i)[=] nexp _ i (RasIR x).
Proof.
 intros x i.
 induction i.
  simpl.
  apply R_One_as_IR.
 simpl.
 autorewrite with RtoIR.
 rewrite -> IHi.
 auto with *.
Qed.
Hint Rewrite R_pow_as_IR : RtoIR.

Lemma R_exp_as_IR : forall x, RasIR (exp x) [=] Exp (RasIR x).
Proof.
 unfold exp.
 unfold projT1.
 intro x; case (exist_exp x).
 unfold exp_in.
 intros y rsums.
 rewrite -> ( R_infsum_f_as_IR x y ((fun x i => / INR (fact i) * Rpow_def.pow x i)) rsums
   (R_infsum_as_IR_convergent _ _ rsums) ).
 simpl.
 apply series_sum_wd.
 intro i.
 autorewrite with RtoIR.
 replace (/ nring (fact i)) with (1 / nring (fact i)).
  2: field; apply (nring_fac_ap_zero RReals i).
 cut (Dom (f_rcpcl' IR) (RasIR (nring (R:=RRing) (fact i)))).
  intro Hy.
  rewrite -> (R_recip_as_IR (nring (fact i)) Hy).
  clear.
  rewrite -> (cg_inv_zero IR (RasIR x)).
  apply mult_wdl.
  apply div_wd.
   reflexivity.
  apply (R_nring_as_IR (fact i)).
 simpl.
 stepl (nring (R:=IR) (fact i)).
  apply (nring_fac_ap_zero IR i).
 symmetry.
 apply (R_nring_as_IR).
Qed.

Hint Rewrite R_exp_as_IR : RtoIR.

(** trigonometry *)

Lemma R_cos_as_IR : forall x, RasIR (cos x) [=] Cos (RasIR x).
Proof.
 unfold cos.
 intro x.
 case (exist_cos (Rsqr x)).
 unfold cos_in.
 intros y rsums.
 rewrite -> (R_infsum_f_as_IR x y (fun x i => cos_n i * Rsqr x ^ i) rsums
   (R_infsum_as_IR_convergent _ _ rsums) ).
 simpl.
 unfold series_sum.
 apply Lim_seq_eq_Lim_subseq with (fun n => 2*n)%nat.
   intros; omega.
  intros n; exists (S n); omega.
 induction n.
  reflexivity.
 simpl in *.
 rewrite -> IHn.
 rewrite (plus_comm n (S (n + 0))).
 simpl.
 rstepr ( seq_part_sum (fun n0 : nat =>
   (cos_seq n0[/]nring (R:=IR) (fact n0)[//]nring_fac_ap_zero IR n0)[*]
     nexp IR n0 (RasIR x[-][0])) (n + 0 + n)[+] (
       (cos_seq (n + 0 + n)[/]nring (R:=IR) (fact (n + 0 + n))[//]
         nring_fac_ap_zero IR (n + 0 + n))[*]nexp IR (n + 0 + n) (RasIR x[-][0])[+]
           (cos_seq (S (n + 0 + n))[/]
             nring (R:=IR) (fact (n + 0 + n) + (n + 0 + n) * fact (n + 0 + n))[//]
               nring_fac_ap_zero IR (S (n + 0 + n)))[*]
                 (nexp IR (n + 0 + n) (RasIR x[-][0])[*](RasIR x[-][0]))) ).
 apply bin_op_wd_unfolded.
  rewrite plus_comm.
  reflexivity.
 replace (n + 0 + n)%nat with (n + n)%nat by auto with *.
 unfold Rsqr.
 unfold cos_n.
 simpl.
 unfold cos_seq.
 simpl.
 destruct (even_or_odd_plus (n + n)).
 destruct (even_or_odd_plus (S(n + n))).
 simpl.
 destruct s; [ | elimtype False; auto with *].
 destruct s0; simpl.
  elimtype False; auto with *.
 autorewrite with RtoIR.
 stepr ( (nexp IR x0 [--][1][/]nring (R:=IR) (fact (n + n))[//]
   nring_fac_ap_zero IR (n + n))[*]nexp IR (n + n) (RasIR x[-][0]) ).
  apply bin_op_wd_unfolded.
   replace (n + 0)%nat with n by auto with *.
   assert (Dom (f_rcpcl' IR) (RasIR (nring (R:=RRing) (fact (n + n))))).
    simpl.
    stepr (RasIR 0); [| now apply R_Zero_as_IR].
    apply R_ap_as_IR_back.
    apply (nring_fac_ap_zero RReals (n + n)).
   rewrite -> (R_div_as_IR ((-1)^n) (nring (R := RRing) (fact (n + n))) X).
   apply div_wd.
    autorewrite with RtoIR.
    replace n with x0 by omega.
    reflexivity.
   autorewrite with RtoIR.
   reflexivity.
  clear.
  induction n; simpl.
   reflexivity.
  rewrite -> IHn.
  replace (n + S n)%nat with (S (n + n))%nat by auto with *.
  simpl.
  rstepr ( nexp IR (n + n) (RasIR x[-][0])[*]((RasIR x[-][0])[*](RasIR x[-][0])) ).
  apply bin_op_wd_unfolded.
   reflexivity.
  rational.
 setoid_replace (([0][/]nring (R:=IR) (fact (n + n) + (n + n) * fact (n + n))[//]
   nring_fac_ap_zero IR (S (n + n)))[*] (nexp IR (n + n) (RasIR x[-][0])[*](RasIR x[-][0])))
     with ([0]:IR).
  rational.
 rational.
Qed.

Hint Rewrite R_cos_as_IR : RtoIR.

Lemma R_sin_as_IR : forall x, RasIR (sin x) [=] Sin (RasIR x).
Proof.
 unfold sin.
 intro x.
 case (exist_sin (Rsqr x)).
 unfold sin_in.
 intros y rsums.
 rewrite -> R_mult_as_IR.
 rewrite -> (R_infsum_f_as_IR x y (fun x i => sin_n i * Rsqr x ^ i) rsums
   (R_infsum_as_IR_convergent _ _ rsums) ).
 assert (convergent (fun n : nat => RasIR x[*](fun i : nat => RasIR (sin_n i * Rsqr x ^ i)) n)).
  apply conv_series_mult_scal.
  apply (R_infsum_as_IR_convergent _ _ rsums).
 rewrite <- (series_sum_mult_scal (fun i : nat => RasIR (sin_n i * Rsqr x ^ i))
   (R_infsum_as_IR_convergent _ _ rsums) (RasIR x) X).
 simpl.
 unfold series_sum.
 apply Lim_seq_eq_Lim_subseq with (fun n => 2*n)%nat.
   intros; omega.
  intros n; exists (S n); omega.
 induction n.
  reflexivity.
 simpl in *.
 rewrite -> IHn.
 rewrite (plus_comm n (S (n + 0))).
 simpl.
 replace (n + 0 + n)%nat with (n + n)%nat by auto with *.
 unfold sin_n.
 simpl.
 replace (n + 0)%nat with (n)%nat by auto with *.
 unfold sin_seq at 3.
 unfold sin_seq at 3.
 simpl.
 destruct (even_or_odd_plus (n + n)).
 destruct (even_or_odd_plus (S(n + n))).
 destruct s; [ | elimtype False; auto with *].
 destruct s0; simpl.
  elimtype False; auto with *.
 rstepr ( seq_part_sum (fun n0 : nat =>
   (sin_seq n0[/]nring (R:=IR) (fact n0)[//]nring_fac_ap_zero IR n0)[*]
     nexp IR n0 (RasIR x[-][0])) (n + n)[+](
       ([0][/]nring (R:=IR) (fact (n + n))[//]nring_fac_ap_zero IR (n + n))[*]
         nexp IR (n + n) (RasIR x[-][0])[+]
           (nexp IR x1 [--][1][/]nring (R:=IR) (fact (n + n) + (n + n) * fact (n + n))[//]
             nring_fac_ap_zero IR (S (n + n)))[*]
               (nexp IR (n + n) (RasIR x[-][0])[*](RasIR x[-][0]))) ).
 apply bin_op_wd_unfolded.
  reflexivity.
 setoid_replace (RasIR x [-] [0]) with (RasIR x);[|rational].
 replace x1 with n by omega.
 clear.
 setoid_replace (([0][/]nring (R:=IR) (fact (n + n))[//]nring_fac_ap_zero IR (n + n))[*]
   nexp IR (n + n) (RasIR x)) with ([0]:IR);[|rational].
 rstepr ( RasIR x [*] ( (nexp IR n [--][1][/]nring (R:=IR) (fact (n + n) + (n + n) * fact (n + n))[//]
   nring_fac_ap_zero IR (S (n + n)))[*](nexp IR (n + n) (RasIR x))) ).
 apply bin_op_wd_unfolded.
  reflexivity.
 autorewrite with RtoIR.
 unfold Rsqr.
 apply bin_op_wd_unfolded.
  cut (Dom (f_rcpcl' IR) (RasIR (nring (R:=RRing) (fact (n + n + 1))))).
   intro X.
   rewrite -> (R_div_as_IR ((-1)^n) (nring (R:=RRing) (fact (n + n + 1))) X).
   apply div_wd.
    autorewrite with RtoIR; reflexivity.
   autorewrite with RtoIR.
   apply nring_wd.
   replace (n + n + 1)%nat with (S (n + n)) by omega.
   simpl.
   reflexivity.
  simpl.
  stepr (RasIR 0); [| now apply R_Zero_as_IR].
  apply R_ap_as_IR_back.
  apply (nring_fac_ap_zero RReals (n + n + 1)).
 induction n; simpl.
  reflexivity.
 replace (n + S n)%nat with (S(n + n)) by omega.
 simpl.
 rewrite -> IHn.
 autorewrite with RtoIR.
 rational.
Qed.

Hint Rewrite R_sin_as_IR : RtoIR.

Lemma R_tan_as_IR : forall x dom, RasIR (tan x) [=] Tan (RasIR x) dom.
Proof.
 intros x dom.
 unfold tan.
 cut (Dom (f_rcpcl' IR) (RasIR (cos x))).
  intro Hdiv.
  rewrite -> (R_div_as_IR (sin x) (cos x) Hdiv).
  cut (Dom (f_rcpcl' IR) (Cos (RasIR x))).
   intro ndom.
   stepl (Sin(RasIR x) [/] Cos(RasIR x) [//] ndom).
    unfold Tan.
    unfold Tang.
    apply: div_wd.
     apply: pfwdef.
     reflexivity.
    apply: pfwdef.
    reflexivity.
   apply div_wd.
    symmetry; apply R_sin_as_IR.
   symmetry; apply R_cos_as_IR.
  unfold pfdom,f_rcpcl' in *.
  stepl (RasIR (cos x)); [| now apply R_cos_as_IR].
  assumption.
 unfold pfdom,f_rcpcl', Tang,Fdiv in *.
 destruct dom.
 destruct e.
 stepl (Cos (RasIR x)); [| now symmetry; apply R_cos_as_IR].
 apply: c.
Qed.

(** logarithm *)

Lemma R_ln_as_IR : forall x prf, RasIR (ln x) [=] Log (RasIR x) prf.
Proof.
 intros x prf.
 apply Exp_cancel.
 rewrite -> Exp_Log.
 rewrite <- R_exp_as_IR.
 apply R_as_IR_wd.
 apply exp_ln.
 apply R_lt_as_IR.
 stepl ([0]:IR); [| now symmetry; apply R_Zero_as_IR].
 assumption.
Qed.

(** pi *)

Lemma R_pi_as_IR : RasIR (PI) [=] Pi.
Proof.
 assert (Sin (RasIR PI) [=] [0]).
  rewrite <- R_sin_as_IR.
  rewrite sin_PI.
  apply R_Zero_as_IR.
 assert (Not (forall z : Z, RasIR PI[#]zring (R:=IR) z[*]Pi)).
  unfold Not.
  intro X.
  apply ((eq_imp_not_ap _ _ _ H) (Sin_ap_Zero (RasIR (PI)) X)).
 clear H.
 apply (not_ap_imp_eq).
 intro PiNot.
 elim H0.
 intro z.
 elim z.
   simpl.
   rstepr ([0]:IR).
   stepr (RasIR 0); [| now apply R_Zero_as_IR].
   apply R_ap_as_IR_back.
   apply PI_neq0.
  intro p.
  rewrite <- convert_is_POS.
  stepr (nring (R := IR) (nat_of_P p) [*] Pi); [| now apply mult_wdl; symmetry; apply (zring_plus_nat IR)].
  case (nat_of_P p).
   simpl.
   rstepr ([0]:IR).
   stepr (RasIR 0); [| now apply R_Zero_as_IR].
   apply R_ap_as_IR_back.
   apply PI_neq0.
  intro n.
  case n.
   simpl.
   rstepr (Pi).
   assumption.
  intro n0.
  apply less_imp_ap.
  apply leEq_less_trans with Four.
   rstepr (([1] [+] [1]) [*] ([1] [+] [1]):IR).
   rewrite <- R_One_as_IR.
   rewrite <- R_plus_as_IR.
   rewrite <- R_mult_as_IR.
   apply IR_le_as_R.
   apply PI_4.
  apply less_leEq_trans with (Two [*] Pi).
   rstepl (Two [*] Two:IR).
   apply mult_resp_less_lft.
    apply Pi_gt_2.
   rstepr (([0] [+] [1]) [+] [1] : IR).
   apply plus_one_ext_less.
   apply zero_lt_posplus1.
   apply eq_imp_leEq.
   reflexivity.
  apply mult_resp_leEq_rht.
   simpl.
   apply (plus_resp_leEq).
   apply (plus_resp_leEq).
   stepl (nring (R := IR) 0); [| now auto with *].
   apply nring_leEq; auto with *.
  apply less_leEq.
  apply pos_Pi.
 intro p.
 apply Greater_imp_ap.
 simpl.
 apply leEq_less_trans with ([0]:IR).
  rewrite -> pring_convert.
  apply less_leEq.
  apply inv_cancel_less.
  rstepl ([0][*][0]:IR).
  rstepr ((nring (R:=IR) (nat_of_P p))[*]Pi).
  apply mult_resp_less_both.
     apply eq_imp_leEq.
     reflexivity.
    rstepl (nring (R := IR) 0) .
    apply nring_less.
    auto with *.
   apply eq_imp_leEq.
   reflexivity.
  auto with *.
 stepl (RasIR 0); [| now apply R_Zero_as_IR].
 apply IR_lt_as_R.
 apply PI_RGT_0.
Qed.

Lemma R_pi_alt_as_IR : RasIR (Alt_PI) [=] pi.
Proof.
 unfold Alt_PI.
 unfold pi.
 destruct (exist_PI) as [x prf].
 unfold pi_series.
 unfold tg_alt in prf.
 unfold PI_tg in prf.
 rewrite -> R_mult_as_IR.
 apply mult_wd.
  change 4%R with ((1 + 1) * (1 + 1))%R.
  rewrite -> R_mult_as_IR.
  rewrite -> R_plus_as_IR.
  rewrite -> R_One_as_IR.
  rational.
 rewrite -> (R_infsum_as_IR x ( (fun i : nat => (-1) ^ i * / INR (2 * i + 1))
   ) prf (R_infsum_as_IR_convergent _ _ prf) ).
 apply series_sum_wd.
 intro n.
 autorewrite with RtoIR.
 apply mult_wd.
  simpl; reflexivity.
 stepr (RasIR (1 / nring (R:=RRing) (2 * n + 1))).
  apply R_as_IR_wd.
  unfold Rdiv.
  simpl; auto with *.
 cut (n + (n + 0) + 1 = S (n + n))%nat.
  intro DF.
  cut (Dom (f_rcpcl' IR) (RasIR (nring (R:=RReals) (2 * n + 1)))).
   intro H.
   rewrite -> (R_recip_as_IR (nring (R:=RReals) (2 * n + 1)) H).
   apply div_wd.
    reflexivity.
   rewrite -> R_nring_as_IR.
   apply nring_wd.
   rewrite <- DF.
   simpl.
   auto.
  simpl.
  stepr (RasIR 0); [| now apply R_Zero_as_IR].
  apply R_ap_as_IR_back.
  apply Rgt_not_eq.
  rewrite DF.
  unfold Rgt.
  change ([0] [<] nring (R:=RRing) (S (n + n))).
  apply pos_nring_S.
 auto with *.
Qed.

Hint Rewrite R_pi_as_IR : RtoIR.

(** rationals *)

Lemma R_Q2R_as_IR : forall q, RasIR (Q2R q) [=] inj_Q IR q.
Proof.
 intro q.
 destruct q.
 unfold Q2R.
 cut (Dom (f_rcpcl' IR) (RasIR (nring (R:=RRing) (nat_of_P Qden)))).
  intro Hy.
  stepr (RasIR (zring (R:=RRing) Qnum)[/]RasIR (nring (R:=RRing) (nat_of_P Qden))[//]Hy).
   stepl (RasIR (zring (R:=RRing) Qnum / nring (R:=RRing) (nat_of_P Qden))).
    apply (R_div_as_IR (zring Qnum) (nring (nat_of_P Qden))).
   apply R_as_IR_wd.
   unfold Rdiv.
   replace (nring (R:=RRing) (nat_of_P Qden)) with (INR (nat_of_P Qden)).
    replace (zring (R:=RRing) Qnum) with (IZR Qnum).
     now rewrite <- positive_nat_Z, INR_IZR_INZ.
    apply IZR_as_zring.
   apply INR_as_nring.
  apply div_wd.
   apply R_zring_as_IR.
  apply R_nring_as_IR.
 simpl.
 stepr (RasIR 0); [| now apply R_Zero_as_IR].
 apply IR_ap_as_R.
 apply Rgt_not_eq.
 unfold Rgt.
 replace 0%R with (nring (R:=RRing) 0).
  change ((nring (R:=RRing) 0 [<] nring (R:=RRing) (nat_of_P Qden))).
  apply nring_less.
  auto with *.
 auto with *.
Qed.

Hint Rewrite R_Q2R_as_IR : RtoIR.
