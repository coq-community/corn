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

Require Import CSetoids.
Require Import CSemiGroups.
Require Import CMonoids.
Require Import CGroups.
Require Import CornTac.
Require Import CAbGroups.
Require Import CRings.
Require Import CFields.
Require Import COrdFields.
Require Import CReals.
Require Import RIneq.
Require Import Rcomplete.
Require Import Rlimit.
Require Import Rbasic_fun.
Require Import Fourier.

(** * Coq Real Numbers

 Warning: The Coq real numbers depend on classical logic.  Importing this
 module will give you classical logic, the axioms of Coq's real number
 structure, plus all the logical consquences of these axioms.  To avoid
 these consequences, use CoRN's real number structure [IR] instead.

 Here we show that the real numbers from the Coq standard library form
 a real number structure.  This is done in the usual way by building up
 the algebraic heirarchy. *)

(** ** Coq real numbers form a setoid *)

Lemma R_is_CSetoid: is_CSetoid R (@eq R) (fun x y : R => x <> y).
Proof.
 constructor.
    unfold irreflexive.
    intros x H.
    apply H; reflexivity.
   unfold Csymmetric.
   intros x y H.
   auto.
  unfold cotransitive.
  intros x y H z.
  elim (total_order_T x z); intro H1.
   elim H1; intro H2.
    left.
    apply Rlt_not_eq; assumption.
   right.
   rewrite <- H2.
   assumption.
  left.
  apply Rgt_not_eq; assumption.
 unfold tight_apart.
 intros x y.
 constructor.
  intro xy.
  elim (total_order_T x y); intro H1.
   elim H1; clear H1; intro H2.
    elimtype False.
    apply xy.
    apply Rlt_not_eq; assumption.
   assumption.
  elimtype False.
  apply xy.
  apply Rgt_not_eq; assumption.
 intros H H0.
 apply H0; assumption.
Qed.

Definition RCSetoid : CSetoid := Build_CSetoid R (@eq R) (fun x y => x <> y) R_is_CSetoid.
Canonical Structure RCSetoid.
Canonical Structure RSetoid := cs_crr RCSetoid.

(** ** Coq real numbers form a semigroup *)

(** addition *)

Lemma RPlus_is_setoid_bin_fun: bin_fun_strext RCSetoid RCSetoid RCSetoid Rplus.
Proof.
 unfold bin_fun_strext.
 intros x1 x2 y1 y2 H.
 elim (total_order_T x1 x2); intro H1.
  elim H1; clear H1; intro H2.
   left.
   apply: Rlt_not_eq; assumption.
  right.
  intro H0.
  apply H.
  rewrite H2.
  rewrite H0.
  reflexivity.
 left.
 apply: Rgt_not_eq; assumption.
Qed.

Definition RPlus_sbinfun : CSetoid_bin_op RCSetoid := Build_CSetoid_bin_op RCSetoid Rplus RPlus_is_setoid_bin_fun.

Lemma R_is_CSemiGroup : is_CSemiGroup RCSetoid RPlus_sbinfun.
Proof.
 unfold is_CSemiGroup.
 unfold associative.
 intros x y z.
 apply eq_symmetric.
 apply Rplus_assoc.
Qed.

Definition RSemiGroup : CSemiGroup := Build_CSemiGroup RCSetoid RPlus_sbinfun R_is_CSemiGroup.
Canonical Structure RSemiGroup.

(** ** Coq real numbers form a monoid *)

Lemma R_is_CMonoid : is_CMonoid RSemiGroup (0%R).
Proof.
 constructor.
  unfold is_rht_unit.
  intro x.
  apply Rplus_0_r.
 unfold is_lft_unit.
 apply Rplus_0_l.
Qed.

Definition RMonoid : CMonoid := Build_CMonoid _ _ R_is_CMonoid.
Canonical Structure RMonoid.

(** ** Coq real numbers form a group *)

(** negation *)

Lemma RNeg_sunop : fun_strext (S1:=RCSetoid) (S2:=RCSetoid) Ropp.
Proof.
 unfold fun_strext.
 intros x y H H0.
 apply H.
 rewrite H0.
 reflexivity.
Qed.

Definition RNeg_op : CSetoid_un_op RMonoid := Build_CSetoid_un_op RCSetoid Ropp RNeg_sunop.

Lemma R_is_Group : is_CGroup RMonoid RNeg_op.
Proof.
 unfold is_CGroup.
 intro x.
 unfold is_inverse.
 split.
  apply Rplus_opp_r.
 apply Rplus_opp_l.
Qed.

Definition RGroup := Build_CGroup _ _ R_is_Group.
Canonical Structure RGroup.

(** ** Coq real numbers form an abelian group *)

Lemma R_is_AbGroup : is_CAbGroup RGroup.
Proof.
 unfold is_CAbGroup.
 unfold commutes.
 intros x y.
 apply Rplus_comm.
Qed.

Definition RAbGroup := Build_CAbGroup _ R_is_AbGroup.
Canonical Structure RAbGroup.

(** ** Coq real numbers form a ring *)

(** multiplication *)

Lemma RMul_is_csbinop : bin_fun_strext RCSetoid RCSetoid RCSetoid Rmult.
Proof.
 unfold bin_fun_strext.
 intros x1 x2 y1 y2 H.
 elim (total_order_T x1 x2); intro H1.
  elim H1; clear H1; intro H2.
   left.
   apply: Rlt_not_eq; assumption.
  right.
  Focus 2.
 left.
 apply: Rgt_not_eq; assumption.
 intro H0.
 apply H.
 rewrite H0.
 rewrite H2.
 reflexivity.
Qed.

Definition RMul_op : CSetoid_bin_op RMonoid := Build_CSetoid_bin_op RCSetoid Rmult RMul_is_csbinop.

Lemma RMul_assoc : associative (S:=RAbGroup) RMul_op.
Proof.
 unfold associative.
 intros x y z.
 apply eq_symmetric.
 apply Rmult_assoc.
Qed.

Lemma R_is_Ring : is_CRing RAbGroup (1%R) RMul_op.
Proof.
 exists RMul_assoc.
    constructor.
     unfold is_rht_unit; intro x.
     apply Rmult_1_r.
    unfold is_lft_unit; intro x.
    apply Rmult_1_l.
   unfold commutes.
   apply Rmult_comm.
  unfold distributive; intros x y z.
  apply Rmult_plus_distr_l.
 apply R1_neq_R0.
Qed.

Definition RRing := Build_CRing _ _ _ R_is_Ring.
Canonical Structure RRing.

(** ** Coq real numbers form a field *)

(** reciprocal *)

Definition Rrecip : forall x : RRing, x [#] Zero -> RRing := fun x _ => Rinv x.

Lemma R_is_Field : is_CField RRing Rrecip.
Proof.
 constructor.
  apply Rinv_r.
  assumption.
 apply Rinv_l.
 assumption.
Qed.

Lemma R_is_Field2: forall (x y : RRing) (x_ : x[#]Zero) (y_ : y[#]Zero),
   Rrecip x x_[#]Rrecip y y_ -> x[#]y.
Proof.
 intros x y x1 y1 H.
 intro.
 apply H.
 clear H.
 unfold Rrecip.
 rewrite H0.
 trivial.
Qed.

Definition RField : CField := Build_CField _ _ R_is_Field R_is_Field2.
Canonical Structure RField.

(** ** Coq real numbers form an ordered field *)

(** less-than *)

Lemma Rlt_strext : Crel_strext RField Rlt.
Proof.
 unfold Crel_strext.
 intros x1 x2 y1 y2 H.
 elim (total_order_T x2 y2); intro H1.
  elim H1; clear H1; intro H2.
   left; assumption.
  right.
  elim (total_order_T x1 x2); intro H1.
   elim H1; clear H1; intro H3.
    left.
    apply: Rlt_not_eq; assumption.
   right.
   rewrite <- H2.
   rewrite <- H3.
   apply: Rgt_not_eq; assumption.
  left.
  apply: Rgt_not_eq; assumption.
 right.
 elim (total_order_T x1 x2); intro H2.
  elim H2; clear H2; intro H3.
   left; apply: Rlt_not_eq; assumption.
  right.
  apply: Rgt_not_eq.
  apply Rgt_trans with x1.
   assumption.
  rewrite H3; assumption.
 left; apply: Rgt_not_eq; assumption.
Qed.

Definition Rless_rel : CCSetoid_relation RField := Build_CCSetoid_relation RField Rlt Rlt_strext.

(** greater-than *)

Lemma Rgt_strext : Crel_strext RField Rgt.
Proof.
 intros x1 x2 y1 y2.
 pose (G := Rlt_strext y1 y2 x1 x2).
 tauto.
Qed.

Definition Rgt_rel : CCSetoid_relation RField := Build_CCSetoid_relation RField Rgt Rgt_strext.

Lemma R_is_OrdField : is_COrdField RField Rless_rel Rle Rgt_rel Rge.
Proof.
 constructor.
       constructor.
        unfold Ctransitive.
        apply Rlt_trans.
       unfold CSetoids.antisymmetric.
       apply Rlt_asym.
      intros x y xy z.
      apply Rplus_lt_compat_r.
      assumption.
     intros x y x0 y0.
     apply Rmult_gt_0_compat; assumption.
    intros x y.
    constructor.
     intro xy.
     elim (total_order_T x y); intro H2.
      elim H2; clear H2; intro H3.
       left; assumption.
      elimtype False; apply xy; assumption.
     right; assumption.
    intro H; destruct H.
     apply: Rlt_not_eq; assumption.
    apply: Rgt_not_eq; assumption.
   intros x y.
   simpl in *.
   unfold Not; split.
    intros; fourier.
   intro.
   apply Rnot_lt_le.
   assumption.
  auto with *.
 auto with *.
Qed.

Definition ROrdField : COrdField := Build_COrdField _ _ _ _ _ R_is_OrdField.
Canonical Structure ROrdField.

(** ** Coq real numbers form a real number structure *)

Lemma cauchy_prop_cauchy_crit : (CauchySeq ROrdField) ->
  forall s : (nat -> ROrdField), (Cauchy_prop (R:=ROrdField) s) -> (Rseries.Cauchy_crit s).
Proof.
 intros x seq cprop.
 unfold Cauchy_prop in cprop.
 unfold Rseries.Cauchy_crit.
 intros eps epsgt.
 elim (cprop ((eps / 2 / 2)%R) (eps2_Rgt_R0 _ (eps2_Rgt_R0 _ epsgt))).
 intros N NProp.
 exists N.
 intros n m ngt mgt.
 assert (AbsSmall (eps / 2) ((seq n) - (seq m)) )%R.
  stepr ((seq n - seq N) + (seq N - seq m))%R by (simpl; ring).
  stepl (eps / 2 / 2 + eps / 2 / 2)%R by (simpl; field).
  apply AbsSmall_plus.
   apply NProp; assumption.
  apply (AbsSmall_minus).
  apply NProp; assumption.
 destruct H.
 unfold Rfunctions.R_dist.
 apply Rabs_def1.
  clear - H0 epsgt.
  simpl in *.
  fourier.
 clear - H epsgt.
 simpl in *.
 fourier.
Qed.

(** limit *)

Definition RLim : CauchySeq ROrdField -> ROrdField.
Proof.
 intro x.
 elim x.
 intros seq cprop.
 cut (Rseries.Cauchy_crit seq).
  intro crit.
  elim (R_complete seq crit).
  intros lim uncv.
  exact lim.
 apply (cauchy_prop_cauchy_crit x).
 exact cprop.
Defined.

(** INR is isomorphic to nring *)

Lemma R_INR_as_IR : forall n : nat, INR n = nring (R:=RRing) n.
Proof.
 induction n.
  simpl; trivial.
 induction n.
  simpl; auto with *.
 simpl in *.
 rewrite IHn.
 trivial.
Qed.

Hint Rewrite R_INR_as_IR : RtoIR.

Lemma RisReals : is_CReals ROrdField RLim.
Proof.
 constructor.
  intros [s hs].
  unfold SeqLimit.
  unfold RLim.
  intros e e0.
  simpl.
  destruct (R_complete s ((cauchy_prop_cauchy_crit (Build_CauchySeq ROrdField s hs) s hs))).
  unfold Rseries.Un_cv in u.
  simpl in *.
  destruct (hs (e/4)) as [N HN].
   simpl.
   fourier.
  exists N.
  intros m Hm.
  destruct (u (e/2)).
   fourier.
  set (z:=max x0 m).
  rstepr (((s m[-]s N)[+](s N[-]s z))[+](s z[-]x)).
  apply AbsSmall_eps_div_two.
   apply AbsSmall_eps_div_two.
    stepl (e/4).
     apply HN; auto.
    change (e / 4 = e * / (0 + 1 + 1) * / (0 + 1 + 1)).
    field.
   apply AbsSmall_minus.
   stepl (e/4).
    unfold z.
    apply HN; eauto with *.
   change (e / 4 = e * / (0 + 1 + 1) * / (0 + 1 + 1)).
   field.
  assert (Hz:(z >= x0)%nat).
   unfold z; eauto with *.
  destruct (Rabs_def2 _ _ (H _ Hz)) as [A0 A1].
  stepl (e/2).
   split; unfold cg_minus; simpl; auto with *.
  change (e / 2 = e * / (0 + 1 + 1)).
  field.
 intro x.
 exists (Zabs_nat (up x)).
 unfold Zabs_nat.
 elim (archimed x).
 destruct (up x); simpl.
   intros; fourier.
  unfold nat_of_P.
  intros H _.
  apply Rlt_le.
  rewrite <- R_INR_as_IR.
  auto.
 intros I _.
 cut (x < 0%R).
  intro H; clear I.
  rewrite <- R_INR_as_IR.
  cut (0 <= INR (nat_of_P p)).
   intro.
   fourier.
  apply pos_INR.
 cut (0 <= INR (nat_of_P p)).
  intro.
  fourier.
 apply pos_INR.
Qed.

Definition RReals : CReals := Build_CReals ROrdField RLim RisReals.
Canonical Structure RReals.


