(* Copyright © 1998-2006
 * Henk Barendregt
 * Luís Cruz-Filipe
 * Herman Geuvers
 * Mariusz Giero
 * Rik van Ginneken
 * Dimitri Hendriks
 * Sébastien Hinderer
 * Bart Kirkels
 * Pierre Letouzey
 * Iris Loeb
 * Lionel Mamane
 * Milad Niqui
 * Russell O’Connor
 * Randy Pollack
 * Nickolay V. Shmyrev
 * Bas Spitters
 * Dan Synek
 * Freek Wiedijk
 * Jan Zwanenburg
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
(*

Formalization of the theorem about extension of real-valued Lipschitz
functions. This theorem originally belongs to McShane and Kirchbraun.

Theorem. Let M - metric space, let X - subset of M. Let f - Lipschitz
function from X to reals with constant C. Then the function defined by

\tilde f (y) = inf_{x \in X} { f(x) + C * d_M (x, y)}

is the extension of f and has the same Lipshitz constant.

The constructive proof also has a restriction on totally boundness of
subset X.

*)

Require Import ContFunctions.
Require Import CMetricSpaces.
Require Import CPMSTheory.

Section LipschitzExtension.

Variable M : CMetricSpace.
Variable P : M -> CProp.
Variable C : IR.
Variable f : CSetoid_fun (SubMetricSpace M P) IR_as_CMetricSpace.

Hypothesis set_bounded : MStotally_bounded (SubMetricSpace M P).
Hypothesis non_empty : {x : M | P x}.
Hypothesis constant_positive : [0][<]C.

Hypothesis f_lip : lipschitz_c f C.

Section BuildExtension.

Definition cdsub' (y : M) : CSetoid_fun (SubMetricSpace M P) IR_as_CMetricSpace.
Proof.
 intros.
 apply Build_CSetoid_fun with (fun x : (SubMetricSpace M P) => C [*] (dsub' M P y x)).
 red. intros x y0 H1.
 elim (bin_op_strext_unfolded _ _ _ _ _ _ H1).
  intros H3.
  elim (ap_irreflexive_unfolded _ _ H3).
 intros H3.
 apply (dsub'_strext M P y); auto.
Defined.

Lemma f_uni_cont: uni_continuous f.
Proof.
 assert (lipschitz' f).
  apply (lip_c_imp_lip (SubMetricSpace M P) IR_as_CMetricSpace f C).
  apply f_lip.
 assert (lipschitz f).
  apply (lipschitz'_imp_lipschitz (SubMetricSpace M P) IR_as_CMetricSpace f); auto.
 apply lipschitz_imp_uni_continuous; auto.
Qed.

Lemma dsub'_is_lipschitz :
forall (y : M) (x1 x2 : SubMetricSpace M P),
C[*]dIR (dsub' M P y x1) (dsub' M P y x2)[<=]C[*](dsub M P x1 x2).
Proof.
 intros.
 apply mult_resp_leEq_lft.
  2: apply less_leEq.
  2: apply constant_positive.
 unfold dsub'. unfold dsub.
 case x1. case x2. intros. simpl.
 astepl (dIR (y[-d]scs_elem0) (y[-d]scs_elem)).
  apply rev_tri_ineq'.
 unfold dIR.
 apply ABSIR_wd.
 assert ((y[-d]scs_elem0)[=](scs_elem0[-d]y)).
  apply ax_d_com.
  apply CPsMetricSpace_is_CPsMetricSpace.
 assert ((y[-d]scs_elem)[=](scs_elem[-d]y)).
  apply ax_d_com.
  apply CPsMetricSpace_is_CPsMetricSpace.
 algebra.
Qed.


Lemma exp_prop : forall (k : nat) (n : nat) (H : Two[#][0]),
Two[^]k[*]nexp IR (n + k) ([1][/] (Two:IR)[//]H)[=]
nexp IR n ([1][/] (Two:IR)[//]H).
Proof.
 intros.
 astepl ((zexp Two H k)[*](nexp IR (n + k) ([1][/] Two[//]H) )).
 astepl ((zexp Two H k)[*](zexp Two H (- (n + k)%nat))).
  astepr (zexp Two H (k + (- (n + k)%nat))).
   apply eq_symmetric.
   apply zexp_plus.
  astepl (zexp Two H (-n)).
   apply (zexp_inv_nexp IR Two H n).
  replace (- n)%Z with (k + - (n + k)%nat)%Z; auto with zarith.
   apply eq_reflexive.
  intros. auto with zarith.
  assert ((n + k)%Z = (n + k)%nat).
   symmetry. apply inj_plus.
   auto with zarith.
 apply mult_wd; auto.
  apply eq_reflexive.
 apply (zexp_inv_nexp IR Two H (n+k)).
Qed.

Lemma cdsub'_uni_cont : forall y : M, uni_continuous (cdsub' y).
Proof.
 intros.
 unfold uni_continuous.
 unfold cdsub'.
 simpl.
 intros.
 elim (power_big C Two). intros k H1.
   3: apply one_less_two.
  2: apply less_leEq; apply constant_positive.
 exists (n + k).
 intros.
 astepl (C[*](dIR (dsub' M P y x) (dsub' M P y y0))).
  cut (C[*]dIR (dsub' M P y x) (dsub' M P y y0)[<=]C[*](dsub M P x y0)).
   intros.
   cut (C[*](dsub M P x y0)[<] nexp IR n ([1][/] Two[//]H)).
    intros.
    apply leEq_less_trans with (C[*](dsub M P x y0)); auto with algebra.
   cut (Two[^]k[*](dsub M P x y0)[<] nexp IR n ([1][/] Two[//]H)).
    intros.
    cut (C[*](dsub M P x y0)[<=]Two[^]k[*](dsub M P x y0)).
     intros.
     apply leEq_less_trans with (Two[^]k[*](dsub M P x y0)); auto with algebra.
    apply mult_resp_leEq_rht; auto.
    apply dsub_nneg.
   astepr (Two[^]k[*](nexp IR (n + k) ([1][/] Two[//]H))).
    apply mult_resp_less_lft; auto.
    apply nexp_resp_pos.
    cut (([1]:IR)[<]Two).
     cut ([0][<]([1]:IR)).
      intros.
      apply less_transitive_unfolded with ([1]:IR); auto.
     apply pos_one.
    apply one_less_two.
   apply exp_prop.
  apply dsub'_is_lipschitz.
 unfold dIR.
 astepr (ABSIR (C[*](dsub' M P y x[-]dsub' M P y y0))).
  apply AbsIR_mult.
  apply less_leEq.
  apply constant_positive.
 apply ABSIR_wd; auto with algebra.
Qed.

Definition f_multi_ext (y : M) : CSetoid_fun (SubMetricSpace M P) IR_as_CMetricSpace.
Proof.
 intros.
 apply Build_CSetoid_fun with (fun x : (SubMetricSpace M P) => f (x) [+] (cdsub' y x)).
 red. intros x y0 H1.
 elim (bin_op_strext_unfolded _ _ _ _ _ _ H1).
  apply (csf_strext (SubMetricSpace M P) IR_as_CMetricSpace f).
 apply (csf_strext (SubMetricSpace M P) IR_as_CMetricSpace (cdsub' y)).
Defined.

Lemma f_multi_ext_uni_continuous :  forall y : M, uni_continuous (A:=SubMetricSpace M P) (B:=IR_as_CPsMetricSpace)
     (f_multi_ext y).
Proof.
 intros.
 unfold f_multi_ext.
 apply (plus_resp_uni_continuous (SubMetricSpace M P) f (cdsub' y) f_uni_cont (cdsub'_uni_cont y)).
Qed.

Lemma inf_f_multi_ext_exists :
forall y : M, {z : IR | set_glb_IR (fun v : IR_as_CMetricSpace => {x : SubMetricSpace M P | f_multi_ext y x[=]v}) z}.
Proof.
 intros.
 elim (infimum_exists (SubMetricSpace M P) (f_multi_ext y)).
    3: apply set_bounded.
   intros x H.
   exists x.
   apply H.
  assert (uni_continuous (f_multi_ext y)).
   apply f_multi_ext_uni_continuous.
  assert (uni_continuous' (f_multi_ext y)).
   apply uni_continuous_imp_uni_continuous'; auto.
  apply uni_continuous'_imp_uni_continuous''; auto.
 elim non_empty.
 intros x H.
 exists x. apply H.
Qed.

Definition lip_extension_f (y : M) : IR.
Proof.
 intros.
 assert ({z : IR | set_glb_IR (fun v : IR_as_CMetricSpace => {x : SubMetricSpace M P | f_multi_ext y x[=]v}) z}).
  apply inf_f_multi_ext_exists.
 destruct X.
 exact x.
Defined.

Lemma lip_extension_strext_case: forall (x : M) (y : M)
  (z1 : IR)  (z2 : IR)  (H : z1[<]z2)
  (H1 : set_glb_IR
         (fun v : IR =>
          sigT (fun x : subcsetoid_crr M P => f x[+]C[*]dsub' M P y x[=]v))
         z1)
  (H2 : set_glb_IR
         (fun v : IR =>
          sigT (fun x0 : subcsetoid_crr M P => f x0[+]C[*]dsub' M P x x0[=]v))
         z2), x [#] y.
Proof.
 unfold set_glb_IR.
 intros.
 destruct H1 as [l s]. destruct H2 as [l0 s0].
 assert {x0 : IR | sigT (fun x1 : subcsetoid_crr M P => f x1[+]C[*]dsub' M P y x1[=]x0) |
   x0[-]z1[<](z2 [-] z1)}.
  apply s.
  apply shift_zero_less_minus; auto.
 destruct X. destruct s1.
 assert (z2[<=]f x1[+]C[*]dsub' M P x x1).
  apply (l0 (f x1[+]C[*]dsub' M P x x1)).
  exists x1.
  algebra.
 assert (x0 [<] z2).
  apply plus_cancel_less with ([--]z1). algebra.
  assert (f x1[+]C[*]dsub' M P y x1 [<] f x1[+]C[*]dsub' M P x x1).
  apply less_leEq_trans with z2; auto.
  astepl (x0). auto.
  assert ((from_SubPsMetricSpace M P x1[-d] y)[#](from_SubPsMetricSpace M P x1[-d]x)).
  apply less_imp_ap.
  apply mult_cancel_less with (z := C).
   apply constant_positive.
  astepl (C[*]dsub' M P y x1).
  astepr (C[*]dsub' M P x x1).
  apply plus_cancel_less with (f x1).
  astepl (f x1[+]C[*]dsub' M P y x1).
  astepr (f x1[+]C[*]dsub' M P x x1).
  auto.
 set (H1 := csbf_strext _ _ _ (cms_d (c:=M)) _ _ _ _ X1).
 elim H1.
  assert (Not (from_SubPsMetricSpace M P x1[#]from_SubPsMetricSpace M P x1)).
   apply ap_irreflexive_unfolded.
  contradiction.
 intros.
 apply ap_symmetric_unfolded.
 auto.
Qed.

Lemma lip_extension_strext :
 fun_strext (lip_extension_f).
Proof.
 unfold fun_strext.
 unfold lip_extension_f.
 intros x y.
 elim inf_f_multi_ext_exists.
 elim inf_f_multi_ext_exists.
 simpl. intros z1 H1 z2 H2 H.
 elim (ap_imp_less IR z1 z2); auto; intros.
   unfold f_multi_ext.
   apply (lip_extension_strext_case x y z1 z2 a H1 H2).
  apply ap_symmetric_unfolded.
  apply (lip_extension_strext_case y x z2 z1 b H2 H1).
 apply ap_symmetric_unfolded. auto.
Qed.

Definition lip_extension :=
  Build_CSetoid_fun M IR_as_CPsMetricSpace (lip_extension_f)
   (lip_extension_strext).

Lemma lip_unfolded : forall (x x1: SubMetricSpace M P),
f x[-]f x1[<=]C[*]dsub' M P (from_SubPsMetricSpace M P x) x1.
Proof.
 intros.
 unfold dsub'.
 astepr (C[*](x[-d]x1)).
  apply leEq_transitive with (AbsIR (f x[-] f x1)).
   apply leEq_AbsIR.
  astepl (f x[-d]f x1).
  assert (lipschitz_c f C).
   apply f_lip.
  apply X.
 apply mult_wd; algebra.
 case x. case x1. intros. simpl.
 apply ax_d_com.
 apply CPsMetricSpace_is_CPsMetricSpace.
Qed.


End BuildExtension.

Section ExtensionProperties.

Lemma lip_extension_keeps_fun : forall (x : SubMetricSpace M P),
lip_extension (from_SubPsMetricSpace M P x) [=] f x.
Proof.
 intros.
 unfold lip_extension.
 simpl.
 unfold lip_extension_f.
 elim inf_f_multi_ext_exists.
 unfold set_glb_IR.
 simpl. intros y H.
 destruct H as [l s].
 apply leEq_imp_eq.
  apply l.
  exists x.
  assert (dsub' M P (from_SubPsMetricSpace M P x) x[=][0]).
   unfold dsub'.
   assert (diag_zero M (cms_d (c:=M))).
    apply pos_imp_ap_imp_diag_zero.
     apply ax_d_pos_imp_ap.
     apply (CPsMetricSpace_is_CPsMetricSpace M).
    apply ax_d_nneg.
    apply (CPsMetricSpace_is_CPsMetricSpace M).
   apply H.
  astepl (f x[+]C[*][0]).
  astepl (f x[+][0]). algebra.
  assert (forall e : IR, [0] [<]e -> f x [-] y [<] e).
  intros.
  assert (sig2T IR (fun x0 : IR => sigT (fun x1 : subcsetoid_crr M P =>
    f x1[+]C[*]dsub' M P (from_SubPsMetricSpace M P x) x1[=]x0)) (fun x : IR => x[-]y[<]e)).
   apply s. auto. destruct X0. destruct s0.
   assert (f x [<=] f x1[+]C[*]dsub' M P (from_SubPsMetricSpace M P x) x1).
   astepr (C[*] dsub' M P (from_SubPsMetricSpace M P x) x1 [+] f x1).
   apply shift_leEq_plus.
   apply lip_unfolded.
  apply leEq_less_trans with (f x1[+]C[*]dsub' M P (from_SubPsMetricSpace M P x) x1[-]y).
   apply minus_resp_leEq; auto.
  astepl (x0 [-] y); auto.
 astepl (f x [-] y [+] y).
 astepr ([0] [+] y).
 apply plus_resp_leEq.
 apply approach_zero; auto.
Qed.

Lemma extension_also_lipschitz_case :
forall (y1 : M) (y2 : M) (fy2 : IR)
(Hfy2 : set_glb_IR (fun v : IR =>
  sigT (fun x : subcsetoid_crr M P => f x[+]C[*]dsub' M P y2 x[=]v)) fy2)
(fy1 : IR)
(Hfy1 : set_glb_IR (fun v : IR =>
 sigT (fun x : subcsetoid_crr M P => f x[+]C[*]dsub' M P y1 x[=]v))  fy1)
(e : IR)
(X : [0][<]e),
fy2[-]fy1[<=]C[*](y1[-d]y2)[+]e.
Proof.
 intros.
 destruct Hfy1. destruct Hfy2  as [l0 s0].
 assert ({x : IR | sigT (fun x0 : SubMetricSpace M P => f x0[+]C[*]dsub' M P y1 x0[=]x) |
   x[-]fy1[<]e}).
  apply s. auto. destruct X0 as [fx1 Ht Hl1].  destruct Ht as [x1 He1].
  assert (fy2 [<=] f x1[+]C[*]dsub' M P y2 x1).
  apply l0; auto. exists x1. apply eq_reflexive_unfolded.
  assert (fx1[-]e[<=]fy1).
  apply less_leEq.
  apply shift_minus_less.
  apply shift_less_plus'; auto.
 (* Inequalites are simple and symmetric*)
 apply leEq_transitive with ((f x1[+]C[*]dsub' M P y2 x1)[-](fx1[-]e)).
  apply minus_resp_leEq_both; auto.
 astepl (f x1[+]C[*]dsub' M P y2 x1[-]fx1[+]e).
 apply plus_resp_leEq.
 astepl (f x1[+]C[*]dsub' M P y2 x1[-](f x1[+]C[*]dsub' M P y1 x1)).
 astepl (f x1[+]C[*]dsub' M P y2 x1[-]f x1[-]C[*]dsub' M P y1 x1).
 astepl (f x1[-]f x1[+]C[*]dsub' M P y2 x1[-]C[*]dsub' M P y1 x1).
  astepl ([0][+]C[*]dsub' M P y2 x1[-]C[*]dsub' M P y1 x1).
  astepl (C[*]dsub' M P y2 x1[-]C[*]dsub' M P y1 x1).
  astepl (C[*](dsub' M P y2 x1[-]dsub' M P y1 x1)).
  apply mult_resp_leEq_lft.
   2: apply less_leEq.
   2: apply constant_positive.
  unfold dsub'.
  astepr (y2[-d]y1).
   apply leEq_transitive with (AbsIR ((from_SubPsMetricSpace M P x1[-d]y2)[-]
     (from_SubPsMetricSpace M P x1[-d]y1))).
    apply leEq_AbsIR.
   apply AbsSmall_imp_AbsIR.
   apply rev_tri_ineq.
  apply ax_d_com.
  apply CPsMetricSpace_is_CPsMetricSpace.
 rational.
Qed.

Lemma extension_also_liscphitz : lipschitz_c (lip_extension) C.
Proof.
 unfold lipschitz_c.
 unfold lip_extension.
 unfold lip_extension_f.
 intros y1 y2. intros. simpl.
 elim inf_f_multi_ext_exists.
 elim inf_f_multi_ext_exists.
 unfold f_multi_ext.
 unfold dIR.
 simpl.
 intros fy2 Hfy2 fy1 Hfy1.
 apply AbsSmall_imp_AbsIR.
 assert (forall e : IR, [0][<]e -> AbsSmall (C[*](y1[-d]y2)[+]e) (fy1[-]fy2)).
  intros.
  unfold AbsSmall. split.
  astepr ([--](fy2 [-] fy1)).
    apply inv_resp_leEq.
    apply extension_also_lipschitz_case; auto.
   rational.
  astepr (C[*](y2[-d]y1)[+]e).
   astepl (fy1 [-] fy2).
   apply (extension_also_lipschitz_case y2 y1 fy1 Hfy1 fy2 Hfy2 e X).
  assert (y2[-d]y1[=]y1[-d]y2).
   apply ax_d_com.
   apply CPsMetricSpace_is_CPsMetricSpace.
  algebra.
 apply AbsSmall_approach. auto.
Qed.

End ExtensionProperties.

End LipschitzExtension.
