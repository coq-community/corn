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

Require Export CoRN.reals.fast.CRArith.
Require Import CoRN.reals.fast.CRIR.
Require Import CoRN.reals.Q_in_CReals.
Require Import CoRN.model.totalorder.QMinMax.
Require Import CoRN.reals.fast.CRarctan_small.
Require Import CoRN.reals.fast.CRpi.
Require Import CoRN.transc.MoreArcTan.
Require Import CoRN.reals.fast.ModulusDerivative.
Require Import CoRN.reals.fast.ContinuousCorrect.
Require Import CoRN.tactics.CornTac.
Require Import CoRN.stdlib_omissions.Q.
Require Import MathClasses.interfaces.abstract_algebra.
Require Import Coq.micromega.Psatz.
Set Implicit Arguments.

Local Open Scope Q_scope.
Local Open Scope uc_scope.

Opaque inj_Q CR.
(**
** Arctangent
Using pi and properties of arctangent, we define arctangent from 1 to
infinity.
*)
Program Definition rational_arctan_big_pos (a:Q) (Ha:1 < a) : CR := 
  (r_pi (1#2) - @rational_arctan_small_pos (/a) _)%CR.
Next Obligation.
 split.
  apply Qinv_le_0_compat; apply Qle_trans with 1; auto with qarith.
 change (/a < /1); apply Q.Qdiv_flip_lt; auto with qarith.
Qed.

Lemma rational_arctan_big_pos_correct_aux (a : Q) :
  0 < a → (r_pi (1 # 2) - IRasCR (ArcTan (inj_Q IR (/ a))))%CR = IRasCR (ArcTan (inj_Q IR a)).
Proof.
 intros Ha.
 rewrite -> r_pi_correct.
 assert (H1:(inj_Q IR a)[#][0]).
  stepr (inj_Q IR [0]); [| now apply (inj_Q_nring IR 0)].
  apply inj_Q_ap.
  apply (Greater_imp_ap _ a 0); assumption.
 rewrite <- IR_minus_as_CR.
 apply IRasCR_wd.
 stepl (Pi[/]TwoNZ[-](ArcTan ([1][/]_[//]H1))).
  assert (H2:[0][<]inj_Q IR a).
   stepl (inj_Q IR [0]); [| now apply (inj_Q_nring IR 0)].
   apply inj_Q_less; assumption.
  unfold cg_minus.
  csetoid_rewrite (ArcTan_recip _ H1 H2).
  rational.
 apply bin_op_wd_unfolded.
  rstepl (((nring 1)[/]TwoNZ)[*]Pi).
  apply mult_wdl.
  change (1#2) with (1/2).
  assert (H2:(inj_Q IR (2#1))[#][0]).
   stepr (inj_Q IR [0]); [| now apply (inj_Q_nring IR 0)].
   apply inj_Q_ap; discriminate.
  apply eq_transitive with ((inj_Q IR 1)[/]_[//]H2).
   apply div_wd.
    apply eq_symmetric; apply (inj_Q_nring IR 1).
   apply eq_symmetric; apply (inj_Q_nring IR 2).
  apply eq_symmetric; apply inj_Q_div.
 apply un_op_wd_unfolded.
 apply ArcTan_wd.
 apply eq_transitive with ((inj_Q IR 1)[/]_[//]H1).
  apply div_wd.
   rstepl (nring 1:IR).
   apply eq_symmetric; apply (inj_Q_nring IR 1).
  apply eq_reflexive.
 eapply eq_transitive.
  apply eq_symmetric; apply inj_Q_div.
 apply inj_Q_wd.
 simpl.
 unfold Qdiv.
 ring.
Qed.

Lemma rational_arctan_big_pos_correct : forall a (Ha: 1 < a),
 (rational_arctan_big_pos Ha == IRasCR (ArcTan (inj_Q IR a)))%CR.
Proof.
 intros a Ha.
 unfold rational_arctan_big_pos.
 rewrite -> rational_arctan_small_pos_correct.
 apply rational_arctan_big_pos_correct_aux.
 now apply Qlt_trans with 1.
Qed.

Lemma rational_arctan_mid_pos_prf a : 0 < a → - (1) < (a - 1) / (a + 1) < 1.
Proof.
split;(try apply Qlt_shift_div_l; try apply Qlt_shift_div_r; psatzl Q).
Qed.

(** Because we have slow convergence near 1, we have another compuation
that works for nonnegative numbers, and is particularly fast near 1. *)
Definition rational_arctan_mid_pos (a:Q) (Ha : 0 < a) : CR :=
 (r_pi (1#4) + (rational_arctan_small (rational_arctan_mid_pos_prf Ha)))%CR.

Lemma rational_arctan_mid_pos_correct_aux (a : Q) : 
  0 < a → (r_pi (1#4) + IRasCR (ArcTan (inj_Q IR ((a - 1) / (a + 1)))))%CR = IRasCR (ArcTan (inj_Q IR a)).
Proof.
 intros Ha.
 rewrite r_pi_correct.
 rewrite <-IR_plus_as_CR.
 apply IRasCR_wd.
 stepl (Pi[/]FourNZ[+]ArcTan (inj_Q IR ((a - 1) / (a + 1)))).
  csetoid_rewrite_rev (ArcTan_one).
  set (y:= (inj_Q IR ((a - 1) / (a + 1)))).
  assert (Y:[0][<][1][-][1][*]y).
   apply shift_zero_less_minus.
   rstepl y.
   rstepr (nring 1:IR).
   stepr (inj_Q IR 1); [| now apply (inj_Q_nring IR 1)].
   apply inj_Q_less.
   now apply rational_arctan_mid_pos_prf.
  apply eq_transitive with (ArcTan ([1][+]y[/]_[//](Greater_imp_ap _ _ _ Y))).
   apply ArcTan_plus_ArcTan.
      apply shift_zero_leEq_minus'.
      rstepr (Two:IR).
      apply nring_nonneg.
     apply leEq_reflexive.
    rstepl ([--](nring 1:IR)).
    stepl (inj_Q IR ([--](1))).
     apply inj_Q_leEq.
     apply less_leEq. now apply rational_arctan_mid_pos_prf.
    csetoid_rewrite_rev (inj_Q_nring IR 1).
    apply inj_Q_inv.
   rstepr (nring 1:IR).
   stepr (inj_Q IR 1); [| now apply (inj_Q_nring IR 1)].
   apply inj_Q_leEq.
   apply less_leEq. now apply rational_arctan_mid_pos_prf.
  apply ArcTan_wd.
  apply mult_cancel_lft with ([1][-][1][*]y).
   apply Greater_imp_ap; assumption.
  rstepl ([1][+]y).
  rstepr (inj_Q IR a[-]y[*]inj_Q IR a).
  csetoid_replace ([1]:IR) (inj_Q IR 1).
   unfold y.
   set (y' := ((a - 1) / (a + 1))).
   unfold cg_minus.
   csetoid_rewrite_rev (inj_Q_mult IR y' a).
   eapply eq_transitive.
    apply eq_symmetric; apply inj_Q_plus.
   apply eq_transitive with (inj_Q IR (a[+][--](y'[*]a)));[| apply inj_Q_minus].
   apply inj_Q_wd.
   simpl.
   unfold y'. 
   field.
   intros E. destruct (Qlt_irrefl 0). transitivity a; auto.
   rewrite <-E, Qlt_minus_iff. now ring_simplify.
  rstepl (nring 1:IR).
  apply eq_symmetric; apply (inj_Q_nring IR 1).
 apply bin_op_wd_unfolded;[|apply eq_reflexive].
 apply mult_cancel_lft with Four.
  apply four_ap_zero.
 rstepl ((nring 1:IR)[*]Pi).
 rstepr ((Four[*]inj_Q IR (1 # 4))[*]Pi).
 apply mult_wdl.
 stepl (inj_Q IR 1); [| now apply (inj_Q_nring IR 1)].
 stepr (inj_Q IR (4*(1#4))).
  apply inj_Q_wd.
  simpl.
  reflexivity.
 eapply eq_transitive.
  apply inj_Q_mult.
 apply mult_wdl.
 apply (inj_Q_nring IR 4).
Qed.

Lemma rational_arctan_mid_pos_correct : forall a (Ha: 0 < a),
 (rational_arctan_mid_pos Ha == IRasCR (ArcTan (inj_Q IR a)))%CR.
Proof.
 intros.
 unfold rational_arctan_mid_pos.
 rewrite rational_arctan_small_correct.
 now apply rational_arctan_mid_pos_correct_aux.
Qed.

(** We glue all of are different methods of computing arctangent into
a nice fast one that works for nonnegative numbers. *)
Definition rational_arctan_pos (a:Q) (Ha:0 <= a) : CR.
Proof.
 revert Ha.
 destruct (Qle_total (2#5) a) as [A|A].
  destruct (Qle_total (5#2) a) as [B|_];  intros _.
   apply (@rational_arctan_big_pos a).
   abstract (eapply Qlt_le_trans;[|apply B];auto with qarith).
  apply (@rational_arctan_mid_pos a).
  abstract (eapply Qlt_le_trans;[|apply A];auto with qarith).
 intros H.
 apply (@rational_arctan_small_pos a).
 abstract ( split;[assumption| eapply Qle_lt_trans;[apply A|auto with qarith]]).
Defined.

Lemma rational_arctan_pos_correct : forall a (Ha: 0 <= a),
 (rational_arctan_pos Ha == IRasCR (ArcTan (inj_Q IR a)))%CR.
Proof.
 intros a Ha.
 unfold rational_arctan_pos.
 destruct (Qle_total (2 # 5) a).
  destruct (Qle_total (5 # 2) a).
   apply rational_arctan_big_pos_correct.
  apply rational_arctan_mid_pos_correct.
 apply rational_arctan_small_pos_correct.
Qed.

(** By symmetry we get arctangent for all numbers. *)
Definition rational_arctan (a:Q) : CR.
Proof.
 destruct (Qle_total a 0) as [H|H].
  refine (-(@rational_arctan_pos (-a)%Q _))%CR.
  abstract ( change (-0 <= -a); apply: (inv_resp_leEq); assumption).
 apply (rational_arctan_pos H).
Defined.

Lemma rational_arctan_correct : forall (a:Q),
 (rational_arctan a == IRasCR (ArcTan (inj_Q IR a)))%CR.
Proof.
 intros a.
 unfold rational_arctan.
 destruct (Qle_total a 0); rewrite -> rational_arctan_pos_correct.
  apply rational_arctan_small_correct_aux.
 reflexivity.
Qed.

Lemma rational_arctan_opp (a : Q) :
  (-rational_arctan (-a) = rational_arctan a)%CR.
Proof.
  do 2 rewrite rational_arctan_correct.
  now apply rational_arctan_small_correct_aux.
Qed.

Lemma rational_arctan_half_pi (a : Q) :
  0 < a → (r_pi (1 # 2) - rational_arctan (/ a) = rational_arctan a)%CR.
Proof.
  intros.
  do 2 rewrite rational_arctan_correct.
  now apply rational_arctan_big_pos_correct_aux.
Qed.

Lemma rational_arctan_fourth_pi (a : Q) :
  0 < a → (r_pi (1 # 4) + rational_arctan ((a - 1) / (a + 1)) = rational_arctan a)%CR.
Proof.
  intros.
  do 2 rewrite rational_arctan_correct.
  now apply rational_arctan_mid_pos_correct_aux.
Qed.

(** Lift arctangent on the rationals to the reals. *)
Lemma arctan_uc_prf : is_UniformlyContinuousFunction rational_arctan Qpos2QposInf.
Proof.
 apply (is_UniformlyContinuousFunction_wd) with rational_arctan (Qscale_modulus (1#1)).
   reflexivity.
  intros x.
  simpl.
  autorewrite with QposElim.
  change (/1) with 1.
  replace RHS with (x:Q) by simpl; ring.
  apply Qle_refl.
 apply (is_UniformlyContinuousD None None I _ _ (Derivative_ArcTan I) rational_arctan).
  intros q [] _.
  apply rational_arctan_correct.
 intros x Hx _.
 assert (X:[0][<][1][+][1][*]x[*]x).
  apply plus_resp_pos_nonneg.
   apply pos_one.
  rstepr (x[^]2).
  apply sqr_nonneg.
 stepr ([1]:IR).
  simpl.
  apply AbsSmall_imp_AbsIR.
  apply leEq_imp_AbsSmall.
   apply shift_leEq_div.
    assumption.
   rstepl ([0]:IR).
   apply less_leEq; apply pos_one.
  apply shift_div_leEq.
   assumption.
  rstepr ([1][+]x[^]2).
  apply shift_leEq_plus'.
  rstepl ([0]:IR).
  apply sqr_nonneg.
 rstepl (nring 1:IR).
 apply eq_symmetric; apply (inj_Q_nring IR 1).
Qed.

Definition arctan_uc : Q_as_MetricSpace --> CR :=
Build_UniformlyContinuousFunction arctan_uc_prf.

Definition arctan : CR --> CR := Cbind QPrelengthSpace arctan_uc.

Lemma arctan_correct : forall x,
 (IRasCR (ArcTan x) == arctan (IRasCR x))%CR.
Proof.
 intros x.
 apply (ContinuousCorrect (I:proper realline)); [apply Continuous_ArcTan | | constructor].
 intros q [] _.
 transitivity (rational_arctan q);[|apply rational_arctan_correct].
 unfold arctan.
 rewrite -> (Cbind_correct QPrelengthSpace arctan_uc (' q))%CR.
 apply: BindLaw1.
Qed.
(* begin hide *)
Hint Rewrite arctan_correct : IRtoCR.
(* end hide *)
Lemma arctan_Qarctan : forall x : Q, (arctan (' x) == rational_arctan x)%CR.
Proof.
 intros x.
 unfold arctan.
 rewrite -> (Cbind_correct QPrelengthSpace arctan_uc (' x))%CR.
 apply: BindLaw1.
Qed.
(* begin hide *)
Hint Rewrite arctan_Qarctan : CRfast_compute.
(* end hide *)

Instance: Proper ((=) ==> (=)) rational_arctan.
Proof.
  intros x1 x2 E.
  rewrite <-2!arctan_Qarctan.
  now rewrite E.
Qed.
