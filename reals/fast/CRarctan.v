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

Require Export CRArith.
Require Import CRIR.
Require Import Q_in_CReals.
Require Import QMinMax.
Require Import CRarctan_small.
Require Import CRpi.
Require Import MoreArcTan.
Require Import ModulusDerivative.
Require Import ContinuousCorrect.
Require Import CornTac.

Set Implicit Arguments.

Open Local Scope Q_scope.
Open Local Scope uc_scope.

Opaque inj_Q CR.
(**
** Arctangent
Using pi and properties of arctangent, we define arctangent from 1 to
infinity.
*)
Definition rational_arctan_big_pos (a:Q) (Ha:1 <= a) : CR.
Proof.
 intros a Ha.
 refine ((r_pi (1#2)) -(@rational_arctan_small_pos (/a) _))%CR.
 split.
  abstract ( apply Qinv_le_0_compat; apply Qle_trans with 1; [discriminate|assumption]).
 abstract ( assert (H:0<a); [apply Qlt_le_trans with 1;[constructor|assumption]|];
   apply: (mult_cancel_leEq _ (/a) 1 a);simpl;[assumption|]; (replace RHS with a by ring);
     replace LHS with (1);[assumption|]; field; apply (Greater_imp_ap _ a 0); assumption).
Defined.

Lemma rational_arctan_big_pos_correct : forall a (Ha: 1 <= a), 1 < a ->
 (rational_arctan_big_pos Ha == IRasCR (ArcTan (inj_Q IR a)))%CR.
Proof.
 intros a Ha H.
 unfold rational_arctan_big_pos.
 assert (H0:0<a); [apply Qlt_trans with 1;[constructor|assumption]|].
 rewrite rational_arctan_small_pos_correct.
  rewrite r_pi_correct.
  assert (H1:(inj_Q IR a)[#]Zero).
   stepr (inj_Q IR Zero); [| by apply (inj_Q_nring IR 0)].
   apply inj_Q_ap.
   apply (Greater_imp_ap _ a 0); assumption.
  rewrite <- IR_minus_as_CR.
  apply IRasCR_wd.
  stepl (Pi[/]TwoNZ[-](ArcTan (One[/]_[//]H1))).
   assert (H2:Zero[<]inj_Q IR a).
    stepl (inj_Q IR Zero); [| by apply (inj_Q_nring IR 0)].
    apply inj_Q_less; assumption.
   unfold cg_minus.
   csetoid_rewrite (ArcTan_recip _ H1 H2).
   rational.
  apply bin_op_wd_unfolded.
   rstepl (((nring 1)[/]TwoNZ)[*]Pi).
   apply mult_wdl.
   change (1#2) with (1/2).
   assert (H2:(inj_Q IR (2#1))[#]Zero).
    stepr (inj_Q IR Zero); [| by apply (inj_Q_nring IR 0)].
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
 apply: (mult_cancel_less _ (/a) 1 a);simpl. assumption.
  ring_simplify.
 replace LHS with 1.
  assumption.
 field.
 apply: (Greater_imp_ap _ a 0); assumption.
Qed.

(** Because we have slow convergence near 1, we have another compuation
that works for nonnegative numbers, and is particularly fast near 1. *)
Definition rational_arctan_mid_pos (a:Q) (Ha:0 <= a) : CR.
Proof.
 intros [n d] Ha.
 refine (r_pi (1#4) + (@rational_arctan_small ((n-d)%Z/(n+d)%Z) _))%CR.
 unfold Qle in Ha; simpl in Ha; rewrite -> Zmult_1_r in Ha; assert (H:~(n+d)%Z==0);[ intros H0;
   apply (Zle_not_lt _ _ Ha); unfold Qeq in H0; simpl in H0; rewrite <- H0; apply Zlt_0_minus_lt;
     ring_simplify; auto with *|]; change (-(1) <= ((inject_Z (n-d)%Z)[/]_[//]H) <= 1);
       split; [apply: shift_leEq_div;simpl | apply: shift_div_leEq';simpl];try
         (unfold Qlt; simpl; auto with * ); rewrite Qle_minus_iff;
           try change (0 <= (n + d)%Z * 1  + (- (n - d))%Z); ring_simplify; unfold Qle; simpl;
             ring_simplify; auto with *.
Defined.

Lemma rational_arctan_mid_pos_correct : forall a (Ha: 0 <= a), 0 < a ->
 (rational_arctan_mid_pos Ha == IRasCR (ArcTan (inj_Q IR a)))%CR.
Proof.
 intros [[|n|n] d] Ha H; try solve [elim (Qlt_not_le _ _ H); unfold Qle; auto with *].
 unfold rational_arctan_mid_pos.
 assert (X:(n - d)%Z / (n + d)%Z < 1).
  assert ((n-d) < (n+d))%Z.
   apply Zlt_0_minus_lt.
   ring_simplify.
   auto with *.
  generalize (n - d)%Z H0.
  intros z Hz.
  unfold Qlt.
  simpl.
  ring_simplify.
  auto with *.
 assert (X0:- (1) < (n - d)%Z / (n + d)%Z).
  assert ((d-n) < (n+d))%Z.
   apply Zlt_0_minus_lt.
   ring_simplify.
   auto with *.
  replace (n-d)%Z with (-(d-n))%Z by ring.
  generalize (d - n)%Z H0.
  intros z Hz.
  unfold Qlt.
  simpl.
  change (Zneg (n+d))%Z with (-(n+d))%Z.
  auto with *.
 rewrite rational_arctan_small_correct; try assumption.
 rewrite r_pi_correct.
 rewrite <- IR_plus_as_CR.
 apply IRasCR_wd.
 stepl (Pi[/]FourNZ[+]ArcTan (inj_Q IR ((n - d)%Z / (n + d)%Z))).
  csetoid_rewrite_rev (ArcTan_one).
  set (y:= (inj_Q IR ((n - d)%Z / (n + d)%Z))).
  assert (Y:Zero[<]One[-]One[*]y).
   apply shift_zero_less_minus.
   rstepl y.
   rstepr (nring 1:IR).
   stepr (inj_Q IR 1); [| by apply (inj_Q_nring IR 1)].
   apply inj_Q_less.
   assumption.
  apply eq_transitive with (ArcTan (One[+]y[/]_[//](Greater_imp_ap _ _ _ Y))).
   apply ArcTan_plus_ArcTan.
      apply shift_zero_leEq_minus'.
      rstepr (Two:IR).
      apply nring_nonneg.
     apply leEq_reflexive.
    rstepl ([--](nring 1:IR)).
    stepl (inj_Q IR ([--](1))).
     apply inj_Q_leEq.
     apply less_leEq; assumption.
    csetoid_rewrite_rev (inj_Q_nring IR 1).
    apply inj_Q_inv.
   rstepr (nring 1:IR).
   stepr (inj_Q IR 1); [| by apply (inj_Q_nring IR 1)].
   apply inj_Q_leEq.
   apply less_leEq; assumption.
  apply ArcTan_wd.
  apply mult_cancel_lft with (One[-]One[*]y).
   apply Greater_imp_ap; assumption.
  rstepl (One[+]y).
  rstepr (inj_Q IR (n # d)[-]y[*]inj_Q IR (n # d)).
  csetoid_replace (One:IR) (inj_Q IR 1).
   unfold y.
   set (y' := ((n - d)%Z / (n + d)%Z)).
   unfold cg_minus.
   csetoid_rewrite_rev (inj_Q_mult IR y' (n#d)).
   eapply eq_transitive.
    apply eq_symmetric; apply inj_Q_plus.
   apply eq_transitive with (inj_Q IR ((n # d)[+][--](y'[*](n # d))));[| apply inj_Q_minus].
   apply inj_Q_wd.
   simpl.
   rewrite (Qmake_Qdiv n d).
   unfold y'.
   unfold Zminus.
   repeat rewrite injz_plus.
   change (inject_Z (- d)) with (- (inject_Z d)).
   field.
   split; unfold Qeq; simpl; auto with *.
  rstepl (nring 1:IR).
  apply eq_symmetric; apply (inj_Q_nring IR 1).
 apply bin_op_wd_unfolded;[|apply eq_reflexive].
 apply mult_cancel_lft with Four.
  apply four_ap_zero.
 rstepl ((nring 1:IR)[*]Pi).
 rstepr ((Four[*]inj_Q IR (1 # 4))[*]Pi).
 apply mult_wdl.
 stepl (inj_Q IR 1); [| by apply (inj_Q_nring IR 1)].
 stepr (inj_Q IR (4*(1#4))).
  apply inj_Q_wd.
  simpl.
  ring.
 eapply eq_transitive.
  apply inj_Q_mult.
 apply mult_wdl.
 apply (inj_Q_nring IR 4).
Qed.

(** We glue all of are different methods of computing arctangent into
a nice fast one that works for nonnegative numbers. *)
Definition rational_arctan_pos (a:Q) (Ha:0 <= a) : CR.
Proof.
 intros a.
 destruct (Qle_total (2#5) a) as [A|A].
  destruct (Qle_total (5#2) a) as [B|_];  intros _.
   apply (@rational_arctan_big_pos a).
   abstract (eapply Qle_trans;[|apply B];discriminate).
  apply (@rational_arctan_mid_pos a).
  abstract (eapply Qle_trans;[|apply A];discriminate).
 intros H.
 apply (@rational_arctan_small_pos a).
 abstract ( split;[assumption| abstract (eapply Qle_trans;[apply A|discriminate])]).
Defined.

Lemma rational_arctan_pos_correct : forall a (Ha: 0 <= a),
 (rational_arctan_pos Ha == IRasCR (ArcTan (inj_Q IR a)))%CR.
Proof.
 intros a Ha.
 unfold rational_arctan_pos.
 destruct (Qle_total (2 # 5) a).
  destruct (Qle_total (5 # 2) a).
   apply rational_arctan_big_pos_correct.
   apply Qlt_le_trans with (5#2); [constructor|assumption].
  apply rational_arctan_mid_pos_correct.
  apply Qlt_le_trans with (2#5); [constructor|assumption].
 apply rational_arctan_small_pos_correct.
 apply Qle_lt_trans with (2#5); [assumption|constructor].
Qed.

(** By symmetry we get arctangent for all numbers. *)
Definition rational_arctan (a:Q) : CR.
Proof.
 intros a.
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
 destruct (Qle_total a 0); rewrite rational_arctan_pos_correct; try reflexivity.
 rewrite <- IR_opp_as_CR.
 apply IRasCR_wd.
 csetoid_rewrite_rev (ArcTan_inv (inj_Q IR (-a))).
 apply ArcTan_wd.
 eapply eq_transitive.
  apply eq_symmetric; apply (inj_Q_inv IR (-a)).
 apply inj_Q_wd.
 simpl.
 ring.
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
  replace RHS with (x:Q) by ring.
  apply Qle_refl.
 apply (is_UniformlyContinuousD None None I _ _ (Derivative_ArcTan CI) rational_arctan).
  intros q [] _.
  apply rational_arctan_correct.
 intros x Hx _.
 assert (X:Zero[<]One[+]One[*]x[*]x).
  apply plus_resp_pos_nonneg.
   apply pos_one.
  rstepr (x[^]2).
  apply sqr_nonneg.
 stepr (One:IR).
  simpl.
  apply AbsSmall_imp_AbsIR.
  apply leEq_imp_AbsSmall.
   apply shift_leEq_div.
    assumption.
   rstepl (Zero:IR).
   apply less_leEq; apply pos_one.
  apply shift_div_leEq.
   assumption.
  rstepr (One[+]x[^]2).
  apply shift_leEq_plus'.
  rstepl (Zero:IR).
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
 apply (ContinuousCorrect (CI:proper realline)); [apply Continuous_ArcTan | | constructor].
 intros q [] _.
 transitivity (rational_arctan q);[|apply rational_arctan_correct].
 unfold arctan.
 rewrite (Cbind_correct QPrelengthSpace arctan_uc (' q))%CR.
 apply: BindLaw1.
Qed.
(* begin hide *)
Hint Rewrite arctan_correct : IRtoCR.
(* end hide *)
Lemma arctan_Qarctan : forall x : Q, (arctan (' x) == rational_arctan x)%CR.
Proof.
 intros x.
 unfold arctan.
 rewrite (Cbind_correct QPrelengthSpace arctan_uc (' x))%CR.
 apply: BindLaw1.
Qed.
(* begin hide *)
Hint Rewrite arctan_Qarctan : CRfast_compute.
(* end hide *)
