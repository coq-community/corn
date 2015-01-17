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
Require Import CRsin.
Require Import CRpi.
Require Import CRIR.
Require Import Compress.
Require Import Qpower.
Require Import Qordfield.
Require Import Qround.
Require Import Pi.
Require Import ModulusDerivative.
Require Import ContinuousCorrect.
Require Import Qmetric.
Require Import SinCos.
Require Import CornTac.
Require Import abstract_algebra.

Opaque inj_Q CR Qmin Qmax.

Open Local Scope Q_scope.
Open Local Scope uc_scope.

(**
** Cosine
Cosine is defined in terms of Sine.  [cos x = 1 - 2*(sin(x/2))^2].
But cosine is still first defined on the rational numbers, and lifted
to the real numbers. *)

Section Cos_Poly.

Definition cos_poly_fun (x:Q) :Q := 1 - (2#1) * x * x.

Global Instance: Proper ((=) ==> (=)) cos_poly_fun.
Proof. unfold cos_poly_fun. solve_proper. Qed.

Lemma cos_poly_fun_correct : forall (q:Q),
 inj_Q IR (cos_poly_fun q)[=][1][-]Two[*](inj_Q IR q[^]2).
Proof.
 intros q.
 unfold cos_poly_fun.
 stepr (inj_Q IR ([1][-]Two*q^2)).
  apply inj_Q_wd. 
  unfold cg_minus; simpl; ring.
 stepr (inj_Q IR ([1])[-]inj_Q IR (Two[*]q ^ 2))%Q.
  apply inj_Q_minus.
 apply cg_minus_wd.
  rstepr (nring 1:IR).
  apply (inj_Q_nring IR 1).
 stepr (inj_Q IR Two[*]inj_Q IR (q^2)).
  apply inj_Q_mult.
 apply mult_wd.
  apply (inj_Q_nring IR 2).
 apply (inj_Q_power IR q 2).
Qed.

Definition cos_poly_modulus (e:Qpos) := Qpos2QposInf ((1#4)*e).

Let X:((-(1))<1)%Q.
Proof.
 constructor.
Qed.

Let D : Derivative (clcr (inj_Q IR (-(1))) (inj_Q IR (1:Q))) (inj_Q_less _ _ _ X) ([-C-]([1]:IR){-}(Two:IR){**}FId{^}2)
 ([-C-]([0]:IR){-}(Two:IR){**}((nring 2){**}([-C-][1]{*}FId{^}1))).
Proof.
 apply Derivative_minus.
  apply Derivative_const.
 apply Derivative_scal.
 apply Derivative_nth.
 apply Derivative_id.
Qed.

Lemma cos_poly_prf : is_UniformlyContinuousFunction (fun x => cos_poly_fun (QboundAbs (1#1) x)) cos_poly_modulus.
Proof.
 apply (fun a => is_UniformlyContinuousD_Q (Some (-(1))%Q) (Some (1:Q)) X _ _ D cos_poly_fun a (4#1)).
  simpl; intros q _ _.
  apply cos_poly_fun_correct.
 simpl; intros x' _ [Hx0 Hx1].
 set (x:=(inj_Q IR x')) in *.
 stepr (Four:IR); [| now (apply eq_symmetric; apply (inj_Q_nring IR 4))].
 stepl (ABSIR ([--](Four[*]x))); [| now (apply AbsIR_wd; rational)].
 stepl (ABSIR (Four[*]x)); [| now apply AbsIR_inv].
 rstepr (Four[*][1]:IR).
 apply AbsSmall_imp_AbsIR.
 apply mult_resp_AbsSmall.
  apply nring_nonneg.
 split.
  stepl ([--](pring IR 1)[/][0][+][1][//]den_is_nonzero IR (-1#1)).
   assumption.
  unfold pring; simpl; rational.
 stepr  (pring IR 1[/][0][+][1][//]den_is_nonzero IR 1).
  assumption.
 unfold pring; simpl; rational.
Qed.

Definition cos_poly_uc : Q_as_MetricSpace --> Q_as_MetricSpace :=
Build_UniformlyContinuousFunction cos_poly_prf.

Definition cos_poly : CR --> CR := Cmap QPrelengthSpace cos_poly_uc.

Lemma cos_poly_correct : forall x, AbsSmall (inj_Q IR (1)) x -> (IRasCR ([1][-]Two[*]x[^]2)==cos_poly (IRasCR x))%CR.
Proof.
 intros x Hx.
 assert (Y:Continuous (clcr (inj_Q IR (-(1))) (inj_Q IR (1:Q))) ([-C-]([1]:IR){-}(Two:IR){**}FId{^}2)).
  eapply Derivative_imp_Continuous.
  apply D.
 apply: (ContinuousCorrect (I:=(clcr (inj_Q IR (-(1))) (inj_Q IR (1:Q)))) (inj_Q_less _ _ _ X) Y);
   [|repeat constructor|].
  intros q Hq Hq0.
  transitivity (IRasCR (inj_Q IR (cos_poly_fun q)));[|apply IRasCR_wd; apply cos_poly_fun_correct].
  simpl.
  change (' q)%CR with (Cunit_fun _ q).
  rewrite -> Cmap_fun_correct.
  rewrite -> MonadLaw3.
  rewrite -> IR_inj_Q_as_CR.
  rewrite -> CReq_Qeq.
  simpl.
  unfold cos_poly_fun.
  setoid_replace (Qmax (- (1 # 1)%Qpos) (Qmin (1 # 1)%Qpos q)) with q.
   reflexivity.
  setoid_replace (Qmin (1 # 1)%Qpos q) with q.
   rewrite <- Qle_max_r.
   apply leEq_inj_Q with IR.
   destruct Hq0; assumption.
  rewrite <- Qle_min_r.
  apply leEq_inj_Q with IR.
  destruct Hq0; assumption.
 destruct Hx; split;[stepl [--](inj_Q IR (1:Q)); [| now apply eq_symmetric; apply inj_Q_inv]|];assumption.
Qed.

Lemma Cos_double_angle : forall x, (Cos(Two[*]x)[=][1][-]Two[*]Sin x[^]2).
Proof.
 intros x.
 csetoid_replace (Two[*]x) (x[+]x);[|rational].
 csetoid_rewrite (Cos_plus x x).
 set (sx:=Sin x).
 set (cx:=Cos x).
 rstepl ((cx[^]2)[-](sx[^]2)).
 unfold cg_minus.
 csetoid_replace (cx[^]2) ([1][-]sx[^]2).
  rational.
 apply cg_inv_unique_2.
 rstepl ((cx[^]2[+]sx[^]2)[-][1]).
 apply x_minus_x.
 apply FFT.
Qed.

End Cos_Poly.

Definition rational_cos (x:Q) := cos_poly (rational_sin (x/2)).

Lemma rational_cos_correct_aux a :
  cos_poly (IRasCR (Sin (inj_Q IR (a / 2))))[=]IRasCR (Cos (inj_Q IR a)).
Proof.
 rewrite <- cos_poly_correct.
  apply IRasCR_wd.
  csetoid_rewrite_rev (Cos_double_angle (inj_Q IR (a/2))).
  apply Cos_wd.
  csetoid_replace (Two:IR) (inj_Q IR (2:Q));[|apply eq_symmetric; apply (inj_Q_nring IR 2)].
  stepl (inj_Q IR (2*(a/2))); [| now apply inj_Q_mult].
  apply inj_Q_wd.
  simpl; field; discriminate.
 apply AbsIR_imp_AbsSmall.
 stepr (nring 1:IR); [| now (apply eq_symmetric; apply (inj_Q_nring IR 1))].
 rstepr ([1]:IR).
 apply AbsIR_Sin_leEq_One.
Qed.

(** Cosine is correct. *)
Lemma rational_cos_correct : forall (a:Q),
 (rational_cos a == IRasCR (Cos (inj_Q IR a)))%CR.
Proof.
 intros a.
 unfold rational_cos.
 rewrite -> rational_sin_correct.
 apply rational_cos_correct_aux.
Qed.

Lemma rational_cos_sin a :
  cos_poly (rational_sin (a / 2)) = rational_cos a.
Proof.
 rewrite rational_sin_correct, rational_cos_correct.
 now apply rational_cos_correct_aux.
Qed.

Definition cos_uc_prf : is_UniformlyContinuousFunction rational_cos Qpos2QposInf.
Proof.
 apply (is_UniformlyContinuousFunction_wd) with (fun x => rational_cos x) (Qscale_modulus (1#1)).
   reflexivity.
  intros x.
  simpl.
  autorewrite with QposElim.
  change (/1) with 1.
  replace RHS with (x:Q) by simpl; ring.
  apply Qle_refl.
 apply (is_UniformlyContinuousD None None I _ _ (Derivative_Cos I) rational_cos).
  intros q [] _.
  apply rational_cos_correct.
 intros x [] _.
 stepr ([1]:IR).
  change (AbsIR ([--](Sin x))[<=][1]).
  stepl (AbsIR (Sin x)); [| now apply AbsIR_inv].
  apply AbsIR_Sin_leEq_One.
 rstepl (nring 1:IR).
 apply eq_symmetric.
 apply (inj_Q_nring IR 1).
Qed.

Definition cos_uc : Q_as_MetricSpace --> CR :=
Build_UniformlyContinuousFunction cos_uc_prf.

Definition cos_slow : CR --> CR := Cbind QPrelengthSpace cos_uc.

Lemma cos_slow_correct : forall x,
 (IRasCR (Cos x) == cos_slow (IRasCR x))%CR.
Proof.
 intros x.
 apply: (ContinuousCorrect (I:proper realline)); [apply Continuous_Cos | | constructor].
 intros q [] _.
 transitivity (rational_cos q);[|apply rational_cos_correct].
 unfold cos_slow.
 rewrite -> (Cbind_correct QPrelengthSpace cos_uc (' q))%CR.
 apply: BindLaw1.
Qed.

Definition cos (x:CR) := cos_slow (x - (compress (scale (2*Qceiling (approximate (x*(CRinv_pos (6#1) (scale 2 CRpi))) (1#2)%Qpos -(1#2))) CRpi)))%CR.

Lemma  cos_cos_slow : forall x, cos x = cos_slow x.
Proof.
  intros x.
  unfold cos.
  generalize (Qround.Qceiling (approximate (x * CRinv_pos (6 # 1) (scale 2 CRpi))
   (1 # 2)%Qpos - (1 # 2)))%CR.
  intros z.
  rewrite -> compress_correct.
  rewrite <- (CRasIRasCR_id x).
  rewrite <- CRpi_correct, <- CRmult_scale, <- IR_inj_Q_as_CR, <- IR_mult_as_CR,
   <- IR_minus_as_CR, <- cos_slow_correct, <- cos_slow_correct.
  remember (CRasIR x) as y.
  clear dependent x. rename y into x.
  apply IRasCR_wd.
  rewrite -> inj_Q_mult.
  change (2:Q) with (Two:Q).
  rewrite -> inj_Q_nring.
  symmetry.
  rstepr (Cos (x[+]([--](inj_Q IR z))[*](Two[*]Pi))).
  setoid_replace (inj_Q IR z) with (zring z:IR).
  rewrite <- zring_inv.
  symmetry; apply Cos_periodic_Z.
  rewrite <- inj_Q_zring.
  apply inj_Q_wd.
  symmetry; apply zring_Q.
Qed.

Lemma cos_correct : forall x,
  (IRasCR (Cos x) == cos (IRasCR x))%CR.
Proof.
  intros x.
  rewrite cos_cos_slow.
  apply cos_slow_correct.
Qed.

Instance Setoid_Morphism_cos : Setoid_Morphism cos.
Proof.
  constructor; try apply st_isSetoid.
  intros a b Heq.
  rewrite cos_cos_slow, cos_cos_slow.
  rewrite Heq.
  reflexivity.
Qed.


Lemma cos_correct_CR : forall x,
  (IRasCR (Cos (CRasIR x)) = cos x).
Proof.
  intros x. rewrite cos_correct.
  apply sm_proper.
  apply CRasIRasCR_id.
Qed.

(* begin hide *)
Hint Rewrite cos_correct : IRtoCR.
(* end hide *)
