(*
Copyright © 2006 Russell O’Connor

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
Require Import CRIR.
Require Import Qpower.
Require Import Qordfield.
Require Import ModulusDerivative.
Require Import ContinuousCorrect.
Require Import Qmetric.
Require Import SinCos.
Require Import CornTac.

Opaque inj_Q CR Qmin Qmax.

Open Local Scope Q_scope.
Open Local Scope uc_scope.

Section Cos_Poly.

Definition cos_poly_fun (x:Q) :Q := 1-2*x*x.

Lemma cos_poly_fun_correct : forall (q:Q),
 inj_Q IR (cos_poly_fun q)[=]One[-]Two[*](inj_Q IR q[^]2).
Proof.
intros q.
unfold cos_poly_fun.
stepr (inj_Q IR (One[-]Two*q^2)).
 apply inj_Q_wd.
 unfold cg_minus; simpl; unfold QONE; ring.
stepr (inj_Q IR (One)[-]inj_Q IR (Two[*]q ^ 2))%Q.
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

Definition cos_poly_modulus (e:Qpos) := Qpos2QposInf (e/(4#1)).

Let X:((-(1))<1)%Q.
constructor.
Qed.

Let D : Derivative (clcr (inj_Q IR (-(1))) (inj_Q IR (1:Q))) (inj_Q_less _ _ _ X) ([-C-](One:IR){-}(Two:IR){**}FId{^}2)
 ([-C-](Zero:IR){-}(Two:IR){**}((nring 2){**}([-C-]One{*}FId{^}1))).
apply Derivative_minus.
 apply Derivative_const.
apply Derivative_scal.
apply Derivative_nth.
apply Derivative_id.
Qed.

Lemma cos_poly_prf : is_UniformlyContinuousFunction (fun x => cos_poly_fun (QboundAbs (1#1) x)) cos_poly_modulus.
Proof.
rapply (is_UniformlyContinuousD_Q (Some (-(1))%Q) (Some (1:Q)) X _ _ D cos_poly_fun).
 simpl; intros q _ _.
 rapply cos_poly_fun_correct.
simpl; intros x _ [Hx0 Hx1].
stepr (Four:IR) by (apply eq_symmetric; apply (inj_Q_nring IR 4)).
stepl (ABSIR ([--](Four[*]x))) by (apply AbsIR_wd; rational).
stepl (ABSIR (Four[*]x)) by apply AbsIR_inv.
rstepr (Four[*]One:IR).
apply AbsSmall_imp_AbsIR.
apply mult_resp_AbsSmall.
 apply nring_nonneg.
split.
 stepl ([--](pring IR 1)[/]Zero[+]One[//]den_is_nonzero IR (-1#1)).
  assumption.
 unfold pring; simpl; rational.
stepr  (pring IR 1[/]Zero[+]One[//]den_is_nonzero IR 1).
 assumption.
unfold pring; simpl; rational.
Qed.

Definition cos_poly_uc : Q_as_MetricSpace --> Q_as_MetricSpace := 
Build_UniformlyContinuousFunction cos_poly_prf.

Definition cos_poly : CR --> CR := Cmap QPrelengthSpace cos_poly_uc.

Lemma cos_poly_correct : forall x, AbsSmall (inj_Q IR (1)) x -> (IRasCR (One[-]Two[*]x[^]2)==cos_poly (IRasCR x))%CR.
Proof.
intros x Hx.
assert (Y:Continuous (clcr (inj_Q IR (-(1))) (inj_Q IR (1:Q))) ([-C-](One:IR){-}(Two:IR){**}FId{^}2)).
 eapply Derivative_imp_Continuous.
 apply D.
rapply (ContinuousCorrect (I:=(clcr (inj_Q IR (-(1))) (inj_Q IR (1:Q)))) (inj_Q_less _ _ _ X) Y);
 [|repeat constructor|].
 intros q Hq Hq0.
 transitivity (IRasCR (inj_Q IR (cos_poly_fun q)));[|apply IRasCR_wd; rapply cos_poly_fun_correct].
 simpl.
 change (' q)%CR with (Cunit_fun _ q).
 rewrite MonadLaw3.
 rewrite IR_inj_Q_as_CR.
 rewrite CReq_Qeq.
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
destruct Hx; split;[stepl [--](inj_Q IR (1:Q)) by apply eq_symmetric; apply inj_Q_inv|];assumption.
Qed.

Lemma Cos_double_angle : forall x, (Cos(Two[*]x)[=]One[-]Two[*]Sin x[^]2).
Proof.
intros x.
csetoid_replace (Two[*]x) (x[+]x);[|rational].
csetoid_rewrite (Cos_plus x x).
set (sx:=Sin x).
set (cx:=Cos x).
rstepl ((cx[^]2)[-](sx[^]2)).
unfold cg_minus.
csetoid_replace (cx[^]2) (One[-]sx[^]2).
 rational.
apply cg_inv_unique_2.
rstepl ((cx[^]2[+]sx[^]2)[-]One).
apply x_minus_x.
rapply FFT.
Qed.

End Cos_Poly.

Definition rational_cos (x:Q) := cos_poly (rational_sin (x/2)).

Lemma rational_cos_correct : forall (a:Q),
 (rational_cos a == IRasCR (Cos (inj_Q IR a)))%CR.
Proof.
intros a.
unfold rational_cos.
rewrite rational_sin_correct.
rewrite <- cos_poly_correct.
 apply AbsIR_imp_AbsSmall.
 stepr (nring 1:IR) by (apply eq_symmetric; apply (inj_Q_nring IR 1)).
 rstepr (One:IR).
 apply AbsIR_Sin_leEq_One.
apply IRasCR_wd.
csetoid_rewrite_rev (Cos_double_angle (inj_Q IR (a/2))).
apply Cos_wd.
csetoid_replace (Two:IR) (inj_Q IR (2:Q));[|apply eq_symmetric; apply (inj_Q_nring IR 2)].
stepl (inj_Q IR (2*(a/2))) by apply inj_Q_mult.
apply inj_Q_wd.
simpl; field; discriminate.
Qed.

Definition cos_uc_prf : is_UniformlyContinuousFunction rational_cos Qpos2QposInf.
Proof.
apply (is_UniformlyContinuousFunction_wd) with (fun x => rational_cos x) (modulusD (1#1)).
  reflexivity.
 intros x.
 simpl.
 autorewrite with QposElim.
 change (/1) with 1.
 replace RHS with (x:Q) by ring.
 apply Qle_refl.
rapply (is_UniformlyContinuousD None None I _ _ (Derivative_Cos CI) rational_cos).
 intros q [] _.
 rapply rational_cos_correct.
intros x [] _.
stepr (One:IR).
 change (AbsIR ([--](Sin x))[<=]One).
 stepl (AbsIR (Sin x)) by apply AbsIR_inv.
 rapply AbsIR_Sin_leEq_One.
rstepl (nring 1:IR).
apply eq_symmetric.
rapply (inj_Q_nring IR 1).
Qed.

Definition cos_uc : Q_as_MetricSpace --> CR := 
Build_UniformlyContinuousFunction cos_uc_prf.

Definition cos : CR --> CR := Cbind QPrelengthSpace cos_uc.

Lemma cos_correct : forall x,
 (IRasCR (Cos x) == cos (IRasCR x))%CR.
Proof.
intros x.
rapply (ContinuousCorrect (CI:proper realline));
 [apply Continuous_Cos | | constructor].
intros q [] _.
transitivity (rational_cos q);[|rapply rational_cos_correct].
rapply BindLaw1.
Qed.

Hint Rewrite cos_correct : IRtoCR.