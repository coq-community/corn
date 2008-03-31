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
Require Export Q_in_CReals.
Require Export CRIR.
Require Export Rolle.
Require Import CornTac.
Require Export Qmetric.
Require Export QMinMax.

Opaque Qmin Qmax.
Opaque CR inj_Q.

Section Modulus.
(**
** Modulus of continity and derivatives.
If two functions, one defined on IR and the other defined on CR, agree
on rational valued inside a closed non-trival interval, and the
function on IR is differentiable on that interval, then the function on
CR is uniformly continuous with modulus [fun e => e/M] where M is
some upper bound on the absolute value of the derivative.
*)
Variable l r : option Q.
Hypothesis Hlr : 
 match l,r with
 | None, _ => True
 | _, None => True
 | Some l', Some r' => (l'<r')%Q
end.

Let I := 
 match l,r with
 | None, None => realline
 | Some l', None => closel (inj_Q _ l')
 | None, Some r' => closer (inj_Q _ r')
 | Some l', Some r' => clcr (inj_Q _ l') (inj_Q _ r')
end.

Let properI : proper I.
Proof.
destruct l as [|l];destruct r as [|r]; try constructor.
simpl.
apply inj_Q_less.
assumption.
Qed.

Let clamp (q:Q) := 
match l,r with
 | None, None => q
 | Some l', None => QboundBelow_uc l' q
 | None, Some r' => QboundAbove_uc r' q
 | Some l', Some r' => (uc_compose (QboundBelow_uc l') (QboundAbove_uc r') q)
end.

Lemma ball_clamp : forall e a b, ball e a b -> ball e (clamp a) (clamp b).
Proof.
destruct l as [|l]; destruct r as [|r]; unfold clamp;
intros e a b Hab; try apply uc_prf; apply Hab.
Qed.

Variable f f' : PartFunct IR.
Hypothesis Hf : Derivative I properI f f'.

Section GeneralCase.

Variable g : Q_as_MetricSpace -> CR.
Hypothesis Hg : forall (q:Q) Hq, I (inj_Q _ q) -> (g q == IRasCR (f (inj_Q _ q) Hq))%CR.

Variable c : Qpos.
Hypothesis Hc : forall x Hx, I x -> (AbsIR (f' x Hx)[<=](inj_Q _ (c:Q))).

Definition modulusD (e:Qpos) := Qpos2QposInf (e/c)%Qpos.

Lemma is_UniformlyContinuousD : is_UniformlyContinuousFunction (fun x => g (clamp x)) modulusD.
Proof.
intros e a b Hab.
assert (X:forall x, I (inj_Q _ (clamp x))).
clear -I Hlr.
intros x.
destruct l as [|l];destruct r as [|r]; try split;
 unfold clamp;
 rapply inj_Q_leEq; simpl;
 auto with *.
assert (Y:=(fun a=> (Hg _ (Derivative_imp_inc _ _ _ _ Hf _ (X a)) (X a)))).
do 2 rewrite Y.
rewrite <- CRAbsSmall_ball.
unfold cg_minus.
simpl.
stepl (IRasCR (inj_Q IR (e:Q))) by simpl; apply IR_inj_Q_as_CR.
stepr (IRasCR
     ((f (inj_Q IR (clamp a))
        (Derivative_imp_inc I properI f f' Hf (inj_Q IR (clamp a)) (X a)))[-]
     (f (inj_Q IR (clamp b))
        (Derivative_imp_inc I properI f f' Hf (inj_Q IR (clamp b)) (X b)))))
 by simpl; apply IR_minus_as_CR.
rewrite <- IR_AbsSmall_as_CR.
apply AbsIR_imp_AbsSmall.
eapply leEq_transitive;[eapply Law_of_the_Mean_Abs_ineq;try apply Hf;try apply X|].
 intros x H Hx.
 apply Hc.
 eapply included_interval;[| |apply H];apply X.
clear - Hab.
assert (Z:Zero[<]inj_Q IR (c:Q)).
 (stepl (inj_Q IR (Zero:Q)) by rapply (inj_Q_nring IR 0)); apply inj_Q_less; apply Qpos_prf.
stepr ((inj_Q _ (c:Q))[*](inj_Q IR (e/c)%Q)).
apply mult_resp_leEq_lft;[|apply less_leEq; assumption].
 apply AbsSmall_imp_AbsIR.
 stepr (inj_Q IR (clamp a - clamp b)%Q) by apply inj_Q_minus.
 apply inj_Q_AbsSmall.
 change (ball (e/c) (clamp a) (clamp b)).
 apply ball_clamp.
 assumption.

rapply eq_transitive.
 apply mult_wdr.
 apply (inj_Q_div IR e c (pos_ap_zero _ _ Z)).
apply div_1'.
Qed.

End GeneralCase.

Lemma is_UniformlyContinuousD_Q
     : forall g : Q_as_MetricSpace -> Q,
       (forall (q : Q) (Hq : Dom f (inj_Q IR q)),
        I (inj_Q IR q) -> (inj_Q IR (g q) [=] (f (inj_Q IR q) Hq))) ->
       forall c : Qpos,
       (forall (x : IR) (Hx : Dom f' x), I x -> AbsIR (f' x Hx)[<=]inj_Q IR (c:Q)) ->
       is_UniformlyContinuousFunction (fun x : Q_as_MetricSpace => g (clamp x)) (modulusD c).
Proof.
intros g Hg c Hc.
intros e a b Hab.
rewrite <- ball_Cunit.
generalize e a b Hab; clear e a b Hab.
change (is_UniformlyContinuousFunction 
  (fun x : Q_as_MetricSpace => ((fun y => '(g y)) (clamp x)))%CR (modulusD c)).
apply is_UniformlyContinuousD;[|assumption].
intros q Hq H.
rewrite <- IR_inj_Q_as_CR.
apply IRasCR_wd.
apply Hg.
assumption.
Qed.

End Modulus.

