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
Require Export MoreIntervals.
Require Export CRIR.
Require Import CornTac.
Require Export Qmetric.
Require Export QposMinMax.

Opaque CR inj_Q.

Set Implicit Arguments.

Open Local Scope uc_scope.
(**
** Correctness of continuous functions.
We show that if two functions, one on IR and one on CR, agree on the
rational values of some closed interval, and both functions are continuous,
then the two functions agree on that entire closed interval.

This is our main method of proving the corrections of functions defined
on CR.
*)
Lemma Q_dense_in_compact : forall a b (Hab : a[<=]b) x, a[<]b -> Compact Hab x ->
 forall e, Zero[<]e -> {q:Q | Compact Hab (inj_Q IR q) | AbsSmall e (x[-]inj_Q IR q)}.
Proof.
 intros a b Hab x Hab0 Hx e He.
 set (l:=Max a (x[-]e)).
 set (r:=Min b (x[+]e)).
 assert (Hlr:l[<]r).
  destruct Hx as [Hx0 Hx1].
  apply less_Min; apply Max_less.
     assumption.
    apply shift_minus_less.
    rstepl (x[+]Zero).
    apply plus_resp_leEq_less; assumption.
   rstepl (a[+]Zero).
   apply plus_resp_leEq_less; assumption.
  apply shift_zero_less_minus'.
  rstepr (e[+]e).
  apply plus_resp_pos; assumption.
 destruct (Q_dense_in_CReals' _ _ _ Hlr) as [q Hlq Hqr].
 exists q; split.
    eapply leEq_transitive.
     apply lft_leEq_Max.
    apply less_leEq; unfold l in Hlq; apply Hlq.
   eapply leEq_transitive.
    apply less_leEq;apply Hqr.
   apply Min_leEq_lft.
  apply shift_zero_leEq_minus'.
  rstepr ((x[+]e)[-]inj_Q IR q).
  apply shift_zero_leEq_minus.
  eapply leEq_transitive.
   apply less_leEq.
   apply Hqr.
  apply Min_leEq_rht.
 apply shift_zero_leEq_minus'.
 rstepr (inj_Q IR q[-](x[-]e)).
 apply shift_zero_leEq_minus.
 eapply leEq_transitive.
  apply rht_leEq_Max.
 apply less_leEq.
 unfold l in Hlq; apply Hlq.
Qed.

Section ContinuousCorrect.

Variable I : interval.
Hypothesis HI : proper I.

Variable f : PartFunct IR.
Hypothesis Hf : Continuous I f.

Variable g : CR --> CR.
Hypothesis Hg : forall (q:Q) Hq, I (inj_Q IR q) -> (g (' q) == IRasCR (f (inj_Q IR q) Hq))%CR.

Lemma ContinuousCorrect : forall (x:IR) Hx, I x -> (IRasCR (f x Hx) == g (IRasCR x))%CR.
Proof.
 intros x Hx H.
 set (J:=compact_in_interval I HI x H).
 apply ball_eq.
 intros e.
 assert (HJ:compact_ J) by apply compact_compact_in_interval.
 destruct Hf as [Hf1 Hf0].
 clear Hf.
 assert (X:Continuous_I (Lend_leEq_Rend J HJ) f).
  apply Hf0.
  eapply included_trans;[|apply included_compact_in_interval].
  unfold J;  apply iprop_compact_in_interval_inc1.
 clear Hf0.
 destruct X as [_ X].
 assert (He : Zero[<](inj_Q IR (((1#2)*e)%Qpos:Q))).
  stepl (inj_Q IR (nring 0)) by apply (inj_Q_nring IR 0).
  apply inj_Q_less.
  apply Qpos_prf.
 destruct (X _ He) as [d0 Hd0 Hf].
 clear X.
 set (d1:=mu g ((1#2)*e)).
 set (Hab := (Lend_leEq_Rend J HJ)) in *.
 set (a:= (@Lend J HJ)) in *.
 set (b:= (@Rend J HJ)) in *.
 assert (HJ':included (Compact Hab) I).
  eapply included_trans.
   unfold Hab, a, b, J; apply iprop_compact_in_interval_inc1.
  apply included_compact_in_interval.
 assert (Hab0: a[<]b).
  apply proper_compact_in_interval'.
 assert (HJx:(Compact Hab) x).
  apply iprop_compact_in_interval'.
 clearbody Hab a b.
 clear J HJ.
 pose (d:=match d1 with | Qpos2QposInf q => Min (inj_Q IR (q:Q)) d0 | QposInfinity => d0 end).
 assert (H0d : Zero[<]d).
  destruct d1; try assumption.
  apply less_Min; try assumption.
  stepl (inj_Q IR Zero).
   apply inj_Q_less.
   apply Qpos_prf.
  apply (inj_Q_nring IR 0).
 destruct (Q_dense_in_compact Hab0 HJx _ H0d) as [q Hq0 Hq1].
 setoid_replace e with ((1#2)*e+(1#2)*e)%Qpos by QposRing.
 assert (Hfq : Dom f (inj_Q IR q)).
  apply Hf1.
  apply HJ'.
  assumption.
 apply ball_triangle with (IRasCR (f (inj_Q IR q) Hfq)).
  rewrite <- CRAbsSmall_ball.
  stepr (IRasCR (f x Hx[-]f (inj_Q IR q) Hfq)) by (simpl; apply IR_minus_as_CR).
  stepl (IRasCR (inj_Q IR (((1 # 2) * e)%Qpos:Q))) by (simpl; apply IR_inj_Q_as_CR).
  rewrite <- IR_AbsSmall_as_CR.
  apply AbsIR_imp_AbsSmall.
  apply Hf; try assumption.
  eapply leEq_transitive.
   apply AbsSmall_imp_AbsIR.
   apply Hq1.
  destruct d1.
   apply Min_leEq_rht.
  apply leEq_reflexive.
 rewrite <- Hg;[|apply HJ';assumption].
 apply uc_prf.
 fold d1.
 destruct d1; try constructor.
 simpl.
 rewrite <- IR_inj_Q_as_CR.
 rewrite <- CRAbsSmall_ball.
 stepr (IRasCR (inj_Q IR q[-]x)) by (simpl; apply IR_minus_as_CR).
 stepl (IRasCR (inj_Q IR (q0:Q))) by (simpl; apply IR_inj_Q_as_CR).
 rewrite <- IR_AbsSmall_as_CR.
 apply AbsSmall_minus.
 eapply AbsSmall_leEq_trans;[|apply Hq1].
 apply Min_leEq_lft.
Qed.

End ContinuousCorrect.
