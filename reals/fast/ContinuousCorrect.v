Require Export Q_in_CReals.
Require Export MoreIntervals.
Require Export CRIR.
Require Import CornTac.
Require Export Qmetric.
Require Export QposMinMax.

Opaque CR inj_Q.

Set Implicit Arguments.

Open Local Scope uc_scope.

Lemma Q_dense_in_compact : forall a b (Hab : a[<=]b) x, a[<]b -> Compact Hab x ->
 forall e, Zero[<]e -> {q:Q | Compact Hab (inj_Q IR q) | AbsSmall e (x[-]inj_Q IR q)}.
Proof.
intros a b Hab x Hab0 Hx e He.
set (l:=Max a (x[-]e)).
set (r:=Min b (x[+]e)).
assert (Hlr:l[<]r).
destruct Hx as [Hx0 Hx1].
rapply less_Min; rapply Max_less.
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
  rapply Min_leEq_lft.
 apply shift_zero_leEq_minus'.
 rstepr ((x[+]e)[-]inj_Q IR q).
 apply shift_zero_leEq_minus.
 eapply leEq_transitive.
  apply less_leEq.
  apply Hqr.
 rapply Min_leEq_rht.
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
rapply ball_eq.
intros e.
assert (HJ:compact_ J) by
 rapply compact_compact_in_interval.
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
 rapply proper_compact_in_interval'.
assert (HJx:(Compact Hab) x).
 rapply iprop_compact_in_interval'.
clearbody Hab a b.
clear J HJ.
pose (d:=match d1 with 
 | Qpos2QposInf q => Min (inj_Q IR (q:Q)) d0
 | QposInfinity => d0
 end).
assert (H0d : Zero[<]d).
 destruct d1; try assumption.
 rapply less_Min; try assumption.
 stepl (inj_Q IR Zero).
  apply inj_Q_less.
  rapply Qpos_prf.
 apply (inj_Q_nring IR 0).
destruct (Q_dense_in_compact Hab0 HJx _ H0d) as [q Hq0 Hq1].
setoid_replace e with ((1#2)*e+(1#2)*e)%Qpos by QposRing.
assert (Hfq : Dom f (inj_Q IR q)).
 apply Hf1.
 apply HJ'.
 assumption.
apply ball_triangle with (IRasCR (f (inj_Q IR q) Hfq)).
 rewrite <- CRAbsSmall_ball.
 stepr (IRasCR (f x Hx[-]f (inj_Q IR q) Hfq)) by (simpl; rapply IR_minus_as_CR).
 stepl (IRasCR (inj_Q IR (((1 # 2) * e)%Qpos:Q))) by (simpl; apply IR_inj_Q_as_CR).
 rewrite <- IR_AbsSmall_as_CR.
 apply AbsIR_imp_AbsSmall.
 apply Hf; try assumption.
 eapply leEq_transitive.
 apply AbsSmall_imp_AbsIR.
 apply Hq1.
 destruct d1.
  rapply Min_leEq_rht.
 rapply leEq_reflexive.
rewrite <- Hg.
 apply HJ'.
 assumption.
apply uc_prf.
fold d1.
destruct d1; try constructor.
simpl.
rewrite <- IR_inj_Q_as_CR.
rewrite <- CRAbsSmall_ball.
 stepr (IRasCR (inj_Q IR q[-]x)) by (simpl; rapply IR_minus_as_CR).
stepl (IRasCR (inj_Q IR (q0:Q))) by (simpl; apply IR_inj_Q_as_CR).
rewrite <- IR_AbsSmall_as_CR.
apply AbsSmall_minus.
eapply AbsSmall_leEq_trans;[|apply Hq1].
rapply Min_leEq_lft.
Qed.

End ContinuousCorrect.
