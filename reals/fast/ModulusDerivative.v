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
 destruct l as [|l]; destruct r as [|r]; unfold clamp; intros e a b Hab; try apply uc_prf; apply Hab.
Qed.

Variable f f' : PartFunct IR.
Hypothesis Hf : Derivative I properI f f'.

Section GeneralCase.

Variable g : Q_as_MetricSpace -> CR.
Hypothesis Hg : forall (q:Q) Hq, I (inj_Q _ q) -> (g q == IRasCR (f (inj_Q _ q) Hq))%CR.

Variable c : Q.
Hypothesis Hc : forall x Hx, I x -> (AbsIR (f' x Hx)[<=](inj_Q _ (c:Q))).

Lemma is_UniformlyContinuousD : is_UniformlyContinuousFunction (fun x => g (clamp x)) (Qscale_modulus c).
Proof.
 intros e a b Hab.
 assert (X:forall x, I (inj_Q _ (clamp x))).
  clear -I Hlr.
  intros x.
  destruct l as [|l];destruct r as [|r]; try split; unfold clamp; apply: inj_Q_leEq; simpl;
    auto with *.
  assert (Y:=(fun a=> (Hg _ (Derivative_imp_inc _ _ _ _ Hf _ (X a)) (X a)))).
 do 2 rewrite -> Y.
 rewrite <- CRAbsSmall_ball.
 unfold cg_minus.
 simpl.
 stepl (IRasCR (inj_Q IR (e:Q))); [| now simpl; apply IR_inj_Q_as_CR].
 stepr (IRasCR ((f (inj_Q IR (clamp a))
   (Derivative_imp_inc I properI f f' Hf (inj_Q IR (clamp a)) (X a)))[-] (f (inj_Q IR (clamp b))
     (Derivative_imp_inc I properI f f' Hf (inj_Q IR (clamp b)) (X b)))))
       ; [| now simpl; apply IR_minus_as_CR].
 rewrite <- IR_AbsSmall_as_CR.
 apply AbsIR_imp_AbsSmall.
 eapply leEq_transitive;[eapply Law_of_the_Mean_Abs_ineq;try apply Hf;try apply X|].
  intros x H Hx.
  apply Hc.
  eapply included_interval;[| |apply H];apply X.
 revert Hab.
 apply Qscale_modulus_elim.
  intros Hc0 _.
  stepl (inj_Q IR (nring 0)).
   apply inj_Q_leEq.
   simpl; auto with *.
  setoid_replace (inj_Q IR c) with (inj_Q IR (nring 0)).
   rewrite -> inj_Q_nring.
   rational.
  apply inj_Q_wd.
  auto.
 intros y Hyc Hab.
 stepr ((inj_Q IR (e/y)%Q[*](inj_Q _ (y:Q)))).
  apply mult_resp_leEq_both.
     eapply leEq_transitive.
      apply AbsIR_nonneg.
     apply (Hc _ (Derivative_imp_inc' I properI f f' Hf (inj_Q IR (clamp a)) (X a))).
     apply X.
    apply AbsIR_nonneg.
   apply inj_Q_leEq.
   destruct Hyc; auto.
  apply AbsSmall_imp_AbsIR.
  stepr (inj_Q IR (clamp a - clamp b)%Q); [| now apply inj_Q_minus].
  apply inj_Q_AbsSmall.
  change (ball y (clamp a) (clamp b)).
  apply ball_clamp.
  auto.
 assert (Z:Zero[<]inj_Q IR (y:Q)).
  (stepl (inj_Q IR (Zero:Q)); [| now apply (inj_Q_nring IR 0)]); apply inj_Q_less; apply Qpos_prf.
 apply: eq_transitive.
  apply mult_wdl.
  apply (inj_Q_div IR e _ (pos_ap_zero _ _ Z)).
 apply div_1.
Qed.

End GeneralCase.

Lemma is_UniformlyContinuousD_Q
     : forall g : Q_as_MetricSpace -> Q,
       (forall (q : Q) (Hq : Dom f (inj_Q IR q)),
        I (inj_Q IR q) -> (inj_Q IR (g q) [=] (f (inj_Q IR q) Hq))) ->
       forall c : Q,
       (forall (x : Q) (Hx : Dom f' (inj_Q IR x)), I (inj_Q IR x) -> AbsIR (f' (inj_Q IR x) Hx)[<=]inj_Q IR (c:Q)) ->
       is_UniformlyContinuousFunction (fun x : Q_as_MetricSpace => g (clamp x)) (Qscale_modulus c).
Proof.
 intros g Hg c Hc.
 intros e a b Hab.
 rewrite <- ball_Cunit.
 generalize e a b Hab; clear e a b Hab.
 change (is_UniformlyContinuousFunction
   (fun x : Q_as_MetricSpace => ((fun y => '(g y)) (clamp x)))%CR (Qscale_modulus c)).
 apply is_UniformlyContinuousD.
  intros q Hq H.
  rewrite <- IR_inj_Q_as_CR.
  apply IRasCR_wd.
  apply Hg.
  assumption.
 intros x Hx HI.
 rstepr (Zero[+]inj_Q IR c).
 apply shift_leEq_plus.
 apply approach_zero_weak.
 intros e He.
 assert (X:Derivative_I (proper_compact_in_interval' I properI x HI
   (compact_compact_in_interval I properI x HI)) f f').
  apply (included_imp_Derivative) with I properI; try assumption.
  eapply included_trans.
   apply iprop_compact_in_interval_inc1.
  apply included_compact_in_interval.
 set (LI' := (Lend (compact_compact_in_interval I properI x HI))).
 set (RI' := (Rend (compact_compact_in_interval I properI x HI))).
 set (I':=(less_leEq IR LI' RI' (proper_compact_in_interval' I properI x HI
   (compact_compact_in_interval I properI x HI)))).
 assert (X':Continuous_I I' (FAbs f')).
  apply Continuous_I_abs.
  apply (deriv_imp_contin'_I _ _ _ _ _ (less_leEq _ _ _ (proper_compact_in_interval' I properI x HI
    (compact_compact_in_interval I properI x HI))) X).
 clear X.
 destruct (contin_prop _ _ _ _ X' _ (pos_div_two _ _ He)) as [d Hd Hd0].
 destruct (iprop_compact_in_interval' _ properI x HI _ I') as [c0 c1].
 assert (Z:~((LI'[<]x or x[<]RI')->False)).
  intro H.
  fold LI' in c0.
  fold RI' in c1.
  apply (leEq_less_or_equal _ _ _ c0).
  intros [H0|H0];[tauto|].
  apply (leEq_less_or_equal _ _ _ c1).
  intros [H1|H1];[tauto|].
  generalize (proper_compact_in_interval' I properI x HI (compact_compact_in_interval I properI x HI)).
  change (Not (LI'[<]RI')).
  rewrite <- leEq_def.
  rewrite -> H0, <- H1.
  apply leEq_reflexive.
 rewrite -> leEq_def.
 intros Z0.
 apply Z.
 intros Z'.
 revert Z0.
 change (Not (e[<]AbsIR (f' x Hx)[-]inj_Q IR c)).
 rewrite <- leEq_def.
 clear Z.
 assert (J:Max LI' (x[-]d)[<]Min RI' (x[+]d)).
  destruct Z' as [Z'|Z'].
   apply less_leEq_trans with x.
    apply Max_less; auto.
    rstepr (x[-]Zero).
    apply minus_resp_less_rht.
    auto.
   apply leEq_Min; auto with *.
   rstepl (x[+]Zero).
   apply plus_resp_leEq_lft.
   apply less_leEq.
   auto with *.
  apply leEq_less_trans with x.
   apply Max_leEq; auto.
   rstepr (x[-]Zero).
   apply minus_resp_leEq_rht.
   apply less_leEq.
   auto.
  apply less_Min; auto with *.
  rstepl (x[+]Zero).
  apply plus_resp_less_lft.
  auto with *.
 destruct (Q_dense_in_CReals' _ _ _ J) as [q Hq0 Hq1].
 rstepr (e[/]TwoNZ [+] e[/]TwoNZ).
 assert (HI0 : Compact I' (inj_Q IR q)).
  split; apply less_leEq.
   eapply leEq_less_trans;[|apply Hq0].
   apply lft_leEq_Max.
  eapply less_leEq_trans;[apply Hq1|].
  apply Min_leEq_lft.
 assert (Hq:Dom f' (inj_Q IR q)).
  apply (Derivative_imp_inc' _ _ _ _ Hf).
  apply (included_compact_in_interval _ properI x HI).
  apply (iprop_compact_in_interval_inc1 _ _ _ _ _ I').
  auto.
 rstepl ((AbsIR (f' x Hx)[-]AbsIR (f' _ Hq))[+](AbsIR (f' _ Hq)[-]inj_Q IR c)).
 apply plus_resp_leEq_both.
  eapply leEq_transitive.
   apply leEq_AbsIR.
  assert (Z : Dom (FAbs f') x).
   split;auto.
  assert (Y : Dom (FAbs f') (inj_Q IR q)).
   split;auto.
  rewrite <- (FAbs_char _ _ Z).
  rewrite <- (FAbs_char _ _ Y).
  apply Hd0; auto.
   apply iprop_compact_in_interval'.
  apply AbsSmall_imp_AbsIR.
  split.
   apply shift_leEq_minus'.
   rstepl (inj_Q IR q[-]d).
   apply shift_minus_leEq.
   apply less_leEq.
   eapply less_leEq_trans;[apply Hq1|].
   apply Min_leEq_rht.
  apply shift_minus_leEq.
  apply shift_leEq_plus'.
  apply less_leEq.
  eapply leEq_less_trans;[|apply Hq0].
  apply rht_leEq_Max.
 eapply leEq_transitive;[|apply nonneg_div_two;apply less_leEq; auto].
 clear - Hc HI0.
 apply shift_minus_leEq.
 rstepr (inj_Q IR c).
 apply Hc.
 apply (included_compact_in_interval _ properI x HI).
 apply (iprop_compact_in_interval_inc1 _ properI x HI _ I').
 auto.
Qed.

End Modulus.
