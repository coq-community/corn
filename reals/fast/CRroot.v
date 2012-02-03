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

Require Import Q_in_CReals.
Require Import CRpower.
Require Export CRArith.
Require Import CRIR.
Require Import NRootIR.
Require Import QMinMax.
Require Import QposMinMax.
Require Import Qmetric.
Require Import Qpower.
Require Import Qordfield.
Require Import Compress.
Require Import Ndigits.
Require Import PowerBound.
Require Import RealPowers.
Require Import ContinuousCorrect.
Require Import Qauto.
Require Import CornTac.
Require Import abstract_algebra.

Open Local Scope Q_scope.

Opaque CR.
Opaque Qmin Qmax.

(**
** Square Root
Square root is implement using Newton's method.
*)

Section SquareRoot.

Variable a : Q.

Hypothesis Ha : 1 <= a <= 4.
(** Square root is first defined on [[1,4]].  Iterating this formula will
converge to the square root of [a]. *)
Definition root_step (b:Q) : Q := b / (2#1) + a / ((2#1) * b).

Definition root_has_error (e:Qpos) (b:Q) := a <= (b+e)^2 /\ (b-e)^2 <= a.
(* begin hide *)
Add Morphism root_has_error with signature QposEq ==> Qeq ==> iff as root_has_error_wd.
Proof.
 intros x1 x2 Hx y1 y2 Hy.
 unfold root_has_error.
 rewrite -> Hy.
 unfold QposEq in Hx.
 rewrite -> Hx.
 reflexivity.
Qed.
(* end hide *)
Lemma root_has_error_le : forall (e1 e2:Qpos) (b:Q), e2 <= b -> e1 <= e2 -> root_has_error e1 b -> root_has_error e2 b.
Proof.
 intros e1 e2 b Hb He [H0 H1].
 rewrite -> Qle_minus_iff in *.
 split; rewrite -> Qle_minus_iff.
  replace RHS with (((b + e1) ^ 2 + - a) + (e2 + - e1)*((2#1) * (b + - e2 + e2) + e2 + e1)) by ring.
  Qauto_nonneg.
 replace RHS with ((a + - (b-e1)^2) + (e2 + -e1)*((e2 + - e1) + (2#1) * (b + - e2))) by ring.
 Qauto_nonneg.
Qed.

Lemma root_error_bnd : forall (e:Qpos) b, e <= 1 -> 1 <= b -> (root_has_error e b) -> b <= (2#1) + e.
Proof.
 intros e b He Hb [H0 H1].
 destruct Ha as [Ha0 Ha1].
 rewrite -> Qle_minus_iff in *.
 assert (X:0 < 2 + b - e).
  apply Qlt_le_trans with 2.
   constructor.
  rewrite -> Qle_minus_iff.
  replace RHS with ((b + -(1)) + (1 + - e)) by (simpl; ring).
  Qauto_nonneg.
 replace RHS with ((((4#1)  + - a) + (a + - (b - e)^2))/((2#1) + b - e)) by simpl; field; auto with *.
 apply Qle_shift_div_l.
  assumption.
 replace LHS with 0 by simpl; ring.
 Qauto_nonneg.
Qed.

Lemma root_has_error_ball : forall (e1 e2:Qpos) (b1 b2:Q), 
  (e1 + e2<=1) ->  (1 <= b1) -> (1 <= b2) -> root_has_error e1 b1 -> Qball e2 b1 b2 -> root_has_error (e1+e2) b2.
Proof.
 intros e1 e2 b1 b2 He Hb1 Hb2 [H0 H1] [H2 H3].
 simpl in H2, H3.
 clear Ha.
 rewrite -> Qle_minus_iff in *.
 unfold root_has_error.
 autorewrite with QposElim.
 split; rewrite -> Qle_minus_iff.
  replace RHS with (((b1 + e1)^2 + - a) + (b2 + - (1)  + e1 + e2 + (b1 + -(1)) + (2#1) + e1)*(e2 - (b1 - b2))) by simpl; ring.
  Qauto_nonneg.
 replace RHS with ((a + - (b1 - e1)^2) +  (b1 - b2 + - - e2)*((b1 + -(1)) + (1 + - (e1 + e2)) + e2 + (b2 + -(1)) + (1 + - (e1 + e2)))) by simpl; ring.
 Qauto_nonneg.
Qed.

Lemma ball_root_has_error : forall (e1 e2:Qpos) (b1 b2:Q), 
  ((e1 + e2)<=1) -> (1<=b1) -> (1<=b2) -> root_has_error e1 b1 -> root_has_error e2 b2 -> Qball (e1+e2) b1 b2.
Proof.
 intros e1 e2 b1 b2 He Hb1 Hb2 [H0 H1] [H2 H3].
 clear Ha.
 rewrite -> Qle_minus_iff in *.
 split; simpl; autorewrite with QposElim; rewrite -> Qle_minus_iff.
  assert (A0:0 < (b1 + e1 + b2 - e2)).
   apply Qlt_le_trans with 1;[constructor|].
   rewrite -> Qle_minus_iff.
   replace RHS with (b1 + - (1) + (b2 + - (1)) + (2#1) * e1 + (1 - (e1 + e2))) by simpl; ring.
   Qauto_nonneg.
  replace RHS with ((((b1 + e1)^2 + - a) + (a + - (b2 - e2)^2))/(b1 + e1 +b2 - e2)) by (simpl; field; auto with * ).
  Qauto_nonneg.
 assert (A0:0 < (b2 + e2 + b1 - e1)).
  apply Qlt_le_trans with 1;[constructor|].
  rewrite -> Qle_minus_iff.
  replace RHS with (b2 + - (1) + (b1 + - (1)) + (2#1) * e2 + (1 - (e1 + e2))) by simpl; ring.
  Qauto_nonneg.
 replace RHS with (((a + -(b1 - e1)^2) + ((b2 + e2)^2 + - a))/(b2 + e2 + b1 - e1)) by (simpl; field;auto with * ).
 Qauto_nonneg.
Qed.

Lemma root_step_error : forall b (e:Qpos), 
  (1 <= b) ->  (e <= 1) -> root_has_error e b -> root_has_error ((1#2)*(e*e)) (root_step b).
Proof.
 intros b e Hb He [H0 H1].
 unfold root_step.
 assert (A0:0 < b).
  apply Qlt_le_trans with 1; try assumption.
  Qauto_pos.
 assert (A1:(0 <= b - e^2)).
  replace RHS with (b + - e^2) by simpl; ring.
  rewrite <- Qle_minus_iff.
  apply Qle_trans with ((1:Q)[^]2); try assumption.
  replace LHS with ((e:Q)[^]2) by (simpl; ring).
  apply: (power_resp_leEq);simpl; try assumption.
  apply Qpos_nonneg.
 assert (A2:(0 <= a)).
  eapply Qle_trans;[|apply H1].
  replace RHS with ((b-e)[^]2) by (simpl; ring).
  apply: sqr_nonneg.
 split.
  apply Qle_trans with ((b / (2#1) + a / ((2#1) * b))^2); [|Qauto_le].
  field_simplify (b / (2#1) + a / ((2#1) * b)); auto with *.
  rewrite -> Qdiv_power.
  apply Qle_shift_div_l.
   Qauto_pos.
  rewrite -> Qle_minus_iff.
  replace RHS with ((b^2 - a)[^]2) by (simpl; ring).
  apply: sqr_nonneg.
 field_simplify (b / (2#1) + a / ((2#1) * b) - ((1#2)*(e * e)%Qpos)); auto with *.
 rewrite -> Qdiv_power.
 apply Qle_shift_div_r.
  Qauto_pos.
 replace LHS with ((a + b^2 - b*e^2)^2) by simpl; ring.
 apply Qle_trans with ((a + b^2 - e^2)^2).
  replace RHS with ((a + b ^ 2 - e ^ 2)[^]2) by (simpl; ring).
  replace LHS with ((a + b ^ 2 - b * e ^ 2)[^]2) by (simpl; ring).
  apply: (power_resp_leEq).
   replace RHS with (a + b*(b-e^2)) by simpl; ring.
   Qauto_nonneg.
  rewrite -> Qle_minus_iff;ring_simplify.
  replace RHS with ((b-1)*((e:Q)[^]2)) by (simpl; ring).
  rewrite -> Qle_minus_iff in Hb.
  Qauto_nonneg.
 rewrite -> Qle_minus_iff.
 replace RHS with ((a-(b-e)^2)*((b+e)^2-a)) by simpl; ring.
 rewrite -> Qle_minus_iff in *|-.
 apply: mult_resp_nonneg; assumption.
Qed.

(** Our initial estimate is (a+1)/2 with an error of 1/2 *)
Definition initial_root :Q := ((1#2)*(a+1)).

Lemma initial_root_error : root_has_error (1#2) initial_root.
Proof.
 destruct Ha as [Ha0 Ha1].
 unfold initial_root, root_has_error.
 autorewrite with QposElim.
 split.
  Qauto_le.
 rewrite -> Qle_minus_iff.
 assert (A0:(0<=1 + -((1#4)*a))).
  rewrite <- Qle_minus_iff.
  replace LHS with (a/(4#1)) by (simpl; field; discriminate).
  apply Qle_shift_div_r; try assumption.
  Qauto_pos.
 rewrite -> Qle_minus_iff in Ha0.
 replace RHS with ((a + -(1) + 1)*(1 +- ((1#4)*a))) by simpl; ring.
 Qauto_nonneg.
Qed.

Lemma root_step_one_le : forall b,  (1 <= b)-> (1 <= root_step b).
Proof.
 intros b Hb.
 assert (A0:0<b).
  apply Qlt_le_trans with 1; auto with *.
 destruct Ha as [Ha0 Ha1].
 unfold root_step.
 rewrite -> Qle_minus_iff in *.
 field_simplify (b / (2#1) + a / ((2#1) * b) + -(1));auto with *.
 apply Qle_shift_div_l.
  Qauto_pos.
 ring_simplify.
 replace RHS with (((b -1) ^ 2 +  (a + -(1)))) by simpl; ring.
 Qauto_nonneg.
Qed.

Lemma initial_root_one_le : (1 <= initial_root).
Proof.
 destruct Ha as [Ha0 Ha1].
 unfold initial_root.
 rewrite -> Qle_minus_iff in *.
 replace RHS with ((1#2)*(a + - (1))) by simpl; ring.
 Qauto_nonneg.
Qed.

(** Each step squares the error *)
Fixpoint root_loop (e:Qpos) (n:nat) (b:Q) (err:positive) {struct n} : Q :=
match n with
| O => b
| S n' => match Qlt_le_dec_fast e (1#err) with
          | left _ => let err':= (err*err)%positive in root_loop e n' (approximateQ (root_step b) (2*err')) err'
          | right _ => b
          end
end.

Opaque root_step.

Lemma root_loop_one_le : forall e n b err,  (1 <= b)-> (1 <= root_loop e n b err).
Proof.
 intros e n.
 induction n; auto with *.
 simpl.
 intros b err Hb.
 destruct (Qlt_le_dec_fast e (1 # err)) as [A|A]; try assumption.
 apply IHn.
 apply approximateQ_big.
 apply root_step_one_le.
 assumption.
Qed.

Lemma root_loop_error : forall (e:Qpos) n b err, (1 <= b) -> root_has_error (1#err) b -> (1#(iter_nat n _ (fun x => (x * x)%positive) err))<=e ->
 root_has_error (Qpos_min (1 # err) e) (root_loop e n b err).
Proof.
 induction n.
  intros b err Hb0 Hb1 He.
  simpl in *.
  setoid_replace (Qpos_min (1 # err) e) with (1#err)%Qpos; try assumption.
  unfold QposEq.
  rewrite <- Qpos_le_min_l.
  assumption.
 intros b err Hb0 Hb1 He.
 simpl in *.
 destruct (Qlt_le_dec_fast e (1 # err)) as [A|A].
  apply root_has_error_le with (Qpos_min (1#(err*err)) e).
    apply Qle_trans with 1.
     apply Qle_trans with (1#err); auto with *.
     apply Qpos_min_lb_l.
    apply root_loop_one_le.
    apply approximateQ_big.
    apply root_step_one_le; assumption.
   apply Qpos_min_glb.
    apply Qle_trans with (1#err*err).
     apply Qpos_min_lb_l.
    change (1*err <= err*err)%Z; auto with *.
   apply Qpos_min_lb_r.
  apply IHn; try assumption.
    apply approximateQ_big.
    apply root_step_one_le; assumption.
   setoid_replace (1#err*err)%Qpos with ((1#(2*(err * err)))+(1#(2*(err * err))))%Qpos.
    apply root_has_error_ball with (root_step b).
        autorewrite with QposElim.
        ring_simplify.
        unfold Qmult, Qle; simpl.
        auto with *.
       apply root_step_one_le; assumption.
      apply approximateQ_big.
      apply root_step_one_le; assumption.
     apply (root_step_error b (1#err)); try assumption.
     unfold Qle; simpl; auto with *.
    apply approximateQ_correct.
   unfold QposEq.
   autorewrite with QposElim.
   ring_simplify.
   constructor.
  replace (iter_nat n positive (fun x : positive => (x * x)%positive) (err * err)%positive)
    with (iter_nat n positive (fun x : positive => (x * x)%positive) err *
      iter_nat n positive (fun x : positive => (x * x)%positive) err)%positive.
   assumption.
  clear - n.
  induction n; try constructor.
  simpl in *.
  rewrite IHn.
  reflexivity.
 setoid_replace (Qpos_min (1 # err) e) with (1#err)%Qpos; try assumption.
 unfold QposEq.
 rewrite <- Qpos_le_min_l.
 assumption.
Qed.

(** Find a bound on the number of iterations we need to take. *)
Lemma root_max_steps : forall (n d:positive), (1#(iter_nat (S (Psize d)) _ (fun x => (x * x)%positive) 2%positive))<=(n#d)%Qpos.
Proof.
 intros n d.
 apply Qle_trans with (1#d).
  clear - d.
  unfold Qle; simpl.
  cut ((d <= iter_nat (S (Psize d)) positive (fun x : positive => (x * x)%positive)
    2%positive)%Z/\(4 <= iter_nat (S (Psize d)) positive (fun x : positive => (x * x)%positive)
      2%positive)%Z).
   tauto.
  induction d; split; try discriminate; destruct IHd as [A B];
    set (t:=iter_nat (S (Psize d)) positive (fun x : positive => (x * x)%positive) 2%positive) in *.
     rewrite Zpos_xI.
     apply Zle_trans with (4*d)%Z; auto with *.
     apply (Zmult_le_compat 4 d t t); auto with *.
    change (4%Z) with (2*2)%Z.
    apply (Zmult_le_compat 2 2 t t); auto with *.
   rewrite Zpos_xO.
   apply Zle_trans with (4*d)%Z; auto with *.
   apply (Zmult_le_compat 4 d t t); auto with *.
  change (4%Z) with (2*2)%Z.
  apply (Zmult_le_compat 2 2 t t); auto with *.
 unfold Qle; simpl.
 change (1*d <= n*d)%Z.
 auto with *.
Qed.

(** Square root on [[1,4]]. *)
Definition sqrt_raw (e:QposInf) : Q :=
match e with
| QposInfinity => 1
| Qpos2QposInf e' => root_loop e' (S (Psize (Qden e'))) initial_root 2
end.

Lemma sqrt_regular : is_RegularFunction sqrt_raw.
Proof.
 intros e1 e2.
 apply ball_weak_le with (Qpos_min (1#2) e1 + Qpos_min (1#2) e2)%Qpos.
  autorewrite with QposElim.
  apply: plus_resp_leEq_both; simpl; auto with *.
 apply ball_root_has_error.
     setoid_replace (1:Q) with ((1#2)%Qpos + (1#2)%Qpos) by (simpl; QposRing).
     apply: plus_resp_leEq_both; apply Qpos_min_lb_l.
    apply root_loop_one_le.
    apply initial_root_one_le.
   apply root_loop_one_le.
   apply initial_root_one_le.
  apply root_loop_error.
    apply initial_root_one_le.
   apply initial_root_error.
  revert e1.
  apply Qpos_positive_numerator_rect.
  apply root_max_steps.
 apply root_loop_error.
   apply initial_root_one_le.
  apply initial_root_error.
 revert e2.
 apply Qpos_positive_numerator_rect.
 apply root_max_steps.
Qed.

Definition rational_sqrt_mid : CR := Build_RegularFunction sqrt_regular.

Lemma rational_sqrt_mid_err : forall (e:Qpos), (e <= 1) -> root_has_error e (approximate rational_sqrt_mid e).
Proof.
 intros e He.
 change (root_has_error e (sqrt_raw e)).
 unfold sqrt_raw.
 eapply root_has_error_le;[| |apply root_loop_error].
     eapply Qle_trans;[apply He|].
     apply root_loop_one_le; apply initial_root_one_le.
    apply Qpos_min_lb_r.
   apply initial_root_one_le.
  apply initial_root_error.
 clear.
 revert e.
 apply Qpos_positive_numerator_rect.
 apply root_max_steps.
Qed.

Lemma rational_sqrt_mid_one_le : forall (e:QposInf), 1 <= (approximate rational_sqrt_mid e).
Proof.
 intros [e|];[|apply Qle_refl].
 apply: root_loop_one_le.
 apply initial_root_one_le.
Qed.

Lemma rational_sqrt_mid_le_3 : forall (e:QposInf), (approximate rational_sqrt_mid e) <= 3.
Proof.
 intros [e|];[|discriminate].
 change (sqrt_raw e <= (3#1)).
 unfold sqrt_raw.
 set (n:= (S (Psize (Qden e)))).
 assert (root_has_error (Qpos_min (1 # 2) e) (root_loop e n initial_root 2)).
  apply root_loop_error.
    apply initial_root_one_le.
   apply initial_root_error.
  subst n.
  clear. revert e.
  apply Qpos_positive_numerator_rect.
  apply root_max_steps.
 eapply Qle_trans.
  apply root_error_bnd;[| |apply H].
   eapply Qle_trans.
    apply Qpos_min_lb_l.
   discriminate.
  apply root_loop_one_le.
  apply initial_root_one_le.
 assert (X:=Qpos_min_lb_l (1#2) e).
 rewrite ->  Qle_minus_iff in *.
 replace RHS with ((1#2)%Qpos + - Qpos_min (1 # 2) e + (1#2)).
  Qauto_nonneg.
 autorewrite with QposElim.
 simpl. ring.
Qed.

Opaque root_loop.

Lemma rational_sqrt_mid_correct0 : (CRpower_N rational_sqrt_mid 2 == ' a)%CR.
Proof.
 assert (H:AbsSmall (R:=CRasCOrdField) (' (3 # 1)%Qpos)%CR rational_sqrt_mid).
  split; simpl.
   intros e.
   change (-e <= sqrt_raw (Qpos2QposInf ((1#2)*e)) + - - (3#1)).
   apply Qle_trans with 0.
    rewrite -> Qle_minus_iff.
    ring_simplify.
    auto with *.
   rewrite <- Qle_minus_iff.
   apply Qle_trans with 1.
    discriminate.
   apply rational_sqrt_mid_one_le.
  intros e.
  change (-e <= 3 + - sqrt_raw (Qpos2QposInf ((1#2)*e))).
  apply Qle_trans with 0.
   rewrite -> Qle_minus_iff.
   ring_simplify.
   auto with *.
  rewrite <- Qle_minus_iff.
  apply rational_sqrt_mid_le_3.
 rewrite <- (CRpower_N_bounded_N_power 2 (3#1));[|assumption].
 apply (regFunEq_e_small (X:=Q_as_MetricSpace) (CRpower_N_bounded 2 (3 # 1) rational_sqrt_mid) (' a)%CR (1#1)).
 intros e.
 destruct (Qpos_as_positive_ratio e) as [[en ed] E].
 subst e.
 simpl fst.
 simpl snd.
 set (e := (en # ed)%Qpos).
 intro He.
 set (d:=(e / (6#1))%Qpos).
 change (Qball (e + e)
  (approximate ((CRpower_N_bounded 2 (3 # 1)) rational_sqrt_mid) e)
  a).
 assert (
   (approximate ((CRpower_N_bounded 2 (3 # 1)) rational_sqrt_mid) e) =
   ((Qmax (- (3#1)) (Qmin (3#1) (approximate rational_sqrt_mid d)))^2)
   ).
  simpl.
  replace d with (Qpos_mult e (Qpos_inv ((2 # 1) * ((3 # 1) ^ (2 - 1)%positive)))).
   reflexivity.
  subst e d.
  f_equal.
  unfold Qpos_mult, mkQpos, Qmult, QposMake. simpl.
  f_equal. f_equal. apply Qlt_uniq.
 rewrite H0.
 clear H0.
 setoid_replace (Qmin (3#1) (approximate rational_sqrt_mid d))
   with ((approximate rational_sqrt_mid d)) by
     (rewrite <- Qle_min_r;destruct H;apply rational_sqrt_mid_le_3).
 setoid_replace (Qmax (-3#1) (approximate rational_sqrt_mid d))
   with ((approximate rational_sqrt_mid d))
     by (rewrite <- Qle_max_r;destruct H;eapply Qle_trans;[|apply rational_sqrt_mid_one_le];discriminate).
 assert (Z:root_has_error d (approximate rational_sqrt_mid d)).
  apply rational_sqrt_mid_err.
  unfold d.
  autorewrite with QposElim.
  change ((e/(6#1)) <= 1).
  apply Qle_shift_div_r.
   constructor.
  eapply Qle_trans.
   apply He.
  discriminate.
 set (z:=approximate rational_sqrt_mid d) in *.
 assert (X:z <= 3).
  apply rational_sqrt_mid_le_3.
 assert (X0:d^2 <= e).
  unfold d.
  autorewrite with QposElim in *.
  change ((e*(1#6))^2 <= e).
  rewrite ->  Qle_minus_iff in *.
  replace RHS with (e*(1 + -e + (35#36)* e)) by simpl; ring.
  Qauto_nonneg.
 destruct Z; split; simpl; rewrite ->  Qle_minus_iff in *; autorewrite with QposElim in *.
  replace RHS with (((z+d)^2 + - a) + (2#1) * ((3#1) + -z) * d + (e + - d^2))
    by (simpl; unfold d; autorewrite with QposElim;field;discriminate).
  Qauto_nonneg.
 replace RHS with (a + - (z-d)^2 + (2#1) * ((3#1) + - z)*d + d^2 + e)
   by (simpl; unfold d; autorewrite with QposElim;field;discriminate).
 Qauto_nonneg.
Qed. (* todo: clean up *)

Lemma rational_sqrt_mid_correct1 : (0 <= rational_sqrt_mid)%CR.
Proof.
 intros e.
 apply Qle_trans with 1.
  Qauto_le.
 change (1 <= sqrt_raw ((1#2)%Qpos*e) - 0).
 ring_simplify.
 apply rational_sqrt_mid_one_le.
Qed.
End SquareRoot.

Lemma rational_sqrt_mid_correct_aux (x : Q) (y : CR) Px :
  CRpower_N y 2 = 'x → 0%CR ≤ y → y = IRasCR (sqrt (inj_Q IR x) Px).
Proof.
 intros f_sqrt f_nonneg.
 rewrite <- (CRasIRasCR_id y).
 apply IRasCR_wd.
 assert (X:[0][<=](CRasIR y)[^]2).
  apply sqr_nonneg.
 stepl (sqrt _ X).
  apply sqrt_wd.
  rewrite -> IR_eq_as_CR.
  rewrite -> (CRpower_N_correct 2).
  rewrite -> IR_inj_Q_as_CR.
  now rewrite -> (CRasIRasCR_id).
 apply sqrt_to_nonneg.
 rewrite -> IR_leEq_as_CR.
 rewrite -> IR_Zero_as_CR.
 now rewrite -> CRasIRasCR_id.
Qed.

Lemma rational_sqrt_mid_correct a Pa H : 
  (rational_sqrt_mid a Pa == IRasCR (sqrt (inj_Q IR a) H))%CR.
Proof.
 apply rational_sqrt_mid_correct_aux.
  now apply rational_sqrt_mid_correct0.
 now apply rational_sqrt_mid_correct1.
Qed.

(** By scaling the input the range of square root can be extened upto 4^n.
*)
Fixpoint rational_sqrt_big_bounded (n:nat) a (Ha:1 <= a <= (4 ^ n)%Z) : CR.
 revert a Ha.
 destruct n as [|n].
  intros _ _.
  exact 1%CR.
 intros a H.
 destruct (Qle_total a (4#1)).
  clear rational_sqrt_big_bounded.
  refine (@rational_sqrt_mid a _).
  abstract (destruct H; tauto).
 refine (scale (2#1) _).
 refine (@rational_sqrt_big_bounded n (a / (4#1)) _).
 clear rational_sqrt_big_bounded.
 abstract ( destruct H; split;[apply Qle_shift_div_l;[constructor|assumption]|];
   apply Qle_shift_div_r;[constructor|]; rewrite -> Zpower_Qpower in *; try auto with *;
     change (a <= ((4#1) ^ n) * (4#1)^1); rewrite <- Qpower_plus; try discriminate; change (n+1)%Z with (Zsucc n);
       rewrite <- inj_S; assumption).
Defined.

Lemma rational_sqrt_big_bounded_correct_aux a Xa4 Xa :
  (scale (2#1)) (IRasCR (sqrt (inj_Q IR (a / (4#1))) Xa4)) [=] IRasCR (sqrt (inj_Q IR a) Xa).
Proof.
 rewrite <- CRmult_scale.
 rewrite <- IR_inj_Q_as_CR.
 rewrite <- IR_mult_as_CR.
 apply IRasCR_wd.
 assert (X1:[0][<=](inj_Q IR (4#1))).
  stepl (inj_Q IR 0); [| now (apply (inj_Q_nring IR 0))].
  apply inj_Q_leEq.
  discriminate.
 csetoid_replace (inj_Q IR (2#1)) (sqrt _ X1).
  assert (X2:[0][<=](inj_Q IR (4#1)[*]inj_Q IR (a/4%positive))).
   apply mult_resp_nonneg;assumption.
  astepl (sqrt _ X2).
  apply sqrt_wd.
  csetoid_rewrite_rev (inj_Q_mult IR (4#1) (a/4%positive)).
  apply inj_Q_wd.
  simpl.
  field; discriminate.
 change (inj_Q IR (4#1)) with (inj_Q IR ((2#1)[*](2#1))).
 assert (X2:[0][<=](inj_Q IR (2#1))[^]2).
  apply sqr_nonneg.
 stepr (sqrt _ X2).
  apply eq_symmetric; apply sqrt_to_nonneg.
  stepl (inj_Q IR 0); [| now (apply (inj_Q_nring IR 0))].
  apply inj_Q_leEq.
  discriminate.
 apply sqrt_wd.
 rstepl ((inj_Q IR (2#1))[*](inj_Q IR (2#1))).
 apply eq_symmetric.
 apply (inj_Q_mult IR (2#1) (2#1)).
Qed.

Lemma rational_sqrt_big_bounded_correct : forall n a Ha H,
 (@rational_sqrt_big_bounded n a Ha == IRasCR (sqrt (inj_Q IR a) H))%CR.
Proof.
 induction n.
  intros a Ha H.
  simpl.
  rewrite <- IR_inj_Q_as_CR.
  apply IRasCR_wd.
  assert (X:[0][<=](inj_Q IR 1:IR)[^]2) by apply sqr_nonneg.
  stepl (sqrt _ X).
   apply sqrt_wd.
   rstepl (inj_Q IR 1[*]inj_Q IR 1).
   stepl (inj_Q IR (1*1)); [| now apply (inj_Q_mult IR)].
   apply inj_Q_wd.
   simpl.
   rewrite -> Qeq_le_def.
   assumption.
  apply sqrt_to_nonneg.
  stepr (nring 1:IR); [| now (apply eq_symmetric; apply (inj_Q_nring IR 1))].
  rstepr ([1]:IR).
  apply less_leEq; apply pos_one.
 intros a Ha H.
 simpl.
 destruct (Qle_total a).
  apply rational_sqrt_mid_correct.
 change (scale 2 (rational_sqrt_big_bounded n (a / 4%positive)(rational_sqrt_big_bounded_subproof0 n a Ha q)) ==
   IRasCR (sqrt (inj_Q IR a) H))%CR.
 assert (X:[0][<=]inj_Q IR (a/4%positive)).
  change (a/4%positive) with (a*(1#4)).
  stepr (inj_Q IR a[*]inj_Q IR (1#4)); [| now apply eq_symmetric; apply (inj_Q_mult IR)].
  apply mult_resp_nonneg.
   assumption.
  stepl (inj_Q IR 0); [| now (apply (inj_Q_nring IR 0))].
  apply inj_Q_leEq.
  discriminate.
 set (X0:= (rational_sqrt_big_bounded_subproof0 n a Ha q)).
 rewrite -> (IHn (a/4%positive) X0 X).
 apply rational_sqrt_big_bounded_correct_aux.
Qed.

(** By scaling the other direction we can extend the range down to 4^(-n).
*)
Fixpoint rational_sqrt_small_bounded (n:nat) a (Ha: / (4^n)%Z <= a <= (4#1)) : CR.
 revert a Ha.
 destruct n as [|n].
  clear rational_sqrt_small_bounded.
  refine (@rational_sqrt_mid).
 intros a H.
 destruct (Qle_total a 1).
  refine (scale (1#2) _).
  refine (@rational_sqrt_small_bounded n ((4#1) * a) _).
  clear rational_sqrt_small_bounded.
  abstract ( destruct H; split;[ rewrite -> Zpower_Qpower in *; auto with *;
    replace (Z_of_nat n) with ((S n) + (-1))%Z by (rewrite inj_S; ring);
      rewrite -> Qpower_plus; try discriminate; change (4%positive^(-1)) with (/(4#1));
        rewrite -> Qinv_mult_distr; change ( / / (4#1)) with (4#1); rewrite -> Qmult_comm
          |replace RHS with ((4#1)*1) by constructor];
            (apply: mult_resp_leEq_lft;simpl;[assumption|discriminate])).
 clear rational_sqrt_small_bounded.
 refine (@rational_sqrt_mid a _).
 abstract (destruct H; tauto).
Defined.

Lemma rational_sqrt_small_bounded_correct_aux a X4a Xa :
  (scale (1 # 2)) (IRasCR (sqrt (inj_Q IR (4%positive * a)) X4a))[=]IRasCR (sqrt (inj_Q IR a) Xa).
Proof.
 rewrite <- CRmult_scale.
 rewrite <- IR_inj_Q_as_CR.
 rewrite <- IR_mult_as_CR.
 apply IRasCR_wd.
 assert (X1:[0][<=](inj_Q IR (1#4))).
  stepl (inj_Q IR 0); [| now (apply (inj_Q_nring IR 0))].
  apply inj_Q_leEq.
  discriminate.
 csetoid_replace (inj_Q IR (1#2)) (sqrt _ X1).
  assert (X2:[0][<=](inj_Q IR (1#4)[*]inj_Q IR (4%positive*a))).
   apply mult_resp_nonneg;assumption.
  astepl (sqrt _ X2).
  apply sqrt_wd.
  csetoid_rewrite_rev (inj_Q_mult IR (1#4) (4%positive*a)).
  apply inj_Q_wd.
  simpl.
  field; discriminate.
 change (inj_Q IR (1#4)) with (inj_Q IR ((1#2)[*](1#2))).
 assert (X2:[0][<=](inj_Q IR (1#2))[^]2).
  apply sqr_nonneg.
 stepr (sqrt _ X2).
  apply eq_symmetric; apply sqrt_to_nonneg.
  stepl (inj_Q IR 0); [| now (apply (inj_Q_nring IR 0))].
  apply inj_Q_leEq.
  discriminate.
 apply sqrt_wd.
 rstepl ((inj_Q IR (1#2))[*](inj_Q IR (1#2))).
 apply eq_symmetric.
 apply (inj_Q_mult IR).
Qed.

Lemma rational_sqrt_small_bounded_correct : forall n a Ha H,
 (@rational_sqrt_small_bounded n a Ha == IRasCR (sqrt (inj_Q IR a) H))%CR.
Proof.
 induction n; try apply rational_sqrt_mid_correct.
 intros a Ha H.
 simpl.
 destruct (Qle_total a 1); [| apply rational_sqrt_mid_correct].
 change (scale (1#2) (rational_sqrt_small_bounded n (4%positive*a) (rational_sqrt_small_bounded_subproof n a Ha q)) ==
   IRasCR (sqrt (inj_Q IR a) H))%CR.
 assert (X:[0][<=]inj_Q IR (4%positive*a)).
  stepr (inj_Q IR (4%positive:Q)[*]inj_Q IR a); [| now apply eq_symmetric; apply (inj_Q_mult IR)].
  apply mult_resp_nonneg.
   stepl (inj_Q IR 0); [| now (apply (inj_Q_nring IR 0))].
   apply inj_Q_leEq.
   discriminate.
  assumption.
 set (X0:= (rational_sqrt_small_bounded_subproof n a Ha q)).
 rewrite -> (IHn (4%positive*a) X0 X).
 apply rational_sqrt_small_bounded_correct_aux.
Qed.

(** And hence it is defined for all postive numbers. *)
Definition rational_sqrt_pos a (Ha:0<a) : CR.
Proof.
 destruct (Qle_total 1 a).
  refine (@rational_sqrt_big_bounded _ a _).
  split.
   assumption.
  apply (power4bound a).
 refine (@rational_sqrt_small_bounded _ a _).
 split.
  apply (power4bound' a).
  assumption.
 abstract (apply Qle_trans with 1;[assumption|discriminate]).
Defined.

Lemma rational_sqrt_pos_correct : forall a Ha H,
 (@rational_sqrt_pos a Ha == IRasCR (sqrt (inj_Q IR a) H))%CR.
Proof.
 intros a Ha H.
 unfold rational_sqrt_pos.
 destruct (Qle_total 1 a).
  apply rational_sqrt_big_bounded_correct.
 apply rational_sqrt_small_bounded_correct.
Qed.

(** We define the square root for all nonpositive numbers. *)
Definition rational_sqrt a : CR :=
match (Qlt_le_dec_fast 0 a) with
|left H => rational_sqrt_pos a H
|right _ => 0%CR
end.

Lemma rational_sqrt_correct : forall a H,
 (@rational_sqrt a == IRasCR (sqrt (inj_Q IR a) H))%CR.
Proof.
 intros a H.
 unfold rational_sqrt.
 destruct (Qlt_le_dec_fast 0 a).
  apply rational_sqrt_pos_correct.
 rewrite <- (IR_nring_as_CR 0).
 apply IRasCR_wd.
 simpl.
 assert (X:[0] [<=] ([0][^]2:IR)).
  rstepr ([0]:IR).
  apply leEq_reflexive.
 stepl (sqrt _ X).
  apply sqrt_wd.
  rstepl ([0]:IR).
  apply leEq_imp_eq.
   assumption.
  stepr (inj_Q IR 0); [| now apply (inj_Q_nring IR 0)].
  apply inj_Q_leEq.
  assumption.
 apply sqrt_to_nonneg.
 apply leEq_reflexive.
Qed.

(** Square root is uniformly continuous everywhere. *)
Definition sqrt_modulus (e:Qpos) : QposInf := Qpos2QposInf (e*e).

Lemma sqrt_uc_prf : is_UniformlyContinuousFunction rational_sqrt sqrt_modulus.
Proof.
 intros e a.
 cut (forall a b, (0 <= a) -> (0 <= b) -> ball_ex (X:=Q_as_MetricSpace) (sqrt_modulus e) a b ->
   ball (m:=CR) e (rational_sqrt a) (rational_sqrt b)).
  intros X b Hab.
  destruct (Qle_total 0 a) as [Ha|Ha].
   destruct (Qle_total 0 b) as [Hb|Hb].
    apply X; assumption.
   unfold rational_sqrt at 2.
   destruct (Qlt_le_dec_fast 0 b) as [Z|_].
    elim (Qle_not_lt _ _ Hb Z).
   change 0%CR with (rational_sqrt 0).
   apply X; try assumption.
    apply Qle_refl.
   destruct Hab.
   split; simpl in *.
    rewrite ->  Qle_minus_iff in *.
    replace RHS with ((a + - 0) + (e*e)%Qpos) by simpl; ring.
    Qauto_nonneg.
   rewrite ->  Qle_minus_iff in *.
   replace RHS with ((e*e)%Qpos + - (a - b) + (0 + - b)) by simpl; ring.
   Qauto_nonneg.
  unfold rational_sqrt at 1.
  destruct (Qlt_le_dec_fast 0 a) as [Z0|_].
   elim (Qle_not_lt _ _ Ha Z0).
  change 0%CR with (rational_sqrt 0).
  destruct (Qle_total 0 b) as [Hb|Hb].
   apply X; try assumption.
    apply Qle_refl.
   destruct Hab.
   split; simpl in *.
    rewrite -> Qle_minus_iff in *.
    replace RHS with ((a - b) + - - (e*e)%Qpos + (0 + - a)) by simpl; ring.
    Qauto_nonneg.
   rewrite -> Qle_minus_iff in *.
   replace RHS with ((e*e)%Qpos + (b + - 0)) by simpl; ring.
   Qauto_nonneg.
  unfold rational_sqrt at 2.
  destruct (Qlt_le_dec_fast 0 b) as [Z0|_].
   elim (Qle_not_lt _ _ Hb Z0).
  change 0%CR with (rational_sqrt 0).
  apply ball_refl.
 clear a.
 intros a b Ha Hb Hab.
 assert (Z:[0][<=]inj_Q IR a).
  stepl (inj_Q IR 0); [| now apply (inj_Q_nring IR 0)].
  apply inj_Q_leEq.
  assumption.
 rewrite -> (rational_sqrt_correct _ Z).
 assert (Z0:[0][<=]inj_Q IR b).
  stepl (inj_Q IR 0); [| now apply (inj_Q_nring IR 0)].
  apply inj_Q_leEq.
  assumption.
 rewrite -> (rational_sqrt_correct _ Z0).
 rewrite <- CRAbsSmall_ball.
 cut (AbsSmall (R:=CRasCOrdField) (IRasCR (inj_Q IR (e:Q)))%CR
   (IRasCR (sqrt (inj_Q IR a) Z[-](sqrt (inj_Q IR b) Z0)))).
  intros [A B].
  unfold cg_minus.
  split; (simpl; rewrite <- (IR_inj_Q_as_CR e); rewrite <- (IR_opp_as_CR (sqrt _ Z0));
    rewrite <- (IR_plus_as_CR); assumption).
 rewrite <- IR_AbsSmall_as_CR.
 assert (Z1:AbsSmall (inj_Q IR (e*e)) ((inj_Q IR a)[-](inj_Q IR b))).
  destruct Hab.
  split.
   stepl (inj_Q IR (-(e*e))); [| now apply (inj_Q_inv IR)].
   stepr (inj_Q IR (a - b)); [| now apply (inj_Q_minus IR)].
   apply inj_Q_leEq.
   assumption.
  stepl (inj_Q IR (a - b)); [| now apply (inj_Q_minus IR)].
  apply inj_Q_leEq.
  assumption.
 clear Hab.
 set (e':=(inj_Q IR (e:Q))).
 set (a':=(sqrt (inj_Q IR a) Z)).
 set (b':=(sqrt (inj_Q IR b) Z0)).
 assert (He:[0][<]e').
  stepl (inj_Q IR 0); [| now apply (inj_Q_nring IR 0)].
  apply inj_Q_less.
  simpl; auto with *.
 split.
  refine (mult_cancel_leEq _ _ _ (e'[+]a'[+]b') _ _).
   rstepl ([0][+][0][+][0]:IR).
   do 2 (apply plus_resp_less_leEq; try apply sqrt_nonneg).
   assumption.
  rstepl (([--](e'[*]e'))[+](e')[*]([--]a'[-]b')).
  rstepr ((a'[^]2[-]b'[^]2)[+](e')[*](a'[-]b')).
  apply plus_resp_leEq_both.
   stepr (inj_Q IR a[-]inj_Q IR b).
    stepl ([--](inj_Q IR (e*e))).
     destruct Z1; assumption.
    unfold e'.
    csetoid_rewrite_rev (inj_Q_mult IR (e:Q) (e:Q)).
    apply eq_reflexive.
   unfold a', b'.
   unfold cg_minus.
   csetoid_rewrite (sqrt_sqr (inj_Q IR a) Z).
   csetoid_rewrite (sqrt_sqr (inj_Q IR b) Z0).
   apply eq_reflexive.
  apply mult_resp_leEq_lft;[|apply less_leEq;assumption].
  apply minus_resp_leEq.
  apply shift_leEq_rht.
  rstepr (Two[*]a').
  apply mult_resp_nonneg.
   apply less_leEq; apply pos_two.
  apply sqrt_nonneg.
 refine (mult_cancel_leEq _ _ _ (e'[+]a'[+]b') _ _).
  rstepl ([0][+][0][+][0]:IR).
  do 2 (apply plus_resp_less_leEq; try apply sqrt_nonneg).
  assumption.
 rstepr (((e'[*]e'))[+](e')[*](a'[+]b')).
 rstepl ((a'[^]2[-]b'[^]2)[+](e')[*](a'[-]b')).
 apply plus_resp_leEq_both.
  stepl (inj_Q IR a[-]inj_Q IR b).
   stepr (inj_Q IR (e*e)).
    destruct Z1; assumption.
   unfold e'.
   csetoid_rewrite_rev (inj_Q_mult IR (e:Q) (e:Q)).
   apply eq_reflexive.
  unfold a', b'.
  unfold cg_minus.
  csetoid_rewrite (sqrt_sqr (inj_Q IR a) Z).
  csetoid_rewrite (sqrt_sqr (inj_Q IR b) Z0).
  apply eq_reflexive.
 apply mult_resp_leEq_lft;[|apply less_leEq;assumption].
 unfold cg_minus.
 apply plus_resp_leEq_lft.
 apply shift_leEq_rht.
 rstepr (Two[*]b').
 apply mult_resp_nonneg.
  apply less_leEq; apply pos_two.
 apply sqrt_nonneg.
Qed.

Open Local Scope uc_scope.

Definition sqrt_uc : Q_as_MetricSpace --> CR :=
Build_UniformlyContinuousFunction sqrt_uc_prf.

Definition CRsqrt : CR --> CR := Cbind QPrelengthSpace sqrt_uc.

Lemma CRsqrt_correct : forall x H,
 (IRasCR (sqrt x H) == CRsqrt (IRasCR x))%CR.
Proof.
 intros x H.
 assert (X:Dom (FNRoot FId 2 (lt_O_Sn 1)) x).
  simpl; split; auto.
 transitivity (IRasCR (FNRoot FId 2 (lt_O_Sn 1) x X)).
  apply IRasCR_wd.
  apply: NRoot_wd.
  apply eq_reflexive.
 apply (ContinuousCorrect (I:proper (closel [0]))); try assumption.
  apply Continuous_NRoot.
   Contin.
  intros; assumption.
 intros q Hq Y.
 transitivity (rational_sqrt q);[|apply: rational_sqrt_correct].
 unfold CRsqrt.
 rewrite -> (Cbind_correct QPrelengthSpace sqrt_uc ('q)%CR).
 apply: BindLaw1.
Qed.
(* begin hide *)
Hint Rewrite CRsqrt_correct : IRtoCR.
(* end hide *)

Lemma CRsqrt_Qsqrt : forall x : Q, (CRsqrt ('x) == rational_sqrt x)%CR.
Proof.
 intros x.
 unfold CRsqrt.
 rewrite -> (Cbind_correct QPrelengthSpace sqrt_uc (' x))%CR.
 apply: BindLaw1.
Qed.

Instance: Proper ((=) ==> (=)) rational_sqrt.
Proof.
  intros x1 x2 E.
  rewrite <-2!CRsqrt_Qsqrt.
  now rewrite E.
Qed.

Lemma rational_sqrt_nonpos (a : Q) :
  a ≤ 0 → rational_sqrt a = 0%CR.
Proof.
 intros. unfold rational_sqrt.
 case Qlt_le_dec_fast; intros; [|reflexivity].
 edestruct Qle_not_lt; eassumption.
Qed.

Lemma rational_sqrt_unique (a : Q) (y : CR) :
  0 ≤ a → CRpower_N y 2 = 'a → 0%CR ≤ y → y = rational_sqrt a.
Proof.
 intros.
 assert (Pa : [0][<=](inj_Q IR a)).
  stepl (inj_Q IR 0); [| now (apply (inj_Q_nring IR 0))].
  now apply inj_Q_leEq.
 rewrite (rational_sqrt_correct _ Pa).
 now apply rational_sqrt_mid_correct_aux.
Qed.

Lemma rational_sqrt_scale (n : Z) a : 
  0 ≤ a → scale ((2#1) ^ n) (rational_sqrt (a * (4#1) ^ (-n))) = rational_sqrt a.
Proof.
 intros E.
 rewrite <-CRmult_scale.
 revert n. apply biinduction.
   solve_proper. 
  simpl. rewrite Qmult_1_r.
  now ring_simplify.
 intros n.
 setoid_replace ('((2#1) ^ (1 + n)) * rational_sqrt (a * (4#1) ^ -(1 + n)))%CR
    with ('((2#1) ^ n) * scale (2#1) (rational_sqrt ((a * (4#1) ^ -n) / (4#1))))%CR.
  assert (Pa1 : [0][<=](inj_Q IR (a * (4#1) ^ (- n)))).
   stepl (inj_Q IR 0); [| now (apply (inj_Q_nring IR 0))].
   apply inj_Q_leEq.
   apply Qmult_le_0_compat; [assumption|].
   now apply Qpower_pos.
  assert (Pa2 : [0][<=](inj_Q IR (a * (4#1) ^ (- n) / (4 # 1)))).
   stepl (inj_Q IR 0); [| now (apply (inj_Q_nring IR 0))].
   apply inj_Q_leEq.
   apply Qmult_le_0_compat; [|easy].
   apply Qmult_le_0_compat; [assumption|].
   now apply Qpower_pos.
  rewrite (rational_sqrt_correct _ Pa1), (rational_sqrt_correct _ Pa2).
  split; intros E2; rewrite <-E2; now rewrite rational_sqrt_big_bounded_correct_aux.
 rewrite Zopp_plus_distr.
 rewrite <-CRmult_scale.
 rewrite 2!Qpower_plus by discriminate.
 simpl.
 rewrite (Qmult_comm (2#1) ((2#1) ^ n)), <-CRmult_Qmult.
 rewrite (Qmult_comm (/(4#1))), Qmult_assoc.
 symmetry. apply associativity.
Qed.
