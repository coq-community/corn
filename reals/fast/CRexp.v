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

Require Import QMinMax.
Require Import CRAlternatingSum.
Require Import CRseries.
Require Export CRArith.
Require Import CRIR.
Require Import iso_CReals.
Require Import Qpower.
Require Import COrdFields2.
Require Import Qordfield.
Require Import PowerSeries.
Require Import CRpower.
Require Import Exponential.
Require Import RealPowers.
Require Import Compress.
Require Import Ndigits.
Require Import ModulusDerivative.
Require Import ContinuousCorrect.
Require Import CRsign.
Require Import Q_in_CReals.
Require Import Qround.
Require Import CornTac.

Set Implicit Arguments.

Opaque CR.
Opaque Exp.

Open Local Scope Q_scope.
Open Local Scope uc_scope.

(**
** Exponential
[exp] is implement by its alternating Taylor's series.
*)

Section ExpSeries.
Variable a:Q.

Definition expSequence := mult_Streams recip_factorials (powers a).

Lemma Str_nth_expSequence : forall n, (Str_nth n expSequence == (1#P_of_succ_nat (pred (fac n)))*a^n)%Q.
Proof.
intros n.
unfold expSequence.
unfold mult_Streams.
rewrite Str_nth_zipWith.
rewrite Str_nth_powers.
rewrite Str_nth_recip_factorials.
reflexivity.
Qed.

(** The exponential is first defined on [[-1,0]]. *)
Hypothesis Ha: 0 <= a <= 1.

Lemma expSequence_dnn : DecreasingNonNegative expSequence.
Proof.
apply mult_Streams_dnn.
apply recip_factorials_dnn.
apply powers_dnn.
assumption.
Qed.

Lemma expSequence_zl : Limit expSequence 0.
Proof.
apply: mult_Streams_zl.
apply recip_factorials_zl.
apply powers_nbz.
assumption.
Defined.

End ExpSeries.

Lemma exp_ps_correct : forall a (n:nat) H, 
  inj_Q IR ((((-(1))^n)*Str_nth n (expSequence (-a)))%Q)[=]Exp_ps n (inj_Q IR a) H.
Proof.
intros a n H.
stepr (inj_Q IR ((1 # P_of_succ_nat (pred (fac n))) * a ^ n)%Q).
apply inj_Q_wd;simpl.
rewrite Str_nth_expSequence.
setoid_replace (a^n)%Q with ((-(1))^n*(-a)^n)%Q.
ring.
 rewrite <- Qmult_power.
 setoid_replace (- (1) * - a) with a by ring.
 reflexivity.
generalize H; clear H.
induction n.

intros H.
simpl.
unfold pring.
simpl.
rational.

intros H.
stepl ((One[/](nring (S n))[//]nringS_ap_zero IR n)[*](inj_Q IR a)[*]Exp_ps n (inj_Q IR a) H).

simpl.
change (nring (R:=IR) n[+]One) with (nring (R:=IR) (S n)).
rstepl (((One[/]nring (R:=IR) (S n)[//]nringS_ap_zero IR n)[*]
(One[/]nring (R:=IR) (fac n)[//]nring_fac_ap_zero IR n))[*]
 (nexp IR n (inj_Q IR a[-]Zero)[*]inj_Q IR a)).
apply mult_wd;[|rational].
assert (X:=(mult_resp_ap_zero _ _ _ (nringS_ap_zero IR n) (nring_fac_ap_zero IR n))).
rstepl (One[/]((nring (R:=IR) (S n))[*]nring (R:=IR) (fac n))[//]X).
apply div_wd;[rational|].
apply eq_symmetric.
change (fac n + n * fac n)%nat with (S n*(fac n))%nat.
apply nring_comm_mult.

stepl (inj_Q IR ((1#(P_of_succ_nat n))*a*((1 # P_of_succ_nat (pred (fac n))) * a ^ n))%Q).
apply inj_Q_wd.
change ((1 # P_of_succ_nat n) * a * ((1 # P_of_succ_nat (pred (fac n))) * a ^ n) ==
 (1 # P_of_succ_nat (pred (S n * fac n))) * a ^ S n)%Q.
replace (P_of_succ_nat (pred (S n * fac n))%nat) with 
 (P_of_succ_nat (pred (S n)) * P_of_succ_nat (pred (fac n)))%positive.
rewrite <- pred_Sn.
rewrite inj_S.
unfold Zsucc.
rewrite Qpower_plus'; auto with *.
change ((1 # P_of_succ_nat n * P_of_succ_nat (pred (fac n))%positive))%Q
 with ((1 # P_of_succ_nat n) * (1#P_of_succ_nat (pred (fac n))))%Q.
ring.
apply nat_of_P_inj.
rewrite nat_of_P_mult_morphism.
repeat rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
rewrite <- pred_Sn.
rewrite S_predn.
rewrite S_predn.
reflexivity.

cut (0 < S n * fac n)%nat;[auto with *|apply (nat_fac_gtzero (S n))].
cut (0 < fac n)%nat;[auto with *|apply (nat_fac_gtzero n)].

stepl ((One[/]nring (R:=IR) (S n)[//]nringS_ap_zero IR n)[*]inj_Q IR a[*]
 inj_Q IR ((1 # P_of_succ_nat (pred (fac n))) * a ^ n)%Q);
 [apply mult_wdr; apply IHn|].
apply eq_symmetric.
eapply eq_transitive;[apply inj_Q_mult|].
eapply eq_transitive;[apply mult_wdl;apply inj_Q_mult|].
apply mult_wdl.
apply mult_wdl.
change (1 # P_of_succ_nat n)%Q with (1/P_of_succ_nat n)%Q.
assert (A:inj_Q IR ((P_of_succ_nat n):Q)[=]nring (S n)).
stepl (inj_Q IR (nring (S n))).
apply inj_Q_nring.
apply inj_Q_wd.
simpl.
clear - n.
induction n.
reflexivity.
simpl.
rewrite IHn.
unfold Qeq.
simpl.
rewrite Pplus_one_succ_r.
repeat (rewrite Zpos_mult_morphism || rewrite Zpos_plus_distr).
ring.

assert (B:inj_Q IR (P_of_succ_nat n:Q)[#]Zero).
stepl (nring (R:=IR) (S n)).
apply nringS_ap_zero.
apply eq_symmetric;assumption.
eapply eq_transitive;[apply inj_Q_div|].
instantiate (1:=B).
apply div_wd.
rstepr (Zero[+]One:IR).
apply (inj_Q_nring IR 1).
assumption.
Qed.

Lemma Qle_ZO_flip : forall a, -(1) <= a <= 0 -> 0 <= (-a) <= 1.
Proof.
intros a [H0 H1].
auto with *.
split.
change 0 with (-0).
apply Qopp_le_compat.
assumption.
change 1 with (- (-(1))).
apply Qopp_le_compat.
assumption.
Qed.

Definition rational_exp_small_neg (a:Q) (p:-(1) <= a <= 0) : CR 
:= let p':= (Qle_ZO_flip p) in InfiniteAlternatingSum (expSequence_dnn p') (expSequence_zl p').

Lemma rational_exp_small_neg_correct : forall (a:Q) Ha,
 (@rational_exp_small_neg a Ha == IRasCR (Exp (inj_Q IR a)))%CR.
Proof.
intros a Ha.
unfold rational_exp_small_neg.
apply: InfiniteAlternatingSum_correct.
intros n.
clear Ha.
apply exp_ps_correct.
Qed.

(** exp is extended to work on [[-2^n, 0]] for all n. *)
Lemma shrink_by_two : forall n a, (-(2^(S n)))%Z <= a <= 0 -> (-(2^n))%Z <= (a/2) <= 0.
Proof.
intros n a [H0 H1].
split.
 apply Qmult_lt_0_le_reg_r with 2.
  constructor.
 change ((-(2 ^ n)%Z) * 2 <= a / 2 * 2).
 rewrite Zpower_Qpower; auto with *.
 rewrite (inj_S n) in H0.
 replace LHS with (-(2%positive^n*2^1)) by ring.
 rewrite <- Qpower_plus;[|discriminate].
 replace RHS with a by (field; discriminate).
 change (- (2 ^ Zsucc n)%Z <= a) in H0.
 rewrite ->  Zpower_Qpower in H0.
  assumption.
 auto with *.
apply: (fun a b => mult_cancel_leEq _ a b (2:Q));simpl.
 constructor.
replace LHS with a by (field; discriminate).
replace RHS with 0 by ring.
assumption.
Qed.

Fixpoint rational_exp_neg_bounded (n:nat) (a:Q) : (-(2^n))%Z <= a <= 0 -> CR :=
match n return (-(2^n))%Z <= a <= 0 -> CR with
| O => @rational_exp_small_neg a
| S n' =>
  match (Qlt_le_dec_fast a (-(1))) with
  | left _ => fun H => CRpower_positive_bounded 2 (1#1) (compress (rational_exp_neg_bounded n' (shrink_by_two n' H)))
  | right H' => fun H => rational_exp_small_neg (conj H' (proj2 H))
  end
end.

(** [exp] works on all nonpositive numbers. *)
Lemma rational_exp_neg_bounded_correct : forall n (a:Q) Ha,
 (@rational_exp_neg_bounded n a Ha == IRasCR (Exp (inj_Q IR a)))%CR.
Proof.
unfold rational_exp_neg_bounded.
induction n.
 apply rational_exp_small_neg_correct.
intros a Ha.
destruct (Qlt_le_dec_fast a (- (1))).
 rewrite IHn.
 clear IHn.
 rewrite compress_correct.
 rewrite <- CRpower_positive_bounded_correct.
  apply IRasCR_wd.
  set (a':=inj_Q IR (a/2)).
  simpl. 
  rstepl (Exp a'[*]Exp a').
  stepl (Exp (a'[+]a')) by apply Exp_plus.
  apply Exp_wd.
  unfold a'.
  eapply eq_transitive.
   apply eq_symmetric; apply (inj_Q_plus IR).
  apply inj_Q_wd.
  simpl.
  field; discriminate.
 apply leEq_imp_AbsSmall.
  apply less_leEq; apply Exp_pos.
 stepr (One:IR).
  apply Exp_leEq_One.
  stepr (inj_Q IR 0) by apply (inj_Q_nring IR 0).
  apply inj_Q_leEq.
  apply mult_cancel_leEq with (2:Q).
   constructor.
  change (a/2*2<=0).
  replace LHS with a by (field; discriminate).
  apply Qle_trans with (-(1)); try discriminate.
  apply Qlt_le_weak.
  assumption. 
 rstepl (nring 1:IR).
 apply eq_symmetric; apply (inj_Q_nring IR 1).
apply rational_exp_small_neg_correct.
Qed.

Lemma rational_exp_bound_power_2 : forall (a:Q), a <= 0 -> (-2^(Z_of_nat match (Qnum a) with |Z0 => O | Zpos x => Psize x | Zneg x => Psize x end))%Z <= a.
Proof.
intros [[|n|n] d] Ha;
simpl.
  discriminate.
 elim Ha.
 reflexivity.
rewrite Qle_minus_iff.
change (0<=(-(n#d) + - (-2^Psize n)%Z)).
rewrite Qplus_comm.
rewrite <- Qle_minus_iff.
change (n # d <= - - (2 ^ Psize n)%Z).
replace RHS with ((2^Psize n)%Z:Q) by ring.
unfold Qle.
simpl.
change (n * 1 <= 2 ^ Psize n * d)%Z.
apply Zmult_le_compat; try auto with *.
clear - n.
apply Zle_trans with (n+1)%Z.
 auto with *.
induction n.
  change (Psize (xI n)) with (1 + (Psize n))%nat.
  rewrite inj_plus.
  rewrite Zpower_exp; try auto with *.
  rewrite Zpos_xI.
  replace LHS with (2*(n+1))%Z by ring.
  apply Zmult_le_compat; auto with *.
 change (Psize (xO n)) with (1 + (Psize n))%nat.
 rewrite inj_plus.
 rewrite Zpower_exp; try auto with *.
 rewrite Zpos_xO.
 apply Zle_trans with (2*(n+1))%Z.
  auto with *.
 apply Zmult_le_compat; auto with *.
discriminate.
Qed.

Definition rational_exp_neg (a:Q) : a <= 0 -> CR.
intros a Ha.
refine (@rational_exp_neg_bounded _ a _).
split.
 apply (rational_exp_bound_power_2 Ha).
apply Ha.
Defined.

Lemma rational_exp_neg_correct : forall (a:Q) Ha,
 (@rational_exp_neg a Ha == IRasCR (Exp (inj_Q IR a)))%CR.
Proof.
intros a Ha.
apply rational_exp_neg_bounded_correct.
Qed.
(** exp(x) is bounded below by (3^x) for x nonpositive, and hence
exp(x) is positive. *)
Lemma minus_one_works_for_rational_exp_small_neg : -(1) <= -(1) <= 0.
Proof.
constructor; discriminate.
Qed.

Lemma rational_exp_small_neg_posH : forall (a:Q) (p:-(1) <= a <= 0),
 ('(1#3) <= rational_exp_small_neg p)%CR.
Proof.
intros a p.
apply CRle_trans with (rational_exp_small_neg minus_one_works_for_rational_exp_small_neg).
unfold CRle.
apply CRpos_nonNeg.
CR_solve_pos (1#1)%Qpos.
do 2 rewrite (rational_exp_small_neg_correct).
rewrite <- IR_leEq_as_CR.
apply Exp_resp_leEq.
apply inj_Q_leEq.
destruct p; assumption.
Qed.

Lemma rational_exp_neg_posH : forall (n:nat) (a:Q) Ha, (-n <= a) ->
 ('((1#3)^n) <= @rational_exp_neg a Ha)%CR.
Proof.
intros n a Ha Hn.
rewrite rational_exp_neg_correct.
rewrite <- IR_inj_Q_as_CR.
rewrite <- IR_leEq_as_CR.
stepl (inj_Q IR (1#3)[^]n) by (apply eq_symmetric; apply inj_Q_power).
assert (X:Zero[<]inj_Q IR (1#3)).
 stepl (inj_Q IR 0) by apply (inj_Q_nring IR 0).
 apply inj_Q_less.
 constructor.
astepl (inj_Q IR (1#3)[!](nring n)[//]X).
unfold power.
apply Exp_resp_leEq.
destruct n.
 rstepl (Zero:IR).
 stepl (inj_Q IR 0) by apply (inj_Q_nring IR 0).
 apply inj_Q_leEq.
 assumption.
apply (fun a b => (shift_mult_leEq' _ a b _ (nringS_ap_zero IR n))).
 apply nring_pos; auto with *.
stepr (inj_Q IR (a/(S n))).
 apply Exp_cancel_leEq.
 astepl (inj_Q IR (1#3)).
 rewrite IR_leEq_as_CR.
 rewrite IR_inj_Q_as_CR.
 assert (Ha0 : -(1)<=(a/S n)<=0).
  split.
   rewrite Qle_minus_iff.
   replace RHS with ((a + S n)*(1/(S n))) by (field;discriminate).
   replace LHS with (0*(1/(S n))) by ring.
   apply: mult_resp_leEq_rht;simpl.
    replace RHS with (a + - (- (P_of_succ_nat n))) by ring.
    rewrite <- Qle_minus_iff.
    assumption.
   rewrite <- (Qmake_Qdiv 1 (P_of_succ_nat n)).
   discriminate.
  replace RHS with (0*(1/(S n))) by ring.
  apply: mult_resp_leEq_rht;simpl.
   assumption.
  rewrite <- (Qmake_Qdiv 1 (P_of_succ_nat n)).
  discriminate.
 rewrite <- (rational_exp_small_neg_correct Ha0).
 apply rational_exp_small_neg_posH.
assert (X0:inj_Q IR (inject_Z (S n))[#]Zero).
 stepl (inj_Q IR (nring (S n))).
  stepl (nring (S n):IR) by (apply eq_symmetric; apply (inj_Q_nring IR (S n))).
  apply (nringS_ap_zero).
 apply inj_Q_wd.
 apply nring_Q.
stepl (inj_Q IR a[/]_[//]X0).
 apply div_wd.
  apply eq_reflexive.
 stepl (inj_Q IR (nring (S n))).
  apply inj_Q_nring.
 apply inj_Q_wd.
 apply nring_Q.
apply eq_symmetric.
apply inj_Q_div.
Qed.

Lemma rational_exp_neg_posH' : forall (a:Q) Ha,
 ('((3#1)^(Zdiv (Qnum a) (Qden a)))%Qpos <= @rational_exp_neg a Ha)%CR.
Proof.
intros [n d] Ha.
simpl.
assert (X1:(d > 0)%Z) by auto with *.
assert (X:n = (d * (n / d) + n mod d)%Z).
 apply Z_div_mod_eq.
 assumption.
set (c:=(n/d)%Z) in *.
assert (X0:(0 <= -c)%Z).
 apply Zmult_le_0_reg_r with d.
  auto with *.
 replace RHS with (-(d*c))%Z by ring.
 change (-(d*c))%Z with (0-(d*c))%Z.
 rewrite <- Zle_plus_swap.
 replace LHS with (d*c + 0)%Z by ring.
 apply Zle_trans with n.
  rewrite X.
  apply Zplus_le_compat_l.
  destruct (Z_mod_lt n _ X1).
  assumption.
 unfold Qle in Ha.
 simpl in Ha.
 replace LHS with (n*1)%Z by ring.
 assumption.
setoid_replace (QposAsQ ((3#1)^c)%Qpos) with ((1#3)^(Z_to_nat X0)).
 apply rational_exp_neg_posH.
 rewrite <- (Z_to_nat_correct X0).
 unfold Qle.
 simpl.
 rewrite X.
 replace LHS with (d*c + 0)%Z by ring.
 replace RHS with (d*c + n mod d)%Z by ring.
 apply Zplus_le_compat_l.
 destruct (Z_mod_lt n _ X1).
 assumption.
rewrite <- Z_to_nat_correct.
rewrite Q_Qpos_power.
change (1#3) with (/3).
rewrite Qinv_power.
rewrite <- Qpower_opp.
replace (- - c)%Z with c by ring.
reflexivity.
Qed.

Lemma rational_exp_neg_pos : forall (a:Q) Ha,
 CRpos (@rational_exp_neg a Ha).
Proof.
intros a Ha.
exists ((3#1)^(Zdiv (Qnum a) (Qden a)))%Qpos.
apply rational_exp_neg_posH'.
Defined.

(** exp is extended to all numbers by saying exp(x) = 1/exp(-x) when x
is positive. *)
Definition rational_exp (a:Q) : CR.
intros a.
destruct (Qle_total 0 a).
refine (CRinv_pos ((3#1)^(Zdiv (Qnum (- a)) (Qden (- a))))%Qpos (@rational_exp_neg (-a) _)).
apply (Qopp_le_compat 0); assumption.
apply (rational_exp_neg q).
Defined.

Lemma rational_exp_correct : forall (a:Q),
 (rational_exp a == IRasCR (Exp (inj_Q IR a)))%CR.
Proof.
intros a.
unfold rational_exp.
destruct (Qle_total 0 a); try apply rational_exp_neg_correct.
assert (X0:=rational_exp_neg_correct (Qopp_le_compat 0 a q)).
rewrite X0.
assert (X:((IRasCR (Exp (inj_Q IR (- a)%Q)) >< '0)%CR)).
 cut (rational_exp_neg (Qopp_le_compat 0 a q) >< ' 0)%CR.
 apply CRapart_wd; assumption || reflexivity.
 right.
 exists ((3 # 1) ^ (Qnum (-a) / Qden (-a)))%Qpos. 
 ring_simplify.
 apply rational_exp_neg_posH'.
rewrite (@CRinv_pos_inv ((3 # 1) ^ (Qnum (-a) / Qden (-a))) _ X);
 [|rewrite <- X0; apply rational_exp_neg_posH'].
rewrite <- IR_recip_as_CR_2.
apply IRasCR_wd.
apply eq_symmetric.
eapply eq_transitive;[|apply div_wd; apply eq_reflexive].
apply Exp_inv'.
rstepl ([--][--](inj_Q IR a)).
csetoid_rewrite_rev (inj_Q_inv IR a).
apply eq_reflexive.
Qed.

(**
*** e
*)
Definition CRe : CR := rational_exp 1.

Lemma CRe_correct : (CRe == IRasCR E)%CR.
Proof.
unfold CRe.
rewrite rational_exp_correct.
apply IRasCR_wd.
csetoid_replace (inj_Q IR 1) (One:IR).
 algebra.
rstepr (nring 1:IR).
apply (inj_Q_nring IR 1).
Qed.

Hint Rewrite <- CRe_correct : IRtoCR.

Opaque inj_Q.

(** [exp] is uniformly continuous below any given integer. *)
Definition exp_bound (z:Z) : Qpos :=
(match z with
 |Z0 => 1#1
 |Zpos p => (3#1)^p
 |Zneg p => (1#2)^p
 end)%Qpos.

Lemma exp_bound_bound : forall (z:Z) x, closer (inj_Q IR (z:Q)) x -> AbsIR (Exp x)[<=]inj_Q IR (exp_bound z:Q).
Proof.
intros [|z|z]; simpl; intros x Hx; 
 apply AbsSmall_imp_AbsIR; 
 (apply leEq_imp_AbsSmall;[apply less_leEq; apply Exp_pos|]).
  stepr (One:IR).
   apply Exp_leEq_One.
   stepr (inj_Q IR (0%Z:Q)).
    assumption.
   apply (inj_Q_nring IR 0).
  rstepl (nring 1:IR).
  apply eq_symmetric; apply (inj_Q_nring IR 1).
 apply leEq_transitive with (Exp (Max x Zero)).
  apply Exp_resp_leEq.
  apply lft_leEq_Max.
 stepr (Three[!](inj_Q IR (z:Q))[//](pos_three IR):IR).
  astepl (E[!](Max x Zero)[//]pos_E).
  apply real_power_resp_leEq_both;
     try solve [IR_solve_ineq (1#1)%Qpos].
   apply rht_leEq_Max.
  apply Max_leEq; auto.
  stepl (inj_Q IR 0).
   apply inj_Q_leEq.
   simpl; auto with *.
  apply (inj_Q_nring IR 0).
 stepl (Three[!]nring (nat_of_P z)[//]pos_three IR).
  astepl (Three[^](nat_of_P z):IR).
  stepl ((inj_Q IR (3:Q))[^](nat_of_P z)).
   stepl (inj_Q IR (3^z)).
    apply inj_Q_wd.
    apply eq_symmetric.
    apply Q_Qpos_power.
   rewrite <- convert_is_POS.
   apply inj_Q_power.
  apply nexp_wd.
  apply (inj_Q_nring IR 3).
 apply power_wd.
  apply eq_reflexive.
 apply eq_symmetric.
 rewrite <- convert_is_POS.
 stepl (inj_Q IR (nring (nat_of_P z))).
  apply (inj_Q_nring).
 apply inj_Q_wd; apply nring_Q.

stepr (Half[!](inj_Q IR (z:Q))[//](pos_half IR):IR).
 astepl (Exp [--][--]x).
 astepl (One[/]_[//](Exp_ap_zero [--]x)).
 unfold Half.
 astepr ((One[!]inj_Q IR (z:Q)[//]pos_one _)[/]((Two[!]inj_Q IR (z:Q)[//]pos_two _))[//]power_ap_zero _ _ _).
 astepr (One[/]((Two[!]inj_Q IR (z:Q)[//]pos_two _))[//]power_ap_zero _ _ _).
 apply recip_resp_leEq.
  apply power_pos.
 astepr (E[!][--]x[//]pos_E).
 apply real_power_resp_leEq_both;
     try solve [IR_solve_ineq (1#1)%Qpos].
  stepl (inj_Q IR 0).
   apply inj_Q_leEq.
   simpl; auto with *.
  apply (inj_Q_nring IR 0).
 rstepl ([--][--](inj_Q IR (z:Q))).
 apply inv_resp_leEq.
 stepr (inj_Q IR ((Zneg z):Q)).
  assumption.
 astepr (inj_Q IR ([--](z:Q))).
 apply inj_Q_wd.
 simpl; reflexivity.
stepl (Half[!]nring (nat_of_P z)[//]pos_half IR).
 astepl (Half[^](nat_of_P z):IR).
 stepl ((inj_Q IR ((1#2):Q))[^](nat_of_P z)).
  stepl (inj_Q IR ((1#2)^z)).
   apply inj_Q_wd.
   apply eq_symmetric.
   apply Q_Qpos_power.
  rewrite <- (convert_is_POS z).
  apply inj_Q_power.
 apply nexp_wd.
 assert (X:(inj_Q IR (2:Q))[#]Zero).
  stepr (inj_Q IR 0).
   apply inj_Q_ap; discriminate.
  apply (inj_Q_nring IR 0).
 stepr ((inj_Q IR 1)[/]_[//]X).
  stepl (inj_Q IR (1/2)).
   apply inj_Q_div.
  apply inj_Q_wd.
  apply eq_symmetric; apply Qmake_Qdiv.
 apply div_wd.
  rstepr (nring 1:IR).
  apply (inj_Q_nring IR 1).
 apply (inj_Q_nring IR 2).
apply power_wd.
 apply eq_reflexive.
apply eq_symmetric.
rewrite <- convert_is_POS.
stepl (inj_Q IR (nring (nat_of_P z))).
 apply (inj_Q_nring).
apply inj_Q_wd; apply nring_Q.
Qed. 

Lemma exp_bound_uc_prf : forall z:Z, is_UniformlyContinuousFunction (fun a => rational_exp (Qmin z a)) (Qscale_modulus (exp_bound z)).
Proof.
intros z.
assert (Z:Derivative (closer (inj_Q IR (z:Q))) CI Expon Expon).
 apply (Included_imp_Derivative realline CI).
  Deriv.
 Included.
apply (is_UniformlyContinuousD None (Some (z:Q)) I _ _ Z).
 intros q [] H.
 apply rational_exp_correct.
intros x [] H.
apply: exp_bound_bound.
assumption.
Qed.

Definition exp_bound_uc (z:Z) :  Q_as_MetricSpace --> CR :=
Build_UniformlyContinuousFunction (@exp_bound_uc_prf z).

(** [exp] for any real number upto a given integer. *)
Definition exp_bounded (z:Z) : CR --> CR := (Cbind QPrelengthSpace (exp_bound_uc z)).

Lemma exp_bounded_correct : forall (z:Z) x, closer (inj_Q _ (z:Q)) x -> (IRasCR (Exp x)==exp_bounded z (IRasCR x))%CR.
Proof.
intros z x Hx.
assert (Z:Continuous (closer (inj_Q IR (z:Q))) Expon).
 apply (Included_imp_Continuous realline).
  Contin.
 Included.
apply (fun a b c => @ContinuousCorrect _ a Expon Z b c x CI); auto with *.
 constructor.
intros q [] H.
transitivity (exp_bound_uc z q);[|].
 change (' q)%CR with (Cunit_fun _ q).
 unfold exp_bounded.
 rewrite (Cbind_correct QPrelengthSpace (exp_bound_uc z) (Cunit_fun Q_as_MetricSpace q)).
 apply: BindLaw1.
change (rational_exp (Qmin z q) == IRasCR (Exp (inj_Q IR q)))%CR.
rewrite rational_exp_correct.
apply IRasCR_wd.
apply Exp_wd.
apply inj_Q_wd.
simpl.
rewrite <- Qle_min_r.
apply leEq_inj_Q with IR.
assumption.
Qed.

(** exp on all real numbers.  [exp_bounded] should be used instead when [x]
is known to be bounded by some intenger. *)
Definition exp (x:CR) : CR := exp_bounded (Qceiling (approximate x ((1#1)%Qpos) + (1#1))) x.
(* begin hide *)
Implicit Arguments exp [].
(* end hide *)
Lemma exp_bound_lemma : forall x : CR, (x <= ' (approximate x (1 # 1)%Qpos + 1))%CR.
Proof.
intros x.
assert (X:=ball_approx_l x (1#1)).
rewrite <- CRAbsSmall_ball in X.
destruct X as [X _].
simpl in X.
rewrite <- CRplus_Qplus.
apply CRle_trans with (doubleSpeed x).
 rewrite (doubleSpeed_Eq x); apply CRle_refl.
intros e.
assert (Y:=X e).
simpl in *.
do 2 (unfold Cap_raw in *; simpl in *).
replace RHS with (approximate x (1 # 1)%Qpos +
    - approximate x ((1 # 2) * ((1 # 2) * e))%Qpos + - - (1 # 1)%Qpos)
 by QposRing.
assumption.
Qed.

Lemma exp_correct : forall x, (IRasCR (Exp x)==exp (IRasCR x))%CR.
Proof.
intros x.
unfold exp.
apply exp_bounded_correct.
simpl.
apply leEq_transitive with (inj_Q IR ((approximate (IRasCR x) (1 # 1)%Qpos + 1)));
 [|apply inj_Q_leEq; simpl;auto with *].
rewrite IR_leEq_as_CR.
rewrite IR_inj_Q_as_CR.
apply exp_bound_lemma.
Qed.
(* begin hide *)
Hint Rewrite exp_correct : IRtoCR.
(* end hide *)
Lemma exp_bound_exp : forall (z:Z) (x:CR),
 (x <= 'z ->
  exp_bounded z x == exp x)%CR.
Proof.
intros z x H.
unfold exp.
set (a:=(approximate x (1 # 1)%Qpos + 1)).
rewrite <- (CRasIRasCR_id x).
rewrite <- exp_bounded_correct.
 rewrite <- exp_bounded_correct.
  reflexivity.
 change (CRasIR x [<=] inj_Q IR (Qceiling a:Q)).
 rewrite IR_leEq_as_CR.
 autorewrite with IRtoCR.
 rewrite CRasIRasCR_id.
 apply CRle_trans with ('a)%CR.
  apply exp_bound_lemma.
 rewrite CRle_Qle.
 auto with *.
change (CRasIR x [<=] inj_Q IR (z:Q)).
rewrite IR_leEq_as_CR.
autorewrite with IRtoCR.
rewrite CRasIRasCR_id.
assumption.
Qed.
(* begin hide *)
Add Morphism exp with signature (@st_eq _) ==> (@st_eq _) as exp_wd.
intros x y Hxy.
unfold exp at 1.
set (a :=  (approximate x (1 # 1)%Qpos + 1)).
rewrite Hxy.
apply exp_bound_exp.
rewrite <- Hxy.
apply CRle_trans with ('a)%CR.
 apply exp_bound_lemma.
rewrite CRle_Qle.
auto with *.
Qed.
(* end hide *)
Lemma exp_Qexp : forall x : Q, (exp (' x) == rational_exp x)%CR.
Proof.
intros x.
rewrite <- IR_inj_Q_as_CR.
rewrite <- exp_correct.
rewrite <- rational_exp_correct.
reflexivity.
Qed.
(* begin hide *)
Hint Rewrite exp_Qexp : CRfast_compute.
(* end hide *)