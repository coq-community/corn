(* Copyright © 1998-2006
 * Henk Barendregt
 * Luís Cruz-Filipe
 * Herman Geuvers
 * Mariusz Giero
 * Rik van Ginneken
 * Dimitri Hendriks
 * Sébastien Hinderer
 * Bart Kirkels
 * Pierre Letouzey
 * Iris Loeb
 * Lionel Mamane
 * Milad Niqui
 * Russell O’Connor
 * Randy Pollack
 * Nickolay V. Shmyrev
 * Bas Spitters
 * Dan Synek
 * Freek Wiedijk
 * Jan Zwanenburg
 *
 * This work is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *)

(** printing [!] %\ensuremath{\hat{\ }}% #^# *)
(** printing {!} %\ensuremath{\hat{\ }}% #^# *)

Require Export CoRN.transc.Exponential.

Opaque Expon.

(**
* Arbitrary Real Powers

** Powers of Real Numbers

We now define
$x^y=e^{y\times\log(x)}$#x<sup>y</sup>=e<sup>y*log(x)</sup>#, whenever
[x [>] 0], inspired by the rules for manipulating these expressions.
*)

Definition power x y (Hx : [0] [<] x) := Exp (y[*]Log x Hx).

Notation "x [!] y [//] Hy" := (power x y Hy) (at level 20).

(**
This definition yields a well defined, strongly extensional function
which extends the algebraic exponentiation to an integer power and
still has all the good properties of that operation; when [x [=] e] it
coincides with the exponential function.
*)

Lemma power_wd : forall x x' y y' Hx Hx', x [=] x' -> y [=] y' -> x[!]y[//]Hx [=] x'[!]y'[//]Hx'.
Proof.
 intros.
 unfold power in |- *; algebra.
Qed.

Lemma power_strext : forall x x' y y' Hx Hx', x[!]y[//]Hx [#] x'[!]y'[//]Hx' -> x [#] x' or y [#] y'.
Proof.
 intros.
 cut (Log x Hx [#] Log x' Hx' or y [#] y'). intro H0.
  elim H0; intro H1; [ left | right ]; auto; exact (Log_strext _ _ _ _ H1).
 apply bin_op_strext_unfolded with (cr_mult (c:=IR)).
 astepl (y[*]Log x Hx); astepr (y'[*]Log x' Hx').
 apply Exp_strext; auto.
Qed.

Lemma power_plus : forall x y z Hx, x[!]y[+]z[//]Hx [=] x[!]y[//]Hx[*]x[!]z[//]Hx.
Proof.
 intros.
 unfold power in |- *.
 Step_final (Exp (y[*]Log x Hx[+]z[*]Log x Hx)).
Qed.

Lemma power_inv : forall x y Hx Hxy, x[!] [--]y[//]Hx [=] ([1][/] x[!]y[//]Hx[//]Hxy).
Proof.
 intros; unfold power in |- *.
 rstepr ([1][/] _[//]Exp_ap_zero (y[*]Log x Hx)).
 Step_final (Exp [--] (y[*]Log x Hx)).
Qed.

Hint Resolve power_wd power_plus power_inv: algebra.

Lemma power_minus : forall x y z Hx Hxz, x[!]y[-]z[//]Hx [=] (x[!]y[//]Hx[/] x[!]z[//]Hx[//]Hxz).
Proof.
 intros.
 unfold cg_minus in |- *.
 astepl (x[!]y[//]Hx[*]x[!][--]z[//]Hx).
 rstepr (x[!]y[//]Hx[*] ([1][/] _[//]Hxz)).
 algebra.
Qed.

Lemma power_nat : forall x n Hx, x[!]nring n[//]Hx [=] x[^]n.
Proof.
 intros; unfold power in |- *.
 induction  n as [| n Hrecn].
  simpl in |- *; astepr (Exp [0]); simpl in |- *; algebra.
 simpl in |- *.
 astepr (Exp (nring n[*]Log x Hx) [*]Exp (Log x Hx)).
 astepr (Exp (nring n[*]Log x Hx[+]Log x Hx)).
 simpl in |- *; rational.
Qed.

Hint Resolve power_minus power_nat: algebra.

Lemma power_zero : forall (x : IR) Hx, x[!][0][//]Hx [=] [1].
Proof.
 intros.
 astepl (x[!]nring 0[//]Hx).
 Step_final (x[^]0).
Qed.

Lemma power_one : forall (x : IR) Hx, x[!][1][//]Hx [=] x.
Proof.
 intros.
 astepr (x[^]1).
 astepr (x[!]nring 1[//]Hx).
 simpl in |- *; algebra.
Qed.

Lemma one_power : forall (x : IR) H, [1][!]x[//]H [=] [1].
Proof.
 intros x H.
 unfold power.
 astepl  (Exp (x[*][0])).
 rstepl (Exp ([0])).
 algebra.
Qed.

Hint Resolve power_zero power_one one_power: algebra.

Opaque nexp_op.

Lemma power_int : forall x z Hx Hx', x[!]zring z[//]Hx [=] (x[//]Hx') [^^] (z).
Proof.
 intros; induction  z as [| p| p].
   simpl in |- *.
   Step_final (x[!][0][//]Hx).
  simpl in |- *.
  Step_final (x[!]nring (nat_of_P p) [//]Hx).
 simpl in |- *.
 astepl (x[!][--] (nring (nat_of_P p)) [//]Hx).
 astepl ([1][/] x[!]nring (nat_of_P p) [//]Hx[//]Exp_ap_zero _).
 Step_final ([1][/] x[^]nat_of_P p[//]nexp_resp_ap_zero _ Hx').
Qed.

Hint Resolve power_int: algebra.

Lemma Exp_power : forall (x : IR) He, E[!]x[//]He [=] Exp x.
Proof.
 intros; unfold power in |- *.
 Step_final (Exp (x[*][1])).
Qed.

Lemma mult_power : forall x y z Hx Hy Hxy, (x[*]y) [!]z[//]Hxy [=] x[!]z[//]Hx[*]y[!]z[//]Hy.
Proof.
 intros; unfold power in |- *.
 astepr (Exp (z[*]Log _ Hx[+]z[*]Log _ Hy)).
 Step_final (Exp (z[*] (Log _ Hx[+]Log _ Hy))).
Qed.

Lemma recip_power : forall x y Hx Hx' Hx'' Hxy, ([1][/] x[//]Hx') [!]y[//]Hx'' [=] ([1][/] x[!]y[//]Hx[//]Hxy).
Proof.
 intros; unfold power in |- *.
 rstepr ([1][/] _[//]Exp_ap_zero (y[*]Log x Hx)).
 astepr (Exp [--] (y[*]Log _ Hx)).
 Step_final (Exp (y[*][--] (Log _ Hx))).
Qed.

Hint Resolve Exp_power mult_power recip_power: algebra.

Lemma div_power : forall x y z Hx Hy Hy' Hxy Hyz,
 (x[/] y[//]Hy') [!]z[//]Hxy [=] (x[!]z[//]Hx[/] y[!]z[//]Hy[//]Hyz).
Proof.
 intros.
 apply eq_transitive_unfolded with ((x[*] ([1][/] _[//]Hy')) [!]z[//]
   mult_resp_pos _ _ _ Hx (recip_resp_pos _ _ Hy' Hy)).
  apply power_wd; rational.
 rstepr (x[!]z[//]Hx[*] ([1][/] _[//]Hyz)).
 Step_final (x[!]z[//]Hx[*]_[!]z[//]recip_resp_pos _ _ Hy' Hy).
Qed.

Hint Resolve div_power: algebra.

Lemma power_ap_zero : forall (x y : IR) Hx, x[!]y[//]Hx [#] [0].
Proof.
 intros; unfold power in |- *.
 apply Exp_ap_zero.
Qed.

Lemma power_mult : forall x y z Hx Hxy, x[!]y[*]z[//]Hx [=] (x[!]y[//]Hx) [!]z[//]Hxy.
Proof.
 intros; unfold power in |- *.
 apply Exp_wd.
 astepl (z[*]y[*]Log x Hx).
 astepl (z[*] (y[*]Log x Hx)).
 algebra.
Qed.

Lemma power_pos : forall (x y : IR) Hx, [0] [<] x[!]y[//]Hx.
Proof.
 intros; unfold power in |- *.
 apply Exp_pos.
Qed.

Hint Resolve power_mult: algebra.

Lemma power_recip : forall x q Hx (Hx' : [0] [<=] x) Hq (Hq' : 0 < q),
 x[!][1][/] nring q[//]Hq[//]Hx [=] NRoot Hx' Hq'.
Proof.
 intros.
 apply NRoot_unique.
   apply less_leEq; apply power_pos.
  apply power_pos.
 astepr (x[!][1][//]Hx).
 astepl (_[!]nring q[//]power_pos _ ([1][/] _[//]Hq) Hx).
 Step_final (x[!] ([1][/] _[//]Hq) [*]nring q[//]Hx).
Qed.

Hint Resolve power_recip: algebra.

Lemma power_div : forall x p q Hx (Hx' : [0] [<=] x) Hq (Hq' : 0 < q),
 x[!]nring p[/] nring q[//]Hq[//]Hx [=] (NRoot Hx' Hq') [^]p.
Proof.
 intros.
 apply eq_transitive_unfolded with (x[!] ([1][/] _[//]Hq) [*]nring p[//]Hx).
  apply power_wd; rational.
 astepr (NRoot Hx' Hq'[!]nring p[//]NRoot_pos _ Hx' _ Hq' Hx).
 Step_final ((x[!][1][/] _[//]Hq[//]Hx) [!]nring p[//]power_pos _ _ _).
Qed.

Hint Resolve power_div: algebra.

Lemma real_power_resp_leEq_rht : forall x y p Hx Hy,
 [0][<=] p -> x[<=]y -> x[!]p[//]Hx [<=] y[!]p[//]Hy.
Proof.
 intros x y p Hp Hx Hy H.
 unfold power.
 apply Exp_resp_leEq.
 apply mult_resp_leEq_lft; try assumption.
 apply Log_resp_leEq.
 assumption.
Qed.

Lemma real_power_resp_less_rht : forall x y p Hx Hy,
 [0][<] p -> x[<]y -> x[!]p[//]Hx [<] y[!]p[//]Hy.
Proof.
 intros x y p Hp Hx Hy H.
 unfold power.
 apply Exp_resp_less.
 apply mult_resp_less_lft; try assumption.
 apply Log_resp_less.
 assumption.
Qed.

Lemma real_power_resp_leEq_lft : forall x p q Hx Hx',
 [1][<=]x -> p[<=]q -> x[!]p[//]Hx [<=] x[!]q[//]Hx'.
Proof.
 intros x p q Hx Hx' Hx0 H.
 unfold power.
 apply Exp_resp_leEq.
 stepr (q[*]Log x Hx); [| now csetoid_rewrite (Log_wd x x Hx Hx' (eq_reflexive IR x)); apply eq_reflexive].
 apply mult_resp_leEq_rht; try assumption.
 apply Zero_leEq_Log.
 assumption.
Qed.

Lemma real_power_resp_less_lft : forall x p q Hx Hx',
 [1][<]x -> p[<]q -> x[!]p[//]Hx [<] x[!]q[//]Hx'.
Proof.
 intros x p q Hx Hx' Hx0 H.
 unfold power.
 apply Exp_resp_less.
 stepr (q[*]Log x Hx); [| now csetoid_rewrite (Log_wd x x Hx Hx' (eq_reflexive IR x)); apply eq_reflexive].
 apply mult_resp_less; try assumption.
 apply Zero_less_Log.
 assumption.
Qed.

Lemma real_power_resp_leEq_both : forall x y p q Hx Hy',
 [1][<=]x -> [0] [<=] p -> x[<=]y -> p[<=]q ->
 x[!]p[//]Hx [<=] y[!]q[//]Hy'.
Proof.
 intros x y p q Hx Hy Hx0 Hp H0 H1.
 apply leEq_transitive with (y[!]p[//]Hy).
  apply real_power_resp_leEq_rht; assumption.
 apply real_power_resp_leEq_lft; try assumption.
 apply leEq_transitive with x; assumption.
Qed.

Lemma real_power_resp_less_both : forall x y p q Hx Hy',
 [1][<]x -> [0] [<] p -> x[<]y -> p[<]q ->
 x[!]p[//]Hx [<] y[!]q[//]Hy'.
Proof.
 intros x y p q Hx Hy Hx0 Hp H0 H1.
 apply less_transitive_unfolded with (y[!]p[//]Hy).
  apply real_power_resp_less_rht; assumption.
 apply real_power_resp_less_lft; try assumption.
 apply less_transitive_unfolded with x; assumption.
Qed.

Section Power_Function.

(**
** Power Function

This operation on real numbers gives birth to an analogous operation
on partial functions which preserves continuity.

%\begin{convention}% Let [F, G : PartIR].
%\end{convention}%
*)

Variable J : interval.
Variables F G : PartIR.

Definition FPower := Expon[o]G{*} (Logarithm[o]F).

Lemma FPower_domain : forall x, Dom F x -> Dom G x ->
 (forall Hx, [0] [<] F x Hx) -> Dom FPower x.
Proof.
 intros x H H0 H1.
 simpl in |- *.
 cut (Conj (Dom G) (fun y : IR => {Hx : _ | [0] [<] Part F y Hx}) x). intro H2.
  exists H2; split.
 split; auto.
 exists H; auto.
Qed.

Lemma Continuous_power : positive_fun J F ->
 Continuous J F -> Continuous J G -> Continuous J FPower.
Proof.
 intros H H0 H1.
 unfold FPower in |- *.
 apply Continuous_comp with realline.
   3: apply Continuous_Exp.
  2: apply Continuous_mult; [ apply H1 | apply Continuous_comp with (openl [0]); auto ].
   3: apply Continuous_Log.
  apply maps_compacts_into_strict_imp_weak; apply Continuous_imp_maps_compacts_into.
  apply Continuous_mult; auto.
  apply Continuous_comp with (openl [0]); auto.
   2: apply Continuous_Log.
  apply maps_compacts_into_strict_imp_weak; apply positive_imp_maps_compacts_into; auto.
 apply maps_compacts_into_strict_imp_weak; apply positive_imp_maps_compacts_into; auto.
Qed.

End Power_Function.

Notation "F {!} G" := (FPower F G) (at level 20).

Section More_on_Power_Function.

Opaque Expon Logarithm.

(** From global continuity we can obviously get local continuity: *)

Lemma continuous_I_power : forall F G a b Hab, Continuous_I Hab F ->
 Continuous_I Hab G -> positive_fun (compact a b Hab) F -> Continuous_I Hab (F{!}G).
Proof.
 intros.
 apply (Int_Continuous (clcr a b) Hab).
 apply Continuous_power.
   auto.
  apply Continuous_Int with Hab Hab; auto.
 apply Continuous_Int with Hab Hab; auto.
Qed.

(** The rule for differentiation is a must. *)

Lemma Derivative_power : forall (J : interval) pJ F F' G G', positive_fun J F ->
 Derivative J pJ F F' -> Derivative J pJ G G' ->
 Derivative J pJ (F{!}G) (G{*} (F{!} (G{-} [-C-][1]) {*}F') {+}F{!}G{*} (G'{*} (Logarithm[o]F))).
Proof.
 intros J pJ F F' G G' H H0 H1.
 unfold FPower in |- *.
 assert (H2 : Derivative (openl [0]) I Logarithm {1/}FId).
  apply Derivative_Log.
 assert (H3 : Derivative realline I Expon Expon).
  apply Derivative_Exp.
 elim H; intros incF H'.
 elim H'; intros c H4 H5; clear incF H'.
 Derivative_Help.
  apply eq_imp_Feq.
    apply included_FMult.
     apply included_FComp.
      intros x H6.
      repeat split.
       apply (Derivative_imp_inc _ _ _ _ H1); auto.
      simpl in |- *.
      exists (Derivative_imp_inc _ _ _ _ H0 _ H6).
      apply Log_domain; apply less_leEq_trans with c; auto.
     intros; apply Exp_domain.
    intros x H6; simpl in |- *; repeat split.
        apply (Derivative_imp_inc _ _ _ _ H1); auto.
       exists (Derivative_imp_inc _ _ _ _ H0 _ H6).
       repeat split.
       intros; simpl in |- *.
       apply Greater_imp_ap; apply less_leEq_trans with c; auto.
      apply (Derivative_imp_inc' _ _ _ _ H0); auto.
     apply (Derivative_imp_inc' _ _ _ _ H1); auto.
    exists (Derivative_imp_inc _ _ _ _ H0 _ H6).
    intros; apply Log_domain; apply less_leEq_trans with c; auto.
   apply included_FPlus.
    apply included_FMult.
     Included.
    apply included_FMult.
     apply included_FComp.
      apply included_FMult.
       Included.
      apply included_FComp.
       Included.
      intros; apply Log_domain; apply less_leEq_trans with c; auto.
     intros; apply Exp_domain.
    Included.
   apply included_FMult.
    apply included_FComp.
     apply included_FMult.
      Included.
     apply included_FComp.
      Included.
     intros; apply Log_domain; apply less_leEq_trans with c; auto.
    intros; apply Exp_domain.
   apply included_FMult.
    Included.
   apply included_FComp.
    Included.
   intros; apply Log_domain; apply less_leEq_trans with c; auto.
  intros.
  astepl (Part _ _ (ProjIR1 Hx) [*]Part _ _ (ProjIR2 Hx)).
  elim Hx; intros Hx1 Hx2; clear Hx.
  astepl (Part _ _ Hx1[*]Part _ _ Hx2).
  astepl (Part _ _ (ProjT2 Hx1) [*]Part _ _ Hx2).
  elim Hx1; clear Hx1; intros Hx1 Hx3.
  astepl (Part _ (Part _ _ Hx1) Hx3[*]Part _ _ Hx2).
  generalize Hx3; clear Hx3.
  elim Hx1; intros Hx4 Hx5.
  intro; astepl (Part _ (Part _ _ (ProjIR1 (Hx4, Hx5)) [*]
    Part _ _ (ProjIR2 (Hx4, Hx5))) Hx3[*] Part _ _ Hx2).
  cut (Dom Expon (Part _ _ Hx4[*]Part _ _ Hx5)). intro H7.
   2: apply dom_wd with (x := Part _ _ (ProjIR1 (Hx4, Hx5)) [*]
     Part _ _ (ProjIR2 (Hx4, Hx5))); algebra.
  astepl (Part _ (Part _ _ Hx4[*]Part _ _ Hx5) H7[*]Part _ _ Hx2).
  clear Hx3; rename H7 into Hx3.
  astepl (Part _ (Part _ _ Hx4[*]Part _ _ (ProjT2 Hx5)) Hx3[*]Part _ _ Hx2).
  generalize Hx3; clear Hx3.
  elim Hx5; intros Hx6 Hx7.
  intro; astepl (Part _ (Part _ _ Hx4[*]Part _ _ Hx7) Hx3[*]Part _ _ Hx2).
  set (A := Part _ (Part _ _ Hx4[*]Part _ _ Hx7) Hx3) in *.
  astepl (A[*] (Part _ _ (ProjIR1 Hx2) [+]Part _ _ (ProjIR2 Hx2))).
  elim Hx2; intros Hx8 Hx9.
  astepl (A[*] (Part _ _ Hx8[+]Part _ _ Hx9)).
  astepl (A[*] (Part _ _ (ProjIR1 Hx8) [*]Part _ _ (ProjIR2 Hx8) [+]Part _ _ Hx9)).
  elim Hx8; intros Hx10 Hx11.
  astepl (A[*] (Part _ _ Hx10[*]Part _ _ Hx11[+]Part _ _ Hx9)).
  astepl (A[*] (Part _ _ Hx10[*]Part _ _ Hx11[+] Part _ _ (ProjIR1 Hx9) [*]Part _ _ (ProjIR2 Hx9))).
  elim Hx9; intros Hx12 Hx13.
  astepl (A[*] (Part _ _ Hx10[*]Part _ _ Hx11[+]Part _ _ Hx12[*]Part _ _ Hx13)).
  astepl (A[*] (Part _ _ Hx10[*] (Part _ _ (ProjIR1 Hx11) [*]Part _ _ (ProjIR2 Hx11)) [+]
    Part _ _ Hx12[*]Part _ _ Hx13)).
  elim Hx11; intros Hx14 Hx15.
  apply eq_transitive_unfolded with (A[*] (Part _ _ Hx10[*] (Part _ _ Hx14[*]Part _ _ Hx15) [+]
    Part _ _ Hx12[*]Part _ _ Hx13)).
   apply mult_wd; algebra.
  astepl (A[*] (Part _ _ Hx10[*] (Part _ _ Hx14[*]Part _ _ Hx15) [+]
    Part _ _ Hx12[*]Part _ _ (ProjT2 Hx13))).
  elim Hx13; intros Hx16 Hx17.
  astepl (A[*] (Part _ _ Hx10[*] (Part _ _ Hx14[*]Part _ _ Hx15) [+] Part _ _ Hx12[*]Part _ _ Hx17)).
  astepl (A[*] (Part _ _ Hx10[*] (Part _ _ (ProjT2 Hx14) [*]Part _ _ Hx15) [+]
    Part _ _ Hx12[*]Part _ _ Hx17)).
  elim Hx14; intros Hx18 Hx19.
  astepl (A[*] (Part _ _ Hx10[*] (Part _ _ Hx19[*]Part _ _ Hx15) [+] Part _ _ Hx12[*]Part _ _ Hx17)).
  elim Hx19; intros Hx20 Hx21.
  assert (H7 : Dom G x). auto.
   assert (H8 : Dom F x). auto.
   cut ([0] [<] Part _ _ H8). intro H9.
   assert (H10 : Part _ _ H8 [#] [0]). apply Greater_imp_ap; auto.
    assert (H11 : Dom F' x). auto.
    assert (H12 : Dom G' x). auto.
    apply eq_transitive_unfolded with (Exp (Part _ _ H7[*]Log _ H9) [*]
      (Part _ _ H7[*] (([1][/] _[//]H10) [*]Part _ _ H11) [+] Part _ _ H12[*]Log _ H9)).
    unfold A, Log in |- *; simpl in |- *.
    repeat first  [apply mult_wd | apply pfwdef | apply bin_op_wd_unfolded]; try reflexivity.
   clear Hx21 Hx20 Hx19 Hx18 Hx17 Hx16 Hx15 Hx14 Hx13 Hx12 Hx11 Hx10 Hx9 Hx8 A
     Hx3 Hx7 Hx6 Hx5 Hx4 Hx1 Hx2.
   astepr (Part _ _ (ProjIR1 Hx') [+]Part _ _ (ProjIR2 Hx')).
   elim Hx'; clear Hx'; intros Hx1 Hx2.
   astepr (Part _ _ Hx1[+]Part _ _ Hx2).
   astepr (Part _ _ Hx1[+]Part _ _ (ProjIR1 Hx2) [*]Part _ _ (ProjIR2 Hx2)).
   elim Hx2; clear Hx2; intros Hx2 Hx3.
   astepr (Part _ _ Hx1[+]Part _ _ Hx2[*]Part _ _ Hx3).
   astepr (Part _ _ Hx1[+] Part _ _ Hx2[*] (Part _ _ (ProjIR1 Hx3) [*]Part _ _ (ProjIR2 Hx3))).
   elim Hx3; clear Hx3; intros Hx3 Hx4.
   astepr (Part _ _ Hx1[+]Part _ _ Hx2[*] (Part _ _ H12[*]Part _ _ Hx4)); clear Hx3.
   astepr (Part _ _ Hx1[+]Part _ _ Hx2[*] (Part _ _ H12[*]Part _ _ (ProjT2 Hx4))).
   elim Hx4; clear Hx4; intros Hx3 Hx4.
   astepr (Part _ _ Hx1[+]Part _ _ Hx2[*] (Part _ _ H12[*]Part _ _ Hx4)).
   apply eq_transitive_unfolded with (Part _ _ Hx1[+]Part _ _ Hx2[*] (Part _ _ H12[*]Log _ H9)).
    2: unfold Log in |- *; apply bin_op_wd_unfolded; algebra.
   clear Hx3 Hx4.
   astepr (Part _ _ Hx1[+]Part _ _ (ProjT2 Hx2) [*] (Part _ _ H12[*]Log _ H9)).
   elim Hx2; clear Hx2; intros Hx2 Hx3.
   astepr (Part _ _ Hx1[+]Part _ _ Hx3[*] (Part _ _ H12[*]Log _ H9)).
   generalize Hx3; clear Hx3.
   elim Hx2; clear Hx2; intros Hx4 Hx5 Hx3.
   assert (H13 : Dom Expon (Part _ _ Hx4[*]Part _ _ Hx5)). apply Exp_domain.
    astepr (Part _ _ Hx1[+] Part _ (Part _ _ (ProjIR1 (Hx4, Hx5)) [*]
      Part _ _ (ProjIR2 (Hx4, Hx5))) Hx3[*] (Part _ _ H12[*]Log _ H9)).
   apply eq_transitive_unfolded with (Part _ _ Hx1[+]Part _ _ H13[*] (Part _ _ H12[*]Log _ H9)).
    2: apply bin_op_wd_unfolded; algebra.
   generalize H13; clear H13 Hx3.
   elim Hx5; clear Hx5; intros Hx5 Hx6 Hx3.
   astepr (Part _ _ Hx1[+] Part _ (Part _ _ Hx4[*]Part _ _ Hx6) Hx3[*] (Part _ _ H12[*]Log _ H9)).
   apply eq_transitive_unfolded with
     (Part _ _ Hx1[+]Exp (Part _ _ H7[*]Log _ H9) [*] (Part _ _ H12[*]Log _ H9)).
    2: apply bin_op_wd_unfolded; [ algebra | unfold Log in |- *; simpl in |- * ].
    2: apply bin_op_wd_unfolded; algebra.
   eapply eq_transitive_unfolded.
    apply ring_dist_unfolded.
   apply bin_op_wd_unfolded.
    2: apply eq_reflexive_unfolded.
   clear Hx3 Hx6 Hx5 Hx4.
   astepr (Part _ _ (ProjIR1 Hx1) [*]Part _ _ (ProjIR2 Hx1)).
   elim Hx1; clear Hx1; intros Hx1 Hx2.
   astepr (Part _ _ Hx1[*]Part _ _ Hx2).
   astepr (Part _ _ H7[*] (Part _ _ (ProjIR1 Hx2) [*]Part _ _ (ProjIR2 Hx2))).
   elim Hx2; clear Hx2 Hx1; intros Hx1 Hx2.
   astepr (Part _ _ H7[*] (Part _ _ Hx1[*]Part _ _ H11)).
   astepr (Part _ _ H7[*] (Part _ _ (ProjT2 Hx1) [*]Part _ _ H11)).
   elim Hx1; clear Hx1 Hx2; intros Hx1 Hx2.
   astepr (Part _ _ H7[*] (Part _ _ Hx2[*]Part _ _ H11)).
   apply eq_transitive_unfolded with (Part _ _ H7[*] (Exp (Part _ _ Hx1) [*]Part _ _ H11)).
    2: simpl in |- *; algebra.
   clear Hx2.
   apply eq_transitive_unfolded with (Part _ _ H7[*]
     (Exp (Part _ _ (ProjIR1 Hx1) [*]Part _ _ (ProjIR2 Hx1)) [*]Part _ _ H11)).
    2: apply mult_wdr; algebra.
   elim Hx1; clear Hx1; intros Hx1 Hx2.
   apply eq_transitive_unfolded
     with (Part _ _ H7[*] (Exp (Part _ _ Hx1[*]Part _ _ Hx2) [*]Part _ _ H11)).
    2: apply mult_wdr; algebra.
   apply eq_transitive_unfolded
     with (Part _ _ H7[*] (Exp ((Part _ _ H7[-][1]) [*]Log _ H9) [*]Part _ _ H11)).
    2: unfold Log in |- *; simpl in |- *.
    2: apply mult_wdr; apply mult_wd; algebra.
   clear Hx1 Hx2.
   rstepl ((Exp (Part _ _ H7[*]Log _ H9) [/] _[//]H10) [*] (Part _ _ H7[*]Part _ _ H11)).
   rstepr (Exp ((Part _ _ H7[-][1]) [*]Log _ H9) [*] (Part _ _ H7[*]Part _ _ H11)).
   apply mult_wdl.
   apply eq_transitive_unfolded with (Exp (Part _ _ H7[*]Log _ H9[-]Log _ H9)).
    2: apply Exp_wd; rational.
   astepr (Exp (G x H7[*]Log _ H9) [/] _[//]Exp_ap_zero (Log _ H9)).
   algebra.
  Transparent Logarithm.
  astepr (Part _ _ Hx16); auto.
 Opaque Logarithm.
 apply Derivative_comp with realline I; Deriv.
  apply Continuous_imp_maps_compacts_into.
  apply Continuous_mult.
   apply Derivative_imp_Continuous with pJ G'; auto.
  apply Continuous_comp with (openl [0]).
    apply maps_compacts_into_strict_imp_weak; apply positive_imp_maps_compacts_into; auto.
    apply Derivative_imp_Continuous with pJ F'; auto.
   apply Derivative_imp_Continuous with pJ F'; auto.
  apply Continuous_Log.
 apply Derivative_mult.
  auto.
 apply Derivative_comp with (openl [0]) I; Deriv.
 apply positive_imp_maps_compacts_into; auto.
 apply Derivative_imp_Continuous with pJ F'; auto.
Qed.

Lemma Diffble_power : forall (J : interval) pJ F G, positive_fun J F ->
 Diffble J pJ F -> Diffble J pJ G -> Diffble J pJ (F{!}G).
Proof.
 intros J pJ F G H H0 H1.
 set (F1 := Deriv _ _ _ H0) in *.
 set (G1 := Deriv _ _ _ H1) in *.
 eapply Derivative_imp_Diffble.
 apply Derivative_power with (F' := F1) (G' := G1).
   auto.
  unfold F1 in |- *; apply Deriv_lemma.
 unfold G1 in |- *; apply Deriv_lemma.
Qed.

End More_on_Power_Function.

Hint Resolve Derivative_power: derivate.
