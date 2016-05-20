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
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *)

(** printing ExpCC %\ensuremath{\exp_{\mathbb C}}% *)

Require Export CoRN.complex.AbsCC.
Require Export CoRN.transc.Exponential.
Require Export CoRN.transc.Pi.

(**
** The Complex Exponential *)

Definition ExpCC (z : CC) := cc_IR (Exp (Re z)) [*] (Cos (Im z) [+I*]Sin (Im z)).

Lemma ExpCC_wd : forall z1 z2 : CC, z1 [=] z2 -> ExpCC z1 [=] ExpCC z2.
Proof.
 intro z1. elim z1. intros x1 y1.
 intro z2. elim z2. intros x2 y2.
 unfold ExpCC in |- *. unfold Re, Im in |- *.
 intros (H1, H2).
 simpl in H1. simpl in H2.
 apply bin_op_wd_unfolded.
  apply cc_IR_wd. apply Exp_wd. assumption.
  astepl (Cos y2[+I*]Sin y1).
 astepl (Cos y2[+I*]Sin y2).
 apply eq_reflexive.
Qed.

(* begin hide *)
Lemma ExpCC_equation_aid_1 :
  forall z1 z2 : CC,
  ExpCC (z1[+]z2) [=]
  cc_IR (Exp (Re z1[+]Re z2)) [*] (Cos (Im z1[+]Im z2) [+I*]Sin (Im z1[+]Im z2)).
Proof.
 intro z1. elim z1. intros x1 y1.
 intro z2. elim z2. intros x2 y2.
 unfold Re, Im in |- *.
 unfold ExpCC in |- *.
 apply bin_op_wd_unfolded.
  apply cc_IR_wd.
  apply Exp_wd.
  algebra.
 split; algebra.

Qed.

Lemma ExpCC_equation_aid_2 :
  forall z1 z2 : CC,
  cc_IR (Exp (Re z1[+]Re z2)) [*] (Cos (Im z1[+]Im z2) [+I*]Sin (Im z1[+]Im z2)) [=]
  cc_IR (Exp (Re z1) [*]Exp (Re z2)) [*]
  ((Cos (Im z1) [*]Cos (Im z2) [-]Sin (Im z1) [*]Sin (Im z2)) [+I*]
   (Sin (Im z1) [*]Cos (Im z2) [+]Cos (Im z1) [*]Sin (Im z2))).
Proof.
 intros z1 z2. apply bin_op_wd_unfolded.
 apply cc_IR_wd. algebra.
  split; algebra.

Qed.

Lemma ExpCC_equation_aid_3 :
  forall z1 z2 : CC,
  cc_IR (Exp (Re z1) [*]Exp (Re z2)) [*]
  ((Cos (Im z1) [*]Cos (Im z2) [-]Sin (Im z1) [*]Sin (Im z2)) [+I*]
   (Sin (Im z1) [*]Cos (Im z2) [+]Cos (Im z1) [*]Sin (Im z2))) [=]
  cc_IR (Exp (Re z1) [*]Exp (Re z2)) [*]
  ((Cos (Im z1) [+I*]Sin (Im z1)) [*] (Cos (Im z2) [+I*]Sin (Im z2))).
Proof.
 intros z1 z2. apply bin_op_wd_unfolded.
 apply eq_reflexive.
 set (c1 := Cos (Im z1)) in *.
 set (c2 := Cos (Im z2)) in *.
 set (s1 := Sin (Im z1)) in *.
 set (s2 := Sin (Im z2)) in *.
 split; simpl in |- *; algebra.
Qed.

Lemma ExpCC_equation_aid_4 :
  forall z1 z2 : CC,
  cc_IR (Exp (Re z1) [*]Exp (Re z2)) [*]
  ((Cos (Im z1) [+I*]Sin (Im z1)) [*] (Cos (Im z2) [+I*]Sin (Im z2))) [=]
  ExpCC z1[*]ExpCC z2.
Proof.
 intros z1 z2.
 unfold ExpCC in |- *.
 set (c := Cos (Im z1) [+I*]Sin (Im z1)) in *.
 set (d := Cos (Im z2) [+I*]Sin (Im z2)) in *.
 astepl (cc_IR (Exp (Re z1)) [*]cc_IR (Exp (Re z2)) [*] (c[*]d)).
 rational.
Qed.
(* end hide *)

Lemma ExpCC_plus : forall z1 z2 : CC, ExpCC (z1[+]z2) [=] ExpCC z1[*]ExpCC z2.
Proof.
 intros z1 z2.
 apply eq_transitive_unfolded with (S := cc_csetoid) (y := cc_IR (Exp (Re z1) [*]Exp (Re z2)) [*]
   ((Cos (Im z1) [*]Cos (Im z2) [-]Sin (Im z1) [*]Sin (Im z2)) [+I*]
     (Sin (Im z1) [*]Cos (Im z2) [+]Cos (Im z1) [*]Sin (Im z2)))).
  eapply eq_transitive_unfolded.
   apply ExpCC_equation_aid_1. apply ExpCC_equation_aid_2.
  eapply eq_transitive_unfolded.
  apply ExpCC_equation_aid_3. apply ExpCC_equation_aid_4.
Qed.

Hint Resolve ExpCC_plus: algebra.

Lemma ExpCC_Zero : ExpCC [0] [=] [1].
Proof.
 unfold ExpCC in |- *.
 astepl (cc_IR (Exp [0]) [*] (Cos [0][+I*]Sin [0])).
 astepl (cc_IR [1][*] (Cos [0][+I*]Sin [0])).
 astepl (cc_IR [1][*] ([1][+I*][0])).
 simpl in |- *. split; simpl in |- *; rational.
Qed.

Hint Resolve ExpCC_Zero: algebra.

Lemma ExpCC_inv_aid : forall z : CC, ExpCC z[*]ExpCC [--]z [=] [1].
Proof.
 intro z.
 apply eq_transitive_unfolded with (S := cc_csetoid) (y := ExpCC [0]).
  astepl (ExpCC (z[+][--]z)).
  apply ExpCC_wd.
  rational.
 algebra.
Qed.

Hint Resolve ExpCC_inv_aid: algebra.

Lemma ExpCC_ap_zero : forall z : CC, ExpCC z [#] [0].
Proof.
 intro z.
 cut (ExpCC z[*]ExpCC [--]z [#] [0]).
  intro H.
  apply (mult_cancel_ap_zero_lft _ _ _ H).
 astepl ([1]:CC).
 apply cc_cr_non_triv.
Qed.

Lemma ExpCC_inv : forall z z_, ([1][/] (ExpCC z) [//]z_) [=] ExpCC [--]z.
Proof.
 intros z H.
 astepl (ExpCC z[*]ExpCC [--]z[/] ExpCC z[//]H). rational.
Qed.

Hint Resolve ExpCC_inv: algebra.

Lemma ExpCC_pow : forall z n, ExpCC z[^]n [=] ExpCC (nring n[*]z).
Proof.
 intro z. simple induction n.
 unfold nexp in |- *.
  astepl ([1]:CC).
  astepr (ExpCC [0]).
   astepr ([1]:CC).
   apply eq_reflexive.
  apply ExpCC_wd.
  rational.
 intros n0 Hrec.
 astepl (ExpCC z[^]n0[*]ExpCC z).
 astepl (ExpCC (nring n0[*]z) [*]ExpCC z).
 astepl (ExpCC (nring n0[*]z[+]z)).
 apply ExpCC_wd.
 algebra.
 rstepl ((nring n0[+][1]) [*]z). algebra.
Qed.

Hint Resolve ExpCC_pow: algebra.

Lemma AbsCC_ExpCC : forall z : CC, AbsCC (ExpCC z) [=] Exp (Re z).
Proof.
 intro z. unfold ExpCC in |- *.
 astepl (AbsCC (cc_IR (Exp (Re z))) [*]AbsCC (Cos (Im z) [+I*]Sin (Im z))).
 astepr (Exp (Re z) [*][1]).
 apply bin_op_wd_unfolded.
  assert (H : AbsCC (cc_IR (Exp (Re z))) [=] Exp (Re z)).
   apply AbsCC_IR.
   apply less_leEq.
   apply Exp_pos.
  astepl (Exp (Re z)).
  apply eq_reflexive.
 cut (AbsCC (Cos (Im z) [+I*]Sin (Im z)) [^]2 [=] [1]).
  set (x := AbsCC (Cos (Im z) [+I*]Sin (Im z))) in *.
  intro H0.
  assert (H1 : x[+][1][~=][0]).
   apply ap_imp_neq.
   apply Greater_imp_ap.
   apply leEq_less_trans with (y := x).
    unfold x in |- *. apply AbsCC_nonneg.
    apply less_plusOne.
  assert (H2 : (x[+][1]) [*] (x[-][1]) [=] [0]).
   cut (x[^]2[-][1][^]2 [=] [0]).
    intro H'.
    astepl (x[^]2[-][1][^]2).
    assumption.
   astepl (x[^]2[-][1]).
   astepr (OneR[-]OneR).
   apply cg_minus_wd; [ assumption | apply eq_reflexive ].
  assert (H3 : x[-][1] [=] [0]).
   apply (mult_eq_zero _ _ _ H1 H2).
  rstepl ([1][+] (x[-][1])).
  astepr (OneR[+]ZeroR).
  apply plus_resp_eq. assumption.
  astepl (Cos (Im z) [^]2[+]Sin (Im z) [^]2).
  astepl OneR.
  apply eq_reflexive.
 apply AbsCC_square_Re_Im.
Qed.

Hint Resolve AbsCC_ExpCC: algebra.

Lemma ExpCC_Periodic : forall z, ExpCC (z[+]II[*]Two[*]cc_IR Pi) [=] ExpCC z.
Proof.
 intro z. elim z. intros x y.
 astepl (ExpCC (x[+I*] (y[+]Two[*]Pi))).
  unfold ExpCC in |- *.
  apply bin_op_wd_unfolded.
   apply cc_IR_wd.
   apply Exp_wd.
   simpl in |- *. apply eq_reflexive_unfolded.
   astepl (Cos (y[+]Two[*]Pi) [+I*]Sin (y[+]Two[*]Pi)).
  astepl (Cos y[+I*]Sin y).
  apply eq_reflexive.
 apply ExpCC_wd.
 split; simpl in |- *; rational.
Qed.

Hint Resolve ExpCC_Periodic: algebra.

Lemma ExpCC_Exp : forall x : IR, ExpCC (cc_IR x) [=] cc_IR (Exp x).
Proof.
 intro x. unfold ExpCC in |- *.
 astepl (cc_IR (Exp x) [*] (Cos (Im (cc_IR x)) [+I*]Sin (Im (cc_IR x)))).
 astepr (cc_IR (Exp x) [*][1]).
 apply bin_op_wd_unfolded.
  algebra.
 astepl (Cos [0][+I*]Sin [0]).
 Step_final ([1][+I*][0]).
Qed.

Hint Resolve ExpCC_Exp: algebra.

Theorem Euler : (ExpCC (II[*] (cc_IR Pi))) [+][1] [=] [0].
Proof.
 split.
  Opaque Sin Cos Exp.
  simpl.
  rstepl ((Exp [0]) [*] (Cos Pi) [+][1]).
  astepl (([1]:IR) [*][--][1][+][1]).
  rational.
 simpl.
 rstepl ((Exp [0]) [*] (Sin Pi)).
 Step_final (([1]:IR) [*][0]).
Qed.
