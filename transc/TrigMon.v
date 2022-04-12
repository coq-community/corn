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

Require Export CoRN.transc.Pi.
Require Import CoRN.tactics.CornTac.

Opaque Sine Cosine.

(**
Sign properties: cosine is positive in
$(-\frac{\pi}2,\frac{\pi}2)$#(-&pi;/2,&pi;/2)#, sine in
$(0,\pi)$#(0,&pi;)# and tangent in $(0,\frac{\pi}2)$#0,&pi;/2)#.
*)

Lemma Cos_pos : forall x, [--] (Pi [/]TwoNZ) [<] x -> x [<] Pi [/]TwoNZ -> [0] [<] Cos x.
Proof.
 intros x H H0.
 assert (H1 : Continuous_I (less_leEq _ _ _ (less_transitive_unfolded _ _ _ _ H H0)) Cosine).
  apply included_imp_Continuous with realline; Contin.
 elim (contin_prop _ _ _ _ H1 Half (pos_half _)); intros d H2 H3.
 elim (less_cotransitive_unfolded _ _ _ H2 x); intros.
  apply pos_cos; try apply less_leEq; auto.
 assert (H4 : [--]d [<] [0]).
  astepr ( [--]ZeroR); apply inv_resp_less; auto.
 elim (less_cotransitive_unfolded _ _ _ H4 x); intros.
  2: astepr (Cos [--]x); apply pos_cos.
   2: astepl ( [--]ZeroR); apply inv_resp_leEq; apply less_leEq; auto.
  2: apply inv_cancel_less; astepr x; auto.
 clear H4 H2 H1.
 astepl (OneR[-][1]).
 apply shift_minus_less; apply shift_less_plus'.
 apply leEq_less_trans with (Half:IR).
  2: apply half_lt1.
 astepl (Cos [0][-]Cos x).
 eapply leEq_transitive.
  apply leEq_AbsIR.
 simpl in |- *; apply H3.
   split; PiSolve.
  split; apply less_leEq; auto.
 apply less_leEq; simpl in |- *; unfold ABSIR in |- *.
 apply Max_less.
  apply shift_minus_less; apply shift_less_plus'.
  astepl ( [--]d); auto.
 rstepl x; auto.
Qed.

Lemma Sin_pos : forall x : IR, [0] [<] x -> x [<] Pi -> [0] [<] Sin x.
Proof.
 intros.
 astepr (Cos (Pi [/]TwoNZ[-]x)).
 apply Cos_pos.
  apply shift_less_minus; apply shift_plus_less'.
  unfold cg_minus in |- *; rstepr Pi; auto.
 apply shift_minus_less; apply shift_less_plus'.
 astepl ZeroR; auto.
Qed.

Lemma Tan_pos : forall x, [0] [<] x -> x [<] Pi [/]TwoNZ -> forall Hx, [0] [<] Tan x Hx.
Proof.
 intros.
 unfold Tan, Tang in |- *; simpl in |- *.
 apply shift_less_div.
  apply less_wdr with (Cos x).
   apply Cos_pos; auto.
   apply less_transitive_unfolded with ZeroR; PiSolve.
  simpl in |- *; algebra.
 astepl ZeroR; apply less_wdr with (Sin x).
  apply Sin_pos; auto.
  apply less_transitive_unfolded with (Pi [/]TwoNZ); PiSolve.
 simpl in |- *; algebra.
Qed.

Lemma Cos_nonneg : forall x, [--] (Pi [/]TwoNZ) [<=] x -> x [<=] Pi [/]TwoNZ -> [0] [<=] Cos x.
Proof.
 simpl in |- *.
 intros; apply olor_pos_clcr_nonneg with ( [--] (Pi [/]TwoNZ)) (Pi [/]TwoNZ) I I.
     PiSolve.
    intros x0 H1 Hx; inversion_clear H1.
    apply less_wdr with (Cos x0); [ apply Cos_pos; auto | simpl in |- *; algebra ].
   astepr (Cos [--] (Pi [/]TwoNZ)); apply eq_imp_leEq; Step_final (Cos (Pi [/]TwoNZ)).
  fold (Cos (Pi [/]TwoNZ)) in |- *; apply eq_imp_leEq; algebra.
 split; auto.
Qed.

Lemma Sin_nonneg : forall x, [0] [<=] x -> x [<=] Pi -> [0] [<=] Sin x.
Proof.
 simpl in |- *.
 intros; apply olor_pos_clcr_nonneg with ZeroR Pi I I.
     PiSolve.
    intros x0 H1 Hx; inversion_clear H1.
    apply less_wdr with (Sin x0); [ apply Sin_pos; auto | simpl in |- *; algebra ].
   fold (Sin [0]) in |- *; apply eq_imp_leEq; algebra.
  fold (Sin Pi) in |- *; apply eq_imp_leEq; algebra.
 split; auto.
Qed.

(** Consequences. *)

Lemma Abs_Sin_less_One : forall x, [--] (Pi [/]TwoNZ) [<] x -> x [<] Pi [/]TwoNZ -> AbsIR (Sin x) [<] [1].
Proof.
 intros.
 apply power_cancel_less with 2.
  apply less_leEq; apply pos_one.
 astepr OneR.
 astepr (Cos x[^]2[+]Sin x[^]2).
 apply less_wdl with (Sin x[^]2).
  astepl ([0][+]Sin x[^]2).
  apply plus_resp_less_rht.
  apply pos_square.
  apply Greater_imp_ap; apply Cos_pos; auto.
 apply eq_symmetric_unfolded.
 eapply eq_transitive_unfolded.
  2: apply AbsIR_eq_x; apply sqr_nonneg.
 apply eq_symmetric_unfolded; apply AbsIR_nexp_op.
Qed.

Lemma Abs_Cos_less_One : forall x, [0] [<] x -> x [<] Pi -> AbsIR (Cos x) [<] [1].
Proof.
 intros.
 astepl (AbsIR (Sin (Pi [/]TwoNZ[-]x))).
 apply Abs_Sin_less_One.
  apply shift_less_minus; apply shift_plus_less'.
  unfold cg_minus in |- *; rstepr Pi; auto.
 apply shift_minus_less; apply shift_less_plus'.
 astepl ZeroR; auto.
Qed.

(**
Sine is (strictly) increasing in [[ [--]Pi[/]Two,Pi[/]Two]]; cosine
is (strictly) decreasing in [[[0],Pi]].
*)

Lemma Sin_resp_leEq : forall x y, [--] (Pi [/]TwoNZ) [<=] x -> y [<=] Pi [/]TwoNZ -> x [<=] y -> Sin x [<=] Sin y.
Proof.
 intros; simpl in |- *.
 cut ( [--] (Pi [/]TwoNZ) [<] Pi [/]TwoNZ). intro H2.
  apply Derivative_imp_resp_leEq with (clcr [--] (Pi [/]TwoNZ) (Pi [/]TwoNZ)) H2 Cosine; auto.
     apply Included_imp_Derivative with realline I; Deriv.
    split; auto; apply leEq_transitive with y; auto.
   split; auto; apply leEq_transitive with x; auto.
  intros.
  apply leEq_glb. intros y0 H3 Hy.
  apply leEq_wdr with (Cos y0).
   inversion_clear H3.
   apply Cos_nonneg.
    apply leEq_transitive with (Min y x); try apply leEq_Min; auto; apply leEq_transitive with x; auto.
   apply leEq_transitive with (Max y x); try apply Max_leEq; auto; apply leEq_transitive with y; auto.
  simpl in |- *; algebra.
 PiSolve.
Qed.

Lemma Cos_resp_leEq : forall x y, [0] [<=] x -> y [<=] Pi -> x [<=] y -> Cos y [<=] Cos x.
Proof.
 intros.
 astepl (Sin (Pi [/]TwoNZ[-]y)); astepr (Sin (Pi [/]TwoNZ[-]x)).
 apply Sin_resp_leEq.
   apply shift_leEq_minus; apply shift_plus_leEq'.
   unfold cg_minus in |- *; rstepr Pi; auto.
  apply shift_minus_leEq; apply shift_leEq_plus'.
  astepl ZeroR; auto.
 apply minus_resp_leEq_both.
  apply leEq_reflexive.
 auto.
Qed.

(* begin hide *)
Lemma Cos_resp_less_aux :
  forall x y : IR, [0] [<] x -> x [<] y -> y [<=] Pi [/]TwoNZ -> Cos y [<] Cos x.
Proof.
 intros x y H H0 H1.
 astepl (Cos y[+][0]).
 apply shift_plus_less'.
 assert (H2 : Continuous_I (less_leEq _ _ _ H0) Sine).
  apply included_imp_Continuous with realline; Contin.
 assert (H3 : Continuous_I (Min_leEq_Max x y) Sine).
  apply included_imp_Continuous with realline; Contin.
 assert (H4 : Continuous_I (Min_leEq_Max y x) Sine).
  apply included_imp_Continuous with realline; Contin.
 assert (H5 : Continuous_I (Min_leEq_Max y x) {--}Sine).
  apply included_imp_Continuous with realline; Contin.
 apply less_leEq_trans with (Sin x[*] (y[-]x)).
  apply mult_resp_pos.
   apply Sin_pos; auto.
   apply less_transitive_unfolded with (Pi [/]TwoNZ).
    apply less_leEq_trans with y; auto.
   PiSolve.
  apply shift_less_minus; astepl x; auto.
 apply leEq_wdr with (Integral H3).
  eapply leEq_wdr.
   2: apply eq_symmetric_unfolded; apply (Integral_integral _ _ _ _ H3 _ H2).
  apply lb_integral.
  intros z H6 Hx.
  apply leEq_wdr with (Sin z).
   2: simpl in |- *; algebra.
  cut ( [--] (Pi [/]TwoNZ) [<=] x); intros.
   inversion_clear H6; apply Sin_resp_leEq; auto.
   apply leEq_transitive with y; auto.
  apply leEq_transitive with ZeroR; PiSolve.
 astepl ( [--][--] (Integral H3)).
 apply eq_transitive_unfolded with ( [--] (Integral H4)).
  apply un_op_wd_unfolded; apply eq_symmetric_unfolded; apply Integral_op.
 apply eq_transitive_unfolded with (Integral H5).
  apply eq_symmetric_unfolded; apply Integral_inv.
 assert (H6 : Derivative realline I Cosine {--}Sine). Deriv.
  eapply eq_transitive_unfolded.
  apply Barrow with (derG0 := H6) (Ha := I) (Hb := I) (pJ := I); Contin; split.
 simpl in |- *; algebra.
Qed.

Lemma Cos_resp_less_aux' :
  forall x y : IR, [0] [<=] x -> x [<] y -> y [<=] Pi [/]TwoNZ -> Cos y [<] Cos x.
Proof.
 intros.
 apply less_leEq_trans with (Cos ((x[+]y) [/]TwoNZ)).
  apply Cos_resp_less_aux; auto.
   apply pos_div_two; astepl (ZeroR[+][0]); apply plus_resp_leEq_less;
     try apply leEq_less_trans with x; auto.
  apply shift_div_less; [ apply pos_two | apply shift_plus_less ].
  rstepr y; auto.
 apply Cos_resp_leEq; auto.
  apply shift_div_leEq.
   apply pos_two.
  rstepr (Pi [/]TwoNZ[+]Pi [/]TwoNZ[+]Pi).
  astepl (x[+]y[+][0]).
  repeat apply plus_resp_leEq_both; auto.
   apply less_leEq; apply less_leEq_trans with y; auto.
  PiSolve.
 apply shift_leEq_div; [ apply pos_two | apply shift_leEq_plus' ].
 rstepl x; apply less_leEq; auto.
Qed.
(* end hide *)

Lemma Cos_resp_less : forall x y, [0] [<=] x -> x [<] y -> y [<=] Pi -> Cos y [<] Cos x.
Proof.
 intros x y H H0 H1.
 simpl in |- *.
 assert (Hab : [0] [<=] Pi [/]TwoNZ).
  apply less_leEq; apply pos_div_two; apply pos_Pi.
 assert (Hbc : Pi [/]TwoNZ [<=] Pi).
  apply less_leEq; apply pos_div_two'; apply pos_Pi.
 assert (Hac : [0] [<=] Pi).
  apply leEq_transitive with (Pi [/]TwoNZ); auto.
 apply strict_dec_glues with (Hab := Hab) (Hbc := Hbc) (Hac := Hac).
      Included.
     intros x0 y0 H2 H3 H4 Hx Hy.
     apply less_wdl with (Cos x0); [ apply less_wdr with (Cos y0) | idtac ];
       [ idtac | simpl in |- *; algebra | simpl in |- *; algebra ].
     inversion_clear H2; inversion_clear H3; apply Cos_resp_less_aux'; auto.
    intros x0 y0 H2 H3 H4 Hx Hy.
    apply less_wdl with (Cos x0); [ apply less_wdr with (Cos y0) | idtac ];
      [ idtac | simpl in |- *; algebra | simpl in |- *; algebra ].
    astepl (Cos [--]x0); astepl ( [--][--] (Cos [--]x0)); astepl ( [--] (Cos ( [--]x0[+]Pi))).
    apply less_wdl with ( [--] (Cos (Pi[-]x0))).
     2: apply un_op_wd_unfolded; apply Cos_wd; rational.
    astepr (Cos [--]y0); astepr ( [--][--] (Cos [--]y0)); astepr ( [--] (Cos ( [--]y0[+]Pi))).
    apply less_wdr with ( [--] (Cos (Pi[-]y0))).
     2: apply un_op_wd_unfolded; apply Cos_wd; rational.
    apply inv_resp_less.
    inversion_clear H2; inversion_clear H3; apply Cos_resp_less_aux'.
      apply shift_leEq_minus; astepl x0; auto.
     unfold cg_minus in |- *; apply plus_resp_leEq_less;
       [ apply leEq_reflexive | apply inv_resp_less; auto ].
    apply shift_minus_leEq; apply shift_leEq_plus'; rstepl (Pi [/]TwoNZ); auto.
   split; auto; apply less_leEq; apply leEq_less_trans with x; auto.
  split; auto; apply less_leEq; apply less_leEq_trans with y; auto.
 auto.
Qed.

Lemma Sin_resp_less : forall x y, [--] (Pi [/]TwoNZ) [<=] x -> x [<] y -> y [<=] Pi [/]TwoNZ -> Sin x [<] Sin y.
Proof.
 intros.
 astepl (Cos (Pi [/]TwoNZ[-]x)); astepr (Cos (Pi [/]TwoNZ[-]y)).
 apply Cos_resp_less; auto.
   apply shift_leEq_minus; astepl y; auto.
  unfold cg_minus in |- *; apply plus_resp_leEq_less;
    [ apply leEq_reflexive | apply inv_resp_less; auto ].
 apply shift_minus_leEq; apply shift_leEq_plus'; rstepl ( [--] (Pi [/]TwoNZ)); auto.
Qed.

Lemma Sin_ap_Zero : forall x:IR, (forall z, x[#](zring z)[*]Pi) -> Sin x [#] [0].
Proof.
 cut (forall x : IR, [0][<]x -> (forall n : nat, x[#]nring (R:=IR) n[*]Pi) -> Sin x[#][0]).
  intros X x Hx.
  destruct (ap_imp_less _ _ _ (Hx 0)).
   rstepl ([--][--](Sin x)).
   rstepr ([--][0]:IR).
   apply inv_resp_ap.
   csetoid_rewrite_rev (Sin_inv x).
   apply X.
    rstepl ([--]([0][*]Pi):IR).
    apply inv_resp_less.
    assumption.
   intros n.
   csetoid_rewrite_rev (zring_plus_nat IR n).
   replace (n:Z) with (- - n)%Z by ring.
   csetoid_rewrite (zring_inv IR (- n)%Z).
   rstepr ([--](zring (-n)[*]Pi)).
   apply inv_resp_ap.
   apply Hx.
  apply X.
   rstepl ([0][*]Pi).
   assumption.
  intros n.
  csetoid_rewrite_rev (zring_plus_nat IR n).
  apply Hx.
 cut (forall x : IR, [0][<]x -> x[<]Two[*]Pi -> (x[#]Pi) -> Sin x[#][0]).
  intros X x Hx0 Hx1.
  assert (Hpi : ([0][<]Two[*]Pi)).
   apply mult_resp_pos.
    apply (nring_pos); auto with *.
   auto with *.
  destruct (Archimedes' (x[/](Two[*]Pi)[//](Greater_imp_ap _ _ _ Hpi))) as [n Hn].
  generalize x Hx0 Hx1 Hn.
  clear x Hx0 Hx1 Hn.
  induction n; intros x Hx0 Hx1 Hn.
   elim (less_antisymmetric_unfolded _ _ _ Hn).
   apply div_resp_pos; assumption.
  destruct (ap_imp_less _ _ _ (Hx1 (2*n))).
   apply IHn; try assumption.
   apply shift_div_less'.
    assumption.
   rstepr ((nring 2[*]nring n)[*]Pi).
   stepr (nring (R:=IR) (2 * n)[*]Pi).
    assumption.
   apply mult_wdl.
   apply nring_comm_mult.
  destruct n as [|n].
   apply X; try assumption.
    rstepr ((Two[*]Pi)[*][1]).
    eapply shift_less_mult'.
     assumption.
    rstepr (nring 1:IR).
    apply Hn.
   rstepr ((nring 1:IR)[*]Pi).
   apply Hx1.
  rstepl (Sin (x[-]Two[*]Pi[+]Two[*]Pi)).
  csetoid_rewrite (Sin_periodic (x[-]Two[*]Pi)).
  apply IHn.
    apply shift_zero_less_minus.
    eapply leEq_less_trans;[|apply c].
    stepr ((Two:IR)[*]nring (S n)[*]Pi);
      [|csetoid_rewrite (nring_comm_mult IR (2%nat) (S n)); apply eq_reflexive].
    rstepl (Two[*]Pi[*]nring 1).
    rstepr (Two[*]Pi[*]nring (S n)).
    apply mult_resp_leEq_lft.
     apply nring_leEq; auto with *.
    apply less_leEq; assumption.
   intros i.
   apply zero_minus_apart.
   rstepl (x[-]((nring 2[+]nring i)[*]Pi)).
   apply minus_ap_zero.
   csetoid_rewrite_rev (nring_comm_plus IR 2 i).
   apply Hx1.
  rstepl ((x[/](Two[*]Pi)[//]Greater_imp_ap IR (Two[*]Pi) [0] Hpi)[-](nring 1)).
  apply shift_minus_less.
  csetoid_rewrite_rev (nring_comm_plus IR (S n) 1).
  rewrite plus_comm.
  assumption.
 intros x Hx0 Hx1 Hx2.
 destruct (ap_imp_less _ _ _ Hx2).
  apply Greater_imp_ap.
  apply Sin_pos; assumption.
 rstepl (Sin (x[-]Pi[+]Pi)).
 csetoid_rewrite (Sin_plus_Pi (x[-]Pi)).
 rstepr ([--][0]:IR).
 apply inv_resp_ap.
 apply Greater_imp_ap.
 apply Sin_pos.
  apply shift_zero_less_minus.
  assumption.
 apply shift_minus_less.
 rstepr (Two[*]Pi).
 assumption.
Qed.

Lemma Cos_ap_Zero : forall x:IR, (forall z, x[#]Pi[/]TwoNZ[+](zring z)[*]Pi) -> Cos x [#] [0].
Proof.
 intros x Hx.
 stepl (Cos (x[-](Pi[/]TwoNZ)[+](Pi[/]TwoNZ))); [| now apply Cos_wd; rational].
 csetoid_rewrite (Cos_plus_HalfPi (x[-](Pi[/]TwoNZ))).
 rstepr ([--][0]:IR).
 apply inv_resp_ap.
 apply Sin_ap_Zero.
 intros i.
 apply zero_minus_apart.
 rstepl (x[-](Pi[/]TwoNZ[+]zring i[*]Pi)).
 apply minus_ap_zero.
 apply Hx.
Qed.

Section Tangent.

Lemma Tang_Domain : forall x:IR, (forall z, x[#]Pi[/]TwoNZ[+](zring z)[*]Pi) -> Dom Tang x.
Proof.
 intros.
 repeat split; try constructor.
 intros [].
 apply: Cos_ap_Zero.
 assumption.
Qed.

Lemma Tang_Domain' : included (olor ([--](Pi[/]TwoNZ)) (Pi[/]TwoNZ)) (Dom Tang).
Proof.
 intros x [Hx0 Hx1].
 apply Tang_Domain.
 intros z.
 destruct (Z_lt_le_dec z 0).
  apply Greater_imp_ap.
  eapply leEq_less_trans;[|apply Hx0].
  rstepr ([--][0][*]Pi[-]Pi[/]TwoNZ).
  apply shift_leEq_minus.
  rstepl (((zring z)[+](zring 1))[*]Pi).
  apply mult_resp_leEq_rht;[|apply less_leEq; auto with *].
  stepl (zring (z+1):IR); [| now apply zring_plus].
  replace (z+1)%Z with (-(-z-1))%Z by ring.
  assert (0<=-z-1)%Z.
   auto with *.
  rewrite (Z_to_nat_correct H).
  stepl ([--](nring (Z_to_nat H)):IR); [| now apply eq_symmetric; apply zring_inv_nat].
  apply inv_resp_leEq.
  apply nring_nonneg.
 apply less_imp_ap.
 eapply less_leEq_trans.
  apply Hx1.
 rstepl (Pi[/]TwoNZ[+][0]).
 apply plus_resp_leEq_lft.
 apply mult_resp_nonneg;[|apply less_leEq; auto with *].
 rewrite (Z_to_nat_correct l).
 stepr (nring (Z_to_nat l):IR); [| now auto with *].
 apply nring_nonneg.
Qed.

(**
** Derivative of Tangent

Finally, two formulas for the derivative of the tangent function and
monotonicity properties.
*)

Lemma bnd_Cos : bnd_away_zero_in_P Cosine (olor [--] (Pi [/]TwoNZ) (Pi [/]TwoNZ)).
Proof.
 intros a b Hab H.
 split.
  Included.
 set (pos2 := less_leEq _ _ _ (pos_two IR)) in *.
 assert (H0 : [0] [<] sqrt Two pos2).
  apply power_cancel_less with 2.
   apply sqrt_nonneg.
  astepl ZeroR; astepr (Two:IR); apply pos_two.
 set (Hsqrt := pos_ap_zero _ _ H0) in *.
 exists (Min (Min (Cos a) (Cos b)) ([1][/] _[//]Hsqrt)).
  elim (H _ (compact_inc_lft _ _ Hab)); intros.
  elim (H _ (compact_inc_rht _ _ Hab)); intros.
  repeat apply less_Min; try apply Cos_pos; auto.
  apply recip_resp_pos.
  apply power_cancel_less with 2.
   apply sqrt_nonneg.
  astepl ZeroR; astepr (Two:IR); apply pos_two.
 intros y Hy X.
 apply leEq_wdr with (Cos y).
  2: apply eq_transitive_unfolded with (AbsIR (Cos y)).
   2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
   2: apply less_leEq; elim (H y X); intros; apply Cos_pos; auto.
  2: apply AbsIR_wd; simpl in |- *; algebra.
 elim (less_cotransitive_unfolded _ _ _ pos_QuarterPi y); intros.
  eapply leEq_transitive.
   apply Min_leEq_lft.
  apply leEq_transitive with (Cos b).
   apply Min_leEq_rht.
  elim (H _ (compact_inc_rht _ _ Hab)); elim (H y X); intros.
  inversion_clear X.
  apply Cos_resp_leEq; auto; apply less_leEq; auto.
  apply less_transitive_unfolded with (Pi [/]TwoNZ); PiSolve.
 elim (less_cotransitive_unfolded _ _ _ neg_invQuarterPi y); intros.
  2: eapply leEq_transitive.
   2: apply Min_leEq_lft.
  2: apply leEq_transitive with (Cos a).
   2: apply Min_leEq_lft.
  2: astepl (Cos [--]a); astepr (Cos [--]y).
  2: elim (H _ (compact_inc_lft _ _ Hab)); elim (H y X); intros.
  2: inversion_clear X.
  2: apply Cos_resp_leEq; auto.
    2: astepl ( [--]ZeroR); apply less_leEq; apply inv_resp_less; auto.
   2: apply less_leEq; apply less_transitive_unfolded with (Pi [/]TwoNZ).
    2: astepr ( [--][--] (Pi [/]TwoNZ)); apply inv_resp_less; auto.
   2: PiSolve.
  2: apply inv_resp_leEq; auto.
 eapply leEq_transitive.
  apply Min_leEq_rht.
 apply leEq_wdr with (([1][/] _[//]Hsqrt) [*] (Cos (y[+]Pi [/]FourNZ) [+]Sin (y[+]Pi [/]FourNZ))).
  apply shift_div_leEq; auto.
  rstepr (Cos (y[+]Pi [/]FourNZ) [+]Sin (y[+]Pi [/]FourNZ)).
  set (z := y[+]Pi [/]FourNZ) in *.
  cut ([0] [<] z); intros.
   2: unfold z in |- *; apply shift_less_plus.
   2: astepl ( [--] (Pi [/]FourNZ)); auto.
  cut (z [<] Pi [/]TwoNZ); intros.
   2: unfold z in |- *; apply shift_plus_less.
   2: rstepr (Pi [/]FourNZ); auto.
  apply power_cancel_leEq with 2.
    auto.
   astepl (ZeroR[+][0]); apply plus_resp_leEq_both.
    apply less_leEq; apply pos_cos; try apply less_leEq; auto.
   apply less_leEq; apply Sin_pos; try apply less_leEq; auto.
   apply less_transitive_unfolded with (Pi [/]TwoNZ); PiSolve.
  simpl in |- *.
  astepl ([1][*]OneR); astepl OneR.
  apply leEq_wdr with (Cos z[^]2[+]Sin z[^]2[+]Two[*]Sin z[*]Cos z).
   2: simpl in |- *; rational.
  astepr ([1][+]Sin (Two[*]z)).
  astepl ([1][+]ZeroR); apply less_leEq.
  apply plus_resp_leEq_less.
   apply leEq_reflexive.
  apply Sin_pos.
   apply shift_less_mult' with (two_ap_zero IR).
    apply pos_two.
   astepl ZeroR; auto.
  astepl (z[*]Two).
  apply shift_mult_less with (two_ap_zero IR).
   apply pos_two.
  auto.
 apply eq_transitive_unfolded with (Cos (y[+]Pi [/]FourNZ[+][--] (Pi [/]FourNZ))).
  2: apply Cos_wd; rational.
 astepl (([1][/] _[//]Hsqrt) [*]Cos (y[+]Pi [/]FourNZ) [+]
   ([1][/] _[//]Hsqrt) [*]Sin (y[+]Pi [/]FourNZ)).
 astepl (Cos (Pi [/]FourNZ) [*]Cos (y[+]Pi [/]FourNZ) [+]
   Sin (Pi [/]FourNZ) [*]Sin (y[+]Pi [/]FourNZ)).
 astepl (Cos (Pi [/]FourNZ) [*]Cos (y[+]Pi [/]FourNZ) [+]
   [--][--] (Sin (Pi [/]FourNZ) [*]Sin (y[+]Pi [/]FourNZ))).
 astepl (Cos [--] (Pi [/]FourNZ) [*]Cos (y[+]Pi [/]FourNZ) [+]
   [--] ( [--] (Sin (Pi [/]FourNZ)) [*]Sin (y[+]Pi [/]FourNZ))).
 astepl (Cos [--] (Pi [/]FourNZ) [*]Cos (y[+]Pi [/]FourNZ) [+]
   [--] (Sin [--] (Pi [/]FourNZ) [*]Sin (y[+]Pi [/]FourNZ))).
 astepl (Cos [--] (Pi [/]FourNZ) [*]Cos (y[+]Pi [/]FourNZ) [-]
   Sin [--] (Pi [/]FourNZ) [*]Sin (y[+]Pi [/]FourNZ)).
 astepl (Cos (y[+]Pi [/]FourNZ) [*]Cos [--] (Pi [/]FourNZ) [-]
   Sin (y[+]Pi [/]FourNZ) [*]Sin [--] (Pi [/]FourNZ)).
 apply eq_symmetric_unfolded; apply Cos_plus.
Qed.

Opaque Sine Cosine.

Lemma Derivative_Tan_1 : forall H, Derivative (olor [--] (Pi [/]TwoNZ) (Pi [/]TwoNZ)) H Tang {1/} (Cosine{^}2).
Proof.
 intros.
 assert (H0 : Derivative _ H Sine Cosine).
  apply Included_imp_Derivative with realline I; Deriv.
 assert (H1 : Derivative _ H Cosine {--}Sine).
  apply Included_imp_Derivative with realline I; Deriv.
 assert (H2 : forall x : IR, olor [--] (Pi [/]TwoNZ) (Pi [/]TwoNZ) x -> Cos x [#] [0]).
  intros x H2; apply Greater_imp_ap; inversion_clear H2; apply Cos_pos; auto.
 unfold Tang in |- *.
 Derivative_Help.
  apply eq_imp_Feq.
    apply included_FDiv.
      apply included_FMinus; Included.
     Included.
    intros; simpl in |- *; apply ap_wdl with (Cos x[*]Cos x).
     apply mult_resp_ap_zero; auto.
    simpl in |- *; algebra.
   apply included_FRecip.
    Included.
   intros; simpl in |- *; apply ap_wdl with (Cos x[*]Cos x).
    apply mult_resp_ap_zero; auto.
   astepl ([1][*]Cos x[*]Cos x); simpl in |- *; algebra.
  intros x H3 Hx Hx'.
  apply eq_transitive_unfolded with (Cos x[*]Cos x[-]Sin x[*][--] (Sin x) [/] _[//]
    mult_resp_ap_zero _ _ _ (H2 x H3) (H2 x H3)).
   elim Hx; intros H4 H5.
   astepl (Part _ _ (ProjIR1 (H4, H5)) [/] _[//]
     ext2 (S:=IR) (ProjIR2 (H4, H5))).
   astepl (Part _ _ H4[/] _[//]ext2 (S:=IR) H5); clear Hx.
   apply div_wd.
    simpl in |- *.
    astepl (Part _ _ (ProjIR1 H4) [-]Part _ _ (ProjIR2 H4)).
    elim H4; clear H4; intros H6 H7.
    astepl (Part _ _ H6[-]Part _ _ H7).
    apply cg_minus_wd; simpl in |- *; algebra.
   elim H5; clear H5; intros H6 H7.
   astepl (Part _ _ H6).
   simpl in |- *; algebra.
  apply eq_transitive_unfolded with ([1][/] _[//]mult_resp_ap_zero _ _ _ (H2 x H3) (H2 x H3)).
   apply div_wd.
    2: simpl in |- *; algebra.
   astepr (Cos x[^]2[+]Sin x[^]2); simpl in |- *; rational.
  simpl in Hx'; astepr ([1][/] _[//]ext2 (S:=IR) Hx').
  apply div_wd.
   algebra.
  astepl ([1][*]Cos x[*]Cos x); simpl in |- *; algebra.
 apply Derivative_div.
   Deriv.
  Deriv.
 apply bnd_Cos.
Qed.

Lemma Derivative_Tan_2 : forall H, Derivative (olor [--] (Pi [/]TwoNZ) (Pi [/]TwoNZ)) H Tang ( [-C-][1]{+}Tang{^}2).
Proof.
 intros.
 eapply Derivative_wdr.
  2: apply Derivative_Tan_1.
 assert (H0 : forall x : IR, olor [--] (Pi [/]TwoNZ) (Pi [/]TwoNZ) x -> Cos x [#] [0]).
  intros x H0; apply Greater_imp_ap; inversion_clear H0; apply Cos_pos; auto.
 apply eq_imp_Feq.
   apply included_FRecip.
    Included.
   intros; simpl in |- *; apply ap_wdl with (Cos x[*]Cos x).
    apply mult_resp_ap_zero; auto.
   astepl ([1][*]Cos x[*]Cos x); simpl in |- *; algebra.
  apply included_FPlus.
   Included.
  apply included_FNth.
  unfold Tang in |- *; apply included_FDiv.
    Included.
   Included.
  intros; simpl in |- *; astepl (Cos x). algebra.
   simpl in |- *; algebra.
 intros x H1 Hx Hx'.
 apply eq_transitive_unfolded with ([1][/] _[//]mult_resp_ap_zero _ _ _ (H0 x H1) (H0 x H1)).
  simpl in |- *; apply div_wd.
   algebra.
  astepr ([1][*]Cos x[*]Cos x); simpl in |- *; algebra.
 astepl (Cos x[^]2[+]Sin x[^]2[/] _[//]mult_resp_ap_zero _ _ _ (H0 x H1) (H0 x H1)).
 apply eq_transitive_unfolded with ([1][+][1][*] (Sin x[/] _[//]H0 x H1) [*] (Sin x[/] _[//]H0 x H1)).
  2: simpl in |- *; apply bin_op_wd_unfolded.
   2: algebra.
  2: repeat simple apply mult_wd; try apply div_wd; algebra.
 simpl in |- *.
 rational.
Qed.

Lemma Tan_resp_less : forall x y,
 [--] (Pi [/]TwoNZ) [<] x -> y [<] Pi [/]TwoNZ -> forall Hx Hy, x [<] y -> Tan x Hx [<] Tan y Hy.
Proof.
 intros x y H H0 Hx Hy H1.
 assert (H2 : [--] (Pi [/]TwoNZ) [<] Pi [/]TwoNZ).
  apply less_transitive_unfolded with x; auto; apply less_transitive_unfolded with y; auto.
 unfold Tan in |- *.
 apply Derivative_imp_resp_less with (olor [--] (Pi [/]TwoNZ) (Pi [/]TwoNZ)) H2 ( {1/} (Cosine{^}2)).
     apply Derivative_Tan_1.
    auto.
   split; auto; apply less_transitive_unfolded with y; auto.
  split; auto; apply less_transitive_unfolded with x; auto.
 intros.
 apply less_leEq_trans with OneR.
  apply pos_one.
 apply leEq_glb.
 intros y0 H3 Hy0.
 cut (Cos y0 [#] [0]). intro H4.
  apply leEq_wdr with ([1][/] _[//]mult_resp_ap_zero _ _ _ H4 H4).
   2: simpl in |- *; rational.
  apply shift_leEq_div.
   astepr (Cos y0[^]2); apply pos_square; auto.
  astepl (Cos y0[*]Cos y0).
  apply leEq_wdl with (AbsIR (Cos y0) [^]2).
   astepr (OneR[^]2).
   apply nexp_resp_leEq.
    apply AbsIR_nonneg.
   apply AbsIR_Cos_leEq_One.
  astepl (AbsIR (Cos y0) [*]AbsIR (Cos y0)).
  eapply eq_transitive_unfolded.
   apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
  apply AbsIR_eq_x.
  astepr (Cos y0[^]2); apply sqr_nonneg.
 inversion_clear Hy0.
 apply cring_mult_ap_zero_op with OneR.
 apply cring_mult_ap_zero with (Cos y0).
 simpl in |- *; simpl in X0; auto.
Qed.

Lemma Tan_resp_leEq : forall x y,
 [--] (Pi [/]TwoNZ) [<] x -> y [<] Pi [/]TwoNZ -> forall Hx Hy, x [<=] y -> Tan x Hx [<=] Tan y Hy.
Proof.
 intros x y H H0 Hx Hy H1.
 unfold Tan in |- *.
 set (H2 := invHalfPi_less_HalfPi) in *.
 apply Derivative_imp_resp_leEq with (olor [--] (Pi [/]TwoNZ) (Pi [/]TwoNZ)) H2 ( {1/} (Cosine{^}2)).
     apply Derivative_Tan_1.
    auto.
   split; auto; apply leEq_less_trans with y; auto.
  split; auto; apply less_leEq_trans with x; auto.
 intros.
 apply leEq_glb.
 intros y0 H3 Hy0.
 cut (Cos y0 [#] [0]). intro H4.
  apply leEq_wdr with (([1][/] _[//]H4) [^]2).
   apply sqr_nonneg.
  simpl in |- *; rational.
 inversion_clear Hy0.
 apply cring_mult_ap_zero_op with OneR.
 apply cring_mult_ap_zero with (Cos y0).
 simpl in |- *; simpl in X0; auto.
Qed.

End Tangent.

Hint Resolve Derivative_Tan_1 Derivative_Tan_2: derivate.
