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

Require Export CoRN.complex.CComplex.

(**
* Absolute value on [CC]
** Properties of [AbsCC] *)

Section AbsCC_properties.

Lemma AbsCC_nonneg : forall x : CC, [0] [<=] AbsCC x.
Proof.
 unfold AbsCC in |- *. intros.
 apply sqrt_nonneg.
Qed.

Lemma AbsCC_ap_zero_imp_pos : forall z : CC, AbsCC z [#] [0] -> [0] [<] AbsCC z.
Proof.
 intros z H.
 apply leEq_not_eq.
  apply AbsCC_nonneg.
 apply ap_symmetric_unfolded. assumption.
Qed.

Lemma AbsCC_wd : forall x y : CC, x [=] y -> AbsCC x [=] AbsCC y.
Proof.
 intros x y. elim x. intros x1 x2. elim y. intros y1 y2.
 simpl in |- *. unfold cc_eq in |- *. unfold AbsCC in |- *. simpl in |- *. intros.
 change (sqrt (x1[^]2[+]x2[^]2) (cc_abs_aid _ x1 x2) [=]
   sqrt (y1[^]2[+]y2[^]2) (cc_abs_aid _ y1 y2)) in |- *.
 elim H. clear H. intros.
 apply sqrt_wd. algebra.
Qed.

Hint Resolve AbsCC_wd: algebra_c.

Lemma cc_inv_abs : forall x : CC, AbsCC [--]x [=] AbsCC x.
Proof.
 intros.
 unfold AbsCC in |- *.
 apply sqrt_wd.
 apply bin_op_wd_unfolded.
  Step_final ( [--] (Re x) [^]2).
 Step_final ( [--] (Im x) [^]2).
Qed.

Hint Resolve cc_inv_abs: algebra.

Lemma cc_minus_abs : forall x y : CC, AbsCC (x[-]y) [=] AbsCC (y[-]x).
Proof.
 intros.
 apply eq_transitive_unfolded with (AbsCC [--] (y[-]x)).
  apply AbsCC_wd. rational.
  apply cc_inv_abs.
Qed.

Lemma cc_mult_abs : forall x y : CC, AbsCC (x[*]y) [=] AbsCC x[*]AbsCC y.
Proof.
 intros x y. elim x. intros x1 x2. elim y. intros y1 y2. intros.
 unfold AbsCC in |- *.
 apply sqrt_mult_wd.
 simpl in |- *.
 rational.
Qed.

Hint Resolve cc_mult_abs: algebra.

Lemma AbsCC_minzero : forall x : CC, AbsCC (x[-][0]) [=] AbsCC x.
Proof.
 intros.
 apply AbsCC_wd.
 algebra.
Qed.

Lemma AbsCC_IR : forall x : IR, [0] [<=] x -> AbsCC (cc_IR x) [=] x.
Proof.
 intros. unfold AbsCC in |- *.
 change (sqrt (x[^]2[+][0][^]2) (cc_abs_aid _ x [0]) [=] x) in |- *.
 apply eq_transitive_unfolded with (sqrt (x[^]2) (sqr_nonneg _ x)).
  apply sqrt_wd. rational.
  apply sqrt_to_nonneg. auto.
Qed.

Hint Resolve AbsCC_IR: algebra.

Lemma cc_div_abs : forall (x y : CC) y_ y__, AbsCC (x[/] y[//]y_) [=] (AbsCC x[/] AbsCC y[//]y__).
Proof.
 intros x y nz anz.
 rstepl (AbsCC y[*]AbsCC (x[/] y[//]nz) [/] AbsCC y[//]anz).
 apply div_wd. 2: algebra.
  astepl (AbsCC (y[*] (x[/] y[//]nz))).
 apply AbsCC_wd. rational.
Qed.

Lemma cc_div_abs' : forall (x : CC) (y : IR) y_ y__,
 [0] [<=] y -> AbsCC (x[/] cc_IR y[//]y__) [=] (AbsCC x[/] y[//]y_).
Proof.
 intros x y nz cnz H.
 rstepl (y[*]AbsCC (x[/] cc_IR y[//]cnz) [/] y[//]nz).
 apply div_wd. 2: algebra.
  astepl (AbsCC (cc_IR y) [*]AbsCC (x[/] cc_IR y[//]cnz)).
 astepl (AbsCC (cc_IR y[*] (x[/] cc_IR y[//]cnz))).
 apply AbsCC_wd.
 rational.
Qed.

Lemma AbsCC_zero : AbsCC [0] [=] [0].
Proof.
 astepl (AbsCC (cc_IR [0])).
 apply AbsCC_IR.
 apply leEq_reflexive.
Qed.

Hint Resolve AbsCC_zero: algebra.

Lemma AbsCC_one : AbsCC [1] [=] [1].
Proof.
 astepl (AbsCC (cc_IR [1])).
 apply AbsCC_IR.
 apply less_leEq. apply pos_one.
Qed.

Lemma cc_pow_abs : forall (x : CC) (n : nat), AbsCC (x[^]n) [=] AbsCC x[^]n.
Proof.
 intros. induction  n as [| n Hrecn]; intros.
 simpl in |- *. apply AbsCC_one.
  simpl in |- *. Step_final (AbsCC (x[^]n) [*]AbsCC x).
Qed.

Lemma AbsCC_pos : forall x : CC, x [#] [0] -> [0] [<] AbsCC x.
Proof.
 intro. elim x. intros x1 x2.
 unfold AbsCC in |- *. simpl in |- *. unfold cc_ap in |- *. simpl in |- *. intros H.
 change ([0] [<] sqrt (x1[^]2[+]x2[^]2) (cc_abs_aid _ x1 x2)) in |- *.
 apply power_cancel_less with 2. apply sqrt_nonneg.
  astepl ZeroR.
 astepr (x1[^]2[+]x2[^]2).
 elim H; clear H; intros.
  apply plus_resp_pos_nonneg.
   apply pos_square. auto. apply sqr_nonneg.
   apply plus_resp_nonneg_pos.
  apply sqr_nonneg. apply pos_square. auto.
Qed.

Lemma AbsCC_ap_zero : forall x : CC, [0] [#] AbsCC x -> x [#] [0].
Proof.
 intro. elim x. intros x1 x2. simpl in |- *. unfold AbsCC in |- *. unfold cc_ap in |- *.
 change ([0] [#] sqrt (x1[^]2[+]x2[^]2) (cc_abs_aid _ x1 x2) -> x1 [#] [0] or x2 [#] [0]) in |- *.
 intros H.
 cut (x1[^]2 [#] [0] or x2[^]2 [#] [0]). intro H0.
  elim H0; clear H0; intros.
   left.
   apply cring_mult_ap_zero with x1.
   astepl (x1[^]2). auto.
   right.
  apply cring_mult_ap_zero with x2.
  astepl (x2[^]2). auto.
  apply cg_add_ap_zero.
 astepl (sqrt (x1[^]2[+]x2[^]2) (cc_abs_aid _ x1 x2) [^]2).
 apply nexp_resp_ap_zero.
 apply ap_symmetric_unfolded. auto.
Qed.

Lemma AbsCC_small_imp_eq : forall x : CC, (forall e, [0] [<] e -> AbsCC x [<] e) -> x [=] [0].
Proof.
 intros x H.
 apply not_ap_imp_eq. intro.
 elim (less_irreflexive_unfolded _ (AbsCC x)).
 apply H.
 apply AbsCC_pos. auto.
Qed.

(* begin hide *)
Let l_1_1_2 :
  forall x y : IR, (x[+I*]y) [*] (x[+I*][--]y) [=] cc_IR (x[^]2[+]y[^]2).
Proof.
 intros. apply calculate_norm with (x := x) (y := y).
Qed.
(* end hide *)

Hint Resolve l_1_1_2: algebra.

Lemma AbsCC_square_Re_Im : forall x y : IR, x[^]2[+]y[^]2 [=] AbsCC (x[+I*]y) [^]2.
Proof.
 intros. unfold AbsCC in |- *.
 Step_final (Re (x[+I*]y) [^]2[+]Im (x[+I*]y) [^]2).
Qed.

Hint Resolve AbsCC_square_Re_Im: algebra.

(* begin hide *)
Let l_1_2_3_CC :
  forall x y : IR, cc_IR (x[^]2[+]y[^]2) [=] cc_IR (AbsCC (x[+I*]y) [^]2).
Proof.
 intros. apply cc_IR_wd. apply AbsCC_square_Re_Im.
Qed.
(* end hide *)

Hint Resolve l_1_2_3_CC: algebra.

Lemma AbsCC_mult_conj : forall z : CC, z[*]CC_conj z [=] cc_IR (AbsCC z[^]2).
Proof.
 intro z. unfold cc_IR in |- *.
 elim z. intros x y.
 apply eq_transitive_unfolded with (S := cc_csetoid) (y := cc_IR (x[^]2[+]y[^]2)).
  eapply l_1_1_2 with (x := x) (y := y).
 split; simpl in |- *.
  2: algebra.
 eapply AbsCC_square_Re_Im with (x := x) (y := y).
Qed.

Hint Resolve CC_conj_mult: algebra.

(* begin hide *)
Lemma l_2_1_2 :
 forall z1 z2 : CC,
 cc_IR (AbsCC (z1[*]z2) [^]2) [=] z1[*]z2[*]CC_conj z1[*]CC_conj z2.
Proof.
 intros z1 z2. apply eq_symmetric_unfolded.
 apply eq_transitive_unfolded with (z1[*]z2[*]CC_conj (z1[*]z2)).
  Step_final (z1[*]z2[*] (CC_conj z1[*]CC_conj z2)).
 apply AbsCC_mult_conj.
Qed.

Hint Resolve l_2_1_2: algebra.
(* end hide *)

Lemma AbsCC_mult_square : forall x y : CC, AbsCC (x[*]y) [^]2 [=] AbsCC x[^]2[*]AbsCC y[^]2.
Proof.
 intros. rstepr ((AbsCC x[*]AbsCC y) [^]2). algebra.
Qed.

Lemma AbsCC_square_ap_zero : forall z : CC, z [#] [0] -> AbsCC z[^]2 [#] [0].
Proof.
 intros z H.
 stepl (Re z[^]2[+]Im z[^]2).
  apply (cc_inv_aid (Re z) (Im z) H).
 apply AbsCC_square_Re_Im with (x := Re z) (y := Im z).
Qed.

Lemma cc_recip_char : forall (z : CC) z_ z__,
 cc_recip z z_ [=] (CC_conj z[/] cc_IR (AbsCC z[^]2) [//]z__).
Proof.
 intros z z_ HAbsCCz.
 unfold cc_recip in |- *.
 astepl (Re z[+I*][--] (Im z) [/] _[//] cc_IR_resp_ap _ _ (cc_inv_aid _ _ (cc_ap_zero _ z_))).
  2: simpl in |- *; split; simpl in |- *; rational.
 apply div_wd with (F := CC) (x := Re z[+I*][--] (Im z)) (y := cc_IR (Re z[^]2[+]Im z[^]2))
   (x' := CC_conj z) (y' := cc_IR (AbsCC z[^]2)).
  elim z. intros x y. simpl in |- *. split; simpl in |- *; algebra.
  apply cc_IR_wd.
 apply AbsCC_square_Re_Im with (x := Re z) (y := Im z).
Qed.

Lemma AbsCC_strext : fun_strext AbsCC.
Proof.
 unfold fun_strext in |- *.
 intros z1 z2 H.
 cut (AbsCC z1[^]2 [#] AbsCC z2[^]2).
  elim z1. intros x1 y1. elim z2. intros x2 y2.
  intro H'.
  assert (H'' : x1[^]2[+]y1[^]2 [#] x2[^]2[+]y2[^]2).
   astepl (AbsCC (x1[+I*]y1) [^]2). astepr (AbsCC (x2[+I*]y2) [^]2). assumption.
   cut (x1[^]2 [#] x2[^]2 or y1[^]2 [#] y2[^]2).
   intros H'''. elim H'''; intro H0.
   cut (x1 [#] x2).
     intro H1.
     simpl in |- *. unfold cc_ap in |- *. unfold Re, Im in |- *.
     left.
     assumption.
    apply (nexp_strong_ext IR 2).
    assumption.
   simpl in |- *. unfold cc_ap in |- *. simpl in |- *.
   right.
   apply (nexp_strong_ext IR 2).
   assumption.
  apply (bin_op_strext_unfolded _ _ _ _ _ _ H'').
 assert (H1 : AbsCC z1[-]AbsCC z2 [#] [0]).
  cut (AbsCC z1[-]AbsCC z2 [#] AbsCC z2[-]AbsCC z2).
   intro H0. astepr (AbsCC z2[-]AbsCC z2). assumption.
   apply minus_resp_ap_rht. assumption.
  assert (H2 : AbsCC z1[+]AbsCC z2 [#] [0]).
  apply Greater_imp_ap.
  assert (H0 : AbsCC z1 [#] [0] or [0] [#] AbsCC z2).
   apply ap_cotransitive_unfolded. assumption.
   elim H0.
   intro H'.
   assert (H'' : [0] [<] AbsCC z1).
    apply (AbsCC_ap_zero_imp_pos _ H').
   apply leEq_less_trans with (y := AbsCC z2).
    apply AbsCC_nonneg.
   rstepl (AbsCC z2[+][0]).
   rstepr (AbsCC z2[+]AbsCC z1).
   apply plus_resp_less_lft.
   assumption.
  intro H'.
  assert (H'' : [0] [<] AbsCC z2).
   apply AbsCC_ap_zero_imp_pos.
   apply ap_symmetric_unfolded. assumption.
   apply leEq_less_trans with (y := AbsCC z1).
   apply AbsCC_nonneg.
  rstepl (AbsCC z1[+][0]).
  apply plus_resp_less_lft.
  assumption.
 cut (AbsCC z1[^]2[-]AbsCC z2[^]2 [#] [0]).
  intro H3.
  cut (AbsCC z1[^]2[-]AbsCC z2[^]2 [#] AbsCC z2[^]2[-]AbsCC z2[^]2).
   intro H4.
   rstepl (AbsCC z1[^]2[-]AbsCC z2[^]2[+]AbsCC z2[^]2).
   rstepr ([0][+]AbsCC z2[^]2).
   apply op_rht_resp_ap with (x := AbsCC z1[^]2[-]AbsCC z2[^]2) (y := ZeroR) (z := AbsCC z2[^]2).
   rstepr (AbsCC z2[^]2[-]AbsCC z2[^]2).
   assumption.
  rstepr ZeroR.
  assumption.
 astepl ((AbsCC z1[-]AbsCC z2) [*] (AbsCC z1[+]AbsCC z2)).
 apply mult_resp_ap_zero; assumption.
Qed.

Definition AbsSmallCC (e : IR) (x : CC) := AbsCC x [<=] e.

Lemma Cexis_AFS_CC : forall x y eps, [0] [<] eps -> {y' : CC | AbsSmallCC eps (y'[-]y) | y' [#] x}.
Proof.
 unfold AbsSmallCC in |- *. intros.
 set (e := cc_IR eps) in *.
 elim (ap_cotransitive_unfolded _ (y[-]e) (y[+]e)) with x; try intro H0.
   exists (y[-]e).
    apply leEq_wdl with (AbsCC [--]e).
     unfold e in |- *.
     astepl (AbsCC (cc_IR eps)).
     apply eq_imp_leEq.
     apply AbsCC_IR.
     apply less_leEq; auto.
    apply AbsCC_wd. rational.
    auto.
  exists (y[+]e).
   apply leEq_wdl with (AbsCC e).
    apply eq_imp_leEq.
    unfold e in |- *; apply AbsCC_IR.
    apply less_leEq; auto.
   apply AbsCC_wd. rational.
   apply ap_symmetric_unfolded. auto.
  apply zero_minus_apart.
 apply ap_wdl_unfolded with (cc_IR ( [--]Two[*]eps)).
  astepr (cc_IR [0]).
  apply cc_IR_resp_ap. apply mult_resp_ap_zero.
  apply inv_resp_ap_zero. apply two_ap_zero.
   apply pos_ap_zero; auto.
 unfold e in |- *.
 astepl (cc_IR [--]Two[*]cc_IR eps).
 rstepr ( [--]Two[*]cc_IR eps).
 apply mult_wdl.
 simpl in |- *. unfold cc_eq in |- *. simpl in |- *.
 split; [ algebra | rational ].
Qed.

(* The following lemmas are just auxiliary results *)

(* begin hide *)
Let l_4_1_2 :
  forall (z : CC) (H : z [#] [0]),
  z[*]cc_recip z H [=]
  (z[*]CC_conj z[/] _[//]cc_IR_resp_ap _ _ (AbsCC_square_ap_zero _ H)).
Proof.
 intros z H.
 apply eq_transitive_unfolded with (S := cc_csetoid) (y := z[*]
   (CC_conj z[/] _[//]cc_IR_resp_ap _ _ (AbsCC_square_ap_zero _ H))).
  2: algebra.
  astepr (z[*] (CC_conj z[/] _[//]cc_IR_resp_ap _ _ (AbsCC_square_ap_zero _ H))).
  apply bin_op_wd_unfolded with (S := CC) (x1 := z) (x2 := z) (y1 := cc_recip z H)
    (y2 := CC_conj z[/] _[//]cc_IR_resp_ap _ _ (AbsCC_square_ap_zero _ H)).
   algebra.
  apply cc_recip_char.
 generalize H. clear H. elim z. intros x y H. simpl in |- *. split; simpl in |- *; rational.
Qed.

Let l_4_2_3 :
  forall (z : CC) (H : z [#] [0]),
  (z[*]CC_conj z[/] _[//]cc_IR_resp_ap _ _ (AbsCC_square_ap_zero _ H)) [=]
  (cc_IR (AbsCC z[^]2) [/] _[//]cc_IR_resp_ap _ _ (AbsCC_square_ap_zero _ H)).
Proof.
 intros z H.
 apply div_wd with (F := CC) (x := z[*]CC_conj z) (y := cc_IR (AbsCC z[^]2))
   (x' := cc_IR (AbsCC z[^]2)) (y' := cc_IR (AbsCC z[^]2)).
  apply AbsCC_mult_conj.
 algebra.
Qed.

Let l_4_3_4 :
  forall (z : CC) (H : z [#] [0]),
  (cc_IR (AbsCC z[^]2) [/] _[//]cc_IR_resp_ap _ _ (AbsCC_square_ap_zero _ H)) [=]
  [1].
Proof.
 intros.
 rational.
Qed.
(* end hide *)

End AbsCC_properties.

#[global]
Hint Resolve AbsCC_wd: algebra_c.
#[global]
Hint Resolve cc_inv_abs cc_mult_abs cc_div_abs cc_div_abs' cc_pow_abs
  AbsCC_zero AbsCC_one AbsCC_IR AbsCC_mult_conj AbsCC_mult_square
  cc_recip_char: algebra.

(**
** The triangle inequality *)

Lemma triangle : forall x y : CC, AbsCC (x[+]y) [<=] AbsCC x[+]AbsCC y.
Proof.
 intros.
 elim x. intros x1 x2.
 elim y. intros y1 y2.
 unfold AbsCC in |- *. simpl in |- *.
 apply power_cancel_leEq with 2. auto.
   astepl ([0][+]ZeroR).
  apply plus_resp_leEq_both; apply sqrt_nonneg.
 astepl ([1][*](x1[+]y1)[*](x1[+]y1)[+][1][*](x2[+]y2)[*](x2[+]y2)).
 rstepr (sqrt ([1][*]x1[*]x1[+][1][*]x2[*]x2) (cc_abs_aid _ x1 x2)[^]2[+]
   sqrt ([1][*]y1[*]y1[+][1][*]y2[*]y2) (cc_abs_aid _ y1 y2)[^]2[+]
     Two[*]sqrt ([1][*]x1[*]x1[+][1][*]x2[*]x2) (cc_abs_aid _ x1 x2)[*]
       sqrt ([1][*]y1[*]y1[+][1][*]y2[*]y2) (cc_abs_aid _ y1 y2)).
 astepr ([1][*]x1[*]x1[+][1][*]x2[*]x2[+]([1][*]y1[*]y1[+][1][*]y2[*]y2)[+]
   Two[*]sqrt ([1][*]x1[*]x1[+][1][*]x2[*]x2) (cc_abs_aid _ x1 x2)[*]
     sqrt ([1][*]y1[*]y1[+][1][*]y2[*]y2) (cc_abs_aid _ y1 y2)).
 apply shift_leEq_rht.
 rstepr (Two[*] (sqrt ([1][*]x1[*]x1[+][1][*]x2[*]x2) (cc_abs_aid _ x1 x2)[*]
   sqrt ([1][*]y1[*]y1[+][1][*]y2[*]y2) (cc_abs_aid _ y1 y2)[-] (x1[*]y1[+]x2[*]y2))).
 apply mult_resp_nonneg. apply less_leEq. apply pos_two.
  apply shift_leEq_lft.
 apply power_cancel_leEq with 2. auto.
   apply mult_resp_nonneg; apply sqrt_nonneg.
 astepr (sqrt ([1][*]x1[*]x1[+][1][*]x2[*]x2) (cc_abs_aid _ x1 x2)[^]2[*]
   sqrt ([1][*]y1[*]y1[+][1][*]y2[*]y2) (cc_abs_aid _ y1 y2)[^]2).
 astepr (([1][*]x1[*]x1[+][1][*]x2[*]x2)[*]([1][*]y1[*]y1[+][1][*]y2[*]y2)).
 apply shift_leEq_rht.
 rstepr ((x1[*]y2[-]x2[*]y1)[^]2).
 apply sqr_nonneg.
Qed.

Lemma triangle_Sum : forall m n (z : nat -> CC),
 m <= S n -> AbsCC (Sum m n z) [<=] Sum m n (fun i => AbsCC (z i)).
Proof.
 intros. induction  n as [| n Hrecn]; intros.
 generalize (toCle _ _ H); clear H; intro H.
  inversion H as [|m0 H1 H2].
   unfold Sum in |- *. unfold Sum1 in |- *.
   astepl (AbsCC [0]).
   astepr ZeroR.
   astepr (AbsCC [0]).
   apply leEq_reflexive.
  inversion H1.
  unfold Sum in |- *. unfold Sum1 in |- *. simpl in |- *.
  cut (AbsCC ([0][+]z 0[-][0])[<=][0][+]AbsCC (z 0)[-][0]).
   auto.
  apply eq_imp_leEq.
  rstepr (AbsCC (z 0)).
  apply AbsCC_wd.
  rational.
 elim (le_lt_eq_dec _ _ H); intro y.
  astepl (AbsCC (Sum m n z[+]z (S n))).
  apply leEq_wdr with (Sum m n (fun i : nat => AbsCC (z i))[+]AbsCC (z (S n))).
   apply leEq_transitive with (AbsCC (Sum m n z)[+]AbsCC (z (S n))).
    apply triangle.
   apply plus_resp_leEq.
   apply Hrecn. auto with arith.
   apply eq_symmetric_unfolded. apply Sum_last with (f := fun i : nat => AbsCC (z i)).
  rewrite y. unfold Sum in |- *. unfold Sum1 in |- *.
 astepl (AbsCC [0]).
 astepr ZeroR.
 astepr (AbsCC [0]).
 apply leEq_reflexive.
Qed.
