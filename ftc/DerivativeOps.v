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

Require Export Derivative.

Section Lemmas.

(**
** Algebraic Operations

We will now prove the main results about deriving functions built from
the algebraic operators#. #%\footnote{%Composition presents some
tricky questions, and is therefore discussed in a separated
context.%}.%

[F'] and [G'] will be the derivatives, respectively, of [F] and [G].

We begin with some technical stuff that will be necessary for division.
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variable F : PartIR.
(* begin hide *)
Let P := Dom F.
(* end hide *)

(* begin show *)
Hypothesis Fbnd : bnd_away_zero I F.
(* end show *)

Lemma bnd_away_zero_square : bnd_away_zero I (F{*}F).
elim Fbnd; clear Fbnd; intros H H0.
elim H0; clear H0; intros x H1 H2.
split.
Included.
exists (x[*]x).
astepl (ZeroR[*]Zero); apply mult_resp_less_both; try apply leEq_reflexive;
 assumption.
intros y Hy H0.
unfold I in H;
 apply leEq_wdr with (AbsIR (FRestr H y H0)[*]AbsIR (FRestr H y H0)).
apply mult_resp_leEq_both; try (apply less_leEq; assumption); simpl in |- *;
 apply H2; try assumption.
eapply eq_transitive_unfolded.
apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
apply AbsIR_wd; simpl in |- *; rational.
Qed.

End Lemmas.

Hint Resolve bnd_away_zero_square: included.

Section Local_Results.

(**
** Local Results

We can now derive all the usual rules for deriving constant and identity functions, sums, inverses and products of functions with a known derivative.
*)

Variables a b : IR.
Hypothesis Hab' : a [<] b.

(* begin hide *)
Let Hab := less_leEq _ _ _ Hab'.
Let I := Compact Hab.
(* end hide *)

Lemma Derivative_I_const : forall c : IR, Derivative_I Hab' [-C-]c [-C-]Zero.
intros.
apply Derivative_I_char.
Included.
Included.
intros e He.
exists OneR.
apply pos_one.
intros.
simpl in |- *.
apply leEq_wdl with ZeroR.
astepl (ZeroR[*]Zero); apply mult_resp_leEq_both; try apply leEq_reflexive.
apply less_leEq; assumption.
apply AbsIR_nonneg.
eapply eq_transitive_unfolded.
apply eq_symmetric_unfolded; apply AbsIRz_isz.
apply AbsIR_wd; rational.
Qed.

Lemma Derivative_I_id : Derivative_I Hab' FId [-C-]One.
intros.
apply Derivative_I_char.
Included.
Included.
intros e He.
exists e.
assumption.
intros.
apply leEq_wdl with ZeroR.
astepl (ZeroR[*]Zero); apply mult_resp_leEq_both; try apply leEq_reflexive.
apply less_leEq; assumption.
apply AbsIR_nonneg.
eapply eq_transitive_unfolded.
apply eq_symmetric_unfolded; apply AbsIRz_isz.
apply AbsIR_wd; simpl in |- *; rational.
Qed.

Variables F F' G G' : PartIR.

Hypothesis derF : Derivative_I Hab' F F'.
Hypothesis derG : Derivative_I Hab' G G'.

Lemma Derivative_I_plus : Derivative_I Hab' (F{+}G) (F'{+}G').
elim derF; intros incF H1.
elim H1; intros incF' H2.
elim derG; intros incG H5.
elim H5; intros incG' H6.
clear H5 H1.
apply Derivative_I_char.
Included.
Included.
intros e He.
elim (H2 _ (pos_div_two _ _ He)).
intros df H H0.
elim (H6 _ (pos_div_two _ _ He)).
intros dg H1 H3.
clear H2 H6.
exists (Min df dg).
apply less_Min; assumption.
intros.
rstepr (e [/]TwoNZ[*]AbsIR (y[-]x)[+]e [/]TwoNZ[*]AbsIR (y[-]x));
 simpl in |- *.
set (fx := F x (ProjIR1 Hx)) in *.
set (fy := F y (ProjIR1 Hy)) in *.
set (gx := G x (ProjIR2 Hx)) in *.
set (gy := G y (ProjIR2 Hy)) in *.
set (f'x := F' x (ProjIR1 Hx')) in *.
set (g'x := G' x (ProjIR2 Hx')) in *.
apply
 leEq_wdl with (AbsIR (fy[-]fx[-]f'x[*](y[-]x)[+](gy[-]gx[-]g'x[*](y[-]x)))).
eapply leEq_transitive.
apply triangle_IR.
apply plus_resp_leEq_both; unfold fx, fy, gx, gy, f'x, g'x in |- *;
 [ apply H0 | apply H3 ]; try assumption;
 apply leEq_transitive with (Min df dg).
assumption.
apply Min_leEq_lft.
assumption.
apply Min_leEq_rht.
apply AbsIR_wd; rational.
Qed.

Lemma Derivative_I_inv : Derivative_I Hab' {--}F {--}F'.
clear derG.
elim derF; intros incF H1.
elim H1; intros incF' H2.
clear H1.
apply Derivative_I_char.
Included.
Included.
intros e He.
elim (H2 e He); intros d H0 H1.
exists d.
assumption.
intros.
simpl in |- *.
apply leEq_wdl with (AbsIR [--](F y Hy[-]F x Hx[-]F' x Hx'[*](y[-]x))).
eapply leEq_wdl.
2: apply AbsIR_inv.
auto.
apply AbsIR_wd; rational.
Qed.

Lemma Derivative_I_mult : Derivative_I Hab' (F{*}G) (F{*}G'{+}F'{*}G).
elim derF; intros incF H1.
elim H1; intros incF' H2.
elim derG; intros incG H5.
elim H5; intros incG' H6.
clear H5 H1.
set (contF := deriv_imp_contin_I _ _ _ _ _ (less_leEq _ _ _ Hab') derF) in *.
set (contG := deriv_imp_contin_I _ _ _ _ _ (less_leEq _ _ _ Hab') derG) in *.
set (contG' := deriv_imp_contin'_I _ _ _ _ _ (less_leEq _ _ _ Hab') derG)
 in *.
set (nF := Norm_Funct contF) in *.
set (nG := Norm_Funct contG) in *.
set (nG' := Norm_Funct contG') in *.
apply Derivative_I_char.
Contin.
Contin.
intros e He.
set (M := Max (Max nF nG) nG'[+]One) in *.
cut (Zero [<] M).
intro HM'.
cut (M [#] Zero).
intro HM.
2: apply Greater_imp_ap; assumption.
cut (Three[*]M [#] Zero).
intro H3M.
2: apply mult_resp_ap_zero; [ apply three_ap_zero | assumption ].
cut (Zero [<] (e[/] _[//]H3M)).
intro HeM.
elim (contin_prop _ _ _ _ contF _ HeM); intros dc H H0.
elim (H2 _ HeM); intros df H1 H3.
elim (H6 _ HeM); intros dg H4 H5.
clear H2 H6.
set (d := Min (Min df dg) dc) in *.
exists d.
unfold d in |- *; repeat apply less_Min; assumption.
intros x y H2 H6 Hx Hy Hx' H7.
simpl in |- *.
set (fx := F x (ProjIR1 Hx)) in *.
set (fy := F y (ProjIR1 Hy)) in *.
set (gx := G x (ProjIR2 Hx)) in *.
set (gy := G y (ProjIR2 Hy)) in *.
set (f'x := F' x (ProjIR1 (ProjIR2 Hx'))) in *.
set (g'x := G' x (ProjIR2 (ProjIR1 Hx'))) in *.
apply
 leEq_wdl with (AbsIR (fy[*]gy[-]fx[*]gx[-](fx[*]g'x[+]f'x[*]gx)[*](y[-]x))).
2: apply AbsIR_wd; unfold fx, f'x, gx, g'x in |- *; rational.
apply
 leEq_wdl
  with
    (AbsIR
       (fy[*](gy[-]gx[-]g'x[*](y[-]x))[+](fy[-]fx)[*]g'x[*](y[-]x)[+]
        gx[*](fy[-]fx[-]f'x[*](y[-]x)))).
astepr (e[*]AbsIR (y[-]x)).
rstepr
 (e [/]ThreeNZ[*]AbsIR (y[-]x)[+]e [/]ThreeNZ[*]AbsIR (y[-]x)[+]
  e [/]ThreeNZ[*]AbsIR (y[-]x)).
eapply leEq_transitive; [ apply triangle_IR | apply plus_resp_leEq_both ].
eapply leEq_transitive; [ apply triangle_IR | apply plus_resp_leEq_both ].
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
apply leEq_transitive with (M[*]AbsIR (gy[-]gx[-]g'x[*](y[-]x))).
apply mult_resp_leEq_rht;
 [ apply leEq_transitive with nF | apply AbsIR_nonneg ].
unfold nF, I, fy in |- *; apply norm_bnd_AbsIR.
assumption.
unfold M in |- *; eapply leEq_transitive.
2: apply less_leEq; apply less_plusOne.
eapply leEq_transitive.
2: apply lft_leEq_Max.
apply lft_leEq_Max.
apply shift_mult_leEq' with HM.
assumption.
rstepr ((e[/] _[//]H3M)[*]AbsIR (y[-]x)).
unfold gx, gy, g'x in |- *; apply H5; try assumption.
apply leEq_transitive with d.
assumption.
unfold d in |- *; eapply leEq_transitive;
 [ apply Min_leEq_lft | apply Min_leEq_rht ].
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
apply mult_resp_leEq_rht.
2: apply AbsIR_nonneg.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
apply leEq_transitive with (AbsIR (fy[-]fx)[*]M).
apply mult_resp_leEq_lft.
unfold M in |- *; eapply leEq_transitive.
2: apply less_leEq; apply less_plusOne.
eapply leEq_transitive.
2: apply rht_leEq_Max.
unfold nG', I, g'x in |- *; apply norm_bnd_AbsIR; assumption.
apply AbsIR_nonneg.
apply shift_mult_leEq with HM.
assumption.
rstepr (e[/] _[//]H3M).
unfold fx, fy in |- *; apply H0; try assumption.
apply leEq_transitive with d.
2: unfold d in |- *; apply Min_leEq_rht.
eapply leEq_wdl.
apply H7.
apply AbsIR_minus.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
apply leEq_transitive with (M[*]AbsIR (fy[-]fx[-]f'x[*](y[-]x))).
apply mult_resp_leEq_rht;
 [ apply leEq_transitive with nG | apply AbsIR_nonneg ].
unfold nG, I, gx in |- *; apply norm_bnd_AbsIR; assumption.
unfold M in |- *; eapply leEq_transitive.
2: apply less_leEq; apply less_plusOne.
eapply leEq_transitive.
2: apply lft_leEq_Max.
apply rht_leEq_Max.
apply shift_mult_leEq' with HM.
assumption.
rstepr ((e[/] _[//]H3M)[*]AbsIR (y[-]x)).
unfold fx, fy, f'x in |- *; apply H3; try assumption.
apply leEq_transitive with d.
assumption.
unfold d in |- *; eapply leEq_transitive;
 [ apply Min_leEq_lft | apply Min_leEq_lft ].
apply AbsIR_wd; rational.
apply div_resp_pos.
astepl (Three[*]ZeroR); apply mult_resp_less_lft.
assumption.
apply pos_three.
assumption.
unfold M in |- *; eapply leEq_less_trans.
2: apply less_plusOne.
eapply leEq_transitive.
2: apply rht_leEq_Max.
unfold nG' in |- *; apply positive_norm.
Qed.

(**
As was the case for continuity, the rule for the reciprocal function has a side condition.
*)

(* begin show *)
Hypothesis Fbnd : bnd_away_zero I F.
(* end show *)

Lemma Derivative_I_recip : Derivative_I Hab' {1/}F {--} (F'{/}F{*}F).
cut (forall (x : IR) (Hx : I x) Hx', F x Hx' [#] Zero).
cut (forall (x : IR) (Hx : I x) Hx', (F{*}F) x Hx' [#] Zero).
intros Hff Hf.
clear derG.
elim derF; intros incF H1.
elim H1; intros incF' H2.
assert (contF := deriv_imp_contin_I _ _ _ _ _ Hab derF).
assert (contF' := deriv_imp_contin'_I _ _ _ _ _ Hab derF).
assert (contF_ := contin_prop _ _ _ _ contF).
clear H1.
apply Derivative_I_char.
Contin.
Contin.
intros e He.
cut (Continuous_I Hab {1/}F); [ intro H | Contin ].
set (nF1 := Norm_Funct H) in *.
set (nF' := Norm_Funct contF') in *.
set (M := Max nF1 nF'[+]One) in *.
cut (Zero [<] M).
intro HM.
cut (M [#] Zero).
intro H0.
2: apply Greater_imp_ap; assumption.
cut (Two[*]M[*]M [#] Zero).
intro HM2.
cut (Two[*]M[*]M[*]M[*]M [#] Zero).
intro HM4.
cut (Zero [<] (e[/] _[//]HM2)).
intro HeM2.
cut (Zero [<] (e[/] _[//]HM4)).
intro HeM4.
elim (contF_ _ HeM4).
intros d1 H1 H3.
elim (H2 _ HeM2).
intros d2 H4 H5.
clear H2.
exists (Min d1 d2).
apply less_Min; assumption.
intros x y H2 H6 Hx Hy Hx' H7.
cut (forall (x : IR) (Hx : I x) Hx', AbsIR (One[/] _[//]Hf x Hx Hx') [<=] M).
intro leEqM.
2: intros z Hz Hz'.
2: apply leEq_wdl with (AbsIR ( {1/}F z (contin_imp_inc _ _ _ _ H z Hz))).
2: unfold M in |- *; eapply leEq_transitive.
3: apply less_leEq; apply less_plusOne.
2: eapply leEq_transitive.
3: apply lft_leEq_Max.
2: unfold nF1 in |- *; apply norm_bnd_AbsIR; assumption.
2: apply AbsIR_wd; simpl in |- *; algebra.
cut (Dom F x);
 [ intro Hxx
 | simpl in Hx; unfold extend in Hx; inversion_clear Hx; assumption ].
cut (Dom F y);
 [ intro Hyy
 | simpl in Hy; unfold extend in Hy; inversion_clear Hy; assumption ].
cut (Dom F' x);
 [ intro Hxx'
 | simpl in Hx'; unfold extend in Hx'; inversion_clear Hx'; assumption ].
apply
 leEq_wdl
  with
    (AbsIR
       ((One[/] _[//]Hf y H6 Hyy)[-](One[/] _[//]Hf x H2 Hxx)[+]
        (F' x Hxx'[/] _[//]
         mult_resp_ap_zero _ _ _ (Hf x H2 Hxx) (Hf x H2 Hxx))[*](
        y[-]x))).
apply
 leEq_wdl
  with
    (AbsIR
       ([--](One[/] _[//]mult_resp_ap_zero _ _ _ (Hf x H2 Hxx) (Hf y H6 Hyy))[*]
        (F y Hyy[-]F x Hxx[-]F' x Hxx'[*](y[-]x)[+]
         F' x Hxx'[*](F x Hxx[-]F y Hyy[/] _[//]Hf x H2 Hxx)[*](y[-]x)))).
2: apply AbsIR_wd; rational.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
rstepr (M[*]M[*]((e[/] _[//]mult_resp_ap_zero _ _ _ H0 H0)[*]AbsIR (y[-]x))).
apply mult_resp_leEq_both; try apply AbsIR_nonneg.
eapply leEq_wdl.
2: apply AbsIR_inv.
apply
 leEq_wdl
  with (AbsIR ((One[/] _[//]Hf x H2 Hxx)[*](One[/] _[//]Hf y H6 Hyy))).
2: apply AbsIR_wd; rational.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
apply mult_resp_leEq_both; try apply AbsIR_nonneg; apply leEqM.
eapply leEq_transitive.
apply triangle_IR.
rstepr ((e[/] _[//]HM2)[*]AbsIR (y[-]x)[+](e[/] _[//]HM2)[*]AbsIR (y[-]x)).
apply plus_resp_leEq_both.
apply H5; try assumption.
eapply leEq_transitive.
apply H7.
apply Min_leEq_rht.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
apply mult_resp_leEq_rht.
2: apply AbsIR_nonneg.
apply
 leEq_wdl
  with (AbsIR ((F x Hxx[-]F y Hyy)[*](F' x Hxx'[/] _[//]Hf x H2 Hxx))).
2: apply AbsIR_wd; rational.
rstepr ((e[/] _[//]HM4)[*](M[*]M)).
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
apply mult_resp_leEq_both; try apply AbsIR_nonneg.
apply H3; try assumption.
eapply leEq_transitive.
apply H7.
apply Min_leEq_lft.
apply leEq_wdl with (AbsIR (F' x Hxx'[*](One[/] _[//]Hf x H2 Hxx))).
2: apply AbsIR_wd; rational.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
apply mult_resp_leEq_both; try apply AbsIR_nonneg.
unfold M in |- *; eapply leEq_transitive.
2: apply less_leEq; apply less_plusOne.
eapply leEq_transitive.
2: apply rht_leEq_Max.
unfold nF' in |- *; apply norm_bnd_AbsIR; assumption.
apply leEqM.
apply AbsIR_wd.
simpl in |- *; rational.
apply div_resp_pos.
repeat (astepl (ZeroR[*]Zero); apply mult_resp_less_both);
 try apply leEq_reflexive; try assumption.
apply pos_two.
assumption.
apply div_resp_pos.
repeat (astepl (ZeroR[*]Zero); apply mult_resp_less_both);
 try apply leEq_reflexive; try assumption.
apply pos_two.
assumption.
repeat apply mult_resp_ap_zero; try assumption.
apply two_ap_zero.
repeat apply mult_resp_ap_zero; try assumption.
apply two_ap_zero.
unfold M in |- *; eapply leEq_less_trans.
2: apply less_plusOne.
eapply leEq_transitive.
2: apply lft_leEq_Max.
unfold nF1 in |- *; apply positive_norm.
intros.
apply bnd_imp_ap_zero with I; auto.
unfold I in |- *; Included.
intros.
apply bnd_imp_ap_zero with I; auto.
Qed.

End Local_Results.

Hint Immediate derivative_imp_inc derivative_imp_inc': included.

Hint Resolve Derivative_I_const Derivative_I_id Derivative_I_plus
  Derivative_I_inv Derivative_I_mult Derivative_I_recip: derivate.

Section Corolaries.

Variables a b : IR.
Hypothesis Hab' : a [<] b.

(* begin hide *)
Let Hab := less_leEq _ _ _ Hab'.
Let I := Compact Hab.
(* end hide *)

Variables F F' G G' : PartIR.

Hypothesis derF : Derivative_I Hab' F F'.
Hypothesis derG : Derivative_I Hab' G G'.

(**
From this lemmas the rules for the other algebraic operations follow directly.
*)

Lemma Derivative_I_minus : Derivative_I Hab' (F{-}G) (F'{-}G').
apply Derivative_I_wdl with (F{+}{--}G).
FEQ.
apply Derivative_I_wdr with (F'{+}{--}G').
FEQ.
Deriv.
Qed.

Lemma Derivative_I_scal : forall c : IR, Derivative_I Hab' (c{**}F) (c{**}F').
intro.
unfold Fscalmult in |- *.
apply Derivative_I_wdr with ([-C-]c{*}F'{+}[-C-]Zero{*}F).
FEQ.
Deriv.
Qed.

Lemma Derivative_I_nth : forall n, Derivative_I Hab' (F{^}S n) (nring (S n) {**} (F'{*}F{^}n)).
unfold Fscalmult in |- *.
intro; induction  n as [| n Hrecn].
apply Derivative_I_wdl with F.
FEQ.
apply Derivative_I_wdr with F'.
FEQ.
assumption.
apply Derivative_I_wdl with (F{*}F{^}S n).
apply FNth_mult'; Included.
apply
 Derivative_I_wdr
  with (F{*} ([-C-](nring (S n)) {*} (F'{*}F{^}n)) {+}F'{*}F{^}S n).
apply eq_imp_Feq.
Included.
Included.
intros; simpl in |- *.
set (fx := F x (ProjIR1 (ProjIR1 Hx))) in *; simpl in (value of fx);
 fold fx in |- *.
set (f'x := F' x (ProjIR1 (ProjIR2 (ProjIR2 (ProjIR1 Hx))))) in *;
 simpl in (value of f'x); fold f'x in |- *.
set (fx' := F x (ProjIR2 (ProjIR2 (ProjIR2 (ProjIR1 Hx))))) in *;
 simpl in (value of fx'); fold fx' in |- *.
set (f'x' := F' x (ProjIR1 (ProjIR2 Hx))) in *; simpl in (value of f'x');
 fold f'x' in |- *.
set (fx'' := F x (ProjIR2 (ProjIR2 Hx))) in *; simpl in (value of fx'');
 fold fx'' in |- *.
set (f'x'' := F' x (ProjIR1 (ProjIR2 Hx'))) in *; simpl in (value of f'x'');
 fold f'x'' in |- *.
set (fx''' := F x (ProjIR2 (ProjIR2 Hx'))) in *; simpl in (value of fx''');
 fold fx''' in |- *.
apply
 eq_transitive_unfolded
  with (fx[*]((nring n[+]One)[*](f'x[*]fx[^]n))[+]f'x[*](fx[^]n[*]fx)).
astepl (fx[*]((nring n[+]One)[*](f'x[*]fx'[^]n))[+]f'x'[*](fx''[^]n[*]fx'')).
repeat apply bin_op_wd_unfolded; try apply nexp_wd;
 unfold fx, f'x, fx', f'x', fx'' in |- *; rational.
rstepl ((nring n[+]One[+]One)[*](f'x[*](fx[^]n[*]fx))).
astepr ((nring n[+]One[+]One)[*](f'x''[*](fx'''[^]n[*]fx'''))).
repeat apply bin_op_wd_unfolded; try apply nexp_wd;
 unfold fx, f'x, f'x'', fx''' in |- *; rational.
Deriv.
Qed.

Lemma Derivative_I_poly : forall p, Derivative_I Hab' (FPoly _ p) (FPoly _ (_D_ p)).
Proof.
induction p.
 apply Derivative_I_wdl with ([-C-] Zero).
  FEQ.
 apply Derivative_I_wdr with ([-C-] Zero).
  FEQ.
 Deriv.
simpl.
change (FPoly IR (cpoly_linear IR s p))
 with (FPoly IR (s[+X*]p)).
change (FPoly IR (cpoly_plus_cs IR p (cpoly_linear IR Zero (cpoly_diff IR p))))
 with (FPoly IR (p[+](Zero[+X*](_D_ p)))).
apply Derivative_I_wdl with ([-C-] s{+}FId{*}(FPoly IR p)).
 repeat constructor.
 reflexivity.
apply Derivative_I_wdr with ([-C-]Zero{+}(FId{*}(FPoly IR (_D_ p)){+}[-C-]One{*}(FPoly IR p))).
 repeat constructor.
 simpl.
 intros x _ _ _.
 change (Zero[+](x[*](_D_ p)!x[+]One[*]p!x)[=]
   (p[+](Zero[+X*](_D_ p)))!x).
 rewrite cpoly_lin.
 autorewrite with apply.
 rational.
Deriv.
Qed.

Hypothesis Gbnd : bnd_away_zero I G.

Lemma Derivative_I_div : Derivative_I Hab' (F{/}G) ((F'{*}G{-}F{*}G') {/}G{*}G).
cut (Derivative_I Hab' (F{/}G) (F{*}{--} (G'{/}G{*}G) {+}F'{*}{1/}G)).
intro H.
eapply Derivative_I_wdr.
2: apply H.
apply eq_imp_Feq.
Included.
apply included_FDiv.
Included.
Included.
intros; apply bnd_imp_ap_zero with I; unfold I in |- *; Included.
intros; simpl in |- *; rational.
apply Derivative_I_wdl with (F{*}{1/}G).
FEQ.
Deriv.
Qed.

End Corolaries.

Hint Resolve Derivative_I_minus Derivative_I_nth Derivative_I_scal
  Derivative_I_div Derivative_I_poly: derivate.

Section Derivative_Sums.

(** The derivation rules for families of functions are easily proved by
induction using the constant and addition rules.
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
Hypothesis Hab' : a [<] b.

(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Lemma Derivative_I_Sum0 : forall f f' : nat -> PartIR,
 (forall n, Derivative_I Hab' (f n) (f' n)) -> forall n, Derivative_I Hab' (FSum0 n f) (FSum0 n f').
intros.
induction  n as [| n Hrecn].
eapply Derivative_I_wdl.
apply FSum0_0; Included.
eapply Derivative_I_wdr.
apply FSum0_0; Included.
apply Derivative_I_const.
eapply Derivative_I_wdl.
apply FSum0_S; Included.
eapply Derivative_I_wdr.
apply FSum0_S; Included.
apply Derivative_I_plus; auto.
Qed.

Lemma Derivative_I_Sumx : forall n (f f' : forall i, i < n -> PartIR),
 (forall i Hi Hi', Derivative_I Hab' (f i Hi) (f' i Hi')) ->
 Derivative_I Hab' (FSumx n f) (FSumx n f').
intro; induction  n as [| n Hrecn]; intros f f' derF.
simpl in |- *; apply Derivative_I_const; auto.
simpl in |- *; apply Derivative_I_plus; auto.
Qed.

Lemma Derivative_I_Sum : forall f f' : nat -> PartIR, (forall n, Derivative_I Hab' (f n) (f' n)) ->
 forall m n, Derivative_I Hab' (FSum m n f) (FSum m n f').
intros.
eapply Derivative_I_wdl.
apply Feq_symmetric; apply FSum_FSum0'; Included.
eapply Derivative_I_wdr.
apply Feq_symmetric; apply FSum_FSum0'; Included.
apply Derivative_I_minus; apply Derivative_I_Sum0; auto.
Qed.

End Derivative_Sums.

Hint Resolve Derivative_I_Sum0 Derivative_I_Sum Derivative_I_Sumx: derivate.
