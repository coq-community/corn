(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* $Id$ *)

Require Export RealPowers.
Require Export TrigMon.
Require Export StrongIVT.

(** printing ArcSin %\ensuremath{\arcsin}% *)
(** printing ArcCos %\ensuremath{\arccos}% *)
(** printing ArcTan %\ensuremath{\arctan}% *)

(** *Inverse Trigonometric Functions

**Definitions

We will now define arcsine, arccosine and arctangent as indefinite
integrals and prove their main properties.  We begin by proving that
the appropriate indefinite integrals can be defined, then prove the
main properties of the function.

Arccosine is defined in terms of arcsine by the relation
[ArcCos(x)=Pi[/]Two-ArcSin(x)].

***Arcsine
*)

Opaque Sine Cosine Expon Logarithm.

Lemma ArcSin_def_lemma : Continuous (olor [--]One One) (( [-C-]One{-}FId{^}2) {!} [-C-] [--] (One [/]TwoNZ)).
split.
unfold FPower in |- *.
apply included_FComp.
apply included_FMult.
Included.
apply included_FComp.
Included.
intros; apply Log_domain.
inversion_clear X.
simpl in |- *; apply shift_less_minus; astepl (x[^]2).
astepr (OneR[^]2).
apply AbsIR_less_square.
simpl in |- *; unfold ABSIR in |- *; apply Max_less; auto.
apply inv_cancel_less; astepr x; auto.
intros; apply Exp_domain.
intros a b Hab H.
apply continuous_I_power.
Contin.
Contin.
split.
Included.
simpl in H.
set (c := Max (AbsIR a) (AbsIR b)) in *.
cut (Zero [<=] c); intros.
2: unfold c in |- *; apply leEq_transitive with (AbsIR a);
    [ apply AbsIR_nonneg | apply lft_leEq_Max ].
elim (H _ (compact_inc_lft _ _ Hab)); intros.
elim (H _ (compact_inc_rht _ _ Hab)); intros.
assert (H1 : c [<] One).
 unfold c in |- *.
 apply Max_less; simpl in |- *; unfold ABSIR in |- *; apply Max_less; auto;
  apply inv_cancel_less.
 astepr a; auto. astepr b; auto.
assert (Hc : [--]c [<=] c). apply leEq_transitive with ZeroR; auto.
 astepr ( [--]ZeroR); apply inv_resp_leEq; auto.
cut (included (Compact Hab) (Compact Hc)). intro H2.
exists (One[-]c[^]2).
apply shift_less_minus.
astepl (c[^]2); astepr (OneR[^]2).
apply nexp_resp_less; auto.
intros y H3 Hy.
astepr (One[-]y[^]2).
apply minus_resp_leEq_both.
apply leEq_reflexive.
apply AbsIR_leEq_square.
elim (H2 _ H3); intros.
simpl in |- *; unfold ABSIR in |- *; apply Max_leEq; auto.
astepr ( [--] [--]c); apply inv_resp_leEq; auto.
intros x H2.
inversion_clear H2; unfold c in |- *; split.
astepr ( [--] [--]x); apply inv_resp_leEq.
apply leEq_transitive with ( [--]a).
apply inv_resp_leEq; auto.
eapply leEq_transitive; [ apply inv_leEq_AbsIR | apply lft_leEq_Max ].
apply leEq_transitive with b; auto.
eapply leEq_transitive; [ apply leEq_AbsIR | apply rht_leEq_Max ].
Qed.

Lemma ArcSin_def_zero : olor [--]One One Zero.
split.
astepr ( [--]ZeroR); apply inv_resp_less; apply pos_one.
apply pos_one.
Qed.

Definition ArcSin := ( [-S-]ArcSin_def_lemma) _ ArcSin_def_zero.

Lemma ArcSin_domain : forall x, [--]One [<] x -> x [<] One -> Dom ArcSin x.
intros; split; auto.
Qed.

Lemma Continuous_ArcSin : Continuous (olor [--]One One) ArcSin.
unfold ArcSin in |- *; apply Continuous_prim.
Qed.

Lemma Derivative_ArcSin : forall H,
 Derivative (olor [--]One One) H ArcSin (( [-C-]One{-}FId{^}2) {!} [-C-] [--] (One [/]TwoNZ)).
intros; unfold ArcSin in |- *.
apply FTC1.
Qed.

Hint Resolve Derivative_ArcSin: derivate.
Hint Resolve Continuous_ArcSin: continuous.

(** ***Arccosine
*)

Definition ArcCos := [-C-] (Pi [/]TwoNZ) {-}ArcSin.

Lemma ArcCos_domain : forall x : IR, [--]One [<] x -> x [<] One -> Dom ArcCos x.
intros; repeat split; auto.
Qed.

Lemma Continuous_ArcCos : Continuous (olor [--]One One) ArcCos.
unfold ArcCos in |- *; Contin.
Qed.

Lemma Derivative_ArcCos : forall H,
 Derivative (olor [--]One One) H ArcCos {--} (( [-C-]One{-}FId{^}2) {!} [-C-] [--] (One [/]TwoNZ)).
intros; unfold ArcCos in |- *.
apply
 Derivative_wdr
  with ( [-C-]Zero{-} ( [-C-]One{-}FId{^}2) {!} [-C-] [--] (One [/]TwoNZ)).
2: Deriv.
apply eq_imp_Feq.
apply included_FMinus.
Included.
apply Continuous_imp_inc; apply ArcSin_def_lemma.
apply included_FInv.
apply Continuous_imp_inc; apply ArcSin_def_lemma.
intros.
astepl (Part _ _ (ProjIR1 Hx) [-]Part _ _ (ProjIR2 Hx)).
astepl (Zero[-]Part _ _ (ProjIR2 Hx)).
astepl ( [--] (Part _ _ (ProjIR2 Hx))).
Step_final ( [--] ((( [-C-]One{-}FId{^}2) {!} [-C-] [--] (One [/]TwoNZ)) x Hx')).
Qed.

(** ***Arctangent
*)

Lemma ArcTan_def_lemma : Continuous realline {1/} ( [-C-]One{+}FId{^}2).
apply Continuous_recip.
Contin.
red in |- *; intros.
split.
Included.
exists OneR.
apply pos_one.
intros; simpl in |- *.
eapply leEq_transitive.
2: apply leEq_AbsIR.
apply shift_leEq_plus'.
astepl ZeroR; astepr (y[^]2).
apply sqr_nonneg.
Qed.

Definition ArcTang := ( [-S-]ArcTan_def_lemma) Zero CI.

Lemma ArcTan_domain : forall x : IR, Dom ArcTang x.
intros; simpl in |- *; auto.
Qed.

Definition ArcTan (x : IR) := ArcTang x CI.

Lemma Continuous_ArcTan : Continuous realline ArcTang.
unfold ArcTang in |- *; Contin.
Qed.

Lemma Derivative_ArcTan : forall H, Derivative realline H ArcTang {1/} ( [-C-]One{+}FId{^}2).
intros; unfold ArcTang in |- *; apply FTC1.
Qed.

Hint Resolve Derivative_ArcCos Derivative_ArcTan: derivate.
Hint Resolve Continuous_ArcCos Continuous_ArcTan: continuous.

Section Inverses.

(** **Composition properties

We now prove that this functions are in fact inverses to the corresponding trigonometric functions.

***Sine and Arcsine
*)

Lemma maps_Sin : maps_compacts_into (olor [--] (Pi [/]TwoNZ) (Pi [/]TwoNZ)) (olor [--]One One) Sine.
intros a b Hab H.
set (min := Min (Sin a) [--] (One [/]TwoNZ)) in *.
set (max := Max (Sin b) (One [/]TwoNZ)) in *.
cut (min [<] max). intro H0.
exists min; exists max; exists H0.
elim (H _ (compact_inc_lft _ _ Hab)); intros Ha1 Ha2.
elim (H _ (compact_inc_rht _ _ Hab)); intros Hb1 Hb2.
split.
intros x H1.
unfold min, max in H1; inversion_clear H1; split.
apply less_leEq_trans with min.
unfold min in |- *; apply less_Min.
apply inv_cancel_less; astepr OneR.
eapply leEq_less_trans.
apply inv_leEq_AbsIR.
apply Abs_Sin_less_One; auto.
apply inv_resp_less; apply (half_lt1 IR).
auto.
eapply leEq_less_trans.
apply H3.
apply Max_less.
eapply leEq_less_trans.
apply leEq_AbsIR.
apply Abs_Sin_less_One; auto.
apply (half_lt1 IR).
intros x Hx H1.
apply compact_wd with (Sin x).
2: simpl in |- *; Algebra.
unfold min, max in |- *; inversion_clear H1.
split.
eapply leEq_transitive; [ apply Min_leEq_lft | apply Sin_resp_leEq; auto ].
apply less_leEq; auto.
apply less_leEq; apply leEq_less_trans with b; auto.
eapply leEq_transitive.
2: apply lft_leEq_Max.
apply Sin_resp_leEq; auto.
apply leEq_transitive with a; auto; apply less_leEq; auto.
apply less_leEq; auto.
unfold min, max in |- *; apply less_transitive_unfolded with ZeroR.
eapply leEq_less_trans.
apply Min_leEq_rht.
astepr ( [--]Zero:IR); apply inv_resp_less; apply (pos_half IR).
eapply less_leEq_trans; [ apply (pos_half IR) | apply rht_leEq_Max ].
Qed.

Lemma ArcSin_Sin_inv : Feq (olor [--] (Pi [/]TwoNZ) (Pi [/]TwoNZ)) (ArcSin[o]Sine) FId.
set (HPi1 := pos_HalfPi) in *.
set (HPi2 := neg_invHalfPi) in *.
set
 (H := invHalfPi_less_HalfPi:proper (olor [--] (Pi [/]TwoNZ) (Pi [/]TwoNZ)))
 in *.
apply Feq_criterium with H ( [-C-]One:PartIR) ZeroR.
assert (H0 : Derivative _ H Sine Cosine).
 apply Included_imp_Derivative with realline CI; Deriv.
assert (H1 : [--]One [<] OneR).
 set (H' := pos_one IR) in *; apply less_transitive_unfolded with ZeroR; auto.
 astepr ( [--]ZeroR); apply inv_resp_less; auto.
set (H2 := Derivative_ArcSin H1) in *.
eapply Derivative_wdr.
2: apply (Derivative_comp _ _ _ _ _ _ _ _ maps_Sin H0 H2).
apply eq_imp_Feq.
apply included_FMult.
apply included_FComp.
Included.
intros.
unfold FPower in |- *.
cut
 (Dom ( [-C-] [--] (One [/]TwoNZ) {*} (Logarithm[o] [-C-]One{-}FId{^}2))
    (Part _ _ Hx)). intro H3.
exists H3; apply Exp_domain.
split.
auto.
exists (CAnd_intro _ _ CI CI).
apply Log_domain.
astepr (One[-]Sine x Hx[^]2).
astepl (OneR[-]One).
unfold cg_minus in |- *; apply plus_resp_less_lft.
apply inv_resp_less.
astepr (OneR[^]2); apply AbsIR_less_square.
apply less_wdl with (AbsIR (Sin x)).
inversion_clear X; apply Abs_Sin_less_One; auto.
apply AbsIR_wd; simpl in |- *; Algebra.
split.
split.
intros x H3 Hx Hx'.
astepr OneR.
cut (Zero [<] One[-]Sin x[^]2). intro H4.
apply
 eq_transitive_unfolded
  with ((One[-]Sin x[^]2) [!] [--] (One [/]TwoNZ) [//]H4[*]Cos x).
unfold power, FPower in |- *.
unfold FPower in Hx.
astepl (Part _ _ (ProjIR1 Hx) [*]Part _ _ (ProjIR2 Hx)).
apply mult_wd.
2: simpl in |- *; Algebra.
elim Hx; clear Hx; intros Hx Hx1.
astepl (Part _ _ Hx); clear Hx1.
astepl (Part _ _ (ProjT2 Hx)).
elim Hx; clear Hx; intros Hx1 Hx2.
astepl (Part _ _ Hx2).
astepl (Part _ _ (ProjT2 Hx2)).
simpl in |- *; apply pfwdef.
elim Hx2; intros Hx3 Hx4.
astepl (Part _ _ Hx3).
clear Hx4 Hx2.
astepl ( [--] (One [/]TwoNZ) [*]Part _ _ (ProjIR2 Hx3)).
elim Hx3; clear Hx3; intros Hx2 Hx3.
astepl ( [--] (One [/]TwoNZ) [*]Part _ _ Hx3).
apply mult_wdr.
astepl (Part _ _ (ProjT2 Hx3)).
unfold Log in |- *; apply pfwdef.
elim Hx3; intros Hx4 Hx5.
astepl (Part _ _ Hx4).
astepl (Part _ _ (ProjIR1 Hx4) [-]Part _ _ (ProjIR2 Hx4)).
elim Hx4; clear Hx5 Hx4 Hx3 Hx2; intros Hx2 Hx3.
astepl (Part _ _ Hx2[-]Part _ _ Hx3).
apply cg_minus_wd.
Algebra.
simpl in |- *; Algebra.
unfold power in |- *.
astepl (Exp [--] (One [/]TwoNZ[*]Log _ H4) [*]Cos x).
astepl ((One[/] _[//]Exp_ap_zero (One [/]TwoNZ[*]Log _ H4)) [*]Cos x).
astepr
 (Exp (One [/]TwoNZ[*]Log _ H4) [/] _[//]Exp_ap_zero (One [/]TwoNZ[*]Log _ H4)).
rstepl (Cos x[/] _[//]Exp_ap_zero (One [/]TwoNZ[*]Log _ H4)).
apply div_wd.
2: Algebra.
astepr (Exp (Log _ H4[*]One [/]TwoNZ)).
assert (H5 : Zero [<] Cos x). inversion_clear H3; apply Cos_pos; auto.
astepl (Exp (Log _ H5)).
apply Exp_wd.
rstepl ((Log _ H5[+]Log _ H5) [/]TwoNZ).
rstepr (Log _ H4 [/]TwoNZ).
apply div_wd.
2: Algebra.
astepl (Log _ (mult_resp_pos _ _ _ H5 H5)).
astepl (Log _ (pos_square _ _ (pos_ap_zero _ _ H5))).
apply Log_wd.
astepr (Cos x[^]2[+]Sin x[^]2[-]Sin x[^]2); rational.
astepl (OneR[-]One).
unfold cg_minus in |- *; apply plus_resp_less_lft.
apply inv_resp_less.
astepr (OneR[^]2); apply AbsIR_less_square.
inversion_clear H3; apply Abs_Sin_less_One; auto.
Deriv.
split; auto.
intros; simpl in |- *; apply Integral_empty.
astepl (Sin Zero); simpl in |- *; Algebra.
Qed.

Opaque ArcSin.

Lemma ArcSin_Sin : forall x, [--] (Pi [/]TwoNZ) [<] x -> x [<] Pi [/]TwoNZ -> forall H, ArcSin (Sin x) H [=] x.
intros.
unfold Sin in |- *.
astepr (FId x CI).
cut (Dom (ArcSin[o]Sine) x). intro H2.
apply eq_transitive_unfolded with ((ArcSin[o]Sine) x H2).
simpl in |- *; Algebra.
apply Feq_imp_eq with (olor [--] (Pi [/]TwoNZ) (Pi [/]TwoNZ)).
apply ArcSin_Sin_inv.
split; auto.
exists CI; auto.
Qed.

Lemma ArcSin_range : forall x Hx, [--] (Pi [/]TwoNZ) [<] ArcSin x Hx and ArcSin x Hx [<] Pi [/]TwoNZ.
intros.
Transparent ArcSin.
cut
 {y : IR | olor [--] (Pi [/]TwoNZ) (Pi [/]TwoNZ) y |
 forall Hy, Sine y Hy [=] x}.
intros H; elim H; clear H; intros y H H0.
elim H; clear H; intros H1 H2.
assert (H : Sin y [=] x). simpl in |- *; Algebra.
assert (H3 : Dom ArcSin (Sin y)). apply dom_wd with x; Algebra.
split.
astepr (ArcSin _ H3).
apply less_wdr with y; auto.
apply eq_symmetric_unfolded; apply ArcSin_Sin; auto.
astepl (ArcSin _ H3).
apply less_wdl with y; auto.
apply eq_symmetric_unfolded; apply ArcSin_Sin; auto.
elim Hx; intros H H0.
set (H1 := less_leEq _ _ _ invHalfPi_less_HalfPi) in *.
cut (Continuous_I H1 Sine). intro H2.
apply IVT'_I with H1 H2; auto.
PiSolve.
intros x0 y H3 H4 H5 Hx0 Hy.
2: astepl (Sine [--] (Pi [/]TwoNZ) CI); astepl (Sin [--] (Pi [/]TwoNZ));
    astepl ( [--] (Sin (Pi [/]TwoNZ))); astepl ( [--]OneR); 
    auto.
2: astepr (Sine (Pi [/]TwoNZ) CI); astepr (Sin (Pi [/]TwoNZ)); astepr OneR;
    auto.
2: apply included_imp_Continuous with realline; Contin.
apply less_wdl with (Sin x0).
2: simpl in |- *; Algebra.
apply less_wdr with (Sin y).
2: simpl in |- *; Algebra.
inversion_clear H3; inversion_clear H4; apply Sin_resp_less; auto.
Qed.

Lemma Sin_ArcSin : forall (x : IR) Hx, x [=] Sin (ArcSin x Hx).
intros.
set (y := Sin (ArcSin x Hx)) in *.
cut (Dom ArcSin y). intro H.
cut (ArcSin x Hx [=] ArcSin y H). intro H0.
2: unfold y in |- *; inversion_clear H.
2: apply eq_symmetric_unfolded.
Transparent ArcSin.
simpl in H0.
unfold y in H0.
cut
 (Continuous_I (Min_leEq_Max x y)
    (( [-C-]One{-}FId{^}2) {!} [-C-] [--] (One [/]TwoNZ))). intro H1.
cut (Integral H1 [=] Zero). intro H2.
clear H0.
elim H; intros H0 H3.
elim Hx; clear H; intros H H4.
apply Integral_eq_zero with (contF := H1) (x := x).
exact (CAnd_intro _ _ (Min_leEq_lft x y) (lft_leEq_Max x y)).
unfold FPower in |- *; intros.
astepr (Part _ _ (ProjT2 Hx0)).
apply less_wdr with (Exp (Part _ _ (ProjT1 Hx0))).
apply Exp_pos.
simpl in |- *; Algebra.
unfold FPower in |- *; intros.
apply less_leEq; astepr (Part _ _ (ProjT2 Hx0)).
apply less_wdr with (Exp (Part _ _ (ProjT1 Hx0))).
apply Exp_pos.
simpl in |- *; Algebra.
auto.
apply eq_transitive_unfolded with (ArcSin y H[-]ArcSin x Hx).
rstepl (ArcSin x Hx[+]Integral H1[-]ArcSin x Hx).
apply cg_minus_wd; [ simpl in |- * | Algebra ].
apply eq_symmetric_unfolded;
 apply Integral_plus_Integral with (Min3_leEq_Max3 Zero y x).
apply included_imp_Continuous with (olor [--]One One).
exact ArcSin_def_lemma.
apply included3_interval; auto.
split.
astepr ( [--]ZeroR); apply inv_resp_less; apply pos_one.
apply pos_one.
apply x_minus_x; simpl in |- *; Algebra.
apply included_imp_Continuous with (olor [--]One One).
exact ArcSin_def_lemma.
apply included_interval; auto.
elim (ArcSin_range x Hx); intros; apply ArcSin_Sin; auto.
elim (ArcSin_range x Hx); intros; apply ArcSin_domain.
unfold y in |- *.
astepr ( [--] [--] (Sin (ArcSin x Hx))); astepr ( [--] (Sin [--] (ArcSin x Hx)));
 apply inv_resp_less.
apply Sin_less_One.
apply Cos_pos.
apply inv_resp_less; auto.
astepr ( [--] [--] (Pi [/]TwoNZ)); apply inv_resp_less; auto.
unfold y in |- *; apply Sin_less_One.
apply Cos_pos; auto.
Qed.

Lemma Sin_ArcSin_inv : Feq (olor [--]One One) (Sine[o]ArcSin) FId.
apply eq_imp_Feq.
apply included_FComp.
Included.
intros; apply sin_domain.
Included.
intros x H Hx Hx'.
elim Hx; intros x0 H0.
astepr x; astepl (Part _ _ (ProjT2 Hx)); astepl (Part _ _ H0).
apply eq_transitive_unfolded with (Sin (ArcSin x x0)).
simpl in |- *; Algebra.
apply eq_symmetric_unfolded; apply Sin_ArcSin.
Algebra.
Qed.

Lemma ArcSin_resp_leEq : forall x y,
 [--]One [<] x -> x [<=] y -> y [<] One -> forall Hx Hy, ArcSin x Hx [<=] ArcSin y Hy.
intros x y H H0 H1 Hx Hy.
assert (H2 : [--]One [<] OneR).
 apply less_transitive_unfolded with ZeroR;
  [ astepr ( [--]ZeroR); apply inv_resp_less | idtac ]; 
  apply pos_one.
apply
 Derivative_imp_resp_leEq
  with (olor [--]One One) H2 (( [-C-]One{-}FId{^}2) {!} [-C-] [--] (One [/]TwoNZ));
 Deriv.
intros; apply leEq_glb; intro z; intros.
elim Hy0; intros.
apply
 leEq_wdr
  with
    (Exp (( [-C-] [--] (One [/]TwoNZ) {*} (Logarithm[o] [-C-]One{-}FId{^}2)) z x0)).
apply less_leEq; apply Exp_pos.
simpl in |- *; Algebra.
Qed.

(** ***Cosine and Arcosine
*)

Lemma ArcCos_Cos : forall x, Zero [<] x -> x [<] Pi -> forall H, ArcCos (Cos x) H [=] x.
intros x H H0 H1.
assert (H2 : Dom ArcCos (Sin (Pi [/]TwoNZ[-]x))).
 apply dom_wd with (Cos x); Algebra.
astepl (Part _ _ H2).
unfold ArcCos in |- *.
astepl (Pi [/]TwoNZ[-]Part _ _ (ProjIR2 H2)).
rstepr (Pi [/]TwoNZ[-] (Pi [/]TwoNZ[-]x)).
apply cg_minus_wd.
Algebra.
apply ArcSin_Sin.
apply shift_less_minus; apply shift_plus_less'.
rstepr Pi; auto.
apply shift_minus_less; apply shift_less_plus'.
astepl ZeroR; auto.
Qed.

Lemma Cos_ArcCos : forall (x : IR) Hx, x [=] Cos (ArcCos x Hx).
intros.
unfold ArcCos in |- *.
astepr (Cos (Pi [/]TwoNZ[-]ArcSin x (ProjIR2 Hx))).
astepr (Sin (ArcSin x (ProjIR2 Hx))).
apply Sin_ArcSin.
Qed.

Lemma ArcCos_Cos_inv : Feq (olor Zero Pi) (ArcCos[o]Cosine) FId.
apply eq_imp_Feq.
apply included_FComp.
Included.
intros.
apply ArcCos_domain.
apply less_wdr with (Cos x).
2: simpl in |- *; Algebra.
apply inv_cancel_less.
astepr OneR.
eapply leEq_less_trans.
apply inv_leEq_AbsIR.
inversion_clear X; apply Abs_Cos_less_One; auto.
apply less_wdl with (Cos x).
2: simpl in |- *; Algebra.
eapply leEq_less_trans.
apply leEq_AbsIR.
inversion_clear X; apply Abs_Cos_less_One; auto.
Included.
intros.
astepl (Part _ _ (ProjT2 Hx)); astepr x.
cut (Dom ArcCos (Cos x)). intro H0.
apply eq_transitive_unfolded with (ArcCos (Cos x) H0).
apply pfwdef; simpl in |- *; Algebra.
inversion_clear X; apply ArcCos_Cos; auto.
inversion_clear Hx.
apply dom_wd with (Cosine x x0); auto.
simpl in |- *; Algebra.
Qed.

Lemma Cos_ArcCos_inv : Feq (olor [--]One One) (Cosine[o]ArcCos) FId.
apply eq_imp_Feq.
apply included_FComp.
unfold ArcCos in |- *; Included.
intros; apply cos_domain.
Included.
intros.
inversion_clear Hx.
astepr x; astepl (Part _ _ (ProjT2 Hx)); astepl (Part _ _ X0).
apply eq_transitive_unfolded with (Cos (ArcCos x x0)).
simpl in |- *; Algebra.
apply eq_symmetric_unfolded; apply Cos_ArcCos.
Qed.

Lemma ArcCos_resp_leEq : forall x y,
 [--]One [<] x -> x [<=] y -> y [<] One -> forall Hx Hy, ArcCos y Hy [<=] ArcCos x Hx.
intros.
Opaque ArcSin.
simpl in |- *; unfold cg_minus in |- *; apply plus_resp_leEq_lft.
apply inv_resp_leEq; apply ArcSin_resp_leEq; auto.
Qed.

(** ***Tangent and Arctangent
*)

Lemma maps_Tan : maps_compacts_into (olor [--] (Pi [/]TwoNZ) (Pi [/]TwoNZ)) realline Tang.
intros a b Hab H.
elim (H _ (compact_inc_lft _ _ Hab)); intros Ha1 Ha2.
elim (H _ (compact_inc_rht _ _ Hab)); intros Hb1 Hb2.
cut (Dom Tang b). cut (Dom Tang a). intros H0 H1.
set (min := Min (Tan a H0) Zero) in *.
set (max := Max (Tan b H1) One) in *.
cut (min [<] max). intro H2.
exists min; exists max; exists H2.
split.
Included.
intros x Hx H3.
fold (Tan x Hx) in |- *.
unfold min, max in |- *; inversion_clear H3.
split.
eapply leEq_transitive; [ apply Min_leEq_lft | apply Tan_resp_leEq; auto ].
apply leEq_less_trans with b; auto.
eapply leEq_transitive.
2: apply lft_leEq_Max.
apply Tan_resp_leEq; auto.
apply less_leEq_trans with a; auto.
unfold min, max in |- *.
eapply leEq_less_trans.
apply Min_leEq_rht.
eapply less_leEq_trans; [ apply pos_one | apply rht_leEq_Max ].
split.
apply sin_domain.
split.
apply cos_domain.
intros; apply ap_wdl with (Cos a).
apply Greater_imp_ap; apply Cos_pos; auto.
simpl in |- *; Algebra.
split.
apply sin_domain.
split.
apply cos_domain.
intros; apply ap_wdl with (Cos b).
apply Greater_imp_ap; apply Cos_pos; auto.
simpl in |- *; Algebra.
Qed.

Lemma ArcTan_Tan_inv : Feq (olor [--] (Pi [/]TwoNZ) (Pi [/]TwoNZ)) (ArcTang[o]Tang) FId.
set (HPi1 := pos_HalfPi) in *.
set (HPi2 := neg_invHalfPi) in *.
set (H := invHalfPi_less_HalfPi) in *.
apply Feq_criterium with H ( [-C-]One:PartIR) ZeroR.
set (H0 := Derivative_Tan_2 H) in *.
set (H2 := Derivative_ArcTan CI) in *.
Derivative_Help.
apply eq_imp_Feq.
apply included_FMult.
apply included_FComp.
Included.
intros.
split.
repeat split.
intros.
astepl (One[+]Tang x Hx[^]2).
apply pos_ap_zero.
astepl (ZeroR[+]Zero); apply plus_resp_less_leEq.
apply pos_one.
apply sqr_nonneg.
Included.
Included.
intros.
astepr OneR.
astepl (Part _ _ (ProjIR1 Hx) [*]Part _ _ (ProjIR2 Hx)).
elim Hx; intros H3 H4.
astepl (Part _ _ H3[*]Part _ _ H4).
astepl
 (Part _ _ (ProjT2 H3) [*] (Part _ _ (ProjIR1 H4) [+]Part _ _ (ProjIR2 H4))).
elim H3; intros x0 H5; elim H4; intros H6 H7.
astepl (Part _ _ H5[*] (Part _ _ H6[+]Part _ _ H7)).
astepl (Part _ _ H5[*] (One[+]Tang x H7[^]2)).
simpl in |- *; rational.
apply Derivative_comp with realline CI.
apply maps_Tan.
Deriv.
Deriv.
Deriv.
split; auto.
intros.
astepr ZeroR.
inversion_clear Hx.
Opaque Tang.
simpl in |- *.
apply Integral_empty.
Algebra.
Qed.

Transparent Tang.
Opaque ArcTang.

Lemma ArcTan_Tan : forall x, [--] (Pi [/]TwoNZ) [<] x -> x [<] Pi [/]TwoNZ -> forall H, ArcTan (Tan x H) [=] x.
intros.
unfold Tan, ArcTan in |- *.
astepr (FId x CI).
cut (Dom (ArcTang[o]Tang) x). intro H2.
apply eq_transitive_unfolded with ((ArcTang[o]Tang) x H2).
simpl in |- *; Algebra.
apply Feq_imp_eq with (olor [--] (Pi [/]TwoNZ) (Pi [/]TwoNZ)).
apply ArcTan_Tan_inv.
split; auto.
exists H; apply CI.
Qed.

Lemma Tan_ilim : forall x, {y : IR | olor [--] (Pi [/]TwoNZ) (Pi [/]TwoNZ) y | forall Hy, x [<=] Tan y Hy}.
intros.
set (aux_val := sqrt _ (less_leEq _ _ _ (pos_two IR)) [/]TwoNZ) in *.
assert (H : Zero [<] aux_val).
 unfold aux_val in |- *.
 apply shift_less_div; [ apply pos_two | apply power_cancel_less with 2 ].
 apply sqrt_nonneg.
 astepl (ZeroR[^]2); astepl ZeroR; astepr (Two:IR); apply pos_two.
assert (H0 : sqrt _ (less_leEq _ _ _ (pos_two _)) [#] Zero).
 apply mult_cancel_ap_zero_lft with (OneR [/]TwoNZ).
 eapply ap_wdl_unfolded;
  [ apply pos_ap_zero; apply H | unfold aux_val in |- *; rational ].
assert (H1 : aux_val [=] (One[/] _[//]H0)).
 unfold aux_val in |- *.
 apply eq_div; astepr (Two:IR);
  Step_final (sqrt _ (less_leEq _ _ _ (pos_two _)) [^]2).
assert (H2 : aux_val [<] One).
 apply power_cancel_less with 2.
 apply less_leEq; apply pos_one.
 unfold aux_val in |- *;
  rstepl ((sqrt _ (less_leEq _ _ _ (pos_two IR)) [^]2) [/]FourNZ); 
  astepr OneR.
 apply shift_div_less; [ apply pos_four | astepl (Two:IR); astepr (Four:IR) ];
  apply two_less_four.
elim (less_cotransitive_unfolded _ _ _ H2 x); intros.
2: exists (Pi [/]FourNZ); repeat split; PiSolve.
2: intro; astepr OneR; apply less_leEq; auto.
assert (H3 : Two[*]x [#] Zero).
 apply mult_resp_ap_zero.
 apply two_ap_zero.
 apply pos_ap_zero; apply less_transitive_unfolded with aux_val; auto.
assert (H4 : Dom ArcCos (One[/] _[//]H3)).
 repeat split.
 apply less_transitive_unfolded with ZeroR;
  [ astepr ( [--]ZeroR); apply inv_resp_less; apply pos_one
  | apply recip_resp_pos ].
 apply mult_resp_pos;
  [ apply pos_two | apply less_transitive_unfolded with aux_val; auto ].
 apply shift_div_less.
 apply mult_resp_pos;
  [ apply pos_two | apply less_transitive_unfolded with aux_val; auto ].
 astepr (Two[*]x); apply less_transitive_unfolded with (Two[*]aux_val).
 2: apply mult_resp_less_lft; auto; apply pos_two.
 unfold aux_val in |- *; rstepr (sqrt _ (less_leEq _ _ _ (pos_two _))).
 apply power_cancel_less with 2.
 apply sqrt_nonneg.
 astepl OneR; astepr (Two:IR); apply one_less_two.
assert (H5 : Pi [/]FourNZ [<=] ArcCos _ H4).
 assert (H5 : Dom ArcCos aux_val).
 repeat split; auto; unfold aux_val in |- *.
 apply less_transitive_unfolded with ZeroR; auto; astepr ( [--]ZeroR);
  apply inv_resp_less; apply pos_one.
 apply leEq_wdl with (ArcCos _ H5).
 2: assert (H6 : Dom ArcCos (Cos (Pi [/]FourNZ))).
 2: apply dom_wd with aux_val; auto.
 2: Step_final (One[/] _[//]H0).
 2: apply eq_transitive_unfolded with (ArcCos _ H6).
 3: apply ArcCos_Cos; PiSolve.
 2: apply pfwdef; unfold aux_val in |- *.
 2: Step_final (One[/] _[//]H0).
 apply ArcCos_resp_leEq.
 apply less_transitive_unfolded with ZeroR.
 astepr ( [--]ZeroR); apply inv_resp_less; apply pos_one.
 apply recip_resp_pos; apply mult_resp_pos; try apply pos_two;
  apply less_transitive_unfolded with aux_val; auto.
 apply shift_div_leEq.
 apply mult_resp_pos;
  [ apply pos_two | apply less_transitive_unfolded with aux_val; auto ].
 apply leEq_wdl with (aux_val[*] (Two[*]aux_val)).
 repeat apply mult_resp_leEq_lft; apply less_leEq; auto; apply pos_two.
 unfold aux_val in |- *.
 rstepl ((sqrt _ (less_leEq _ _ _ (pos_two _)) [^]2) [/]TwoNZ).
 Step_final ((Two:IR) [/]TwoNZ).
 auto.
exists (ArcCos _ H4).
Opaque iprop.
unfold ArcCos in |- *; simpl in |- *.
Transparent iprop.
elim H4; intros H6' H7; elim H7; intros.
apply iprop_wd with (Pi [/]TwoNZ[-]ArcSin _ H7).
2: Algebra.
elim (ArcSin_range _ H7); intros; split.
apply shift_less_minus; apply shift_plus_less'.
rstepr Pi; apply less_transitive_unfolded with (Pi [/]TwoNZ); PiSolve.
apply shift_minus_less; apply shift_less_plus'.
astepl ZeroR.
assert (H6 : Dom ArcSin (Sin Zero)).
 apply dom_wd with ZeroR; [ split | Algebra ];
  [ astepr ( [--]ZeroR); apply inv_resp_less | idtac ]; 
  apply pos_one.
apply less_wdl with (ArcSin _ H6).
2: apply ArcSin_Sin; PiSolve.
apply leEq_not_eq.
apply ArcSin_resp_leEq; auto.
astepr ZeroR; astepr ( [--]ZeroR); apply inv_resp_less; apply pos_one.
astepl ZeroR; apply less_leEq; apply recip_resp_pos.
apply mult_resp_pos;
 [ apply pos_two | apply less_transitive_unfolded with aux_val; auto ].
apply pfstrx with Sine CI CI.
apply ap_wdl_unfolded with ZeroR.
apply ap_wdr_unfolded with (One[/] _[//]H3).
apply ap_symmetric_unfolded; apply pos_ap_zero; apply recip_resp_pos.
apply mult_resp_pos;
 [ apply pos_two | apply less_transitive_unfolded with aux_val; auto ].
apply eq_transitive_unfolded with (Sin (ArcSin _ H7));
 [ apply Sin_ArcSin | simpl in |- *; Algebra ].
apply eq_transitive_unfolded with (Sin (ArcSin _ H6));
 [ astepl (Sin Zero); apply Sin_ArcSin | simpl in |- *; Algebra ].
intros; unfold Tan, Tang in |- *.
assert (H6 : Cos (ArcCos _ H4) [#] Zero).
 eapply ap_wdl_unfolded.
 2: apply Cos_ArcCos.
 apply recip_ap_zero; auto.
apply leEq_wdr with (Sin (ArcCos _ H4) [/] _[//]H6).
2: simpl in |- *; Algebra.
apply shift_leEq_div.
Opaque Cos.
unfold ArcCos in |- *; simpl in |- *.
astepr (Sin (ArcSin _ (ProjIR2 H4))).
eapply less_wdr.
2: apply Sin_ArcSin.
apply recip_resp_pos; apply mult_resp_pos;
 [ apply pos_two | apply less_transitive_unfolded with aux_val; auto ].
apply leEq_wdl with (x[*] (One[/] _[//]H3)).
2: apply mult_wdr; apply Cos_ArcCos.
rstepl (OneR [/]TwoNZ).
apply leEq_transitive with (One[/] _[//]H0).
apply recip_resp_leEq.
astepl (ZeroR[*]Two); apply shift_mult_less with (two_ap_zero IR); auto;
 apply pos_two.
apply power_cancel_leEq with 2; auto.
apply less_leEq; apply pos_two.
astepl (Two:IR); rstepr (Four:IR); apply less_leEq; apply two_less_four.
astepl (Sin (Pi [/]FourNZ)); apply Sin_resp_leEq.
PiSolve.
astepl (Pi [/]TwoNZ[-]ArcSin _ (ProjIR2 H4)).
apply shift_minus_leEq; apply shift_leEq_plus'; astepl ZeroR.
assert (H7 : Dom ArcSin (Sin Zero)).
 apply dom_wd with ZeroR; [ split | Algebra ];
  [ astepr ( [--]ZeroR); apply inv_resp_less | idtac ]; 
  apply pos_one.
apply leEq_wdl with (ArcSin _ H7).
2: apply ArcSin_Sin; PiSolve.
apply ArcSin_resp_leEq.
astepr ZeroR; astepr ( [--]ZeroR); apply inv_resp_less; apply pos_one.
astepl ZeroR; apply less_leEq; apply recip_resp_pos.
apply mult_resp_pos;
 [ apply pos_two | apply less_transitive_unfolded with aux_val; auto ].
apply shift_div_less.
apply mult_resp_pos;
 [ apply pos_two | apply less_transitive_unfolded with aux_val; auto ].
astepr (Two[*]x); apply less_transitive_unfolded with (Two[*]aux_val).
2: apply mult_resp_less_lft; auto; apply pos_two.
unfold aux_val in |- *; rstepr (sqrt _ (less_leEq _ _ _ (pos_two _))).
apply power_cancel_less with 2.
apply sqrt_nonneg.
astepl OneR; astepr (Two:IR); apply one_less_two.
auto.
Qed.

Opaque Min.
Transparent Cos.

Section ArcTan_Range.

Variable x : IR.

(* begin hide *)
Let min := proj1_sig2T _ _ _ (Tan_ilim x).
Let max := proj1_sig2T _ _ _ (Tan_ilim [--]x).

Let min1 : [--] (Pi [/]TwoNZ) [<] min.
elim (proj2a_sig2T _ _ _ (Tan_ilim x)); auto.
Qed.

Let min2 : min [<] Pi [/]TwoNZ.
elim (proj2a_sig2T _ _ _ (Tan_ilim x)); auto.
Qed.

Let min3 : Dom Tang min.
split.
apply sin_domain.
split.
apply cos_domain.
intro; apply ap_wdl_unfolded with (Cos min).
2: simpl in |- *; Algebra.
apply pos_ap_zero; apply Cos_pos.
apply min1.
apply min2.
Qed.

Let min4 : x [<=] Tan min min3 := proj2b_sig2T _ _ _ (Tan_ilim x) min3.

Let max1 : [--] (Pi [/]TwoNZ) [<] max.
elim (proj2a_sig2T _ _ _ (Tan_ilim [--]x)); auto.
Qed.

Let max2 : max [<] Pi [/]TwoNZ.
elim (proj2a_sig2T _ _ _ (Tan_ilim [--]x)); auto.
Qed.

Let max3 : Dom Tang max.
split.
apply sin_domain.
split.
apply cos_domain.
intro; apply ap_wdl_unfolded with (Cos max).
2: simpl in |- *; Algebra.
apply pos_ap_zero; apply Cos_pos.
apply max1.
apply max2.
Qed.

Let max4 : [--]x [<=] Tan max max3 := proj2b_sig2T _ _ _ (Tan_ilim [--]x) max3.

Let min5 : Dom Tang [--]min.
split.
apply sin_domain.
split.
apply cos_domain.
intro; apply ap_wdl_unfolded with (Cos [--]min).
2: simpl in |- *; Algebra.
astepl (Cos min).
apply pos_ap_zero; apply Cos_pos.
apply min1.
apply min2.
Qed.

Let min6 : Tan [--]min min5 [<=] [--]x.
astepl ( [--] (Tan _ min3)); apply inv_resp_leEq.
apply min4.
Qed.

Let max5 : Dom Tang [--]max.
split.
apply sin_domain.
split.
apply cos_domain.
intro; apply ap_wdl_unfolded with (Cos [--]max).
2: simpl in |- *; Algebra.
astepl (Cos max).
apply pos_ap_zero; apply Cos_pos.
apply max1.
apply max2.
Qed.

Let max6 : Tan [--]max max5 [<=] x.
astepl ( [--] (Tan _ max3)); astepr ( [--] [--]x); apply inv_resp_leEq.
apply max4.
Qed.

Let a :=
  ( [--] (Pi [/]TwoNZ) [+]
   Min [--] (Pi [/]FourNZ) (Min (Min min [--]min) (Min max [--]max))) [/]TwoNZ.

Let a1 : [--] (Pi [/]TwoNZ) [<] a.
unfold a in |- *; clear a.
apply shift_less_div.
apply pos_two.
apply shift_less_plus'; rstepl ( [--] (Pi [/]TwoNZ)).
repeat apply less_Min.
PiSolve.
apply min1.
apply inv_resp_less; apply min2.
apply max1.
apply inv_resp_less; apply max2.
Qed.

Let a2 : a [<] min.
unfold a in |- *.
apply shift_div_less.
apply pos_two.
apply shift_plus_less'.
eapply leEq_less_trans.
apply Min_leEq_rht.
eapply leEq_less_trans.
apply Min_leEq_lft.
eapply leEq_less_trans.
apply Min_leEq_lft.
apply shift_less_minus; apply shift_plus_less'.
rstepr min; apply min1.
Qed.

Let a3 : a [<] [--]min.
unfold a in |- *.
apply shift_div_less.
apply pos_two.
apply shift_plus_less'.
eapply leEq_less_trans.
apply Min_leEq_rht.
eapply leEq_less_trans.
apply Min_leEq_lft.
eapply leEq_less_trans.
apply Min_leEq_rht.
apply shift_less_minus; apply shift_plus_less'.
rstepr ( [--]min); apply inv_resp_less; apply min2.
Qed.

Let a4 : a [<] max.
unfold a in |- *.
apply shift_div_less.
apply pos_two.
apply shift_plus_less'.
eapply leEq_less_trans.
apply Min_leEq_rht.
eapply leEq_less_trans.
apply Min_leEq_rht.
eapply leEq_less_trans.
apply Min_leEq_lft.
apply shift_less_minus; apply shift_plus_less'.
rstepr max; apply max1.
Qed.

Let a5 : a [<] [--]max.
unfold a in |- *.
apply shift_div_less.
apply pos_two.
apply shift_plus_less'.
eapply leEq_less_trans.
apply Min_leEq_rht.
eapply leEq_less_trans.
apply Min_leEq_rht.
eapply leEq_less_trans.
apply Min_leEq_rht.
apply shift_less_minus; apply shift_plus_less'.
rstepr ( [--]max); apply inv_resp_less; apply max2.
Qed.

Let b :=
  (Pi [/]TwoNZ[+]Max (Pi [/]FourNZ) (Max (Max min [--]min) (Max max [--]max)))
  [/]TwoNZ.

Let b1 : b [<] Pi [/]TwoNZ.
unfold b in |- *.
apply shift_div_less.
apply pos_two.
apply shift_plus_less'; rstepr (Pi [/]TwoNZ).
repeat apply Max_less.
PiSolve.
apply min2.
astepr ( [--] [--] (Pi [/]TwoNZ)); apply inv_resp_less; apply min1.
apply max2.
astepr ( [--] [--] (Pi [/]TwoNZ)); apply inv_resp_less; apply max1.
Qed.

Let b2 : min [<] b.
unfold b in |- *.
apply shift_less_div.
apply pos_two.
apply shift_less_plus'.
eapply less_leEq_trans.
2: apply rht_leEq_Max.
eapply less_leEq_trans.
2: apply lft_leEq_Max.
eapply less_leEq_trans.
2: apply lft_leEq_Max.
apply shift_minus_less; apply shift_less_plus'.
rstepl min; apply min2.
Qed.

Let b3 : [--]min [<] b.
unfold b in |- *.
apply shift_less_div.
apply pos_two.
apply shift_less_plus'.
eapply less_leEq_trans.
2: apply rht_leEq_Max.
eapply less_leEq_trans.
2: apply lft_leEq_Max.
eapply less_leEq_trans.
2: apply rht_leEq_Max.
apply shift_minus_less; apply shift_less_plus'.
rstepl ( [--]min); astepr ( [--] [--] (Pi [/]TwoNZ)); apply inv_resp_less;
 apply min1.
Qed.

Let b4 : max [<] b.
unfold b in |- *.
apply shift_less_div.
apply pos_two.
apply shift_less_plus'.
eapply less_leEq_trans.
2: apply rht_leEq_Max.
eapply less_leEq_trans.
2: apply rht_leEq_Max.
eapply less_leEq_trans.
2: apply lft_leEq_Max.
apply shift_minus_less; apply shift_less_plus'.
rstepl max; apply max2.
Qed.

Let b5 : [--]max [<] b.
unfold b in |- *.
apply shift_less_div.
apply pos_two.
apply shift_less_plus'.
eapply less_leEq_trans.
2: apply rht_leEq_Max.
eapply less_leEq_trans.
2: apply rht_leEq_Max.
eapply less_leEq_trans.
2: apply rht_leEq_Max.
apply shift_minus_less; apply shift_less_plus'.
rstepl ( [--]max); astepr ( [--] [--] (Pi [/]TwoNZ)); apply inv_resp_less;
 apply max1.
Qed.

Let ab : a [<] b.
apply less_transitive_unfolded with min; [ apply a2 | apply b2 ].
Qed.

Lemma ArcTan_range_lemma :
  {y : IR | olor [--] (Pi [/]TwoNZ) (Pi [/]TwoNZ) y |
  forall Hy, Tang y Hy [=] x}.
assert (H : Continuous (olor [--] (Pi [/]TwoNZ) (Pi [/]TwoNZ)) Tang).
 eapply Derivative_imp_Continuous;
  apply (Derivative_Tan_1 invHalfPi_less_HalfPi).
assert (H0 : Continuous_I (less_leEq _ _ _ ab) Tang).
 eapply included_imp_Continuous; [ apply H | apply compact_included ].
 split;
  [ apply a1
  | apply less_transitive_unfolded with b; [ apply ab | apply b1 ] ].
 split;
  [ apply less_transitive_unfolded with a; [ apply a1 | apply ab ]
  | apply b1 ].
elim IVT'_I with (contF := H0) (z := x).
intros y H1 H2; exists y; auto.
inversion_clear H1; split.
apply less_transitive_unfolded with a; auto; apply a1.
apply less_transitive_unfolded with b; auto; apply b1.
apply ab.
intros x0 y H1 H2 H3 Hx Hy.
fold (Tan x0 Hx) in |- *; fold (Tan y Hy) in |- *.
inversion_clear H1; inversion_clear H2; apply Tan_resp_less; auto.
apply less_leEq_trans with a; auto; apply a1.
apply leEq_less_trans with b; auto; apply b1.
fold (Tan a (contin_imp_inc _ _ _ _ H0 _ (compact_inc_lft _ _ _))) in |- *.
apply less_leEq_trans with (Tan [--]max max5).
apply Tan_resp_less.
apply a1.
apply less_transitive_unfolded with b; [ apply b5 | apply b1 ].
apply a5.
apply max6.
fold (Tan b (contin_imp_inc _ _ _ _ H0 _ (compact_inc_rht _ _ _))) in |- *.
apply leEq_less_trans with (Tan min min3).
apply min4.
apply Tan_resp_less.
apply min1.
apply b1.
apply b2.
Qed.
(* end hide *)

Lemma ArcTan_range : [--] (Pi [/]TwoNZ) [<] ArcTan x and ArcTan x [<] Pi [/]TwoNZ.
intros.
Transparent ArcTang.
elim ArcTan_range_lemma; intros y H H0.
elim H; intros.
cut (Dom Tang y). intro H1.
assert (H2 : Tan y H1 [=] x). unfold Tan in |- *; Algebra.
split.
apply less_wdr with y; auto.
apply eq_symmetric_unfolded; eapply eq_transitive_unfolded.
2: apply ArcTan_Tan with (H := H1); auto.
unfold ArcTan in |- *; Algebra.
apply less_wdl with y; auto.
apply eq_symmetric_unfolded; eapply eq_transitive_unfolded.
2: apply ArcTan_Tan with (H := H1); auto.
unfold ArcTan in |- *; Algebra.
repeat split.
intro; apply Greater_imp_ap.
apply less_wdr with (Cos y); [ apply Cos_pos; auto | simpl in |- *; Algebra ].
Qed.

End ArcTan_Range.

Lemma Tan_ArcTan : forall (x : IR) Hx, x [=] Tan (ArcTan x) Hx.
intros.
set (y := Tan (ArcTan x) Hx) in *.
assert (H : ArcTan x [=] ArcTan y).
 unfold y in |- *; apply eq_symmetric_unfolded; elim ArcTan_range with x;
  intros; apply ArcTan_Tan; auto.
Transparent ArcTang.
cut (Continuous_I (Min_leEq_Max x y) {1/} ( [-C-]One{+}FId{^}2)). intro H0.
cut (Integral H0 [=] Zero). intro H1.
elim Hx; intros H2 H3.
apply Integral_eq_zero with (contF := H0) (x := x).
exact (CAnd_intro _ _ (Min_leEq_lft x y) (lft_leEq_Max x y)).
intros.
simpl in |- *; apply recip_resp_pos.
astepl (ZeroR[+]Zero); apply plus_resp_less_leEq.
apply pos_one.
astepr (x[^]2); apply sqr_nonneg.
intros x0 H4 Hx0; simpl in |- *.
apply less_leEq; apply recip_resp_pos.
astepl (ZeroR[+]Zero); apply plus_resp_less_leEq.
apply pos_one.
astepr (x0[^]2); apply sqr_nonneg.
auto.
apply eq_transitive_unfolded with (ArcTan y[-]ArcTan x).
rstepl (ArcTan x[+]Integral H0[-]ArcTan x).
apply cg_minus_wd; [ simpl in |- * | Algebra ].
apply eq_symmetric_unfolded; unfold ArcTan in |- *; simpl in |- *.
apply Integral_plus_Integral with (Min3_leEq_Max3 Zero y x).
apply included_imp_Continuous with realline.
exact ArcTan_def_lemma.
apply included3_interval; split.
apply x_minus_x; simpl in |- *; Algebra.
apply included_imp_Continuous with realline.
exact ArcTan_def_lemma.
apply included_interval; split.
Qed.

Lemma Tan_ArcTan_inv : Feq realline (Tang[o]ArcTang) FId.
apply eq_imp_Feq.
apply included_FComp.
Included.
intros; split.
auto.
split.
auto.
intros.
apply ap_wdl with (Cos (ArcTan x)).
Opaque ArcTang.
2: unfold ArcTan in |- *; simpl in |- *; Algebra.
elim ArcTan_range with x; intros.
apply pos_ap_zero; apply Cos_pos; auto.
Included.
intros; inversion_clear Hx.
astepr x; astepl (Part _ _ (ProjT2 Hx)); astepl (Part _ _ X0).
cut (Dom Tang (ArcTan x)); intros.
apply eq_transitive_unfolded with (Tan (ArcTan x) X1).
unfold Tan, ArcTan in |- *; Algebra.
apply eq_symmetric_unfolded; apply Tan_ArcTan.
apply dom_wd with (ArcTang x x0); auto.
unfold ArcTan in |- *; Algebra.
Qed.

End Inverses.
