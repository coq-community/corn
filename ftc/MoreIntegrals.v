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

Require Export Integral.
Require Export MoreFunctions.

Section Lemmas.

(** printing Integral %\ensuremath{\int}% #&int;# *)
(** printing integral' %\ensuremath{\int}% #&int;# *)

(**
* The generalized integral

In this file we extend the definition of integral to allow for
arbitrary integration domains (that is, not requiring that the lower
endpoint of integration be less or equal than the upper endpoint) and
we prove the fundamental properties of the new operator.

%\begin{convention}% Let [a, b : IR] and assume that [F] and [G] are two 
partial functions continuous in [[Min(a,b),Max(a,b)]].
%\end{convention}%

** Definitions

Before we define the new integral we need to some trivial interval inclusions.
*)

Variables a b : IR.
Hypothesis Hab : Min a b [<=] Max a b.

Lemma compact_inc_Min_lft : forall H, included (compact (Min a b) a H) (Compact Hab).
intros.
apply included_compact; split.
apply leEq_reflexive.
apply Min_leEq_Max.
apply Min_leEq_lft.
apply lft_leEq_Max.
Qed.

Lemma compact_inc_Min_rht : forall H, included (compact (Min a b) b H) (Compact Hab).
intros.
apply included_compact; split.
apply leEq_reflexive.
apply Min_leEq_Max.
apply Min_leEq_rht.
apply rht_leEq_Max.
Qed.

End Lemmas.

Section Definitions.

(**
The integral is defined by the formula
$\int_a^bf=\int_{\min(a,b)}^bf-\int_{\min(a,b)}^af$#&int;<sub>a</sub><sup>b</sup>f=&int;<sub>min(a,b)</sub><sup>b</sup>f-&int;<sub>min(a,b)</sub><sup>a</sup>f#,
inspired by the domain union rule; obviously it coincides with the
classical definition, and it collapses to the old one in the case [a
 [<=]  b].
*)

Variables a b : IR.
Hypothesis Hab : Min a b [<=] Max a b.
Variable F : PartIR.

Hypothesis HF : Continuous_I Hab F.

Lemma Integral_inc1 : Continuous_I (Min_leEq_lft a b) F.
eapply included_imp_contin with (Hab := Hab).
2: apply HF.
apply compact_inc_Min_lft.
Qed.

Lemma Integral_inc2 : Continuous_I (Min_leEq_rht a b) F.
eapply included_imp_contin with (Hab := Hab).
2: apply HF.
apply compact_inc_Min_rht.
Qed.

Definition Integral :=
  integral _ _ (Min_leEq_rht a b) F Integral_inc2[-]integral _ _ (Min_leEq_lft a b) _ Integral_inc1.

Lemma Integral_integral : forall Hab' HF', Integral [=] integral a b Hab' F HF'.
intros.
unfold Integral in |- *.
astepr (integral a b Hab' F HF'[-]Zero).
apply cg_minus_wd.
apply integral_wd'.
apply leEq_imp_Min_is_lft; assumption.
algebra.
apply integral_empty.
apply leEq_imp_Min_is_lft; assumption.
Qed.

End Definitions.

Implicit Arguments Integral [a b Hab F].

Section Properties_of_Integral.

(**
** Properties of the Integral

All our old properties carry over to this new definition---and some
new ones, too.  We begin with (strong) extensionality.
*)

Variables a b : IR.
Hypothesis Hab : Min a b [<=] Max a b.
Variables F G : PartIR.

Hypothesis contF : Continuous_I Hab F.
Hypothesis contG : Continuous_I Hab G.

Lemma Integral_strext : Integral contF [#] Integral contG ->
 {x : IR | Compact Hab x | forall Hx Hx', Part F x Hx [#] Part G x Hx'}.
intro H.
unfold Integral in H.
elim (cg_minus_strext _ _ _ _ _ H); intro.
elim (integral_strext _ _ _ _ _ _ _ a0); intros.
exists x.
apply compact_inc_Min_rht with (H := Min_leEq_rht a b); assumption.
assumption.
elim (integral_strext _ _ _ _ _ _ _ b0); intros.
exists x.
apply compact_inc_Min_lft with (H := Min_leEq_lft a b); assumption.
assumption.
Qed.

Lemma Integral_strext' : forall c d Hcd HF1 HF2,
 Integral (Hab:=Hab) (F:=F) HF1 [#] Integral (a:=c) (b:=d) (Hab:=Hcd) (F:=F) HF2 ->
 a [#] c or b [#] d.
intros c d Hcd HF1 HF2 H.
elim (cg_minus_strext _ _ _ _ _ H); clear H; intro H;
 elim (integral_strext' _ _ _ _ _ _ _ _ _ H); clear H; 
 intro H.
elim (Min_strext_unfolded _ _ _ _ H); auto.
auto.
elim (Min_strext_unfolded _ _ _ _ H); auto.
auto.
Qed.

Lemma Integral_wd : Feq (Compact Hab) F G -> Integral contF [=] Integral contG.
intros; unfold Integral in |- *.
apply cg_minus_wd; apply integral_wd.
apply included_Feq with (Compact Hab).
apply compact_inc_Min_rht.
assumption.
apply included_Feq with (Compact Hab).
apply compact_inc_Min_lft.
assumption.
Qed.

Lemma Integral_wd' : forall a' b' Ha'b' contF', a [=] a' -> b [=] b' ->
 Integral contF [=] Integral (a:=a') (b:=b') (Hab:=Ha'b') (F:=F) contF'.
intros.
unfold Integral in |- *.
apply cg_minus_wd; apply integral_wd'; try apply bin_op_wd_unfolded; algebra.
Qed.

(**
The integral is a linear operator.
*)

Lemma Integral_const : forall c (H : Continuous_I Hab [-C-]c), Integral H [=] c[*] (b[-]a).
intros.
unfold Integral in |- *.
rstepr (c[*] (b[-]Min a b) [-]c[*] (a[-]Min a b)).
apply cg_minus_wd; apply integral_const.
Qed.

Lemma Integral_comm_scal : forall c (H : Continuous_I Hab (c{**}F)), Integral H [=] c[*]Integral contF.
intros.
unfold Integral in |- *.
eapply eq_transitive_unfolded.
2: apply eq_symmetric_unfolded; apply dist_2a.
apply cg_minus_wd; apply integral_comm_scal.
Qed.

Lemma Integral_plus : forall H : Continuous_I Hab (F{+}G), Integral H [=] Integral contF[+]Integral contG.
intro.
unfold Integral in |- *.
cut (forall x y z w : IR, x[-]y[+] (z[-]w) [=] x[+]z[-] (y[+]w)); intros.
2: rational.
eapply eq_transitive_unfolded.
2: apply eq_symmetric_unfolded; apply H0.
apply cg_minus_wd; apply integral_plus.
Qed.

Lemma Integral_inv : forall H : Continuous_I Hab {--}F, Integral H [=] [--] (Integral contF).
intro.
unfold Integral in |- *.
cut (forall x y : IR, [--] (x[-]y) [=] [--]x[-][--]y); intros.
2: rational.
eapply eq_transitive_unfolded.
2: apply eq_symmetric_unfolded; apply H0.
apply cg_minus_wd; apply integral_inv.
Qed.

Lemma Integral_minus : forall H : Continuous_I Hab (F{-}G), Integral H [=] Integral contF[-]Integral contG.
intro.
unfold Integral in |- *.
cut (forall x y z w : IR, x[-]y[-] (z[-]w) [=] x[-]z[-] (y[-]w)); intros.
2: rational.
eapply eq_transitive_unfolded.
2: apply eq_symmetric_unfolded; apply H0.
apply cg_minus_wd; apply integral_minus.
Qed.

Lemma linear_Integral : forall alpha beta (H : Continuous_I Hab (alpha{**}F{+}beta{**}G)),
 Integral H [=] alpha[*]Integral contF[+]beta[*]Integral contG.
intros; unfold Integral in |- *.
cut
 (forall x y z r s t : IR,
  x[*] (y[-]z) [+]r[*] (s[-]t) [=] x[*]y[+]r[*]s[-] (x[*]z[+]r[*]t)).
2: intros; rational.
intro; eapply eq_transitive_unfolded.
2: apply eq_symmetric_unfolded; apply H0.
clear H0.
apply cg_minus_wd; apply linear_integral.
Qed.

(**
If the endpoints are equal then the integral vanishes.
*)

Lemma Integral_empty : a [=] b -> Integral contF [=] Zero.
intros.
unfold Integral in |- *.
astepr (ZeroR[-]Zero).
apply cg_minus_wd; apply integral_empty.
astepr a; apply leEq_imp_Min_is_lft; apply eq_imp_leEq; assumption.
apply leEq_imp_Min_is_lft; apply eq_imp_leEq; assumption.
Qed.

(**
And the norm provides an upper bound for the absolute value of the integral.
*)

Lemma Integral_leEq_norm : AbsIR (Integral contF) [<=] Norm_Funct contF[*]AbsIR (b[-]a).
unfold Integral in |- *.
eapply leEq_transitive.
apply triangle_IR_minus.
apply
 leEq_transitive
  with (Norm_Funct contF[*] (b[-]Min a b) [+]Norm_Funct contF[*] (a[-]Min a b)).
apply plus_resp_leEq_both;
 (eapply leEq_transitive;
   [ apply integral_leEq_norm | apply mult_resp_leEq_rht ]).
apply leEq_Norm_Funct; intros.
apply norm_bnd_AbsIR; apply compact_inc_Min_rht with (H := Min_leEq_rht a b);
 assumption.
apply shift_leEq_minus; astepl (Min a b); apply Min_leEq_rht.
apply leEq_Norm_Funct; intros.
apply norm_bnd_AbsIR; apply compact_inc_Min_lft with (H := Min_leEq_lft a b);
 assumption.
apply shift_leEq_minus; astepl (Min a b); apply Min_leEq_lft.
eapply leEq_wdl.
2: apply ring_dist_unfolded.
apply mult_resp_leEq_lft.
2: apply positive_norm.
rstepl (a[+]b[-]Two[*]Min a b).
apply shift_minus_leEq; apply shift_leEq_plus'.
apply shift_leEq_mult' with (two_ap_zero IR).
apply pos_two.
apply leEq_Min.
apply shift_div_leEq.
apply pos_two.
apply shift_minus_leEq; apply shift_leEq_plus'.
rstepl (b[-]a); apply leEq_AbsIR.
apply shift_div_leEq.
apply pos_two.
apply shift_minus_leEq; apply shift_leEq_plus'.
rstepl ( [--] (b[-]a)); apply inv_leEq_AbsIR.
Qed.

End Properties_of_Integral.

Section More_Properties.

(**
Two other ways of stating the addition law for domains.
*)

Lemma integral_plus_Integral : forall a b Hab F c Hac Hcb Hab' Hac' Hcb',
 integral c b Hcb F Hcb' [=] integral a b Hab F Hab'[-]integral a c Hac F Hac'.
intros.
rstepl
 (integral a c Hac F Hac'[+]integral c b Hcb F Hcb'[-]integral a c Hac F Hac').
apply cg_minus_wd.
apply integral_plus_integral.
algebra.
Qed.

Lemma integral_plus_integral' : forall a b Hab F c Hac Hcb Hab' Hac' Hcb',
 integral a c Hac F Hac' [=] integral a b Hab F Hab'[-]integral c b Hcb F Hcb'.
intros.
rstepl
 (integral a c Hac F Hac'[+]integral c b Hcb F Hcb'[-]integral c b Hcb F Hcb').
apply cg_minus_wd.
apply integral_plus_integral.
algebra.
Qed.

(**
And now we can prove the addition law for domains with our general operator.

%\begin{convention}% Assume [c : IR].
%\end{convention}%
*)

Variables a b c : IR.
(* begin show *)
Hypothesis Hab' : Min a b [<=] Max a b.
Hypothesis Hac' : Min a c [<=] Max a c.
Hypothesis Hcb' : Min c b [<=] Max c b.
Hypothesis Habc' : Min (Min a b) c [<=] Max (Max a b) c.
(* end show *)

Variable F : PartIR.

(* begin show *)
Hypothesis Hab : Continuous_I Hab' F.
Hypothesis Hac : Continuous_I Hac' F.
Hypothesis Hcb : Continuous_I Hcb' F.
Hypothesis Habc : Continuous_I Habc' F.
(* end show *)

(* begin hide *)
Let le_abc_ab : Min (Min a b) c [<=] Min a b.
apply Min_leEq_lft.
Qed.

Let le_abc_ac : Min (Min a b) c [<=] Min a c.
apply leEq_Min.
eapply leEq_transitive.
apply Min_leEq_lft.
apply Min_leEq_lft.
apply Min_leEq_rht.
Qed.

Let le_abc_cb : Min (Min a b) c [<=] Min c b.
apply leEq_Min.
apply Min_leEq_rht.
eapply leEq_transitive.
apply Min_leEq_lft.
apply Min_leEq_rht.
Qed.

Let le_abc_a : Min (Min a b) c [<=] a.
eapply leEq_transitive.
apply Min_leEq_lft.
apply Min_leEq_lft.
Qed.

Let le_abc_b : Min (Min a b) c [<=] b.
eapply leEq_transitive.
apply Min_leEq_lft.
apply Min_leEq_rht.
Qed.

Let le_abc_c : Min (Min a b) c [<=] c.
apply Min_leEq_rht.
Qed.

Let le_ab_a : Min a b [<=] a.
apply Min_leEq_lft.
Qed.

Let le_cb_c : Min c b [<=] c.
apply Min_leEq_lft.
Qed.

Let le_ac_a : Min a c [<=] a.
apply Min_leEq_lft.
Qed.

Let le_ab_b : Min a b [<=] b.
apply Min_leEq_rht.
Qed.

Let le_cb_b : Min c b [<=] b.
apply Min_leEq_rht.
Qed.

Let le_ac_c : Min a c [<=] c.
apply Min_leEq_rht.
Qed.

Let Habc_abc : Compact Habc' (Min (Min a b) c).
apply compact_inc_lft.
Qed.

Let Habc_ab : Continuous_I le_abc_ab F.
apply included_imp_contin with (Hab := Habc').
2: apply Habc.
apply included_compact; [ apply Habc_abc | split ].
apply Min_leEq_lft.
eapply leEq_transitive.
apply Min_leEq_Max.
apply lft_leEq_Max.
Qed.

Let Habc_ac : Continuous_I le_abc_ac F.
apply included_imp_contin with (Hab := Habc').
2: apply Habc.
apply included_compact; [ apply Habc_abc | split ].
apply le_abc_ac.
eapply leEq_transitive.
apply Min_leEq_Max.
apply Max_leEq.
eapply leEq_transitive.
2: apply lft_leEq_Max.
apply lft_leEq_Max.
apply rht_leEq_Max.
Qed.

Let Habc_cb : Continuous_I le_abc_cb F.
apply included_imp_contin with (Hab := Habc').
2: apply Habc.
apply included_compact; [ apply Habc_abc | split ].
apply le_abc_cb.
eapply leEq_transitive.
2: apply rht_leEq_Max.
apply Min_leEq_lft.
Qed.

Let Habc_a : Continuous_I le_abc_a F.
apply included_imp_contin with (Hab := Habc').
2: apply Habc.
apply included_compact; [ apply Habc_abc | split ].
apply le_abc_a.
eapply leEq_transitive.
2: apply lft_leEq_Max.
apply lft_leEq_Max.
Qed.

Let Habc_b : Continuous_I le_abc_b F.
apply included_imp_contin with (Hab := Habc').
2: apply Habc.
apply included_compact; [ apply Habc_abc | split ].
apply le_abc_b.
eapply leEq_transitive.
2: apply lft_leEq_Max.
apply rht_leEq_Max.
Qed.

Let Habc_c : Continuous_I le_abc_c F.
apply included_imp_contin with (Hab := Habc').
2: apply Habc.
apply included_compact; [ apply Habc_abc | split ].
apply le_abc_c.
apply rht_leEq_Max.
Qed.
(* end hide *)

Lemma Integral_plus_Integral : Integral Hab [=] Integral Hac[+]Integral Hcb.
unfold Integral in |- *.
apply
 eq_transitive_unfolded
  with
    (integral _ _ le_abc_b _ Habc_b[-]integral _ _ le_abc_ab _ Habc_ab[-]
     (integral _ _ le_abc_a _ Habc_a[-]integral _ _ le_abc_ab _ Habc_ab)).
apply cg_minus_wd; apply integral_plus_Integral.
rstepl (integral _ _ le_abc_b _ Habc_b[-]integral _ _ le_abc_a _ Habc_a).
rstepl
 (integral _ _ le_abc_c _ Habc_c[-]integral _ _ le_abc_ac _ Habc_ac[-]
  (integral _ _ le_abc_a _ Habc_a[-]integral _ _ le_abc_ac _ Habc_ac) [+]
  (integral _ _ le_abc_b _ Habc_b[-]integral _ _ le_abc_cb _ Habc_cb[-]
   (integral _ _ le_abc_c _ Habc_c[-]integral _ _ le_abc_cb _ Habc_cb))).
apply eq_symmetric_unfolded; apply bin_op_wd_unfolded; apply cg_minus_wd;
 apply integral_plus_Integral.
Qed.

(**
Notice that, unlike in the classical case, an extra hypothesis (the
continuity of [F] in the interval [[Min(a,b,c),Max(a,b,c)]]) must be assumed.
*)

End More_Properties.

Section Corollaries.

Variables a b : IR.
Hypothesis Hab : Min a b [<=] Max a b.
Variable F : PartIR.

Hypothesis contF : Continuous_I Hab F.

(** As a corollary, we get the following rule: *)

Lemma Integral_op : forall Hab' (contF' : Continuous_I (a:=Min b a) (b:=Max b a) Hab' F),
 Integral contF [=] [--] (Integral contF').
intros.
apply cg_inv_unique'.
cut (Continuous_I (Min_leEq_Max a a) F). intro H.
apply eq_transitive_unfolded with (Integral H).
cut (Min (Min a a) b [<=] Max (Max a a) b); intros.
apply eq_symmetric_unfolded; apply Integral_plus_Integral with H0.
cut (included (Compact H0) (Compact Hab)). intro H1.
exact (included_imp_contin _ _ _ _ _ _ _ H1 contF).
apply included_compact.
split.
apply leEq_Min.
apply leEq_transitive with a.
apply Min_leEq_lft.
apply eq_imp_leEq; apply eq_symmetric_unfolded; apply Min_id.
apply Min_leEq_rht.
apply leEq_transitive with b.
apply Min_leEq_rht.
apply rht_leEq_Max.
split.
apply leEq_transitive with b.
apply Min_leEq_rht.
apply rht_leEq_Max.
apply Max_leEq.
apply leEq_wdl with a.
apply lft_leEq_Max.
apply eq_symmetric_unfolded; apply Max_id.
apply rht_leEq_Max.
apply leEq_transitive with b.
apply Min_leEq_rht.
apply rht_leEq_Max.
apply Integral_empty; algebra.
apply included_imp_contin with (Hab := Hab).
2: apply contF.
intros x H.
apply compact_wd with a.
split.
apply Min_leEq_lft.
apply lft_leEq_Max.
inversion_clear H.
apply leEq_imp_eq.
eapply leEq_wdl.
apply H0.
apply Min_id.
eapply leEq_wdr.
apply H1.
apply Max_id.
Qed.

(** Finally, some miscellaneous results: *)

Lemma Integral_less_norm : a [#] b -> forall x, Compact Hab x -> forall Hx,
 AbsIR (F x Hx) [<] Norm_Funct contF -> AbsIR (Integral contF) [<] Norm_Funct contF[*]AbsIR (b[-]a).
intros H x H0 Hx H1.
set (N := Norm_Funct contF) in *.
elim (ap_imp_less _ _ _ H); intro.
apply less_wdr with (N[*] (b[-]a)).
eapply less_wdl.
eapply less_leEq_trans.
apply
 integral_less_norm
  with
    (contF := included_imp_contin _ _ _ _ _ _ _
                (compact_map2 a b (less_leEq _ _ _ a0) Hab) contF)
    (Hx := Hx); auto.
apply compact_map1 with (Hab' := Hab); auto.
eapply less_leEq_trans.
apply H1.
unfold N in |- *; apply included_imp_norm_leEq.
apply compact_map1.
apply mult_resp_leEq_rht.
unfold N in |- *; apply included_imp_norm_leEq.
apply compact_map2.
apply shift_leEq_minus; apply less_leEq.
astepl a; auto.
apply AbsIR_wd; apply eq_symmetric_unfolded.
apply Integral_integral.
apply mult_wdr.
apply eq_symmetric_unfolded; apply AbsIR_eq_x.
apply shift_leEq_minus; apply less_leEq.
astepl a; auto.

apply less_wdr with (N[*] (a[-]b)).
set (Hmin := Min_leEq_Max b a) in *.
cut (included (Compact Hmin) (Compact Hab)).
cut (included (Compact Hab) (Compact Hmin)). intros H2 H3.
cut (Continuous_I Hmin F). intro H4.
eapply less_wdl.
eapply less_leEq_trans.
apply
 integral_less_norm
  with
    (contF := included_imp_contin _ _ _ _ _ _ _
                (compact_map2 _ _ (less_leEq _ _ _ b0) Hmin) H4)
    (Hx := Hx); auto.
apply compact_map1 with (Hab' := Hmin); auto.
eapply less_leEq_trans.
apply H1.
unfold N in |- *; apply included_imp_norm_leEq.
eapply included_trans.
2: apply compact_map1 with (Hab' := Hmin).
apply H2.
apply mult_resp_leEq_rht.
unfold N in |- *; apply included_imp_norm_leEq.
eapply included_trans.
apply compact_map2 with (Hab' := Hmin).
apply H3.
apply shift_leEq_minus; apply less_leEq.
astepl b; auto.
eapply eq_transitive_unfolded.
apply AbsIR_inv.
apply AbsIR_wd; apply eq_symmetric_unfolded.
apply
 eq_transitive_unfolded
  with ( [--] (Integral (included_imp_contin _ _ _ _ _ _ _ H3 contF))).
apply Integral_op.
apply un_op_wd_unfolded.
apply Integral_integral.
apply included_imp_contin with (Hab := Hab); auto.
red in |- *; intros.
apply compact_wd' with (Hab := Hab).
apply Min_comm.
apply Max_comm.
auto.
red in |- *; intros.
apply compact_wd' with (Hab := Hmin).
apply Min_comm.
apply Max_comm.
auto.
apply mult_wdr.
eapply eq_transitive_unfolded.
apply eq_symmetric_unfolded; apply AbsIR_eq_x.
apply shift_leEq_minus; apply less_leEq.
astepl b; auto.
apply AbsIR_minus.
Qed.

Lemma ub_Integral : a [#] b -> forall c, (forall x, Compact Hab x -> forall Hx, AbsIR (F x Hx) [<=] c) ->
 forall x, Compact Hab x -> forall Hx, AbsIR (F x Hx) [<] c -> AbsIR (Integral contF) [<] c[*]AbsIR (b[-]a).
intros H c H0 x H1 Hx H2.
set (N := Norm_Funct contF) in *.
cut (N [<=] c); intros.
elim (less_cotransitive_unfolded _ _ _ H2 N); intros.
apply less_leEq_trans with (N[*]AbsIR (b[-]a)).
unfold N in |- *; apply Integral_less_norm with x Hx; auto.
apply mult_resp_leEq_rht; auto.
apply AbsIR_nonneg.
apply leEq_less_trans with (N[*]AbsIR (b[-]a)).
unfold N in |- *; apply Integral_leEq_norm.
apply mult_resp_less; auto.
apply AbsIR_pos.
apply minus_ap_zero.
apply ap_symmetric_unfolded; auto.
unfold N in |- *; apply leEq_Norm_Funct; auto.
Qed.

End Corollaries.

Lemma Integral_ap_zero : forall a b Hab (F : PartIR) contF, a [#] b -> forall x,
 Compact Hab x -> forall Hx, Zero [<] F x Hx -> (forall x, Compact Hab x -> forall Hx, Zero [<=] F x Hx) ->
 Zero [<] AbsIR (Integral (a:=a) (b:=b) (Hab:=Hab) (F:=F) contF).
intros a b Hab F contF H x H0 Hx H1 H2.
elim (ap_imp_less _ _ _ H); intro.
eapply less_leEq_trans.
2: apply leEq_AbsIR.
eapply less_wdr.
2: apply eq_symmetric_unfolded.
2: apply
    Integral_integral
     with
       (HF' := included_imp_contin _ _ _ _ _ _ _
                 (compact_map2 a b (less_leEq _ _ _ a0) Hab) contF).
eapply integral_gt_zero with x Hx; auto.
exact (compact_map1 _ _ (less_leEq _ _ _ a0) Hab x H0).
intros x0 H3 Hx0; apply H2.
exact (compact_map2 _ _ (less_leEq _ _ _ a0) Hab _ H3).

cut (included (Compact (Min_leEq_Max b a)) (Compact Hab)).
2: apply included_compact; split.
2: apply eq_imp_leEq; apply Min_comm.
2: apply leEq_transitive with a; [ apply Min_leEq_rht | apply lft_leEq_Max ].
2: apply leEq_transitive with b; [ apply Min_leEq_rht | apply lft_leEq_Max ].
2: apply eq_imp_leEq; apply Max_comm.
cut (included (Compact Hab) (Compact (Min_leEq_Max b a))).
2: apply included_compact; split.
2: apply eq_imp_leEq; apply Min_comm.
2: apply leEq_transitive with b; [ apply Min_leEq_rht | apply lft_leEq_Max ].
2: apply leEq_transitive with a; [ apply Min_leEq_rht | apply lft_leEq_Max ].
2: apply eq_imp_leEq; apply Max_comm.
intros H3 H4.
eapply less_leEq_trans.
2: apply inv_leEq_AbsIR.
eapply less_wdr.
2: apply
    Integral_op with (contF := included_imp_contin _ _ _ _ _ _ _ H4 contF).
eapply less_wdr.
2: apply eq_symmetric_unfolded.
2: apply
    Integral_integral
     with
       (HF' := included_imp_contin _ _ _ _ _ _ _
                 (compact_map2 _ _ (less_leEq _ _ _ b0) (Min_leEq_Max b a))
                 (included_imp_contin _ _ _ _ _ _ _ H4 contF)).
eapply integral_gt_zero with x Hx; auto.
exact (compact_map1 _ _ (less_leEq _ _ _ b0) (Min_leEq_Max b a) x (H3 x H0)).
intros x0 H5 Hx0; apply H2.
exact (H4 _ (compact_map2 _ _ (less_leEq _ _ _ b0) (Min_leEq_Max _ _) _ H5)).
Qed.

Lemma Integral_eq_zero : forall a b Hab (F : PartIR) contF x, Compact Hab x ->
 (forall Hx, Zero [<] F x Hx) -> (forall x, Compact Hab x -> forall Hx, Zero [<=] F x Hx) ->
 Integral (a:=a) (b:=b) (Hab:=Hab) (F:=F) contF [=] Zero -> a [=] b.
intros a b Hab F contF x H X H0 H1.
apply not_ap_imp_eq; intro.
apply less_irreflexive_unfolded with (x := ZeroR).
apply less_wdr with (AbsIR (Integral contF)).
2: Step_final (AbsIR Zero).
apply Integral_ap_zero with x (contin_imp_inc _ _ _ _ contF x H); auto.
Qed.
