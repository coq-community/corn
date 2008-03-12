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

(** printing Exp %\ensuremath{\exp}% *)
(** printing Sin %\ensuremath{\sin}% *)
(** printing Cos %\ensuremath{\cos}% *)
(** printing Log %\ensuremath{\log}% *)
(** printing Tan %\ensuremath{\tan}% *)

Require Export FTC.

(**
* More on Power Series

We will now formally define an operator that defines a function as the
sum of some series given a number sequence.  Along with it, we will
prove some important properties of these entities.
*)

Section Power_Series.

(**
** General results

%\begin{convention}% Let [J : interval] and [x0 : IR] be a point of [J].
Let [a : nat -> IR].
%\end{convention}%
*)

Variable J : interval.
Variable x0 : IR.
Hypothesis Hx0 : J x0.

Variable a : nat -> IR.

Definition FPowerSeries (n : nat) := a n{**} (FId{-} [-C-]x0) {^}n.

(**
The most important convergence criterium specifically for power series
is the Dirichlet criterium.
*)

(* begin show *)
Hypothesis Ha : {r : IR | {H : Zero [<] r | {N : nat | forall n, N <= n ->
  AbsIR (a (S n)) [<=] (One[/] r[//]pos_ap_zero _ _ H) [*]AbsIR (a n)}}}.

Let r := ProjT1 Ha.
Let Hr := ProjT1 (ProjT2 Ha).
(* end show *)

Lemma Dirichlet_crit : fun_series_abs_convergent_IR (olor (x0[-]r) (x0[+]r)) FPowerSeries.
fold r in (value of Hr).
red in |- *; intros.
red in |- *; intros.
apply fun_ratio_test_conv.
intro.
unfold FPowerSeries in |- *; Contin.
elim (ProjT2 (ProjT2 Ha)); intros N HN.
exists N.
cut
 {z : IR | Zero [<] z and z [<] r |
 forall x : IR, Compact Hab x -> AbsIR (x[-]x0) [<=] z}.
intro H.
elim H; intros z Hz.
elim Hz; clear Hz; intros H0z Hzr Hz.
clear H.
exists ((One[/] r[//]pos_ap_zero _ _ Hr) [*]z).
apply shift_mult_less with (pos_ap_zero _ _ H0z).
assumption.
apply recip_resp_less; assumption.
split.
apply less_leEq; apply mult_resp_pos.
apply recip_resp_pos; assumption.
assumption.
intros.
astepl (AbsIR (FPowerSeries (S n) x (ProjIR1 Hx'))).
apply leEq_wdl with (AbsIR (a (S n)) [*]AbsIR (x[-]x0) [*]AbsIR ((x[-]x0) [^]n)).
apply
 leEq_wdr
  with
    ((One[/] r[//]pos_ap_zero _ _ Hr) [*]z[*]AbsIR (a n) [*]
     AbsIR ((x[-]x0) [^]n)).
apply mult_resp_leEq_rht.
2: apply AbsIR_nonneg.
rstepr ((One[/] r[//]pos_ap_zero _ _ Hr) [*]AbsIR (a n) [*]z).
apply mult_resp_leEq_both; try apply AbsIR_nonneg.
apply HN; assumption.
apply Hz; auto.
rstepl
 ((One[/] r[//]pos_ap_zero _ _ Hr) [*]z[*](AbsIR (a n) [*]AbsIR ((x[-]x0) [^]n))).
apply mult_wdr.
astepr (AbsIR (FPowerSeries n x (ProjIR1 Hx))).
simpl in |- *; apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
simpl in |- *.
apply eq_symmetric_unfolded; eapply eq_transitive_unfolded.
apply AbsIR_resp_mult.
apply
 eq_transitive_unfolded
  with (AbsIR (a (S n)) [*](AbsIR ((x[-]x0) [^]n) [*]AbsIR (x[-]x0))).
apply mult_wdr; apply AbsIR_resp_mult.
simpl in |- *; rational.
clear HN.
cut
 ((forall x : IR, Compact Hab x -> a0 [<=] x) /\
  (forall x : IR, Compact Hab x -> x [<=] b)); intros.
inversion_clear H.
exists (Max (Max (b[-]x0) (x0[-]a0)) (r [/]TwoNZ)).
repeat split.
eapply less_leEq_trans.
2: apply rht_leEq_Max.
apply pos_div_two; auto.
repeat apply Max_less.
apply shift_minus_less'.
elim (Hinc _ (compact_inc_rht _ _ Hab)); auto.
apply shift_minus_less; apply shift_less_plus';
 elim (Hinc _ (compact_inc_lft _ _ Hab)); auto.
apply pos_div_two'; auto.
intros.
simpl in |- *; unfold ABSIR in |- *; apply Max_leEq.
apply leEq_transitive with (b[-]x0).
apply minus_resp_leEq; apply H1; auto.
eapply leEq_transitive.
2: apply lft_leEq_Max.
apply lft_leEq_Max.
apply leEq_transitive with (x0[-]a0).
rstepr ([--](a0[-]x0)); apply inv_resp_leEq.
apply minus_resp_leEq; apply H0; auto.
eapply leEq_transitive.
2: apply lft_leEq_Max.
apply rht_leEq_Max.
split; intros x H; elim H; auto.
Qed.

(**
When defining a function using its Taylor series as a motivation, the following operator can be of use.
*)

Definition FPowerSeries' n := (a n[/] _[//]nring_fac_ap_zero _ n) {**} (FId{-} [-C-]x0) {^}n.

(**
This function is also continuous and has a good convergence ratio.
*)

Lemma FPowerSeries'_cont : forall n, Continuous realline (FPowerSeries' n).
intros; unfold FPowerSeries' in |- *.
Contin.
Qed.

Lemma included_FPowerSeries' : forall n P, included P (Dom (FPowerSeries' n)).
repeat split.
Qed.

(* begin show *)
Hypothesis Ha' : {N : nat | {c : IR | Zero [<] c |
  forall n, N <= n -> AbsIR (a (S n)) [<=] c[*]AbsIR (a n)}}.
(* end show *)

Lemma FPowerSeries'_conv' : fun_series_abs_convergent_IR realline FPowerSeries'.
clear Hr r Ha.
red in |- *; intros.
red in |- *; intros.
apply fun_ratio_test_conv.
intro.
unfold FPowerSeries' in |- *; Contin.
elim Ha'; intros N HN.
elim HN; intros c H H0.
clear HN Ha'.
elim (Archimedes (Max (Max b x0[-]Min a0 x0) One[*]Two[*]c)); intros y Hy.
exists (max N y); exists (Half:IR); repeat split.
unfold Half in |- *.
apply pos_div_two'; apply pos_one.
apply less_leEq; apply pos_half.
intros x H1; intros.
astepl (AbsIR (FPowerSeries' (S n) x (ProjIR1 Hx'))).
astepr (Half[*]AbsIR (FPowerSeries' n x (ProjIR1 Hx))).
simpl in |- *.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
apply
 leEq_wdl
  with
    ((AbsIR (a (S n)) [/] _[//]nring_fac_ap_zero _ (S n)) [*]
     (AbsIR ((x[-]x0) [^]n) [*]AbsIR (x[-]x0))).
2: apply mult_wd.
2: apply
    eq_transitive_unfolded
     with
       (AbsIR (a (S n)) [/] _[//]
        AbsIR_resp_ap_zero _ (nring_fac_ap_zero _ (S n))).
3: apply eq_symmetric_unfolded; apply AbsIR_division.
2: apply div_wd; algebra.
2: apply eq_symmetric_unfolded; apply AbsIR_eq_x; apply nring_nonneg.
2: apply eq_symmetric_unfolded; eapply eq_transitive_unfolded.
2: apply AbsIR_resp_mult.
2: apply mult_wd; apply AbsIR_wd; simpl in |- *; algebra.
apply
 leEq_wdr
  with
    (One [/]TwoNZ[*](AbsIR (a n) [/] _[//]nring_fac_ap_zero _ n) [*]
     AbsIR ((x[-]x0) [^]n)).
2: apply eq_symmetric_unfolded; eapply eq_transitive_unfolded.
3: apply mult_assoc_unfolded.
2: apply mult_wdr.
2: eapply eq_transitive_unfolded.
2: apply AbsIR_resp_mult.
2: apply mult_wdl; simpl in |- *; algebra.
2: apply
    eq_transitive_unfolded
     with (AbsIR (a n) [/] _[//]AbsIR_resp_ap_zero _ (nring_fac_ap_zero _ n)).
2: apply AbsIR_division.
2: apply div_wd; algebra.
2: apply AbsIR_eq_x; apply nring_nonneg.
rstepl
 (AbsIR (a (S n)) [*]AbsIR (x[-]x0) [*]AbsIR ((x[-]x0) [^]n) [/] _[//]
  nring_fac_ap_zero _ (S n)).
apply shift_div_leEq.
apply pos_nring_fac.
rstepr
 (One [/]TwoNZ[*]
  (AbsIR (a n) [*]nring (fac (S n)) [/] _[//]nring_fac_ap_zero _ n) [*]
  AbsIR ((x[-]x0) [^]n)).
apply
 leEq_wdr
  with (One [/]TwoNZ[*](AbsIR (a n) [*]nring (S n)) [*]AbsIR ((x[-]x0) [^]n)).
2: apply mult_wdl; apply mult_wdr.
2: rstepr (AbsIR (a n) [*](nring (fac (S n)) [/] _[//]nring_fac_ap_zero _ n)).
2: apply mult_wdr.
2: astepr (nring (S n * fac n) [/] _[//]nring_fac_ap_zero IR n).
2: astepr (nring (S n) [*]nring (fac n) [/] _[//]nring_fac_ap_zero IR n);
    rational.
rstepr (One [/]TwoNZ[*]nring (S n) [*]AbsIR (a n) [*]AbsIR ((x[-]x0) [^]n)).
apply mult_resp_leEq_rht.
2: apply AbsIR_nonneg.
apply leEq_transitive with (AbsIR (a (S n)) [*]AbsIR (Max b x0[-]Min a0 x0)).
apply mult_resp_leEq_lft.
cut (Min a0 x0 [<=] Max b x0). intro H3.
apply compact_elements with H3.
inversion_clear H1; split.
apply leEq_transitive with a0; auto; apply Min_leEq_lft.
apply leEq_transitive with b; auto; apply lft_leEq_Max.
split.
apply Min_leEq_rht.
apply rht_leEq_Max.
apply leEq_transitive with x0.
apply Min_leEq_rht.
apply rht_leEq_Max.
apply AbsIR_nonneg.
apply leEq_transitive with (AbsIR (a (S n)) [*]Max (Max b x0[-]Min a0 x0) One).
apply mult_resp_leEq_lft.
2: apply AbsIR_nonneg.
eapply leEq_wdl.
apply lft_leEq_Max.
apply eq_symmetric_unfolded; apply AbsIR_eq_x.
apply shift_leEq_minus; astepl (Min a0 x0).
apply leEq_transitive with x0.
apply Min_leEq_rht.
apply rht_leEq_Max.
apply shift_mult_leEq with (max_one_ap_zero (Max b x0[-]Min a0 x0)).
apply pos_max_one.
apply leEq_transitive with (c[*]AbsIR (a n)).
apply H0.
apply le_trans with (max N y); auto; apply le_max_l.
apply shift_leEq_div.
apply pos_max_one.
rstepl (c[*]Max (Max b x0[-]Min a0 x0) One[*]AbsIR (a n)).
apply mult_resp_leEq_rht.
2: apply AbsIR_nonneg.
rstepr (nring (R:=IR) (S n) [/]TwoNZ); apply shift_leEq_div.
apply pos_two.
apply less_leEq; apply leEq_less_trans with (nring (R:=IR) y).
eapply leEq_wdl.
apply Hy.
rational.
apply nring_less.
red in |- *.
cut (y <= n); intros; auto with arith.
apply le_trans with (max N y); auto with arith.
Qed.

Lemma FPowerSeries'_conv : fun_series_convergent_IR realline FPowerSeries'.
apply abs_imp_conv_IR.
apply FPowerSeries'_cont.
apply FPowerSeries'_conv'.
Qed.

End Power_Series.

Hint Resolve FPowerSeries'_cont: continuous.

Section More_on_PowerSeries.

(**
%\begin{convention}% Let [F] and [G] be the power series defined
respectively by [a] and by [fun n => (a (S n))].
%\end{convention}%
*)

Variable x0 : IR.
Variable a : nat -> IR.

(* begin hide *)
Let F := FPowerSeries' x0 a.
Let G := FPowerSeries' x0 (fun n => a (S n)).
(* end hide *)

(* begin show *)
Hypothesis Hf : fun_series_convergent_IR realline F.
Hypothesis Hf' : fun_series_abs_convergent_IR realline F.
Hypothesis Hg : fun_series_convergent_IR realline G.
(* end show *)

(** We get a comparison test for power series. *)

Lemma FPowerSeries'_comp : forall b, (forall n, AbsIR (b n) [<=] a n) ->
 fun_series_convergent_IR realline (FPowerSeries' x0 b).
intros.
apply fun_comparison_IR with (fun n : nat => FAbs (FPowerSeries' x0 a n)).
Contin.
auto.
intros.
apply leEq_wdr with (AbsIR (FPowerSeries' x0 a n x (ProjIR1 Hx'))).
2: apply eq_symmetric_unfolded; apply FAbs_char.
simpl in |- *.
eapply leEq_wdr.
2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
apply mult_resp_leEq_rht.
2: apply AbsIR_nonneg.
eapply leEq_wdr.
2: apply eq_symmetric_unfolded;
    apply
     AbsIR_division
      with (y__ := AbsIR_resp_ap_zero _ (nring_fac_ap_zero IR n)).
eapply leEq_wdl.
2: apply eq_symmetric_unfolded;
    apply
     AbsIR_division
      with (y__ := AbsIR_resp_ap_zero _ (nring_fac_ap_zero IR n)).
apply div_resp_leEq.
eapply less_leEq_trans.
apply (pos_nring_fac IR n).
apply leEq_AbsIR.
apply leEq_transitive with (a n); [ auto | apply leEq_AbsIR ].
Qed.

(** And a rule for differentiation. *)

Lemma Derivative_FPowerSeries1' : forall H, Derivative realline H (FSeries_Sum Hf) (FSeries_Sum Hg).
intro.
eapply Derivative_wdr.
apply Feq_symmetric; apply (insert_series_sum _ _ Hg).
apply Derivative_FSeries.
intro; case n; clear n; intros.
simpl in |- *.
apply Derivative_wdl with (Fconst (S:=IR) (a 0)).
FEQ.
Deriv.
simpl in |- *.
Opaque nring fac.
unfold F, G, FPowerSeries' in |- *; simpl in |- *.
Derivative_Help.
apply eq_imp_Feq.
apply included_FScalMult; apply included_FScalMult.
apply included_FMult; Included.
apply included_FScalMult; Included.
intros; simpl in |- *.
set (y := nexp _ n (x[-]x0)) in *.
rstepl (a (S n) [*]y[*](nring (S n) [/] _[//]nring_fac_ap_zero _ (S n))).
rstepr
 (a (S n) [*]y[*]
  (nring (S n) [/] _[//]
   mult_resp_ap_zero _ _ _ (pos_ap_zero _ _ (pos_nring_S _ n))
     (nring_fac_ap_zero _ n))).
apply mult_wdr.
apply div_wd; algebra.
Step_final (nring (R:=IR) (S n * fac n)).
Qed.

End More_on_PowerSeries.

Section Definitions.

(**
** Function definitions through power series

We now define the exponential, sine and cosine functions as power
series, and prove their convergence.  Tangent is defined as the
quotient of sine over cosine.
*)

Definition Exp_ps := FPowerSeries' Zero (fun n : nat => One).

Definition sin_seq : nat -> IR.
intro n; elim (even_or_odd_plus n); intros k Hk; inversion_clear Hk.
apply ZeroR.
apply ([--]OneR[^]k).
Defined.

Definition sin_ps := FPowerSeries' Zero sin_seq.

Definition cos_seq : nat -> IR.
intro n; elim (even_or_odd_plus n); intros k Hk; inversion_clear Hk.
apply ([--]OneR[^]k).
apply ZeroR.
Defined.

Definition cos_ps := FPowerSeries' Zero cos_seq.

Lemma Exp_conv' : fun_series_abs_convergent_IR realline Exp_ps.
unfold Exp_ps in |- *.
apply FPowerSeries'_conv'.
exists 0; exists OneR.
apply pos_one.
intros; apply eq_imp_leEq; algebra.
Qed.

Lemma Exp_conv : fun_series_convergent_IR realline Exp_ps.
unfold Exp_ps in |- *.
apply FPowerSeries'_conv.
exists 0; exists OneR.
apply pos_one.
intros; apply eq_imp_leEq; algebra.
Qed.

Lemma sin_conv : fun_series_convergent_IR realline sin_ps.
unfold sin_ps in |- *; apply FPowerSeries'_comp with (fun n : nat => OneR).
apply Exp_conv'.
intros; unfold sin_seq in |- *.
elim even_or_odd_plus; intros k Hk; simpl in |- *.
elim Hk; simpl in |- *; intro.
eapply leEq_wdl;
 [ apply less_leEq; apply pos_one
 | apply eq_symmetric_unfolded; apply AbsIRz_isz ].
apply eq_imp_leEq.
elim (even_odd_dec k); intro.
apply eq_transitive_unfolded with (AbsIR One).
apply AbsIR_wd; astepl ([--]OneR[^]k); apply inv_one_even_nexp; auto.
apply AbsIR_eq_x; apply less_leEq; apply pos_one.
apply eq_transitive_unfolded with (AbsIR [--]One).
apply AbsIR_wd; astepl ([--]OneR[^]k); apply inv_one_odd_nexp; auto.
astepr ([--][--]OneR); apply AbsIR_eq_inv_x; apply less_leEq.
astepr ([--]ZeroR); apply inv_resp_less; apply pos_one.
Qed.

Lemma cos_conv : fun_series_convergent_IR realline cos_ps.
unfold cos_ps in |- *; apply FPowerSeries'_comp with (fun n : nat => OneR).
apply Exp_conv'.
intros; unfold cos_seq in |- *.
elim even_or_odd_plus; intros k Hk; simpl in |- *.
elim Hk; simpl in |- *; intro.
apply eq_imp_leEq.
elim (even_odd_dec k); intro.
apply eq_transitive_unfolded with (AbsIR One).
apply AbsIR_wd; astepl ([--]OneR[^]k); apply inv_one_even_nexp; auto.
apply AbsIR_eq_x; apply less_leEq; apply pos_one.
apply eq_transitive_unfolded with (AbsIR [--]One).
apply AbsIR_wd; astepl ([--]OneR[^]k); apply inv_one_odd_nexp; auto.
astepr ([--][--]OneR); apply AbsIR_eq_inv_x; apply less_leEq.
astepr ([--]ZeroR); apply inv_resp_less; apply pos_one.
eapply leEq_wdl;
 [ apply less_leEq; apply pos_one
 | apply eq_symmetric_unfolded; apply AbsIRz_isz ].
Qed.

Definition Expon := FSeries_Sum Exp_conv.

Definition Sine := FSeries_Sum sin_conv.

Definition Cosine := FSeries_Sum cos_conv.

Definition Tang := Sine{/}Cosine.

(**
Some auxiliary domain results.
*)

Lemma Exp_domain : forall x : IR, Dom Expon x.
intros; simpl in |- *; auto.
Qed.

Lemma sin_domain : forall x : IR, Dom Sine x.
intros; simpl in |- *; auto.
Qed.

Lemma cos_domain : forall x : IR, Dom Cosine x.
intros; simpl in |- *; auto.
Qed.

Lemma included_Exp : forall P, included P (Dom Expon).
intro; simpl in |- *; Included.
Qed.

Lemma included_Sin : forall P, included P (Dom Sine).
intro; simpl in |- *; Included.
Qed.

Lemma included_Cos : forall P, included P (Dom Cosine).
intro; simpl in |- *; Included.
Qed.

(**
Definition of the logarithm.
*)

Lemma log_defn_lemma : Continuous (openl Zero) {1/}FId.
apply Continuous_recip.
apply Continuous_id.
intros a b Hab H.
split.
Included.
assert (H0 : Zero [<] a). apply H; apply compact_inc_lft.
exists a.
auto.
intros y Hy H1; inversion_clear H1.
apply leEq_transitive with y.
auto.
apply leEq_AbsIR.
Qed.

Definition Logarithm := ( [-S-]log_defn_lemma) One (pos_one IR).

End Definitions.

Hint Resolve included_Exp included_Sin included_Cos: included.

(**
As most of these functions are total, it makes sense to treat them as setoid functions on the reals.  In the case of logarithm and tangent, this is not possible; however, we still define some abbreviations for aesthetical reasons.
*)

Definition Exp : CSetoid_un_op IR.
red in |- *.
apply Build_CSetoid_fun with (fun x : IR => Expon x CI).
intros x y H.
exact (pfstrx _ _ _ _ _ _ H).
Defined.

Definition Sin : CSetoid_un_op IR.
red in |- *.
apply Build_CSetoid_fun with (fun x : IR => Sine x CI).
intros x y H.
exact (pfstrx _ _ _ _ _ _ H).
Defined.

Definition Cos : CSetoid_un_op IR.
red in |- *.
apply Build_CSetoid_fun with (fun x : IR => Cosine x CI).
intros x y H.
exact (pfstrx _ _ _ _ _ _ H).
Defined.

Definition Log x (Hx : Zero [<] x) := Logarithm x Hx.

Definition Tan x Hx := Tang x Hx.
