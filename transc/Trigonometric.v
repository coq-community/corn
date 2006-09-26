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

Require Export TaylorSeries.

(** *The Trigonometric Functions

In this section, we explore the properties of the trigonometric functions which we previously defined.
*)

Section Lemmas.

(** First, we need a lemma on mappings. *)

Lemma maps_translation : forall y, maps_compacts_into realline realline (FId{+} [-C-]y).
intros y a b Hab H.
exists (a[+]y); exists (b[+]y[+]One).
cut (a[+]y [<] b[+]y[+]One). intro H0.
exists H0.
split.
split.
intros x Hx H1; simpl in |- *; inversion_clear H1; split.
apply plus_resp_leEq; auto.
apply less_leEq; apply leEq_less_trans with (b[+]y).
apply plus_resp_leEq; auto.
apply less_plusOne.
apply leEq_less_trans with (b[+]y).
apply plus_resp_leEq; auto.
apply less_plusOne.
Qed.

End Lemmas.

Section Sine_and_Cosine.

(** Sine, cosine and tangent at [Zero]. *)

Lemma Sin_zero : Sin Zero [=] Zero.
simpl in |- *.
eapply eq_transitive_unfolded.
2: apply (series_sum_zero conv_zero_series).
apply series_sum_wd; intros; simpl in |- *.
case n.
unfold sin_seq in |- *; simpl in |- *.
elim even_or_odd_plus; intros; simpl in |- *.
elim p; intros; simpl in |- *.
rational.
elimtype False; inversion b.
clear n; intro; simpl in |- *.
rational.
Qed.

Lemma Cos_zero : Cos Zero [=] One.
simpl in |- *.
unfold series_sum in |- *.
apply eq_symmetric_unfolded; apply Limits_unique.
intros eps H.
exists 1; intros.
apply AbsSmall_wdr_unfolded with ZeroR.
apply zero_AbsSmall; apply less_leEq; auto.
simpl in |- *.
unfold seq_part_sum in |- *.
induction  m as [| m Hrecm].
elimtype False; inversion H0.
clear Hrecm; induction  m as [| m Hrecm].
simpl in |- *.
unfold cos_seq in |- *.
elim even_or_odd_plus; intros; simpl in |- *.
elim p; intros; simpl in |- *.
cut (x = 0); [ intro | omega ].
rewrite H1; simpl in |- *; rational.
elimtype False; inversion b.
set (n := S m) in *.
cut (1 <= n); [ intro | unfold n in |- *; auto with arith ].
cut (n = S m); [ intro | auto ].
clearbody n.
simpl in |- *.
set
 (h :=
  fun i : nat =>
  (cos_seq i[/] _[//]nring_fac_ap_zero _ i) [*]nexp IR i (Zero[-]Zero)) 
 in *.
fold (h n) in |- *.
rstepr (h n[+] (Sum0 n h[-]One)).
astepl (ZeroR[+]Zero).
apply bin_op_wd_unfolded.
2: auto.
unfold h, cos_seq in |- *.
elim even_or_odd_plus; intros; simpl in |- *.
elim p; intros; simpl in |- *.
2: rational.
apply eq_symmetric_unfolded; apply x_mult_zero.
rewrite H2; simpl in |- *; rational.
Qed.

Hint Resolve Sin_zero Cos_zero: algebra.

Opaque Sine Cosine.

Lemma Tan_zero : forall H, Tan Zero H [=] Zero.
intros; unfold Tan, Tang in |- *.
simpl in |- *.
astepr (ZeroR [/]OneNZ); apply div_wd.
astepr (Sin Zero); simpl in |- *; algebra.
astepr (Cos Zero); simpl in |- *; algebra.
Qed.

Transparent Sine Cosine.

(**
Continuity of sine and cosine are trivial.
*)

Lemma Continuous_Sin : Continuous realline Sine.
unfold Sine in |- *; Contin.
Qed.

Lemma Continuous_Cos : Continuous realline Cosine.
unfold Cosine in |- *; Contin.
Qed.

(**
The rules for the derivative of the sine and cosine function; we begin by proving that their defining sequences can be expressed in terms of one another.
*)

Lemma cos_sin_seq : forall n : nat, cos_seq n [=] sin_seq (S n).
intro.
apply eq_symmetric_unfolded.
unfold sin_seq, cos_seq in |- *.
elim even_or_odd_plus; intros; simpl in |- *.
elim p; intros; simpl in |- *.
elim even_or_odd_plus; intros; simpl in |- *.
elim p0; intros; simpl in |- *.
elimtype False; omega.
algebra.
elim even_or_odd_plus; intros; simpl in |- *.
elim p0; intros; simpl in |- *.
cut (x0 = x); [ intro | omega ].
rewrite H; algebra.
elimtype False; omega.
Qed.

Lemma sin_cos_seq : forall n : nat, sin_seq n [=] [--] (cos_seq (S n)).
intros.
unfold sin_seq, cos_seq in |- *.
elim even_or_odd_plus; intros; simpl in |- *.
elim p; intros; simpl in |- *.
elim even_or_odd_plus; intros; simpl in |- *.
elim p0; intros; simpl in |- *.
elimtype False; omega.
algebra.
elim even_or_odd_plus; intros; simpl in |- *.
elim p0; intros; simpl in |- *.
cut (S x = x0); [ intro | omega ].
rewrite <- H; simpl in |- *; rational.
elimtype False; omega.
Qed.

Lemma Derivative_Sin : forall H, Derivative realline H Sine Cosine.
intro.
unfold Sine, Cosine, sin_ps, cos_ps in |- *.
cut
 (fun_series_convergent_IR realline
    (FPowerSeries' Zero (fun n : nat => sin_seq (S n)))). intro H0.
eapply Derivative_wdr.
2: apply Derivative_FPowerSeries1' with (Hg := H0).
FEQ.
simpl in |- *.
apply series_sum_wd; intros.
apply mult_wdl.
apply div_wd.
apply eq_symmetric_unfolded; apply cos_sin_seq.
algebra.
apply fun_series_convergent_wd_IR with (FPowerSeries' Zero cos_seq).
intros; FEQ.
repeat split.
repeat split.
simpl in |- *.
apply mult_wdl.
apply div_wd.
apply cos_sin_seq.
algebra.
apply cos_conv.
Qed.

Lemma Derivative_Cos : forall H, Derivative realline H Cosine {--}Sine.
intro.
unfold Sine, Cosine, sin_ps, cos_ps in |- *.
cut
 (fun_series_convergent_IR realline
    (FPowerSeries' Zero (fun n : nat => cos_seq (S n)))). intro H0.
eapply Derivative_wdr.
2: apply Derivative_FPowerSeries1' with (Hg := H0).
FEQ.
simpl in |- *.
apply
 eq_transitive_unfolded
  with
    (series_sum _
       (conv_series_inv _
          (fun_series_conv_imp_conv _ _ (leEq_reflexive _ x) _
             (sin_conv _ _ (leEq_reflexive _ x)
                (compact_single_iprop realline x Hx')) x
             (compact_single_prop x)
             (fun_series_inc_IR realline _ sin_conv x Hx')))).
apply series_sum_wd; intros.
simpl in |- *.
rstepr
 (( [--] (sin_seq n) [/] _[//]nring_fac_ap_zero _ n) [*]nexp IR n (x[-]Zero)).
apply mult_wdl.
apply div_wd.
apply eq_symmetric_unfolded.
astepr ( [--][--] (cos_seq (S n))); apply un_op_wd_unfolded.
apply sin_cos_seq.
algebra.
simpl in |- *.
apply
 series_sum_inv
  with
    (x := fun n : nat =>
          (sin_seq n[/] _[//]nring_fac_ap_zero IR n) [*]nexp IR n (x[-]Zero)).
apply
 fun_series_convergent_wd_IR
  with (fun n : nat => {--} (FPowerSeries' Zero sin_seq n)).
intros; FEQ.
repeat split.
repeat split.
simpl in |- *.
rstepl
 (( [--] (sin_seq n) [/] _[//]nring_fac_ap_zero _ n) [*]nexp IR n (x[-]Zero)).
apply mult_wdl.
apply div_wd.
astepr ( [--][--] (cos_seq (S n))); apply un_op_wd_unfolded.
apply sin_cos_seq.
algebra.
apply FSeries_Sum_inv_conv.
apply sin_conv.
Qed.

Hint Resolve Derivative_Sin Derivative_Cos: derivate.
Hint Resolve Continuous_Sin Continuous_Cos: continuous.

Section Sine_of_Sum.

(**
We now prove the rule for the sine and cosine of the sum.  These rules
have to be proved first as functional equalities, which is why we also
state the results in a function form (which we won't do in other
situations).

%\begin{convention}% Let:
 - [F := fun y => Sine[o] (FId{+} [-C-]y)];
 - [G := fun y => (Sine{*} [-C-] (Cos y)) {+} (Cosine{*} [-C-] (Sin y))].

%\end{convention}%
*)

(* begin hide *)
Let F (y : IR) := Sine[o]FId{+} [-C-]y.
Let G (y : IR) := Sine{*} [-C-] (Cos y) {+}Cosine{*} [-C-] (Sin y).
Let F' (y : IR) :=
  (fix funct (n : nat) : PartIR :=
     match n with
     | O => Sine[o]FId{+} [-C-]y
     | S O => Cosine[o]FId{+} [-C-]y
     | S (S O) => {--} (Sine[o]FId{+} [-C-]y)
     | S (S (S O)) => {--} (Cosine[o]FId{+} [-C-]y)
     | S (S (S (S p))) => funct p
     end).
Let G' (y : IR) :=
  (fix funct (n : nat) : PartIR :=
     match n with
     | O => Sine{*} [-C-] (Cos y) {+}Cosine{*} [-C-] (Sin y)
     | S O => Cosine{*} [-C-] (Cos y) {-}Sine{*} [-C-] (Sin y)
     | S (S O) => {--} (Sine{*} [-C-] (Cos y) {+}Cosine{*} [-C-] (Sin y))
     | S (S (S O)) => Sine{*} [-C-] (Sin y) {-}Cosine{*} [-C-] (Cos y)
     | S (S (S (S p))) => funct p
     end).
(* end hide *)
Opaque Sine Cosine.

Lemma Sin_plus_Taylor_bnd_lft : forall y : IR, Taylor_bnd (F' y).
clear F G G'; intros.
apply
 bnd_imp_Taylor_bnd
  with (FAbs (Sine[o]FId{+} [-C-]y) {+}FAbs (Cosine[o]FId{+} [-C-]y)).
intro;
 apply
  four_ind
   with
     (P := fun n : nat =>
           forall (x : IR) Hx Hx',
           AbsIR (F' y n x Hx) [<=] 
           AbsIR
             ((FAbs (Sine[o]FId{+} [-C-]y) {+}FAbs (Cosine[o]FId{+} [-C-]y)) x
                Hx')).

intros.
unfold F' in |- *.
Opaque FAbs.
simpl in |- *.
eapply leEq_transitive.
2: apply leEq_AbsIR.
astepl (AbsIR (Sine (x[+]y) (ProjT2 Hx)) [+]Zero).
apply plus_resp_leEq_both.
apply eq_imp_leEq; apply eq_symmetric_unfolded.
Transparent FAbs.
apply eq_transitive_unfolded with (AbsIR (Part _ _ (ProjIR1 (ProjIR1 Hx')))).
apply FAbs_char.
apply AbsIR_wd; simpl in |- *; rational.
apply FAbs_nonneg.

intros.
unfold F' in |- *.
Opaque FAbs.
simpl in |- *.
eapply leEq_transitive.
2: apply leEq_AbsIR.
astepl (Zero[+]AbsIR (Cosine (x[+]y) (ProjT2 Hx))).
apply plus_resp_leEq_both.
apply FAbs_nonneg.
apply eq_imp_leEq; apply eq_symmetric_unfolded.
Transparent FAbs.
apply eq_transitive_unfolded with (AbsIR (Part _ _ (ProjIR1 (ProjIR2 Hx')))).
apply FAbs_char.
apply AbsIR_wd; simpl in |- *; rational.

intros.
unfold F' in |- *.
Opaque FAbs.
simpl in |- *.
eapply leEq_transitive.
2: apply leEq_AbsIR.
astepl (AbsIR [--] (Sine (x[+]y) (ProjT2 Hx)) [+]Zero).
apply leEq_wdl with (AbsIR (Sine (x[+]y) (ProjT2 Hx)) [+]Zero).
apply plus_resp_leEq_both.
apply eq_imp_leEq; apply eq_symmetric_unfolded.
Transparent FAbs.
apply eq_transitive_unfolded with (AbsIR (Part _ _ (ProjIR1 (ProjIR1 Hx')))).
apply FAbs_char.
apply AbsIR_wd; simpl in |- *; rational.
apply FAbs_nonneg.
apply bin_op_wd_unfolded.
apply AbsIR_inv.
algebra.

intros.
unfold F' in |- *.
Opaque FAbs.
simpl in |- *.
eapply leEq_transitive.
2: apply leEq_AbsIR.
astepl (Zero[+]AbsIR [--] (Cosine (x[+]y) (ProjT2 Hx))).
apply leEq_wdl with (Zero[+]AbsIR (Cosine (x[+]y) (ProjT2 Hx))).
apply plus_resp_leEq_both.
apply FAbs_nonneg.
apply eq_imp_leEq; apply eq_symmetric_unfolded.
Transparent FAbs.
apply eq_transitive_unfolded with (AbsIR (Part _ _ (ProjIR1 (ProjIR2 Hx')))).
apply FAbs_char.
apply AbsIR_wd; simpl in |- *; rational.
apply bin_op_wd_unfolded.
algebra.
apply AbsIR_inv.

auto.

cut (maps_compacts_into realline realline (Fid IR{+} [-C-]y)); intros.
apply Continuous_plus; apply Continuous_abs;
 apply Continuous_comp with realline; Contin.
intros a b Hab H.
exists (a[+]y); exists (b[+]y[+]One).
cut (a[+]y [<] b[+]y[+]One). intro H0.
exists H0.
split.
Included.
intros x Hx H1; inversion_clear H1.
split.
simpl in |- *; apply plus_resp_leEq; auto.
simpl in |- *; apply leEq_transitive with (b[+]y).
apply plus_resp_leEq; auto.
apply less_leEq; apply less_plusOne.
apply leEq_less_trans with (b[+]y).
apply plus_resp_leEq; auto.
apply less_plusOne.
apply
 four_induction
  with (P := fun n : nat => included (fun _ : IR => CTrue) (Dom (F' y n)));
 auto; unfold F' in |- *; Included.
Qed.

Lemma Sin_plus_Taylor_bnd_rht : forall y : IR, Taylor_bnd (G' y).
clear F G F'; intros.
apply
 bnd_imp_Taylor_bnd
  with
    (FAbs (Sine{*} [-C-] (Cos y) {+}Cosine{*} [-C-] (Sin y)) {+}
     FAbs (Cosine{*} [-C-] (Cos y) {-}Sine{*} [-C-] (Sin y))).
intro;
 apply
  four_ind
   with
     (P := fun n : nat =>
           forall (x : IR) Hx Hx',
           AbsIR (G' y n x Hx) [<=] 
           AbsIR
             ((FAbs (Sine{*} [-C-] (Cos y) {+}Cosine{*} [-C-] (Sin y)) {+}
               FAbs (Cosine{*} [-C-] (Cos y) {-}Sine{*} [-C-] (Sin y))) x Hx')).

intros.
unfold G' in |- *.
Opaque FAbs.
simpl in |- *.
eapply leEq_transitive.
2: apply leEq_AbsIR.
astepl
 (AbsIR
    (Sine x (ProjIR1 (ProjIR1 Hx)) [*]Cos y[+]
     Cosine x (ProjIR1 (ProjIR2 Hx)) [*]Sin y) [+]Zero).
apply plus_resp_leEq_both.
apply eq_imp_leEq; apply eq_symmetric_unfolded.
Transparent FAbs.
apply eq_transitive_unfolded with (AbsIR (Part _ _ (ProjIR1 (ProjIR1 Hx')))).
apply FAbs_char.
apply AbsIR_wd; simpl in |- *; rational.
apply FAbs_nonneg.

intros.
unfold G' in |- *.
Opaque FAbs.
simpl in |- *.
eapply leEq_transitive.
2: apply leEq_AbsIR.
astepl
 (Zero[+]
  AbsIR
    (Cosine x (ProjIR1 (ProjIR1 Hx)) [*]Cos y[-]
     Sine x (ProjIR1 (ProjIR2 Hx)) [*]Sin y)).
apply plus_resp_leEq_both.
apply FAbs_nonneg.
apply eq_imp_leEq; apply eq_symmetric_unfolded.
Transparent FAbs.
apply eq_transitive_unfolded with (AbsIR (Part _ _ (ProjIR1 (ProjIR2 Hx')))).
apply FAbs_char.
apply AbsIR_wd; simpl in |- *; rational.

intros.
unfold G' in |- *.
Opaque FAbs.
simpl in |- *.
eapply leEq_transitive.
2: apply leEq_AbsIR.
astepl
 (AbsIR
    [--]
    (Sine x (ProjIR1 (ProjIR1 Hx)) [*]Cos y[+]
     Cosine x (ProjIR1 (ProjIR2 Hx)) [*]Sin y) [+]Zero).
apply
 leEq_wdl
  with
    (AbsIR
       (Sine x (ProjIR1 (ProjIR1 Hx)) [*]Cos y[+]
        Cosine x (ProjIR1 (ProjIR2 Hx)) [*]Sin y) [+]Zero).
apply plus_resp_leEq_both.
apply eq_imp_leEq; apply eq_symmetric_unfolded.
Transparent FAbs.
apply eq_transitive_unfolded with (AbsIR (Part _ _ (ProjIR1 (ProjIR1 Hx')))).
apply FAbs_char.
apply AbsIR_wd; simpl in |- *; rational.
apply FAbs_nonneg.
apply bin_op_wd_unfolded.
apply AbsIR_inv.
algebra.

intros.
unfold G' in |- *.
Opaque FAbs.
simpl in |- *.
eapply leEq_transitive.
2: apply leEq_AbsIR.
astepl
 (Zero[+]
  AbsIR
    (Sine x (ProjIR1 (ProjIR1 Hx)) [*]Sin y[-]
     Cosine x (ProjIR1 (ProjIR2 Hx)) [*]Cos y)).
apply
 leEq_wdl
  with
    (Zero[+]
     AbsIR
       (Cosine x (ProjIR1 (ProjIR2 Hx)) [*]Cos y[-]
        Sine x (ProjIR1 (ProjIR1 Hx)) [*]Sin y)).
apply plus_resp_leEq_both.
apply FAbs_nonneg.
apply eq_imp_leEq; apply eq_symmetric_unfolded.
Transparent FAbs.
apply eq_transitive_unfolded with (AbsIR (Part _ _ (ProjIR1 (ProjIR2 Hx')))).
apply FAbs_char.
apply AbsIR_wd; simpl in |- *; rational.
apply bin_op_wd_unfolded.
algebra.
apply AbsIR_minus.

auto.
Contin.
apply
 four_induction
  with (P := fun n : nat => included (fun _ : IR => CTrue) (Dom (G' y n)));
 auto; unfold G' in |- *.
apply included_FPlus; Included.
apply included_FMinus; Included.
apply included_FInv; apply included_FPlus; Included.
apply included_FMinus; Included.
Qed.

Lemma Sin_plus_eq : forall y n HaF HaG, F' y n Zero HaF [=] G' y n Zero HaG.
do 2 intro;
 apply
  four_ind
   with
     (P := fun n : nat => forall HaF HaG, F' y n Zero HaF [=] G' y n Zero HaG).
intros; simpl in |- *.
apply eq_transitive_unfolded with (Sin y).
simpl in |- *; rational.
apply eq_transitive_unfolded with (Sin Zero[*]Cos y[+]Cos Zero[*]Sin y).
2: simpl in |- *; algebra.
rstepl (Zero[*]Cos y[+]One[*]Sin y).
algebra.

intros; simpl in |- *.
apply eq_transitive_unfolded with (Cos y).
simpl in |- *; rational.
apply eq_transitive_unfolded with (Cos Zero[*]Cos y[-]Sin Zero[*]Sin y).
2: simpl in |- *; algebra.
rstepl (One[*]Cos y[-]Zero[*]Sin y).
algebra.

intros; simpl in |- *.
apply un_op_wd_unfolded.
apply eq_transitive_unfolded with (Sin y).
simpl in |- *; rational.
apply eq_transitive_unfolded with (Sin Zero[*]Cos y[+]Cos Zero[*]Sin y).
2: simpl in |- *; algebra.
rstepl (Zero[*]Cos y[+]One[*]Sin y).
algebra.

intros; simpl in |- *.
apply eq_transitive_unfolded with ( [--] (Cos y)).
simpl in |- *; rational.
apply eq_transitive_unfolded with (Sin Zero[*]Sin y[-]Cos Zero[*]Cos y).
2: simpl in |- *; algebra.
rstepl (Zero[*]Sin y[-]One[*]Cos y).
algebra.

intros.
simpl in |- *; auto.
Qed.

Lemma Sin_plus_der_lft : forall y n, Derivative_n n realline CI (F y) (F' y n).
intro; apply Derivative_n_chain.
simpl in |- *; unfold F in |- *.
apply Feq_reflexive.
apply included_FComp; Included.
intro.

cut (maps_compacts_into realline realline (FId{+} [-C-]y));
 [ intro | apply maps_translation ].

cut (Derivative realline CI (FId{+} [-C-]y) [-C-]One); intros.
2: apply Derivative_wdr with ( [-C-]One{+} [-C-]Zero:PartIR).
2: FEQ.
2: Deriv.

apply
 four_induction
  with (P := fun n : nat => Derivative realline CI (F' y n) (F' y (S n))).
simpl in |- *.
apply Derivative_wdr with ((Cosine[o]FId{+} [-C-]y) {*} [-C-]One).
FEQ.
apply Derivative_comp with realline CI; auto.
Deriv.

simpl in |- *.
apply Derivative_wdr with (( {--}Sine[o]FId{+} [-C-]y) {*} [-C-]One).
FEQ.
apply Derivative_comp with realline CI; auto.
Deriv.

simpl in |- *.
apply Derivative_inv.
apply Derivative_wdr with ((Cosine[o]FId{+} [-C-]y) {*} [-C-]One).
FEQ.
apply Derivative_comp with realline CI; auto.
Deriv.

simpl in |- *.
apply Derivative_wdr with ( {--} (( {--}Sine[o]FId{+} [-C-]y) {*} [-C-]One)).
FEQ.
apply Derivative_inv.
apply Derivative_comp with realline CI; auto.
Deriv.

intros.
auto.
Qed.

Lemma Sin_plus_der_rht : forall y n, Derivative_n n realline CI (G y) (G' y n).
intro; apply Derivative_n_chain.
simpl in |- *; unfold G in |- *.
apply Feq_reflexive.
apply included_FPlus; Included.
intro.
cut (Derivative realline CI Sine Cosine); [ intro | Deriv ].
cut (Derivative realline CI Cosine {--}Sine); [ intro | Deriv ].

apply
 four_induction
  with (P := fun n : nat => Derivative realline CI (G' y n) (G' y (S n))).
simpl in |- *.
let r := PartIR_to_symbPF (Sine{*} [-C-] (Cos y) {+}Cosine{*} [-C-] (Sin y)) in
apply Derivative_wdr with (symbPF_deriv r).
simpl in |- *.
apply eq_imp_Feq.
repeat split.
repeat split.
intros; simpl in |- *; rational.
simpl in |- *; Deriv.

simpl in |- *.
let r := PartIR_to_symbPF (Cosine{*} [-C-] (Cos y) {-}Sine{*} [-C-] (Sin y)) in
apply Derivative_wdr with (symbPF_deriv r).
simpl in |- *.
apply eq_imp_Feq.
repeat split.
repeat split.
intros; simpl in |- *; rational.
simpl in |- *; Deriv.

simpl in |- *.
let r :=
 PartIR_to_symbPF ( {--} (Sine{*} [-C-] (Cos y) {+}Cosine{*} [-C-] (Sin y))) in
apply Derivative_wdr with (symbPF_deriv r).
simpl in |- *.
apply eq_imp_Feq.
repeat split.
repeat split.
intros; simpl in |- *; rational.
simpl in |- *; Deriv.

simpl in |- *.
let r := PartIR_to_symbPF (Sine{*} [-C-] (Sin y) {-}Cosine{*} [-C-] (Cos y)) in
apply Derivative_wdr with (symbPF_deriv r).
simpl in |- *.
apply eq_imp_Feq.
repeat split.
repeat split.
intros; simpl in |- *; rational.
simpl in |- *; Deriv.

auto.
Qed.

Lemma Sin_plus_fun : forall y : IR, Feq realline (F y) (G y).
intro.
cut (Taylor_bnd (F' y)). intro H.
cut (Taylor_bnd (G' y)). intro H0.
cut (forall n : nat, Continuous realline (G' y n)).
intro H1;
 apply Taylor_unique_crit with ZeroR (F' y) (G' y) (Sin_plus_der_lft y) H.
exact (Sin_plus_der_rht y).
auto.
apply Sin_plus_eq.
apply Taylor_Series_conv_to_fun.
auto.
apply four_induction with (P := fun n : nat => Continuous realline (G' y n)).
simpl in |- *; Contin.
simpl in |- *; Contin.
simpl in |- *; Contin.
simpl in |- *; Contin.
auto.
apply Sin_plus_Taylor_bnd_rht.
apply Sin_plus_Taylor_bnd_lft.
Qed.

End Sine_of_Sum.

Opaque Sine Cosine.

Lemma Cos_plus_fun : forall y, Feq realline (Cosine[o]FId{+} [-C-]y) (Cosine{*} [-C-] (Cos y) {-}Sine{*} [-C-] (Sin y)).
intro.
assert (H : Derivative realline CI Sine Cosine). Deriv.
assert (H0 : Derivative realline CI Cosine {--}Sine). Deriv.
apply Derivative_unique with CI (Sine[o]FId{+} [-C-]y).
Derivative_Help.
FEQ.
apply Derivative_comp with realline CI.
apply maps_translation.
Deriv.
Deriv.
apply Derivative_wdl with (Sine{*} [-C-] (Cos y) {+}Cosine{*} [-C-] (Sin y)).
apply Feq_symmetric; apply Sin_plus_fun.
apply Derivative_wdl with (Cos y{**}Sine{+}Sin y{**}Cosine).
apply eq_imp_Feq.
apply included_FPlus; Included.
apply included_FPlus; Included.
intros; simpl in |- *; rational.
apply Derivative_wdr with (Cos y{**}Cosine{+}Sin y{**}{--}Sine).
apply eq_imp_Feq.
apply included_FPlus; Included.
apply included_FMinus; Included.
intros; simpl in |- *; rational.
Deriv.
Qed.

End Sine_and_Cosine.
