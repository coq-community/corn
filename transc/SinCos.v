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

Require Export Trigonometric.

Section Sum_and_so_on.

Opaque Sine Cosine.

(* begin hide *)
Let F (y : IR) := Sine[o]FId{+} [-C-]y.
Let G (y : IR) := Sine{*}[-C-] (Cos y) {+}Cosine{*}[-C-] (Sin y).
Let F' (y : IR) :=
  (fix funct (n : nat) : PartIR :=
     match n with
     | O => Sine[o]FId{+}[-C-]y
     | S O => Cosine[o]FId{+}[-C-]y
     | S (S O) => {--} (Sine[o]FId{+}[-C-]y)
     | S (S (S O)) => {--} (Cosine[o]FId{+}[-C-]y)
     | S (S (S (S p))) => funct p
     end).
Let G' (y : IR) :=
  (fix funct (n : nat) : PartIR :=
     match n with
     | O => Sine{*}[-C-] (Cos y) {+}Cosine{*}[-C-] (Sin y)
     | S O => Cosine{*}[-C-] (Cos y) {-}Sine{*}[-C-] (Sin y)
     | S (S O) => {--} (Sine{*}[-C-] (Cos y) {+}Cosine{*}[-C-] (Sin y))
     | S (S (S O)) => Sine{*}[-C-] (Sin y) {-}Cosine{*}[-C-] (Cos y)
     | S (S (S (S p))) => funct p
     end).
(* end hide *)

Lemma Sin_plus : forall x y : IR, Sin (x[+]y) [=] Sin x[*]Cos y[+]Cos x[*]Sin y.
Proof.
 intros.
 cut (Feq realline (F y) (G y)).
  intro H.
  cut (Dom (F y) x). intro H0.
   cut (Dom (G y) x). intro H1.
    cut (Part _ _ H0 [=] Part _ _ H1). intro H2.
     simpl in H2.
     simpl in |- *.
     eapply eq_transitive_unfolded.
      eapply eq_transitive_unfolded.
       2: apply H2.
      algebra.
     algebra.
    apply Feq_imp_eq with (fun x : IR => True); auto.
   repeat split.
  exists (I, I); done.
 unfold F, G in |- *; apply Sin_plus_fun.
Qed.

Lemma Cos_plus : forall x y : IR, Cos (x[+]y) [=] Cos x[*]Cos y[-]Sin x[*]Sin y.
Proof.
 intros.
 elim (Cos_plus_fun y). intros.
 elim b; intros H H0.
 cut (Dom (Cosine[o]FId{+}[-C-]y) x). intro H1.
  cut (Dom (Cosine{*}[-C-] (Cos y) {-}Sine{*}[-C-] (Sin y)) x). intro H2.
   simpl in H0.
   simpl in |- *.
   eapply eq_transitive_unfolded.
    eapply eq_transitive_unfolded.
     2: apply (H0 x I H1 H2).
    algebra.
   algebra.
  repeat split.
 by exists (I, I).
Qed.

Opaque Sine Cosine.

Hint Resolve Cos_plus Sin_plus: algebra.

(** As a corollary we get the rule for the tangent of the sum. *)

Lemma Tan_plus : forall x y Hx Hy Hxy H,
 Tan (x[+]y) Hxy [=] (Tan x Hx[+]Tan y Hy[/] One[-]Tan x Hx[*]Tan y Hy[//]H).
Proof.
 intros.
 cut (Cos (x[+]y) [#] Zero).
  cut (Cos y [#] Zero).
   cut (Cos x [#] Zero).
    intros H0 H1 H2.
    apply eq_transitive_unfolded with (Sin (x[+]y) [/] _[//]H2).
     unfold Tan in |- *; simpl in |- *; algebra.
    rstepr ((Tan x Hx[+]Tan y Hy) [*]Cos x[*]Cos y[/] _[//]
      mult_resp_ap_zero _ _ _ H (mult_resp_ap_zero _ _ _ H0 H1)).
    apply div_wd.
     astepl (Sin x[*]Cos y[+]Cos x[*]Sin y).
     unfold Tan, Tang in |- *; simpl in |- *.
     unfold Sin, Cos in |- *; rational.
    astepl (Cos x[*]Cos y[-]Sin x[*]Sin y).
    unfold Tan, Tang in |- *; simpl in |- *; rational.
   inversion_clear Hx.
   inversion_clear X0.
   simpl in |- *; auto.
  inversion_clear Hy.
  inversion_clear X0.
  simpl in |- *; auto.
 inversion_clear Hxy.
 inversion_clear X0.
 simpl in |- *; auto.
Qed.

Transparent Sine Cosine.

(** Sine, cosine and tangent of [[--]x]. *)

Lemma Cos_inv : forall x : IR, Cos [--]x [=] Cos x.
Proof.
 intros.
 simpl in |- *.
 apply series_sum_wd.
 intro.
 unfold cos_seq in |- *.
 elim even_or_odd_plus; intros; simpl in |- *.
 elim p; intros; simpl in |- *.
  2: rational.
 apply mult_wdr.
 astepl (( [--]x[-]Zero) [^]n); astepr ((x[-]Zero) [^]n).
 rewrite a.
 eapply eq_transitive_unfolded.
  2: apply inv_nexp_even; apply even_plus_n_n.
 apply nexp_wd; rational.
Qed.

Lemma Sin_inv : forall x : IR, Sin [--]x [=] [--] (Sin x).
Proof.
 intros.
 simpl in |- *.
 assert (H : forall (x : nat -> IR) (convX : convergent x),
   series_sum _ (conv_series_inv _ convX) [=] [--] (series_sum x convX)). intros; apply series_sum_inv.
  eapply eq_transitive_unfolded.
  2: apply H.
 apply series_sum_wd.
 intro.
 unfold sin_seq in |- *.
 elim even_or_odd_plus; intros; simpl in |- *.
 elim p; intros; simpl in |- *.
  rational.
 apply eq_transitive_unfolded
   with ( [--]One[^]x0[*] ( [--]x[-]Zero) [^]n[/] _[//]nring_fac_ap_zero IR n).
  simpl in |- *; rational.
 apply eq_transitive_unfolded
   with ( [--]One[^]x0[*][--] ((x[-]Zero) [^]n) [/] _[//]nring_fac_ap_zero IR n).
  2: simpl in |- *; rational.
 apply div_wd.
  2: algebra.
 apply mult_wdr.
 rewrite b.
 eapply eq_transitive_unfolded.
  2: apply inv_nexp_odd; apply odd_S; apply even_plus_n_n.
 apply nexp_wd; rational.
Qed.

Opaque Sine Cosine.

Hint Resolve Cos_inv Sin_inv: algebra.

Lemma Tan_inv : forall x Hx Hx', Tan [--]x Hx' [=] [--] (Tan x Hx).
Proof.
 intros; unfold Tan, Tang in |- *.
 cut (Cos x [#] Zero).
  cut (Cos [--]x [#] Zero). intros H H0.
   apply eq_transitive_unfolded with (Sin [--]x[/] _[//]H).
    simpl in |- *; algebra.
   astepl ( [--] (Sin x) [/] _[//]H0).
   rstepl ( [--] (Sin x[/] _[//]H0)).
   simpl in |- *; algebra.
  inversion_clear Hx'.
  inversion_clear X0.
  simpl in |- *; auto.
 inversion_clear Hx.
 inversion_clear X0.
 simpl in |- *; auto.
Qed.

Transparent Sine Cosine.

(**
The fundamental formulas of trigonometry: $\cos(x)^2+\sin(x)^2=1$#cos(x)<sup>2</sup>+sin(x)<sup>2</sup>=1# and, equivalently, $1+\tan(x)^2=\frac1{\cos(x)^2}$#1+tan(x)<sup>2</sup>=1/(cos(x)<sup>2</sup>)#.
*)

Hint Resolve Cos_zero: algebra.

Theorem FFT : forall x : IR, Cos x[^]2[+]Sin x[^]2 [=] One.
Proof.
 intros.
 astepl (Cos x[*]Cos x[+]Sin x[*]Sin x).
 astepr (Cos Zero).
 apply eq_transitive_unfolded with (Cos (x[+][--]x)).
  2: algebra.
 apply eq_symmetric_unfolded.
 eapply eq_transitive_unfolded.
  apply Cos_plus.
 unfold cg_minus in |- *.
 apply bin_op_wd_unfolded.
  algebra.
 astepl (Sin x[*][--] (Sin [--]x)).
 Step_final (Sin x[*][--][--] (Sin x)).
Qed.

Opaque Sine Cosine.

Hint Resolve FFT: algebra.

Lemma FFT' : forall x Hx H, One[+]Tan x Hx[^]2 [=] (One[/] Cos x[^]2[//]H).
Proof.
 intros.
 unfold Tan, Tang in |- *.
 apply eq_transitive_unfolded with (One[+] (Sin x[^]2[/] _[//]H)).
  simpl in |- *; rational.
 astepr (Cos x[^]2[+]Sin x[^]2[/] _[//]H).
 rational.
Qed.

End Sum_and_so_on.

Hint Resolve Derivative_Sin Derivative_Cos: derivate.
Hint Resolve Continuous_Sin Continuous_Cos: continuous.
Hint Resolve Sin_zero Cos_zero Tan_zero Sin_plus Cos_plus Tan_plus Sin_inv
  Cos_inv Tan_inv FFT FFT': algebra.

Opaque Min Sine Cosine.

Section Basic_Properties.

(**
** Basic properties

We now prove most of the usual trigonometric (in)equalities.

Sine, cosine and tangent are strongly extensional and well defined.
*)

Lemma Sin_strext : forall x y : IR, Sin x [#] Sin y -> x [#] y.
Proof.
 intros x y H.
 unfold Sin in H; exact (un_op_strext_unfolded _ _ _ _ H).
Qed.

Lemma Cos_strext : forall x y : IR, Cos x [#] Cos y -> x [#] y.
Proof.
 intros x y H.
 unfold Cos in H; exact (un_op_strext_unfolded _ _ _ _ H).
Qed.

Lemma Tan_strext : forall x y Hx Hy, Tan x Hx [#] Tan y Hy -> x [#] y.
Proof.
 intros x y Hx Hy H.
 unfold Tan in H; exact (pfstrx _ _ _ _ _ _ H).
Qed.

Lemma Sin_wd : forall x y : IR, x [=] y -> Sin x [=] Sin y.
Proof.
 intros; algebra.
Qed.

Lemma Cos_wd : forall x y : IR, x [=] y -> Cos x [=] Cos y.
Proof.
 intros; algebra.
Qed.

Lemma Tan_wd : forall x y Hx Hy, x [=] y -> Tan x Hx [=] Tan y Hy.
Proof.
 intros; unfold Tan in |- *; algebra.
Qed.

Lemma Tan_Sin_over_Cos : forall x Hx H, Tan x Hx[=](Sin x[/]Cos x[//]H).
Proof.
 intros x Hx H.
 change ((Sine x (prj1 IR _ _ _ Hx)[/] Cosine x (ProjT1 (ext2_a IR (Dom Cosine)
   (fun (x0 : IR) (Hx0 : Dom Cosine x0) => Cosine x0 Hx0[#]Zero) x (prj2 IR _ _ _ Hx)))[//]
     ext2 (S:=IR) (P:=Dom Cosine)
       (R:=fun (x0 : IR) (Hx0 : Dom Cosine x0) => Cosine x0 Hx0[#]Zero) (x:=x)
         (prj2 _ _ _ _ Hx))[=](Sine x I[/]Cosine x I[//]H)).
 algebra.
Qed.

(**
The sine and cosine produce values in [[-1,1]].
*)

Lemma AbsIR_Sin_leEq_One : forall x : IR, AbsIR (Sin x) [<=] One.
Proof.
 intros.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply AbsIR_sqrt_sqr with (x2pos := sqr_nonneg _ (Sin x)).
 apply power_cancel_leEq with 2.
   auto with arith.
  apply less_leEq; apply pos_one.
 astepl (Sin x[^]2).
 astepr OneR.
 eapply leEq_wdr.
  2: apply FFT with (x := x).
 apply shift_leEq_plus.
 astepl ZeroR.
 apply sqr_nonneg.
Qed.

Lemma AbsIR_Cos_leEq_One : forall x : IR, AbsIR (Cos x) [<=] One.
Proof.
 intros.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply AbsIR_sqrt_sqr with (x2pos := sqr_nonneg _ (Cos x)).
 apply power_cancel_leEq with 2.
   auto with arith.
  apply less_leEq; apply pos_one.
 astepl (Cos x[^]2).
 astepr OneR.
 eapply leEq_wdr.
  2: apply FFT with (x := x).
 apply shift_leEq_plus'.
 astepl ZeroR.
 apply sqr_nonneg.
Qed.

Lemma Sin_leEq_One : forall x : IR, Sin x [<=] One.
Proof.
 intro.
 eapply leEq_transitive.
  apply leEq_AbsIR.
 apply AbsIR_Sin_leEq_One.
Qed.

Lemma Cos_leEq_One : forall x : IR, Cos x [<=] One.
Proof.
 intro.
 eapply leEq_transitive.
  apply leEq_AbsIR.
 apply AbsIR_Cos_leEq_One.
Qed.

(**
If the cosine is positive then the sine is in [(-1,1)].
*)

Lemma Sin_less_One : forall x : IR, Zero [<] Cos x -> Sin x [<] One.
Proof.
 intros.
 apply power_cancel_less with 2.
  auto.
  apply less_leEq; apply pos_one.
 astepr OneR.
 eapply less_wdr.
  2: apply (FFT x).
 apply shift_less_plus.
 astepl ZeroR.
 apply pos_square; apply Greater_imp_ap; auto.
Qed.

Lemma AbsIR_Sin_less_One : forall x : IR, Zero [<] Cos x -> AbsIR (Sin x) [<] One.
Proof.
 intros.
 apply power_cancel_less with 2.
  auto.
  apply less_leEq; apply pos_one.
 astepr OneR.
 eapply less_wdr.
  2: apply (FFT x).
 apply shift_less_plus.
 apply less_wdl with ZeroR.
  apply pos_square; apply Greater_imp_ap; auto.
 apply eq_symmetric_unfolded; apply x_minus_x.
 eapply eq_transitive_unfolded.
  2: apply AbsIR_eq_x.
  2: apply sqr_nonneg.
 apply eq_symmetric_unfolded; apply AbsIR_nexp_op.
Qed.

End Basic_Properties.

Hint Resolve Sin_wd Cos_wd Tan_wd: algebra.
