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

Require Export CoRN.fta.CC_Props.

(**
* Continuity of complex polynomials
*)

Section Mult_CC_Continuous.

Lemma mult_absCC : forall (x y : CC) (X Y : IR),
 AbsCC x [<=] X -> AbsCC y [<=] Y -> AbsCC (x[*]y) [<=] X[*]Y.
Proof.
 intros.
 astepl (AbsCC x[*]AbsCC y).
 apply mult_resp_leEq_both.
    apply AbsCC_nonneg. apply AbsCC_nonneg. auto. auto.
Qed.

Lemma estimate_absCC : forall x : CC, {X : IR | [0] [<] X | AbsCC x [<=] X}.
Proof.
 intros.
 exists (AbsCC x[+][1]).
  astepl ([0][+]ZeroR).
  apply plus_resp_leEq_less. apply AbsCC_nonneg. apply pos_one.
   astepl (AbsCC x[+][0]).
 apply less_leEq.
 apply plus_resp_less_lft. apply pos_one.
Qed.

Lemma mult_CC_contin : forall (x y : CC) (e : IR),
 [0] [<] e -> {c : IR | [0] [<] c | {d : IR | [0] [<] d | forall x' y',
 AbsCC (x[-]x') [<=] c -> AbsCC (y[-]y') [<=] d -> AbsCC (x[*]y[-]x'[*]y') [<=] e}}.
Proof.
 do 3 intro. intro H.
 cut ([0] [<] e [/]TwoNZ). intro H0.
  elim (estimate_absCC x). intro X. intros H1 H2.
  elim (estimate_absCC y). intro Y. intros H3 H4.
  cut (Y[#][0]). intro H5.
   exists (e [/]TwoNZ[/] Y[//]H5).
    apply div_resp_pos. auto. auto.
     cut ([0] [<] X[+](e [/]TwoNZ[/] Y[//]H5)). intro.
    cut (X[+](e [/]TwoNZ[/] Y[//]H5)[#][0]). intro H7.
     exists (e [/]TwoNZ[/] X[+](e [/]TwoNZ[/] Y[//]H5)[//]H7).
      apply div_resp_pos. auto. auto.
       intros.
     apply leEq_wdl with (AbsCC ((x[-]x')[*]y[+]x'[*](y[-]y'))).
      apply leEq_transitive with (AbsCC ((x[-]x')[*]y)[+]AbsCC (x'[*](y[-]y'))).
       apply triangle.
      rstepr (e [/]TwoNZ[+]e [/]TwoNZ).
      apply plus_resp_leEq_both.
       apply leEq_wdr with ((e [/]TwoNZ[/] Y[//]H5)[*]Y).
        apply mult_absCC; auto.
       rational.
      apply leEq_wdr with ((X[+](e [/]TwoNZ[/] Y[//]H5))[*]
        (e [/]TwoNZ[/] X[+](e [/]TwoNZ[/] Y[//]H5)[//]H7)).
       apply mult_absCC; auto.
       apply leEq_wdl with (AbsCC (x[+](x'[-]x))).
        apply leEq_transitive with (AbsCC x[+]AbsCC (x'[-]x)).
         apply triangle.
        apply plus_resp_leEq_both. auto.
         astepl (AbsCC [--](x'[-]x)).
        apply leEq_wdl with (AbsCC (x[-]x')). auto.
         apply AbsCC_wd. rational.
        apply AbsCC_wd. rational.
       rational.
     apply AbsCC_wd. rational.
     apply Greater_imp_ap. auto.
    apply plus_resp_pos; auto.
   apply div_resp_pos; auto.
  apply Greater_imp_ap. auto.
  apply pos_div_two. auto.
Qed.

End Mult_CC_Continuous.


Section CPoly_CC_Continuous.

(**
%\begin{convention}% Let [g] be a polynomial over the complex numbers.
%\end{convention}%
*)

Variable g : CCX.

Lemma cpoly_CC_contin : forall (x : CC) (e : IR), [0] [<] e ->
 {d : IR | [0] [<] d | forall x', AbsCC (x[-]x') [<=] d -> AbsCC (g ! x[-]g ! x') [<=] e}.
Proof.
 elim g.
  intros.
  exists OneR. intros. apply pos_one. intros.
   apply leEq_wdl with ZeroR. apply less_leEq. auto.
   cut ([0] [=] AbsCC ([0][-][0])). auto.
   Step_final (AbsCC [0]).
 intros a f. intro H. do 2 intro. intro H0.
 elim (mult_CC_contin x f ! x e H0). intro d1. intros H1 H2.
 elim H2. clear H2. intro c. intros H2 H3.
 elim (H x c H2). clear H. intro d2. intros H H4.
 exists (Min d1 d2). apply less_Min; auto. intros.
  simpl in |- *.
 cut (AbsCC (a[+]x[*]f ! x[-](a[+]x'[*]f ! x')) [<=] e). auto.
  apply leEq_wdl with (AbsCC (x[*]f ! x[-]x'[*]f ! x')).
  apply H3. clear H3.
   apply leEq_transitive with (Min d1 d2); auto. apply Min_leEq_lft.
   apply H4. clear H4.
  apply leEq_transitive with (Min d1 d2); auto. apply Min_leEq_rht.
  apply AbsCC_wd.
 rational.
Qed.

Lemma contin_polyCC : CCcontin (fun x => g ! x).
Proof.
 unfold CCcontin in |- *. unfold CCcontinAt in |- *. unfold CCfunLim in |- *.
 intros.
 elim (cpoly_CC_contin x e); auto.
 intro d. intros H0 H1.
 exists d. auto. intros.
  apply H1; auto.
Qed.

End CPoly_CC_Continuous.
