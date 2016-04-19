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

Require Export CoRN.reals.IVT.

(**
* Roots of polynomials of odd degree *)

Section CPoly_Big.

(**
** Monic polynomials are positive near infinity
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

Variable R : COrdField.

(* begin hide *)
Let RX := (cpoly R).
(* end hide *)

Lemma Cbigger : forall x y : R, {z : R | x [<=] z | y [<=] z}.
Proof.
 intros.
 elim (less_cotransitive_unfolded _ x (x[+][1]) (less_plusOne _ _) y); intro.
  exists (y[+][1]); apply less_leEq.
   apply less_leEq_trans with y. auto. apply less_leEq; apply less_plusOne.
    apply less_plusOne.
 exists (x[+][1]); apply less_leEq.
  apply less_plusOne.
 auto.
Qed.

Lemma Ccpoly_big : forall (p : RX) n, 0 < n ->
 monic n p -> forall Y, {X : R | forall x, X [<=] x -> Y [<=] p ! x}.
Proof.
 intro. elim p.
 unfold monic in |- *. simpl in |- *. intros. elim H0. intros H1 H2.
  cut ([0][~=] ([1]:R)). intro. elim (H3 H1).
   apply ap_imp_neq. apply ap_symmetric_unfolded. apply ring_non_triv.
  intros c q. intros H n H0 H1 Y.
 elim (O_or_S n); intro y. elim y. intro m. intro y0.
  rewrite <- y0 in H1.
  elim (zerop m); intro y1. simpl in |- *.
   exists (Y[-]c). intros.
   rewrite y1 in H1.
   apply shift_leEq_plus'.
   cut (q ! x [=] [1]). intro.
    astepr (x[*][1]). astepr x. auto.
    apply monic_one with c. auto.
   cut (monic m q). intro H2.
   elim (Cbigger [0] (Y[-]c)). intro Y'. intros H3 H4.
   elim (H m y1 H2 Y'). intro X'. intro H5.
   simpl in |- *.
   elim (Cbigger [1] X'). intro X. intros H6 H7.
   exists X. intros.
   apply shift_leEq_plus'.
   apply leEq_transitive with ([1][*]Y').
    astepr Y'. auto.
    apply mult_resp_leEq_both; auto.
     apply less_leEq. apply pos_one.
     apply leEq_transitive with X; auto.
   change (Y' [<=] q ! x) in |- *.
   apply H5.
   apply leEq_transitive with X; auto.
  apply monic_cpoly_linear with c; auto.
 rewrite <- y in H0.
 elim (lt_irrefl _ H0).
Qed.

Lemma cpoly_pos : forall (p : RX) n, 0 < n -> monic n p -> {x : R | [0] [<=] p ! x}.
Proof.
 intros.
 elim (Ccpoly_big _ _ H H0 [0]). intros x H1.
 exists (x[+][1]).
 apply H1. apply less_leEq. apply less_plusOne.
Qed.

Lemma Ccpoly_pos' : forall (p : RX) a n, 0 < n -> monic n p -> {x : R | a [<] x | [0] [<=] p ! x}.
Proof.
 intros.
 elim (Ccpoly_big _ _ H H0 [0]). intro x'. intro H1.
 elim (Cbigger (a[+][1]) x'). intro x. intros.
 exists x; auto.
 apply less_leEq_trans with (a[+][1]).
  apply less_plusOne. auto.
Qed.

End CPoly_Big.

Section Flip_Poly.

(**
** Flipping a polynomial
%\begin{convention}% Let [R] be a ring.
%\end{convention}%
*)

Variable R : CRing.

Add Ring R: (CRing_Ring R).

(* begin hide *)
Let RX := (cpoly R).
(* end hide *)

Fixpoint flip (p : RX) : RX :=
  match p with
  | cpoly_zero _     => cpoly_zero _
  | cpoly_linear _ c q => cpoly_inv _ (cpoly_linear _ c (flip q))
  end.

Lemma flip_poly : forall (p : RX) x, (flip p) ! x [=] [--]p ! ( [--]x).
Proof.
 intro p. elim p.
 intros. simpl in |- *. algebra.
  intros c q. intros.
 change ( [--]c[+]x[*] (cpoly_inv _ (flip q)) ! x [=] [--] (c[+][--]x[*]q ! ( [--]x))) in |- *.
 astepl ( [--]c[+]x[*][--] (flip q) ! x).
 astepl ( [--]c[+]x[*][--][--]q ! ( [--]x)).
 ring.
Qed.

Lemma flip_coefficient : forall (p : RX) i,
 nth_coeff i (flip p) [=] [--] ( [--][1][^]i) [*]nth_coeff i p.
Proof.
 intro p. elim p.
 simpl in |- *. algebra.
  intros c q. intros.
 elim i. simpl in |- *. ring.
  intros. simpl in |- *.
 astepl ( [--] (nth_coeff n (flip q))).
 astepl ( [--] ( [--] ( [--][1][^]n) [*]nth_coeff n q)).
 simpl in |- *. ring.
Qed.

Hint Resolve flip_coefficient: algebra.

Lemma flip_odd : forall (p : RX) n, odd n -> monic n p -> monic n (flip p).
Proof.
 unfold monic in |- *. unfold degree_le in |- *.
 intros.
 elim H0. clear H0. intros.
 split.
  astepl ( [--] ( [--][1][^]n) [*]nth_coeff n p).
  astepl ( [--][--] ([1][^]n) [*]nth_coeff n p).
  astepl ([1][^]n[*]nth_coeff n p).
  astepl ([1][*]nth_coeff n p).
  Step_final ([1][*] ([1]:R)).
 intros.
 astepl ( [--] ( [--][1][^]m) [*]nth_coeff m p).
 Step_final ( [--] ( [--][1][^]m) [*] ([0]:R)).
Qed.

End Flip_Poly.

Hint Resolve flip_poly: algebra.


Section OddPoly_Signs.

(**
** Sign of a polynomial of odd degree
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

Variable R : COrdField.

(* begin hide *)
Let RX := (cpoly R).
(* end hide *)

Lemma oddpoly_pos : forall (p : RX) n, odd n -> monic n p -> {x : R | [0] [<=] p ! x}.
Proof.
 intros.
 apply cpoly_pos with n; auto.
 elim H. intros. auto with arith.
Qed.

Lemma oddpoly_pos' : forall (p : RX) a n,
 odd n -> monic n p -> {x : R | a [<] x | [0] [<=] p ! x}.
Proof.
 intros.
 elim (Ccpoly_pos' _ p a n). intros x H1 H2.
   exists x; assumption.
  elim H; auto with arith.
 assumption.
Qed.

Lemma oddpoly_neg : forall (p : RX) n, odd n -> monic n p -> {x : R | p ! x [<=] [0]}.
Proof.
 intros.
 elim (oddpoly_pos _ _ H (flip_odd _ _ _ H H0)). intro x. intros.
 exists ( [--]x).
 astepl ( [--][--]p ! ( [--]x)). astepr ( [--] ([0]:R)).
 apply inv_resp_leEq.
 astepr (flip _ p) ! x. auto.
Qed.

End OddPoly_Signs.


Section Poly_Norm.

(**
** The norm of a polynomial
%\begin{convention}% Let [R] be a field, and [RX] the polynomials over
this field.
%\end{convention}%
*)

Variable R : CField.
(* begin hide *)
Let RX := cpoly_cring R.
(* end hide *)

Lemma poly_norm_aux : forall (p : RX) n, degree n p -> nth_coeff n p [#] [0].
Proof.
 unfold degree in |- *. intros p n H.
 elim H. auto.
Qed.

Definition poly_norm p n H := _C_ ([1][/] _[//]poly_norm_aux p n H) [*]p.

Lemma poly_norm_monic : forall p n H, monic n (poly_norm p n H).
Proof.
 unfold poly_norm in |- *. unfold monic in |- *. unfold degree in |- *. unfold degree_le in |- *. intros.
 elim H. intros H0 H1.
 split.
  Step_final (([1][/] nth_coeff n p[//]poly_norm_aux p n (pair H0 H1)) [*] nth_coeff n p).
 intros.
 astepl (([1][/] nth_coeff n p[//]poly_norm_aux p n (pair H0 H1)) [*] nth_coeff m p).
 Step_final (([1][/] nth_coeff n p[//]poly_norm_aux p n H) [*][0]).
Qed.

Lemma poly_norm_apply : forall p n H x, (poly_norm p n H) ! x [=] [0] -> p ! x [=] [0].
Proof.
 unfold poly_norm in |- *. intros.
 apply mult_cancel_lft with ([1][/] nth_coeff n p[//]poly_norm_aux p n H).
  apply div_resp_ap_zero_rev. apply ring_non_triv.
  astepl ((_C_ ([1][/] nth_coeff n p[//]poly_norm_aux p n H)) ! x[*]p ! x).
 astepl (_C_ ([1][/] nth_coeff n p[//]poly_norm_aux p n H) [*]p) ! x.
 Step_final ([0]:R).
Qed.

End Poly_Norm.


Section OddPoly_Root.

(**
** Roots of polynomials of odd degree
Polynomials of odd degree over the reals always have a root. *)

Lemma oddpoly_root' : forall f n, odd n -> monic n f -> {x : IR | f ! x [=] [0]}.
Proof.
 intros.
 elim (oddpoly_neg _ f n); auto. intro a. intro H1.
 elim (oddpoly_pos' _ f a n); auto. intro b. intros H2 H3.
 cut {x : IR | a [<=] x /\ x [<=] b /\ f ! x [=] [0]}.
  intro H4.
  elim H4. clear H4. intros x H4.
  elim H4. clear H4. intros H4 H5.
  elim H5. clear H5. intros.
  exists x. auto.
  apply Civt_poly; auto.
 apply monic_apzero with n; auto.
Qed.

Lemma oddpoly_root : forall f n, odd n -> degree n f -> {x : IR | f ! x [=] [0]}.
Proof.
 intros f n H H0.
 elim (oddpoly_root' (poly_norm _ f n H0) n); auto.
  intros. exists x.
  apply poly_norm_apply with n H0; auto.
 apply poly_norm_monic; auto.
Qed.

Lemma realpolyn_oddhaszero : forall f, odd_cpoly _ f -> {x : IR | f ! x [=] [0]}.
Proof.
 unfold odd_cpoly in |- *.
 intros f H.
 elim H. clear H. intro n. intros H H0.
 cut (odd n).
  intro.
  elim (oddpoly_root f n H1 H0). intros. exists x. auto.
  apply Codd_to.
 assumption.
Qed.

End OddPoly_Root.
