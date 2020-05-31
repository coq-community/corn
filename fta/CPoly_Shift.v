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

Require Export CoRN.complex.CComplex.
Import CRing_Homomorphisms.coercions.

(**
* Shifting polynomials
This can be done for [CRings] in general, but we do it here
only for [CC] because extensionality makes everything much easier,
and we only need it for [CC].
*)

Section Poly_Shifted.

Definition Shift (a : CC) (p : CCX) :=
  Sum 0 (lth_of_poly p) (fun i => _C_ (nth_coeff i p) [*] (_X_[+]_C_ a) [^]i).

Lemma Shift_apply : forall a p (x : CC), (Shift a p) ! x [=] p ! (x[+]a).
Proof.
 intros.
 unfold Shift in |- *.
 apply eq_transitive_unfolded with (Sum 0 (lth_of_poly p)
   (fun i : nat => (_C_ (nth_coeff i p) [*] (_X_[+]_C_ a) [^]i) ! x)).
  apply Sum_cpoly_ap with (f := fun i : nat => _C_ (nth_coeff i p) [*] (_X_[+]_C_ a) [^]i).
 apply eq_symmetric_unfolded.
 astepl (Sum 0 (lth_of_poly p) (fun i : nat => _C_ (nth_coeff i p) [*]_X_[^]i)) ! (x[+]a).
 apply eq_transitive_unfolded with (Sum 0 (lth_of_poly p)
   (fun i : nat => (_C_ (nth_coeff i p) [*]_X_[^]i) ! (x[+]a))).
  apply Sum_cpoly_ap with (f := fun i : nat => _C_ (nth_coeff i p) [*]_X_[^]i).
 apply Sum_wd. intros.
 astepl ((_C_ (nth_coeff i p)) ! (x[+]a) [*] (_X_[^]i) ! (x[+]a)).
 astepl (nth_coeff i p[*]_X_ ! (x[+]a) [^]i).
 astepl (nth_coeff i p[*] (x[+]a) [^]i).
 astepl (nth_coeff i p[*] (_X_ ! x[+] (_C_ a) ! x) [^]i).
 astepl (nth_coeff i p[*] (_X_[+]_C_ a) ! x[^]i).
 Step_final ((_C_ (nth_coeff i p)) ! x[*] ((_X_[+]_C_ a) [^]i) ! x).
Qed.

Hint Resolve Shift_apply: algebra.

Lemma Shift_wdr : forall a p p', p [=] p' -> Shift a p [=] Shift a p'.
Proof.
 intros. apply poly_CC_extensional. intros.
 astepl p ! (x[+]a). Step_final p' ! (x[+]a).
Qed.

Lemma Shift_shift : forall a p, Shift [--]a (Shift a p) [=] p.
Proof.
 intros. apply poly_CC_extensional. intros.
 astepl (Shift a p) ! (x[+][--]a).
 astepl p ! (x[+][--]a[+]a).
 apply apply_wd. algebra. rational.
Qed.

Lemma Shift_mult : forall a p1 p2, Shift a (p1[*]p2) [=] Shift a p1[*]Shift a p2.
Proof.
 intros. apply poly_CC_extensional. intros.
 astepl (p1[*]p2) ! (x[+]a).
 astepl (p1 ! (x[+]a) [*]p2 ! (x[+]a)).
 Step_final ((Shift a p1) ! x[*] (Shift a p2) ! x).
Qed.

Lemma Shift_degree_le : forall a p n, degree_le n p -> degree_le n (Shift a p).
Proof.
 intros.
 unfold Shift in |- *.
 apply Sum_degree_le. auto with arith. intros.
  elim (le_lt_dec i n); intros.
  replace n with (0 + n).
   apply degree_le_mult. apply degree_le_c_.
    apply degree_le_mon with (1 * i).
    omega.
   apply degree_le_nexp. apply degree_imp_degree_le.
   apply degree_wd with (_C_ a[+]_X_). algebra.
    apply degree_plus_rht with 0. apply degree_le_c_. apply degree_x_.
     auto. auto.
  unfold degree_le in H.
 apply degree_le_wd with (_C_ ([0]:CC)).
  astepl ([0]:cpoly_cring CC).
  astepl ([0][*] (_X_[+]_C_ a) [^]i).
  apply bin_op_wd_unfolded.
   Step_final (_C_ ([0]:CC)).
  algebra.
 apply degree_le_mon with 0.
  auto with arith.
 apply degree_le_c_.
Qed.

Lemma Shift_monic : forall a p n, monic n p -> monic n (Shift a p).
Proof.
 intros.
 unfold monic in H. elim H. clear H. intros H H0. unfold degree_le in H0.
 apply monic_wd with (Sum 0 n (fun i : nat => _C_ (nth_coeff i p) [*] (_X_[+]_C_ a) [^]i)).
  astepl (Sum 0 n (fun i : nat => _C_ (nth_coeff i p) [*] (_X_[+]_C_ a) [^]i) [+][0]).
  apply eq_transitive_unfolded with
    (Sum 0 n (fun i : nat => _C_ (nth_coeff i p) [*] (_X_[+]_C_ a) [^]i) [+] Sum (S n) (lth_of_poly p)
      (fun i : nat => _C_ (nth_coeff i p) [*] (_X_[+]_C_ a) [^]i)).
   apply bin_op_wd_unfolded. algebra.
    apply eq_symmetric_unfolded.
   apply Sum_zero.
    cut (n < lth_of_poly p). intro. auto with arith.
     apply lt_i_lth_of_poly. astepl ([1]:CC). algebra.
    intros. cut (n < i). intro.
   astepl (_C_ [0][*] (_X_[+]_C_ a) [^]i).
    Step_final ([0][*] (_X_[+]_C_ a) [^]i).
   auto with arith.
  unfold Shift in |- *.
  apply Sum_Sum.
 elim (O_or_S n); intro y. elim y. clear y. intros x y.
  rewrite <- y in H. rewrite <- y in H0. rewrite <- y.
  apply monic_wd with (Sum 0 x (fun i : nat => _C_ (nth_coeff i p) [*] (_X_[+]_C_ a) [^]i) [+]
    (_X_[+]_C_ a) [^]S x).
   apply eq_transitive_unfolded with
     (Sum 0 x (fun i : nat => _C_ (nth_coeff i p) [*] (_X_[+]_C_ a) [^]i) [+]
       _C_ (nth_coeff (S x) p) [*] (_X_[+]_C_ a) [^]S x).
    apply bin_op_wd_unfolded. algebra.
     astepl ([1][*] (_X_[+]_C_ a) [^]S x).
    apply bin_op_wd_unfolded.
     Step_final (_C_ ([1]:CC)). algebra.
    apply eq_symmetric_unfolded.
   apply Sum_last with (f := fun i : nat => _C_ (nth_coeff i p) [*] (_X_[+]_C_ a) [^]i).
  apply monic_plus with x.
    apply Sum_degree_le. auto with arith. intros.
     replace x with (0 + x).
     apply degree_le_mult. apply degree_le_c_.
      apply degree_le_mon with (1 * i).
      omega.
     apply degree_le_nexp. apply degree_imp_degree_le.
     apply degree_wd with (_C_ a[+]_X_). algebra.
      apply degree_plus_rht with 0. apply degree_le_c_. apply degree_x_.
       auto. auto.
    pattern (S x) at 1 in |- *. replace (S x) with (1 * S x).
   apply monic_nexp.
    apply monic_wd with (_C_ a[+]_X_). algebra.
     apply monic_plus with 0. apply degree_le_c_.
      apply monic_x_.
    auto. auto with arith. auto.
   rewrite <- y in H. rewrite <- y in H0. rewrite <- y.
 apply monic_wd with ([1]:CCX).
  unfold Sum in |- *. unfold Sum1 in |- *. simpl in |- *. split.
  cut ([1] [=] nth_coeff 0 p[*][1][+][0]). auto.
    astepl (nth_coeff 0 p). rational. auto.
   apply monic_wd with (_C_ ([1]:CC)). algebra.
  apply monic_c_one.
Qed.

End Poly_Shifted.

Hint Resolve Shift_wdr: algebra_c.
Hint Resolve Shift_apply Shift_shift Shift_mult: algebra.
