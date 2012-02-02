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

Require Export CPoly_Degree.

(**
* Reverse of polynomials
*)

Section Monomials.

(**
%\begin{convention}% Let [R] be a ring, and let [RX] be the
polynomials over this ring.
%\end{convention}%
*)

Variable R : CRing.
(* begin hide *)
Let RX := cpoly_cring R.
(* end hide *)

Fixpoint monom (a : R) (n : nat) {struct n} : cpoly_cring R :=
  match n with
  | O   => cpoly_linear _ a (cpoly_zero _)
  | S m => cpoly_linear _ [0] (monom a m)
  end.

Lemma monom_coeff : forall (c : R) n, nth_coeff n (monom c n) [=] c.
Proof.
 intros. induction  n as [| n Hrecn]; intros.
 simpl in |- *. algebra.
  simpl in |- *. algebra.
Qed.

Lemma monom_coeff' : forall (c : R) m n, m <> n -> nth_coeff n (monom c m) [=] [0].
Proof.
 intros c m.
 induction  m as [| m Hrecm]; intros.
  elim (O_or_S n); intro y. elim y. clear y. intros x y. rewrite <- y.
   simpl in |- *. algebra.
   elim (H y).
 elim (O_or_S n); intro y. elim y. clear y. intros x y. rewrite <- y.
  simpl in |- *. apply Hrecm. omega.
  rewrite <- y.
 simpl in |- *. algebra.
Qed.

Hint Resolve monom_coeff monom_coeff': algebra.

Lemma monom_degree : forall (a : R) n, degree_le n (monom a n).
Proof.
 unfold degree_le in |- *. intros.
 cut (n <> m). intro. algebra. omega.
Qed.

Lemma monom_S : forall (a : R) n, monom a (S n) [=] _X_[*]monom a n.
Proof.
 intros.
 apply eq_transitive_unfolded with (cpoly_linear _ [0] (monom a n)).
  simpl in |- *. split. algebra. cut (monom a n [=] monom a n). auto. algebra.
  astepl (_X_[*]monom a n[+]_C_ [0]).
 Step_final (_X_[*]monom a n[+][0]).
Qed.

Hint Resolve monom_S: algebra.

Lemma monom_wd_lft : forall (a b : R) n, a [=] b -> monom a n [=] monom b n.
Proof.
 intros.
 induction  n as [| n Hrecn].
  simpl in |- *. split; auto.
  astepl (_X_[*]monom a n).
 Step_final (_X_[*]monom b n).
Qed.

Hint Resolve monom_wd_lft: algebra_c.

Lemma monom_mult' : forall (a b : R) n, _C_ a[*]monom b n [=] monom (a[*]b) n.
Proof.
 intros.
 induction  n as [| n Hrecn].
  simpl in |- *. split; algebra.
  astepl (_C_ a[*] (_X_[*]monom b n)).
 astepl (_C_ a[*]_X_[*]monom b n).
 astepl (_X_[*]_C_ a[*]monom b n).
 astepl (_X_[*] (_C_ a[*]monom b n)).
 Step_final (_X_[*]monom (a[*]b) n).
Qed.

Hint Resolve monom_mult': algebra.

Lemma monom_mult : forall (a b : R) m n,
 monom a m[*]monom b n [=] monom (a[*]b) (m + n).
Proof.
 intros. induction  m as [| m Hrecm]; intros.
 replace (monom a 0) with (_C_ a). algebra. algebra.
   astepl (_X_[*]monom a m[*]monom b n).
 astepl (_X_[*] (monom a m[*]monom b n)).
 replace (S m + n) with (S (m + n)).
  Step_final (_X_[*]monom (a[*]b) (m + n)).
 auto.
Qed.

Lemma monom_sum : forall (p : RX) n,
 degree_le n p -> p [=] Sum 0 n (fun i => monom (nth_coeff i p) i).
Proof.
 intros.
 unfold RX in |- *; apply all_nth_coeff_eq_imp. intros.
 apply eq_symmetric_unfolded.
 apply eq_transitive_unfolded
   with (Sum 0 n (fun i0 : nat => nth_coeff i (monom (nth_coeff i0 p) i0))).
  apply nth_coeff_sum with (p_ := fun i0 : nat => monom (nth_coeff i0 p) i0).
 elim (le_lt_dec i n); intros.
  apply eq_transitive_unfolded with (nth_coeff i (monom (nth_coeff i p) i)).
   apply Sum_term with (f := fun i0 : nat => nth_coeff i (monom (nth_coeff i0 p) i0)) (i := i).
     auto with arith. auto.
    intros. algebra.
   algebra.
 apply eq_transitive_unfolded with ([0]:R).
  apply Sum_zero. auto with arith.
   intros. cut (i0 <> i). intro. algebra. omega.
  algebra.
Qed.

End Monomials.

Hint Resolve monom_coeff monom_coeff' monom_mult monom_sum: algebra.

Implicit Arguments monom [R].

Section Poly_Reverse.

Variable R : CRing.
(* begin hide *)
Let RX := cpoly_cring R.
(* end hide *)

Definition Rev (n : nat) (p : RX) :=
  Sum 0 n (fun i => monom (nth_coeff i p) (n - i)).

Lemma Rev_coeff : forall n p i, i <= n -> nth_coeff i (Rev n p) [=] nth_coeff (n - i) p.
Proof.
 intros.
 unfold Rev in |- *.
 apply eq_transitive_unfolded with
   (Sum 0 n (fun i0 : nat => nth_coeff i (monom (nth_coeff i0 p) (n - i0)))).
  apply nth_coeff_sum with (p_ := fun i0 : nat => monom (nth_coeff i0 p) (n - i0)).
 apply eq_transitive_unfolded with (nth_coeff i (monom (nth_coeff (n - i) p) (n - (n - i)))).
  apply Sum_term with (i := n - i)
    (f := fun i0 : nat => nth_coeff i (monom (nth_coeff i0 p) (n - i0))).
    auto with arith. omega.
   intros.
  cut (n - j <> i). intro. algebra. omega.
   replace (n - (n - i)) with i. algebra. omega.
Qed.

Lemma Rev_coeff' : forall n p i, n < i -> nth_coeff i (Rev n p) [=] [0].
Proof.
 intros.
 unfold Rev in |- *.
 apply eq_transitive_unfolded with
   (Sum 0 n (fun i0 : nat => nth_coeff i (monom (nth_coeff i0 p) (n - i0)))).
  apply nth_coeff_sum with (p_ := fun i0 : nat => monom (nth_coeff (R:=R) i0 p) (n - i0)).
 apply Sum_zero. auto with arith.
  intros.
 cut (n - i0 <> i). intro. algebra. omega.
Qed.

Hint Resolve Rev_coeff Rev_coeff': algebra.

Lemma Rev_wd : forall n p p', degree_le n p -> p [=] p' -> Rev n p [=] Rev n p'.
Proof.
 unfold RX in |- *. intros.
 apply all_nth_coeff_eq_imp. intros.
 elim (le_lt_dec i n); intros.
  astepl (nth_coeff (n - i) p).
  Step_final (nth_coeff (n - i) p').
 Step_final ([0]:R).
Qed.

Hint Resolve Rev_wd: algebra_c.

Lemma Rev_rev : forall n p, degree_le n p -> Rev n (Rev n p) [=] p.
Proof.
 unfold RX in |- *. intros.
 apply all_nth_coeff_eq_imp. intros.
 elim (le_lt_dec i n); intros.
  astepl (nth_coeff (n - i) (Rev n p)).
  pattern i at 2 in |- *. replace i with (n - (n - i)).
  apply Rev_coeff.
   omega.
  omega.
 unfold degree_le in H.
 Step_final ([0]:R).
Qed.

Hint Resolve Rev_rev: algebra.

Lemma Rev_degree_le : forall n p, degree_le n (Rev n p).
Proof.
 unfold degree_le in |- *. algebra.
Qed.

Lemma Rev_degree : forall n p, p ! [0] [#] [0] -> degree n (Rev n p).
Proof.
 unfold degree_le in |- *. unfold degree in |- *. intros. split.
 astepl (nth_coeff (n - n) p).
  replace (n - n) with 0.
   astepl p ! [0]. auto.
   auto with arith.
 apply Rev_degree_le.
Qed.

Lemma Rev_monom : forall (c : R) m n, m <= n -> Rev n (monom c m) [=] monom c (n - m).
Proof.
 intros.
 apply all_nth_coeff_eq_imp. intros.
 elim (le_lt_dec i n); intro y.
  astepl (nth_coeff (n - i) (monom c m)).
  elim (eq_nat_dec m (n - i)); intro H0.
   cut (i = n - m). intro y0.
    rewrite <- y0. rewrite H0. Step_final c.
    omega.
  cut (n - m <> i). intro.
   Step_final ([0]:R).
  omega.
 cut (n - m <> i). intro.
  Step_final ([0]:R).
 omega.
Qed.

Hint Resolve Rev_monom: algebra.

Lemma Rev_zero : forall n, Rev n [0] [=] ([0]:RX).
Proof.
 intros.
 apply all_nth_coeff_eq_imp. intros.
 elim (le_lt_dec i n); intros.
  astepl (nth_coeff (n - i) [0]:R).
  Step_final ([0]:R).
 Step_final ([0]:R).
Qed.

Hint Resolve Rev_zero: algebra.

Lemma Rev_plus : forall p1 p2 n, Rev n (p1[+]p2) [=] Rev n p1[+]Rev n p2.
Proof.
 intros.
 apply all_nth_coeff_eq_imp. intros.
 elim (le_lt_dec i n); intros.
  astepl (nth_coeff (n - i) (p1[+]p2)).
  unfold RX in |- *.
  astepl (nth_coeff (n - i) p1[+]nth_coeff (n - i) p2).
  Step_final (nth_coeff i (Rev n p1) [+]nth_coeff i (Rev n p2)).
 astepl ([0]:R).
 astepl ([0][+] ([0]:R)).
 Step_final (nth_coeff i (Rev n p1) [+]nth_coeff i (Rev n p2)).
Qed.

Hint Resolve Rev_plus: algebra.

Lemma Rev_minus : forall p1 p2 n, Rev n (p1[-]p2) [=] Rev n p1[-]Rev n p2.
Proof.
 intros.
 apply all_nth_coeff_eq_imp. intros.
 elim (le_lt_dec i n); intros.
  astepl (nth_coeff (n - i) (p1[-]p2)).
  unfold RX in |- *.
  astepl (nth_coeff (n - i) p1[-]nth_coeff (n - i) p2).
  Step_final (nth_coeff i (Rev n p1) [-]nth_coeff i (Rev n p2)).
 astepl ([0]:R).
 astepl ([0][-] ([0]:R)).
 Step_final (nth_coeff i (Rev n p1) [-]nth_coeff i (Rev n p2)).
Qed.

Hint Resolve Rev_minus: algebra.

Lemma Rev_sum0 : forall a_ l n, Rev n (Sum0 l a_) [=] Sum0 l (fun i => Rev n (a_ i)).
Proof.
 intros.
 induction  l as [| l Hrecl].
  replace (Sum0 0 a_) with ([0]:RX).
   replace (Sum0 0 (fun i : nat => Rev n (a_ i))) with ([0]:RX).
    algebra. auto. auto.
   replace (Sum0 (S l) a_) with (Sum0 l a_[+]a_ l).
  replace (Sum0 (S l) (fun i : nat => Rev n (a_ i))) with
    (Sum0 l (fun i : nat => Rev n (a_ i)) [+]Rev n (a_ l)).
   astepl (Rev n (Sum0 l a_) [+]Rev n (a_ l)).
   apply bin_op_wd_unfolded. auto. algebra.
    auto. auto.
Qed.

Hint Resolve Rev_sum0: algebra.

Lemma Rev_sum : forall a_ k l n, Rev n (Sum k l a_) [=] Sum k l (fun i => Rev n (a_ i)).
Proof.
 intros.
 unfold Sum in |- *. unfold Sum1 in |- *.
 astepl (Rev n (Sum0 (S l) a_) [-]Rev n (Sum0 k a_)).
 apply cg_minus_wd; apply Rev_sum0.
Qed.

Lemma Rev_mult : forall n1 n2 p1 p2, degree_le n1 p1 -> degree_le n2 p2 ->
 Rev (n1 + n2) (p1[*]p2) [=] Rev n1 p1[*]Rev n2 p2.
Proof.
 intros.
 cut (degree_le (n1 + n2) (p1[*]p2)). intro.
  cut (p1[*]p2 [=] Sum 0 n2 (fun i2 : nat => Sum 0 n1
    (fun i1 : nat => monom (nth_coeff i1 p1[*]nth_coeff i2 p2) (i1 + i2)))). intro.
   cut (Rev (n1 + n2) (p1[*]p2) [=] Sum 0 n2 (fun i2 : nat => Sum 0 n1 (fun i1 : nat =>
     monom (nth_coeff i1 p1[*]nth_coeff i2 p2) (n1 + n2 - (i1 + i2))))). intro.
    cut (Rev n1 p1 [=] Sum 0 n1 (fun i1 : nat => monom (nth_coeff i1 p1) (n1 - i1))). intro.
     cut (Rev n2 p2 [=] Sum 0 n2 (fun i2 : nat => monom (nth_coeff i2 p2) (n2 - i2))). intro.
      cut (Rev n1 p1[*]Rev n2 p2 [=] Sum 0 n2 (fun i2 : nat => Sum 0 n1 (fun i1 : nat =>
        monom (nth_coeff i1 p1[*]nth_coeff i2 p2) (n1 + n2 - (i1 + i2))))). intro.
       Step_final (Sum 0 n2 (fun i2 : nat => Sum 0 n1 (fun i1 : nat =>
         monom (nth_coeff i1 p1[*]nth_coeff i2 p2) (n1 + n2 - (i1 + i2))))).
      astepl (Sum 0 n1 (fun i1 : nat => monom (nth_coeff i1 p1) (n1 - i1)) [*]
        Sum 0 n2 (fun i2 : nat => monom (nth_coeff i2 p2) (n2 - i2))).
      apply eq_transitive_unfolded with (Sum 0 n2 (fun i2 : nat =>
        Sum 0 n1 (fun i1 : nat => monom (nth_coeff i1 p1) (n1 - i1)) [*]
          monom (nth_coeff i2 p2) (n2 - i2))).
       apply eq_symmetric_unfolded.
       apply mult_distr_sum_lft with (f := fun i2 : nat => monom (nth_coeff i2 p2) (n2 - i2)).
      apply Sum_wd'. auto with arith. intro i2. intros.
       astepl (monom (nth_coeff i2 p2) (n2 - i2) [*]
         Sum 0 n1 (fun i1 : nat => monom (nth_coeff i1 p1) (n1 - i1))).
      apply eq_transitive_unfolded with (Sum 0 n1 (fun i1 : nat =>
        monom (nth_coeff i2 p2) (n2 - i2) [*]monom (nth_coeff i1 p1) (n1 - i1))).
       apply eq_symmetric_unfolded.
       apply mult_distr_sum_lft with (f := fun i1 : nat => monom (nth_coeff i1 p1) (n1 - i1)).
      apply Sum_wd'. auto with arith. intro i1. intros.
       astepl (monom (nth_coeff i1 p1) (n1 - i1) [*]monom (nth_coeff i2 p2) (n2 - i2)).
      astepl (monom (nth_coeff i1 p1[*]nth_coeff i2 p2) (n1 - i1 + (n2 - i2))).
      replace (n1 - i1 + (n2 - i2)) with (n1 + n2 - (i1 + i2)).
       algebra.
      omega.
     unfold Rev in |- *. algebra.
     unfold Rev in |- *. algebra.
    astepl (Rev (n1 + n2) (Sum 0 n2 (fun i2 : nat => Sum 0 n1 (fun i1 : nat =>
      monom (nth_coeff i1 p1[*]nth_coeff i2 p2) (i1 + i2))))).
   apply eq_transitive_unfolded with (Sum 0 n2 (fun i2 : nat => Rev (n1 + n2) (Sum 0 n1 (fun i1 : nat =>
     monom (nth_coeff i1 p1[*]nth_coeff i2 p2) (i1 + i2))))).
    apply Rev_sum with (a_ := fun i2 : nat => Sum 0 n1 (fun i1 : nat =>
      monom (nth_coeff i1 p1[*]nth_coeff i2 p2) (i1 + i2))).
   apply Sum_wd'. auto with arith. intro i2. intros.
    apply eq_transitive_unfolded with (Sum 0 n1 (fun i1 : nat =>
      Rev (n1 + n2) (monom (nth_coeff i1 p1[*]nth_coeff i2 p2) (i1 + i2)))).
    apply Rev_sum with (a_ := fun i1 : nat => monom (nth_coeff i1 p1[*]nth_coeff i2 p2) (i1 + i2)).
   apply Sum_wd'. auto with arith. intro i1. intros.
    apply Rev_monom. omega.
   astepl (Sum 0 n1 (fun i1 : nat => monom (nth_coeff i1 p1) i1) [*]
     Sum 0 n2 (fun i2 : nat => monom (nth_coeff i2 p2) i2)).
  apply eq_transitive_unfolded with (Sum 0 n2 (fun i2 : nat =>
    Sum 0 n1 (fun i1 : nat => monom (nth_coeff i1 p1) i1) [*] monom (nth_coeff i2 p2) i2)).
   apply eq_symmetric_unfolded.
   apply mult_distr_sum_lft with (f := fun i2 : nat => monom (nth_coeff i2 p2) i2).
  apply Sum_wd'. auto with arith. intro i2. intros.
   astepl (monom (nth_coeff i2 p2) i2[*] Sum 0 n1 (fun i1 : nat => monom (nth_coeff i1 p1) i1)).
  apply eq_transitive_unfolded with (Sum 0 n1 (fun i1 : nat =>
    monom (nth_coeff i2 p2) i2[*]monom (nth_coeff i1 p1) i1)).
   apply eq_symmetric_unfolded.
   apply mult_distr_sum_lft with (f := fun i1 : nat => monom (nth_coeff i1 p1) i1).
  apply Sum_wd'. auto with arith. intro i1. intros.
   Step_final (monom (nth_coeff i1 p1) i1[*]monom (nth_coeff i2 p2) i2).
 unfold RX in |- *. apply degree_le_mult; auto.
Qed.

End Poly_Reverse.

Hint Resolve Rev_wd: algebra_c.
Hint Resolve Rev_rev Rev_mult: algebra.

Implicit Arguments Rev [R].
