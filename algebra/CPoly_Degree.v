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

Require Export CoRN.algebra.CPoly_NthCoeff.
Require Export CoRN.algebra.CFields.
Require Export CoRN.tactics.Rational.
Require Import Lia.
Import CRing_Homomorphisms.coercions.
Set Automatic Introduction.

(**
* Degrees of Polynomials
** Degrees of polynomials over a ring
%\begin{convention}%
Let [R] be a ring and write [RX] for the ring of polynomials
over [R].
%\end{convention}%
*)

Section Degree_def.

Variable R : CRing.

(* begin hide *)
Notation RX := (cpoly_cring R).
(* end hide *)
(**
The length of a polynomial is the number of its coefficients. This is
a syntactical property, as the highest coefficient may be [0]. Note that
the `zero' polynomial [cpoly_zero] has length [0],
a constant polynomial has length [1] and so forth. So the length
is always [1] higher than the `degree' (assuming that the highest
coefficient is [[#][0]])!
*)

Arguments cpoly_zero {CR}.
Arguments cpoly_linear [CR].

Fixpoint lth_of_poly (p : RX) : nat :=
  match p with
  | cpoly_zero       => 0
  | cpoly_linear d q => S (lth_of_poly q)
  end.

(**
When dealing with constructive polynomials, notably over the reals or
complex numbers, the degree may be unknown, as we can not decide
whether the highest coefficient is [[#][0]]. Hence,
degree is a relation between polynomials and natural numbers; if the
degree is unknown for polynomial [p], degree(n,p) doesn't hold for
any [n].  If we don't know the degree of [p], we may still
know it to be below or above a certain number. E.g. for the polynomial
$p_0 +p_1 X +\cdots + p_{n-1} X^{n-1}$#p0 +p1 X + ... + p(n-1)
X^(n-1)#, if $p_i \mathrel{\#}0$#pi apart from 0#, we can say that the
`degree is at least [i]' and if $p_{j+1} = \ldots =p_n =0$#p(j+1)
= ... =pn =0# (with [n] the length of the polynomial), we can say
that the `degree is at most [j]'.
*)

Definition degree_le n (p : RX) : Prop := forall m, n < m -> nth_coeff m p [=] [0].

Definition degree n (p : RX) : CProp := nth_coeff n p [#] [0] and degree_le n p.

Definition monic n (p : RX) : Prop := nth_coeff n p [=] [1] /\ degree_le n p.

Definition odd_cpoly (p : RX) : CProp := {n : nat | Codd n | degree n p}.

Definition even_cpoly (p : RX) : CProp := {n : nat | Ceven n | degree n p}.

Definition regular (p : RX) : CProp := {n : nat | degree n p}.

End Degree_def.

Arguments degree_le [R].
Arguments degree [R].
Arguments monic [R].
Arguments lth_of_poly [R].

Section Degree_props.

Variable R : CRing.

Add Ring R: (CRing_Ring R).

(* begin hide *)
Notation RX := (cpoly_cring R).
(* end hide *)

Lemma degree_le_wd : forall (p p' : RX) n,
 p [=] p' -> degree_le n p -> degree_le n p'.
Proof.
 unfold degree_le in |- *. intros.
 Step_final (nth_coeff m p).
Qed.

Lemma degree_wd : forall (p p' : RX) n, p [=] p' -> degree n p -> degree n p'.
Proof.
 unfold degree in |- *. intros p p' n H H0.
 elim H0. clear H0. intros. split.
 astepl (nth_coeff n p). auto.
  apply degree_le_wd with p; auto.
Qed.

Lemma monic_wd : forall (p p' : RX) n, p [=] p' -> monic n p -> monic n p'.
Proof.
 unfold monic in |- *. intros.
 elim H0. clear H0. intros. split.
 Step_final (nth_coeff n p).
 apply degree_le_wd with p; auto.
Qed.

Lemma degree_imp_degree_le : forall (p : RX) n, degree n p -> degree_le n p.
Proof.
 unfold degree in |- *. intros p n H. elim H. auto.
Qed.

Lemma degree_le_cpoly_zero n: degree_le n (cpoly_zero R).
Proof. intro. reflexivity. Qed.

Lemma degree_le_c_ : forall c : R, degree_le 0 (_C_ c).
Proof.
 unfold degree_le in |- *. intros c m. elim m; intros.
 elim (lt_irrefl _ H).
 simpl in |- *. algebra.
Qed.

Lemma degree_c_ : forall c : R, c [#] [0] -> degree 0 (_C_ c).
Proof.
 unfold degree in |- *. intros. split. simpl in |- *. auto. apply degree_le_c_.
Qed.

Lemma monic_c_one : monic 0 (_C_ ([1]:R)).
Proof.
 unfold monic in |- *. intros. split. simpl in |- *. algebra. apply degree_le_c_.
Qed.

Lemma degree_le_x_ : degree_le 1 (_X_:RX).
Proof.
 unfold degree_le in |- *.
 intro. elim m. intros. elim (lt_n_O _ H).
 intro. elim n. intros. elim (lt_irrefl _ H0).
 intros. simpl in |- *. algebra.
Qed.

Lemma degree_x_ : degree 1 (_X_:RX).
Proof.
 unfold degree in |- *. split. simpl in |- *. algebra. exact degree_le_x_.
Qed.

Lemma monic_x_ : monic 1 (_X_:RX).
Proof.
 unfold monic in |- *. split. simpl in |- *. algebra. exact degree_le_x_.
Qed.

Lemma degree_le_mon : forall (p : RX) m n,
 m <= n -> degree_le m p -> degree_le n p.
Proof.
 unfold degree_le in |- *. intros. apply H0.
 apply le_lt_trans with n; auto with arith.
Qed.

Lemma degree_le_inv : forall (p : RX) n, degree_le n p -> degree_le n [--]p.
Proof.
 unfold degree_le in |- *. intros.
 astepl ( [--] (nth_coeff m p)).
 Step_final ( [--] ([0]:R)).
Qed.

Lemma degree_le_plus : forall (p q : RX) n,
 degree_le n p -> degree_le n q -> degree_le n (p[+]q).
Proof.
 unfold degree_le in |- *. intros.
 astepl (nth_coeff m p[+]nth_coeff m q).
 Step_final ([0][+] ([0]:R)).
Qed.

Lemma degree_le_minus : forall (p q : RX) n,
 degree_le n p -> degree_le n q -> degree_le n (p[-]q).
Proof.
 unfold degree_le in |- *. intros.
 astepl (nth_coeff m p[-]nth_coeff m q).
 Step_final ([0][-] ([0]:R)).
Qed.

Lemma Sum_degree_le : forall (f : nat -> RX) (n k l : nat), k <= S l ->
 (forall i, k <= i -> i <= l -> degree_le n (f i)) -> degree_le n (Sum k l f).
Proof.
 unfold degree_le in |- *. intros. induction  l as [| l Hrecl]; intros.
 generalize (toCle _ _ H); clear H; intro H.
  inversion H as [|m0 X]. 
   unfold Sum in |- *. unfold Sum1 in |- *. simpl in |- *.
   apply eq_transitive with (nth_coeff m ([0]:RX)).
    apply nth_coeff_wd. algebra. algebra.
    inversion X. rename H3 into kis0. unfold Sum in |- *. unfold Sum1 in |- *. simpl in |- *.
  apply eq_transitive with (nth_coeff m (f 0)).
   apply nth_coeff_wd. cut (f 0[-][0] [=] f 0). auto. algebra.
   apply H0; try auto. rewrite kis0; auto.
  elim (le_lt_eq_dec _ _ H); intro y.
  apply eq_transitive_unfolded with (nth_coeff m (Sum k l f[+]f (S l))).
   apply nth_coeff_wd. algebra.
   astepl (nth_coeff m (Sum k l f) [+]nth_coeff m (f (S l))).
  astepr ([0][+] ([0]:R)). apply bin_op_wd_unfolded.
  apply Hrecl. auto with arith. intros.
    apply H0. auto. auto. auto.
     apply H0. auto with arith. auto. auto.
    rewrite y. unfold Sum in |- *. unfold Sum1 in |- *. simpl in |- *.
 apply eq_transitive_unfolded with (nth_coeff m ([0]:RX)).
  apply nth_coeff_wd. algebra. algebra.
Qed.

Lemma degree_le_Sum (l: list (cpoly R)) n:
  (forall p, In p l -> degree_le n p) -> degree_le n (cm_Sum l).
Proof.
 induction l; intros.
  apply degree_le_cpoly_zero.
 change (degree_le n (a [+] cm_Sum l)).
 apply degree_le_plus; intuition.
Qed.

Lemma degree_inv : forall (p : RX) (n : nat), degree n p -> degree n [--]p.
Proof.
 unfold degree in |- *. intros p n H.
 elim H. clear H. intros. split.
 astepl ( [--] (nth_coeff n p)). algebra.
  apply degree_le_inv; auto.
Qed.

Lemma degree_plus_rht : forall (p q : RX) m n,
 degree_le m p -> degree n q -> m < n -> degree n (p[+]q).
Proof.
 unfold degree in |- *. unfold degree_le in |- *. intros.
 elim X. clear X. intros.
 split.
  astepl (nth_coeff n p[+]nth_coeff n q).
  astepl ([0][+]nth_coeff n q).
  astepl (nth_coeff n q). auto.
  intros.
 astepl (nth_coeff m0 p[+]nth_coeff m0 q).
 cut (m < m0). intro.
  Step_final ([0][+] ([0]:R)).
 apply lt_trans with n; auto.
Qed.

Lemma degree_minus_lft : forall (p q : RX) m n,
 degree_le m p -> degree n q -> m < n -> degree n (q[-]p).
Proof.
 intros.
 apply degree_wd with ( [--]p[+]q).
  Step_final (q[+][--]p).
 apply degree_plus_rht with m.
   apply degree_le_inv. auto. auto. auto.
Qed.

Lemma monic_plus : forall (p q : RX) m n,
 degree_le m p -> monic n q -> m < n -> monic n (p[+]q).
Proof.
 unfold monic in |- *. unfold degree_le in |- *. intros.
 elim H0. clear H0. intros.
 split.
  astepl (nth_coeff n p[+]nth_coeff n q).
  astepl ([0][+]nth_coeff n q).
  Step_final (nth_coeff n q).
 intros.
 astepl (nth_coeff m0 p[+]nth_coeff m0 q).
 cut (m < m0). intro.
  Step_final ([0][+] ([0]:R)).
 apply lt_trans with n; auto.
Qed.

Lemma monic_minus : forall (p q : RX) m n,
 degree_le m p -> monic n q -> m < n -> monic n (q[-]p).
Proof.
 intros.
 apply monic_wd with ( [--]p[+]q).
  Step_final (q[+][--]p).
 apply monic_plus with m.
   apply degree_le_inv. auto. auto. auto.
Qed.

Lemma degree_le_mult : forall (p q : RX) m n,
 degree_le m p -> degree_le n q -> degree_le (m + n) (p[*]q).
Proof.
 unfold degree_le in |- *. intros.
 astepl (Sum 0 m0 (fun i : nat => nth_coeff i p[*]nth_coeff (m0 - i) q)).
 apply Sum_zero. auto with arith.
  intros.
 cut ({m < i} + {n < m0 - i}). intro.
  elim H4; clear H4; intros.
   Step_final ([0][*]nth_coeff (m0 - i) q).
  Step_final (nth_coeff i p[*][0]).
 elim (lt_eq_lt_dec m i); intro.
  elim a; intro.
   auto.
  right.
  lia.
 right.
 lia.
Qed.

Lemma degree_le_Product (l: list (cpoly R)) n:
  (forall p, In p l -> degree_le n p) ->
  degree_le (length l * n) (cr_Product l).
Proof.
 induction l; intros.
  apply (degree_le_c_ [1]).
 change (degree_le (n + length l * n) (a [*] cr_Product l)).
 apply degree_le_mult; intuition.
Qed.

Lemma degree_le_mult_constant_l (p: cpoly R) (x: R) (n: nat):
  degree_le n p -> degree_le n (_C_ x [*] p).
Proof with auto.
 intros.
 replace n with (0 + n)%nat...
 apply degree_le_mult...
 apply degree_le_c_.
Qed.

Lemma degree_le_mult_constant_r (p: cpoly R) (x: R) (n: nat):
  degree_le n p -> degree_le n (p [*] _C_ x).
Proof with auto.
 intros.
 replace n with (n + 0)%nat...
 apply degree_le_mult...
 apply degree_le_c_.
Qed.

Lemma degree_mult_aux : forall (p q : RX) m n, degree_le m p -> degree_le n q ->
 nth_coeff (m + n) (p[*]q)  [=] nth_coeff m p[*]nth_coeff n q.
Proof.
 unfold degree_le in |- *. intros.
 astepl (Sum 0 (m + n) (fun i : nat => nth_coeff i p[*]nth_coeff (m + n - i) q)).
 astepl (Sum 0 m (fun i : nat => nth_coeff i p[*]nth_coeff (m + n - i) q) [+]
   Sum (S m) (m + n) (fun i : nat => nth_coeff i p[*]nth_coeff (m + n - i) q)).
 astepr (nth_coeff m p[*]nth_coeff n q[+][0]).
 apply bin_op_wd_unfolded.
  elim (O_or_S m); intro y.
   elim y. clear y. intros x y. rewrite <- y in H. rewrite <- y.
   apply eq_transitive_unfolded with
     (Sum 0 x (fun i : nat => nth_coeff i p[*]nth_coeff (S x + n - i) q) [+]
       nth_coeff (S x) p[*]nth_coeff (S x + n - S x) q).
    apply Sum_last with (f := fun i : nat => nth_coeff i p[*]nth_coeff (S x + n - i) q).
   astepr ([0][+]nth_coeff (S x) p[*]nth_coeff n q).
   apply bin_op_wd_unfolded.
    apply Sum_zero. auto with arith. intros.
     cut (n < S x + n - i). intro.
     Step_final (nth_coeff i p[*][0]).
    lia.
   replace (S x + n - S x) with n. algebra. auto with arith.
    rewrite <- y in H. rewrite <- y.
  pattern n at 2 in |- *. replace n with (0 + n - 0).
  apply Sum_one with (f := fun i : nat => nth_coeff i p[*]nth_coeff (0 + n - i) q).
  auto with arith.
 apply Sum_zero. auto with arith. intros.
  cut (m < i). intro.
  Step_final ([0][*]nth_coeff (m + n - i) q).
 auto.
Qed.

Lemma lead_coeff_product_1 (n: nat) (l: list (cpoly R)):
  (forall p, In p l -> (nth_coeff n p [=] [1] /\ degree_le n p)) ->
  nth_coeff (length l * n) (cr_Product l) [=] [1].
Proof with auto.
 intro H.
 induction l.
  simpl. reflexivity.
 change (nth_coeff (n + length l * n) (a [*] cr_Product l)[=][1]).
 rewrite degree_mult_aux.
   setoid_replace (nth_coeff n a) with ([1]:R).
    rewrite IHl.
     apply mult_one.
    intros. apply H...
   apply H...
  apply H...
 apply degree_le_Product.
 intros. apply H...
Qed.

Hint Resolve degree_mult_aux: algebra.

Lemma monic_mult : forall (p q : RX) m n,
 monic m p -> monic n q -> monic (m + n) (p[*]q).
Proof.
 unfold monic in |- *. intros.
 elim H. clear H. intros. elim H0. clear H0. intros. split.
 astepl (nth_coeff m p[*]nth_coeff n q).
  Step_final ([1][*] ([1]:R)).
 apply degree_le_mult; auto.
Qed.

Lemma degree_le_nexp : forall (p : RX) m n,
 degree_le m p -> degree_le (m * n) (p[^]n).
Proof.
 intros. induction  n as [| n Hrecn]; intros.
 replace (m * 0) with 0.
   apply degree_le_wd with (_C_ ([1]:R)). algebra.
    apply degree_le_c_.
  auto.
 replace (m * S n) with (m * n + m).
  apply degree_le_wd with (p[^]n[*]p). algebra.
   apply degree_le_mult; auto.
 auto.
Qed.

Lemma monic_nexp : forall (p : RX) m n, monic m p -> monic (m * n) (p[^]n).
Proof.
 intros. induction  n as [| n Hrecn]; intros.
 replace (m * 0) with 0.
   apply monic_wd with (_C_ ([1]:R)). algebra.
    apply monic_c_one.
  auto.
 replace (m * S n) with (m * n + m).
  apply monic_wd with (p[^]n[*]p). algebra.
   apply monic_mult; auto.
 auto.
Qed.

Lemma lt_i_lth_of_poly : forall i (p : RX),
 nth_coeff i p [#] [0] -> i < lth_of_poly p.
Proof.
 intros i. induction  i as [| i Hreci]; intros; rename X into H.
 induction  p as [| s p Hrecp]; intros.
   simpl in H. elim (ap_irreflexive_unfolded _ _ H).
   simpl in |- *. auto with arith.
  induction  p as [| s p Hrecp]; intros.
  simpl in H. elim (ap_irreflexive_unfolded _ _ H).
  simpl in |- *. simpl in H. apply lt_n_S. auto.
Qed.

Lemma poly_degree_lth : forall p : RX, degree_le (lth_of_poly p) p.
Proof.
 unfold degree_le in |- *. intros. apply not_ap_imp_eq. intro.
 elim (lt_not_le _ _ H). apply lt_le_weak.
 apply lt_i_lth_of_poly. auto.
Qed.

Lemma Cpoly_ex_degree : forall p : RX, {n : nat | degree_le n p}.
Proof.
 intros. exists (lth_of_poly p). apply poly_degree_lth.
Qed.

Lemma poly_as_sum'' : forall (p : RX) n,
 degree_le n p -> p [=] Sum 0 n (fun i => _C_ (nth_coeff i p) [*]_X_[^]i).
Proof.
 unfold degree_le in |- *. intros. apply all_nth_coeff_eq_imp. intros.
 apply eq_symmetric_unfolded.
 apply eq_transitive_unfolded with
   (Sum 0 n (fun i0 : nat => nth_coeff i (_C_ (nth_coeff i0 p) [*]_X_[^]i0))).
  apply nth_coeff_sum with (p_ := fun i : nat => _C_ (nth_coeff i p) [*]_X_[^]i).
 apply eq_transitive_unfolded
   with (Sum 0 n (fun i0 : nat => nth_coeff i0 p[*]nth_coeff i (_X_[^]i0))).
  apply Sum_wd. intros. algebra.
  elim (le_lt_dec i n); intros.
  astepr (nth_coeff i p[*][1]).
  astepr (nth_coeff i p[*]nth_coeff i (_X_[^]i)).
  apply Sum_term with (i := i) (f := fun i0 : nat => nth_coeff i0 p[*]nth_coeff i (_X_[^]i0)).
    auto with arith. auto.
   intros.
  Step_final (nth_coeff j p[*][0]).
 astepr ([0]:R).
 apply Sum_zero. auto with arith. intros.
  cut (i <> i0). intro.
  Step_final (nth_coeff i0 p[*][0]).
 intro; rewrite <- H2 in H1.
 apply (le_not_lt i n); auto.
Qed.

Hint Resolve poly_as_sum'': algebra.

Lemma poly_as_sum' : forall p : RX,
 p [=] Sum 0 (lth_of_poly p) (fun i => _C_ (nth_coeff i p) [*]_X_[^]i).
Proof.
 intros. apply poly_as_sum''. apply poly_degree_lth.
Qed.

Lemma poly_as_sum : forall (p : RX) n, degree_le n p ->
 forall x, p ! x [=] Sum 0 n (fun i => nth_coeff i p[*]x[^]i).
Proof.
 intros.
 astepl (Sum 0 n (fun i : nat => _C_ (nth_coeff i p) [*]_X_[^]i)) ! x.
 apply eq_transitive_unfolded with (Sum 0 n (fun i : nat => (_C_ (nth_coeff i p) [*]_X_[^]i) ! x)).
  apply Sum_cpoly_ap with (f := fun i : nat => _C_ (nth_coeff i p) [*]_X_[^]i).
 apply Sum_wd. intros.
 astepl ((_C_ (nth_coeff i p)) ! x[*] (_X_[^]i) ! x).
 Step_final (nth_coeff i p[*]_X_ ! x[^]i).
Qed.

Lemma degree_le_zero : forall p : RX, degree_le 0 p -> {a : R | p [=] _C_ a}.
Proof.
 unfold degree_le in |- *. intros.
 exists (nth_coeff 0 p).
 apply all_nth_coeff_eq_imp. intros.
 elim (O_or_S i); intro y.
  elim y. clear y. intros x y. rewrite <- y.
  cut (0 < S x). intro. Step_final ([0]:R). auto with arith.
   rewrite <- y. algebra.
Qed.

Lemma degree_le_1_imp : forall p : RX,
 degree_le 1 p -> {a : R | {b : R | p [=] _C_ a[*]_X_[+]_C_ b}}.
Proof.
 unfold degree_le in |- *. intros.
 exists (nth_coeff 1 p). exists (nth_coeff 0 p).
 apply all_nth_coeff_eq_imp. intros.
 elim i; intros. simpl in |- *. ring.
 elim n; intros.
 simpl in |- *. algebra.
 simpl in |- *. apply H. auto with arith.
Qed.

Lemma degree_le_cpoly_linear : forall (p : cpoly R) c n,
 degree_le (S n) (c[+X*]p) -> degree_le n p.
Proof.
 unfold degree_le in |- *. intros.
 change (nth_coeff (S m) (cpoly_linear _ c p)  [=] [0]) in |- *.
 apply H. auto with arith.
Qed.

Lemma degree_le_cpoly_linear_inv (p: cpoly R) (c: R) (n: nat):
  degree_le n p -> degree_le (S n) (c[+X*]p).
Proof. intros H [|m] E. inversion E. apply (H m). auto with arith. Qed.

Lemma monic_cpoly_linear : forall (p : cpoly R) c n, monic (S n) (c[+X*]p) -> monic n p.
Proof.
 unfold monic in |- *. intros. elim H. clear H. intros. split. auto.
 apply degree_le_cpoly_linear with c. auto.
Qed.

Lemma monic_one : forall (p : cpoly R) c, monic 1 (c[+X*]p) -> forall x, p ! x [=] [1].
Proof.
 intros. cut (monic 0 p). unfold monic in |- *. intros. elim H0. clear H0.
 intros H0 H1.
  elim (degree_le_zero _ H1). intro d. intros.
  astepl (_C_ d) ! x.
  astepl d.
  astepl (nth_coeff 0 (_C_ d)).
  Step_final (nth_coeff 0 p).
 apply monic_cpoly_linear with c. auto.
Qed.

Lemma monic_apzero : forall (p : RX) n, monic n p -> p [#] [0].
Proof.
 unfold monic in |- *. intros.
 elim H. clear H. intros.
 apply nth_coeff_ap_zero_imp with n.
 astepl ([1]:R). apply one_ap_zero.
Qed.

End Degree_props.

Hint Resolve poly_as_sum'' poly_as_sum' poly_as_sum: algebra.
Hint Resolve degree_mult_aux: algebra.


Section degree_props_Field.
(**
** Degrees of polynomials over a field
%\begin{convention}% Let [F] be a field and write [FX] for the ring of
polynomials over [F].
%\end{convention}%
*)

Variable F : CField.

(* begin hide *)
Notation FX := (cpoly_cring F).
(* end hide *)

Lemma degree_mult : forall (p q : FX) m n,
 degree m p -> degree n q -> degree (m + n) (p[*]q).
Proof.
 unfold degree in |- *. intros. rename X into H. rename X0 into H0.
 elim H. clear H. intros H1 H2. elim H0. clear H0. intros H3 H4.
 split.
  astepl (nth_coeff m p[*]nth_coeff n q). algebra.
  apply degree_le_mult; auto.
Qed.

Lemma degree_nexp : forall (p : FX) m n, degree m p -> degree (m * n) (p[^]n).
Proof.
 intros. induction  n as [| n Hrecn]; intros.
 replace (m * 0) with 0.
   apply degree_wd with (_C_ ([1]:F)). algebra.
    apply degree_c_. algebra.
   auto.
 replace (m * S n) with (m * n + m).
  apply degree_wd with (p[^]n[*]p). algebra.
   apply degree_mult; auto.
 auto.
Qed.

Lemma degree_le_mult_imp : forall (p q : FX) m n,
 degree m p -> degree_le (m + n) (p[*]q) -> degree_le n q.
Proof.
 unfold degree in |- *. unfold degree_le in |- *. intros.  rename H0 into H1. rename H into H0. rename X into H. elim H. clear H. intros H2 H3.
 elim (Cpoly_ex_degree _ q). unfold degree_le in |- *. intro N. intro H4.
 (* Set_ not necessary *)
 cut (forall k i : nat, n < i -> N - k < i -> nth_coeff i q [=] [0]). intro H5.
  elim (le_lt_dec m0 N); intros H6.
   replace m0 with (N - (N - m0)). apply H5 with (N - n).
    lia. lia. lia.
    apply H4; auto.
 intro. induction  k as [| k Hreck]; intros.
 apply H4. rewrite <- minus_n_O in H5; auto.
  elim (le_lt_eq_dec (N - k) i); try intro y. auto. rewrite y in Hreck.
   apply mult_cancel_lft with (nth_coeff m p). auto. astepr ([0]:F).
   apply eq_transitive_unfolded with
     (Sum 0 (m + i) (fun j : nat => nth_coeff j p[*]nth_coeff (m + i - j) q)).
   pattern i at 1 in |- *. replace i with (m + i - m).
   apply eq_symmetric_unfolded.
    apply Sum_term with (f := fun j : nat => nth_coeff j p[*]nth_coeff (m + i - j) q).
      auto with arith. auto with arith.
     intros. elim (le_lt_dec j m); intros.
    cut (i < m + i - j). intro.
      cut (n < m + i - j). intro.
       Step_final (nth_coeff j p[*][0]).
      lia. lia.
     Step_final ([0][*]nth_coeff (m + i - j) q).
   auto with arith.
  astepl (nth_coeff (m + i) (p[*]q)).
  cut (m + n < m + i). intro.
   auto.
  auto with arith.
 lia.
Qed.

Lemma degree_mult_imp : forall (p q : FX) m n,
 degree m p -> degree (m + n) (p[*]q) -> degree n q.
Proof.
 unfold degree in |- *. intros. rename X into H. rename X0 into H0.
 elim H. clear H. intros H H1.
 elim H0. clear H0. intros H0 H2.
 cut (degree_le n q). intro H3. split.
  apply mult_cancel_ap_zero_rht with (nth_coeff m p).
   astepl (nth_coeff (m + n) (p[*]q)). auto.
   assumption.
 apply degree_le_mult_imp with p m; auto.
 unfold degree in |- *. split. auto.
 assumption.
Qed.

End degree_props_Field.
