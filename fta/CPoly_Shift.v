(* $Id$ *)

Require Export CComplex.

(**
* Shifting polynomials
This can be done for [CRings] in general, but we do it here
only for [CC] because extensionality makes everything much easier,
and we only need it for [CC].
*)

Section Poly_Shifted.

(**
%\begin{convention}%
Let [R] stand for the complex numbers, and [RX] for the polynomials
over [R].
%\end{convention}%
*)

(* begin hide *)
Let R := CC.
Let RX := cpoly_cring R.
(* end hide *)

Definition Shift (a : R) (p : RX) :=
  Sum 0 (lth_of_poly p)
    (fun i : nat => _C_ (nth_coeff i p)[*](_X_[+]_C_ a)[^]i).

Lemma Shift_apply :
 forall (a : R) (p : RX) (x : R), (Shift a p) ! x[=]p ! (x[+]a).
intros.
unfold Shift in |- *.
apply
 eq_transitive_unfolded
  with
    (Sum 0 (lth_of_poly p)
       (fun i : nat => (_C_ (nth_coeff i p)[*](_X_[+]_C_ a)[^]i) ! x)).
apply
 Sum_cpoly_ap
  with (f := fun i : nat => _C_ (nth_coeff i p)[*](_X_[+]_C_ a)[^]i).
apply eq_symmetric_unfolded.
AStepl
 (Sum 0 (lth_of_poly p) (fun i : nat => _C_ (nth_coeff i p)[*]_X_[^]i))
 ! (x[+]a).
apply
 eq_transitive_unfolded
  with
    (Sum 0 (lth_of_poly p)
       (fun i : nat => (_C_ (nth_coeff i p)[*]_X_[^]i) ! (x[+]a))).
apply Sum_cpoly_ap with (f := fun i : nat => _C_ (nth_coeff i p)[*]_X_[^]i).
apply Sum_wd. intros.
AStepl ((_C_ (nth_coeff i p)) ! (x[+]a)[*](_X_[^]i) ! (x[+]a)).
AStepl (nth_coeff i p[*]_X_ ! (x[+]a)[^]i).
AStepl (nth_coeff i p[*](x[+]a)[^]i).
AStepl (nth_coeff i p[*](_X_ ! x[+](_C_ a) ! x)[^]i).
AStepl (nth_coeff i p[*](_X_[+]_C_ a) ! x[^]i).
Step_final ((_C_ (nth_coeff i p)) ! x[*]((_X_[+]_C_ a)[^]i) ! x).
Qed.

Hint Resolve Shift_apply: algebra.

Lemma Shift_wd_rht :
 forall (a : R) (p p' : RX), p[=]p' -> Shift a p[=]Shift a p'.
intros. apply poly_CC_extensional. intros.
AStepl p ! (x[+]a). Step_final p' ! (x[+]a).
Qed.

Lemma Shift_shift : forall (a : R) (p : RX), Shift [--]a (Shift a p)[=]p.
intros. apply poly_CC_extensional. intros.
AStepl (Shift a p) ! (x[+][--]a).
AStepl p ! (x[+][--]a[+]a).
apply apply_wd. Algebra. rational.
Qed.

Lemma Shift_mult :
 forall (a : R) (p1 p2 : RX), Shift a (p1[*]p2)[=]Shift a p1[*]Shift a p2.
intros. apply poly_CC_extensional. intros.
AStepl (p1[*]p2) ! (x[+]a). unfold RX in |- *.
AStepl (p1 ! (x[+]a)[*]p2 ! (x[+]a)).
Step_final ((Shift a p1) ! x[*](Shift a p2) ! x).
Qed.

Lemma Shift_degree_le :
 forall (a : R) (p : RX) (n : nat), degree_le n p -> degree_le n (Shift a p).
intros.
unfold Shift in |- *.
apply Sum_degree_le. auto with arith. intros.
elim (le_lt_dec i n); intros.
replace n with (0 + n).
apply degree_le_mult. apply degree_le_c_.
apply degree_le_mon with (1 * i).
omega.
apply degree_le_nexp. apply degree_imp_degree_le.
apply degree_wd with (_C_ a[+]_X_). Algebra.
apply degree_plus_rht with 0. apply degree_le_c_. apply degree_x_.
auto. auto.
unfold degree_le in H.
apply degree_le_wd with (_C_ (Zero:CC)).
AStepl (Zero:cpoly_cring CC).
AStepl (Zero[*](_X_[+]_C_ a)[^]i).
apply bin_op_wd_unfolded.
Step_final (_C_ (Zero:CC)).
Algebra.
apply degree_le_mon with 0.
auto with arith.
apply degree_le_c_.
Qed.

Lemma Shift_monic :
 forall (a : R) (p : RX) (n : nat), monic n p -> monic n (Shift a p).
intros.
unfold monic in H. elim H. clear H. intros H H0. unfold degree_le in H0.
apply
 monic_wd
  with (Sum 0 n (fun i : nat => _C_ (nth_coeff i p)[*](_X_[+]_C_ a)[^]i)).
AStepl
 (Sum 0 n (fun i : nat => _C_ (nth_coeff i p)[*](_X_[+]_C_ a)[^]i)[+]Zero).
apply
 eq_transitive_unfolded
  with
    (Sum 0 n (fun i : nat => _C_ (nth_coeff i p)[*](_X_[+]_C_ a)[^]i)[+]
     Sum (S n) (lth_of_poly p)
       (fun i : nat => _C_ (nth_coeff i p)[*](_X_[+]_C_ a)[^]i)).
apply bin_op_wd_unfolded. Algebra.
apply eq_symmetric_unfolded.
apply Sum_zero.
cut (n < lth_of_poly p). intro. auto with arith.
apply lt_i_lth_of_poly. AStepl (One:R). Algebra.
intros. cut (n < i). intro.
AStepl (_C_ Zero[*](_X_[+]_C_ a)[^]i).
Step_final (Zero[*](_X_[+]_C_ a)[^]i).
auto with arith.
unfold Shift in |- *.
apply Sum_Sum.
elim (O_or_S n); intro y. elim y. clear y. intros x y.
rewrite <- y in H. rewrite <- y in H0. rewrite <- y.
apply
 monic_wd
  with
    (Sum 0 x (fun i : nat => _C_ (nth_coeff i p)[*](_X_[+]_C_ a)[^]i)[+]
     (_X_[+]_C_ a)[^]S x).
apply
 eq_transitive_unfolded
  with
    (Sum 0 x (fun i : nat => _C_ (nth_coeff i p)[*](_X_[+]_C_ a)[^]i)[+]
     _C_ (nth_coeff (S x) p)[*](_X_[+]_C_ a)[^]S x).
apply bin_op_wd_unfolded. Algebra.
AStepl (One[*](_X_[+]_C_ a)[^]S x).
apply bin_op_wd_unfolded.
Step_final (_C_ (One:R)). Algebra.
apply eq_symmetric_unfolded.
apply
 Sum_last with (f := fun i : nat => _C_ (nth_coeff i p)[*](_X_[+]_C_ a)[^]i).
apply monic_plus with x.
apply Sum_degree_le. auto with arith. intros.
replace x with (0 + x).
apply degree_le_mult. apply degree_le_c_.
apply degree_le_mon with (1 * i).
omega.
apply degree_le_nexp. apply degree_imp_degree_le.
apply degree_wd with (_C_ a[+]_X_). Algebra.
apply degree_plus_rht with 0. apply degree_le_c_. apply degree_x_.
auto. auto.
pattern (S x) at 1 in |- *. replace (S x) with (1 * S x).
apply monic_nexp.
apply monic_wd with (_C_ a[+]_X_). Algebra.
apply monic_plus with 0. apply degree_le_c_.
apply monic_x_.
auto. auto with arith. auto.
rewrite <- y in H. rewrite <- y in H0. rewrite <- y.
apply monic_wd with (One:RX).
unfold Sum in |- *. unfold Sum1 in |- *. simpl in |- *. split.
cut (One[=]nth_coeff 0 p[*]One[+]Zero). auto.
AStepl (nth_coeff 0 p). rational. auto.
apply monic_wd with (_C_ (One:R)). Algebra.
apply monic_c_one.
Qed.

End Poly_Shifted.

Hint Resolve Shift_wd_rht: algebra_c.
Hint Resolve Shift_apply Shift_shift Shift_mult: algebra.