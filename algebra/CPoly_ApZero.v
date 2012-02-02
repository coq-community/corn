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
Require Export COrdFields2.
Require Import Morphisms Permutation.
Require ne_list.
Import ne_list.notations.

Set Automatic Introduction.

(**
* Polynomials apart from zero *)

Definition distinct1 (A : CSetoid) (f : nat -> A) := forall i j, i <> j -> f i [#] f j.

Implicit Arguments distinct1 [A].

Section Poly_Representation.
(**
** Representation of polynomials
%\begin{convention}% Let [R] be a field, [RX] the ring of polynomials
over [R], [a_ : nat->R] with [(distinct1 a_)] and let [f] be a
polynomial over [R], [n] a natural with [(degree_le n f)], i.e. [f]
has degree at most [n].
%\end{convention}%
*)

Variable R : CField.
Variable a_ : nat -> R.
Hypothesis distinct_a_ : distinct1 a_.
Variable f : cpoly_cring R.
Variable n : nat.
Hypothesis degree_f : degree_le n f.

Add Ring cpolycring_th : (cpoly_ring_th R).

(* begin hide *)
Notation RX := (cpoly_cring R).
(* end hide *)

Load "Transparent_algebra".

Lemma poly_linear_shifted : forall (a : R) (f : RX),
 {f' : RX | {f'' : R | f [=] (_X_[-]_C_ a) [*]f'[+]_C_ f''}}.
Proof.
 intros.
 induction  f0 as [| s f0 Hrecf0]; intros.
  exists (cpoly_zero R).
  exists ([0]:R).
  simpl in |- *.
  algebra.
 elim Hrecf0. intro g'. intros H.
 elim H. intro g''. intros H0.
 exists (_X_[*]g'[+]_C_ g'').
 exists (a[*]g''[+]s).
 astepl (_X_[*]f0[+]_C_ s).
 astepl (_X_[*] ((_X_[-]_C_ a) [*]g'[+]_C_ g'') [+]_C_ s).
 apply eq_symmetric_unfolded.
 cut (_C_ (a[*]g''[+]s) [=] _C_ a[*]_C_ g''[+]_C_ s). intro.
  astepl ((_X_[-]_C_ a) [*] (_X_[*]g'[+]_C_ g'') [+] (_C_ a[*]_C_ g''[+]_C_ s)).
  unfold cg_minus. ring.
 Step_final (_C_ (a[*]g'') [+]_C_ s).
Qed.
Load "Opaque_algebra".

Lemma poly_linear_factor : forall (f : RX) a, f ! a [=] [0] -> {f' : RX | f [=] (_X_[-]_C_ a) [*]f'}.
Proof.
 intros.
 elim (poly_linear_shifted a f0). intro f'. intros H0.
 elim H0. intro f''. intros H1.
 exists f'.
 cut (_C_ f'' [=] [0]). intro.
  astepl ((_X_[-]_C_ a) [*]f'[+]_C_ f'').
  Step_final ((_X_[-]_C_ a) [*]f'[+][0]).
 astepr (_C_ ([0]:R)).
 apply cpoly_const_eq.
 astepl ([0][+]f'').
 astepl ([0][*]f' ! a[+]f'').
 astepl ((a[-]a) [*]f' ! a[+]f'').
 astepl ((_X_ ! a[-] (_C_ a) ! a) [*]f' ! a[+]f'').
 astepl ((_X_[-]_C_ a) ! a[*]f' ! a[+]f'').
 astepl (((_X_[-]_C_ a) [*]f') ! a[+]f'').
 astepl (((_X_[-]_C_ a) [*]f') ! a[+] (_C_ f'') ! a).
 astepl ((_X_[-]_C_ a) [*]f'[+]_C_ f'') ! a.
 Step_final f0 ! a.
Qed.

Lemma zero_poly : forall n,
  (forall i j: nat, i <= n -> j <= n -> i <> j -> a_ i[#]a_ j) ->
  forall (f : RX),
 degree_le n f -> (forall i, i <= n -> f ! (a_ i) [=] [0]) -> f [=] [0].
Proof with auto.
 intro.
 clear degree_f n distinct_a_.
 intro distinct_a_.
 induction  n0 as [| n0 Hrecn0]; intros.
  elim (degree_le_zero _ _ H). intros.
  astepl (_C_ x).
  astepr (_C_ ([0]:R)).
  apply cpoly_const_eq.
  apply eq_transitive_unfolded with f0 ! (a_ 0).
   Step_final (_C_ x) ! (a_ 0).
  apply H0...
 cut (f0 ! (a_ (S n0)) [=] [0])... intro.
 elim (poly_linear_factor f0 (a_ (S n0)) H1). intro f'. intros.
 astepl ((_X_[-]_C_ (a_ (S n0))) [*]f').
 cut (f' [=] [0]). intro.
  Step_final ((_X_[-]_C_ (a_ (S n0))) [*][0]).
 apply Hrecn0.
   intuition.
  apply degree_le_mult_imp with (_X_[-]_C_ (a_ (S n0))) 1.
   apply degree_minus_lft with 0...
    apply degree_le_c_.
   apply degree_x_.
  apply degree_le_wd with f0...
 intros.
 apply mult_cancel_lft with (a_ i[-]a_ (S n0)).
  apply minus_ap_zero.
  apply distinct_a_...
  intro; rewrite H3 in H2; exact (le_Sn_n _ H2).
 astepr ([0]:R).
 cut (a_ i[-]a_ (S n0) [=] (_X_[-]_C_ (a_ (S n0))) ! (a_ i)). intro.
  astepl ((_X_[-]_C_ (a_ (S n0))) ! (a_ i) [*]f' ! (a_ i)).
  astepl ((_X_[-]_C_ (a_ (S n0))) [*]f') ! (a_ i).
  astepl f0 ! (a_ i)...
 Step_final (_X_ ! (a_ i) [-] (_C_ (a_ (S n0))) ! (a_ i)).
Qed.

Lemma identical_poly :
  (forall i j: nat, i <= n -> j <= n -> i <> j -> a_ i[#]a_ j) ->
  forall f g : RX, degree_le n f -> degree_le n g ->
   (forall i, i <= n -> f ! (a_ i) [=] g ! (a_ i)) -> f [=] g.
Proof.
 intros.
 apply cg_inv_unique_2.
 apply zero_poly with n.
   assumption.
  apply degree_le_minus; auto.
 intros.
 astepl (f0 ! (a_ i) [-]g ! (a_ i)).
 Step_final (f0 ! (a_ i) [-]f0 ! (a_ i)).
Qed.

Definition poly_01_factor' (n : nat) := _X_[-]_C_ (a_ n).

Lemma poly_01_factor'_degree : forall n, degree_le 1 (poly_01_factor' n).
Proof.
 intros.
 unfold poly_01_factor' in |- *.
 apply degree_imp_degree_le.
 apply degree_minus_lft with 0.
   apply degree_le_c_.
  apply degree_x_.
 auto.
Qed.

Lemma poly_01_factor'_zero : forall n, (poly_01_factor' n) ! (a_ n) [=] [0].
Proof.
 intros.
 unfold poly_01_factor' in |- *.
 astepl (_X_ ! (a_ n0) [-] (_C_ (a_ n0)) ! (a_ n0)).
 Step_final (a_ n0[-]a_ n0).
Qed.

Lemma poly_01_factor'_apzero :
 forall n i, i <> n -> (poly_01_factor' n) ! (a_ i) [#] [0].
Proof.
 intros.
 unfold poly_01_factor' in |- *.
 astepl (_X_ ! (a_ i) [-] (_C_ (a_ n0)) ! (a_ i)).
 astepl (a_ i[-]a_ n0). algebra.
Qed.

Hint Resolve poly_01_factor'_zero.

Definition poly_01_factor n i (H : i <> n) :=
 poly_01_factor' n[*]
   _C_ ([1][/] (poly_01_factor' n) ! (a_ i) [//]poly_01_factor'_apzero n i H).

Lemma poly_01_factor_degree : forall n i H, degree_le 1 (poly_01_factor n i H).
Proof.
 intros.
 unfold poly_01_factor in |- *.
 replace 1 with (1 + 0).
  apply degree_le_mult.
   apply poly_01_factor'_degree.
  apply degree_le_c_.
 auto.
Qed.

Lemma poly_01_factor_zero : forall n i H, (poly_01_factor n i H) ! (a_ n) [=] [0].
Proof.
 intros.
 unfold poly_01_factor in |- *.
 astepl ((poly_01_factor' n0) ! (a_ n0) [*] (_C_
   ([1][/] (poly_01_factor' n0) ! (a_ i) [//]poly_01_factor'_apzero n0 i H)) ! (a_ n0)).
 Step_final ([0][*] (_C_ ([1][/] (poly_01_factor' n0) ! (a_ i) [//]poly_01_factor'_apzero n0 i H))
   ! (a_ n0)).
Qed.

Lemma poly_01_factor_one : forall n i H, (poly_01_factor n i H) ! (a_ i) [=] [1].
Proof.
 intros.
 unfold poly_01_factor in |- *.
 astepl ((poly_01_factor' n0) ! (a_ i) [*] (_C_
   ([1][/] (poly_01_factor' n0) ! (a_ i) [//]poly_01_factor'_apzero n0 i H)) ! (a_ i)).
 astepl ((poly_01_factor' n0) ! (a_ i) [*]
   ([1][/] (poly_01_factor' n0) ! (a_ i) [//]poly_01_factor'_apzero n0 i H)).
 apply div_1'.
Qed.

Hint Resolve poly_01_factor_zero poly_01_factor_one: algebra.

Fixpoint poly_01 (i n : nat) {struct n} : cpoly_cring R :=
  match eq_nat_dec i n with
  | left  _  => [1]
  | right ne => poly_01_factor n i ne
  end
  [*]
  match n with
  | O   => [1]
  | S m => poly_01 i m
  end.

Lemma poly_01_degree' : forall n i, degree_le (S n) (poly_01 i n).
Proof.
 intros.
 induction  n0 as [| n0 Hrecn0]. intros.
  simpl in |- *.
  elim (eq_nat_dec i 0); intro y.
   apply degree_le_wd with (_C_ ([1]:R)).
    Step_final ([1]:cpoly_cring R).
   apply degree_le_mon with 0.
    auto with arith.
   apply degree_le_c_.
  apply degree_le_wd with (poly_01_factor 0 i y).
   algebra.
  apply poly_01_factor_degree.
 simpl in |- *.
 elim (eq_nat_dec i (S n0)); intro.
  apply degree_le_mon with (S n0).
   auto.
  apply degree_le_wd with (poly_01 i n0).
   algebra.
  auto.
 replace (S (S n0)) with (1 + S n0).
  apply degree_le_mult.
   apply poly_01_factor_degree.
  auto.
 auto.
Qed.

Lemma poly_01_degree : forall n i, i <= n -> degree_le n (poly_01 i n).
Proof.
 intros.
 induction  n0 as [| n0 Hrecn0]; intros.
  simpl in |- *.
  elim (eq_nat_dec i 0); intro y.
   apply degree_le_wd with (_C_ ([1]:R)).
    Step_final ([1]:cpoly_cring R).
   apply degree_le_c_.
  cut (i = 0). intro.
   elim (y H0).
  auto with arith.
 simpl in |- *.
 elim (eq_nat_dec i (S n0)); intro.
  apply degree_le_wd with (poly_01 i n0).
   algebra.
  apply poly_01_degree'.
 pattern (S n0) at 1 in |- *.
 replace (S n0) with (1 + n0).
  apply degree_le_mult.
   apply poly_01_factor_degree.
  apply Hrecn0.
  elim (le_lt_eq_dec _ _ H); auto with arith.
  intro; elim (b b0).
 auto.
Qed.

Lemma poly_01_zero : forall n i j, j <= n -> j <> i -> (poly_01 i n) ! (a_ j) [=] [0].
Proof.
 intros.
 induction  n0 as [| n0 Hrecn0]; intros.
  rewrite <- (le_n_O_eq j H).
  rewrite <- (le_n_O_eq j H) in H0.
  simpl in |- *.
  elim (eq_nat_dec i 0); intro y.
   rewrite y in H0.
   elim (H0 (refl_equal 0)).
  astepl ((poly_01_factor 0 i y) ! (a_ 0) [*][1] ! (a_ 0)).
  astepl ((poly_01_factor 0 i y) ! (a_ 0) [*][1]).
  astepl (poly_01_factor 0 i y) ! (a_ 0).
  apply poly_01_factor_zero.
 elim (eq_nat_dec j (S n0)); intro y.
  simpl in |- *.
  rewrite <- y.
  elim (eq_nat_dec i j); intro y0.
   rewrite y0 in H0.
   elim (H0 (refl_equal j)).
  astepl ((poly_01_factor j i y0) ! (a_ j) [*] (poly_01 i n0) ! (a_ j)).
  Step_final ([0][*] (poly_01 i n0) ! (a_ j)).
 cut (j <= n0). intro.
  simpl in |- *.
  elim (eq_nat_dec i (S n0)); intro y0.
   astepl ([1] ! (a_ j) [*] (poly_01 i n0) ! (a_ j)).
   Step_final ([1] ! (a_ j) [*][0]).
  astepl ((poly_01_factor (S n0) i y0) ! (a_ j) [*] (poly_01 i n0) ! (a_ j)).
  Step_final ((poly_01_factor (S n0) i y0) ! (a_ j) [*][0]).
 elim (le_lt_eq_dec _ _ H); auto with arith.
 intro; elim (y b).
Qed.

Lemma poly_01_one : forall n i, (poly_01 i n) ! (a_ i) [=] [1].
Proof.
 intros.
 induction  n0 as [| n0 Hrecn0]; intros.
  simpl in |- *.
  elim (eq_nat_dec i 0); intro y.
   astepl ([1] ! (a_ i) [*][1] ! (a_ i)).
   Step_final ([1][*] ([1]:R)).
  astepl ((poly_01_factor 0 i y) ! (a_ i) [*][1] ! (a_ i)).
  astepl ((poly_01_factor 0 i y) ! (a_ i) [*][1]).
  astepl (poly_01_factor 0 i y) ! (a_ i).
  apply poly_01_factor_one.
 simpl in |- *.
 elim (eq_nat_dec i (S n0)); intro y.
  astepl ([1] ! (a_ i) [*] (poly_01 i n0) ! (a_ i)).
  astepl ([1][*] (poly_01 i n0) ! (a_ i)).
  Step_final ([1][*] ([1]:R)).
 astepl ((poly_01_factor (S n0) i y) ! (a_ i) [*] (poly_01 i n0) ! (a_ i)).
 astepl ((poly_01_factor (S n0) i y) ! (a_ i) [*][1]).
 astepl (poly_01_factor (S n0) i y) ! (a_ i).
 apply poly_01_factor_one.
Qed.

Hint Resolve poly_01_zero poly_01_one: algebra.

Lemma poly_representation'' : forall (a : nat -> R) i,
 i <= n -> (forall j, j <> i -> a j [=] [0]) -> Sum 0 n a [=] a i.
Proof.
 intro. intro.
 elim i.
  intros.
  astepl (a 0[+]Sum 1 n a).
  astepr (a 0[+][0]).
  apply bin_op_wd_unfolded.
   algebra.
  apply Sum_zero.
   auto with arith.
  intros.
  apply H0.
  intro; rewrite H3 in H1; inversion H1.
 intro i'.
 intros.
 astepl (Sum 0 i' a[+]Sum (S i') n a).
 astepr ([0][+]a (S i')).
 apply bin_op_wd_unfolded.
  apply Sum_zero.
   auto with arith.
  intros.
  apply H1.
  intro; rewrite H4 in H3; exact (le_Sn_n _ H3).
 astepl (a (S i') [+]Sum (S (S i')) n a).
 astepr (a (S i') [+][0]).
 apply bin_op_wd_unfolded.
  algebra.
 apply Sum_zero.
  auto with arith.
 intros.
 apply H1.
 intro; rewrite H4 in H2; exact (le_Sn_n _ H2).
Qed.

Lemma poly_representation' : forall (f_ : nat -> RX) k,
 k <= n -> (Sum 0 n (fun i => f_ i[*]poly_01 i n)) ! (a_ k) [=] (f_ k) ! (a_ k).
Proof.
 intros.
 apply eq_transitive_unfolded with (Sum 0 n (fun i : nat => (f_ i[*]poly_01 i n) ! (a_ k))).
  apply Sum_cpoly_ap with (f := fun i : nat => f_ i[*]poly_01 i n).
 astepl (Sum 0 n (fun i : nat => (f_ i) ! (a_ k) [*] (poly_01 i n) ! (a_ k))).
 astepr ((f_ k) ! (a_ k) [*][1]).
 astepr ((f_ k) ! (a_ k) [*] (poly_01 k n) ! (a_ k)).
 apply poly_representation'' with (a := fun i : nat => (f_ i) ! (a_ k) [*] (poly_01 i n) ! (a_ k)).
  auto.
 intros.
 Step_final ((f_ j) ! (a_ k) [*][0]).
Qed.

Lemma poly_representation : f [=] Sum 0 n (fun i => _C_ f ! (a_ i) [*]poly_01 i n).
Proof.
 apply identical_poly; auto.
  apply Sum_degree_le. auto with arith. intros.
   replace n with (0 + n).
   apply degree_le_mult.
    apply degree_le_c_.
   apply poly_01_degree.
   auto.
  auto with arith.
 intros.
 apply eq_symmetric_unfolded.
 astepr (_C_ f ! (a_ i)) ! (a_ i).
 apply poly_representation' with (f_ := fun i : nat => _C_ f ! (a_ i)).
 auto.
Qed.

Hint Resolve poly_representation: algebra.

Lemma Cpoly_choose_apzero : f [#] [0] -> {i : nat | i <= n | f ! (a_ i) [#] [0]}.
Proof.
 intros H.
 cut (Sum 0 n (fun i : nat => _C_ f ! (a_ i) [*]poly_01 i n) [#] [0]). intros H0.
  elim (Sum_apzero _ (fun i : nat => _C_ f ! (a_ i) [*]poly_01 i n) 0 n ( le_O_n n) H0).
  intro i. intro H1.
  elim H1. intros H2 H3. intro H4.
  exists i.
   auto.
  apply poly_c_apzero.
  apply cring_mult_ap_zero with (poly_01 i n).
  auto.
 astepl f. auto.
Qed.

End Poly_Representation.

Section Characteristic_zero.

(**
If we are in a field of characteristic zero, the previous result can be
strengthened.
*)

Variable R:CField.
(* begin show *)
Hypothesis H : (Char0 R).
(* end show *)
(* begin hide *)
Notation RX := (cpoly_cring R).
(* end hide *)

Lemma poly_apzero : forall f : RX, f [#] [0] -> {c : R | f ! c [#] [0]}.
Proof.
 intros f H0.
 elim (Cpoly_ex_degree _ f). intro n. intro H1. (* Set_ not necessary *)
 cut (distinct1 (fun i : nat => nring i:R)). intro H2.
  elim (Cpoly_choose_apzero _ (fun i : nat => nring i:R) H2 f n H1 H0).
  (* Set_ not necessary *)
  intro i. intros.
  exists (nring i:R).
  auto.
 unfold distinct1 in |- *.
 intros.
 apply nring_different; auto.
Qed.

(**
Also, in this situation polynomials are extensional functions.
*)

Lemma poly_extensional : forall p q : RX, (forall x, p ! x [=] q ! x) -> p [=] q.
Proof.
 intros p q H0.
 apply cg_inv_unique_2.
 apply not_ap_imp_eq. unfold Not in |- *. intros H1.
 elim (poly_apzero  (p[-]q)). intros x H2.
  cut ((p[-]q) ! x [=] [0]). intro.
   elim (eq_imp_not_ap _ _ _ H3 H2).
  astepl (p ! x[-]q ! x).
  Step_final (p ! x[-]p ! x).
 auto.
Qed.

End Characteristic_zero.

(**
** Polynomials are nonzero on any interval
*)

Section Poly_ApZero_Interval.

Variable R : COrdField.
(* begin hide *)
Notation RX := (cpoly_cring R).
(* end hide *)

Lemma Cpoly_apzero_interval : forall f : RX, f [#] [0] ->
 forall a b, a [<] b -> {c : R | a [<=] c /\ c [<=] b | f ! c [#] [0]}.
Proof.
 intros f H a b H0.
 assert (H1 := poly_degree_lth _ f).
 set (n := lth_of_poly f) in *.
 cut ([0] [<] (nring n:R)). intros H2.
  cut (nring n [#] ([0]:R)). intros H3.
   cut (distinct1 (fun i : nat => nring i[*]a[+] (nring n[-]nring i) [*]b[/] nring n[//]H3)).
    intro H4.
    elim (Cpoly_choose_apzero _ (fun i : nat => nring i[*]a[+] (nring n[-]nring i) [*]b[/] nring n[//]H3)
      H4 f n H1 H).
    intro i. intros H6 H7.
    exists (nring i[*]a[+] (nring n[-]nring i) [*]b[/] nring n[//]H3).
     split.
      apply shift_leEq_div.
       auto.
      rstepl (nring i[*]a[+] (nring n[-]nring i) [*]a).
      apply plus_resp_leEq_lft.
      apply mult_resp_leEq_lft.
       apply less_leEq. auto.
       apply shift_leEq_minus. astepl (nring (R:=R) i).
      apply nring_leEq.
      auto.
     apply shift_div_leEq.
      auto.
     rstepr (nring i[*]b[+] (nring n[-]nring i) [*]b).
     apply plus_resp_leEq.
     apply mult_resp_leEq_lft.
      apply less_leEq. auto.
      astepl (nring 0:R).
     apply nring_leEq.
     auto with arith.
    auto.
   unfold distinct1 in |- *.
   intros.
   unfold cf_div in |- *. apply mult_rht_resp_ap.
   apply zero_minus_apart.
    rstepl ((nring i[-]nring j) [*] (a[-]b)).
    apply mult_resp_ap_zero.
     apply minus_ap_zero.
     apply nring_apart. auto.
     apply minus_ap_zero.
    apply less_imp_ap.
    auto.
   apply f_rcpcl_resp_ap_zero.
  apply pos_ap_zero. auto.
  astepl (nring 0:R).
 apply nring_less.
 unfold n in |- *.
 generalize H; clear H1 H; case f.
  intro H; inversion H.
 intros; simpl in |- *.
 auto with arith.
Qed.

End Poly_ApZero_Interval.

Global Instance: forall {R: CRing} (n: nat), Proper (@st_eq _ ==> iff) (@degree_le R n).
Proof. split; apply degree_le_wd; [| symmetry]; assumption. Qed.

Section interpolation.

  Context {F: CField}.

  Definition interpolates (l: list (F * F)) (p: cpoly F): Prop :=
    forall xy, In xy l -> p ! (fst xy) [=] snd xy.

  Definition interpolates_economically (l: ne_list (F * F)) (p: cpoly F): Prop :=
    interpolates l p /\ degree_le (length (tl l)) p.

  Global Instance: Proper (@Permutation _ ==> @st_eq _ ==> iff) interpolates.
  Proof with auto.
   cut (forall x y: list (F * F), Permutation x y ->
    forall p q: cpoly F, p [=] q -> interpolates x p -> interpolates y q).
    split; apply H; auto; symmetry...
   unfold interpolates.
   intros ?? E ?? G ??.
   rewrite <- E, <- G...
  Qed.

  Global Instance: Proper (ne_list.Permutation ==> @st_eq _ ==> iff) interpolates_economically.
  Proof with auto.
   intros ?? E ?? U.
   unfold interpolates_economically.
   rewrite U.
   rewrite (ne_list.Permutation_ne_tl_length x y)...
   rewrite E.
   reflexivity.
  Qed.

  Lemma interpolation_unique (l: ne_list (F * F)): CNoDup (@cs_ap _) (map (@fst _ _) l) ->
    forall p q: cpoly F,
      interpolates_economically l p ->
      interpolates_economically l q ->
        p [=] q.
  Proof with auto with arith.
   intros ??? [A ?] [B ?].
   apply (identical_poly F (fun i => fst (nth i l ([0], [0]))) (length (tl l)))...
    repeat intro.
    rewrite <- map_nth.
    rewrite <- (map_nth (@fst _ _) l).
    simpl @fst.
    apply CNoDup_indexed...
      intros. apply ap_symmetric.
     rewrite map_length. rewrite <- ne_list.tl_length...
    rewrite map_length. rewrite <- ne_list.tl_length...
   intros.
   transitivity (snd (nth i l ([0], [0]))).
    apply A, nth_In... rewrite <- ne_list.tl_length...
   symmetry.
   apply B, nth_In... rewrite <- ne_list.tl_length...
  Qed.

End interpolation.
