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

Require Export PowerSeries.
Require Export Taylor.

(**
* Taylor Series

We now generalize our work on Taylor's theorem to define the Taylor
series of an infinitely many times differentiable function as a power
series.  We prove convergence (always) of the Taylor series and give
criteria for when the sum of this series is the original function.

** Definitions

%\begin{convention}% Let [J] be a proper interval and [F] an
infinitely many times differentiable function in [J].  Let [a] be a
point of [J].
%\end{convention}%
*)

Section Definitions.

Variable J : interval.
Hypothesis pJ : proper J.

Variable F : PartIR.
Hypothesis diffF : forall n : nat, Diffble_n n J pJ F.

Variable a : IR.
Hypothesis Ha : J a.

Definition Taylor_Series' :=
  FPowerSeries' a (fun n : nat => N_Deriv _ _ _ _ (diffF n) a Ha).

(**
%\begin{convention}% Assume also that [f] is the sequence of
derivatives of [F].
%\end{convention}%
*)

Variable f : nat -> PartIR.
Hypothesis derF : forall n, Derivative_n n J pJ F (f n).

Definition Taylor_Series := FPowerSeries' a
 (fun n => f n a (Derivative_n_imp_inc' _ _ _ _ _ (derF n) _ Ha)).

Opaque N_Deriv.

(** Characterizations of the Taylor remainder. *)

Lemma Taylor_Rem_char : forall n H x Hx Hx' Hx'',
 F x Hx[-]FSum0 (S n) Taylor_Series x Hx' [=] Taylor_Rem J pJ F a x Ha Hx'' n H.
Proof.
 intros; unfold Taylor_Rem in |- *; repeat apply cg_minus_wd.
  algebra.
 simpl in |- *.
 apply bin_op_wd_unfolded.
  2: apply mult_wdl.
  apply eq_symmetric_unfolded.
  cut (ext_fun_seq' (fun (i : nat) (l : i < n) => [-C-] (N_Deriv _ _ _ _
    (le_imp_Diffble_n _ _ _ _ (lt_n_Sm_le _ _ (lt_S _ _ l)) _ H) a Ha[/]
      _[//]nring_fac_ap_zero _ i) {*} (FId{-} [-C-]a) {^}i)). intro H0.
   apply eq_transitive_unfolded with (Sumx (fun (i : nat) (Hi : i < n) => Part ( [-C-] (N_Deriv _ _ _ _
     (le_imp_Diffble_n _ _ _ _ (lt_n_Sm_le _ _ (lt_S _ _ Hi)) _ H) a
       Ha[/] _[//]nring_fac_ap_zero _ i) {*} (FId{-} [-C-]a) {^}i) x
         (FSumx_pred _ _ H0 _ (ProjIR1 (TaylorB _ _ _ a x Ha _ H)) i Hi))).
    exact (FSumx_char _ _ _ _ H0).
   apply Sumx_Sum0.
   intros; simpl in |- *.
   apply mult_wdl; apply div_wd.
    2: algebra.
   apply Feq_imp_eq with J; auto.
   apply Derivative_n_unique with pJ i F; auto.
   apply N_Deriv_lemma.
  red in |- *; do 3 intro.
  rewrite H0; intros; simpl in |- *; auto.
 apply div_wd.
  2: algebra.
 apply Feq_imp_eq with J; auto.
 apply Derivative_n_unique with pJ n F; auto.
 Deriv.
Qed.

Lemma abs_Taylor_Rem_char : forall n H x Hx Hx' Hx'',
 AbsIR (F x Hx[-]FSum0 (S n) Taylor_Series x Hx') [=]
   AbsIR (Taylor_Rem J pJ F a x Ha Hx'' n H).
Proof.
 intros; apply AbsIR_wd; apply Taylor_Rem_char.
Qed.

End Definitions.

Section Convergence_in_IR.

(**
** Convergence

Our interval is now the real line.  We begin by proving some helpful
continuity properties, then define a boundedness condition for the
derivatives of [F] that guarantees convergence of its Taylor series to
[F].
*)

Hypothesis H : proper realline.

Variable F : PartIR.

Variable a : IR.
Hypothesis Ha : realline a.

Variable f : nat -> PartIR.
Hypothesis derF : forall n, Derivative_n n realline H F (f n).

Lemma Taylor_Series_imp_cont : Continuous realline F.
Proof.
 apply Derivative_n_imp_Continuous with H 1 (f 1); auto.
Qed.

Lemma Taylor_Series_lemma_cont : forall r n,
 Continuous realline ((r[^]n[/] _[//]nring_fac_ap_zero _ n) {**}f n).
Proof.
 intros.
 apply Continuous_scal; case n.
  apply Continuous_wd with F.
   apply Derivative_n_unique with H 0 F; auto.
   apply Derivative_n_O.
   apply Derivative_n_imp_inc with H n (f n); auto.
  apply Taylor_Series_imp_cont.
 clear n; intros.
 apply Derivative_n_imp_Continuous' with H (S n) F; auto with arith.
Qed.

Definition Taylor_bnd := forall r H, conv_fun_seq'_IR realline
  (fun n => (r[^]n[/] _[//]nring_fac_ap_zero _ n) {**}f n) _ H (Continuous_const _ Zero).

(* begin show *)
Hypothesis bndf : Taylor_bnd.
(* end show *)

Opaque nexp_op fac.

(* begin hide *)
Let H1 : forall n, Two[^]n [#] ZeroR.
Proof.
 intro; apply nexp_resp_ap_zero; apply two_ap_zero.
Qed.

Lemma Taylor_Series_conv_lemma1 :
  forall t x y Hxy (e : IR) (He : Zero [<] e),
  {N : nat |
  forall n : nat,
  N <= n ->
  forall w z : IR,
  compact x y Hxy z ->
  Compact (Min_leEq_Max' x y t) w ->
  forall Hw Hz,
  AbsIR
    (((Part _ _ (Derivative_n_imp_inc' _ _ _ _ _ (derF (S n)) w Hw) [/] _[//]
       nring_fac_ap_zero _ (S n)) {**} ((FId{-} [-C-]w) {^}n{*} (FId{-} [-C-]a))) z
       Hz) [<=] (e[/] _[//]H1 (S n))}.
Proof.
 intros.
 set (r := Max y (Max a t) [-]Min x (Min a t)) in *.
 cut (Min x (Min a t) [<=] Max y (Max a t)).
  intro Hxy'; cut (included (Compact (Min_leEq_Max' x y t)) (Compact Hxy')).
   intro Hinc'.
   cut (forall w z : IR, Compact Hxy z -> Compact Hxy' w -> AbsIR (z[+][--]w) [<=] r). intro.
    2: intros w z H0 H2; fold (z[-]w) in |- *; unfold r in |- *.
    set (r' := Two[*]Max r One) in *.
    set (H' := Taylor_Series_lemma_cont r') in *.
    elim (bndf r' H' _ _ (Min_leEq_Max' x y t) (included_interval' realline _ _ _ _ I I I I _) e He);
      intros N HN.
    exists N. intros n H2 w z H3 H4 Hw Hz.
    simpl in |- *; fold (Two:IR) in |- *.
    assert (H5 : forall n : nat, Zero [<] r'[^]n).
     intro; unfold r' in |- *; apply nexp_resp_pos; unfold r' in |- *;
       apply mult_resp_pos; [ apply pos_two | apply pos_max_one ].
    apply leEq_transitive with ((e[/] _[//]pos_ap_zero _ _ (H5 (S n))) [*]
      AbsIR ((z[+][--]w) [^]n[*] (z[+][--]a))).
     eapply leEq_wdl.
      2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
     apply mult_resp_leEq_rht.
      2: apply AbsIR_nonneg.
     apply shift_leEq_div.
      auto.
     clear Hz H3 z.
     eapply leEq_transitive.
      2: apply (HN (S n) (le_S _ _ H2) w H4).
     simpl in |- *.
     cut (forall z : IR, AbsIR z [=] AbsIR (z[-]Zero)); intros.
      2: apply AbsIR_wd; algebra.
     eapply leEq_wdr.
      2: apply H3.
     clear H3; eapply leEq_wdr.
      2: apply eq_symmetric_unfolded; apply AbsIR_mult_pos'.
      eapply leEq_wdr.
       2: apply mult_commutes.
      cut (forall z : IR, AbsIR (z[/] _[//]nring_fac_ap_zero _ (S n)) [*]r'[^]S n [=]
        AbsIR z[*] (r'[^]S n[/] _[//]nring_fac_ap_zero _ (S n))); intros.
       eapply leEq_wdr.
        2: apply H3.
       clear H3; apply mult_resp_leEq_rht.
        apply eq_imp_leEq; apply AbsIR_wd; algebra.
       apply less_leEq; auto.
      rstepr ((AbsIR z[/] _[//]nring_fac_ap_zero _ (S n)) [*]r'[^]S n).
      apply mult_wdl.
      eapply eq_transitive_unfolded.
       apply AbsIR_division with (y__ := AbsIR_resp_ap_zero _ (nring_fac_ap_zero _ (S n))).
      apply div_wd.
       algebra.
      apply AbsIR_eq_x.
      apply nring_nonneg.
     apply less_leEq; apply div_resp_pos; [ apply pos_nring_fac | auto ].
    Transparent nexp_op.
    apply shift_leEq_div.
     apply nexp_resp_pos; apply pos_two.
    unfold r' in |- *.
    apply leEq_wdl with (e[*] (AbsIR ((z[+][--]w) [^]n[*] (z[+][--]a)) [/] _[//]
      nexp_resp_ap_zero (S n) (max_one_ap_zero r))).
     astepr (e[*]One).
     apply mult_resp_leEq_lft.
      2: apply less_leEq; auto.
     apply shift_div_leEq.
      apply nexp_resp_pos; apply pos_max_one.
     astepr (Max r One[^]S n).
     eapply leEq_wdl.
      2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
     astepr (Max r One[^]n[*]Max r One).
     apply mult_resp_leEq_both; try apply AbsIR_nonneg.
      eapply leEq_wdl.
       2: apply eq_symmetric_unfolded; apply AbsIR_nexp_op.
      apply nexp_resp_leEq.
       apply AbsIR_nonneg.
      apply leEq_transitive with r; auto.
      apply lft_leEq_Max.
     apply leEq_transitive with r.
      apply H0; auto.
      split.
       eapply leEq_transitive.
        apply Min_leEq_rht.
       apply Min_leEq_lft.
      eapply leEq_transitive.
       2: apply rht_leEq_Max.
      apply lft_leEq_Max.
     apply lft_leEq_Max.
    rstepl ((e[/] _[//] mult_resp_ap_zero _ _ _ (nexp_resp_ap_zero (S n) (max_one_ap_zero r))
      (H1 (S n))) [*]AbsIR ((z[+][--]w) [^]n[*] (z[+][--]a)) [*] Two[^]S n).
    repeat apply mult_wdl.
    apply div_wd; algebra.
    eapply eq_transitive_unfolded.
     2: apply eq_symmetric_unfolded; apply mult_nexp.
    algebra.
   apply leEq_wdr with (AbsIR (Max y (Max a t) [-]Min x (Min a t))).
    apply compact_elements with Hxy'; auto.
    inversion_clear H0; split.
     apply leEq_transitive with x; auto; apply Min_leEq_lft.
    apply leEq_transitive with y; auto; apply lft_leEq_Max.
   apply AbsIR_eq_x.
   apply shift_leEq_minus; astepl (Min x (Min a t)); auto.
  red in |- *; intros z Hz.
  inversion_clear Hz; split.
   eapply leEq_transitive.
    2: apply H0.
   apply leEq_Min.
    apply Min_leEq_lft.
   eapply leEq_transitive; apply Min_leEq_rht.
  eapply leEq_transitive.
   apply H2.
  apply Max_leEq.
   apply lft_leEq_Max.
  eapply leEq_transitive.
   2: apply rht_leEq_Max.
  apply rht_leEq_Max.
 apply leEq_transitive with t.
  eapply leEq_transitive; apply Min_leEq_rht.
 eapply leEq_transitive.
  2: apply rht_leEq_Max.
 apply rht_leEq_Max.
Qed.

Lemma Taylor_Series_conv_lemma2 :
  forall x y Hxy (e : IR) (He : Zero [<] e),
  {N : nat |
  forall n : nat,
  N <= n ->
  forall z : IR,
  compact x y Hxy z ->
  forall Hz,
  AbsIR (Taylor_Series _ _ _ a Ha _ derF n z Hz) [<=] (e[/] _[//]H1 n)}.
Proof.
 intros.
 elim Taylor_Series_conv_lemma1 with (t := a) (Hxy := Hxy) (e := e); auto.
 intros N HN; exists (S N).
 intros n H0 z H2 Hz.
 assert (n = S (pred n)). apply S_pred with N; auto with arith.
  set (p := pred n) in *.
 assert (N <= p). unfold p in |- *; apply le_S_n; rewrite <- S_pred with n N; auto with arith.
  clearbody p; rewrite H3.
 assert (H5 : forall c d : IR, Dom (c{**} ((FId{-} [-C-]d) {^}p{*} (FId{-} [-C-]a))) z).
  repeat split.
 assert (H6 : Compact (Min_leEq_Max' x y a) a).
  split; [ apply Min_leEq_rht | apply rht_leEq_Max ].
 eapply leEq_wdl.
  apply (HN p H4 a z H2 H6 Ha (H5
    (Part _ _ (Derivative_n_imp_inc' _ _ _ _ _ (derF (S p)) a Ha) [/] _[//]
      nring_fac_ap_zero _ (S p)) a)).
 apply AbsIR_wd; algebra.
Qed.
(* end hide *)

(** The Taylor series always converges on the realline. *)

Lemma Taylor_Series_conv_IR :
 fun_series_convergent_IR realline (Taylor_Series _ _ _ a Ha _ derF).
Proof.
 red in |- *; intros.
 unfold Taylor_Series, FPowerSeries' in |- *.
 apply fun_str_comparison with (fun n : nat => Fconst (S:=IR) ((One [/]TwoNZ) [^]n)).
   Contin.
  apply conv_fun_const_series with (x := fun n : nat => (OneR [/]TwoNZ) [^]n).
  apply ratio_test_conv.
  exists 0; exists (OneR [/]TwoNZ); repeat split.
    apply pos_div_two'; apply pos_one.
   apply less_leEq; fold (Half:IR) in |- *; apply pos_half.
  intros; apply eq_imp_leEq.
  eapply eq_transitive_unfolded.
   2: apply mult_commutes.
  eapply eq_transitive_unfolded.
   2: apply AbsIR_mult_pos; apply less_leEq; fold (Half (R:=IR)) in |- *; apply pos_half.
  Transparent nexp_op.
  apply AbsIR_wd; simpl in |- *; rational.
 Opaque nexp_op.
 elim (Taylor_Series_conv_lemma2 _ _ Hab One (pos_one _)); intros N HN;
   exists N; intros n H0 x X Hx Hx'.
 eapply leEq_wdr.
  eapply leEq_wdl.
   apply (HN _ H0 _ X Hx).
  apply AbsIR_wd; algebra.
 simpl in |- *; algebra.
Qed.

(* begin hide *)
Lemma Taylor_majoration_lemma :
  forall (n : nat) (e : IR), Zero [<] e -> e[*] (nring n[/] _[//]H1 n) [<=] e.
Proof.
 intro; case n.
  intros; simpl in |- *; rstepl ZeroR; apply less_leEq; auto.
 clear n; intro; induction  n as [| n Hrecn].
  intros; simpl in |- *.
  eapply leEq_wdl.
   apply less_leEq; apply pos_div_two'; auto.
  rational.
 intros e H0.
 eapply leEq_transitive.
  2: apply Hrecn; auto.
 apply mult_resp_leEq_lft.
  2: apply less_leEq; auto.
 apply shift_div_leEq.
  repeat apply mult_resp_pos; try apply nexp_resp_pos; apply pos_two.
 rstepr (nring (S n) [*]Two[^]S (S n) [/] _[//]H1 (S n)).
 apply shift_leEq_div.
  apply nexp_resp_pos; apply pos_two.
 Transparent nexp_op.
 set (p := S n) in *.
 cut (p = S n); [ intro | auto ].
 clear H0; clearbody p.
 simpl in |- *; fold (Two:IR) in |- *.
 rstepl (nring (R:=IR) p[*]nexp _ p Two[+]nring 1[*]nexp _ p Two).
 rstepr (nring (R:=IR) p[*]nexp _ p Two[+]nring p[*]nexp _ p Two).
 apply plus_resp_leEq_lft.
 apply mult_resp_leEq_rht.
  apply nring_leEq; rewrite H2; auto with arith.
 astepr ((Two:IR) [^]p); apply nexp_resp_nonneg.
 apply less_leEq; apply pos_two.
Qed.

Opaque N_Deriv fac.

Lemma Taylor_Series_conv_lemma3 :
  forall a' b d c e a'' x : IR,
  a' [=] a'' ->
  x [=] b[*]e ->
  Zero [<=] e ->
  forall Hb He Hx,
  (AbsIR (a'[*] (One[/] b[//]Hb) [*]c[*]d) [/] e[//]He) [=]
  AbsIR ((a''[/] x[//]Hx) [*] (c[*]d)).
Proof.
 intros.
 astepr (AbsIR ((a''[/] x[//]Hx) [*]c[*]d)).
 apply eq_transitive_unfolded with
   (AbsIR a'[*] (One[/] _[//]AbsIR_resp_ap_zero _ Hb) [*]AbsIR c[*]AbsIR d[/] e[//]He).
  apply div_wd; algebra.
  repeat (eapply eq_transitive_unfolded; [ apply AbsIR_resp_mult | apply mult_wdl ]).
  eapply eq_transitive_unfolded; [ apply AbsIR_resp_mult | apply mult_wdr ].
  apply AbsIR_recip.
 rstepl ((AbsIR a'[/] _[//]mult_resp_ap_zero _ _ _ (AbsIR_resp_ap_zero _ Hb) He) [*]
   AbsIR c[*]AbsIR d).
 apply eq_symmetric_unfolded.
 repeat (eapply eq_transitive_unfolded; [ apply AbsIR_resp_mult | apply mult_wdl ]).
 eapply eq_transitive_unfolded; [ apply AbsIR_division with (y__ := AbsIR_resp_ap_zero _ Hx)
   | apply div_wd; algebra ].
 eapply eq_transitive_unfolded.
  2: apply AbsIR_mult_pos; auto.
 algebra.
Qed.
(* end hide *)

(**
We now prove that, under our assumptions, it actually converges to the
original function.  For generality and also usability, however, we
will separately assume convergence.
*)

(* begin show *)
Hypothesis Hf : fun_series_convergent_IR realline (Taylor_Series _ _ _ a Ha _ derF).
(* end show *)

Lemma Taylor_Series_conv_to_fun : Feq realline F (FSeries_Sum Hf).
Proof.
 cut (Continuous realline (FSeries_Sum Hf)). intro H0.
  cut (forall n : nat, Continuous realline (FSum0 n (Taylor_Series _ _ _ _ Ha _ derF))).
   intro H2.
   cut (Continuous realline F). intro H3.
    eapply FLim_unique_IR with (HG := H0) (HF := H3)
      (f := fun n : nat => FSum0 n (Taylor_Series _ _ _ _ Ha _ derF)) (contf := H2).
     2: apply FSeries_conv.
    3: Contin.
   2: apply Derivative_imp_Continuous with H (f 1).
   2: apply Derivative_n_Sn with F 0.
    2: apply Derivative_n_O; eapply Derivative_n_imp_inc; apply (derF 0).
   2: auto.
  2: unfold Taylor_Series in |- *; Contin.
 intros a0 b Hab Hinc e H4.
 set (Hab' := Min_leEq_Max' a0 b a) in *.
 elim (Taylor_Series_conv_lemma1 a _ _ Hab _ (pos_div_two _ _ H4)); intros N HN.
 exists (S N); intros p Hp.
 cut (p = S (pred p)); [ intro Hn | apply S_pred with N; auto ].
 set (n := pred p) in *; clearbody n.
 generalize Hp; clear Hp; rewrite Hn; clear Hn p.
 intros.
 cut (Zero [<] nring (S n) [*]e [/]TwoNZ); [ intro He | apply mult_resp_pos ].
   2: apply pos_nring_S.
  2: apply pos_div_two; auto.
 elim (Taylor' _ _ _ _ _ Ha (Hinc x Hx) n (Derivative_n_imp_Diffble_n _ _ _ _ _ (derF (S n)))
   (Derivative_n_imp_Diffble_n _ _ _ _ _ (derF n)) _ ( pos_div_two _ _ H4)).
 intros y H5 H6.
 set (H7 := pair (I, I) (I, I) :Dom
   (N_Deriv _ _ _ _ (Derivative_n_imp_Diffble_n _ _ _ _ _ (derF (S n))) {*}
     [-C-] (One[/] _[//]nring_fac_ap_zero _ n) {*} ( [-C-]x{-}FId) {^}n) y) in *.
 eapply leEq_wdl.
  2: apply AbsIR_minus.
 cut (forall z w : IR, AbsIR z [<=] AbsIR (z[-]w) [+]AbsIR w); intros.
  2: eapply leEq_wdl.
   2: apply triangle_IR.
  2: apply AbsIR_wd; rational.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply (abs_Taylor_Rem_char realline H F a Ha f derF n
    (Derivative_n_imp_Diffble_n _ _ _ _ _ (derF n)) x
      (contin_imp_inc _ _ _ _ (included_imp_Continuous _ _ H3 _ _ _ Hinc) _ Hx) (contin_imp_inc _ _ _ _
        (included_imp_Continuous _ _ (H2 (S n)) _ _ _ Hinc) _ Hx) (Hinc _ Hx)).
 rstepr (e [/]TwoNZ[+]e [/]TwoNZ).
 eapply leEq_transitive.
  apply H8 with (w := Part (N_Deriv _ _ _ _ (Derivative_n_imp_Diffble_n _ _ _ _ _ (derF (S n))) {*}
    [-C-] (One[/] _[//]nring_fac_ap_zero _ n) {*} ( [-C-]x{-}FId) {^}n) y H7[*] (x[-]a)).
 apply plus_resp_leEq_both; auto.
 eapply leEq_transitive.
  2: apply Taylor_majoration_lemma with (n := S n); apply pos_div_two; auto.
 rstepr (nring (S n) [*] (e [/]TwoNZ[/] _[//]H1 (S n))).
 apply shift_leEq_mult' with (pos_ap_zero _ _ (pos_nring_S IR n)).
  apply pos_nring_S.
 set (H9 := pair I (pair (I, I) (I, I))) in *.
 eapply leEq_wdl.
  apply HN with (n := n) (w := y) (z := x) (Hw := I) (Hz := H9); auto with arith.
  inversion_clear Hx; inversion_clear H5; split.
   apply leEq_transitive with (Min a x); auto.
   apply leEq_Min.
    apply Min_leEq_rht.
   apply leEq_transitive with a0; auto.
   apply Min_leEq_lft.
  apply leEq_transitive with (Max a x); auto.
  apply Max_leEq.
   apply rht_leEq_Max.
  apply leEq_transitive with b; auto.
  apply lft_leEq_Max.
 simpl in |- *.
 unfold Taylor_Rem in |- *; simpl in |- *.
 clear H8 H6 H4 He Hx Hp HN Hab' H3 H2 H0 bndf.
 set (fy := Part _ _ (Derivative_n_imp_inc' _ _ _ _ _ (derF (S n)) y I)) in *.
 set (Fy := Part (N_Deriv _ _ _ _ (Derivative_n_imp_Diffble_n _ _ _ _ _ (derF (S n))))
   y (ProjIR1 (ProjIR1 H7))) in *.
 astepr (AbsIR (Fy[*] (One[/] _[//]nring_fac_ap_zero _ n) [*] (x[+][--]y) [^]n[*] (x[-]a)) [/]
   _[//]pos_ap_zero _ _ (pos_nring_S _ n)).
 unfold cg_minus in |- *.
 apply eq_symmetric_unfolded; apply Taylor_Series_conv_lemma3.
   unfold fy, Fy in |- *.
   apply Feq_imp_eq with realline; auto.
   apply Derivative_n_unique with H (S n) F; Deriv.
  eapply eq_transitive_unfolded.
   2: apply nring_comm_mult.
  Transparent fac.
  replace (fac (S n)) with (fac n * S n).
   algebra.
  Opaque mult.
  unfold fac in |- *; fold (fac n) in |- *.
  auto with arith.
 apply nring_nonneg.
Qed.

End Convergence_in_IR.

Section Other_Results.

(**
The condition for the previous lemma is not very easy to prove.  We
give some helpful lemmas.
*)

Lemma Taylor_bnd_trans : forall f g : nat -> PartIR,
 (forall n x Hx Hx', AbsIR (f n x Hx) [<=] AbsIR (g n x Hx')) ->
 (forall n, Continuous realline (g n)) -> Taylor_bnd g -> Taylor_bnd f.
Proof.
 intros f g bndf contg Gbnd r H a b Hab Hinc e H0.
 elim (Gbnd r (fun n : nat => Continuous_scal _ _ (contg n) _) _ _ _ Hinc e H0); intros N HN.
 exists N; intros.
 eapply leEq_transitive.
  2: apply HN with (n := n) (Hx := Hx); auto.
 cut (forall (z t : IR) Ht, AbsIR z [=] AbsIR (z[-][-C-]Zero t Ht)); intros.
  2: simpl in |- *; apply AbsIR_wd; algebra.
 eapply leEq_wdl.
  2: apply H2.
 eapply leEq_wdr.
  2: apply H2.
 simpl in |- *.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
 eapply leEq_wdr.
  2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
 apply mult_resp_leEq_lft; auto.
 apply AbsIR_nonneg.
Qed.

(* begin hide *)
Lemma convergence_lemma :
  forall r : IR,
  conv_fun_seq'_IR realline
    (fun n : nat => [-C-] (r[^]n[/] _[//]nring_fac_ap_zero IR n))
    [-C-]Zero (fun n : nat => Continuous_const realline _)
    (Continuous_const realline _).
Proof.
 red in |- *; intros.
 apply seq_conv_imp_fun_conv with (x := fun n : nat => r[^]n[/] _[//]nring_fac_ap_zero _ n).
 clear Hinc Hab b a.
 apply series_seq_Lim.
 assert (H : forall n : nat, Dom (Exp_ps n) r). repeat split.
  apply convergent_wd with (fun n : nat => Part (Exp_ps n) r (H n)).
  Opaque nexp_op.
  intros; simpl in |- *.
  rstepl ((r[-]Zero) [^]n[/] _[//]nring_fac_ap_zero _ n).
  algebra.
 apply fun_series_conv_imp_conv_IR with realline.
  apply Exp_conv.
 split.
Qed.
(* end hide *)

Lemma bnd_imp_Taylor_bnd : forall (f : nat -> PartIR) (F : PartIR),
 (forall n x Hx Hx', AbsIR (f n x Hx) [<=] AbsIR (F x Hx')) -> Continuous realline F ->
 (forall n, included (fun _ => True) (Dom (f n))) -> Taylor_bnd f.
Proof.
 intros f F H H0 H1.
 apply Taylor_bnd_trans with (fun n : nat => F); auto.
 red in |- *; intros.
 unfold Fscalmult in |- *.
 apply conv_fun_seq'_wdr'_IR with (contF := Continuous_mult _ _ _ (Continuous_const _ Zero) H0).
  FEQ.
 apply fun_Lim_seq_mult'_IR with (f := fun n : nat => [-C-] (r[^]n[/] _[//]nring_fac_ap_zero _ n))
   (contf := fun n : nat => Continuous_const realline (r[^]n[/] _[//]nring_fac_ap_zero _ n))
     (g := fun n : nat => F) (contg := fun n : nat => H0) (contF := Continuous_const realline Zero)
       (contG := H0).
  apply convergence_lemma.
 apply fun_Lim_seq_const_IR.
Qed.

(**
Finally, a uniqueness criterium: two functions [F] and [G] are equal,
provided that their derivatives coincide at a given point and their
Taylor series converge to themselves.
*)

Variables F G : PartIR.

Variable a : IR.

Variables f g : nat -> PartIR.
Hypothesis derF : forall n, Derivative_n n realline I F (f n).
Hypothesis derG : forall n, Derivative_n n realline I G (g n).

Hypothesis bndf : Taylor_bnd f.
Hypothesis bndg : Taylor_bnd g.

(* begin show *)
Hypothesis Heq : forall n HaF HaG, f n a HaF [=] g n a HaG.
(* end show *)

(* begin hide *)
Let Hf := Taylor_Series_conv_IR I F a I f derF bndf.
(* end hide *)

Lemma Taylor_unique_crit : Feq realline F (FSeries_Sum Hf) -> Feq realline F G.
Proof.
 intro H.
 cut (fun_series_convergent_IR realline (Taylor_Series realline I G a I g derG)).
  intro Hg.
  apply Feq_transitive with (FSeries_Sum Hf); auto.
  apply Feq_transitive with (FSeries_Sum Hg).
   apply eq_imp_Feq; simpl in |- *; Included.
   intros; apply series_sum_wd.
   intros; algebra.
  apply Feq_symmetric; apply Taylor_Series_conv_to_fun; auto.
 apply Taylor_Series_conv_IR; auto.
Qed.

End Other_Results.
