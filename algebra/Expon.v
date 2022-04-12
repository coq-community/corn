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

(** printing [^^] %\ensuremath{\hat{\ }}% #^# *)

Require Export Coq.Arith.Arith.
Require Export CoRN.algebra.COrdCauchy.
From Coq Require Import Lia.

Load "Transparent_algebra".

(**
* Exponentiation
** More properties about [nexp]
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

Section More_Nexp.

Variable R : COrdField.

Lemma nexp_resp_ap_zero : forall (x : R) n, x [#] [0] -> x[^]n [#] [0].
Proof.
 intros.
 elim n.
  simpl in |- *.
  algebra.
 intros.
 simpl in |- *.
 apply mult_resp_ap_zero.
  assumption.
 assumption.
Qed.

Hint Resolve nexp_resp_ap_zero: algebra.

Lemma nexp_distr_div : forall (x y : R) n y_ yn_, (x[/] y[//]y_) [^]n [=] (x[^]n[/] y[^]n[//]yn_).
Proof.
 simple induction n.
  intros.
  simpl in |- *.
  algebra.
 intros.
 simpl in |- *.
 generalize (H y_ (nexp_resp_ap_zero y n0 y_)); intro.
 astepl ((x[^]n0[/] y[^]n0[//]nexp_resp_ap_zero y n0 y_) [*] (x[/] y[//]y_)).
 simpl in |- *.
 rational.
Qed.

Lemma nexp_distr_div' : forall (x y : R) n y_,
 (x[/] y[//]y_) [^]n [=] (x[^]n[/] y[^]n[//]nexp_resp_ap_zero y n y_).
Proof.
 intros.
 apply nexp_distr_div.
Qed.

Lemma small_nexp_resp_lt : forall (x : R) m n,
 [0] [<] x -> x [<] [1] -> m < n -> x[^]n [<] x[^]m.
Proof.
 intros.
 cut (forall k : nat, 0 < k -> x[^]k [<] [1]).
  intro H2.
  replace n with (m + (n - m)).
   astepl (x[^]m[*]x[^] (n - m)).
   astepr (x[^]m[*][1]).
   apply mult_resp_less_lft.
    apply H2.
    lia.
   apply nexp_resp_pos.
   assumption.
  auto with arith.
 simple induction k.
  intro H2.
  elimtype False.
  inversion H2.
 intros.
 elim n0.
  astepl x.
  assumption.
 intros.
 astepl (x[*]x[^]S n1).
 astepr ([1][*] ([1]:R)).
 apply mult_resp_less_both.
    apply less_leEq.
    assumption.
   assumption.
  apply less_leEq.
  apply nexp_resp_pos.
  assumption.
 assumption.
Qed.

Lemma great_nexp_resp_lt : forall (x : R) m n, [1] [<] x -> m < n -> x[^]m [<] x[^]n.
Proof.
 intros. induction  n as [| n Hrecn]; intros.
 elimtype False.
  inversion H.
 cut (m <= n). intro.
  cut (x[^]n [<] x[^]S n). intro.
   elim (le_lt_eq_dec _ _ H0); intro y.
    apply less_transitive_unfolded with (x[^]n); auto.
   rewrite y. auto.
   astepl (x[^]n[*][1]).
  astepr (x[^]n[*]x).
  apply mult_resp_less_lft. auto.
   apply nexp_resp_pos.
  apply leEq_less_trans with ([1]:R). apply less_leEq. apply pos_one. auto.
   auto with arith.
Qed.

Lemma small_nexp_resp_le : forall (x : R) m n,
 [0] [<=] x -> x [<=] [1] -> m <= n -> x[^]n [<=] x[^]m.
Proof.
 intros.
 cut (forall k : nat, x[^]k [<=] [1]).
  intro.
  replace n with (m + (n - m)).
   astepl (x[^]m[*]x[^] (n - m)).
   astepr (x[^]m[*][1]).
   apply mult_resp_leEq_lft.
    apply H2.
   apply nexp_resp_nonneg. auto.
   auto with arith.
 simple induction k.
  apply leEq_reflexive.
 clear H1 n; intros.
 astepl (x[^]n[*]x); astepr (([1]:R)[*][1]).
 apply mult_resp_leEq_both; auto.
 apply nexp_resp_nonneg; auto.
Qed.

Lemma great_nexp_resp_le : forall (x : R) m n, [1] [<=] x -> m <= n -> x[^]m [<=] x[^]n.
Proof.
 intros.
 induction  n as [| n Hrecn]; intros.
  replace m with 0.
   apply leEq_reflexive.
  auto with arith.
 elim (le_lt_eq_dec _ _ H0); intro.
  astepl (x[^]m[*][1]).
  astepr (x[^]n[*]x).
  apply mult_resp_leEq_both; auto with arith.
   apply nexp_resp_nonneg; auto.
   apply leEq_transitive with ([1]:R); auto.
   apply less_leEq. apply pos_one.
   apply less_leEq. apply pos_one.
  rewrite b. apply leEq_reflexive.
Qed.

Lemma nexp_resp_leEq : forall (x y : R) k, [0] [<=] x -> x [<=] y -> x[^]k [<=] y[^]k.
Proof.
 intros. rewrite -> leEq_def in *. intro. apply H0.
 apply power_cancel_less with k; firstorder using leEq_def.
Qed.

Lemma nexp_resp_leEq_one : forall c : R, [0] [<=] c -> c [<=] [1] -> forall n, c[^]n [<=] [1].
Proof.
 simple induction n.
  red in |- *; apply eq_imp_leEq.
  algebra.
 clear n; intros.
 astepl (c[^]n[*]c).
 astepr (([1]:R)[*][1]).
 apply mult_resp_leEq_both; auto.
 apply nexp_resp_nonneg; assumption.
Qed.

Lemma nexp_resp_leEq_neg_even : forall n, even n ->
 forall x y : R, y [<=] [0] -> x [<=] y -> y[^]n [<=] x[^]n.
Proof.
 do 2 intro; pattern n in |- *; apply even_ind.
   intros; simpl in |- *; apply leEq_reflexive.
  clear H n; intros.
  astepr (x[^]n[*]x[*]x); astepl (y[^]n[*]y[*]y).
  astepr (x[^]n[*] (x[*]x)); astepl (y[^]n[*] (y[*]y)).
  apply mult_resp_leEq_both.
     eapply leEq_wdr.
      2: apply inv_nexp_even; auto.
     apply nexp_resp_nonneg; astepl ([--] ([0]:R)); apply inv_resp_leEq; auto.
    astepr (y[^]2); apply sqr_nonneg.
   auto.
  astepl (y[^]2); astepr (x[^]2).
  eapply leEq_wdr.
   2: apply inv_nexp_even; auto with arith.
  eapply leEq_wdl.
   2: apply inv_nexp_even; auto with arith.
  apply nexp_resp_leEq.
   astepl ([--] ([0]:R)); apply inv_resp_leEq; auto.
  apply inv_resp_leEq; auto.
 auto.
Qed.

Lemma nexp_resp_leEq_neg_odd : forall n, odd n ->
 forall x y : R, y [<=] [0] -> x [<=] y -> x[^]n [<=] y[^]n.
Proof.
 intro; case n.
  intros; elimtype False; inversion H.
 clear n; intros.
 astepl (x[^]n[*]x); astepr (y[^]n[*]y).
 rstepl ([--] (x[^]n[*][--]x)); rstepr ([--] (y[^]n[*][--]y)).
 apply inv_resp_leEq; apply mult_resp_leEq_both.
    eapply leEq_wdr.
     2: apply inv_nexp_even; inversion H; auto.
    apply nexp_resp_nonneg; astepl ([--] ([0]:R)); apply inv_resp_leEq; auto.
   astepl ([--] ([0]:R)); apply inv_resp_leEq; auto.
  apply nexp_resp_leEq_neg_even; auto; inversion H; auto.
 apply inv_resp_leEq; auto.
Qed.

Lemma nexp_distr_recip : forall (x : R) n x_ xn_, ([1][/] x[//]x_) [^]n [=] ([1][/] x[^]n[//]xn_).
Proof.
 intros. induction  n as [| n Hrecn]; intros.
 simpl in |- *. algebra.
  astepl (([1][/] x[//]x_)[^]n[*] ([1][/] x[//]x_)).
 cut (x[^]n [#] [0]). intro H.
  astepl (([1][/] x[^]n[//]H)[*] ([1][/] x[//]x_)).
  cut (x[^]n[*]x [#] [0]). intro H2.
   rstepl ([1][/] x[^]n[*]x[//]H2).
   apply div_wd; algebra.
  apply mult_resp_ap_zero; auto.
 apply nexp_resp_ap_zero. auto.
Qed.

Hint Resolve nexp_distr_recip: algebra.

Lemma nexp_even_nonneg : forall n, even n -> forall x : R, [0] [<=] x[^]n.
Proof.
 do 2 intro.
 pattern n in |- *; apply even_ind; intros.
   simpl in |- *; apply less_leEq; apply pos_one.
  apply leEq_wdr with (x[^]n0[*]x[^]2).
   2: simpl in |- *; rational.
  apply mult_resp_nonneg.
   auto.
  apply sqr_nonneg.
 auto.
Qed.

Lemma nexp_resp_le' : forall c : R, [0] [<=] c -> c [<=] [1] -> forall m n, m <= n -> c[^]n [<=] c[^]m.
Proof.
 intros.
 astepl ([0][+]c[^]n); apply shift_plus_leEq.
 set (N := n - m) in *.
 apply leEq_wdr with (c[^]m[-]c[^]m[*]c[^]N).
  rstepr (c[^]m[*] ([1][-]c[^]N)).
  astepl (([0]:R)[*][0]); apply mult_resp_leEq_both; try apply leEq_reflexive.
   apply nexp_resp_nonneg; auto.
  apply shift_leEq_minus.
  astepl (c[^]N).
  apply nexp_resp_leEq_one; assumption.
 apply cg_minus_wd.
  algebra.
 eapply eq_transitive_unfolded.
  apply nexp_plus.
 replace n with (m + (n - m)).
  algebra.
 auto with arith.
Qed.

Lemma nexp_resp_le : forall c : R, [1] [<=] c -> forall m n, m <= n -> c[^]m [<=] c[^]n.
Proof.
 intros.
 cut ([0] [<] c); intros.
  2: apply less_leEq_trans with ([1]:R); [ apply pos_one | assumption ].
 cut (c [#] [0]); intros.
  2: apply Greater_imp_ap; assumption.
 cut (forall n : nat, c[^]n [#] [0]); intros H3.
  2: apply nexp_resp_ap_zero; assumption.
 cut (forall n : nat, ([1][/] _[//]H3 n) [#] [0]); intros H4.
  2: apply div_resp_ap_zero_rev; apply one_ap_zero.
 rstepl ([1][/] _[//]H4 m).
 rstepr ([1][/] _[//]H4 n).
 apply recip_resp_leEq.
  apply recip_resp_pos; apply nexp_resp_pos; assumption.
 eapply leEq_wdl.
  2: apply nexp_distr_recip with (x_ := X0).
 eapply leEq_wdr.
  2: apply nexp_distr_recip with (x_ := X0).
 apply nexp_resp_le'.
   apply less_leEq. apply recip_resp_pos; assumption.
   apply shift_div_leEq.
   assumption.
  astepr c; assumption.
 assumption.
Qed.

Lemma bin_less_un : forall n H H1, ([1][/] (Two:R) [^]S n[//]H) [<] ([1][/] nring (S n) [//]H1).
Proof.
 intros n H H1.
 apply recip_resp_less.
  simpl in |- *.
  apply plus_resp_nonneg_pos.
   apply nring_nonneg.
  apply pos_one.
 induction  n as [| n Hrecn].
  simpl in |- *.
  astepl ([1]:R).
  astepr (([1]:R)[+][1]).
   astepr (Two:R).
   apply one_less_two.
  rational.
 astepr ((Two:R)[*]Two[^]S n).
 apply leEq_less_trans with ((Two:R)[*]nring (S n)).
  apply suc_leEq_dub.
 apply mult_resp_less_lft.
  apply Hrecn.
   red; unfold f_rcpcl'.
   apply nexp_resp_ap_zero.
   apply Greater_imp_ap.
   apply pos_two.
  red; unfold f_rcpcl'.
  apply nring_ap_zero.
  auto.
 apply pos_two.
Qed.

End More_Nexp.

Hint Resolve nexp_distr_div nexp_distr_recip: algebra.

Arguments nexp_resp_ap_zero [R x].

(**
** Definition of [zexp]: integer exponentiation
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

Section Zexp_def.

Variable R : CField.

(**
It would be nicer to define [zexp] using [caseZdiff], but we already
have most properties now.
*)

Definition zexp (x : R) x_ (n : Z) : R :=
  match n with
  | Z0     => [1]:R
  | Zpos p => x[^]nat_of_P p
  | Zneg p => ([1][/] x[//]x_) [^]nat_of_P p
  end.

End Zexp_def.

Arguments zexp [R].
Notation "( x [//] Hx ) [^^] n" := (zexp x Hx n) (at level 0).

(**
** Properties of [zexp]
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

Section Zexp_properties.

Variable R : COrdField.

Lemma zexp_zero : forall (x : R) x_, (x[//]x_) [^^] (0) [=] [1].
Proof.
 intros.
 unfold zexp in |- *.
 algebra.
Qed.

Hint Resolve zexp_zero: algebra.

Lemma zexp_nexp : forall (x : R) x_ (n : nat), (x[//]x_) [^^] (n) [=] x[^]n.
Proof.
 intros.
 unfold zexp in |- *.
 simpl in |- *.
 elim n.
  simpl in |- *.
  algebra.
 intros.
 simpl in |- *.
 rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
 simpl in |- *.
 algebra.
Qed.

Hint Resolve zexp_nexp: algebra.

Lemma zexp_inv_nexp : forall (x : R) x_ (n : nat), (x[//]x_) [^^] (- n) [=] ([1][/] x[//]x_) [^]n.
Proof.
 intros.
 unfold zexp in |- *.
 simpl in |- *.
 elim n.
  simpl in |- *.
  algebra.
 intros.
 simpl in |- *.
 rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
 simpl in |- *.
 algebra.
Qed.

Hint Resolve zexp_inv_nexp: algebra.

Lemma zexp_inv_nexp' : forall (x : R) (n : nat) x_ xn_, (x[//]x_) [^^] (- n) [=] ([1][/] x[^]n[//]xn_).
Proof.
 intros x n Hx H1.
 astepl (([1][/] x[//]Hx) [^]n).
 astepr ([1][^]n[/] x[^]n[//]H1).
 apply nexp_distr_div.
Qed.

Hint Resolve zexp_inv_nexp': algebra.

Lemma zexp_strext : forall (x y : R) m x_ y_, (x[//]x_) [^^] (m) [#] (y[//]y_) [^^] (m) -> x [#] y.
Proof.
 intros x y m Hx Hy.
 pattern m in |- *.
 apply Cnats_Z_ind.
  intros.
  apply (nexp_strong_ext R n).
  change (x[^]n [#] y[^]n) in |- *.
  astepl (x[//]Hx)[^^] (n).
  astepr (y[//]Hy)[^^] (n). auto.
  intros.
 apply (nexp_strong_ext R n).
 change (x[^]n [#] y[^]n) in |- *.
 cut (([1][/] x[^]n[//]nexp_resp_ap_zero n Hx) [#] ([1][/] y[^]n[//]nexp_resp_ap_zero n Hy)).
  intro H0.
  generalize (div_strext _ _ _ _ _ _ _ H0); intro.
  elim X0; intros H2.
   elim (ap_irreflexive_unfolded _ _ H2).
  assumption.
 astepl (x[//]Hx)[^^] (- n).
 astepr (y[//]Hy)[^^] (- n). auto.
Qed.

Lemma zexp_wd : forall (x y : R) m x_ y_, x [=] y -> (x[//]x_) [^^] (m) [=] (y[//]y_) [^^] (m).
Proof.
 intros x y m Hx Hy; intros.
 apply not_ap_imp_eq.
 intro H0.
 generalize (zexp_strext _ _ _ _ _ H0); intro.
 apply (eq_imp_not_ap _ _ _ H).
 assumption.
Qed.

Hint Resolve zexp_wd: algebra_c.

Lemma zexp_plus1 : forall (x : R) x_ m, (x[//]x_) [^^] (m + 1) [=] (x[//]x_) [^^] (m) [*]x.
Proof.
 intros x Hx m.
 pattern m in |- *.
 apply nats_Z_ind.
  intro.
  replace (Z_of_nat n + 1)%Z with (S n:Z).
   astepl (x[^]S n).
   astepr (x[^]n[*]x).
   algebra.
  rewrite Znat.inj_S.
  reflexivity.
 intros.
 induction  n as [| n Hrecn].
  simpl in |- *.
  algebra.
 replace (- Z_of_nat (S n) + 1)%Z with (- n)%Z.
  astepl (([1][/] x[//]Hx) [^]n).
  astepr (([1][/] x[//]Hx) [^]S n[*]x).
  simpl in |- *.
  rational.
 rewrite Znat.inj_S.
 replace (Z.succ (Z_of_nat n)) with (1 + Z_of_nat n)%Z.
  rewrite Zopp_plus_distr.
  rewrite Zplus_comm.
  unfold Z.opp at 2 in |- *.
  rewrite Zplus_assoc.
  reflexivity.
 unfold Z.succ in |- *.
 apply Zplus_comm.
Qed.

Hint Resolve zexp_plus1: algebra.

Lemma zexp_resp_ap_zero : forall (x : R) m x_, (x[//]x_) [^^] (m) [#] [0].
Proof.
 intros.
 pattern m in |- *.
 apply Cnats_Z_ind.
  intros.
  astepl (x[^]n).
  apply nexp_resp_ap_zero.
  assumption.
 intro.
 astepl (([1][/] x[//]x_) [^]n).
 apply nexp_resp_ap_zero.
 apply div_resp_ap_zero_rev.
 algebra.
Qed.

Hint Resolve zexp_resp_ap_zero: algebra.

Lemma zexp_inv : forall (x : R) x_ m xm_, (x[//]x_) [^^] (- m) [=] ([1][/] (x[//]x_) [^^] (m) [//]xm_).
Proof.
 intros x Hx m.
 pattern m in |- *.
 apply nats_Z_ind.
  intros.
  (* Here I would like to use Rewrite zexp_inv_nexp', i.e. Rewriting with our own equality. *)
  apply eq_transitive_unfolded with ([1][/] x[^]n[//]nexp_resp_ap_zero n Hx).
   apply zexp_inv_nexp'.
  apply div_wd.
   algebra.
  algebra.
 intros.
 rewrite Z.opp_involutive.
 astepl (x[^]n).
 astepl ((x[^]n) [/]OneNZ).
 apply eq_div.
 astepl (x[^]n[*] ([1][/] x[//]Hx) [^]n).
 astepl ((x[*] ([1][/] x[//]Hx)) [^]n).
 astepr ([1]:R).
 astepr (([1]:R) [^]n).
 apply nexp_wd.
 algebra.
Qed.

Hint Resolve zexp_inv: algebra.

Lemma zexp_inv1 : forall (x : R) x_ m, (x[//]x_) [^^] (m - 1) [=] ((x[//]x_) [^^] (m) [/] x[//]x_).
Proof.
 intros x Hx; intros.
 replace (m - 1)%Z with (- (- m + 1))%Z.
  (* Here I would like to use Rewriting with our own equality. *)
  astepl ([1][/] (x[//]Hx) [^^] (- m + 1) [//]zexp_resp_ap_zero x (- m + 1) Hx).
  apply eq_div.
  astepr ((x[//]Hx) [^^] (m) [*] ((x[//]Hx) [^^] (- m) [*]x)).
  astepr ((x[//]Hx) [^^] (m) [*] (([1][/] (x[//]Hx) [^^] (m) [//]zexp_resp_ap_zero x m Hx) [*]x)).
  rational.
 rewrite Zopp_plus_distr.
 rewrite Z.opp_involutive.
 reflexivity.
Qed.

Hint Resolve zexp_inv1: algebra.

Lemma zexp_plus : forall (x : R) x_ m n, (x[//]x_) [^^] (m + n) [=] (x[//]x_) [^^] (m) [*] (x[//]x_) [^^] (n).
Proof.
 intros x Hx; intros.
 pattern n in |- *.
 apply pred_succ_Z_ind.
   simpl in |- *.
   replace (m + 0)%Z with m.
    algebra.
   auto with zarith.
  intros.
  replace (m + (n0 + 1))%Z with (m + n0 + 1)%Z.
   astepl ((x[//]Hx) [^^] (m + n0) [*]x).
   astepr ((x[//]Hx) [^^] (m) [*] ((x[//]Hx) [^^] (n0) [*]x)).
   astepr ((x[//]Hx) [^^] (m) [*] (x[//]Hx) [^^] (n0) [*]x).
   algebra.
  auto with zarith.
 intros.
 replace (m + (n0 - 1))%Z with (m + n0 - 1)%Z.
  astepl ((x[//]Hx) [^^] (m + n0) [/] x[//]Hx).
  astepr ((x[//]Hx) [^^] (m) [*] ((x[//]Hx) [^^] (n0) [/] x[//]Hx)).
  astepr ((x[//]Hx) [^^] (m) [*] (x[//]Hx) [^^] (n0) [/] x[//]Hx).
  algebra.
 unfold Zminus in |- *.
 auto with zarith.
Qed.

Hint Resolve zexp_plus: algebra.

Lemma zexp_minus : forall (x : R) x_ m n xn_,
 (x[//]x_) [^^] (m - n) [=] ((x[//]x_) [^^] (m) [/] (x[//]x_) [^^] (n) [//]xn_).
Proof.
 intros x Hx m n Hexp.
 replace (m - n)%Z with (m + - n)%Z.
  astepl ((x[//]Hx) [^^] (m) [*] (x[//]Hx) [^^] (- n)).
  astepl ((x[//]Hx) [^^] (m) [*] ([1][/] (x[//]Hx) [^^] (n) [//]Hexp)).
  astepl ((x[//]Hx) [^^] (m) [*][1][/] (x[//]Hx) [^^] (n) [//]Hexp).
  algebra.
 reflexivity.
Qed.

Hint Resolve zexp_minus: algebra.

Lemma one_zexp : forall z, ([1][//]ring_non_triv _) [^^] (z) [=] ([1]:R).
Proof.
 intro.
 pattern z in |- *.
 apply nats_Z_ind.
  intro.
  (* Rewrite would be nice *)
  astepl (([1]:R) [^]n).
  apply one_nexp.
 intros.
 astepl ([1][/] ([1][//]ring_non_triv _) [^^] (n) [//] zexp_resp_ap_zero [1] n (ring_non_triv _)).
 astepr (([1]:R) [/]OneNZ).
 apply eq_div.
 astepr (([1]:R) [*][1][^]n).
 astepr (([1]:R) [*][1]).
 algebra.
Qed.

Hint Resolve one_zexp: algebra.

Lemma mult_zexp : forall (x y : R) z x_ y_ xy_,
 (x[*]y[//]xy_) [^^] (z) [=] (x[//]x_) [^^] (z) [*] (y[//]y_) [^^] (z).
Proof.
 intros x y z Hx Hy Hp.
 pattern z in |- *.
 apply nats_Z_ind.
  intros.
  astepl ((x[*]y) [^]n).
  astepr (x[^]n[*]y[^]n).
  apply mult_nexp.
 intros.
 astepl ([1][/] (x[*]y[//]Hp) [^^] (n) [//]zexp_resp_ap_zero (x[*]y) n Hp).
 astepr (([1][/] (x[//]Hx) [^^] (n) [//]zexp_resp_ap_zero x n Hx) [*]
   ([1][/] (y[//]Hy) [^^] (n) [//]zexp_resp_ap_zero y n Hy)).
 astepl ([1][/] (x[*]y) [^]n[//]nexp_resp_ap_zero n Hp).
 astepr (([1][/] x[^]n[//]nexp_resp_ap_zero n Hx) [*] ([1][/] y[^]n[//]nexp_resp_ap_zero n Hy)).
 rstepr ([1][/] x[^]n[*]y[^]n[//]
   mult_resp_ap_zero _ _ _ (nexp_resp_ap_zero n Hx) (nexp_resp_ap_zero n Hy)).
 apply eq_div.
 algebra.
Qed.

Hint Resolve mult_zexp: algebra.

Lemma zexp_mult : forall (x : R) m n x_ xm_,
 (x[//]x_) [^^] (m * n) [=] ((x[//]x_) [^^] (m) [//]xm_) [^^] (n).
Proof.
 intros x m n Hx He.
 pattern n in |- *.
 apply pred_succ_Z_ind.
   rewrite <- Zmult_0_r_reverse.
   algebra.
  intros.
  rewrite Zmult_plus_distr_r.
  astepr (((x[//]Hx) [^^] (m) [//]He) [^^] (n0) [*] (x[//]Hx) [^^] (m)).
  rewrite Zmult_1_r.
  astepl ((x[//]Hx) [^^] (m * n0) [*] (x[//]Hx) [^^] (m)).
  algebra.
 intros.
 rewrite CornBasics.Zmult_minus_distr_r.
 astepr (((x[//]Hx) [^^] (m) [//]He) [^^] (n0) [/] (x[//]Hx) [^^] (m) [//]He).
 rewrite Zmult_1_r.
 astepl ((x[//]Hx) [^^] (m * n0) [/] (x[//]Hx) [^^] (m) [//]He).
 algebra.
Qed.

Hint Resolve zexp_mult: algebra.

Lemma zexp_two : forall (x : R) x_, (x[//]x_) [^^] (2) [=] x[*]x.
Proof.
 intros.
 simpl in |- *.
 algebra.
Qed.

Hint Resolve zexp_two: algebra.

Lemma inv_zexp_even : forall (x : R) m, Zeven m -> forall x_ x__,
 ([--]x[//]x__) [^^] (m) [=] (x[//]x_) [^^] (m).
Proof.
 intros x m H Hx Hneg.
 pattern m in |- *.
 rewrite ->  Zeven.Zeven_div2.
  astepl (([--]x[//]Hneg) [^^] (2) [//]zexp_resp_ap_zero [--]x 2 Hneg) [^^] (Z.div2 m).
  astepl ([--]x[*][--]x[//]mult_resp_ap_zero _ _ _ Hneg Hneg) [^^] (Z.div2 m).
  astepl (x[*]x[//]mult_resp_ap_zero _ _ _ Hx Hx) [^^] (Z.div2 m).
  astepl ((x[//]Hx) [^^] (2) [//]zexp_resp_ap_zero x 2 Hx) [^^] (Z.div2 m).
  algebra.
 assumption.
Qed.

Hint Resolve inv_zexp_even: algebra.

Lemma inv_zexp_two : forall (x : R) x_ x__, ([--]x[//]x__) [^^] (2) [=] (x[//]x_) [^^] (2).
Proof.
 intros.
 apply inv_zexp_even.
 simpl in |- *.
 auto.
Qed.

Hint Resolve inv_zexp_two: algebra.

Lemma inv_zexp_odd : forall (x : R) m, Zodd m -> forall x_ x__,
 ([--]x[//]x__) [^^] (m) [=] [--] (x[//]x_) [^^] (m).
Proof.
 intros x m H Hx Hneg.
 replace m with (m - 1 + 1)%Z.
  astepl (([--]x[//]Hneg) [^^] (m - 1) [*][--]x).
  astepr ([--] ((x[//]Hx) [^^] (m - 1) [*]x)).
  rstepr ((x[//]Hx) [^^] (m - 1) [*][--]x).
  apply mult_wd.
   apply inv_zexp_even.
   apply Zodd_Zeven_min1.
   assumption.
  simpl in |- *.
  auto.
  algebra.
 change ((m + -1 + 1)%Z = m) in |- *.
 rewrite <- Zplus_assoc.
 simpl in |- *.
 rewrite <- Zplus_0_r_reverse.
 reflexivity.
Qed.

Lemma zexp_one : forall (x : R) x_, (x[//]x_) [^^] (1) [=] x.
Proof.
 intros.
 simpl in |- *.
 algebra.
Qed.

Hint Resolve zexp_one: algebra.

Lemma zexp_funny : forall (x y : R) x_ y_, (x[+]y) [*] (x[-]y) [=] (x[//]x_) [^^] (2) [-] (y[//]y_) [^^] (2).
Proof.
 intros.
 astepr (x[*]x[-]y[*]y).
 rational.
Qed.

Hint Resolve zexp_funny: algebra.

Lemma zexp_funny' : forall (x y : R) x_ y_, (x[-]y) [*] (x[+]y) [=] (x[//]x_) [^^] (2) [-] (y[//]y_) [^^] (2).
Proof.
 intros.
 astepl ((x[+]y) [*] (x[-]y)).
 apply zexp_funny.
Qed.

Hint Resolve zexp_funny': algebra.

Lemma zexp_pos : forall (x : R) x_ z, [0] [<] x -> [0] [<] (x[//]x_) [^^] (z).
Proof.
 intros.
 pattern z in |- *.
 apply Cnats_Z_ind.
  intros.
  astepr (x[^]n).
  apply nexp_resp_pos.
  assumption.
 intros.
 astepr ([1][/] x[^]n[//]nexp_resp_ap_zero n x_).
 apply div_resp_pos.
  apply nexp_resp_pos.
  assumption.
 apply pos_one.
Qed.

End Zexp_properties.

Hint Resolve nexp_resp_ap_zero zexp_zero zexp_nexp zexp_inv_nexp
  zexp_inv_nexp' zexp_plus1 zexp_resp_ap_zero zexp_inv zexp_inv1 zexp_plus
  zexp_minus one_zexp mult_zexp zexp_mult zexp_two inv_zexp_even inv_zexp_two
  zexp_one zexp_funny zexp_funny': algebra.

Hint Resolve zexp_wd: algebra_c.

Section Root_Unique.

Variable R : COrdField.

Lemma root_unique : forall x y : R,
 [0] [<=] x -> [0] [<=] y -> forall n, 0 < n -> x[^]n [=] y[^]n -> x [=] y.
Proof.
 intros.
 apply leEq_imp_eq.
  apply power_cancel_leEq with n; auto.
  astepr (x[^]n).
  apply leEq_reflexive.
 apply power_cancel_leEq with n; auto.
 astepl (x[^]n).
 apply leEq_reflexive.
Qed.

Lemma root_one : forall x : R, [0] [<=] x -> forall n, 0 < n -> x[^]n [=] [1] -> x [=] [1].
Proof.
 intros.
 apply root_unique with n; auto.
  apply less_leEq. apply pos_one.
  Step_final ([1]:R).
Qed.

End Root_Unique.
