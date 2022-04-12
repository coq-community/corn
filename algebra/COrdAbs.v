(* Copyright © 1998-2008
 * Henk Barendregt
 * Luís Cruz-Filipe
 * Herman Geuvers
 * Mariusz Giero
 * Rik van Ginneken
 * Dimitri Hendriks
 * Sébastien Hinderer
 * Cezary Kaliszyk
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
Require Export CoRN.algebra.COrdFields2.

(**
** Properties of [AbsSmall]
*)

(* Begin_SpecReals *)

Definition AbsSmall (R : COrdField) (e x : R) : Prop := [--]e [<=] x /\ x [<=] e.

Arguments AbsSmall [R].

(* End_SpecReals *)

Section AbsSmall_properties.

(**
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)
Variable R : COrdField.

Lemma AbsSmall_wdr : rel_wdr R (AbsSmall (R:=R)).
Proof.
 unfold rel_wdr in |- *.
 unfold AbsSmall in |- *.
 intros.
 elim H; intros.
 split.
  astepr y.
  assumption.
 astepl y.
 assumption.
Qed.

Lemma AbsSmall_wdr_unfolded : forall x y z : R,
 AbsSmall x y -> y [=] z -> AbsSmall x z.
Proof AbsSmall_wdr.

Lemma AbsSmall_wdl : rel_wdl R (AbsSmall (R:=R)).
Proof.
 unfold rel_wdl in |- *.
 unfold AbsSmall in |- *.
 intros.
 elim H; intros.
 split.
  astepl ([--]x).
  assumption.
 astepr x.
 assumption.
Qed.

Lemma AbsSmall_wdl_unfolded : forall x y z : R,
 AbsSmall x y -> x [=] z -> AbsSmall z y.
Proof AbsSmall_wdl.

Declare Left Step AbsSmall_wdl_unfolded.
Declare Right Step AbsSmall_wdr_unfolded.

(* begin hide *)
Notation ZeroR := ([0]:R).
(* end hide *)

Lemma AbsSmall_leEq_trans : forall e1 e2 d : R,
 e1 [<=] e2 -> AbsSmall e1 d -> AbsSmall e2 d.
Proof.
 unfold AbsSmall in |- *.
 intros.
 elim H0; intros.
 split.
  apply leEq_transitive with ([--]e1).
   apply inv_resp_leEq.
   assumption.
  assumption.
 apply leEq_transitive with e1.
  assumption.
 assumption.
Qed.

Lemma zero_AbsSmall : forall e : R, [0] [<=] e -> AbsSmall e [0].
Proof.
 intros.
 unfold AbsSmall in |- *.
 split.
  astepr ([--]ZeroR).
  apply inv_resp_leEq.
  assumption.
 assumption.
Qed.

Lemma AbsSmall_reflexive : forall (e : R), [0] [<=] e -> AbsSmall e e.
Proof.
 intros.
 unfold AbsSmall.
 split.
  apply leEq_transitive with ([0]:R); auto.
  astepr ([--][0]:R).
  apply inv_resp_leEq.
  auto.
 apply leEq_reflexive.
Qed.

Lemma AbsSmall_trans : forall e1 e2 d : R,
 e1 [<] e2 -> AbsSmall e1 d -> AbsSmall e2 d.
Proof.
 intros.
 apply AbsSmall_leEq_trans with e1.
  apply less_leEq.
  assumption.
 assumption.
Qed.

Lemma leEq_imp_AbsSmall : forall e d : R, [0] [<=] e -> e [<=] d -> AbsSmall d e.
Proof.
 intros.
 unfold AbsSmall in |- *.
 split; try assumption.
 apply leEq_transitive with ZeroR; try assumption.
 astepr ([--]ZeroR).
 apply inv_resp_leEq.
 apply leEq_transitive with e; assumption.
Qed.

Lemma inv_resp_AbsSmall : forall x y : R, AbsSmall x y -> AbsSmall x [--]y.
Proof.
 unfold AbsSmall in |- *.
 intros.
 elim H; intros.
 split.
  apply inv_resp_leEq.
  assumption.
 astepr ([--][--]x).
 apply inv_resp_leEq.
 assumption.
Qed.

Lemma mult_resp_AbsSmall: forall (R: COrdField) (x y e : R) (H: [0][<=]y),
AbsSmall e x -> AbsSmall (y[*]e) (y[*]x).
Proof.
 unfold AbsSmall.
 intros.
 destruct H0.
 split.
  rstepl (y[*]([--]e)).
  apply mult_resp_leEq_lft; auto.
 apply mult_resp_leEq_lft; auto.
Qed.

Lemma div_resp_AbsSmall: forall (R: COrdField) (x y e : R) (H: [0][<]y),
AbsSmall e x -> AbsSmall (e[/]y[//]pos_ap_zero _ _ H) (x[/]y[//]pos_ap_zero _ _ H).
Proof.
 unfold AbsSmall.
 intros.
 destruct H0.
 split.
  rstepl (([--]e)[/]y[//]pos_ap_zero _ _ H).
  apply div_resp_leEq; auto.
 apply div_resp_leEq; auto.
Qed.

Lemma sum_resp_AbsSmall : forall
(x y : nat -> R) (n m: nat)
(H1 : m <= n) (H2 : forall i : nat, m <= i -> i <= n ->  AbsSmall (y i) (x i)),
AbsSmall (Sum m n y) (Sum m n x).
Proof.
 unfold AbsSmall.
 intros.
 assert (H3 : forall i : nat, m <= i -> i <= n ->  [--](y i)[<=]x i).
  intros.
  elim (H2 i H H0). auto.
  assert (H4 : forall i : nat, m <= i -> i <= n ->  x i[<=]y i).
  intros.
  elim (H2 i H H0). auto.
  split.
  astepl (Sum m n (fun k: nat => [--](y k))).
  apply Sum_resp_leEq .
   auto with arith. intros. auto.
  apply Sum_resp_leEq .
  auto with arith. intros. auto.
Qed.


Lemma AbsSmall_minus : forall e x1 x2 : R, AbsSmall e (x1[-]x2) -> AbsSmall e (x2[-]x1).
Proof.
 intros.
 rstepr ([--](x1[-]x2)).
 apply inv_resp_AbsSmall.
 assumption.
Qed.

Lemma AbsSmall_plus : forall e1 e2 x1 x2 : R,
 AbsSmall e1 x1 -> AbsSmall e2 x2 -> AbsSmall (e1[+]e2) (x1[+]x2).
Proof.
 unfold AbsSmall in |- *.
 intros.
 elim H; intros.
 elim H0; intros.
 split.
  rstepl ([--]e1[+][--]e2).
  apply plus_resp_leEq_both; assumption.
 apply plus_resp_leEq_both; assumption.
Qed.

Lemma AbsSmall_eps_div_two : forall e x1 x2 : R,
 AbsSmall (e [/]TwoNZ) x1 -> AbsSmall (e [/]TwoNZ) x2 -> AbsSmall e (x1[+]x2).
Proof.
 intros.
 rstepl (e [/]TwoNZ[+]e [/]TwoNZ).
 apply AbsSmall_plus.
  assumption.
 assumption.
Qed.

Lemma AbsSmall_x_plus_delta : forall x eps delta : R,
 [0] [<=] eps -> [0] [<=] delta -> delta [<=] eps -> AbsSmall eps (x[-] (x[+]delta)).
Proof.
 intros.
 (* astepr ((x[-]x)[-]delta).
 astepr ([0][-]delta). *)
 rstepr ([--]delta).
 apply inv_resp_AbsSmall.
 apply leEq_imp_AbsSmall.
  assumption.
 assumption.
Qed.

Lemma AbsSmall_x_minus_delta : forall x eps delta : R,
 [0] [<=] eps -> [0] [<=] delta -> delta [<=] eps -> AbsSmall eps (x[-] (x[-]delta)).
Proof.
 intros.
 (* astepr ((x[-]x)[+]delta).
 astepr ([0][+]delta). *)
 rstepr delta.
 apply leEq_imp_AbsSmall.
  assumption.
 assumption.
Qed.

Lemma AbsSmall_x_plus_eps_div2 : forall x eps : R, [0] [<=] eps -> AbsSmall eps (x[-] (x[+]eps [/]TwoNZ)).
Proof.
 intros.
 apply AbsSmall_x_plus_delta.
   assumption.
  apply nonneg_div_two.
  assumption.
 apply nonneg_div_two'.
 assumption.
Qed.

Lemma AbsSmall_x_minus_eps_div2 : forall x eps : R, [0] [<=] eps -> AbsSmall eps (x[-] (x[-]eps [/]TwoNZ)).
Proof.
 intros.
 apply AbsSmall_x_minus_delta.
   assumption.
  apply nonneg_div_two.
  assumption.
 apply eps_div_leEq_eps.
  assumption.
 apply less_leEq.
 apply one_less_two.
Qed.

Lemma AbsSmall_intermediate : forall x y z eps : R,
 x [<=] y -> y [<=] z -> AbsSmall eps (z[-]x) -> AbsSmall eps (z[-]y).
Proof.
 intros.
 apply leEq_imp_AbsSmall.
  apply shift_leEq_minus; astepl y.
  assumption.
 unfold AbsSmall in H1.
 elim H1; intros.
 apply leEq_transitive with (z[-]x); try assumption.
 apply minus_resp_leEq_rht.
 assumption.
Qed.

Lemma AbsSmall_eps_div2 : forall eps : R, [0] [<=] eps -> AbsSmall eps (eps [/]TwoNZ).
Proof.
 intros.
 apply leEq_imp_AbsSmall.
  apply nonneg_div_two.
  assumption.
 apply eps_div_leEq_eps.
  assumption.
 apply less_leEq.
 apply one_less_two.
Qed.

Lemma AbsSmall_nonneg : forall e x : R, AbsSmall e x -> [0] [<=] e.
Proof.
 unfold AbsSmall in |- *.
 intros.
 elim H.
 intros.
 cut ([--]e [<=] e).
  intros.
  apply mult_cancel_leEq with (z := Two:R).
   apply pos_two.
  apply plus_cancel_leEq_rht with (z := [--]e).
  rstepl ([--]e).
  rstepr e.
  assumption.
 apply leEq_transitive with (y := x).
  assumption.
 assumption.
Qed.


Lemma AbsSmall_mult : forall e1 e2 x1 x2 : R,
 AbsSmall e1 x1 -> AbsSmall e2 x2 -> AbsSmall (Three[*] (e1[*]e2)) (x1[*]x2).
Proof.
 unfold AbsSmall in |- *.
 intros.
 elim H.
 intros.
 elim H0.
 intros.
 cut ([0] [<=] e1).
  intro.
  cut ([0] [<=] e2).
   intro.
   split.
    apply plus_cancel_leEq_rht with (z := Three[*] (e1[*]e2)).
    rstepl ZeroR.
    rstepr (x1[*]x2[+]e1[*]e2[+]e1[*]e2[+]e1[*]e2).
    apply leEq_transitive with (y := x1[*]x2[+]e1[*]e2[+]x1[*]e2[+]e1[*]x2).
     rstepr ((e1[+]x1)[*](e2[+]x2)).
     apply mult_resp_nonneg.
      apply plus_cancel_leEq_rht with (z := [--]x1).
      rstepl ([--]x1).
      rstepr ([--][--]e1).
      apply inv_resp_leEq.
      assumption.
     apply plus_cancel_leEq_rht with (z := [--]x2).
     rstepl ([--]x2).
     rstepr ([--][--]e2).
     apply inv_resp_leEq.
     assumption.
    rstepl (x1[*]x2[+]e1[*]e2[+](x1[*]e2[+]e1[*]x2)).
    rstepr (x1[*]x2[+]e1[*]e2[+](e1[*]e2[+]e1[*]e2)).
    apply plus_resp_leEq_lft.
    apply plus_resp_leEq_both.
     apply mult_resp_leEq_rht.
      assumption.
     assumption.
    apply mult_resp_leEq_lft.
     assumption.
    assumption.
   apply plus_cancel_leEq_rht with (z := [--](x1[*]x2)).
   rstepl ZeroR.
   rstepr ([--](x1[*]x2)[+]e1[*]e2[+](e1[*]e2[+]e1[*]e2)).
   apply leEq_transitive with (y := [--](x1[*]x2)[+]e1[*]e2[+](x1[*]e2[-]e1[*]x2)).
    rstepr ((e1[+]x1)[*](e2[-]x2)).
    apply mult_resp_nonneg.
     apply plus_cancel_leEq_rht with (z := [--]x1).
     rstepl ([--]x1).
     rstepr ([--][--]e1).
     apply inv_resp_leEq.
     assumption.
    apply plus_cancel_leEq_rht with (z := x2).
    rstepl x2.
    rstepr e2.
    assumption.
   apply plus_resp_leEq_lft.
   rstepl (x1[*]e2[+][--]e1[*]x2).
   apply plus_resp_leEq_both.
    apply mult_resp_leEq_rht.
     assumption.
    assumption.
   rstepl (e1[*][--]x2).
   apply mult_resp_leEq_lft.
    rstepr ([--][--]e2).
    apply inv_resp_leEq.
    assumption.
   assumption.
  apply AbsSmall_nonneg with (e := e2) (x := x2).
  assumption.
 apply AbsSmall_nonneg with (e := e1) (x := x1).
 assumption.
Qed.

Lemma AbsSmall_cancel_mult : forall e x z : R,
 [0] [<] z -> AbsSmall (e[*]z) (x[*]z) -> AbsSmall e x.
Proof.
 unfold AbsSmall in |- *.
 intros.
 elim H.
 intros.
 split.
  apply mult_cancel_leEq with (z := z).
   assumption.
  rstepl ([--](e[*]z)).
  assumption.
 apply mult_cancel_leEq with (z := z).
  assumption.
 assumption.
Qed.

Lemma AbsSmall_approach_zero : forall x : R, (forall e, [0] [<] e -> AbsSmall e x) -> x [=] [0].
Proof.
 intros.
 apply not_ap_imp_eq.
 intro H0.
 elim (ap_imp_less _ _ _ H0).
  change (Not (x [<] [0])).
  rewrite <- leEq_def.
  apply inv_cancel_leEq.
  astepr ZeroR.
  apply approach_zero_weak.
  intros.
  apply inv_cancel_leEq; astepr x.
  elim (H e); auto.
 change (Not ([0] [<] x)).
 rewrite <- leEq_def.
 apply approach_zero_weak.
 intros.
 elim (H e); auto.
Qed.

Lemma mult_AbsSmall'_rht : forall x y C : R, [0] [<=] C ->
 [--]C [<=] x -> x [<=] C -> [--]C [<=] y -> y [<=] C -> x[*]y [<=] Three[*]C[^]2.
Proof.
 intros.
 astepl ([0][+]x[*]y). apply shift_plus_leEq.
 apply leEq_transitive with ((C[+]x)[*](C[-]y)).
  apply mult_resp_nonneg.
   apply shift_leEq_plus. astepl ([--]x). astepr ([--][--]C).
   apply inv_resp_leEq. auto.
   apply shift_leEq_minus. astepl y. auto.
  rstepl (C[^]2[-]x[*]y[+]C[*](x[-]y)).
 rstepr (C[^]2[-]x[*]y[+]C[*](C[-][--]C)).
 apply plus_resp_leEq_lft.
 apply mult_resp_leEq_lft.
  apply minus_resp_leEq_both.
   auto. auto. auto.
Qed.

Lemma mult_AbsSmall_rht : forall x y X Y : R, [0] [<=] X ->
 [0] [<=] Y -> [--]X [<=] x -> x [<=] X -> [--]Y [<=] y -> y [<=] Y -> x[*]y [<=] X[*]Y.
Proof.
 intros.
 rewrite -> leEq_def.
 intro.
 cut ([0] [<] x[*]y); intros.
  2: apply leEq_less_trans with (X[*]Y); auto.
 rewrite -> leEq_def in *.
 cut (x[*]y [#] [0]); intros.
  2: apply pos_ap_zero; auto.
 cut (x [#] [0]); intros.
  2: apply mult_cancel_ap_zero_lft with y; auto.
 elim (ap_imp_less _ _ _ X3); intro.
  cut (y [<] [0]); intros.
   2: astepl ([--][--]y); astepr ([--]([0]:R)); apply inv_resp_less.
   2: apply mult_cancel_pos_rht with ([--]x).
    2: astepr (x[*]y); auto.
   2: astepl ([--]([0]:R)); apply less_leEq; apply inv_resp_less; auto.
  apply (less_irreflexive_unfolded R [1]).
  apply leEq_less_trans with (X[*]Y[/] _[//]X2).
   rstepr ((X[/] [--]x[//]inv_resp_ap_zero _ _ X3)[*]
     (Y[/] [--]y[//]inv_resp_ap_zero _ _ (less_imp_ap _ _ _ X4))).
   astepl ([1][*]([1]:R)).
   apply mult_resp_leEq_both.
      apply less_leEq; apply pos_one.
     apply less_leEq; apply pos_one.
    apply shift_leEq_div.
     astepl ([--]([0]:R)); apply inv_resp_less; auto.
    astepl ([--]x); astepr ([--][--]X); apply inv_resp_leEq; firstorder using leEq_def.
   apply shift_leEq_div.
    astepl ([--]([0]:R)); apply inv_resp_less; auto.
   astepl ([--]y); astepr ([--][--]Y); apply inv_resp_leEq; firstorder using leEq_def.
  apply shift_div_less; auto.
  astepr (x[*]y); auto.
 cut ([0] [<] y); intros.
  2: apply mult_cancel_pos_rht with x; try apply less_leEq; auto.
 apply (less_irreflexive_unfolded R [1]).
 apply leEq_less_trans with (X[*]Y[/] _[//]X2).
  rstepr ((X[/] x[//]X3)[*](Y[/] y[//]pos_ap_zero _ _ X4)).
  astepl ([1][*]([1]:R)).
  apply mult_resp_leEq_both.
     apply less_leEq; apply pos_one.
    apply less_leEq; apply pos_one.
   apply shift_leEq_div; auto.
   astepl x; firstorder using leEq_def.
  apply shift_leEq_div; auto.
  astepl y; firstorder using leEq_def.
 apply shift_div_less; auto.
 astepr (x[*]y); firstorder using leEq_def.
Qed.

Lemma mult_AbsSmall_lft : forall x y X Y : R, [0] [<=] X -> [0] [<=] Y ->
 [--]X [<=] x -> x [<=] X -> [--]Y [<=] y -> y [<=] Y -> [--](X[*]Y) [<=] x[*]y.
Proof.
 intros.
 rstepr ([--]([--]x[*]y)).
 apply inv_resp_leEq.
 apply mult_AbsSmall_rht; auto.
  apply inv_resp_leEq. auto.
  rstepr ([--][--]X).
 apply inv_resp_leEq. auto.
Qed.

Lemma mult_AbsSmall : forall x y X Y : R,
 AbsSmall X x -> AbsSmall Y y -> AbsSmall (X[*]Y) (x[*]y).
Proof.
 unfold AbsSmall in |- *.
 intros.
 elim H. intros. elim H0. intros.
 cut ([0] [<=] X). intro. cut ([0] [<=] Y). intro.
  split.
    apply mult_AbsSmall_lft; auto.
   apply mult_AbsSmall_rht; auto.
  apply AbsSmall_nonneg with y; auto.
 apply AbsSmall_nonneg with x; auto.
Qed.

End AbsSmall_properties.

Declare Left Step AbsSmall_wdl_unfolded.
Declare Right Step AbsSmall_wdr_unfolded.

(**
** Properties of [AbsBig] *)

Definition absBig (R : COrdField) (e x : R) : CProp :=
 [0] [<] e and (e [<=] x or x [<=] [--]e).

Notation AbsBig := (absBig _).

Lemma AbsBigSmall_minus : forall (R : COrdField) (e1 e2 x1 x2 : R),
 e2 [<] e1 -> AbsBig e1 x1 -> AbsSmall e2 x2 -> AbsBig (e1[-]e2) (x1[-]x2).
Proof.
 intros.
 unfold absBig in |- *.
 split.
  apply plus_cancel_less with (z := e2).
  rstepl e2.
  rstepr e1.
  assumption.
 unfold absBig in X0.
 elim X0.
 intros H2 H3.
 case H3.
  intro H4.
  left.
  unfold AbsSmall in H.
  elim H.
  intros.
  rstepl (e1[+][--]e2).
  rstepr (x1[+][--]x2).
  apply plus_resp_leEq_both.
   assumption.
  apply inv_cancel_leEq.
  rstepl x2.
  rstepr e2.
  assumption.
 intro H4.
 right.
 unfold AbsSmall in H.
 elim H.
 intros H5 H6.
 rstepr ([--]e1[+]e2).
 rstepl (x1[+][--]x2).
 apply plus_resp_leEq_both.
  assumption.
 apply inv_cancel_leEq.
 rstepr x2.
 rstepl ([--]e2).
 assumption.
Qed.


Section absBig_wd_properties.
(**
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)

Variable R : COrdField.

Lemma AbsBig_wdr : Crel_wdr R AbsBig.
Proof.
 red in |- *.
 intros.
 unfold absBig in |- *.
 unfold absBig in H.
 elim X.
 intros H1 H2.
 split.
  assumption.
 case H2.
  intro H3.
  left.
  apply leEq_wdr with y.
   assumption.
  assumption.
 intro H3.
 right.
 apply leEq_wdl with y.
  assumption.
 assumption.
Qed.

Lemma AbsBig_wdl : Crel_wdl R AbsBig.
Proof.
 red in |- *.
 unfold absBig in |- *.
 intros.
 elim X.
 intros H1 H2.
 split.
  astepr x.
  assumption.
 case H2.
  intro H3.
  left.
  astepl x.
  assumption.
 intro H3.
 right.
 astepr ([--]x).
 assumption.
Qed.

Lemma AbsBig_wdr_unfolded : forall x y z : R, AbsBig x y -> y [=] z -> AbsBig x z.
Proof AbsBig_wdr.

Lemma AbsBig_wdl_unfolded : forall x y z : R, AbsBig x y -> x [=] z -> AbsBig z y.
Proof AbsBig_wdl.

End absBig_wd_properties.

Declare Left Step AbsBig_wdl_unfolded.
Declare Right Step AbsBig_wdr_unfolded.

Add Parametric Morphism c : (@AbsSmall c) with signature (@cs_eq (cof_crr c)) ==> (@cs_eq c) ==> iff as AbsSmall_morph_wd.
Proof with try assumption.
 intros x1 x2 xeq y1 y2 yeq.
 split; intro H.
  stepr y1...
  stepl x1...
 symmetry in xeq, yeq.
 stepr y2...
 stepl x2...
Qed.
