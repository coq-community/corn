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

(**
* On density of the image of [Q] in an arbitrary real number structure
In this file we introduce the image of the concrete rational numbers
(as defined earlier) in an arbitrary structure of type
[CReals]. At the end of this file we assign to any real number two
rational numbers for which the real number lies betwen image of them;
in other words we will prove that the image of rational numbers in
dense in any real number structure. *)

Require Export CoRN.model.reals.Cauchy_IR.
Require Export CoRN.model.monoids.Nmonoid.
Require Export CoRN.model.rings.Zring.
Require Import CoRN.algebra.CRing_Homomorphisms.
Require Import CoRN.algebra.Expon.
Require Import Coq.QArith.Qpower.
Require Import CoRN.tactics.CornTac.

Section Rational_sequence_prelogue.

(**
%\begin{convention}% Let [R1] be a real number structure.
%\end{convention}%
*)
Variable R1 : CReals.

(* We clone these proofs from CReals1.v just because there IR is an axiom *)
(* begin hide *)
Lemma CReals_is_CReals : is_CReals R1 (Lim (IR:=R1)).
Proof.
 unfold Lim in |- *.
 elim R1; intros.
 exact crl_proof.
Qed.

Lemma Lim_Cauchy : forall s : CauchySeq R1, SeqLimit s (Lim s).
Proof.
 elim CReals_is_CReals.
 intros.
 apply ax_Lim.
Qed.

Lemma Archimedes : forall x : R1, {n : nat | x [<=] nring n}.
Proof.
 elim CReals_is_CReals.
 intros.
 apply ax_Arch.
Qed.

Lemma Archimedes' : forall x : R1, {n : nat | x [<] nring n}.
Proof.
 intro x.
 elim (Archimedes (x[+][1])); intros n Hn.
 exists n.
 apply less_leEq_trans with (x[+][1]); auto.
 apply less_plusOne.
Qed.
(*--------------------------------------*)

Local Coercion nat_of_P : positive >-> nat.
(* end hide *)

(**
** Injection from [Q] to an arbitrary real number structure
 First we need to define the injection from [Q] to [R1]. Note that in [Cauchy_CReals] we defined [inject_Q] from an arbitray field [F] to [(R_COrdField F)] which was the set of Cauchy sequences of that field. But since [R1] is an %\emph{arbitrary}%#<i>arbitrary</i># real number structure we can not use [inject_Q].

 To define the injection we need one elemntary lemma about the denominator:
*)

Lemma den_is_nonzero : forall x : Q_as_COrdField, nring (R:=R1) (Qden x) [#] [0].
Proof.
 intro.
 apply nring_ap_zero.
 intro.
 absurd (0 < Qden x).
  rewrite H.
  auto with arith.
 apply lt_O_nat_of_P.
Qed.

(** And we define the injection in the natural way, using [zring] and [nring]. We call this [inj_Q], in contrast with [inject_Q] defined in [Cauchy_CReals]. *)

Definition inj_Q : Q_as_COrdField -> R1.
Proof.
 intro x.
 case x.
 intros num0 den0.
 exact (zring num0[/]nring (R:=R1) den0[//]den_is_nonzero (Qmake num0 den0)).
Defined.

(** Next we need some properties of [nring], on the setoid of natural numbers: *)

Lemma nring_strext : forall m n : nat_as_CMonoid,
 (nring (R:=R1) m [#] nring (R:=R1) n) -> m [#] n.
Proof.
 intros m n.
 case m.
  case n.
   intro H.
   simpl in |- *.
   red in |- *.
   simpl in H.
   cut (Not ([0] [#] ([0]:R1))).
    intro.
    intro.
    elim H0.
    assumption.
   apply eq_imp_not_ap.
   apply eq_reflexive_unfolded.
  intros.
  simpl in |- *.
  red in |- *.
  discriminate.
 case n.
  intros.
  simpl in |- *.
  red in |- *.
  discriminate.
 intros.
 simpl in |- *.
 red in |- *.
 intro.
 cut (Not (nring (R:=R1) (S n1) [#] nring (R:=R1) (S n0))).
  intro H1.
  elim H1.
  assumption.
 apply eq_imp_not_ap.
 rewrite H.
 apply eq_reflexive_unfolded.
Qed.

Lemma nring_wd : forall m n : nat_as_CMonoid,
 (m [=] n) -> nring (R:=R1) m [=] nring (R:=R1) n.
Proof.
 intros.
 simpl in H.
 rewrite H.
 apply eq_reflexive_unfolded.
Qed.

Lemma nring_eq : forall m n : nat, m = n -> nring (R:=R1) m [=] nring (R:=R1) n.
Proof.
 intros.
 rewrite H.
 apply eq_reflexive_unfolded.
Qed.

Lemma nring_leEq : forall (OF : COrdField) m n,
 m <= n -> nring (R:=OF) m [<=] nring (R:=OF) n.
Proof.
 intros.
 induction  m as [| m Hrecm].
  simpl in |- *.
  case n.
   simpl in |- *.
   apply leEq_reflexive.
  intro.
  apply less_leEq.
  apply pos_nring_S.
 case (le_lt_eq_dec (S m) n H).
  intro.
  apply less_leEq.
  apply nring_less.
  assumption.
 intro.
 rewrite e.
 apply leEq_reflexive.
Qed.

(** Similarly we prove some properties of [zring] on the ring of integers: *)

Lemma zring_strext : forall m n : Z_as_CRing,
 (zring (R:=R1) m [#] zring n) -> m [#] n.
Proof.
 intros m n.
 case m.
   case n.
     intro H.
     elimtype False.
     cut ([0] [=] ([0]:R1)).
      change (~ ([0] [=] ([0]:R1))) in |- *.
      apply ap_imp_neq.
      simpl in H.
      assumption.
     apply eq_reflexive_unfolded.
    intros.
    simpl in |- *.
    red in |- *.
    discriminate.
   intros.
   simpl in |- *.
   red in |- *.
   discriminate.
  case n.
    intros.
    simpl in |- *.
    red in |- *.
    discriminate.
   intros.
   simpl in |- *.
   intro.
   cut (Not (zring (R:=R1) (BinInt.Zpos p0) [#] zring (R:=R1) (BinInt.Zpos p))).
    intro H1.
    elim H1.
    assumption.
   apply eq_imp_not_ap.
   rewrite H.
   apply eq_reflexive_unfolded.
  intros.
  simpl in |- *.
  red in |- *.
  discriminate.
 case n.
   intros.
   simpl in |- *.
   red in |- *.
   discriminate.
  intros.
  simpl in |- *.
  red in |- *.
  discriminate.
 intros.
 simpl in |- *.
 intro.
 cut (Not (zring (R:=R1) (Zneg p0) [#] zring (R:=R1) (Zneg p))).
  intro H1.
  elim H1.
  assumption.
 apply eq_imp_not_ap.
 rewrite H.
 apply eq_reflexive_unfolded.
Qed.

Lemma zring_wd : forall m n : Z_as_CRing,
 (m [=] n) -> zring (R:=R1) m [=] zring (R:=R1) n.
Proof.
 intros.
 simpl in H.
 rewrite H.
 apply eq_reflexive_unfolded.
Qed.

Lemma zring_less : forall m n : Z_as_CRing,
 (m < n)%Z -> zring (R:=R1) m [<] zring (R:=R1) n.
Proof.
 intros m n.
 case m.
   case n.
     intro.
     apply False_rect.
     generalize H.
     change (~ (0 < 0)%Z) in |- *.
     apply Z.lt_irrefl.
    intros.
    simpl in |- *.
    astepl (nring (R:=R1) 0).
    astepr (nring (R:=R1) (nat_of_P p)).
    apply nring_less.
    case (ZL4' p).
    intro a.
    intro H0.
    rewrite H0.
    apply lt_O_Sn.
   intros.
   apply False_rect.
   generalize H.
   change (~ (0 < Zneg p)%Z) in |- *.
   apply Zlt_asym.
   constructor.
  case n.
    intros.
    apply False_rect.
    generalize H.
    change (~ (BinInt.Zpos p < 0)%Z) in |- *.
    apply Zlt_asym.
    constructor.
   intros p1 p2.
   intro.
   simpl in |- *.
   astepl (nring (R:=R1) (nat_of_P p2)).
   astepr (nring (R:=R1) (nat_of_P p1)).
   apply nring_less.
   apply nat_of_P_lt_Lt_compare_morphism.
   red in H.
   simpl in H.
   assumption.
  intros p1 p2.
  intro.
  apply False_rect.
  generalize H.
  change (~ (BinInt.Zpos p2 < Zneg p1)%Z) in |- *.
  apply Zlt_asym.
  constructor.
 case n.
   intros.
   simpl in |- *.
   astepl [--](nring (R:=R1) (nat_of_P p)).
   astepr ([0]:R1).
   apply inv_cancel_less.
   astepl ([0]:R1).
   astepr (nring (R:=R1) (nat_of_P p)).
   case (ZL4' p).
   intro h.
   intros H0.
   rewrite H0.
   apply pos_nring_S.
  intros p1 p2.
  intro.
  simpl in |- *.
  case (ZL4' p1).
  intro h1.
  case (ZL4' p2).
  intro h2.
  intros.
  apply less_transitive_unfolded with (y := [0]:R1).
   astepl [--](nring (R:=R1) (nat_of_P p2)).
   apply inv_cancel_less.
   astepl ([0]:R1).
   astepr (nring (R:=R1) (nat_of_P p2)).
   rewrite e.
   apply pos_nring_S.
  astepr (nring (R:=R1) p1).
  rewrite e0.
  apply pos_nring_S.
 intros p1 p2.
 intro.
 simpl in |- *.
 astepl [--](nring (R:=R1) (nat_of_P p2)).
 astepr [--](nring (R:=R1) (nat_of_P p1)).
 apply inv_resp_less.
 apply nring_less.
 apply nat_of_P_lt_Lt_compare_morphism.
 red in H.
 simpl in H. now rewrite ZC4.
Qed.

(** Using the above lemmata we prove the basic properties of [inj_Q], i.e.%\% it is a setoid function and preserves the ring operations and oreder operation. *)

Lemma inj_Q_strext : forall q1 q2, (inj_Q q1 [#] inj_Q q2) -> q1 [#] q2.
Proof.
 intros q1 q2.
 generalize (den_is_nonzero q1).
 generalize (den_is_nonzero q2).
 case q1.
 intros n1 d1.
 case q2.
 intros n2 d2.
 intros H H0 H1.
 simpl in |- *.
 simpl in H.
 simpl in H0.
 unfold Qap in |- *.
 unfold Qeq in |- *.
 unfold Qnum in |- *.
 unfold Qden in |- *.
 intro.
 cut (~ (inj_Q (Qmake n1 d1) [=] inj_Q (Qmake n2 d2))).
  intro.
  elim H3.
  simpl in |- *.
  apply mult_cancel_lft with (z := nring (R:=R1) d1[*]nring (R:=R1) d2).
   apply mult_resp_ap_zero.
    assumption.
   assumption.
  rstepl (zring (R:=R1) n1[*]nring (R:=R1) d2).
  rstepr (zring (R:=R1) n2[*]nring (R:=R1) d1).
  astepr (zring (R:=R1) (n1 * d2)).
   astepr (zring (R:=R1) n1[*]zring (R:=R1) d2).
   apply mult_wdr.
   astepl (zring (R:=R1) (Z_of_nat (nat_of_P d2))).
   rewrite inject_nat_convert.
   algebra.
  rewrite H2.
  astepl (zring (R:=R1) n2[*]zring (R:=R1) d1).
  apply mult_wdr.
  astepr (zring (R:=R1) (Z_of_nat (nat_of_P d1))).
  rewrite inject_nat_convert.
  algebra.
 change (inj_Q (Qmake n1 d1)[~=]inj_Q (Qmake n2 d2)) in |- *.
 apply ap_imp_neq.
 assumption.
Qed.

Lemma inj_Q_wd : forall q1 q2, (q1 [=] q2) -> inj_Q q1 [=] inj_Q q2.
Proof.
 intros.
 apply not_ap_imp_eq.
 intro.
 cut (~ (q1 [=] q2)).
  intro H1.
  apply H1.
  assumption.
 change (q1[~=]q2) in |- *.
 apply ap_imp_neq.
 apply inj_Q_strext.
 assumption.
Qed.

Lemma inj_Q_plus : forall q1 q2, inj_Q (q1[+]q2) [=] inj_Q q1[+]inj_Q q2.
Proof.
 intros.
 generalize (den_is_nonzero q1).
 generalize (den_is_nonzero q2).
 case q1.
 intros n1 d1.
 case q2.
 intros n2 d2.
 simpl in |- *.
 intros.
 apply mult_cancel_lft with (z := nring (R:=R1) d1[*]nring (R:=R1) d2).
  apply mult_resp_ap_zero.
   assumption.
  assumption.
 astepr (zring (R:=R1) (n1 * d2 + n2 * d1)).
  astepr (nring (R:=R1) (d1 * d2)%positive[*]
    (zring (R:=R1) (n1 * d2 + n2 * d1)[/]nring (R:=R1) (d1 * d2)%positive[//]
      den_is_nonzero (Qmake (n1 * d2 + n2 * d1)%Z (d1 * d2)%positive))).
  apply mult_wdl.
  rewrite nat_of_P_mult_morphism.
  algebra.
 astepr (zring (R:=R1) n1[*]nring (R:=R1) d2[+]zring (R:=R1) n2[*]nring (R:=R1) d1).
  astepl (zring (R:=R1) (n1 * d2)[+]zring (R:=R1) (n2 * d1)).
  apply bin_op_wd_unfolded.
   astepr (zring (R:=R1) n1[*]zring (R:=R1) (Z_of_nat (nat_of_P d2))).
   rewrite inject_nat_convert.
   algebra.
  astepr (zring (R:=R1) n2[*]zring (R:=R1) (Z_of_nat (nat_of_P d1))).
  rewrite inject_nat_convert.
  algebra.
 rational.
Qed.

Lemma inj_Q_mult : forall q1 q2, inj_Q (q1[*]q2) [=] inj_Q q1[*]inj_Q q2.
Proof.
 intros.
 generalize (den_is_nonzero q1).
 generalize (den_is_nonzero q2).
 case q1.
 intros n1 d1.
 case q2.
 intros n2 d2.
 simpl in |- *.
 intros.
 apply mult_cancel_lft with (z := nring (R:=R1) d1[*]nring (R:=R1) d2).
  apply mult_resp_ap_zero.
   assumption.
  trivial.
 astepr (zring (R:=R1) (n1 * n2)).
  astepr (nring (R:=R1) (d1 * d2)%positive[*]
    (zring (R:=R1) (n1 * n2)[/]nring (R:=R1) (d1 * d2)%positive[//]
      den_is_nonzero (Qmake (n1 * n2)%Z (d1 * d2)%positive))).
  apply mult_wdl.
  rewrite nat_of_P_mult_morphism.
  algebra.
 astepr (zring (R:=R1) n1[*]zring (R:=R1) n2).
  apply zring_mult.
 rational.
Qed.

Lemma inj_Q_less : forall q1 q2, (q1 [<] q2) -> inj_Q q1 [<] inj_Q q2.
Proof.
 intros q1 q2.
 case q1.
 intros n1 d1.
 case q2.
 intros n2 d2.
 intro H.
 simpl in H.
 unfold Qlt in H.
 simpl in H.
 simpl in |- *.
 apply mult_cancel_less with (z := nring (R:=R1) d1[*]nring (R:=R1) d2).
  apply mult_resp_pos.
   elim (ZL4' d1); intros.
   rewrite p.
   apply pos_nring_S.
  elim (ZL4' d2); intros.
  rewrite p.
  apply pos_nring_S.
 rstepl (zring (R:=R1) n1[*]nring (R:=R1) d2).
 rstepr (zring (R:=R1) n2[*]nring (R:=R1) d1).
 apply less_wdl with (x := zring (R:=R1) n1[*]zring (R:=R1) (Z_of_nat d2)).
  apply less_wdr with (y := zring (R:=R1) n2[*]zring (R:=R1) (Z_of_nat d1)).
   apply less_wdl with (x := zring (R:=R1) (n1 * d2)).
    apply less_wdr with (y := zring (R:=R1) (n2 * d1)).
     apply zring_less.
     apply CZlt_to.
     assumption.
    rewrite inject_nat_convert.
    apply zring_mult.
   rewrite inject_nat_convert.
   apply zring_mult.
  algebra.
 algebra.
Qed.

Lemma less_inj_Q : forall q1 q2, (inj_Q q1 [<] inj_Q q2) -> q1 [<] q2.
Proof.
 intros.
 cut (q1 [#] q2).
  intro H0.
  case (ap_imp_less _ q1 q2 H0).
   intro.
   assumption.
  intro.
  elimtype False.
  cut (inj_Q q2 [<] inj_Q q1).
   change (Not (inj_Q q2 [<] inj_Q q1)) in |- *.
   apply less_antisymmetric_unfolded.
   assumption.
  apply inj_Q_less.
  assumption.
 apply inj_Q_strext.
 apply less_imp_ap.
 assumption.
Qed.

Lemma inj_Q_ap : forall q1 q2, (q1 [#] q2) -> inj_Q q1 [#] inj_Q q2.
Proof.
 intros q1 q2 H.
 destruct (ap_imp_less _ _ _ H); [apply less_imp_ap|apply Greater_imp_ap];
   apply inj_Q_less; assumption.
Qed.

Lemma leEq_inj_Q : forall q1 q2, (inj_Q q1 [<=] inj_Q q2) -> q1 [<=] q2.
Proof.
 intros.
 rewrite -> leEq_def; intro.
 apply less_irreflexive_unfolded with (x := inj_Q q2).
 eapply less_leEq_trans.
  2: apply H.
 apply inj_Q_less.
 auto.
Qed.

Lemma inj_Q_leEq : forall q1 q2, (q1 [<=] q2) -> inj_Q q1 [<=] inj_Q q2.
Proof.
 intros.
 rewrite -> leEq_def; intro.
 rewrite -> leEq_def in H; apply H.
 apply less_inj_Q.
 assumption.
Qed.

Lemma inj_Q_inv : forall q1, inj_Q [--]q1 [=] [--](inj_Q q1).
Proof.
 intro.
 apply cg_cancel_lft with (x := inj_Q q1).
 astepr (inj_Q (q1[+][--]q1)).
  apply eq_symmetric_unfolded.
  apply inj_Q_plus.
 astepr (inj_Q [0]).
  apply inj_Q_wd.
  algebra.
 simpl in |- *.
 rstepl ([0]:R1).
 algebra.
Qed.

Lemma inj_Q_minus : forall q1 q2, inj_Q (q1[-]q2) [=] inj_Q q1[-]inj_Q q2.
Proof.
 intros.
 astepl (inj_Q (q1[+][--]q2)).
 astepr (inj_Q q1[+]inj_Q [--]q2).
  apply inj_Q_plus.
 astepr (inj_Q q1[+][--](inj_Q q2)).
 apply plus_resp_eq.
 apply inj_Q_inv.
Qed.

Lemma inj_Q_div : forall q1 q2 H, inj_Q (q1/q2)%Q [=] (inj_Q q1[/]inj_Q q2[//]H).
Proof.
 intros.
 apply mult_cancel_rht with (inj_Q q2);[apply H|].
 apply eq_symmetric.
 eapply eq_transitive;[|apply inj_Q_mult].
 eapply eq_transitive;[apply div_1|].
 apply inj_Q_wd.
 simpl.
 field.
 apply inj_Q_strext.
 stepr ([0]:R1).
  apply H.
 rstepl (inj_Q q1[-]inj_Q q1).
 apply eq_symmetric.
 eapply eq_transitive;[|apply inj_Q_minus].
 apply inj_Q_wd.
 unfold cg_minus.
 simpl.
 ring.
Qed.

Hint Resolve inj_Q_plus inj_Q_mult inj_Q_inv inj_Q_minus inj_Q_div : algebra.

(** Moreover, and as expected, the [AbsSmall] predicate is also
preserved under the [inj_Q] *)

Lemma inj_Q_AbsSmall : forall q1 q2,
 AbsSmall q1 q2 -> AbsSmall (inj_Q q1) (inj_Q q2).
Proof.
 intros.
 red in |- *.
 elim H.
 intros.
 split.
  astepl (inj_Q [--]q1).
  apply inj_Q_leEq.
  assumption.
 apply inj_Q_leEq.
 assumption.
Qed.

Lemma AbsSmall_inj_Q : forall q e,
 AbsSmall (inj_Q e) (inj_Q q) -> AbsSmall e q.
Proof.
 intros.
 elim H.
 intros.
 split.
  apply leEq_inj_Q.
  apply leEq_wdl with (x := [--](inj_Q e)).
   assumption.
  apply eq_symmetric_unfolded.
  apply inj_Q_inv.
 apply leEq_inj_Q.
 assumption.
Qed.


(**
** Injection preserves Cauchy property
We apply the above lemmata to obtain following theorem, which says
that a Cauchy sequence of elemnts of [Q] will be Cauchy in [R1].
*)

Theorem inj_Q_Cauchy : forall g : CauchySeq Q_as_COrdField,
 Cauchy_prop (fun n => inj_Q (g n)).
Proof.
 intros.
 case g.
 intros g_ pg.
 simpl in |- *.
 red in |- *.
 intros e H.
 cut {n : nat | ([1][/]e[//]Greater_imp_ap _ e [0] H) [<] nring (R:=R1) n}.
  intro H0.
  case H0.
  intros N1 H1.
  unfold Cauchy_prop in pg.
  cut {N : nat | forall m : nat, N <= m ->
    AbsSmall (R:=Q_as_COrdField) (Qmake 1%Z (P_of_succ_nat N1)) (g_ m[-]g_ N)}.
   intro H2.
   case H2.
   intro N.
   intro.
   exists N.
   intros.
   apply AbsSmall_leEq_trans with (e1 := inj_Q (Qmake 1%Z (P_of_succ_nat N1))).
    apply less_leEq.
    apply mult_cancel_less with (z := nring (R:=R1) (S N1)[*]([1][/]e[//]Greater_imp_ap _ e [0] H)).
     apply mult_resp_pos.
      apply pos_nring_S.
     apply div_resp_pos.
      assumption.
     apply pos_one.
    unfold inj_Q in |- *.
    rewrite <- nat_of_P_o_P_of_succ_nat_eq_succ with N1.
    rstepl ([1][/]e[//]Greater_imp_ap _ e [0] H).
    rstepr (nring (R:=R1) (P_of_succ_nat N1)).
    apply less_transitive_unfolded with (y := nring (R:=R1) N1).
     assumption.
    apply nring_less.
    rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
    apply lt_n_Sn.
   astepr (inj_Q (g_ m[-]g_ N)).
   apply inj_Q_AbsSmall.
   apply a.
   assumption.
  apply pg.
  simpl in |- *.
  red in |- *.
  simpl in |- *.
  constructor.
 apply Archimedes'.
Qed.

(** Furthermore we prove that applying [nring] (which is adding the
ring unit [n] times) is the same whether we do it in [Q] or in [R1]:
*)

Lemma inj_Q_nring : forall n, inj_Q (nring n) [=] nring (R:=R1) n.
Proof.
 intro.
 simpl in |- *.
 induction  n as [| n Hrecn].
  simpl in |- *.
  rational.
 change (inj_Q (nring n[+][1]) [=] nring (R:=R1) n[+][1]) in |- *.
 astepr (inj_Q (nring n)[+]inj_Q [1]).
  apply inj_Q_plus.
 apply bin_op_wd_unfolded.
  assumption.
 simpl in |- *.
 unfold pring in |- *; simpl in |- *.
 rational.
Qed.

Lemma inj_Q_pring : forall n, inj_Q (pring _ n) [=] pring R1 n.
Proof.
 intros n.
 change (inj_Q (zring n)[=]zring n).
 stepr (inj_Q (nring n)).
  apply inj_Q_wd.
  rewrite <- inject_nat_convert.
  apply zring_plus_nat.
 stepr (nring n:R1).
  apply inj_Q_nring.
 apply eq_symmetric.
 rewrite <- inject_nat_convert.
 apply zring_plus_nat.
Qed.

Lemma inj_Q_zring : forall n, inj_Q (zring n) [=] zring (R:=R1) n.
Proof.
 intros [|n|n].
   simpl.
   rational.
  simpl.
  apply inj_Q_pring.
 change (inj_Q ([--](pring _ n))[=][--](pring _ n)).
 stepl ([--](inj_Q (zring (R:=Q_as_COrdField) n))).
  apply un_op_wd_unfolded.
  simpl.
  apply inj_Q_pring.
 apply eq_symmetric.
 apply inj_Q_inv.
Qed.

Lemma inj_Q_One : inj_Q [1] [=] [1].
Proof.
 rstepr ((nring 1):R1).
 apply (inj_Q_nring 1).
Qed.

Lemma inj_Q_Zero : inj_Q [0] [=] [0].
Proof.
 rstepr ((nring 0):R1).
 apply (inj_Q_nring 0).
Qed.

Hint Resolve inj_Q_nring inj_Q_pring inj_Q_zring inj_Q_One inj_Q_Zero : algebra.

Definition inj_Q_hom : RingHom Q_as_CRing R1.
Proof.
 exists (Build_CSetoid_fun _ _ _ inj_Q_strext).
   refine inj_Q_plus.
  refine inj_Q_mult.
 refine inj_Q_One.
Defined.

Lemma inj_Q_power : forall q1 (n:nat), inj_Q (q1^n)%Q [=] (inj_Q q1[^]n).
Proof.
 intros q.
 induction n.
  apply inj_Q_One.
 rewrite inj_S.
 unfold Z.succ.
 stepr (inj_Q (q^n*q)%Q).
  apply inj_Q_wd.
  simpl.
  apply Qpower_plus'.
  auto with *.
 stepr (inj_Q (q^n)%Q[*]inj_Q q).
  apply inj_Q_mult.
 simpl.
 apply mult_wdl.
 assumption.
Qed.

Lemma inj_Q_power_Z : forall q1 (n:Z) H, inj_Q (q1^n)%Q [=] ((inj_Q q1)[//]H)[^^]n.
Proof.
 intros q [|n|n] H.
   change (inj_Q (q ^ 0)%Q[=][1]).
   apply inj_Q_One.
  simpl.
  change (inj_Q (q ^ n)%Q[=]inj_Q q[^]n).
  csetoid_rewrite_rev (inj_Q_power q n).
  rewrite inject_nat_convert.
  apply eq_reflexive.
 change ((inj_Q (/q ^ n))%Q[=]([1][/]inj_Q q[//]H)[^]n).
 stepl (inj_Q ((1/q)^n)%Q).
  stepr ((inj_Q (1/q)%Q)[^]n).
   csetoid_rewrite_rev (inj_Q_power (1/q)%Q n).
   rewrite inject_nat_convert.
   apply eq_reflexive.
  apply nexp_wd.
  stepr (inj_Q 1%Q[/]_[//]H).
   apply inj_Q_div.
  apply div_wd.
   rstepr (nring 1:R1).
   apply (inj_Q_nring 1).
  apply eq_reflexive.
 apply inj_Q_wd.
 change (((1 * / q) ^ n)%Q==(/ q ^ n))%Q.
 rewrite <- Qinv_power.
 rewrite -> Qmult_1_l.
 reflexivity.
Qed.

Hint Resolve inj_Q_power inj_Q_power_Z : algebra.

(**
** Injection of [Q] is dense
Finally we are able to prove the density of image of [Q] in [R1]. We
state this fact in two different ways. Both of them have their
specific use.

The first theorem states the fact that any real number can be bound by
the image of two rational numbers. This is called [start_of_sequence]
because it can be used as an starting point for the typical "interval
trisection" argument, which is ubiquitous in constructive analysis.
*)

Theorem start_of_sequence : forall x : R1,
 {q1 : Q_as_COrdField | {q2 : Q_as_COrdField | inj_Q q1 [<] x | x [<] inj_Q q2}}.
Proof.
 intros.
 cut {n : nat | x [<] nring (R:=R1) n}.
  intro H.
  cut {n : nat | [--]x [<] nring (R:=R1) n}.
   intro H0.
   case H.
   intro n2.
   intro.
   case H0.
   intro n1.
   intro.
   exists (Qmake (- n1) 1).
   exists (Qmake n2 1).
    simpl in |- *.
    rstepl (zring (R:=R1) (- Z_of_nat n1)).
    astepl [--](nring (R:=R1) n1).
    apply inv_cancel_less.
    astepr (nring (R:=R1) n1).
    assumption.
   simpl in |- *.
   rstepr (zring (R:=R1) (Z_of_nat n2)).
   astepr (nring (R:=R1) n2).
   assumption.
  apply Archimedes'.
 apply Archimedes'.
Qed.

(** The second version of the density of [Q] in [R1] states that given
any positive real number, there is a rational number between it and
zero. This lemma can be used to prove the more general fact that there
is a rational number between any two real numbers. *)

Lemma Q_dense_in_CReals : forall e : R1,
 [0] [<] e -> {q : Q_as_COrdField | [0] [<] inj_Q q | inj_Q q [<] e}.
Proof.
 intros e H.
 cut {n : nat | ([1][/] e[//]Greater_imp_ap _ e [0] H) [<] nring (R:=R1) n}.
  intro H0.
  case H0.
  intro N.
  intros.
  exists (Qmake 1 (P_of_succ_nat N)).
   simpl in |- *.
   unfold pring in |- *; simpl in |- *.
   apply mult_cancel_less with (z := nring (R:=R1) N[+][1]).
    change ([0] [<] nring (R:=R1) (S N)) in |- *.
    apply pos_nring_S.
   astepl ([0]:R1).
   astepr (([0][+][1][-][0][/] nring (P_of_succ_nat N)[//]
     den_is_nonzero (Qmake 1%positive (P_of_succ_nat N)))[*] nring (S N)).
    rewrite <- nat_of_P_o_P_of_succ_nat_eq_succ with N.
    rstepr ([1]:R1).
    apply pos_one.
   apply bin_op_wd_unfolded.
    rational.
   algebra.
  simpl in |- *.
  apply swap_div with (z_ := Greater_imp_ap _ e [0] H).
    rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
    apply pos_nring_S.
   assumption.
  unfold pring in |- *; simpl in |- *.
  rstepl ([1][/] e[//]Greater_imp_ap _ e [0] H).
  apply less_transitive_unfolded with (y := nring (R:=R1) N).
   assumption.
  rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
  apply nring_less_succ.
 apply Archimedes'.
Qed.

Lemma Q_dense_in_CReals' : forall a b : R1,
 a [<] b -> {q : Q_as_COrdField | a [<] inj_Q q | inj_Q q [<] b}.
Proof.
 cut (forall a b : R1, [0][<]b -> a[<]b -> {q : Q_as_COrdField | a[<]inj_Q q | inj_Q q[<]b}).
  intros H a b Hab.
  destruct (less_cotransitive_unfolded _ _ _ Hab [0]);[|apply H;assumption].
  assert (X:[0][<][--]a).
   rstepl ([--][0]:R1).
   apply inv_resp_less.
   assumption.
  assert (Y:=inv_resp_less _ _ _ Hab).
  destruct (H _ _ X Y) as [q Hqa Hqb].
  exists (-q)%Q.
   stepr ([--](inj_Q q)).
    apply inv_cancel_less.
    stepl (inj_Q q);[assumption|apply eq_symmetric; apply cg_inv_inv].
   apply eq_symmetric; apply inj_Q_inv.
  stepl ([--](inj_Q q)).
   apply inv_cancel_less.
   stepr (inj_Q q);[assumption|apply eq_symmetric; apply cg_inv_inv].
  apply eq_symmetric; apply inj_Q_inv.
 cut  (forall a b : R1, [0][<]b -> (a[+][1])[<]b -> {n : nat | a[<]nring n | nring n[<]b}).
  intros H a b Hb Hab.
  destruct (Q_dense_in_CReals _ (shift_zero_less_minus _ _ _ Hab)) as [q Haq Hbq].
  assert (X0 := pos_ap_zero _ _ Haq).
  assert (X1 : [0][<](b[/]inj_Q q[//]X0)).
   apply div_resp_pos; assumption.
  assert (X2 : (a[/]inj_Q q[//]X0)[+][1][<](b[/]inj_Q q[//]X0)).
   apply shift_plus_less'.
   rstepr ((b[-]a)[/]inj_Q q[//]X0).
   apply shift_less_div.
    assumption.
   rstepl (inj_Q q).
   assumption.
  destruct (H _ _ X1 X2) as [r Hra Hrb].
  exists ((nring r)[*]q)%Q; csetoid_rewrite (inj_Q_mult (nring r) q).
   eapply shift_less_mult.
    assumption.
   stepr (nring (R:=R1) r).
    apply Hra.
   apply eq_symmetric. apply inj_Q_nring.
  eapply shift_mult_less.
   assumption.
  stepl (nring (R:=R1) r).
   apply Hrb.
  apply eq_symmetric. apply inj_Q_nring.
 intros a b Hb Hab.
 destruct (Archimedes' a) as [n Hn].
 induction n.
  exists 0; try assumption.
 destruct (less_cotransitive_unfolded _ _ _ Hab (nring (R:=R1) (S n))).
  apply IHn.
  apply plus_cancel_less with [1].
  apply c.
 exists (S n); assumption.
Qed.

End Rational_sequence_prelogue.

Hint Resolve inj_Q_plus inj_Q_mult inj_Q_inv inj_Q_minus inj_Q_div : algebra.
Hint Resolve inj_Q_nring inj_Q_pring inj_Q_zring : algebra.
Hint Resolve inj_Q_power inj_Q_power_Z : algebra.
