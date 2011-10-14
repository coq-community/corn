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
Require Export CGroups.

Section Abelian_Groups.

(**
* Abelian Groups
Now we introduce commutativity and add some results.
*)

Definition is_CAbGroup (G : CGroup) := commutes (csg_op (c:=G)).

Record CAbGroup : Type :=
 {cag_crr   :> CGroup;
  cag_proof :  is_CAbGroup cag_crr}.

Section AbGroup_Axioms.

Variable G : CAbGroup.
(**
%\begin{convention}% Let [G] be an Abelian Group.
%\end{convention}%
*)

Lemma CAbGroup_is_CAbGroup : is_CAbGroup G.
Proof.
 elim G; auto.
Qed.

Lemma cag_commutes : commutes (csg_op (c:=G)).
Proof.
 exact CAbGroup_is_CAbGroup.
Qed.

Lemma cag_commutes_unfolded : forall x y : G, x[+]y [=] y[+]x.
Proof cag_commutes.

End AbGroup_Axioms.

Section SubCAbGroups.

(**
** Subgroups of an Abelian Group
*)
Variable G : CAbGroup.
Variable P : G -> CProp.
Variable Punit : P [0].
Variable op_pres_P : bin_op_pres_pred _ P csg_op.
Variable inv_pres_P : un_op_pres_pred _ P cg_inv.

(**
%\begin{convention}%
Let [G] be an Abelian Group and [P] be a ([CProp]-valued) predicate on [G]
that contains [Zero] and is closed under [[+]] and [[--]].
%\end{convention}%
*)

Let subcrr : CGroup := Build_SubCGroup _ _ Punit op_pres_P inv_pres_P.

Lemma isabgrp_scrr : is_CAbGroup subcrr.
Proof.
 red in |- *. intros x y. case x. case y. intros. simpl in |- *. apply cag_commutes_unfolded.
Qed.

Definition Build_SubCAbGroup : CAbGroup := Build_CAbGroup subcrr isabgrp_scrr.

End SubCAbGroups.

Section Various.
(**
** Basic properties of Abelian groups
*)
Hint Resolve cag_commutes_unfolded: algebra.

Variable G : CAbGroup.
(**
%\begin{convention}% Let [G] be an Abelian Group.
%\end{convention}%
*)

Lemma cag_op_inv : forall x y : G, [--] (x[+]y) [=] [--]x[+] [--]y.
Proof.
 intros x y.
 astepr ([--]y[+] [--]x).
 apply cg_inv_op.
Qed.

Hint Resolve cag_op_inv: algebra.

Lemma assoc_1 : forall x y z : G, x[-] (y[-]z) [=] x[-]y[+]z.
Proof.
 intros x y z; unfold cg_minus in |- *.
 astepr (x[+]([--]y[+]z)).
 Step_final (x[+]([--]y[+] [--][--]z)).
Qed.

Lemma minus_plus : forall x y z : G, x[-] (y[+]z) [=] x[-]y[-]z.
Proof.
 intros x y z.
 unfold cg_minus in |- *.
 Step_final (x[+]([--]y[+] [--]z)).
Qed.

Lemma op_lft_resp_ap : forall x y z : G, y [#] z -> x[+]y [#] x[+]z.
Proof.
 intros x y z H.
 astepl (y[+]x).
 astepr (z[+]x).
 apply op_rht_resp_ap; assumption.
Qed.

Lemma cag_ap_cancel_lft : forall x y z : G, x[+]y [#] x[+]z -> y [#] z.
Proof.
 intros x y z H.
 apply ap_symmetric_unfolded.
 apply cg_ap_cancel_rht with x.
 apply ap_symmetric_unfolded.
 astepl (x[+]y).
 astepr (x[+]z).
 auto.
Qed.

Lemma plus_cancel_ap_lft : forall x y z : G, z[+]x [#] z[+]y -> x [#] y.
Proof.
 intros x y z H.
 apply cag_ap_cancel_lft with z.
 assumption.
Qed.

End Various.

End Abelian_Groups.

Hint Resolve cag_commutes_unfolded: algebra.
Hint Resolve cag_op_inv assoc_1 zero_minus minus_plus op_lft_resp_ap: algebra.

Section Nice_Char.

(**
** Building an abelian group

In order to actually define concrete abelian groups,
it is not in general practical to construct first a semigroup,
then a monoid, then a group and finally an abelian group.  The
presence of commutativity, for example, makes many of the monoid
proofs trivial.  In this section, we provide a constructor that
will allow us to go directly from a setoid to an abelian group.

We start from a setoid S with an element [unit], a
commutative and associative binary operation [plus] which
is strongly extensional in its first argument and admits [unit]
as a left unit, and a unary setoid
function [inv] which inverts elements respective to [plus].
*)

Variable S : CSetoid.
Variable unit : S.
Variable plus : S -> S -> S.
(**
%\begin{convention}%
Let [S] be a Setoid and [unit:S], [plus:S->S->S] and [inv] a unary
setoid operation on [S].
Assume that [plus] is commutative, associative and `left-strongly-extensional
([(plus x z) [#] (plus y z) -> x [#] y]), that [unit] is a left-unit
for [plus] and [(inv x)] is a right-inverse of [x] w.r.t.%\% [plus].
%\end{convention}%
*)

Hypothesis plus_lext : forall x y z : S, plus x z [#] plus y z -> x [#] y.
Hypothesis plus_lunit : forall x : S, plus unit x [=] x.
Hypothesis plus_comm : forall x y : S, plus x y [=] plus y x.
Hypothesis plus_assoc : associative plus.

Variable inv : CSetoid_un_op S.

Hypothesis inv_inv : forall x : S, plus x (inv x) [=] unit.

Lemma plus_rext : forall x y z : S, plus x y [#] plus x z -> y [#] z.
Proof.
 intros x y z H.
 apply plus_lext with x.
 astepl (plus x y).
 astepr (plus x z).
 auto.
Qed.

Lemma plus_runit : forall x : S, plus x unit [=] x.
Proof.
 intro x.
 Step_final (plus unit x).
Qed.

Lemma plus_is_fun : bin_fun_strext _ _ _ plus.
Proof.
 intros x x' y y' H.
 elim (ap_cotransitive_unfolded _ _ _ H (plus x y')); intro H'.
  right; apply plus_lext with x.
  astepl (plus x y); astepr (plus x y'); auto.
 left; eauto.
Qed.

Lemma inv_inv' : forall x : S, plus (inv x) x [=] unit.
Proof.
 intro.
 Step_final (plus x (inv x)).
Qed.

Definition plus_fun : CSetoid_bin_op S := Build_CSetoid_bin_fun _ _ _ plus plus_is_fun.

Definition Build_CSemiGroup' : CSemiGroup.
Proof.
 apply Build_CSemiGroup with S plus_fun.
 exact plus_assoc.
Defined.

Definition Build_CMonoid' : CMonoid.
Proof.
 apply Build_CMonoid with Build_CSemiGroup' unit.
 apply Build_is_CMonoid.
  exact plus_runit.
 exact plus_lunit.
Defined.

Definition Build_CGroup' : CGroup.
Proof.
 apply Build_CGroup with Build_CMonoid' inv.
 split.
  auto.
 apply inv_inv'.
Defined.

Definition Build_CAbGroup' : CAbGroup.
Proof.
 apply Build_CAbGroup with Build_CGroup'.
 exact plus_comm.
Defined.

End Nice_Char.

(** ** Iteration

For reflection the following is needed; hopefully it is also useful.
*)

Section Group_Extras.

Variable G : CAbGroup.

Fixpoint nmult (a:G) (n:nat) {struct n} : G :=
  match n with
  | O => [0]
  | S p => a[+]nmult a p
  end.

Lemma nmult_wd : forall (x y:G) (n m:nat), (x [=] y) -> n = m -> nmult x n [=] nmult y m.
Proof.
 simple induction n; intros.
  rewrite <- H0; algebra.
 rewrite <- H1; simpl in |- *; algebra.
Qed.

Lemma nmult_one : forall x:G, nmult x 1 [=] x.
Proof.
 simpl in |- *; algebra.
Qed.

Lemma nmult_Zero : forall n:nat, nmult [0] n [=] [0].
Proof.
 intro n.
 induction n.
  algebra.
 simpl in |- *; Step_final (([0]:G)[+][0]).
Qed.

Lemma nmult_plus : forall m n x, nmult x m[+]nmult x n [=] nmult x (m + n).
Proof.
 simple induction m.
  simpl in |- *; algebra.
 clear m; intro m.
 intros.
 simpl in |- *. Step_final (x[+](nmult x m[+]nmult x n)).
Qed.

Lemma nmult_mult : forall n m x, nmult (nmult x m) n [=] nmult x (m * n).
Proof.
 simple induction n.
  intro. rewrite mult_0_r. algebra.
  clear n; intros.
 simpl in |- *.
 rewrite mult_comm. simpl in |- *.
 eapply eq_transitive_unfolded.
  2: apply nmult_plus.
 rewrite mult_comm. algebra.
Qed.

Lemma nmult_inv : forall n x, nmult [--]x n [=] [--] (nmult x n).
Proof.
 intro; induction n; simpl in |- *.
  algebra.
 intros.
 Step_final ([--]x[+] [--](nmult x n)).
Qed.

Lemma nmult_plus' : forall n x y, nmult x n[+]nmult y n [=] nmult (x[+]y) n.
Proof.
 intro; induction n; simpl in |- *; intros.
  algebra.
 astepr (x[+]y[+](nmult x n[+]nmult y n)).
 astepr (x[+](y[+](nmult x n[+]nmult y n))).
 astepr (x[+](y[+]nmult x n[+]nmult y n)).
 astepr (x[+](nmult x n[+]y[+]nmult y n)).
 Step_final (x[+](nmult x n[+](y[+]nmult y n))).
Qed.

Hint Resolve nmult_wd nmult_Zero nmult_inv nmult_plus nmult_plus': algebra.

Definition zmult a z := caseZ_diff z (fun n m => nmult a n[-]nmult a m).

(*
Lemma Zeq_imp_nat_eq : forall m n:nat, m = n -> m = n.
auto.
intro m; induction m.
intro n; induction n; auto.

intro; induction n.
intro. inversion H.
intros.
rewrite (IHm n).
auto.
repeat rewrite inj_S in H.
auto with zarith.
Qed.
*)

Lemma zmult_char : forall (m n:nat) z, z = (m - n)%Z ->
 forall x, zmult x z [=] nmult x m[-]nmult x n.
Proof.
 simple induction z; intros.
   simpl in |- *.
   replace m with n. Step_final ([0]:G). auto with zarith.
    simpl in |- *.
  astepl (nmult x (nat_of_P p)).
  apply cg_cancel_rht with (nmult x n).
  astepr (nmult x m).
  astepl (nmult x (nat_of_P p + n)).
  apply nmult_wd; algebra.
  rewrite <- convert_is_POS in H.
  auto with zarith.
 simpl in |- *.
 astepl [--](nmult x (nat_of_P p)).
 unfold cg_minus in |- *.
 astepr ([--][--](nmult x m)[+] [--](nmult x n)).
 astepr [--]([--](nmult x m)[+]nmult x n).
 apply un_op_wd_unfolded.
 apply cg_cancel_lft with (nmult x m).
 astepr (nmult x m[+] [--](nmult x m)[+]nmult x n).
 astepr ([0][+]nmult x n).
 astepr (nmult x n).
 astepl (nmult x (m + nat_of_P p)).
 apply nmult_wd; algebra.
 rewrite <- min_convert_is_NEG in H.
 auto with zarith.
Qed.

Lemma zmult_wd : forall (x y:G) (n m:Z), (x [=] y) -> n = m -> zmult x n [=] zmult y m.
Proof.
 do 3 intro.
 case n; intros; inversion H0.
   algebra.
  unfold zmult in |- *.
  simpl in |- *.
  astepl (nmult x (nat_of_P p)); Step_final (nmult y (nat_of_P p)).
 simpl in |- *.
 astepl [--](nmult x (nat_of_P p)).
 Step_final [--](nmult y (nat_of_P p)).
Qed.

Lemma zmult_one : forall x:G, zmult x 1 [=] x.
Proof.
 simpl in |- *; algebra.
Qed.

Lemma zmult_min_one : forall x:G, zmult x (-1) [=] [--]x.
Proof.
 intros; simpl in |- *; Step_final ([0][-]x).
Qed.

Lemma zmult_zero : forall x:G, zmult x 0 [=] [0].
Proof.
 simpl in |- *; algebra.
Qed.

Lemma zmult_Zero : forall k:Z, zmult [0] k [=] [0].
Proof.
 intro; induction k; simpl in |- *.
   algebra.
  Step_final (([0]:G)[-][0]).
 Step_final (([0]:G)[-][0]).
Qed.

Hint Resolve zmult_zero: algebra.

Lemma zmult_plus : forall m n x, zmult x m[+]zmult x n [=] zmult x (m + n).
Proof.
 intros; case m; case n; intros.
         simpl in |- *; Step_final ([0][+]([0][-][0]):G).
        simpl in |- *; Step_final ([0][+](nmult x (nat_of_P p)[-][0])).
       simpl in |- *; Step_final ([0][+]([0][-]nmult x (nat_of_P p))).
      simpl in |- *; Step_final (nmult x (nat_of_P p)[-][0][+][0]).
     simpl in |- *.
     astepl (nmult x (nat_of_P p0)[+]nmult x (nat_of_P p)).
     astepr (nmult x (nat_of_P (p0 + p))).
     rewrite nat_of_P_plus_morphism. apply nmult_plus.
     simpl (zmult x (Zpos p0)[+]zmult x (Zneg p)) in |- *.
    astepl (nmult x (nat_of_P p0)[+] [--](nmult x (nat_of_P p))).
    astepl (nmult x (nat_of_P p0)[-]nmult x (nat_of_P p)).
    apply eq_symmetric_unfolded; apply zmult_char with (z := (Zpos p0 + Zneg p)%Z).
    rewrite convert_is_POS. unfold Zminus in |- *. rewrite min_convert_is_NEG; auto.
    rewrite <- Zplus_0_r_reverse. Step_final (zmult x (Zneg p)[+][0]).
   simpl (zmult x (Zneg p0)[+]zmult x (Zpos p)) in |- *.
  astepl ([--](nmult x (nat_of_P p0))[+]nmult x (nat_of_P p)).
  astepl (nmult x (nat_of_P p)[+] [--](nmult x (nat_of_P p0))).
  astepl (nmult x (nat_of_P p)[-]nmult x (nat_of_P p0)).
  rewrite Zplus_comm.
  apply eq_symmetric_unfolded; apply zmult_char with (z := (Zpos p + Zneg p0)%Z).
  rewrite convert_is_POS. unfold Zminus in |- *. rewrite min_convert_is_NEG; auto.
  simpl in |- *.
 astepl ([--](nmult x (nat_of_P p0))[+] [--](nmult x (nat_of_P p))).
 astepl [--](nmult x (nat_of_P p0)[+]nmult x (nat_of_P p)).
 astepr [--](nmult x (nat_of_P (p0 + p))).
 apply un_op_wd_unfolded.
 rewrite nat_of_P_plus_morphism. apply nmult_plus.
Qed.

Lemma zmult_mult : forall m n x, zmult (zmult x m) n [=] zmult x (m * n).
Proof.
 simple induction m; simple induction n; simpl in |- *; intros.
         Step_final ([0][-][0][+]([0]:G)).
        astepr ([0]:G). astepl (nmult ([0][-][0]) (nat_of_P p)).
        Step_final (nmult [0] (nat_of_P p)).
       astepr [--]([0]:G). astepl [--](nmult ([0][-][0]) (nat_of_P p)).
       Step_final [--](nmult [0] (nat_of_P p)).
      algebra.
     astepr (nmult x (nat_of_P (p * p0))).
     astepl (nmult (nmult x (nat_of_P p)) (nat_of_P p0)[-][0]).
     astepl (nmult (nmult x (nat_of_P p)) (nat_of_P p0)).
     rewrite nat_of_P_mult_morphism. apply nmult_mult.
     astepr [--](nmult x (nat_of_P (p * p0))).
    astepl ([0][-]nmult (nmult x (nat_of_P p)) (nat_of_P p0)).
    astepl [--](nmult (nmult x (nat_of_P p)) (nat_of_P p0)).
    rewrite nat_of_P_mult_morphism. apply un_op_wd_unfolded. apply nmult_mult.
    algebra.
  astepr [--](nmult x (nat_of_P (p * p0))).
  astepl (nmult [--](nmult x (nat_of_P p)) (nat_of_P p0)[-][0]).
  astepl (nmult [--](nmult x (nat_of_P p)) (nat_of_P p0)).
  rewrite nat_of_P_mult_morphism. eapply eq_transitive_unfolded.
  apply nmult_inv. apply un_op_wd_unfolded. apply nmult_mult.
  astepr (nmult x (nat_of_P (p * p0))).
 astepr [--][--](nmult x (nat_of_P (p * p0))).
 astepl ([0][-]nmult [--](nmult x (nat_of_P p)) (nat_of_P p0)).
 astepl [--](nmult [--](nmult x (nat_of_P p)) (nat_of_P p0)).
 rewrite nat_of_P_mult_morphism. apply un_op_wd_unfolded. eapply eq_transitive_unfolded.
 apply nmult_inv. apply un_op_wd_unfolded. apply nmult_mult.
Qed.

Lemma zmult_plus' : forall z x y, zmult x z[+]zmult y z [=] zmult (x[+]y) z.
Proof.
 intro z; pattern z in |- *.
 apply nats_Z_ind.
  intro n; case n.
   intros; simpl in |- *. Step_final (([0]:G)[+]([0][-][0])).
   clear n; intros.
  rewrite POS_anti_convert; simpl in |- *. set (p := nat_of_P (P_of_succ_nat n)) in *.
  astepl (nmult x p[+]nmult y p). Step_final (nmult (x[+]y) p).
  intro n; case n.
  intros; simpl in |- *. Step_final (([0]:G)[+]([0][-][0])).
  clear n; intros.
 rewrite NEG_anti_convert; simpl in |- *. set (p := nat_of_P (P_of_succ_nat n)) in *.
 astepl ([--](nmult x p)[+] [--](nmult y p)). astepr [--](nmult (x[+]y) p).
 Step_final [--](nmult x p[+]nmult y p).
Qed.

End Group_Extras.

Hint Resolve nmult_wd nmult_one nmult_Zero nmult_plus nmult_inv nmult_mult
  nmult_plus' zmult_wd zmult_one zmult_min_one zmult_zero zmult_Zero
  zmult_plus zmult_mult zmult_plus': algebra.

Implicit Arguments nmult [G].
Implicit Arguments zmult [G].
