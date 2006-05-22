(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


Require Export COrdFields2.

(**
** Properties of [AbsSmall]
*)

(* Begin_SpecReals *)

Definition AbsSmall (R : COrdField) (e x : R) : Prop := [--]e [<=] x /\ x [<=] e.

Implicit Arguments AbsSmall [R].

(* End_SpecReals *)

Section AbsSmall_properties.

(**
%\begin{convention}% Let [R] be an ordered field.
%\end{convention}%
*)
Variable R : COrdField.

Lemma AbsSmall_wdr : rel_wdr R (AbsSmall (R:=R)).
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
Notation ZeroR := (Zero:R).
(* end hide *)

Lemma AbsSmall_leEq_trans : forall e1 e2 d : R,
 e1 [<=] e2 -> AbsSmall e1 d -> AbsSmall e2 d.
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

Lemma zero_AbsSmall : forall e : R, Zero [<=] e -> AbsSmall e Zero.
intros.
unfold AbsSmall in |- *.
split.
astepr ([--]ZeroR).
apply inv_resp_leEq.
assumption.
assumption.
Qed.

Lemma AbsSmall_trans : forall e1 e2 d : R,
 e1 [<] e2 -> AbsSmall e1 d -> AbsSmall e2 d.
intros.
apply AbsSmall_leEq_trans with e1.
apply less_leEq.
assumption.
assumption.
Qed.

Lemma leEq_imp_AbsSmall : forall e d : R, Zero [<=] e -> e [<=] d -> AbsSmall d e.
intros.
unfold AbsSmall in |- *.
split; try assumption.
apply leEq_transitive with ZeroR; try assumption.
astepr ([--]ZeroR).
apply inv_resp_leEq.
apply leEq_transitive with e; assumption.
Qed.

Lemma inv_resp_AbsSmall : forall x y : R, AbsSmall x y -> AbsSmall x [--]y.
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

Lemma AbsSmall_minus : forall e x1 x2 : R, AbsSmall e (x1[-]x2) -> AbsSmall e (x2[-]x1).
intros.
rstepr ([--](x1[-]x2)).
apply inv_resp_AbsSmall.
assumption.
Qed.

Lemma AbsSmall_plus : forall e1 e2 x1 x2 : R,
 AbsSmall e1 x1 -> AbsSmall e2 x2 -> AbsSmall (e1[+]e2) (x1[+]x2).
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
intros.
rstepl (e [/]TwoNZ[+]e [/]TwoNZ).
apply AbsSmall_plus.
assumption.
assumption.
Qed.

Lemma AbsSmall_x_plus_delta : forall x eps delta : R,
 Zero [<=] eps -> Zero [<=] delta -> delta [<=] eps -> AbsSmall eps (x[-] (x[+]delta)).
intros.
(* astepr ((x[-]x)[-]delta).
astepr (Zero[-]delta). *)
rstepr ([--]delta).
apply inv_resp_AbsSmall.
apply leEq_imp_AbsSmall.
assumption.
assumption.
Qed.

Lemma AbsSmall_x_minus_delta : forall x eps delta : R,
 Zero [<=] eps -> Zero [<=] delta -> delta [<=] eps -> AbsSmall eps (x[-] (x[-]delta)).
intros.
(* astepr ((x[-]x)[+]delta).
   astepr (Zero[+]delta). *)
rstepr delta.
apply leEq_imp_AbsSmall.
assumption.
assumption.
Qed.

Lemma AbsSmall_x_plus_eps_div2 : forall x eps : R, Zero [<=] eps -> AbsSmall eps (x[-] (x[+]eps [/]TwoNZ)).
intros.
apply AbsSmall_x_plus_delta.
assumption.

apply nonneg_div_two.
assumption.

apply nonneg_div_two'.
assumption.
Qed.

Lemma AbsSmall_x_minus_eps_div2 : forall x eps : R, Zero [<=] eps -> AbsSmall eps (x[-] (x[-]eps [/]TwoNZ)).
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

Lemma AbsSmall_eps_div2 : forall eps : R, Zero [<=] eps -> AbsSmall eps (eps [/]TwoNZ).
intros.
apply leEq_imp_AbsSmall.
apply nonneg_div_two.
assumption.

apply eps_div_leEq_eps.
assumption.

apply less_leEq.
apply one_less_two.
Qed.

Lemma AbsSmall_nonneg : forall e x : R, AbsSmall e x -> Zero [<=] e.
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
 unfold AbsSmall in |- *.
 intros.
 elim H.
 intros.
 elim H0.
 intros.
 cut (Zero [<=] e1).
 intro.
 cut (Zero [<=] e2).
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
 apply
  leEq_transitive with (y := [--](x1[*]x2)[+]e1[*]e2[+](x1[*]e2[-]e1[*]x2)).
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
 Zero [<] z -> AbsSmall (e[*]z) (x[*]z) -> AbsSmall e x.
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

Lemma AbsSmall_approach_zero : forall x : R, (forall e, Zero [<] e -> AbsSmall e x) -> x [=] Zero.
Proof.
 intros.
 apply not_ap_imp_eq.
 intro H0.
 elim (ap_imp_less _ _ _ H0).
 change (Zero [<=] x) in |- *.
 apply inv_cancel_leEq.
 astepr ZeroR.
 red in |- *; apply approach_zero_weak.
 intros.
 apply inv_cancel_leEq; astepr x.
 elim (H e); auto.

 change (x [<=] Zero) in |- *.
 red in |- *; apply approach_zero_weak.
 intros.
 elim (H e); auto.
Qed.

End AbsSmall_properties.

Declare Left Step AbsSmall_wdl_unfolded.
Declare Right Step AbsSmall_wdr_unfolded.

(** ** Properties of [AbsBig] *)

Definition absBig (R : COrdField) (e x : R) : CProp :=
 Zero [<] e and (e [<=] x or x [<=] [--]e).

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
