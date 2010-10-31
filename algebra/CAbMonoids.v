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
Require Export CMonoids.

Require Import SetoidPermutation Setoid Morphisms.

Section Abelian_Monoids.

(**
* Abelian Monoids
Now we introduce commutativity and add some results.
*)

Definition is_CAbMonoid (G : CMonoid) := commutes (csg_op (c:=G)).

Record CAbMonoid : Type :=
 {cam_crr   :> CMonoid;
  cam_proof :  is_CAbMonoid cam_crr}.

Section AbMonoid_Axioms.

Variable M : CAbMonoid.
(**
%\begin{convention}% Let [M] be an abelian monoid.
%\end{convention}%
*)

Lemma CAbMonoid_is_CAbMonoid : is_CAbMonoid M.
Proof.
 elim M; auto.
Qed.

Lemma cam_commutes : commutes (csg_op (c:=M)).
Proof.
 exact CAbMonoid_is_CAbMonoid.
Qed.

Lemma cam_commutes_unfolded : forall x y : M, x[+]y [=] y[+]x.
Proof cam_commutes.

End AbMonoid_Axioms.

Global Instance cm_Sum_AbMonoid_Proper: forall {M: CAbMonoid},
 Proper (SetoidPermutation (@st_eq M) ==> @st_eq M) cm_Sum.
Proof.
 repeat intro.
 apply cm_Sum_Proper.
  apply cam_proof.
 assumption.
Qed.

Section SubCAbMonoids.

(**
** Subgroups of an Abelian Monoid
*)
Variable M : CAbMonoid.
Variable P : M -> CProp.
Variable Punit : P Zero.
Variable op_pres_P : bin_op_pres_pred _ P csg_op.

(**
%\begin{convention}%
Let [M] be an Abelian Monoid and [P] be a ([CProp]-valued) predicate on [M]
that contains [Zero] and is closed under [[+]] and [[--]].
%\end{convention}%
*)

Let subcrr : CMonoid := Build_SubCMonoid _ _ Punit op_pres_P.

Lemma isabgrp_scrr : is_CAbMonoid subcrr.
Proof.
 red in |- *. intros x y. case x. case y. intros.
 simpl in |- *. apply cam_commutes_unfolded.
Qed.

Definition Build_SubCAbMonoid : CAbMonoid := Build_CAbMonoid _ isabgrp_scrr.

End SubCAbMonoids.

End Abelian_Monoids.

Hint Resolve cam_commutes_unfolded: algebra.
