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

Require Import Lia.
Require Export CoRN.algebra.CMonoids.
Require Export CoRN.model.monoids.Nmonoid.

Section p71E1.

(**
** A function from the natural numbers to a cyclic monoid
%\begin{convention}%
Let [M:CMonoid], [c:M] and
[is_generated_by: forall(m:M),{n:nat | (power_CMonoid c n)[=]m}].
%\end{convention}%
*)

Variable M:CMonoid.
Variable c:M.

Definition power_CMonoid_CSetoid: M-> nat_as_CSetoid -> M.
Proof.
 simpl.
 exact (@power_CMonoid M).
Defined.

Variable is_generated_by: forall(m:M),{n:nat | (power_CMonoid c n)[=]m}.

Let f:= fun (H:forall(m:M),{n:nat | (power_CMonoid c n)[=]m})=>
  fun (n:nat_as_CMonoid)=> power_CMonoid c n.

Lemma f_strext: (fun_strext (f is_generated_by)).
Proof.
 unfold fun_strext; simpl.
 induction x; destruct y.
 - intros ? ?.
   pose proof (ax_ap_irreflexive M (@cs_eq  M) (@cs_ap M)) as H_irreflexive.
   unfold irreflexive, Not in H_irreflexive.
   elim H_irreflexive with (cm_unit M); auto using CSetoid_is_CSetoid.
 - firstorder lia.
 - firstorder lia.
 - unfold f.
   simpl.
   elim (@csg_op M).
   simpl.
   intros op op_strext H1.
   pose proof (op_strext c c (power_CMonoid c _) (power_CMonoid c _) H1) as [ H3 | ].
   + destruct (ap_irreflexive_unfolded M c H3).
   + firstorder.
Qed.

Definition f_as_CSetoid_fun:=
(Build_CSetoid_fun nat_as_CMonoid M (f is_generated_by) f_strext).

Lemma surjective_f: (surjective f_as_CSetoid_fun).
Proof.
 unfold surjective.
 simpl.
 intro b.
 elim (is_generated_by b).
 intros m H.
 exists m.
 unfold f.
 exact H.
Qed.

End p71E1.
