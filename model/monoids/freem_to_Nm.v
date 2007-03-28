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
Require Export Nmonoid.

Section p71E2.

(** **A morphism from a free monoid to the natural numbers
%\begin{convention}%
Let [A:CSetoid].
%\end{convention}%
*) 

Variable A:CSetoid.

Let L: (free_monoid_as_CMonoid A)-> nat_as_CMonoid.
simpl.
unfold Astar.
intros l.
exact (length l).
Defined.

Lemma L_strext: (fun_strext L).
simpl.
unfold fun_strext.
simpl.
unfold Astar.
intros x.
induction x.
intro y.
case y.
simpl.
unfold ap_nat.
unfold CNot.
intuition.

simpl.
intuition.

intro y.
case y.
simpl.
intuition.

simpl.
intros c l H.
right.
apply IHx.
unfold ap_nat in H |- *.
unfold CNot in H |- *.
intuition.
Qed.

Definition L_as_CSetoid_fun:=
(Build_CSetoid_fun _ _ L L_strext).

Lemma L_is_morphism: (morphism _ _ L_as_CSetoid_fun).
unfold morphism.
simpl.
split.
reflexivity.

unfold Astar.
intros a.
induction a.
simpl.
reflexivity.

simpl.
intuition.
Qed.

End p71E2.
