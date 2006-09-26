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
Require Export COrdFields.

Section test.

Variable R:COrdField.

Variable F:(PartFunct R).
Variable x:R.
Hypothesis Hx1 : (Dom F x).
Hypothesis Hx2 : (Dom F (x[/]TwoNZ[+]x[/]TwoNZ)).
Hypothesis Hx3 : (Dom F (Two[*]x)).
Hypothesis Hx4 : (Dom F (x[+]x)).

Goal F x Hx1 [=] F _ Hx2.
(* rational verbose. *)
Abort.

Goal F _ Hx3 [=] F _ Hx4.
(* rational verbose. *)
Abort.

End test.
