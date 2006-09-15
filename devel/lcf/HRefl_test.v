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

Require Export GroupReflection.
Require Export CFields.

Section Rtest.
Variable G : CAbGroup.
Variable f : CSetoid_un_op G.
Variable g : CSetoid_bin_op G.
Variables a b c : G.

Goal f (a[+]b)[=]f (b[+]a).
rational.
Abort.

Goal
f (a[+]b)[+]g c (a[-]b)[=][--][--](g (Zero[+]c) ([--]b[+]a))[+]f (b[+]a).
rational.
Abort.

End Rtest.

Require Export RingReflection.

Section Rtest2.
Variable R : CRing.
Variable f : CSetoid_un_op R.
Variable g : CSetoid_bin_op R.
Variables a b c : R.

Goal f (a[*]b)[=]f (b[*]a).
rational.
Abort.

Goal
f (a[+]b)[*]g (c[^]1) (a[-]b)[=]
[--][--](g (Zero[+]c) ([--]b[+]a))[*]f (b[+]a)[*]One.
rational.
Abort.

End Rtest2.

Require Export COrdFields.

Section Rtest3.
Variable F : COrdField.
Variable f : CSetoid_un_op F.
Variable g : CSetoid_bin_op F.
Variables a b c : F.

Goal f (a[*]b [/]OneNZ)[=]f (b[*]a).
rational.
Abort.

Goal Two [/]TwoNZ[=](One:F).
rational.
Abort.

Goal Two [/]TwoNZ[+]Zero[*]a[=]One.
rational.
Abort.


Goal
f (a[+]b)[*]g (c[^]1) (a[-]b)[=]
[--][--](g (Zero[+]c) ([--]b[+]a))[*]f (b[+]a) [/]OneNZ.
rational.
Abort.

End Rtest3.

Section Rtest4.
Variable R : CRing.
Variable F : CField.
Variable f : CSetoid_fun R F.
Variables x y : R.
Variable z : F.

Goal f (x[+]y)[+]z[=]z[+]f (x[+]y).
rational.
Abort.

End Rtest4.

Section Rtest5.
Variable F : CField.
Variable f : CSetoid_un_op F.
Variables x y : F.
Variable z : F.

Goal f (x[*]y)[*]z[=]z[*]f (y[*]x).
rational.
Abort.

End Rtest5.
