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
Require Export CSetoidFun.

Section move_us.

Lemma csr_wd :
 forall (S:CSetoid) (R:CSetoid_relation S) (x1 x2 y1 y2:S),
   R x1 x2 -> (x1[=]y1) -> (x2[=]y2) -> R y1 y2.
Proof
  fun S R x1 x2 y1 y2 h h0 h1 =>
    csr_wdl S R x1 y2 y1 (csr_wdr S R x1 x2 y2 h h1) h0.

Lemma Ccsr_wd :
 forall (S:CSetoid) (R:CCSetoid_relation S) (x1 x2 y1 y2:S),
   R x1 x2 -> (x1[=]y1) -> (x2[=]y2) -> R y1 y2.
Proof
  fun S R x1 x2 y1 y2 h h0 h1 =>
    Ccsr_wdl S R x1 y2 y1 (Ccsr_wdr S R x1 x2 y2 h h1) h0.

Lemma eq_wd :
 forall (S:CSetoid) (x1 x2 y1 y2:S),
   (x1[=]x2) -> (x1[=]y1) -> (x2[=]y2) -> y1[=]y2.
Proof
  fun S x1 x2 y1 y2 h h0 h1 =>
    eq_transitive S y1 x1 y2 (eq_symmetric S x1 y1 h0)
      (eq_transitive S x1 x2 y2 h h1).

Lemma ap_wd :
 forall (S:CSetoid) (x1 x2 y1 y2:S),
   (x1[#]x2) -> (x1[=]y1) -> (x2[=]y2) -> y1[#]y2.
Proof
  fun S x1 x2 y1 y2 h h0 h1 =>
    ap_wdl S x1 y2 y1 (ap_wdr S x1 x2 y2 h h1) h0.

Lemma COr_elim : forall A B C:CProp, (A -> C) -> (B -> C) -> A or B -> C.
intros A B C H H0 H1.
elim H1; intro H2; [ exact (H H2) | exact (H0 H2) ].
Qed.

End move_us.
