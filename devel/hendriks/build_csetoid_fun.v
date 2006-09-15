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
Require Export CSetoids.

Ltac trivi H :=
  exact H ||  ( left; exact H ) || ( right; exact H ).

Ltac prove_strong_ext :=
  let H := fresh "H" in
  (
  match goal with
  | id : (cs_ap (csbf_fun _ _ _ ?f _ _) (csbf_fun _ _ _ ?f _ _)) |- _ =>
      elim (csbf_strext _ _ _ f _ _ _ _ id); clear id; intro H;
      trivi H || prove_strong_ext
  | id : (cs_ap (csf_fun _ _ ?f _) (csf_fun _ _ ?f _)) |- _ =>
      assert (H := (csf_strext _ _ f _ _ id)); clear id;
      trivi H || prove_strong_ext
  end
  ).

Ltac build_csetoid_un_fun f :=
  let x := fresh "x" in
  let y := fresh "y" in
  let H  := fresh "H" in
  apply Build_CSetoid_fun with (csf_fun:=f);
  intros x y H;
  exact H || prove_strong_ext.

Ltac build_csetoid_bin_fun f :=
  let x1 := fresh "x" in
  let x2 := fresh "x" in
  let y1 := fresh "y" in
  let y2 := fresh "y" in
  let H  := fresh "H" in
  apply Build_CSetoid_bin_fun with (csbf_fun:=f);
  intros x1 x2 y1 y2 H;
  trivi H || prove_strong_ext.

Ltac build_csetoid_fun' f :=
  let F := type of f in
  match F with
  | ?S1 -> ?S2 -> ?S3 => build_csetoid_bin_fun f
  | ?S1 -> ?S2        => build_csetoid_un_fun f
  | _                 => fail "sorry"
  end.

(* try to unfold f *)
Ltac build_csetoid_fun f :=
  ( 
  let f' := ( eval unfold f in f ) in
  build_csetoid_fun' f'
  )
  ||
  build_csetoid_fun' f.
