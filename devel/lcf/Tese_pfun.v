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

(** Alternative definitions of partial functions *)

Require Export CSetoidFun.

Record PartFunct' (S : CSetoid) : Type := 
  {dom : S -> CProp;
   dom_wd : pred_wd _ dom;
   fun_ :> CSetoid_fun (Build_SubCSetoid S dom) S}.

Definition map1 (S : CSetoid) : PartFunct S -> PartFunct' S.
intros S F.
inversion F.
apply Build_PartFunct' with pfdom.
auto.
apply
 Build_CSetoid_fun
  with
    (fun x : Build_SubCSetoid S pfdom =>
     pfpfun (scs_elem _ _ x) (scs_prf _ _ x)).
red in |- *; intros x y.
case x; case y; simpl in |- *; intros.
eauto.
Defined.

Definition map2 (S : CSetoid) : PartFunct' S -> PartFunct S.
intros S F.
inversion F.
inversion fun_0.
apply
 Build_PartFunct
  with
    dom0
    (fun (x : S) (Hx : dom0 x) => csf_fun (Build_subcsetoid_crr _ _ x Hx)).
auto.
intros.
apply (csf_strext _ _ X).
Qed.
