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
Require Export FieldReflection.
Require Export RingReflection.
Require Export CRing_as_Ring.

Inductive AlgebraName : Type :=
|cfield : CField -> AlgebraName
|cring : CRing -> AlgebraName.

Ltac GetStructureName t :=
match t with
| (csg_crr (cm_crr (cg_crr (cag_crr (cr_crr ?r))))) =>
  match r with
  | (cf_crr ?q) => constr:(cfield q)
  | _ => constr:(cring r)
 end
end.

Ltac legacy_rational:=
match goal with
[|-@cs_eq (cs_crr ?T) ?x ?y] =>
 match GetStructureName T with
 |(cfield ?F) => rationalF F x y
 |(cring ?R) => rationalR R x y
 end
end.

Ltac rational :=
match goal with
[|-@cs_eq (cs_crr ?T) ?x ?y] =>
 match GetStructureName T with
 |(cfield ?F) => rationalF F x y
 |(cring ?R) => (repeat (try apply csf_fun_wd);simpl;ring)
(*
 |(cring ?R) => (try (repeat (try apply csf_fun_wd);simpl;ring));rationalR R x y
*)(* Perhaps we should add wd for partial functions too *)
 end
end.

Tactic Notation "rstepl" constr(c) :=  stepl c;[idtac|rational].
Tactic Notation "rstepr" constr(c) :=  stepr c;[idtac|rational].
