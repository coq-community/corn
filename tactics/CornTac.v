(* Copyright © 2006
 * Russell O’Connor
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

(** Generic Tacticals used by the CoRN project *)
(* begin hide *)

Require Import SetoidTactics.

(* Replace the LHS or RHS of an expression with another expression
  This tactic along with the setiod functionality, basically replaces the step
  tactic *)

Tactic Notation "replace" "LHS" "with" constr (a) "by" tactic (t) :=
match goal with
| |-(?r ?b ?c) =>
  let Z := fresh "Z" in
  (change (let Z:=b in r Z c);intro Z;setoid_replace Z with a;
   [unfold Z; clear Z|unfold Z; clear Z; solve [ t ]])
end.

Tactic Notation "replace" "LHS" "with" constr (a) :=
match goal with
| |-(?r ?b ?c) =>
  let Z := fresh "Z" in
  (change (let Z:=b in r Z c);intro Z;setoid_replace Z with a;
   unfold Z; clear Z)
end.

Tactic Notation "replace" "RHS" "with" constr (a) "by" tactic (t) :=
match goal with
| |-(?r ?b ?c) =>
  let Z := fresh "Z" in
  (change (let Z:=c in r b Z);intro Z;setoid_replace Z with a;
   [unfold Z; clear Z|unfold Z; clear Z; solve [ t ]])
end.

Tactic Notation "replace" "RHS" "with" constr (a) :=
match goal with
| |-(?r ?b ?c) =>
  let Z := fresh "Z" in
  (change (let Z:=c in r b Z);intro Z;setoid_replace Z with a;
   unfold Z; clear Z)
end.
(*end hide*)
