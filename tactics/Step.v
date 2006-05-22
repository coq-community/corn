(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* begin hide *)
Declare ML Module "rational".

Ltac Algebra := auto with algebra_r algebra algebra_c algebra_s.

Ltac astepl x := stepl x; [idtac | Algebra].

Ltac astepr x := stepr x; [idtac | Algebra].

Tactic Notation "astepl" constr(c) :=  astepl c.

Tactic Notation "astepr" constr(c) :=  astepr c.

Ltac rstepl x := stepl x; [idtac | rational].

Ltac rstepr x := stepr x; [idtac | rational].

Tactic Notation "rstepl" constr(c) :=  rstepl c.

Tactic Notation "rstepr" constr(c) :=  rstepr c.

Ltac Included := eauto with included.

(* end hide *)

(** * [algebra] and [step]
These tactics simplify equational reasoning.  See the references for a
description.

* [Included]
[Included] will solve goals of the form [(included A (dom F))].
*)
