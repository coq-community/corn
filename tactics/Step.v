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
