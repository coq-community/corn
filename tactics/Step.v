(* begin hide *)
Declare ML Module "rational".
Declare ML Module "step".

Ltac Algebra := auto with algebra_r algebra algebra_c algebra_s.

Ltac AStepl x := stepl x Algebra.

Ltac AStepr x := stepr x Algebra.

Tactic Notation "AStepl" constr(c) :=  AStepl c.

Tactic Notation "AStepr" constr(c) :=  AStepr c.

Ltac RStepl x := stepl x rational.

Ltac RStepr x := stepr x rational.

Tactic Notation "RStepl" constr(c) :=  RStepl c.

Tactic Notation "RStepr" constr(c) :=  RStepr c.

(* end hide *)
