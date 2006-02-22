(* begin hide *)
Ltac Algebra := auto with algebra_r algebra algebra_c algebra_s.

Ltac astepl x := stepl x; [idtac | Algebra].

Ltac astepr x := stepr x; [idtac | Algebra].

Tactic Notation "astepl" constr(c) :=  astepl c.

Tactic Notation "astepr" constr(c) :=  astepr c.

Ltac Included := eauto with included.
