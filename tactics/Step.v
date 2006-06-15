(* begin hide *)
Ltac algebra := auto with algebra_r algebra algebra_c algebra_s.

Ltac astepl x := stepl x; [idtac | algebra].

Ltac astepr x := stepr x; [idtac | algebra].

Tactic Notation "astepl" constr(c) :=  astepl c.

Tactic Notation "astepr" constr(c) :=  astepr c.

Ltac Included := eauto with included.
