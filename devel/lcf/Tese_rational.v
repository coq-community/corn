Require Export COrdFields.

Section test.

Variable R:COrdField.

Variable F:(PartFunct R).
Variable x:R.
Hypothesis Hx1 : (Dom F x).
Hypothesis Hx2 : (Dom F (x[/]TwoNZ[+]x[/]TwoNZ)).
Hypothesis Hx3 : (Dom F (Two[*]x)).
Hypothesis Hx4 : (Dom F (x[+]x)).

Goal F x Hx1 [=] F _ Hx2.
(* rational verbose. *)
Abort.

Goal F _ Hx3 [=] F _ Hx4.
(* rational verbose. *)
Abort.

End test.
