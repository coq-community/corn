(* begin hide *)
Ltac Contin := auto with continuous included.
Ltac Deriv := eauto with derivate continuous included.
(* end hide *)

(** *Search tactics for reasoning in Real Analysis

The following tactics are defined:
 - [Contin] will solve [(Continuous_I H F)]
 - [Deriv] will solve [(Derivative_I H F F')].

All these tactics are defined using [eauto].
*)
