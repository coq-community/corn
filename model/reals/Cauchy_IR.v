(* $Id$ *)


Require Export Qordfield.
Require Export Cauchy_CReals.

(**
* Cauchy Real Numbers

  In [Cauchy_Creals], we defined a construction of a real number structure from an arbitrary archimedian ordered field.  Plugging in [QQ] from [Fraction_Rat] we 
get the model of the real numbers as Cauchy sequences of rationals.
*)

Definition Cauchy_IR : CReals := R_as_CReals Q_as_COrdField Q_is_archemaedian.

(** The term [Cauchy_IR] is of type [CReals]. *)
