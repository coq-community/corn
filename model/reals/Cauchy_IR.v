(* $Id: Cauchy_IR.v,v 1.2 2004/04/06 15:46:03 lcf Exp $ *)

Require Export Qordfield.
Require Export Cauchy_CReals.

(** * Cauchy Real Numbers
Earlier we defined a construction of a real number structure from an
arbitrary archimedian ordered field.  Plugging in [Q] we get the model
of the real numbers as Cauchy sequences of rationals.
*)

Definition Cauchy_IR : CReals := R_as_CReals _ Q_is_archemaedian.

(** The term [Cauchy_IR] is of type [CReals]. *)
