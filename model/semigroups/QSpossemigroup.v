(* $Id: QSpossemigroup.v,v 1.5 2004/04/08 08:20:35 lcf Exp $ *)

Require Export Qpossetoid.
Require Import CSemiGroups.

(** **Example of a semi-group: $\langle$#&lang;#[Qpos],$(x,y) \mapsto xy/2$#(x,y) &#x21A6; xy/2#$\rangle$#&rang;#
The positive rationals form with the operation
$(x,y) \mapsto xy/2$#(x,y) &#x21A6; xy/2# a CSemiGroup.
*)

Definition Qpos_multdiv2_as_CSemiGroup := Build_CSemiGroup
 Qpos multdiv2 associative_multdiv2.
