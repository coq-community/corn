(* $Id$ *)

Require Export Qpossetoid.
Require Import CSemiGroups.

(** *Example of a semi-group: <$\mathbb{Q}^{+}$ #Q<SUP>+</SUP>#,$(x,y) \mapsto xy/2$ #(x,y) &#x21A6; xy/2#>
*)

(** The positive rationals form with the operation  $(x,y) \mapsto xy/2$ 
#(x,y) &#x21A6; xy/2# a CSemiGroup.
*)

Definition Qpos_multdiv2_as_CSemiGroup :=
  Build_CSemiGroup Qpos multdiv2 associative_multdiv2.
