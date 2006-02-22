(* $Id: Zabgroup.v,v 1.5 2004/04/08 08:20:32 lcf Exp $ *)


Require Export Zgroup.
Require Import CAbGroups.

(** **Example of an abelian group: $\langle$#&lang;#[Z],[[+]]$\rangle$#&rang;#
*)

Lemma Z_is_CAbGroup : is_CAbGroup Z_as_CGroup. 
Proof.
red in |- *.
simpl in |- *.
exact Zplus_is_commut.
Qed.

Definition Z_as_CAbGroup := Build_CAbGroup Z_as_CGroup Z_is_CAbGroup.

(** The term [Z_as_CAbGroup] is of type [CAbGroup]. Hence we have proven that [Z] is a constructive Abelian group. *)
