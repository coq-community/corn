(* $Id$ *)

Require Export Nsemigroup.
Require Import CMonoids.

(** *Example of a monoid: <N,+>
*)

(** Zero is an unit for the addition.
*)

Lemma O_as_rht_unit : is_rht_unit (S:=nat_as_CSetoid) plus_is_bin_fun 0.
Proof.
red in |- *.
simpl in |- *.
intro x.
symmetry  in |- *.
apply plus_n_O.
Qed.

Lemma O_as_lft_unit : is_lft_unit (S:=nat_as_CSetoid) plus_is_bin_fun 0.
Proof.
red in |- *.
simpl in |- *.
intro x.
reflexivity.
Qed.

Definition nat_is_CMonoid :=
  Build_is_CMonoid nat_as_CSemiGroup _ O_as_rht_unit O_as_lft_unit.

(**
 Whence we can define #<i>#%\emph{%the monoid of natural numbers%}%#</i>#:
*)

Definition nat_as_CMonoid := Build_CMonoid nat_as_CSemiGroup _ nat_is_CMonoid. 
