
Require Export Nsemigroup.
Require Import CMonoids.

(** **Example of a monoid: $\langle$#&lang;#[nat],[[+]]$\rangle$#&rang;#
Zero is an unit for the addition.
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

Definition nat_is_CMonoid := Build_is_CMonoid
 nat_as_CSemiGroup _ O_as_rht_unit O_as_lft_unit.

(**
 Whence we can define #<i>#%\emph{%the monoid of natural numbers%}%#</i>#:
*)

Definition nat_as_CMonoid := Build_CMonoid nat_as_CSemiGroup _ nat_is_CMonoid. 

Lemma SO_as_rht_unit : is_rht_unit (S:=nat_as_CSetoid) mult_as_bin_fun 1.
Proof.
red in |- *.
simpl.
auto with arith.
Qed.

Lemma SO_as_lft_unit : is_lft_unit (S:=nat_as_CSetoid) mult_as_bin_fun 1.
Proof.
red in |- *.
simpl.
auto with arith.
Qed.

Print plus_is_bin_fun.
Print mult_as_bin_fun.

Definition Nmult_is_CMonoid := Build_is_CMonoid
 Nmult_as_CSemiGroup _ SO_as_rht_unit SO_as_lft_unit.

Definition Nmult_as_CMonoid := Build_CMonoid Nmult_as_CSemiGroup _ Nmult_is_CMonoid.
