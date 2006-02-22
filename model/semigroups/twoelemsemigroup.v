(* $Id: twoelemsemigroup.v,v 1.1 2004/09/22 11:06:14 loeb Exp $ *)

Require Export CSemiGroups.
Require Export twoelemsetoid.

Section p68E1b1.

(** **Example of a semigroup: semigroups with two elements
*)

Lemma M1_is_CSemiGroup:(is_CSemiGroup M1_as_CSetoid M1_mult_as_bin_fun).
unfold is_CSemiGroup.
unfold associative.
simpl.
unfold M1_CS_mult.
intros x y z.
case x.
case y.
case z.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.

case z.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.

case y.
case z.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.

case z.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.
Qed.

Lemma e1_is_lft_unit: (is_lft_unit M1_mult_as_bin_fun e1).
unfold is_lft_unit.
simpl.
unfold M1_eq.
reflexivity.
Qed.

Lemma e1_is_rht_unit:(is_rht_unit M1_mult_as_bin_fun e1).
unfold is_rht_unit.
simpl.
unfold M1_eq.
unfold M1_CS_mult.
intro x.
case x.
simpl.
reflexivity.

simpl.
reflexivity.
Qed.

Definition M1_as_CSemiGroup:CSemiGroup:=
(Build_CSemiGroup M1_as_CSetoid M1_mult_as_bin_fun M1_is_CSemiGroup).

Lemma M2_is_CSemiGroup:(is_CSemiGroup M1_as_CSetoid M2_mult_as_bin_fun).
unfold is_CSemiGroup.
unfold associative.
simpl.
intros x y z.
case x.
case y.
case z.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.

case z.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.

case y.
case z.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.
Qed.
       
Definition M2_as_CSemiGroup:=
(Build_CSemiGroup M1_as_CSetoid M2_mult_as_bin_fun M2_is_CSemiGroup).

Lemma e1_is_lft_unit_M2: (is_lft_unit M2_mult_as_bin_fun e1). 
unfold is_lft_unit.
simpl.
unfold M1_eq.
reflexivity.
Qed.

Lemma e1_is_rht_unit_M2: (is_rht_unit M2_mult_as_bin_fun e1).
unfold is_rht_unit.
simpl.
intro x.
case x.
simpl.
unfold M1_eq.
reflexivity.

simpl.
unfold M1_eq.
reflexivity.
Qed.

End  p68E1b1.
