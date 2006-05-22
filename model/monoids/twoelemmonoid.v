(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* $Id$ *)

Require Export CMonoids.
Require Export twoelemsemigroup.
Require Export Nm_to_cycm.

Section p68E1b1.

(** **Example of a monoid: monoids with two elements
*)

Definition M1_is_CMonoid:(is_CMonoid M1_as_CSemiGroup e1):=
(Build_is_CMonoid M1_as_CSemiGroup e1 e1_is_rht_unit e1_is_lft_unit).

Definition M1_as_CMonoid:CMonoid:=
(Build_CMonoid M1_as_CSemiGroup e1 M1_is_CMonoid).

Definition M2_is_CMonoid :=
(Build_is_CMonoid M2_as_CSemiGroup e1 e1_is_rht_unit_M2 e1_is_lft_unit_M2).

Definition M2_as_CMonoid:CMonoid:=
(Build_CMonoid M2_as_CSemiGroup e1 M2_is_CMonoid).

Lemma two_element_CMonoids:
forall (op :(CSetoid_bin_fun M1_as_CSetoid M1_as_CSetoid M1_as_CSetoid))
(H: (is_CSemiGroup M1_as_CSetoid op)),
(is_unit (Build_CSemiGroup M1_as_CSetoid op H) e1)-> 
(forall (x y:M1_as_CSetoid),(op x y)= (M1_mult_as_bin_fun x y)) or
(forall (x y:M1_as_CSetoid), (op x y)= (M2_mult_as_bin_fun x y)).
intros op H unit0.
cut (((op u u)=e1) or ((op u u)= u)).
intro H0.
unfold is_unit in unit0.
simpl in unit0.
elim H0.
clear H0.
intro H0.
left.
simpl.
intros x y.
unfold M1_CS_mult.
case x.
case y.
simpl.
set (unit1:= (unit0 e1)).
unfold M1_eq in unit1.
intuition.

simpl.
set (unit1:= (unit0 u)).
unfold M1_eq in unit1.
intuition.

case y.
simpl.
set (unit1:= (unit0 u)).
unfold M1_eq in unit1.
intuition.

simpl.
exact H0.

clear H0.
intro H0.
right.
simpl.
intros x y.
unfold M1_CS_mult.
case x.
case y.
simpl.
set (unit1:= (unit0 e1)).
unfold M1_eq in unit1.
intuition.

simpl.
set (unit1:= (unit0 u)).
unfold M1_eq in unit1.
intuition.

case y.
simpl.
set (unit1:= (unit0 u)).
unfold M1_eq in unit1.
intuition.

simpl.
exact H0.
apply (M1_eq_dec (op u u)).
Qed.

End p68E1b1.

Section p69E1.

Let PM1M2:=(direct_product_as_CMonoid M1_as_CMonoid M2_as_CMonoid).

Let uu: PM1M2.
simpl.
exact (pairT u u).
Defined.

Let e1u: PM1M2.
simpl.
exact (pairT e1 u).
Defined.

Lemma ex_69 : uu [+] uu [=]e1u.
simpl.
unfold M1_eq.
intuition.
Qed.

End p69E1.

Section p71E1_.

Lemma M1_is_generated_by_u: (forall(m:M1_as_CMonoid),
  {n:nat | (@power_CMonoid M1_as_CMonoid u n)[=]m}):CProp.
simpl.
intro m.
induction m.
exists 0.
simpl.
set (H:= (eq_reflexive M1_as_CSetoid e1)).
intuition.

exists 1.
simpl.
set (H:= (eq_reflexive M1_as_CSetoid u)).
intuition.
Qed.

Lemma not_injective_f:
 Not(injective (f_as_CSetoid_fun M1_as_CMonoid u M1_is_generated_by_u)).
red.
unfold injective.
simpl.
intro H.
set (H3:=(H 0 2)).
cut (0 {#N} 2).
intro H4.
set (H5:= (H3 H4)).
set (H6:=(ap_imp_neq _ (@power_CMonoid M1_as_CMonoid u 0)
         (@power_CMonoid M1_as_CMonoid u 2) H5)).
unfold cs_neq in H6.
simpl in H6.
apply H6.
set (H7:= (eq_reflexive_unfolded M1_as_CMonoid e1)).
intuition.

unfold ap_nat.
unfold CNot.
intro H4.
cut False.
intuition.
intuition.
Qed.

End p71E1_.

Section p71E2b1.

Lemma not_isomorphic_M1_M2: Not (isomorphic M1_as_CMonoid M2_as_CMonoid).
unfold Not.
unfold isomorphic.
simpl.
unfold isomorphism.
unfold morphism.
simpl.
intro H.
elim H.
clear H.
intros f H.
elim H.
clear H.
intros H H0.
elim H.
clear H.
intros H H2.
unfold bijective in H0.
elim H0.
clear H0.
intros H0 H3.
unfold surjective in H3.
simpl in H3.
elim (H3 u).
intros x H4.
cut (M1_eq (f u) u).
intros H5.
set (H1:= not_M1_eq_e1_u).
unfold Not in H1.
apply H1.
unfold M1_eq in H, H2, H5 |- *.
set (H6:=(H2 u u)).
simpl in H6.
rewrite H in H6.
rewrite H5 in H6.
simpl in H6.
exact H6.

unfold M1_eq in H, H4 |- *.
set (H1:= (M1_eq_dec x)).
unfold M1_eq in H1.
elim H1.
intro H5.
rewrite H5 in H4.
rewrite H4 in H.
set (H6:= not_M1_eq_e1_u).
unfold Not in H6.
unfold M1_eq in H6.
elim H6.
cut (u=e1).
intuition.
exact H.

intro H5.
rewrite H5 in H4.
exact H4.
Qed.

End p71E2b1.
