(* Copyright © 1998-2006
 * Henk Barendregt
 * Luís Cruz-Filipe
 * Herman Geuvers
 * Mariusz Giero
 * Rik van Ginneken
 * Dimitri Hendriks
 * Sébastien Hinderer
 * Bart Kirkels
 * Pierre Letouzey
 * Iris Loeb
 * Lionel Mamane
 * Milad Niqui
 * Russell O’Connor
 * Randy Pollack
 * Nickolay V. Shmyrev
 * Bas Spitters
 * Dan Synek
 * Freek Wiedijk
 * Jan Zwanenburg
 * 
 * This work is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *) 
(* CQuotient_Rings.v, v1.0, 28april2004, Bart Kirkels *)

(** printing [+] %\ensuremath+% #+# *)
(** printing [*] %\ensuremath\times% #&times;# *)
(** printing ['] %\ensuremath.% #.# *)
(** printing [-] %\ensuremath{-}% #&minus;# *)
(** printing [--] %\ensuremath-% #&minus;# *)
(** printing [=] %\ensuremath=% #&equiv;# *)
(** printing [#] %\ensuremath\#% *)
(** printing Zero %\ensuremath{\mathbf0}% #0# *)
(** printing One %\ensuremath{\mathbf1}% #1# *)

Require Export CIdeals.

(**
* Quotient Rings
Let [R] be a ring and [C] a coideal of [R].%\\%
We will prove that $A / \lnot C$ #A / ~C# is a ring, called QuotRing.
** QuotRing is a setoid
To achieve this we define a new apartness on the elements of [R].
*)

Section QuotRing.

Variable R : CRing.
Variable C : coideal R.

Definition ap_quotring (x y:R) := C(x[-]y).

Lemma ap_quotring_irreflexive : irreflexive ap_quotring.
red in |-*.
intro x.
unfold ap_quotring in |-*.
assert (x[-]x[=]Zero); algebra.
assert (Not ((cipred R C) Zero)); algebra.
intro. apply H0.
apply (coideal_wd R C (x[-]x) Zero); auto.
Qed.

Lemma ap_quotring_symmetric : Csymmetric ap_quotring.
red in |-*.
intros x y.
unfold ap_quotring.
intro X.
cut (C [--]One and C (y[-]x)). intuition.
apply (coideal_mult R C [--]One (y[-]x)).
apply (coideal_wd R C (x[-]y) ([--]One[*](y[-]x))); algebra.
astepr [--](y[-]x). 
astepr [--](y[+][--]x).
astepr ([--][--]x[+][--]y).
Step_final (x[+][--]y).
Qed.

Lemma ap_quotring_cotransitive : cotransitive ap_quotring.
red in |-*.
intros x y; unfold ap_quotring.
intros X z.
apply (coideal_plus R C (x[-]z) (z[-]y)).
apply (coideal_wd R C (x[-]y) ((x[-]z)[+](z[-]y))); auto.
astepr ((x[-]z)[+]z[-]y).
astepr ((x[-]z)[+]z[+][--]y).
astepr ((x[+][--]z)[+]z[+][--]y).
astepr (x[+]([--]z[+]z)[+][--]y).
astepr (x[+]Zero[+][--]y).
astepr (x[+][--]y).
astepr (x[-]y).
apply eq_reflexive.
Qed.

(**
We take `not apart' as the new equality.
*)

Definition eq_quotring (x y:R) := Not (C(x[-]y)).

Lemma eq_quotring_wd : forall (x y:R), x[=]y -> (eq_quotring x y).
intros x y X; auto.
red in |-*; intro X0.
assert ((cipred R C)(Zero)); algebra.
apply (coideal_wd R C (x[-]y) Zero); algebra.
apply x_minus_x; auto.
apply (coideal_nonzero R C); assumption.
Qed.

Lemma ap_quotring_tight : tight_apart eq_quotring ap_quotring.
red in |-*.
intros x y; intuition.
Qed.

Definition ap_quotring_is_apartness :=
Build_is_CSetoid R eq_quotring ap_quotring 
ap_quotring_irreflexive
ap_quotring_symmetric
ap_quotring_cotransitive
ap_quotring_tight.

Definition quotring_as_CSetoid := Build_CSetoid _ _ _ 
ap_quotring_is_apartness.

(**
%\newpage%
** QuotRing is a semigroup
We use [[+]] as the operation for this.
*)

Lemma drplus_is_ext : bin_fun_strext quotring_as_CSetoid 
quotring_as_CSetoid quotring_as_CSetoid (csg_op (c:=R)).
red in |-*.
intros x1 x2 y1 y2.
simpl in |-*.
unfold ap_quotring in |-*.
intro X.
apply (coideal_plus R C (x1[-]x2) (y1[-]y2)); auto.
apply (coideal_wd R C ((x1[+]y1)[-](x2[+]y2)) ((x1[-]x2)[+](y1[-]y2))); auto.
astepr ((x1[+][--]x2)[+](y1[+][--]y2)).
astepr ((x1[+][--]x2)[+]y1[+][--]y2).
astepr (((x1[+][--]x2)[+]y1)[+][--]y2).
astepr ([--]y2[+]((x1[+][--]x2)[+]y1)).
astepr ([--]y2[+](x1[+][--]x2)[+]y1).
astepr ([--]y2[+]([--]x2[+]x1)[+]y1).
astepr (([--]y2[+][--]x2)[+]x1[+]y1).
astepr (([--]y2[+][--]x2)[+](x1[+]y1)).
astepr ((x1[+]y1)[+]([--]y2[+][--]x2)).
astepr ((x1[+]y1)[+][--](x2[+]y2)).
algebra.
Qed.

Definition drplus_is_bin_fun := 
Build_CSetoid_bin_fun quotring_as_CSetoid quotring_as_CSetoid
quotring_as_CSetoid (csg_op (c:=R)) drplus_is_ext.

Lemma drplus_is_assoc : associative drplus_is_bin_fun.
red in |-*; auto.
intros x y z; simpl in |-*.
apply eq_quotring_wd; algebra.
Qed.

Definition quotring_as_CSemiGroup := Build_CSemiGroup quotring_as_CSetoid
drplus_is_bin_fun drplus_is_assoc.

(**
** QuotRing is a monoid
[Zero:R] will work as unit.
*)

Lemma zero_as_rht_unit : is_rht_unit drplus_is_bin_fun Zero.
red in |-*; intro x.
simpl in |-*.
apply eq_quotring_wd; algebra.
Qed.

Lemma zero_as_lft_unit : is_lft_unit drplus_is_bin_fun Zero.
red in |-*; intro x; simpl in |-*.
apply eq_quotring_wd; algebra.
Qed.

Definition quotring_is_CMonoid := Build_is_CMonoid quotring_as_CSemiGroup
Zero zero_as_rht_unit zero_as_lft_unit.

Definition quotring_as_CMonoid := Build_CMonoid quotring_as_CSemiGroup
Zero quotring_is_CMonoid.

(**
** QuotRing is a group
The same function still works as inverse (i.e. minus).
*)

Lemma drinv_is_ext : un_op_strext quotring_as_CSetoid (cg_inv (c:=R)).
red in |-*.
red in |-*.
intros x y.
simpl in |-*.
unfold ap_quotring in |-*.
intro X.
cut (C (x[-]y) and C [--]One). intuition.
apply (coideal_mult R C (x[-]y) [--]One); algebra.
apply (coideal_wd R C ([--]One[*](x[-]y)) ((x[-]y)[*][--]One)); algebra.
apply (coideal_wd R C ([--]x[-][--]y) ([--]One[*](x[-]y))); algebra.
astepr ([--](x[-]y)).
astepr ([--](x[+][--]y)).
Step_final ([--]x[+][--][--]y).
Qed.

Definition drinv_is_un_op := 
Build_CSetoid_un_op quotring_as_CSetoid (cg_inv (c:=R)) drinv_is_ext.

Lemma drinv_is_inv : is_CGroup quotring_as_CMonoid drinv_is_un_op.
red in |-*.
intro x.
simpl in |-*.
unfold is_inverse in |-*.
simpl in |-*.
split; apply eq_quotring_wd; algebra.
Qed.

Definition quotring_as_CGroup := Build_CGroup quotring_as_CMonoid
drinv_is_un_op drinv_is_inv.

(**
%\newpage%
** QuotRing is an Abelian group
*)

Lemma drplus_is_commutative : commutes drplus_is_bin_fun.
red in |-*.
intros x y.
simpl in |-*.
apply eq_quotring_wd; algebra.
Qed.

Definition quotring_as_CAbGroup := Build_CAbGroup quotring_as_CGroup
drplus_is_commutative.

(**
** QuotRing is a ring
Multiplication from [R] still works as a multiplicative function, making
quotring a ring.
*)

Lemma drmult_is_ext : bin_fun_strext quotring_as_CAbGroup 
quotring_as_CAbGroup quotring_as_CAbGroup (cr_mult (c:=R)).
red in |-*.
intros x1 x2 y1 y2.
simpl in |-*.
unfold ap_quotring.
intro X.
cut (C ((x1[*](y1[-]y2)) [+] ((x1[-]x2)[*]y2))).
intro.
assert (C (x1[*](y1[-]y2)) or C ((x1[-]x2)[*]y2)); algebra.
elim X1; intros.
right. cut (C x1 and C (y1[-]y2)). intuition.
apply coideal_mult; assumption.
left. cut (C (x1[-]x2) and C y2). intuition.
apply coideal_mult; assumption.
apply (coideal_wd R C (x1[*]y1 [-] x2[*]y2)); try assumption.
astepr (x1[*]y1 [-] x1[*]y2 [+] (x1[-]x2)[*]y2).
astepr (x1[*]y1 [-] x1[*]y2 [+] x1[*]y2 [-] x2[*]y2).
astepr (x1[*]y1 [+] [--](x1[*]y2) [+] x1[*]y2 [+] [--](x2[*]y2)).
astepr ((x1[*]y1 [+] ([--](x1[*]y2) [+] x1[*]y2)) [+] [--](x2[*]y2)).
astepr ((x1[*]y1 [+] Zero) [+] [--](x2[*]y2)).
Step_final (x1[*]y1 [+] [--](x2[*]y2)).
astepl ((x1[*]y1 [-] x1[*]y2)[+](x1[*]y2)[+][--](x2[*]y2)).
astepl ((x1[*]y1 [-] x1[*]y2)[+](x1[*]y2[+][--](x2[*]y2))).
apply plus_resp_eq.
apply eq_symmetric; apply (ring_distr2 R x1 x2 y2).
astepl ((x1[-]x2)[*]y2 [+] (x1[*]y1 [-] x1[*]y2)).
astepr ((x1[-]x2)[*]y2 [+] x1[*](y1[-]y2)).
apply plus_resp_eq.
apply eq_symmetric; apply (ring_distr1 R x1 y1 y2).
Qed.

Definition drmult_is_bin_op := 
Build_CSetoid_bin_op quotring_as_CAbGroup (cr_mult (c:=R)) drmult_is_ext.

Lemma drmult_associative : associative drmult_is_bin_op.
red in |-*; simpl in |-*.
intros x y z; apply eq_quotring_wd.
algebra.
Qed.

Lemma drmult_monoid : is_CMonoid (Build_CSemiGroup quotring_as_CAbGroup
   drmult_is_bin_op drmult_associative) One.
apply Build_is_CMonoid; red in |-*; intro x; simpl in |-*;
apply eq_quotring_wd; algebra.
Qed.

Lemma drmult_commutes : commutes drmult_is_bin_op.
red in |-*; simpl in |-*; intros x y; apply eq_quotring_wd; algebra.
Qed.

Lemma quotring_distr : distributive drmult_is_bin_op drplus_is_bin_fun.
red in |-*; simpl in |-*; intros x y z.
apply eq_quotring_wd; algebra.
Qed.

Lemma quotring_nontriv : (One:quotring_as_CAbGroup) [#] (Zero:quotring_as_CAbGroup).
simpl in |-*.
unfold ap_quotring.
apply (coideal_wd R C One (One[-]Zero)); algebra.
Qed.

Definition quotring_is_CRing := Build_is_CRing quotring_as_CAbGroup One
drmult_is_bin_op drmult_associative drmult_monoid 
drmult_commutes quotring_distr quotring_nontriv.

Definition quotring_as_CRing := Build_CRing quotring_as_CAbGroup
One drmult_is_bin_op quotring_is_CRing.

End QuotRing.



