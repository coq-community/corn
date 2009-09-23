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
(* CQuotient_Modules.v, v1.0, 28april2004, Bart Kirkels *)

(** printing [+] %\ensuremath+% #+# *)
(** printing [*] %\ensuremath\times% #&times;# *)
(** printing ['] %\ensuremath.% #.# *)
(** printing [-] %\ensuremath{-}% #&minus;# *)
(** printing [--] %\ensuremath-% #&minus;# *)
(** printing [=] %\ensuremath=% #&equiv;# *)
(** printing [#] %\ensuremath\#% *)
(** printing Zero %\ensuremath{\mathbf0}% #0# *)
(** printing One %\ensuremath{\mathbf1}% #1# *)

Require Export CModules.

(**
* Quotient Modules
Let [R] be a ring, [A] an [R]-Module and [cm] a comodule of [A]. %\\%
We will prove that $A / \lnot cm$ #A / ~cm# is a module, called QuotMod.
** QuotMod is a setoid
To achieve this we define a new apartness on the elements of [A].
*)

Section QuotMod.

Variable R : CRing.
Variable A :RModule R.
Variable cm: comod A.

Definition ap_quotmod (x y:A) := cm(x[-]y).

Lemma ap_quotmod_irreflexive : irreflexive ap_quotmod.
Proof.
 red in |-*.
 intro x.
 unfold ap_quotmod in |-*.
 assert (x[-]x[=]Zero); algebra.
 assert (Not ((cmpred A cm) Zero)); algebra.
 intro. apply H0.
 apply (comod_wd A cm (x[-]x) Zero); auto.
Qed.

Lemma ap_quotmod_symmetric : Csymmetric ap_quotmod.
Proof.
 red in |-*.
 intros x y.
 unfold ap_quotmod.
 intro X.
 apply (comod_mult A cm (y[-]x) ([--]One)).
 apply (comod_wd A cm (x[-]y) (rm_mu A [--]One (y[-]x))); algebra.
 astepr [--](y[-]x); try apply eq_symmetric; try apply muminus1.
 astepl [--](y[+][--]x).
 astepl ([--][--]x[+][--]y).
 astepl (x[+][--]y).
 algebra.
Qed.

Lemma ap_quotmod_cotransitive : cotransitive ap_quotmod.
Proof.
 red in |-*.
 intros x y; unfold ap_quotmod.
 intros X z.
 apply (comod_plus A cm (x[-]z) (z[-]y)).
 apply (comod_wd A cm (x[-]y) ((x[-]z)[+](z[-]y))); auto.
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

Definition eq_quotmod (x y:A) := Not (cm(x[-]y)).

Lemma eq_quotmod_wd : forall (x y:A), x[=]y -> (eq_quotmod x y).
Proof.
 intros x y X; auto.
 red in |-*; intro X0.
 assert ((cmpred A cm)(Zero)); algebra.
  apply (comod_wd A cm (x[-]y) Zero); algebra.
  apply x_minus_x; auto.
 apply (comod_nonzero A cm); assumption.
Qed.

Lemma ap_quotmod_tight : tight_apart eq_quotmod ap_quotmod.
Proof.
 red in |-*.
 intros x y; intuition.
Qed.

Definition ap_quotmod_is_apartness :=
Build_is_CSetoid A eq_quotmod ap_quotmod
ap_quotmod_irreflexive
ap_quotmod_symmetric
ap_quotmod_cotransitive
ap_quotmod_tight.

Definition quotmod_as_CSetoid := Build_CSetoid _ _ _
ap_quotmod_is_apartness.

(**
%\newpage%
** QuotMod is a semigroup
We use [[+]] as the operation for this.
*)

Lemma dmplus_is_ext : bin_fun_strext quotmod_as_CSetoid
quotmod_as_CSetoid quotmod_as_CSetoid (csg_op (c:=A)).
Proof.
 red in |-*.
 intros x1 x2 y1 y2.
 simpl in |-*.
 unfold ap_quotmod in |-*.
 intro X.
 apply (comod_plus A cm (x1[-]x2) (y1[-]y2)); auto.
 apply (comod_wd A cm ((x1[+]y1)[-](x2[+]y2)) ((x1[-]x2)[+](y1[-]y2))); auto.
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

Definition dmplus_is_bin_fun :=
Build_CSetoid_bin_fun quotmod_as_CSetoid quotmod_as_CSetoid
quotmod_as_CSetoid (csg_op (c:=A)) dmplus_is_ext.

Lemma dmplus_is_assoc : associative dmplus_is_bin_fun.
Proof.
 red in |-*; auto.
 intros x y z; simpl in |-*.
 apply eq_quotmod_wd; algebra.
Qed.

Definition quotmod_as_CSemiGroup := Build_CSemiGroup quotmod_as_CSetoid
dmplus_is_bin_fun dmplus_is_assoc.

(**
** QuotMod ia a monoid
[Zero:A] will work as unit.
*)

Lemma zero_as_rht_unit : is_rht_unit dmplus_is_bin_fun Zero.
Proof.
 red in |-*; intro x.
 simpl in |-*.
 apply eq_quotmod_wd; algebra.
Qed.

Lemma zero_as_lft_unit : is_lft_unit dmplus_is_bin_fun Zero.
Proof.
 red in |-*; intro x; simpl in |-*.
 apply eq_quotmod_wd; algebra.
Qed.

Definition quotmod_is_CMonoid := Build_is_CMonoid quotmod_as_CSemiGroup
Zero zero_as_rht_unit zero_as_lft_unit.

Definition quotmod_as_CMonoid := Build_CMonoid quotmod_as_CSemiGroup
Zero quotmod_is_CMonoid.

(**
** QuotMod is a group
The same function still works as inverse (i.e. minus).
*)

Lemma dminv_is_ext : un_op_strext quotmod_as_CSetoid (cg_inv (c:=A)).
Proof.
 red in |-*.
 red in |-*.
 intros x y.
 simpl in |-*.
 unfold ap_quotmod in |-*.
 intro X.
 apply (comod_mult A cm (x[-]y) [--]One); algebra.
 apply (comod_wd A cm ([--]x[-][--]y) ([--]One['](x[-]y))); algebra.
 astepr ([--](x[-]y)).
 astepr ([--](x[+][--]y)).
 astepr ([--]x[+][--][--]y).
 algebra.
Qed.

Definition dminv_is_un_op :=
Build_CSetoid_un_op quotmod_as_CSetoid (cg_inv (c:=A)) dminv_is_ext.

Lemma dminv_is_inv : is_CGroup quotmod_as_CMonoid dminv_is_un_op.
Proof.
 red in |-*.
 intro x.
 simpl in |-*.
 unfold is_inverse in |-*.
 simpl in |-*.
 split; apply eq_quotmod_wd; algebra.
Qed.

Definition quotmod_as_CGroup := Build_CGroup quotmod_as_CMonoid
dminv_is_un_op dminv_is_inv.

(**
%\newpage%
** QuotMod is an Abelian group
*)

Lemma dmplus_is_commutative : commutes dmplus_is_bin_fun.
Proof.
 red in |-*.
 intros x y.
 simpl in |-*.
 apply eq_quotmod_wd; algebra.
Qed.

Definition quotmod_as_CAbGroup := Build_CAbGroup quotmod_as_CGroup
dmplus_is_commutative.

(**
** QuotMod is an [R]-module
[rm_mu A] does the job.
*)

Lemma dmmu_is_ext : bin_fun_strext R
quotmod_as_CAbGroup quotmod_as_CAbGroup (rm_mu A).
Proof.
 red in |-*.
 intros a1 a2 x1 x2.
 simpl in |-*;simpl in |-*.
 unfold ap_quotmod in |-*.
 intro X.
 cut (cm ( a1['](x1[-]x2) [+] (a1[-]a2)[']x2) ).
  intro.
  assert ( cm (a1['](x1[-]x2)) or cm ((a1[-]a2)[']x2) ).
   algebra.
  elim X1;intros.
   right.
   apply (comod_mult A cm (x1[-]x2) a1); assumption.
  left.
  cut ( (a1[-]a2)[']x2 [#] Zero).
   intro X2; cut ((a1[-]a2)[#]Zero); algebra.
   apply (mu_axap0_aap0 R A (a1[-]a2) x2); assumption.
  apply (comod_apzero A cm); assumption.
 apply (comod_wd A cm (a1[']x1 [-] a2[']x2) ); try assumption.
 astepr ( a1['](x1[+][--]x2) [+] (a1[-]a2)[']x2).
 astepr ((a1['](x1[+][--]x2))[+]((a1[+][--]a2)[']x2)).
 astepr ((a1['](x1[+][--]x2))[+](a1[']x2 [+] [--]a2[']x2)).
 astepr ((a1[']x2 [+] [--]a2[']x2) [+] (a1['](x1[+][--]x2))).
 astepr (a1[']x2 [+] [--]a2[']x2 [+] (a1['](x1[+][--]x2))).
 astepr ((a1[']x2) [+] ([--]a2[']x2) [+] (a1['](x1[+][--]x2))).
 simpl in |-*.
 astepr (a1[']x2 [+] [--]a2[']x2 [+] a1[']x1 [+] a1['][--]x2); simpl in |-*.
  astepr ((a1[']x2 [+] [--]a2[']x2 [+] a1[']x1) [+] a1['][--]x2); simpl in |-*.
  astepr ((a1[']x2 [+] [--]a2[']x2 [+] a1[']x1) [+] [--](a1[']x2)).
  astepr ([--](a1[']x2) [+] (a1[']x2 [+] [--]a2[']x2 [+] a1[']x1)).
  astepr ([--](a1[']x2) [+] (a1[']x2 [+] ([--]a2[']x2 [+] a1[']x1))).
  astepr (([--](a1[']x2) [+] a1[']x2) [+] ([--]a2[']x2 [+] a1[']x1)).
  astepr (Zero [+] ([--]a2[']x2 [+] a1[']x1)).
  astepr ([--]a2[']x2 [+] a1[']x1).
  astepr (a1[']x1 [+] [--]a2[']x2).
  astepr (a1[']x1 [+] [--](a2[']x2)).
  Step_final (a1[']x1 [-] a2[']x2).
 astepl ((a1[']x2 [+] [--]a2[']x2) [+] (a1[']x1 [+] a1['][--]x2)).
 apply plus_resp_eq; algebra.
Qed.

Definition dmmu_is_bin_fun :=
Build_CSetoid_bin_fun R quotmod_as_CAbGroup
quotmod_as_CAbGroup (rm_mu A) dmmu_is_ext.

Lemma quotmod_is_RModule : is_RModule quotmod_as_CAbGroup
dmmu_is_bin_fun.
Proof.
 apply Build_is_RModule; intuition; simpl in |-*; apply eq_quotmod_wd; algebra.
Qed.

Definition quotmod_as_RModule := Build_RModule R quotmod_as_CAbGroup
dmmu_is_bin_fun quotmod_is_RModule.

End QuotMod.

Implicit Arguments quotmod_as_RModule [R].
