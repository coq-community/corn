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
(* Ideals.v, v1.0, 28april2004, Bart Kirkels *)

(** printing [+] %\ensuremath+% #+# *)
(** printing [*] %\ensuremath\times% #&times;# *)
(** printing ['] %\ensuremath.% #.# *)
(** printing [-] %\ensuremath{-}% #&minus;# *)
(** printing [--] %\ensuremath-% #&minus;# *)
(** printing [=] %\ensuremath=% #&equiv;# *)
(** printing [#] %\ensuremath\#% *)
(** printing Zero %\ensuremath{\mathbf0}% #0# *)
(** printing One %\ensuremath{\mathbf1}% #1# *)

Require Export CRings.

(**
* Ideals and coideals
** Definition of ideals and coideals
Let [R] be a ring. At this moment all CRings are commutative and
non-trivial. So our ideals are automatically two-sided. As soon
as non-commutative rings are represented in CoRN left and
right ideals should be defined.
*)

Section Ideals.

Variable R : CRing.

Record is_ideal (idP : wd_pred R) : CProp :=
  { idax : forall a x:R, idP a -> idP (a[*]x);
    idprpl : forall x y : R, idP x -> idP y -> idP (x[+]y)}.

Record ideal : Type :=
  { idpred :> wd_pred R;
    idproof : is_ideal idpred}.

(* begin hide *)
Variable I : ideal.
Definition ideal_as_CSetoid := Build_SubCSetoid R I.
(* end hide *)

(**
We actually define strongly non-trivival co-ideals.
*)

Record is_coideal (ciP : wd_pred R) : CProp :=
  { ciapzero : forall x:R, ciP x -> x[#]Zero;
    ciplus : forall x y:R, ciP (x[+]y) -> ciP x or ciP y;
    cimult : forall x y:R, ciP (x[*]y) -> ciP x and ciP y;
    cinontriv : ciP One}.

Record coideal : Type :=
  { cipred :> wd_pred R;
    ciproof : is_coideal cipred}.

(* begin hide *)
Variable C : coideal.
Definition coideal_as_CSetoid := Build_SubCSetoid R C.
(* end hide *)

End Ideals.

Implicit Arguments is_ideal [R].
Implicit Arguments is_coideal [R].

(**
%\newpage%
** Axioms of ideals and coideals
Let [R] be a ring, [I] and ideal of [R] and [C] a coideal of [R].
*)

Section Ideal_Axioms.

Variable R : CRing.
Variable I : ideal R.
Variable C : coideal R.

Lemma ideal_is_ideal : is_ideal I.
Proof.
 elim I; auto.
Qed.

Lemma coideal_is_coideal : is_coideal C.
Proof.
 elim C; auto.
Qed.

Lemma coideal_apzero : forall x:R, C x -> x[#]Zero.
Proof.
 elim C. intuition elim ciproof0.
Qed.

Lemma coideal_nonzero : Not (C Zero).
Proof.
 intro.
 cut ((Zero:R)[#](Zero:R)); try apply coideal_apzero; try assumption.
 apply ap_irreflexive.
Qed.

Lemma coideal_plus : forall x y:R, C (x[+]y) -> C x or C y.
Proof.
 elim C. intuition elim ciproof0.
Qed.

Lemma coideal_mult : forall x y:R, C (x[*]y) -> C x and C y.
Proof.
 elim C. intuition elim ciproof0.
Qed.

Lemma coideal_nontriv : C One.
Proof.
 elim C. intuition elim ciproof0.
Qed.

Lemma coideal_wd : forall x y:R, x[=]y -> C x -> C y.
Proof.
 elim C. simpl in |-*. intro.
 elim cipred0. intros.
 apply (wdp_well_def x y); auto.
Qed.

End Ideal_Axioms.

Hint Resolve coideal_apzero coideal_nonzero coideal_plus: algebra.
Hint Resolve coideal_mult coideal_wd coideal_nontriv: algebra.
