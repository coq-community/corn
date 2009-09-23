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
(* CModule_Homomorphisms.v, v1.0, 28april2004, Bart Kirkels *)

(** printing [+] %\ensuremath+% #+# *)
(** printing [*] %\ensuremath\times% #&times;# *)
(** printing ['] %\ensuremath.% #.# *)
(** printing [-] %\ensuremath{-}% #&minus;# *)
(** printing [--] %\ensuremath-% #&minus;# *)
(** printing [=] %\ensuremath=% #&equiv;# *)
(** printing [#] %\ensuremath\#% *)
(** printing Zero %\ensuremath{\mathbf0}% #0# *)
(** printing One %\ensuremath{\mathbf1}% #1# *)
(** printing phi %\ensuremath{\phi}%  *)

Require Export CModules.

(**
* Module Homomorphisms
** Definition of Module Homomorphisms
Let [R] be a ring, let [A] and [B] be [R]-Modules and [phi : A -> B].
*)

Section ModHom_Definition.

Variable R : CRing.
Variables A B : RModule R.

Section ModHom_Preliminary.

Variable phi : CSetoid_fun A B.

Definition fun_pres_plus := forall x y:A, phi (x [+] y) [=] (phi x) [+] (phi y).
Definition fun_pres_unit := (phi (cm_unit A)) [=] (cm_unit B).
Definition fun_pres_mult := forall (a:R)(x:A), phi (rm_mu A a x) [=] rm_mu B a (phi x).

End ModHom_Preliminary.


Record ModHom : Type :=
  {hommap :> CSetoid_fun A B;
   hom1 : fun_pres_plus hommap;
   hom2 : fun_pres_unit hommap;
   hom3 : fun_pres_mult hommap}.

End ModHom_Definition.

Implicit Arguments ModHom [R].
Implicit Arguments hommap [R].
Implicit Arguments hom1 [R].
Implicit Arguments hom2 [R].
Implicit Arguments hom3 [R].

(**
** Lemmas on Module Homomorphisms
Let [R] be a ring, [A] and [B] [R]-Modules
and [f] a module homomorphism from [A] to [B].
*** Axioms on Module Homomorphisms
*)

Section ModHom_Lemmas.

Variable R : CRing.
Variables A B : RModule R.

Section ModHom_Axioms.

Variable f : ModHom A B.

Lemma mh_strext : forall x y:A, (f x) [#] (f y) -> x [#] y.
Proof.
 elim f; intuition.
 assert (fun_strext hommap0); elim hommap0; intuition.
Qed.

Lemma mh_pres_plus : forall x y:A, f (x[+]y) [=] (f x) [+] (f y).
Proof.
 elim f; auto.
Qed.

Lemma mh_pres_unit : (f (cm_unit A)) [=] (cm_unit B).
Proof.
 elim f; auto.
Qed.

Lemma mh_pres_mult : forall (a:R)(x:A), f (rm_mu A a x) [=] rm_mu B a (f x).
Proof.
 elim f; auto.
Qed.

End ModHom_Axioms.


Hint Resolve mh_strext mh_pres_plus mh_pres_unit mh_pres_mult : algebra.

(**
*** Facts on Module Homomorphisms
*)

Section ModHom_Basics.

Variable f : ModHom A B.

Lemma mh_pres_zero : (f (Zero:A)) [=] (Zero:B).
Proof.
 astepr ((f Zero)[-](f Zero)).
 astepr ((f (Zero[+]Zero))[-](f Zero)).
 Step_final ((f Zero[+]f Zero)[-]f Zero).
Qed.

Lemma mh_pres_minus : forall x:A, (f [--]x) [=] [--] (f x).
Proof.
 intro x; apply (cg_cancel_lft B (f x)).
 astepr (Zero:B).
 astepl (f (x[+][--]x)).
 Step_final (f (Zero:A)); try apply mh_pres_zero.
Qed.

Lemma mh_apzero : forall x:A, (f x) [#] Zero -> x [#] Zero.
Proof.
 intros x X; apply (cg_ap_cancel_rht A x (Zero:A) x).
 astepr x.
 apply (mh_strext f (x[+]x) x).
 astepl ((f x)[+](f x)).
 astepr ((Zero:B) [+] (f x)).
 apply (op_rht_resp_ap B (f x) (Zero:B) (f x)).
 assumption.
Qed.

End ModHom_Basics.

End ModHom_Lemmas.

Implicit Arguments mh_strext [R].
Implicit Arguments mh_pres_plus [R].
Implicit Arguments mh_pres_unit [R].
Implicit Arguments mh_pres_mult [R].
Implicit Arguments mh_pres_zero [R].
Implicit Arguments mh_pres_minus [R].
Implicit Arguments mh_apzero [R].

Hint Resolve mh_strext mh_pres_plus mh_pres_unit mh_pres_mult : algebra.
Hint Resolve mh_pres_zero mh_pres_minus mh_apzero : algebra.
