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
(* CRing_Homomorphisms.v, v1.0, 28april2004, Bart Kirkels *)

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

Require Export CRings.

(**
* Ring Homomorphisms
** Definition of Ring Homomorphisms
Let [R] and [S] be rings, and [phi : R -> S].
*)

Section RingHom_Definition.

Variables R S : CRing.

Section RingHom_Preliminary.

Variable phi : CSetoid_fun R S.

Definition fun_pres_plus := forall x y:R, phi (x[+]y) [=] (phi x) [+] (phi y).
Definition fun_pres_mult := forall x y:R, phi (x[*]y) [=] (phi x) [*] (phi y).
Definition fun_pres_unit := (phi (One:R)) [=] (One:S).

End RingHom_Preliminary.


Record RingHom : Type :=
  {rhmap :> CSetoid_fun R S;
   rh1 : fun_pres_plus rhmap;
   rh2 : fun_pres_mult rhmap;
   rh3 : fun_pres_unit rhmap}.

End RingHom_Definition.

(**
** Lemmas on Ring Homomorphisms
Let [R] and [S] be rings and [f] a ring homomorphism from [R] to [S].
*** Axioms on Ring Homomorphisms
*)

Section RingHom_Lemmas.

Variables R S : CRing.

Section RingHom_Axioms.

Variable f : RingHom R S.

Lemma rh_strext : forall x y:R, (f x) [#] (f y) -> x [#] y.
Proof.
 elim f; intuition.
 assert (fun_strext rhmap0); elim rhmap0; intuition.
Qed.

Lemma rh_pres_plus : forall x y:R, f (x[+]y) [=] (f x) [+] (f y).
Proof.
 elim f; auto.
Qed.

Lemma rh_pres_mult : forall x y:R, f (x[*]y) [=] (f x) [*] (f y).
Proof.
 elim f; auto.
Qed.

Lemma rh_pres_unit : (f (One:R)) [=] (One:S).
Proof.
 elim f; auto.
Qed.

End RingHom_Axioms.


Hint Resolve rh_strext rh_pres_plus rh_pres_mult rh_pres_unit : algebra.

(**
*** Facts on Ring Homomorphisms
*)

Section RingHom_Basics.

Variable f : RingHom R S.

Lemma rh_pres_zero : (f (Zero:R)) [=] (Zero:S).
Proof.
 astepr ((f Zero)[-](f Zero)).
 astepr ((f (Zero[+]Zero))[-](f Zero)).
 Step_final ((f Zero[+]f Zero)[-]f Zero).
Qed.

Lemma rh_pres_inv : forall x:R, (f [--]x) [=] [--] (f x).
Proof.
 intro x; apply (cg_cancel_lft S (f x)).
 astepr (Zero:S).
 astepl (f (x[+][--]x)).
 Step_final (f (Zero:R)); try apply rh_pres_zero.
Qed.

Lemma rh_pres_minus : forall x y:R, f (x[-]y) [=] (f x) [-] (f y).
Proof.
 unfold cg_minus.
 intros x y.
 rewrite -> rh_pres_plus.
 rewrite -> rh_pres_inv.
 reflexivity.
Qed.

Lemma rh_apzero : forall x:R, (f x) [#] Zero -> x [#] Zero.
Proof.
 intros x X; apply (cg_ap_cancel_rht R x (Zero:R) x).
 astepr x.
 apply (rh_strext f (x[+]x) x).
 astepl ((f x)[+](f x)).
 astepr ((Zero:S) [+] (f x)).
 apply (op_rht_resp_ap S (f x) (Zero:S) (f x)).
 assumption.
Qed.


Lemma rh_pres_nring : forall n, (f (nring n:R)) [=] (nring n:S).
Proof.
 induction n.
  apply rh_pres_zero.
 simpl.
 rewrite -> rh_pres_plus;auto with *.
Qed.

End RingHom_Basics.

End RingHom_Lemmas.

Hint Resolve rh_strext rh_pres_plus rh_pres_mult rh_pres_unit : algebra.
Hint Resolve rh_pres_zero rh_pres_minus rh_pres_inv rh_apzero : algebra.
Hint Rewrite rh_pres_zero rh_pres_plus rh_pres_minus rh_pres_inv rh_pres_mult rh_pres_unit : ringHomPush.

Definition RHid R : RingHom R R.
Proof.
 exists (id_un_op R).
   intros x y; apply eq_reflexive.
  intros x y; apply eq_reflexive.
 apply eq_reflexive.
Defined.

Section Compose.

Variable R S T : CRing.
Variable phi : RingHom S T.
Variable psi : RingHom R S.

Lemma RHcompose1 : fun_pres_plus _ _ (compose_CSetoid_fun _ _ _ psi phi).
Proof.
 intros x y.
 simpl.
 repeat rewrite -> rh_pres_plus;reflexivity.
Qed.

Lemma RHcompose2 : fun_pres_mult _ _ (compose_CSetoid_fun _ _ _ psi phi).
Proof.
 intros x y.
 simpl.
 repeat rewrite -> rh_pres_mult; reflexivity.
Qed.

Lemma RHcompose3 : fun_pres_unit _ _ (compose_CSetoid_fun _ _ _ psi phi).
Proof.
 unfold fun_pres_unit.
 simpl.
 repeat rewrite -> rh_pres_unit; reflexivity.
Qed.

Definition RHcompose : RingHom R T := Build_RingHom _ _ _ RHcompose1 RHcompose2 RHcompose3.

End Compose.
