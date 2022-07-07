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

(** printing included %\ensuremath{\subseteq}% #&sube;# *)

Require Export CoRN.algebra.CSetoidFun.

Section inclusion.

(**
** Inclusion

Let [S] be a setoid, and [P], [Q], [R] be predicates on [S]. *)

Variable S : CSetoid.

Definition included (P Q : S -> CProp) : CProp := forall x : S, P x -> Q x.

Section Basics.

Variables P Q R : S -> CProp.

Lemma included_refl : included P P.
Proof.
 red in |- *; intros.
 auto.
Qed.

Lemma included_trans : included P Q -> included Q R -> included P R.
Proof.
 intros.
 red in |- *; intros.
 apply X0; apply X; auto.
Qed.

Lemma included_conj : forall P Q R, included P Q -> included P R -> included P (Conj Q R).
Proof.
 intros.
 red in |- *; red in X, X0.
 intros; red in |- *.
 split.
  apply X; assumption.
 apply X0; assumption.
Qed.

Lemma included_conj' : included (Conj P Q) P.
Proof.
 exact (prj1 _ P Q).
Qed.

Lemma included_conj'' : included (Conj P Q) Q.
Proof.
 exact (prj2 _ P Q).
Qed.

Lemma included_conj_lft : included R (Conj P Q) -> included R P.
Proof.
 red in |- *.
 unfold conjP.
 intros H1 x H2.
 elim (H1 x); auto.
Qed.

Lemma included_conj_rht : included R (Conj P Q) -> included R Q.
Proof.
 red in |- *. unfold conjP.
 intros H1 x H2.
 elim (H1 x); auto.
Qed.

Lemma included_extend : forall (H : forall x, P x -> CProp),
 included R (extend P H) -> included R P.
Proof.
 intros H0 H1.
 red in |- *.
 unfold extend in H1.
 intros.
 elim (H1 x); auto.
Qed.

End Basics.

(**
%\begin{convention}% Let [I,R:S->CProp] and [F G:(PartFunct S)], and denote
by [P] and [Q], respectively, the domains of [F] and [G].
%\end{convention}%
*)

Variables F G : (PartFunct S).

(* begin hide *)
Let P := Dom F.
Let Q := Dom G.
(* end hide *)

Variable R : S -> CProp.

Lemma included_FComp : included R P -> (forall x Hx, (R x) -> Q (F x Hx)) -> included R (Dom (G[o]F)).
Proof.
 intros HP HQ.
 simpl in |- *.
 red in |- *; intros x Hx.
 exists (HP x Hx).
 apply HQ.
 assumption.
Qed.

Lemma included_FComp' : included R (Dom (G[o]F)) -> included R P.
Proof.
 intro H; simpl in H; red in |- *; intros x Hx.
 elim (H x Hx); auto.
Qed.

End inclusion.

Arguments included [S].

#[global]
Hint Resolve included_refl included_FComp : included.

#[global]
Hint Immediate included_trans included_FComp' : included.
