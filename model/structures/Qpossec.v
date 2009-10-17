(* Copyright © 1998-2008
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

(** printing Qpos $\mathbb{Q}^{+}$ #Q<SUP>+</SUP># *)

Require Export QArith.
Require Import Qpower.
Require Import Qordfield.
Require Import COrdFields2.
Require Import Eqdep_dec.
Require Import CornTac.

Open Local Scope Q_scope.

(**
* [Qpos]
We define [Qpos] as a pair of positives (n,d) which represents the
fraction n/d.  *)

Record Qpos : Set := QposMake
{QposNumerator : positive
;QposDenominator : positive
}.

Notation "a # b" := (QposMake a b) (at level 55, no associativity) : Qpos_scope.

Bind Scope Qpos_scope with Qpos.
Delimit Scope Qpos_scope with Qpos.

(** There is an injection from [Qpos] to [Q] that we make into a
coersion. *)
Definition QposAsQ (a:Qpos) : Q :=
(Zpos (QposNumerator a))#(QposDenominator a).

Coercion QposAsQ : Qpos >-> Q.

(** Basic properties about [Qpos] *)
Lemma Qpos_prf : forall a:Qpos, 0 < a.
Proof.
 firstorder.
Qed.

Lemma Qpos_nonzero : forall x:Qpos, (x:Q)[#]0.
Proof.
 intros x.
 apply: pos_ap_zero.
 apply Qpos_prf.
Qed.

Lemma Qpos_nonneg : forall a:Qpos, 0 <= a.
Proof.
 intros a.
 apply Qlt_le_weak.
 apply Qpos_prf.
Qed.

(** Any positive rational number can be transformed into a [Qpos]. *)
Definition mkQpos (a:Q) (p:0 < a) : Qpos.
Proof.
 intros [an ad] p.
 destruct an as [|an|an].
   compute in p.
   abstract discriminate p.
  exact (QposMake an ad).
 compute in p.
 abstract discriminate p.
Defined.
(* begin hide *)
Implicit Arguments mkQpos [a].
(* end hide *)
Lemma QposAsmkQpos : forall (a:Q) (p:0<a), (QposAsQ (mkQpos p))=a.
Proof.
 intros [[|an|an] ad] p.
   discriminate.
  reflexivity.
 discriminate.
Qed.
(* begin hide *)
Implicit Arguments QposAsmkQpos [a].
(* end hide *)
Lemma QposAsQposMake : forall a b, (QposAsQ (QposMake a b)) = (Zpos a)#b.
Proof.
 trivial.
Qed.
(* begin hide *)
Hint Rewrite QposAsmkQpos QposAsQposMake : QposElim.
(* end hide *)

(**
*** Equality
*)
Definition QposEq (a b:Qpos) := Qeq a b.

Add Relation Qpos QposEq
 reflexivity proved by (fun (x:Qpos) => refl_Qeq x)
 symmetry proved by (fun (x y:Qpos) => sym_Qeq x y)
 transitivity proved by (fun (x y z:Qpos) => trans_Qeq x y z) as QposSetoid.

Definition QposAp (a b:Qpos) := Qap a b.

(**
*** Addition
*)
Definition Qpos_plus (x y:Qpos) : Qpos.
Proof.
 intros x y.
 apply mkQpos with (x+y).
 abstract (apply: plus_resp_pos; apply Qpos_prf).
Defined.

Infix "+" := Qpos_plus : Qpos_scope.
(* begin hide *)
Add Morphism Qpos_plus : Qpos_plus_wd.
Proof.
 intros x1 x2 Hx y1 y2 Hy.
 unfold QposEq in *.
 unfold Qpos_plus.
 autorewrite with QposElim.
 apply Qplus_comp; assumption.
Qed.
(* end hide *)
Lemma Q_Qpos_plus : forall (x y:Qpos), ((x + y)%Qpos:Q)=(x:Q)+(y:Q).
Proof.
 trivial.
Qed.
(* begin hide *)
Hint Rewrite Q_Qpos_plus : QposElim.
(* end hide *)
(**
*** Multiplicaiton
*)
Definition Qpos_mult (x y:Qpos) : Qpos.
Proof.
 intros x y.
 apply mkQpos with (x*y).
 abstract (apply: mult_resp_pos; apply Qpos_prf).
Defined.

Infix "*" := Qpos_mult : Qpos_scope.
(* begin hide *)
Add Morphism Qpos_mult : Qpos_mult_wd.
Proof.
 intros x1 x2 Hx y1 y2 Hy.
 unfold QposEq in *.
 unfold Qpos_mult.
 autorewrite with QposElim.
 apply Qmult_comp; assumption.
Qed.
(* end hide *)
Lemma Q_Qpos_mult : forall (x y:Qpos), ((x * y)%Qpos:Q)=(x:Q)*(y:Q).
Proof.
 trivial.
Qed.
(* begin hide *)
Hint Rewrite Q_Qpos_mult : QposElim.
(* end hide *)
(**
*** Inverse
*)
Definition Qpos_inv (x:Qpos) : Qpos :=
((QposDenominator x)#(QposNumerator x))%Qpos.
(* begin hide *)
Add Morphism Qpos_inv : Qpos_inv_wd.
Proof.
 intros [x1n x1d] [x2n x2d] Hx.
 unfold QposEq in *.
 unfold Qpos_inv.
 unfold Qeq in *.
 simpl in *.
 rewrite Pmult_comm.
 symmetry.
 rewrite Pmult_comm.
 apply Hx.
Qed.
(* end hide *)
Lemma Q_Qpos_inv : forall (x:Qpos), Qpos_inv x = / x :> Q.
Proof.
 trivial.
Qed.
Hint Rewrite Q_Qpos_inv : QposElim.

Notation "a / b" := (Qpos_mult a (Qpos_inv b)) : Qpos_scope.

(**
*** Tactics
These tactics solve Ring and Field equations over [Qpos] by converting
them to problems over [Q].
*)
Ltac QposRing :=
 unfold QposEq;
 autorewrite with QposElim;
 ring.

Ltac QposField :=
 unfold QposEq;
 autorewrite with QposElim;
 field.

(** This is a standard way of decomposing a rational b that is greater than
a into a plus a positive value c. *)
Lemma Qpos_lt_plus : forall (a b:Q),
 a< b ->
 {c:Qpos | b==(a+c)}.
Proof.
 intros.
 assert (0<b-a).
  apply: shift_zero_less_minus.
  assumption.
 exists (mkQpos H0).
 QposRing.
Defined.
(* begin hide *)
Implicit Arguments Qpos_lt_plus [a b].
(* end hide *)
(**
*** Power
*)
Lemma Qpos_power_pos : forall (x:Qpos) z, 0 < x^z.
Proof.
 intros x z.
 destruct (Qle_lt_or_eq _ _ (Qpower_pos x z (Qlt_le_weak _ _ (Qpos_prf x))));[assumption|].
 destruct z.
   discriminate H.
  elim (Qpower_not_0_positive x p).
   apply Qpos_nonzero.
  symmetry; assumption.
 elim (Qpower_not_0_positive (/x) p).
  change (~(Qpos_inv x) == 0).
  apply Qpos_nonzero.
 change ((/x)^p==0).
 rewrite -> Qinv_power.
 symmetry; assumption.
Qed.

Definition Qpos_power (x:Qpos) (z:Z) : Qpos.
Proof.
 intros x z.
 apply mkQpos with (x^z).
 apply Qpos_power_pos.
Defined.

Infix "^" := Qpos_power : Qpos_scope.

(** The default relation on Z is [eqm] otherwise. *)
Instance Z_default : @DefaultRelation Z (@eq Z).
(* begin hide *)
Add Morphism Qpos_power : Qpos_power_wd.
Proof.
 intros x1 x2 Hx y.
 unfold QposEq in *.
 unfold Qpos_power.
 autorewrite with QposElim.
 rewrite -> Hx.
 reflexivity.
Qed.
(* end hide *)
Lemma Q_Qpos_power : forall (x:Qpos) z, ((x^z)%Qpos:Q)==(x:Q)^z.
Proof.
 intros.
 unfold Qpos_power.
 autorewrite with QposElim.
 reflexivity.
Qed.
Hint Rewrite Q_Qpos_power : QposElim.

(**
*** Summing lists
*)
Definition QposSum (l:list Qpos) : Q := fold_right
(fun (x:Qpos) (y:Q) => x+y) (Zero:Q) l.

Lemma QposSumNonNeg : forall l, 0 <= QposSum l.
Proof.
 induction l.
  apply: leEq_reflexive.
 simpl.
 apply: plus_resp_nonneg.
  apply: less_leEq.
  apply Qpos_prf.
 assumption.
Qed.

(** A version of [Qred] for [Qpos]. *)
Lemma QposRed_prf : forall (a:Q), (0 < a) -> (0 < Qred a).
Proof.
 intros a Ha.
 rewrite -> Qred_correct.
 assumption.
Qed.

Definition QposRed (a:Qpos) : Qpos := mkQpos (QposRed_prf a (Qpos_prf a)).

Lemma QposRed_complete : forall p q : Qpos, p == q -> QposRed p = QposRed q.
Proof.
 intros p q H.
 unfold QposRed.
 generalize (QposRed_prf p (Qpos_prf p)).
 generalize (QposRed_prf q (Qpos_prf q)).
 rewrite (Qred_complete p q H).
 unfold Qlt, Zlt.
 intros A B.
 assert (X:forall x y : comparison, x = y \/ x <> y).
  decide equality.
 rewrite (eq_proofs_unicity X A B).
 reflexivity.
Qed.

Lemma QposRed_correct : forall p, QposRed p == p.
Proof.
 unfold QposRed.
 intros p.
 autorewrite with QposElim.
 apply Qred_correct.
Qed.
