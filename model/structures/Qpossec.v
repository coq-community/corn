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

(** printing Qpos $\mathbb{Q}^{+}$ #Q<SUP>+</SUP># *)

Require Export QArith.
Require Import Qordfield.
Require Import COrdFields2.
Require Import Eqdep_dec.
Require Import CornTac.

Record Qpos : Set := QposMake 
{QposNumerator : positive
;QposDenominator : positive
}.

Notation "a # b" := (QposMake a b) (at level 55, no associativity) : Qpos_scope.

Bind Scope Qpos_scope with Qpos.
Delimit Scope Qpos_scope with Qpos.

Definition QposAsQ (a:Qpos) : Q :=
(Zpos (QposNumerator a))#(QposDenominator a).

Coercion QposAsQ : Qpos >-> Q.

Lemma Qpos_prf : forall a:Qpos, 0 < a.
Proof.
firstorder.
Qed.

Lemma Qpos_nonzero : forall x:Qpos, (x:Q)[#]0.
Proof.
intros x.
rsapply pos_ap_zero.
apply Qpos_prf.
Qed.

Lemma Qpos_nonneg : forall a:Qpos, 0 <= a.
Proof.
intros a.
apply Qlt_le_weak.
apply Qpos_prf.
Qed.

Definition mkQpos (a:Q) (p:0 < a) : Qpos.
intros [an ad] p.
destruct an as [|an|an].
compute in p.
abstract discriminate p.
exact (QposMake an ad).
compute in p.
abstract discriminate p.
Defined.

Implicit Arguments mkQpos [a].

Lemma QposAsmkQpos : forall (a:Q) (p:0<a), (QposAsQ (mkQpos p))=a.
Proof.
intros [[|an|an] ad] p.
discriminate.
reflexivity.
discriminate.
Qed.

Implicit Arguments QposAsmkQpos [a].

Lemma QposAsQposMake : forall a b, (QposAsQ (QposMake a b)) = (Zpos a)#b.
Proof.
trivial.
Qed.

Hint Rewrite QposAsmkQpos QposAsQposMake : QposElim.

Definition QposEq (a b:Qpos) := Qeq a b.

Add Relation Qpos QposEq
 reflexivity proved by (fun (x:Qpos) => refl_Qeq x)
 symmetry proved by (fun (x y:Qpos) => sym_Qeq x y)
 transitivity proved by (fun (x y z:Qpos) => trans_Qeq x y z) as QposSetoid.

Definition QposAp (a b:Qpos) := Qap a b.

Definition Qpos_plus (x y:Qpos) : Qpos. 
intros x y.
apply mkQpos with (x+y).
abstract (rsapply plus_resp_pos; apply Qpos_prf).
Defined.

Infix "+" := Qpos_plus : Qpos_scope.

Add Morphism Qpos_plus : Qpos_plus_wd.
intros x1 x2 Hx y1 y2 Hy.
unfold QposEq in *.
unfold Qpos_plus.
autorewrite with QposElim.
apply Qplus_comp; assumption.
Qed.

Lemma Q_Qpos_plus : forall (x y:Qpos), ((x + y)%Qpos:Q)=(x:Q)+(y:Q).
Proof.
trivial.
Qed.
Hint Rewrite Q_Qpos_plus : QposElim.

Definition Qpos_mult (x y:Qpos) : Qpos. 
intros x y.
apply mkQpos with (x*y).
abstract (rsapply mult_resp_pos; apply Qpos_prf).
Defined.

Infix "*" := Qpos_mult : Qpos_scope.

Add Morphism Qpos_mult : Qpos_mult_wd.
intros x1 x2 Hx y1 y2 Hy.
unfold QposEq in *.
unfold Qpos_mult.
autorewrite with QposElim.
apply Qmult_comp; assumption.
Qed.

Lemma Q_Qpos_mult : forall (x y:Qpos), ((x * y)%Qpos:Q)=(x:Q)*(y:Q).
Proof.
trivial.
Qed.
Hint Rewrite Q_Qpos_mult : QposElim.

Definition Qpos_inv (x:Qpos) : Qpos :=
((QposDenominator x)#(QposNumerator x))%Qpos.

Add Morphism Qpos_inv : Qpos_inv_wd.
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

Lemma Q_Qpos_inv : forall (x:Qpos), Qpos_inv x = / x :> Q.
Proof.
trivial.
Qed.
Hint Rewrite Q_Qpos_inv : QposElim.

Notation "a / b" := (Qpos_mult a (Qpos_inv b)) : Qpos_scope.

Ltac QposRing :=
 unfold QposEq;
 autorewrite with QposElim;
 ring.

Ltac QposField :=
 unfold QposEq;
 autorewrite with QposElim;
 field.

Lemma Qpos_lt_plus : forall (a b:Q), 
 a< b ->
 {c:Qpos | b==(a+c)}.
Proof.
intros.
assert (0<b-a).
rsapply shift_zero_less_minus.
assumption.
exists (mkQpos H0).
QposRing.
Defined.

Implicit Arguments Qpos_lt_plus [a b].

Definition QposSum (l:list Qpos) : Q := fold_right
(fun (x:Qpos) (y:Q) => x+y) (Zero:Q) l.

Lemma QposSumNonNeg : forall l, 0 <= QposSum l.
Proof.
induction l.
rsapply leEq_reflexive.
simpl.
rsapply plus_resp_nonneg.
rsapply less_leEq.
apply Qpos_prf.
assumption.
Qed.

Lemma QposRed_prf : forall (a:Q), (0 < a) -> (0 < Qred a).
Proof.
intros a Ha.
rewrite Qred_correct.
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
