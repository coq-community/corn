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

From Coq Require Export QArith.
From Coq Require Import Qpower.
Require Import CoRN.model.ordfields.Qordfield.
Require Import CoRN.algebra.COrdFields2.
From Coq Require Import Eqdep_dec.
Require Import CoRN.tactics.CornTac.
From Coq Require Import Qround.
From Coq Require Import Qabs.
Require Import CoRN.stdlib_omissions.Q.

(* Backwards compatibility for Hint Rewrite locality attributes *)
Set Warnings "-unsupported-attributes".

Local Open Scope Q_scope.

(**
* [Qpos]
*)

Definition Qpos: Set := sig (Qlt 0).

Program Definition QposMake (num den: positive): Qpos := num # den.
Next Obligation. auto with *. Qed.

Notation "a # b" := (QposMake a b) (at level 55, no associativity) : Qpos_scope.

Bind Scope Qpos_scope with Qpos.
Delimit Scope Qpos_scope with Qpos.

Program Definition integral_Qpos (p: positive): Qpos := (p:Q).

Coercion integral_Qpos: positive >-> Qpos.

(** There is an injection from [Qpos] to [Q] that we make into a
coercion. *)

Definition QposAsQ: Qpos -> Q := @proj1_sig _ _.

Coercion QposAsQ : Qpos >-> Q.

(** Basic properties about [Qpos] *)
Definition Qpos_prf : forall a:Qpos, 0 < a := @proj2_sig _ _.

#[global]
Hint Immediate Qpos_prf.

Lemma Qpos_nonzero : forall x:Qpos, (x:Q)[#]0.
Proof.
 intros ?.
 apply: pos_ap_zero.
 apply Qpos_prf.
Qed.

Lemma Qpos_nonzero' (q: Qpos): ~ q == 0.
  (* simpler variant that actually shows up as proof obligations *)
Proof. apply Qpos_nonzero. Qed.

#[global]
Hint Immediate Qpos_nonzero'.

Lemma Qpos_nonneg : forall a:Qpos, 0 <= a.
Proof. intros [??]. auto with *. Qed.

#[global]
Hint Immediate Qpos_nonneg.

Lemma Qopp_Qpos_neg (x: Qpos): -x < 0.
Proof. apply Qopp_Qlt_0_r. auto. Qed.

#[global]
Hint Immediate Qopp_Qpos_neg.

(** Any positive rational number can be transformed into a [Qpos]. *)
Definition mkQpos: forall (a:Q) (p:0 < a), Qpos := @exist Q (Qlt 0).

(* begin hide *)
Arguments mkQpos [a].
(* end hide *)
Lemma QposAsmkQpos : forall (a:Q) (p:0<a), (QposAsQ (mkQpos p))=a.
Proof.
 intros [[|an|an] ad] p.
   discriminate.
  reflexivity.
 discriminate.
Qed.
(* begin hide *)
Arguments QposAsmkQpos [a].
(* end hide *)

Lemma positive_Z (z: Z): Z.lt 0 z -> sig (fun p: positive => Zpos p = z).
 destruct z; intros.
   intros.
   elim (Z.lt_irrefl _ H).
  exists p.
  reflexivity.
 exfalso.
 apply (Zlt_asym _ _ H).
 auto with *.
Defined.

(* todo: move this Qlt_uniq stuff elsewhere *)
From Coq Require Eqdep_dec.

Definition comparison_eq_dec (a b: comparison): { a = b } + { a <> b}.
 destruct a, b; try (left; reflexivity); try (right; discriminate).
Defined.

Lemma Zlt_uniq (a b: Z) (p q: (a < b)%Z): p = q.
Proof.
 unfold Z.lt in *. destruct p. intros.
 apply (Eqdep_dec.K_dec_set comparison_eq_dec).
 reflexivity.
Qed.

Lemma Qlt_uniq (a b: Q) (p q: a < b): p = q.
Proof. intros. apply Zlt_uniq. Qed.

Program Definition Qpos_as_positive_ratio (q: Qpos):
  sig (fun ps: positive * positive => q = QposMake (fst ps) (snd ps)) :=
  (positive_Z (Qnum q) _, Qden q).

Next Obligation.
 destruct q as [[??] ?]. unfold Qlt in *. simpl in *. auto with *.
Qed.

Next Obligation.
 destruct q as [[??] ?]. simpl.
 destruct positive_Z. simpl.
 subst. unfold QposMake.
 f_equal. apply Qlt_uniq.
Qed.

Lemma Qpos_positive_numerator_rect (P: Qpos -> Type):
  (forall (a b: positive), P (a # b)%Qpos) -> forall q, P q.
Proof.
 intros H q.
 destruct (Qpos_as_positive_ratio q).
 subst.
 apply H.
Defined.

Lemma QposAsQposMake : forall a b, (QposAsQ (QposMake a b)) = (Zpos a)#b.
Proof.
 trivial.
Qed.

(* begin hide *)
#[global]
Hint Rewrite QposAsmkQpos QposAsQposMake : QposElim.
(* end hide *)

(**
*** Equality
*)
Definition QposEq (a b:Qpos) := Qeq a b.
#[global]
Instance Qpos_default : @DefaultRelation Qpos QposEq | 2 := {}.

Add Relation Qpos QposEq
 reflexivity proved by (fun (x:Qpos) => Qeq_refl x)
 symmetry proved by (fun (x y:Qpos) => Qeq_sym x y)
 transitivity proved by (fun (x y z:Qpos) => Qeq_trans x y z) as QposSetoid.

Definition QposAp (a b:Qpos) := Qap a b.

Definition Qpos_PI (a b: Qpos): (a: Q) = b -> a = b.
Proof.
 destruct a, b.
 simpl. intros. subst.
 f_equal. apply Qlt_uniq.
Qed.

(**
*** Addition
*)
Program Definition Qpos_plus (x y:Qpos) : Qpos := Qplus x y.

Next Obligation.
 apply: plus_resp_pos; apply Qpos_prf.
Qed.

Infix "+" := Qpos_plus : Qpos_scope.
(* begin hide *)
Add Morphism Qpos_plus : Qpos_plus_wd.
Proof.
 intros x1 x2 Hx y1 y2 Hy.
 unfold QposEq in *.
 unfold Qpos_plus.
 simpl.
 apply Qplus_comp; assumption.
Qed.
(* end hide *)
Lemma Q_Qpos_plus : forall (x y:Qpos), ((x + y)%Qpos:Q)=(x:Q)+(y:Q).
Proof.
 trivial.
Qed.
(* begin hide *)
#[global]
Hint Rewrite Q_Qpos_plus : QposElim.
(* end hide *)

(**
*** One
*)
Program Definition Qpos_one : Qpos := 1.
Next Obligation. auto with qarith. Qed.
Notation "1" := Qpos_one : Qpos_scope.

Lemma Q_Qpos_one : (1%Qpos:Q)=(1:Q).
Proof. trivial. Qed.
(* begin hide *)
#[global]
Hint Rewrite Q_Qpos_one : QposElim.
(* end hide *)

(**
*** Multiplication
*)

Program Definition Qpos_mult (x y:Qpos) : Qpos := Qmult x y.

Infix "*" := Qpos_mult : Qpos_scope.
(* begin hide *)
Add Morphism Qpos_mult : Qpos_mult_wd.
Proof.
 intros x1 x2 Hx y1 y2 Hy.
 unfold QposEq in *.
 unfold Qpos_mult.
 simpl.
 apply Qmult_comp; assumption.
Qed.
(* end hide *)
Lemma Q_Qpos_mult : forall (x y:Qpos), ((x * y)%Qpos:Q)=(x:Q)*(y:Q).
Proof.
 trivial.
Qed.
(* begin hide *)
#[global]
Hint Rewrite Q_Qpos_mult : QposElim.
(* end hide *)
(**
*** Inverse
*)

Program Definition Qpos_inv (x:Qpos): Qpos := / x.

Next Obligation.
 apply Qinv_lt_0_compat.
 destruct x.
 assumption.
Qed.

(* begin hide *)
Add Morphism Qpos_inv : Qpos_inv_wd.
Proof.
 intros [x P] [y Q] E.
 unfold QposEq in *.
 simpl in *.
 rewrite E.
 reflexivity.
Qed.
(* end hide *)
Lemma Q_Qpos_inv : forall (x:Qpos), Qpos_inv x = / x :> Q.
Proof.
 trivial.
Qed.
#[global]
Hint Rewrite Q_Qpos_inv : QposElim.

Notation "a / b" := (Qpos_mult a (Qpos_inv b)) : Qpos_scope.

(**
*** Tactics
These tactics solve Ring and Field equations over [Qpos] by converting
them to problems over [Q].
*)
Ltac QposRing :=
 unfold canonical_names.equiv, QposEq;
 autorewrite with QposElim;
 ring.

Ltac QposField :=
 unfold canonical_names.equiv, QposEq;
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
Arguments Qpos_lt_plus [a b].
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
 apply mkQpos with (x^z).
 apply Qpos_power_pos.
Defined.

Infix "^" := Qpos_power : Qpos_scope.
(* begin hide *)
#[global]
Instance Qpos_power_wd: Proper (QposEq ==> @eq Z ==> QposEq) Qpos_power.
Proof.
 intros x1 x2 Hx y1 y2 Hy.
 unfold QposEq in *.
 unfold Qpos_power.
 autorewrite with QposElim.
 simpl.
 now rewrite Hx, Hy.
Qed.
(* end hide *)
Lemma Q_Qpos_power : forall (x:Qpos) z, ((x^z)%Qpos:Q)==(x:Q)^z.
Proof.
 intros.
 unfold Qpos_power.
 autorewrite with QposElim.
 reflexivity.
Qed.
#[global]
Hint Rewrite Q_Qpos_power : QposElim.

(**
*** Summing lists
*)
Definition QposSum (l:list Qpos) : Q := fold_right
(fun (x:Qpos) (y:Q) => x+y) ([0]:Q) l.

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

#[global]
Instance QposRed_complete: Proper (QposEq ==> eq) QposRed.
Proof.
 intros p q H.
 unfold QposRed.
 generalize (QposRed_prf p (Qpos_prf p)).
 generalize (QposRed_prf q (Qpos_prf q)).
 rewrite (Qred_complete p q H).
 unfold Qlt, Z.lt.
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
 simpl.
 apply Qred_correct.
Qed.

(* For a Qpos we know its ceiling is positive: *)

Definition QposCeiling (q: Qpos): positive :=
  match Qceiling q with
  | Zpos p => p
  | _ => 1%positive (* impossible *)
  end.

Lemma QposCeiling_Qceiling (q: Qpos): (QposCeiling q: Z) = Qceiling q.
Proof with auto with *.
 unfold QposCeiling.
 pose proof Qle_ceiling q.
 destruct (Qceiling q); try reflexivity; exfalso; destruct q; simpl in *.
  apply (Qlt_not_le 0 x q)...
 apply (Qlt_irrefl 0).
 apply Qlt_le_trans with x...
 apply Qle_trans with (Zneg p)...
Qed.

(* This function is only defined for non zero elements, so in case of 0, we yield a dummy *)
Definition QabsQpos (x : Q) : Qpos :=
  match x with
  | 0 # _ => (1%Qpos)
  | (Zpos an) # ad => (an # ad)%Qpos
  | (Zneg an) # ad => (an # ad)%Qpos
  end.

Lemma QabsQpos_correct x : ~x == 0 -> QabsQpos x == Qabs x.
Proof with auto with qarith.
 intros E. destruct x as [n d]. simpl. 
 destruct n...
 destruct E...
Qed.

Lemma QabsQpos_Qpos (x : Qpos) : QposEq (QabsQpos x) x.
Proof with auto with qarith.
 unfold QposEq.
 rewrite QabsQpos_correct...
 apply Qabs_pos...
Qed.
