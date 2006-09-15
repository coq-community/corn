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
Require Export CSetoids.
Require Export CSetoidFun.            

Definition ap_fun (A B : CSetoid) (f g : CSetoid_fun A B) :=
  {a : A | f a[#]g a}.

Definition eq_fun (A B : CSetoid) (f g : CSetoid_fun A B) :=
  forall a : A, f a[=]g a.


Lemma irrefl_apfun : forall A B : CSetoid, irreflexive (ap_fun A B).
intros A B.
unfold irreflexive in |- *.
intros f.
unfold ap_fun in |- *.
red in |- *.
intro H.
elim H.
intros a H0.
set (H1 := ap_irreflexive_unfolded B (f a)) in *.
intuition.
Qed.

Lemma cotrans_apfun : forall A B : CSetoid, cotransitive (ap_fun A B).
intros A B.
unfold cotransitive in |- *.
unfold ap_fun in |- *.
intros f g H h.
elim H.
clear H.
intros a H.
set (H1 := ap_cotransitive B (f a) (g a) H (h a)) in *.
elim H1.
clear H1.
intros H1.
left.
exists a.
exact H1.

clear H1.
intro H1.
right.
exists a.
exact H1.
Qed.

Lemma ta_apfun : forall A B : CSetoid, tight_apart (eq_fun A B) (ap_fun A B).
unfold tight_apart in |- *.
unfold ap_fun in |- *.
unfold eq_fun in |- *.
intros A B f g.
split.
intros H a.
red in H.
apply not_ap_imp_eq.
red in |- *.
intros H0.
apply H.
exists a.
exact H0.
intros H.
red in |- *.

intro H1.
elim H1.
intros a X.
set (H2 := eq_imp_not_ap B (f a) (g a) (H a) X) in *.
exact H2.
Qed.

Lemma sym_apfun : forall A B : CSetoid, Csymmetric (ap_fun A B).
unfold Csymmetric in |- *.
unfold ap_fun in |- *.
intros A B f g H.
elim H.
clear H.
intros a H.
exists a.
apply ap_symmetric_unfolded.
exact H.
Qed.

Definition FS_is_CSetoid (A B : CSetoid) :=
  Build_is_CSetoid (CSetoid_fun A B) (eq_fun A B) (
    ap_fun A B) (irrefl_apfun A B) (sym_apfun A B) (
    cotrans_apfun A B) (ta_apfun A B).

Definition FS_as_CSetoid (A B : CSetoid) :=
  Build_CSetoid (CSetoid_fun A B) (eq_fun A B) (ap_fun A B)
    (FS_is_CSetoid A B).

Print associative.
Definition comp (A B C : CSetoid) :
  FS_as_CSetoid A B -> FS_as_CSetoid B C -> FS_as_CSetoid A C.
intros A B C f g.
set (H := compose_CSetoid_fun A B C f g) in *.
exact H.
Defined.

Definition comp_as_bin_op (A : CSetoid) : CSetoid_bin_op (FS_as_CSetoid A A).
intro A.
unfold CSetoid_bin_op in |- *.
eapply Build_CSetoid_bin_fun with (comp A A A).
unfold bin_fun_strext in |- *.
unfold comp in |- *.
intros f1 f2 g1 g2.
simpl in |- *.
unfold ap_fun in |- *.
unfold compose_CSetoid_fun in |- *.
simpl in |- *.
elim f1.
unfold fun_strext in |- *.
clear f1.
intros f1 Hf1.
elim f2.
unfold fun_strext in |- *.
clear f2.
intros f2 Hf2.
elim g1.
unfold fun_strext in |- *.
clear g1.
intros g1 Hg1.
elim g2.
unfold fun_strext in |- *.
clear g2.
intros g2 Hg2.
simpl in |- *.
intro H.
elim H.
clear H.
intros a H.
set (H0 := ap_cotransitive A (g1 (f1 a)) (g2 (f2 a)) H (g2 (f1 a))) in *.
elim H0.
clear H0.
intro H0.
right.
exists (f1 a).
exact H0.

clear H0.
intro H0.
left.
exists a.
apply Hg2.
exact H0.
Defined.


Lemma assoc_comp : forall A : CSetoid, associative (comp_as_bin_op A).
unfold associative in |- *.
unfold comp_as_bin_op in |- *.
intros A f g h.
simpl in |- *.
unfold eq_fun in |- *.
simpl in |- *.
intuition.
Qed.

Require Import CSemiGroups.

Definition FS_as_CSemiGroup (A : CSetoid) :=
  Build_CSemiGroup (FS_as_CSetoid A A) (comp_as_bin_op A) (assoc_comp A).

Require Import CMonoids.

Definition FS_id (A : CSetoid) : FS_as_CSetoid A A.
intro A.
unfold FS_as_CSetoid in |- *.
simpl in |- *.
exact (id_un_op A).
Defined.

Lemma id_is_rht_unit :
 forall A : CSetoid, is_rht_unit (comp_as_bin_op A) (FS_id A).
unfold is_rht_unit in |- *.
unfold comp_as_bin_op in |- *.
unfold FS_id in |- *.
simpl in |- *.
unfold eq_fun in |- *.
unfold id_un_op in |- *.
simpl in |- *.
intuition.
Qed.

Lemma id_is_lft_unit :
 forall A : CSetoid, is_lft_unit (comp_as_bin_op A) (FS_id A).
unfold is_lft_unit in |- *.
unfold comp_as_bin_op in |- *.
unfold FS_id in |- *.
simpl in |- *.
unfold eq_fun in |- *.
unfold id_un_op in |- *.
simpl in |- *.
intuition.
Qed.

Definition FS_is_CMonoid (A : CSetoid) :=
  Build_is_CMonoid (FS_as_CSemiGroup A) (FS_id A) (
    id_is_rht_unit A) (id_is_lft_unit A).

Definition FS_as_CMonoid (A : CSetoid) :=
  Build_CMonoid (FS_as_CSemiGroup A) (FS_id A) (FS_is_CMonoid A).


Definition PS_as_CMonoid (A : CSetoid) :=
  Build_SubCMonoid (FS_as_CMonoid A) (bijective (A:=A) (B:=A)) (
    id_is_bij A) (comp_resp_bij A A A).  

Require Import CGroups.

Lemma Inv_is_bij :
 forall (A B : CSetoid) (f : CSetoid_fun A B) (H : bijective f),
 bijective (Inv f H).
intros A B f.
case f.
unfold fun_strext in |- *.
intros f0 H5.
unfold bijective in |- *.
intro H.
elim H.
clear H.
unfold injective in |- *.
unfold surjective in |- *.
simpl.
intros H0 H1.
unfold invfun in |- *.
simpl in |- *.
unfold sigT_rect in |- *.
split.
intros a0 a1 H2.
case inv.
case inv.
intros x H3 y H4.
simpl in H3.
simpl in H4.
apply H5.
astepl a0.
astepr a1.
exact H2.

intros b.
exists (f0 b).
case inv.
simpl in |- *.
intros x H2.
apply not_ap_imp_eq.
red in |- *.
intro H3.
set (H4 := H0 x b H3) in *.
set (H6 := ap_imp_neq B (f0 x) (f0 b) H4) in *.
intuition.
Qed.


(* Lemma Inv_is_bij :
 forall (A B : CSetoid) (f : CSetoid_fun A B) (H : bijective f),
 bijective (Inv f H).
intros A B f.
case f.
unfold fun_strext in |- *.
intros f0 H5.
unfold bijective in |- *.
intro H.
elim H.
clear H.
unfold injective in |- *.
unfold surjective in |- *.
intros H0 H1.
split.
unfold Inv in |- *.
simpl in |- *.
unfold invfun in |- *.
simpl in |- *.
unfold sigT_rect in |- *.
intros a0 a1 H2.
case H1.
case (H1 a1).
intros x H3 y H4.
simpl in H3.
simpl in H4.
simpl in H0.
simpl in H1.
apply H5.
astepl a0.
astepr a1.
exact H2.

simpl in |- *.
unfold invfun in |- *.
simpl in |- *.
unfold sigT_rect in |- *.
intros b.
exists (f0 b).
case (H1 (f0 b)).
simpl in |- *.
intros x H2.
simpl in H0.
simpl in H1.
apply not_ap_imp_eq.
red in |- *.
intro H3.
set (H4 := H0 x b H3) in *.
set (H6 := ap_imp_neq B (f0 x) (f0 b) H4) in *.
intuition.
Qed.*)


Definition PS_Inv (A : CSetoid) : PS_as_CMonoid A -> PS_as_CMonoid A.
intro A.
simpl in |- *.
intros f.
elim f.
intros fo prfo.
set (H0 := Inv fo prfo) in *.
apply Build_subcsetoid_crr with H0.
unfold H0 in |- *.
apply Inv_is_bij.
Defined.

Definition Inv_as_un_op (A : CSetoid) : CSetoid_un_op (PS_as_CMonoid A).
intro A.
unfold CSetoid_un_op in |- *.
apply Build_CSetoid_fun with (PS_Inv A).
unfold fun_strext in |- *.
intros x y.
case x.
case y.
simpl in |- *.
intros f H g H0.
unfold ap_fun in |- *.
intro H1.
elim H1.
clear H1.
intros a H1.
exists (Inv g H0 a).
astepl a.
2: simpl in |- *.
2: apply eq_symmetric_unfolded.
2: apply inv1.
unfold bijective in H.
elim H.
unfold injective in |- *.
intros H2 H3.
astepl (f (Inv f H a)).
apply H2.
apply ap_symmetric_unfolded.
exact H1.
simpl in |- *.
apply inv1.
Defined.

Lemma PS_is_CGroup :
 forall A : CSetoid, is_CGroup (PS_as_CMonoid A) (Inv_as_un_op A). 
intro A.
unfold is_CGroup in |- *.
intro x.
unfold is_inverse in |- *.
simpl in |- *.
split.
case x.
simpl in |- *.
intros f H.
unfold eq_fun in |- *.
intro a.
unfold comp in |- *.
simpl in |- *.
apply inv2.

case x.
simpl in |- *.
intros f H.
unfold eq_fun in |- *.
intro a.
unfold comp in |- *.
simpl in |- *.
apply inv1.
Qed.

Definition PS_as_CGroup (A : CSetoid) :=
  Build_CGroup (PS_as_CMonoid A) (Inv_as_un_op A) (PS_is_CGroup A).

(* In het algemeen niet Abels! *)
