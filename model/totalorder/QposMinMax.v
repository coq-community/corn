(*
Copyright © 2006-2008 Russell O’Connor

Permission is hereby granted, free of charge, to any person obtaining a copy of
this proof and associated documentation files (the "Proof"), to deal in
the Proof without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Proof, and to permit persons to whom the Proof is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Proof.

THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
*)

Require Import Qpossec.
Require Import QArith.
Require Import QMinMax.
Require Import TotalOrder.

(**
** Example of a Total Order: <Qpos, Qpos_le, Qpos_min, Qpos_max>
*)

Definition Qpos_le_total (x y : Qpos) : {x <= y} + {y <= x} :=
match Qlt_le_dec_fast x y with
| left p => left _ (Qlt_le_weak _ _ p)
| right p => right _ p
end.

Lemma Qpos_eq_le_def : forall (x y: Qpos), x == y <-> x <= y /\ y <= x.
Proof.
intros.
split.
intros H; rewrite H.
firstorder using Qle_refl.
firstorder using Qle_antisym.
Qed.

Definition Qpos_monotone : (Qpos -> Qpos) -> Prop := Default.monotone (fun (x y:Qpos) => x <= y).
Definition Qpos_antitone : (Qpos -> Qpos) -> Prop := Default.antitone (fun (x y:Qpos) => x <= y).
Definition Qpos_min : Qpos -> Qpos -> Qpos := Default.min _ _ Qpos_le_total.
Definition Qpos_max : Qpos -> Qpos -> Qpos := Default.max _ _ Qpos_le_total.

Definition Qpos_min_case :
 forall (x y:Qpos) (P : Qpos -> Type), (x <= y -> P x) -> (y <= x -> P y) -> P (Qpos_min x y) :=
 Default.min_case _ _ Qpos_le_total.
Definition Qpos_max_case :
 forall (x y:Qpos) (P : Qpos -> Type), (y <= x -> P x) -> (x <= y -> P y) -> P (Qpos_max x y) :=
 Default.max_case _ _ Qpos_le_total.

Definition QposTotalOrder : TotalOrder.
apply makeTotalOrder with 
  Qpos QposEq (fun (x y:Qpos) => x <= y) Qpos_monotone Qpos_antitone Qpos_min Qpos_max.
apply Qpos_eq_le_def.
firstorder using Qle_refl.
firstorder using Qle_trans.
firstorder using Qpos_le_total.
firstorder using PartialOrder.Default.monotone_def.
firstorder using PartialOrder.Default.antitone_def.
apply (TotalOrder.Default.min_def1 _ _ _ Qpos_eq_le_def Qpos_le_total).
apply (TotalOrder.Default.min_def2 _ _ _ Qpos_eq_le_def Qpos_le_total).
apply (TotalOrder.Default.max_def1 _ _ _ Qpos_eq_le_def Qpos_le_total).
apply (TotalOrder.Default.max_def2 _ _ _ Qpos_eq_le_def Qpos_le_total).
Defined.
(* begin hide *)
Add Morphism Qpos_min : Qpos_min_compat.
exact (@meet_compat QposTotalOrder).
Qed.

Add Morphism Qpos_max : Qpos_max_compat.
exact (@join_compat QposTotalOrder).
Qed.
(* end hide *)
Section QTotalOrder.

Let Qto := QposTotalOrder.

Definition Qpos_min_lb_l : forall x y : Qpos, Qpos_min x y <= x := @meet_lb_l Qto.
Definition Qpos_min_lb_r : forall x y : Qpos, Qpos_min x y <= y := @meet_lb_r Qto.
Definition Qpos_min_glb : forall x y z : Qpos, z <= x -> z <= y -> z <= (Qpos_min x y) :=
 @meet_glb Qto.
Definition Qpos_min_comm : forall x y : Qpos, Qpos_min x y == Qpos_min y x := @meet_comm Qto.
Definition Qpos_min_assoc : forall x y z : Qpos, Qpos_min x (Qpos_min y z) == Qpos_min (Qpos_min x y) z:= 
 @meet_assoc Qto.
Definition Qpos_min_idem : forall x : Qpos, Qpos_min x x == x := @meet_idem Qto.
Definition Qpos_le_min_l : forall x y : Qpos, x <= y <-> Qpos_min x y == x := @le_meet_l Qto.
Definition Qpos_le_min_r : forall x y : Qpos, y <= x <-> Qpos_min x y == y := @le_meet_r Qto.
Definition Qpos_min_irred : forall x y: Qpos, {Qpos_min x y == x} + {Qpos_min x y == y} := @meet_irred Qto.
Definition Qpos_min_monotone_r : forall a : Qpos, Qpos_monotone (Qpos_min a) :=
 @meet_monotone_r Qto.
Definition Qpos_min_monotone_l : forall a : Qpos, Qpos_monotone (fun x => Qpos_min x a) :=
 @meet_monotone_l Qto.
Definition Qpos_min_le_compat : 
 forall w x y z : Qpos, w <= y -> x <= z -> Qpos_min w x <= Qpos_min y z :=
 @meet_le_compat Qto.

Definition Qpos_max_ub_l : forall x y : Qpos, x <= Qpos_max x y := @join_ub_l Qto.
Definition Qpos_max_ub_r : forall x y : Qpos, y <= Qpos_max x y := @join_ub_r Qto.
Definition Qpos_max_glb : forall x y z : Qpos, x <= z -> y <= z -> (Qpos_max x y) <= z :=
 @join_lub Qto.
Definition Qpos_max_comm : forall x y : Qpos, Qpos_max x y == Qpos_max y x := @join_comm Qto.
Definition Qpos_max_assoc : forall x y z : Qpos, Qpos_max x (Qpos_max y z) == Qpos_max (Qpos_max x y) z:= 
 @join_assoc Qto.
Definition Qpos_max_idem : forall x : Qpos, Qpos_max x x == x := @join_idem Qto.
Definition Qpos_le_max_l : forall x y : Qpos, y <= x <-> Qpos_max x y == x := @le_join_l Qto.
Definition Qpos_le_max_r : forall x y : Qpos, x <= y <-> Qpos_max x y == y := @le_join_r Qto.
Definition Qpos_max_irred : forall x y: Qpos, {Qpos_max x y == x} + {Qpos_max x y == y} := @join_irred Qto.
Definition Qpos_max_monotone_r : forall a : Qpos, Qpos_monotone (Qpos_max a) :=
 @join_monotone_r Qto.
Definition Qpos_max_monotone_l : forall a : Qpos, Qpos_monotone (fun x => Qpos_max x a) :=
 @join_monotone_l Qto.
Definition Qpos_max_le_compat :
 forall w x y z : Qpos, w<=y -> x<=z -> Qpos_max w x <= Qpos_max y z :=
 @join_le_compat Qto.

Definition Qpos_min_max_absorb_l_l : forall x y : Qpos, Qpos_min x (Qpos_max x y) == x :=
 @meet_join_absorb_l_l Qto.
Definition Qpos_max_min_absorb_l_l : forall x y : Qpos, Qpos_max x (Qpos_min x y) == x :=
 @join_meet_absorb_l_l Qto.
Definition Qpos_min_max_absorb_l_r : forall x y : Qpos, Qpos_min x (Qpos_max y x) == x :=
 @meet_join_absorb_l_r Qto.
Definition Qpos_max_min_absorb_l_r : forall x y : Qpos, Qpos_max x (Qpos_min y x) == x :=
 @join_meet_absorb_l_r Qto.
Definition Qpos_min_max_absorb_r_l : forall x y : Qpos, Qpos_min (Qpos_max x y) x == x :=
 @meet_join_absorb_r_l Qto.
Definition Qpos_max_min_absorb_r_l : forall x y : Qpos, Qpos_max (Qpos_min x y) x == x :=
 @join_meet_absorb_r_l Qto.
Definition Qpos_min_max_absorb_r_r : forall x y : Qpos, Qpos_min (Qpos_max y x) x == x :=
 @meet_join_absorb_r_r Qto.
Definition Qpos_max_min_absorb_r_r : forall x y : Qpos, Qpos_max (Qpos_min y x) x == x :=
 @join_meet_absorb_r_r Qto.

Definition Qpos_min_max_eq : forall x y : Qpos, Qpos_min x y == Qpos_max x y -> x == y :=
 @meet_join_eq Qto.

Definition Qpos_max_min_distr_r : forall x y z : Qpos,
 Qpos_max x (Qpos_min y z) == Qpos_min (Qpos_max x y) (Qpos_max x z) := 
 @join_meet_distr_r Qto.
Definition Qpos_max_min_distr_l : forall x y z : Qpos,
 Qpos_max (Qpos_min y z) x == Qpos_min (Qpos_max y x) (Qpos_max z x) := 
 @join_meet_distr_l Qto.
Definition Qpos_min_max_distr_r : forall x y z : Qpos,
 Qpos_min x (Qpos_max y z) == Qpos_max (Qpos_min x y) (Qpos_min x z) := 
 @meet_join_distr_r Qto.
Definition Qpos_min_max_distr_l : forall x y z : Qpos,
 Qpos_min (Qpos_max y z) x == Qpos_max (Qpos_min y x) (Qpos_min z x) := 
 @meet_join_distr_l Qto.

(*I don't know who wants modularity laws, but here they are *)
Definition Qpos_max_min_modular_r : forall x y z : Qpos,
 Qpos_max x (Qpos_min y (Qpos_max x z)) == Qpos_min (Qpos_max x y) (Qpos_max x z) := 
 @join_meet_modular_r Qto.
Definition Qpos_max_min_modular_l : forall x y z : Qpos,
 Qpos_max (Qpos_min (Qpos_max x z) y) z == Qpos_min (Qpos_max x z) (Qpos_max y z) := 
 @join_meet_modular_l Qto.
Definition Qpos_min_max_modular_r : forall x y z : Qpos,
 Qpos_min x (Qpos_max y (Qpos_min x z)) == Qpos_max (Qpos_min x y) (Qpos_min x z) := 
 @meet_join_modular_r Qto.
Definition Qpos_min_max_modular_l : forall x y z : Qpos,
 Qpos_min (Qpos_max (Qpos_min x z) y) z == Qpos_max (Qpos_min x z) (Qpos_min y z) := 
 @meet_join_modular_l Qto.

Definition Qpos_min_max_disassoc : forall x y z : Qpos, Qpos_min (Qpos_max x y) z <= Qpos_max x (Qpos_min y z) :=
 @meet_join_disassoc Qto.

Lemma Qplus_monotone_r : forall a, Qpos_monotone (Qpos_plus a).
intros a x y Hxy.
repeat rewrite Q_Qpos_plus.
firstorder using Qle_refl Qplus_le_compat .
Qed.
Lemma Qplus_monotone_l : forall a, Qpos_monotone (fun x => Qpos_plus x a).
intros a x y Hxy.
repeat rewrite Q_Qpos_plus.
firstorder using Qle_refl Qplus_le_compat.
Qed.

Open Local Scope Qpos_scope.

Definition Qpos_min_plus_distr_r : (forall x y z : Qpos, Qpos_plus x (Qpos_min y z) == Qpos_min (Qpos_plus x y) (Qpos_plus x z))  :=
 fun a => @monotone_meet_distr Qto _ (Qplus_monotone_r a).
Definition Qpos_min_plus_distr_l : forall x y z : Qpos, Qpos_plus (Qpos_min y z) x == Qpos_min (Qpos_plus y x) (Qpos_plus z x) :=
 fun a => @monotone_meet_distr Qto _ (Qplus_monotone_l a).
Definition Qpos_max_plus_distr_r : forall x y z : Qpos, Qpos_plus x (Qpos_max y z) == Qpos_max (Qpos_plus x y) (Qpos_plus x z)  :=
 fun a => @monotone_join_distr Qto _ (Qplus_monotone_r a).
Definition Qpos_max_plus_distr_l : forall x y z : Qpos, Qpos_plus (Qpos_max y z) x == Qpos_max (Qpos_plus y x) (Qpos_plus z x) :=
 fun a => @monotone_join_distr Qto _ (Qplus_monotone_l a).

End QTotalOrder.

Lemma Q_Qpos_min : forall (x y:Qpos), ((Qpos_min x y)%Qpos:Q)==Qmin (x:Q) (y:Q).
Proof.
intros x y.
unfold Qpos_min.
unfold Qmin.
unfold Default.min.
destruct (Qpos_le_total x y) as [H|H];
destruct (Qle_total x y) as [H0|H0]; try reflexivity;
 apply Qle_antisym; auto.
Qed.
(* begin hide *)
Hint Rewrite Q_Qpos_min : QposElim.
(* end hide *)
Lemma Q_Qpos_max : forall (x y:Qpos), ((Qpos_max x y)%Qpos:Q)==Qmax (x:Q) (y:Q).
Proof.
intros x y.
unfold Qpos_max.
unfold Qmax.
unfold Default.max.
destruct (Qpos_le_total y x) as [H|H];
destruct (Qle_total y x) as [H0|H0]; try reflexivity;
 apply Qle_antisym; auto.
Qed.
(* begin hide *)
Hint Rewrite Q_Qpos_max : QposElim.
(* end hide *)