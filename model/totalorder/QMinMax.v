(*
Copyright © 2006 Russell O’Connor

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

Require Import QArith_base.
Require Import TotalOrder.

Opaque Qlt_le_dec.

Definition Qle_total x y : {x <= y} + {y <= x} :=
match Qlt_le_dec x y with
| left p => left _ (Qlt_le_weak _ _ p)
| right p => right _ p
end.

Lemma Qeq_le_def : forall x y, x == y <-> x <= y /\ y <= x.
Proof.
intros.
split.
intros H; rewrite H.
firstorder using Qle_refl.
firstorder using Qle_antisym.
Qed.

Definition Qmonotone : (Q -> Q) -> Prop := Default.monotone Qle.
Definition Qantitone : (Q -> Q) -> Prop := Default.antitone Qle.
Definition Qmin : Q -> Q -> Q := Default.min Q Qle Qle_total.
Definition Qmax : Q -> Q -> Q := Default.max Q Qle Qle_total.

Definition Qmin_case :
 forall x y (P : Q -> Type), (Qle x y -> P x) -> (Qle y x -> P y) -> P (Qmin x y) :=
 Default.min_case Q Qle Qle_total.
Definition Qmax_case :
 forall x y (P : Q -> Type), (Qle y x -> P x) -> (Qle x y -> P y) -> P (Qmax x y) :=
 Default.max_case Q Qle Qle_total.

Definition QTotalOrder : TotalOrder.
apply makeTotalOrder with 
  Q Qeq Qle Qmonotone Qantitone Qmin Qmax.
apply Qeq_le_def.
apply Qle_refl.
apply Qle_trans.
apply Qle_total.
firstorder using PartialOrder.Default.monotone_def.
firstorder using PartialOrder.Default.antitone_def.
apply (TotalOrder.Default.min_def1 Q Qeq Qle Qeq_le_def Qle_total).
apply (TotalOrder.Default.min_def2 Q Qeq Qle Qeq_le_def Qle_total).
apply (TotalOrder.Default.max_def1 Q Qeq Qle Qeq_le_def Qle_total).
apply (TotalOrder.Default.max_def2 Q Qeq Qle Qeq_le_def Qle_total).
Defined.

Add Morphism Qmin : Qmin_compat.
Proof @meet_compat QTotalOrder.

Add Morphism Qmax : Qmax_compat.
Proof @join_compat QTotalOrder.

Section QTotalOrder.

Let Qto := QTotalOrder.

Definition Qmin_lb_l : forall x y : Q, Qmin x y <= x := @meet_lb_l Qto.
Definition Qmin_lb_r : forall x y : Q, Qmin x y <= y := @meet_lb_r Qto.
Definition Qmin_glb : forall x y z : Q, z <= x -> z <= y -> z <= (Qmin x y) :=
 @meet_glb Qto.
Definition Qmin_comm : forall x y : Q, Qmin x y == Qmin y x := @meet_comm Qto.
Definition Qmin_assoc : forall x y z : Q, Qmin x (Qmin y z) == Qmin (Qmin x y) z:= 
 @meet_assoc Qto.
Definition Qmin_idem : forall x : Q, Qmin x x == x := @meet_idem Qto.
Definition Qle_min_l : forall x y : Q, x <= y <-> Qmin x y == x := @le_meet_l Qto.
Definition Qle_min_r : forall x y : Q, y <= x <-> Qmin x y == y := @le_meet_r Qto.
Definition Qmin_irred : forall x y: Q, {Qmin x y == x} + {Qmin x y == y} := @meet_irred Qto.
Definition Qmin_monotone_r : forall a : Q, Qmonotone (Qmin a) :=
 @meet_monotone_r Qto.
Definition Qmin_monotone_l : forall a : Q, Qmonotone (fun x => Qmin x a) :=
 @meet_monotone_l Qto.
Definition Qmin_le_compat : 
 forall w x y z : Q, w <= y -> x <= z -> Qmin w x <= Qmin y z :=
 @meet_le_compat Qto.

Definition Qmax_ub_l : forall x y : Q, x <= Qmax x y := @join_ub_l Qto.
Definition Qmax_ub_r : forall x y : Q, y <= Qmax x y := @join_ub_r Qto.
Definition Qmax_glb : forall x y z : Q, x <= z -> y <= z -> (Qmax x y) <= z :=
 @join_lub Qto.
Definition Qmax_comm : forall x y : Q, Qmax x y == Qmax y x := @join_comm Qto.
Definition Qmax_assoc : forall x y z : Q, Qmax x (Qmax y z) == Qmax (Qmax x y) z:= 
 @join_assoc Qto.
Definition Qmax_idem : forall x : Q, Qmax x x == x := @join_idem Qto.
Definition Qle_max_l : forall x y : Q, y <= x <-> Qmax x y == x := @le_join_l Qto.
Definition Qle_max_r : forall x y : Q, x <= y <-> Qmax x y == y := @le_join_r Qto.
Definition Qmax_irred : forall x y: Q, {Qmax x y == x} + {Qmax x y == y} := @join_irred Qto.
Definition Qmax_monotone_r : forall a : Q, Qmonotone (Qmax a) :=
 @join_monotone_r Qto.
Definition Qmax_monotone_l : forall a : Q, Qmonotone (fun x => Qmax x a) :=
 @join_monotone_l Qto.
Definition Qmax_le_compat :
 forall w x y z : Q, w<=y -> x<=z -> Qmax w x <= Qmax y z :=
 @join_le_compat Qto.

Definition Qmin_max_absorb_l_l : forall x y : Q, Qmin x (Qmax x y) == x :=
 @meet_join_absorb_l_l Qto.
Definition Qmax_min_absorb_l_l : forall x y : Q, Qmax x (Qmin x y) == x :=
 @join_meet_absorb_l_l Qto.
Definition Qmin_max_absorb_l_r : forall x y : Q, Qmin x (Qmax y x) == x :=
 @meet_join_absorb_l_r Qto.
Definition Qmax_min_absorb_l_r : forall x y : Q, Qmax x (Qmin y x) == x :=
 @join_meet_absorb_l_r Qto.
Definition Qmin_max_absorb_r_l : forall x y : Q, Qmin (Qmax x y) x == x :=
 @meet_join_absorb_r_l Qto.
Definition Qmax_min_absorb_r_l : forall x y : Q, Qmax (Qmin x y) x == x :=
 @join_meet_absorb_r_l Qto.
Definition Qmin_max_absorb_r_r : forall x y : Q, Qmin (Qmax y x) x == x :=
 @meet_join_absorb_r_r Qto.
Definition Qmax_min_absorb_r_r : forall x y : Q, Qmax (Qmin y x) x == x :=
 @join_meet_absorb_r_r Qto.

Definition Qmin_max_eq : forall x y : Q, Qmin x y == Qmax x y -> x == y :=
 @meet_join_eq Qto.

Definition Qmax_min_distr_r : forall x y z : Q,
 Qmax x (Qmin y z) == Qmin (Qmax x y) (Qmax x z) := 
 @join_meet_distr_r Qto.
Definition Qmax_min_distr_l : forall x y z : Q,
 Qmax (Qmin y z) x == Qmin (Qmax y x) (Qmax z x) := 
 @join_meet_distr_l Qto.
Definition Qmin_max_distr_r : forall x y z : Q,
 Qmin x (Qmax y z) == Qmax (Qmin x y) (Qmin x z) := 
 @meet_join_distr_r Qto.
Definition Qmin_max_distr_l : forall x y z : Q,
 Qmin (Qmax y z) x == Qmax (Qmin y x) (Qmin z x) := 
 @meet_join_distr_l Qto.

(*I don't know who wants modularity laws, but here they are *)
Definition Qmax_min_modular_r : forall x y z : Q,
 Qmax x (Qmin y (Qmax x z)) == Qmin (Qmax x y) (Qmax x z) := 
 @join_meet_modular_r Qto.
Definition Qmax_min_modular_l : forall x y z : Q,
 Qmax (Qmin (Qmax x z) y) z == Qmin (Qmax x z) (Qmax y z) := 
 @join_meet_modular_l Qto.
Definition Qmin_max_modular_r : forall x y z : Q,
 Qmin x (Qmax y (Qmin x z)) == Qmax (Qmin x y) (Qmin x z) := 
 @meet_join_modular_r Qto.
Definition Qmin_max_modular_l : forall x y z : Q,
 Qmin (Qmax (Qmin x z) y) z == Qmax (Qmin x z) (Qmin y z) := 
 @meet_join_modular_l Qto.

Definition Qmin_max_disassoc : forall x y z : Q, Qmin (Qmax x y) z <= Qmax x (Qmin y z) :=
 @meet_join_disassoc Qto.

Lemma Qplus_monotone_r : forall a, Qmonotone (Qplus a).
firstorder using Qle_refl Qplus_le_compat .
Qed.
Lemma Qplus_monotone_l : forall a, Qmonotone (fun x => Qplus x a).
firstorder using Qle_refl Qplus_le_compat.
Qed.
Definition Qmin_plus_distr_r : forall x y z : Q, x + Qmin y z == Qmin (x+y) (x+z)  :=
 fun a => @monotone_meet_distr Qto _ (Qplus_monotone_r a).
Definition Qmin_plus_distr_l : forall x y z : Q, Qmin y z + x == Qmin (y+x) (z+x) :=
 fun a => @monotone_meet_distr Qto _ (Qplus_monotone_l a).
Definition Qmax_plus_distr_r : forall x y z : Q, x + Qmax y z == Qmax (x+y) (x+z)  :=
 fun a => @monotone_join_distr Qto _ (Qplus_monotone_r a).
Definition Qmax_plus_distr_l : forall x y z : Q, Qmax y z + x == Qmax (y+x) (z+x) :=
 fun a => @monotone_join_distr Qto _ (Qplus_monotone_l a).
Definition Qmin_minus_distr_l : forall x y z : Q, Qmin y z - x == Qmin (y-x) (z-x) :=
 (fun x => Qmin_plus_distr_l (-x)).
Definition Qmax_minus_distr_l : forall x y z : Q, Qmax y z - x == Qmax (y-x) (z-x) :=
 (fun x => Qmax_plus_distr_l (-x)).

Definition Qmin_max_de_morgan : forall x y : Q, -(Qmin x y) == Qmax (-x) (-y) :=
 @antitone_meet_join_distr Qto _ Qopp_le_compat.
Definition Qmax_min_de_morgan : forall x y : Q, -(Qmax x y) == Qmin (-x) (-y) :=
 @antitone_join_meet_distr Qto _ Qopp_le_compat.

Lemma Qminus_antitone : forall a : Q, Qantitone (fun x => a - x).
change (forall a x y : Q, x <= y -> a + - y <= a + - x).
intros.
apply Qplus_le_compat;
 firstorder using Qle_refl Qopp_le_compat.
Qed.

Definition Qminus_min_max_antidistr_r : forall x y z : Q, x - Qmin y z == Qmax (x-y) (x-z) :=
 fun a => @antitone_meet_join_distr Qto _ (Qminus_antitone a).
Definition Qminus_max_min_antidistr_r : forall x y z : Q, x - Qmax y z == Qmin (x-y) (x-z) :=
 fun a => @antitone_join_meet_distr Qto _ (Qminus_antitone a).

End QTotalOrder.

Transparent Qlt_le_dec.
