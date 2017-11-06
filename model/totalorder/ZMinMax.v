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

Require Export Coq.ZArith.Zmin.
Require Export Coq.ZArith.Zmax.
Require Import Coq.ZArith.ZArith.
Require Import CoRN.order.TotalOrder.

Opaque Z_lt_le_dec.
(**
** Example of a Total Order: <Z, Zle, Zmin, Zmax>
*)
Section ZTotalOrder.

Local Open Scope Z_scope.

Definition Zle_total x y : {x <= y} + {y <= x} :=
match Z_lt_le_dec x y with
| left p => left _ (Zlt_le_weak _ _ p)
| right p => right _ p
end.

Lemma Zeq_le_def : forall x y, x = y <-> x <= y /\ y <= x.
Proof.
 intros.
 split.
  intros H; rewrite H.
  firstorder using Zle_refl.
 firstorder using Zle_antisym.
Qed.

Definition Zmonotone : (Z -> Z) -> Prop := Default.monotone Zle.
Definition Zantitone : (Z -> Z) -> Prop := Default.antitone Zle.

Definition ZTotalOrder : TotalOrder.
 apply makeTotalOrder with Z (@eq Z) Zle Zmonotone Zantitone Zmin Zmax; try solve [auto with *].
Proof.
     apply Zle_total.
    firstorder using PartialOrder.Default.monotone_def.
    firstorder using PartialOrder.Default.antitone_def.
    intros. apply Zmin_case_strong; auto with *.
    intros. apply Zmin_case_strong; auto with *.
   intros. apply Zmax_case_strong; auto with *.
  intros. apply Zmax_case_strong; auto with *.
Defined.

Let Zto := ZTotalOrder.

Definition Zmin_lb_l : forall x y : Z, Zmin x y <= x := @meet_lb_l Zto.
Definition Zmin_lb_r : forall x y : Z, Zmin x y <= y := @meet_lb_r Zto.
Definition Zmin_glb : forall x y z : Z, z <= x -> z <= y -> z <= (Zmin x y) :=
 @meet_glb Zto.
Definition Zmin_comm : forall x y : Z, Zmin x y = Zmin y x := @meet_comm Zto.
Definition Zmin_assoc : forall x y z : Z, Zmin x (Zmin y z) = Zmin (Zmin x y) z:=
 @meet_assoc Zto.
Definition Zmin_idem : forall x : Z, Zmin x x = x := @meet_idem Zto.
Definition Zle_min_l : forall x y : Z, x <= y <-> Zmin x y = x := @le_meet_l Zto.
Definition Zle_min_r : forall x y : Z, y <= x <-> Zmin x y = y := @le_meet_r Zto.
Definition Zmin_irred : forall x y: Z, {Zmin x y = x} + {Zmin x y = y} := @meet_irred Zto.
Definition Zmin_monotone_r : forall a : Z, Zmonotone (Zmin a) :=
 @meet_monotone_r Zto.
Definition Zmin_monotone_l : forall a : Z, Zmonotone (fun x => Zmin x a) :=
 @meet_monotone_l Zto.
Definition Zmin_le_compat : forall w x y z : Z, w <= y -> x <= z -> Zmin w x <= Zmin y z :=
 @meet_le_compat Zto.

Definition Zmax_ub_l : forall x y : Z, x <= Zmax x y := @join_ub_l Zto.
Definition Zmax_ub_r : forall x y : Z, y <= Zmax x y := @join_ub_r Zto.
Definition Zmax_glb : forall x y z : Z, x <= z -> y <= z -> (Zmax x y) <= z :=
 @join_lub Zto.
Definition Zmax_comm : forall x y : Z, Zmax x y = Zmax y x := @join_comm Zto.
Definition Zmax_assoc : forall x y z : Z, Zmax x (Zmax y z) = Zmax (Zmax x y) z:=
 @join_assoc Zto.
Definition Zmax_idem : forall x : Z, Zmax x x = x := @join_idem Zto.
Definition Zle_max_l : forall x y : Z, y <= x <-> Zmax x y = x := @le_join_l Zto.
Definition Zle_max_r : forall x y : Z, x <= y <-> Zmax x y = y := @le_join_r Zto.
Definition Zmax_irred : forall x y: Z, {Zmax x y = x} + {Zmax x y = y} := @join_irred Zto.
Definition Zmax_monotone_r : forall a : Z, Zmonotone (Zmax a) :=
 @join_monotone_r Zto.
Definition Zmax_monotone_l : forall a : Z, Zmonotone (fun x => Zmax x a) :=
 @join_monotone_l Zto.
Definition Zmax_le_compat : forall w x y z : Z, w <= y -> x <= z -> Zmax w x <= Zmax y z :=
 @join_le_compat Zto.

Definition Zmin_max_absorb_l_l : forall x y : Z, Zmin x (Zmax x y) = x :=
 @meet_join_absorb_l_l Zto.
Definition Zmax_min_absorb_l_l : forall x y : Z, Zmax x (Zmin x y) = x :=
 @join_meet_absorb_l_l Zto.
Definition Zmin_max_absorb_l_r : forall x y : Z, Zmin x (Zmax y x) = x :=
 @meet_join_absorb_l_r Zto.
Definition Zmax_min_absorb_l_r : forall x y : Z, Zmax x (Zmin y x) = x :=
 @join_meet_absorb_l_r Zto.
Definition Zmin_max_absorb_r_l : forall x y : Z, Zmin (Zmax x y) x = x :=
 @meet_join_absorb_r_l Zto.
Definition Zmax_min_absorb_r_l : forall x y : Z, Zmax (Zmin x y) x = x :=
 @join_meet_absorb_r_l Zto.
Definition Zmin_max_absorb_r_r : forall x y : Z, Zmin (Zmax y x) x = x :=
 @meet_join_absorb_r_r Zto.
Definition Zmax_min_absorb_r_r : forall x y : Z, Zmax (Zmin y x) x = x :=
 @join_meet_absorb_r_r Zto.

Definition Zmax_min_distr_r : forall x y z : Z,
 Zmax x (Zmin y z) = Zmin (Zmax x y) (Zmax x z) :=
 @join_meet_distr_r Zto.
Definition Zmax_min_distr_l : forall x y z : Z,
 Zmax (Zmin y z) x = Zmin (Zmax y x) (Zmax z x) :=
 @join_meet_distr_l Zto.
Definition Zmin_max_distr_r : forall x y z : Z,
 Zmin x (Zmax y z) = Zmax (Zmin x y) (Zmin x z) :=
 @meet_join_distr_r Zto.
Definition Zmin_max_distr_l : forall x y z : Z,
 Zmin (Zmax y z) x = Zmax (Zmin y x) (Zmin z x) :=
 @meet_join_distr_l Zto.

(*I don't know who wants modularity laws, but here they are *)
Definition Zmax_min_modular_r : forall x y z : Z,
 Zmax x (Zmin y (Zmax x z)) = Zmin (Zmax x y) (Zmax x z) :=
 @join_meet_modular_r Zto.
Definition Zmax_min_modular_l : forall x y z : Z,
 Zmax (Zmin (Zmax x z) y) z = Zmin (Zmax x z) (Zmax y z) :=
 @join_meet_modular_l Zto.
Definition Zmin_max_modular_r : forall x y z : Z,
 Zmin x (Zmax y (Zmin x z)) = Zmax (Zmin x y) (Zmin x z) :=
 @meet_join_modular_r Zto.
Definition Zmin_max_modular_l : forall x y z : Z,
 Zmin (Zmax (Zmin x z) y) z = Zmax (Zmin x z) (Zmin y z) :=
 @meet_join_modular_l Zto.

Definition Zmin_max_disassoc : forall x y z : Z, Zmin (Zmax x y) z <= Zmax x (Zmin y z) :=
 @meet_join_disassoc Zto.

Lemma Zsucc_monotone : Zmonotone Zsucc.
Proof.
 unfold Zmonotone, Default.monotone.
 auto with *.
Qed.
Definition Zsucc_min_distr : forall x y : Z,
 Zsucc (Zmin x y) = Zmin (Zsucc x ) (Zsucc y) :=
 @monotone_meet_distr Zto _ Zsucc_monotone.
Definition Zsucc_max_distr : forall x y : Z,
 Zsucc (Zmax x y) = Zmax (Zsucc x ) (Zsucc y) :=
 @monotone_join_distr Zto _ Zsucc_monotone.

Lemma Zpred_monotone : Zmonotone Zpred.
Proof.
 unfold Zmonotone, Default.monotone.
 intros x y H.
 rewrite (Zsucc_pred x) in H.
 rewrite (Zsucc_pred y) in H.
  auto with zarith. 
Qed.
Definition Zpred_min_distr : forall x y : Z,
 Zpred (Zmin x y) = Zmin (Zpred x ) (Zpred y) :=
 @monotone_meet_distr Zto _ Zpred_monotone.
Definition Zpred_max_distr : forall x y : Z,
 Zpred (Zmax x y) = Zmax (Zpred x ) (Zpred y) :=
 @monotone_join_distr Zto _ Zpred_monotone.

Lemma Zplus_monotone_r : forall a, Zmonotone (Zplus a).
Proof.
 do 2 red. auto with zarith.
Qed.
Lemma Zplus_monotone_l : forall a, Zmonotone (fun x => Zplus x a).
Proof.
 unfold Zmonotone, Default.monotone.
 auto with *.
Qed.
Definition Zmin_plus_distr_r : forall x y z : Z, x + Zmin y z = Zmin (x+y) (x+z)  :=
 fun a => @monotone_meet_distr Zto _ (Zplus_monotone_r a).
Definition Zmin_plus_distr_l : forall x y z : Z, Zmin y z + x = Zmin (y+x) (z+x) :=
 fun a => @monotone_meet_distr Zto _ (Zplus_monotone_l a).
Definition Zmax_plus_distr_r : forall x y z : Z, x + Zmax y z = Zmax (x+y) (x+z)  :=
 fun a => @monotone_join_distr Zto _ (Zplus_monotone_r a).
Definition Zmax_plus_distr_l : forall x y z : Z, Zmax y z + x = Zmax (y+x) (z+x) :=
 fun a => @monotone_join_distr Zto _ (Zplus_monotone_l a).
Definition Zmin_minus_distr_l : forall x y z : Z, Zmin y z - x = Zmin (y-x) (z-x) :=
 (fun x => Zmin_plus_distr_l (-x)).
Definition Zmax_minus_distr_l : forall x y z : Z, Zmax y z - x = Zmax (y-x) (z-x) :=
 (fun x => Zmax_plus_distr_l (-x)).

Lemma Zopp_le_compat : forall x y : Z, x <= y -> -y <= -x.
Proof.
 auto with *.
Qed.
Definition Zmin_max_de_morgan : forall x y : Z, -(Zmin x y) = Zmax (-x) (-y) :=
 @antitone_meet_join_distr Zto _ Zopp_le_compat.
Definition Zmax_min_de_morgan : forall x y : Z, -(Zmax x y) = Zmin (-x) (-y) :=
 @antitone_join_meet_distr Zto _ Zopp_le_compat.

Lemma Zminus_antitone : forall a : Z, Zantitone (fun x => a - x).
Proof.
 change (forall a x y : Z, x <= y -> a + - y <= a + - x).
 intros.
 apply Zplus_le_compat; firstorder using Zle_refl Zopp_le_compat.
Qed.

Definition Zminus_min_max_antidistr_r : forall x y z : Z, x - Zmin y z = Zmax (x-y) (x-z) :=
 fun a => @antitone_meet_join_distr Zto _ (Zminus_antitone a).
Definition Zminus_max_min_antidistr_r : forall x y z : Z, x - Zmax y z = Zmin (x-y) (x-z) :=
 fun a => @antitone_join_meet_distr Zto _ (Zminus_antitone a).

End ZTotalOrder.

Transparent Z_lt_le_dec.
