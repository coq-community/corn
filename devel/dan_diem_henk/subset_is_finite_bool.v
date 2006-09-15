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
Require Export Arith.
Require Export BoolToProp.
Require Export expl_case.

Implicit Types i n : nat.

Set Implicit Arguments.

Definition universe := nat.

Implicit Types u : universe.

Definition set :=
  universe -> Prop.

Implicit Types A B : set.

Definition decset := universe -> bool.

Implicit Types D : decset.

Definition IsSubset A B  :=
  forall u, A u -> B u.

Infix "<=s" := IsSubset  (at level 70).

Definition N_ n : set :=
  fun i => lt i n.

Definition protofun :=
  universe -> universe.

Implicit Types f : protofun.

Definition IsFun A B f :=
  forall u, A u -> B (f u).

Definition IsInjective A B f :=
  IsFun A B f /\
  forall u1 u2, A u1 -> A u2 -> f u1 = f u2 -> u1 = u2.

Definition IsSurjective A B f  :=
  IsFun A B f /\
  forall u, B u -> exists u', A u' /\ f u' = u.

Definition IsBijective A B f :=
  IsInjective A B f /\ IsSurjective A B f.

Definition Finite A : Prop :=
  exists n, exists f, IsBijective A (N_ n) f.

Definition Emptyset : set := 
  fun _ => False.

Definition id := 
  fun u => u.

Definition Singleton u :=
  fun u' => u' = u.

Definition Union A B :=
  fun u => A u \/ B u.

Infix "[U]" := Union (at level 40, left associativity).

Definition Eqset A B :=
  forall u, A u <-> B u.

Infix "=s" := Eqset (at level 70).

Lemma fun_id_empty_N_n :
  forall n, IsFun Emptyset (N_ n) id.
Proof.
intros n u e; elim e.
Qed.

Lemma empty_finite : Finite Emptyset.
Proof.
unfold Finite.
exists O.
exists id.
unfold IsBijective.
assert (H0 := fun_id_empty_N_n 0).
split.
unfold IsInjective.
split.
exact H0.
intros u1 u2 e1 e2 H.
exact H.
unfold IsSurjective.
split.
exact H0.
intros u p.
inversion p.
Qed.

Lemma eqset_finite :
  forall A B, A =s B -> Finite A -> Finite B.
Proof.
intros A B H [ u [ f [ [ Funf Injf ] [ _ Surf ] ] ] ].
exists u.
exists f.
unfold Eqset in H.
(* improve (def tac distributing forall over conjuncts?) *)
assert (ab : forall u, A u -> B u).
intros u'; elim (H u'); intros ab _; exact ab.
assert (ba : forall u, B u -> A u).
intros u'; elim (H u'); intros _ ba; exact ba.
assert (H0 : IsFun B (N_ u) f).
unfold IsFun.
intros u' b.
apply Funf.
exact (ba u' b).
split; ( split; [ exact H0 | idtac ] ).
intros u1 u2 b1 b2 H1.
apply Injf with (3:=H1).
apply ba with (1:=b1).
apply ba with (1:=b2).
intros u1 H1.
elim Surf with (1:=H1); intros u2 [ H2 H3 ].
exists u2; split.
apply ab with (1:=H2).
exact H3.
Qed.

Lemma add_one_preserves_finiteness :
   forall D,
   Finite D ->
   forall u, Finite (D [U] (Singleton u)).
Proof.
intros D [ n [ f [ [ Funf Injf ] [ _ Surf ] ] ] ] u.
unfold Finite.
expl_case (D u).
(* D u *)
exists n.
set (f' := f).
exists f'.
(* f' is a function on D[U](Singleton u) *)
assert (Funf' : IsFun  (D[U](Singleton u)) (N_ n) f).
unfold IsFun.
intros x H0.
apply Funf.
elim H0; intro H1.
exact H1.
rewrite H1.
exact H.
split; ( split; [ exact Funf' | idtac ] ).
(* f' is injective *)
intros u1 u2 H0 H1 H2.
apply Injf.
elim H0; intro H3.
exact H3.
rewrite H3; exact H.
elim H1; intro H4.
exact H4.
rewrite H4; exact H.
exact H2.
(* f' is surjective *)
intros u' H0.
elim (Surf u' H0); intros u'' [ H1 H2 ].
exists u''; split.
left; exact H1.
exact H2.
(* ~ D u *)
exists (S n).
set (f' := fun u' => if D u' then f u' else n).
exists f'.
(* f' is a function *)
assert (H0 : IsFun (D[U](Singleton u)) (N_ (S n)) f').
unfold IsFun. 
intros u' H0.
unfold f'.
expl_case (D u').
unfold N_.
assert (H2 := (Funf u' H1)).
unfold N_ in H2.
auto with arith.
unfold N_.
auto with arith.
split; ( split; [ exact H0 | clear H0 ] ).
(* f' is injective *)
intros u1 u2 H0 H1.
unfold f'.
elim H0; intro H3; rewrite H3; elim H1; intro H4; rewrite H4; intro H2.
apply Injf with (1:=H3) (2:=H4) (3:=H2).
rewrite H in H2.
assert (H5 := (Funf u1 H3)).
unfold N_ in H5.
rewrite H2 in H5.
elim (lt_irrefl n H5).
rewrite H in H2.
assert (H5 := (Funf u2 H4)).
unfold N_ in H5.
rewrite <- H2 in H5.
elim (lt_irrefl n H5).
reflexivity.
(* f' surjective *)
intros u' H0.
unfold N_ in H0.
assert (H1 : u' <= n).
auto with arith.
assert (H2 := le_lt_or_eq u' n H1). 
elim H2; intro H3.
(* u' < n *)
elim (Surf u' H3); intros u'' [ H4 H5 ].
exists u''; split.
left; exact H4.
unfold f'.
rewrite H4.
exact H5.
(* u' = n *)
exists u; split.
right.
unfold Singleton.
reflexivity.
rewrite H3.
unfold f'; rewrite H; reflexivity.
Qed.

Theorem subset_is_finite :
  forall B D, 
  Finite B -> 
  D <=s B -> 
  Finite D.
Proof.
intros B D [ n [ f ] H ].
load H.
load f.
load D.
load B.
induction n; intros B D f [ [ Funf Injf ] [ _ Surf ] ] H.
assert (H0 : Emptyset =s D).
intro u.
split ; intro H0.
elim H0.
assert (H1 := Funf u (H u H0)).
unfold N_ in H1.
inversion H1.
apply eqset_finite with (1:=H0) (2:=empty_finite).
elim (Surf n).
intros b [ H0 H1 ].
(* B' is B minus b *)
set (B' := fun u => B u /\ u <> b).
set (f' := f).
(* f' is a function on B' *)
assert (Funf' : IsFun B' (N_ n) f').
intros x [ H3 H4 ].
unfold IsFun in Funf.
assert (H5 : f x <= n).
assert (H5 := (Funf x H3)).
unfold N_, lt in H5 |- *.
auto with arith.
elim le_lt_or_eq with (1:=H5); intro H6.
exact H6.
elim H4.
apply Injf with (1:=H3) (2:=H0).
rewrite H1; exact H6.
assert (Bijf' : IsBijective B' (N_ n) f').
split; ( split; [ exact Funf' | idtac ] ).
intros u1 u2 [ H3 H4 ] [ H5 H6 ] H7.
apply Injf with (1:=H3) (2:=H5) (3:=H7).
intros m H3.
elim (Surf m).
intros u [ H4 H5 ].
exists u; split.
split.
exact H4.
intro H6.
rewrite H6 in H5; rewrite H5 in H1; rewrite H1 in H3.
unfold N_ in H3.
exact (lt_irrefl n H3).
exact H5.
unfold N_ in H3 |- *.
auto with arith.
expl_case (D b).
(* D b *)
(* D' is D minus b *)
set (D' := fun u => D u && negb (beq u b)).
assert (H3 : D' <=s B').
intros d H3.
boolToProp_in H3.
elim H4; intros H5 H6.
split.
apply H with (1:=H5).
exact H6.
assert (FinD' := IHn B' D' f' Bijf' H3).
rename H2 into H27.
clear IHn Funf' Bijf' H H0 H1 H3.
assert (H : (D'[U](Singleton b)) =s D).
intro u; split; intro H.
elim H; intro H0.
boolToProp_in H0.
elim H1; intros H2 _; exact H2.
rewrite H0.
exact H27.
unfold Union.
boolToProp.
expl_case (beq u b).
boolToProp_in H0.
right; exact H1.
boolToProp_in H0.
left; split; [ exact H | exact H1 ].
apply (eqset_finite H).
apply add_one_preserves_finiteness with (1:=FinD').
(* ~ D b *)
apply (IHn B' D f').
exact Bijf'.
intros d H3.
split.
apply H with (1:=H3).
intro H4.
rewrite H4 in H3.
rewrite H2 in H3.
inversion H3.
unfold N_; auto with arith.
Qed.
