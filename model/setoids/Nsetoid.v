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

Require Export Nsec.
Require Import CSetoidFun.

(** **Example of a setoid: [nat]

We will show that the natural numbers form a CSetoid. 
*)

Lemma ap_nat_irreflexive : irreflexive (A:=nat) ap_nat.
Proof.
red in |- *.
apply ap_nat_irreflexive0.
Qed.


Lemma ap_nat_symmetric : Csymmetric ap_nat.
Proof.
red in |- *.
apply ap_nat_symmetric0.
Qed.

Lemma ap_nat_cotransitive : cotransitive (A:=nat) ap_nat.
Proof.
red in |- *.
apply ap_nat_cotransitive0.
Qed.

Lemma ap_nat_tight : tight_apart (A:=nat) (eq (A:=nat)) ap_nat.
red in |- *.
apply ap_nat_tight0.
Qed.

Definition ap_nat_is_apartness := Build_is_CSetoid nat (eq (A:=nat)) ap_nat
 ap_nat_irreflexive ap_nat_symmetric ap_nat_cotransitive ap_nat_tight.


Definition nat_as_CSetoid := Build_CSetoid _ _ _ ap_nat_is_apartness.

Canonical Structure nat_as_CSetoid.

(** ***Addition
*)

Lemma plus_wd : bin_fun_wd nat_as_CSetoid nat_as_CSetoid nat_as_CSetoid plus.
Proof.
red in |- *.
simpl in |- *.
auto.
Qed.

Lemma plus_strext : bin_fun_strext nat_as_CSetoid nat_as_CSetoid nat_as_CSetoid plus.
Proof.
red in |- *.
simpl in |- *.
apply plus_strext0.
Qed.

Definition plus_is_bin_fun := Build_CSetoid_bin_fun _ _ _ _ plus_strext.

(** It is associative and commutative.
*)

Lemma plus_is_assoc : associative plus_is_bin_fun.
Proof.
red in |- *.
intros x y z.
simpl in |- *.
apply plus_assoc.
Qed.

Lemma plus_is_commut : commutes plus_is_bin_fun. 
Proof.
red in |- *.
simpl in |- *.
intros x y.
exact (plus_comm x y). 
Qed.

(** ***Multiplication
*)

Lemma mult_strext : bin_fun_strext
 nat_as_CSetoid nat_as_CSetoid nat_as_CSetoid mult. 
red in |- *.
simpl in |- *.
apply mult_strext0.
Qed.

Definition mult_as_bin_fun := Build_CSetoid_bin_fun _ _ _ _ mult_strext. 

(** ***Ternary addition
*)

Definition plus1 (n:nat)(m:nat): (n_ary_operation 1 nat_as_CSetoid).
simpl.
intros n  m.
apply (projected_bin_fun _ _ _ plus_is_bin_fun (plus_is_bin_fun n m)).
Defined.

Lemma to_plus1_strext:forall (n:nat), fun_strext (S1:=nat_as_CSetoid)
     (S2:=FS_as_CSetoid nat_as_CSetoid nat_as_CSetoid)
     (fun m : nat => plus1 n m).
intro n.
unfold plus1.
unfold fun_strext.
simpl.
intros x y H.
unfold ap_fun in H.
simpl in H.
elim H.
clear H.
intros a H.
set (H1:= plus_strext).
unfold bin_fun_strext in H1.
cut ((n+x{#N}n + y) or (a{#N}a)).
intro H2.
elim H2.
intro H3.
cut ((n{#N}n) or (x{#N}y)).
intro H4.
elim H4.
set (H5:=(ap_nat_irreflexive n)).
intro H6.
set (H7:= (H5 H6)).
contradiction.

intro H5.
exact H5.

apply H1.
exact H3.

intro H3.
set (H5:=(ap_nat_irreflexive a)).
set (H7:= (H5 H3)).
contradiction.

apply H1.
exact H.
Qed.

Definition plus2 (n:nat): (n_ary_operation 2 nat_as_CSetoid).
simpl.
intro n.
apply Build_CSetoid_fun with (fun m => (plus1 n m)).
apply to_plus1_strext.
Defined.


Lemma to_plus2_strext:fun_strext (S1:=nat_as_CSetoid)
     (S2:=FS_as_CSetoid nat_as_CSetoid
            (FS_as_CSetoid nat_as_CSetoid nat_as_CSetoid))
     (fun m : nat => plus2 m).
unfold fun_strext.
intros x y.
simpl.
unfold ap_fun.
simpl.
intro H.
elim H.
clear H.
unfold ap_fun.
intros a H.
elim H.
clear H.
intros a0 H.
unfold plus1 in H.
simpl in H.
set (H1:= (plus_strext)).
unfold bin_fun_strext in H1.
cut (((x+a){#N}(y+a)) or (a0 {#N} a0)).
intro H2.
elim H2.
clear H2.
intro H2.
set (H3:=(H1 x y a a H2)).
simpl in H3.
elim H3.
clear H3.
intro H3.
exact H3.
clear H3.
intro H3.
set (H5:=(ap_nat_irreflexive a)).
set (H7:= (H5 H3)).
contradiction.

set (H5:=(ap_nat_irreflexive a0)).
intro H6.
set (H7:= (H5 H6)).
contradiction.

apply H1.
exact H.
Qed.


Definition plus3 :(n_ary_operation 3 nat_as_CSetoid).
simpl.
apply Build_CSetoid_fun with (fun m => (plus2 m )).
apply to_plus2_strext.
Defined.

Definition on: nat_as_CSetoid -> nat_as_CSetoid -> nat_as_CSetoid ->
(n_ary_operation 3 nat_as_CSetoid)-> nat_as_CSetoid.
intros n m k p.
unfold n_ary_operation in p.
simpl in p.
elim p.
clear p.
intros pfun0 prf0.
set (pfun1 := (pfun0 n)).
elim pfun1.
clear pfun1.
intros pfun1 prf1.
set (pfun2:= (pfun1 m)).
elim pfun2.
clear pfun2.
intros pfun2 prf2.
set (pfun3:= (pfun2 k)).
exact pfun3.
Defined.


Let ex_3_ary: (on 3 5 7 plus3)[=] 3+5+7.
simpl.
reflexivity.
Qed.
