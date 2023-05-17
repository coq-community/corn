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

Require Export CoRN.ftc.Continuity.
From Coq Require Import Lia.

(** printing Partition_Sum %\ensuremath{\sum_P}% #&sum;<sub>P</sub># *)

Section Definitions.

(**
* Partitions

We now begin to lay the way for the definition of Riemann integral.  This will
be done through the definition of a sequence of
sums that is proved to be convergent; in order to do that, we first
need to do a bit of work on partitions.

** Definitions

A partition is defined as a record type.  For each compact interval [[a,b]]
and each natural number [n], a partition of [[a,b]] with [n+1] points is a
choice of real numbers [a [=] a0 [<=] a1 [<=] an [=] b]; the following
specification works as follows:
 - [Pts] is the function that chooses the points (it is declared as a
coercion);
 - [prf1] states that [Pts] is a setoid function;
 - [prf2] states that the points are ordered;
 - [start] requires that [a0 [=] a] and
 - [finish] requires that [an [=] b].

*)

Record Partition (a b : IR) (Hab : a [<=] b) (lng : nat) : Type :=
  {Pts    :> forall i, i <= lng -> IR;
   prf1   :  forall i j, i = j -> forall Hi Hj, Pts i Hi [=] Pts j Hj;
   prf2   :  forall i Hi HSi, Pts i Hi [<=] Pts (S i) HSi;
   start  :  forall H, Pts 0 H [=] a;
   finish :  forall H, Pts lng H [=] b}.

(** Two immediate consequences of this are that [ai [<=] aj] whenever
[i < j] and that [ai] is in [[a,b]] for all [i].
*)

Lemma Partition_mon : forall a b Hab lng (P : Partition a b Hab lng) i j Hi Hj,
 i <= j -> P i Hi [<=] P j Hj.
Proof.
 intros; induction  j as [| j Hrecj].
  cut (i = 0); [ intro | auto with arith ].
  apply eq_imp_leEq; apply prf1; auto.
 elim (le_lt_eq_dec _ _ H); intro H1.
  cut (j <= lng); [ intro | clear Hrecj; lia ].
  apply leEq_transitive with (Pts _ _ _ _ P j H0).
   apply Hrecj; clear Hrecj; auto with arith.
  apply prf2.
 apply eq_imp_leEq; apply prf1; assumption.
Qed.

Lemma Partition_in_compact : forall a b Hab lng (P : Partition a b Hab lng) i Hi,
 compact a b Hab (P i Hi).
Proof.
 intros.
 split.
  apply leEq_wdl with (P _ (Nat.le_0_l _)).
   apply Partition_mon; auto with arith.
  apply start.
 apply leEq_wdr with (P _ (le_n _)).
  apply Partition_mon; auto with arith.
 apply finish.
Qed.

(**
Each partition of [[a,b]] implies a partition of the interval
$[a,a_{n-1}]$#[a,a<sub>n-1</sub>]#.  This partition will play an
important role in much of our future work, so we take some care to
define it.
*)

Lemma part_pred_lemma : forall a b Hab lng (P : Partition a b Hab lng) i Hi, a [<=] P i Hi.
Proof.
 intros.
 apply leEq_wdl with (P 0 (Nat.le_0_l _)).
  apply Partition_mon; auto with arith.
 apply start.
Qed.

Definition Partition_Dom a b Hab n P :
  Partition a _ (part_pred_lemma a b Hab (S n) P n (le_n_Sn n)) n.
Proof.
 intros.
 apply Build_Partition with (fun (i : nat) (Hi : i <= n) => P i (le_S _ _ Hi)).
    intros; simpl in |- *; apply prf1; assumption.
   intros; simpl in |- *; apply prf2.
  intros; simpl in |- *; apply start.
 intros; simpl in |- *; apply prf1; auto.
Defined.

(**
The mesh of a partition is the greatest distance between two
consecutive points.  For convenience's sake we also define the dual
concept, which is very helpful in some situations.  In order to do
this, we begin by building a list with all the distances between
consecutive points; next we only need to extract the maximum and the
minimum of this list. Notice that this list is nonempty except in the
case when [a [=] b] and [n = 0]; this means that the convention we took
of defining the minimum and maximum of the empty list to be [0] actually
helps us in this case.
*)

Definition Part_Mesh_List n a b Hab (P : Partition a b Hab n) : list IR.
Proof.
 revert a b Hab P; induction  n as [| n Hrecn]; intros.
  apply (@nil IR).
 apply cons.
  apply (P _ (le_n (S n)) [-]P _ (le_S _ _ (le_n n))).
 apply Hrecn with a (P _ (le_n_Sn n)) (part_pred_lemma _ _ _ _ P n (le_n_Sn n)).
 apply Partition_Dom.
Defined.

Definition Mesh a b Hab n P := maxlist (Part_Mesh_List n a b Hab P).

Definition AntiMesh a b Hab n P := minlist (Part_Mesh_List n a b Hab P).

(**
Even partitions (partitions where all the points are evenly spaced)
will also play a central role in our work; the first two lemmas are
presented simply to make the definition of even partition lighter.
*)

Lemma even_part_1 : forall a b n Hn, a[+]nring 0[*] (b[-]a[/] _[//]nring_ap_zero' IR n Hn) [=] a.
Proof.
 intros; rational.
Qed.

Lemma even_part_2 : forall a b n Hn, a[+]nring n[*] (b[-]a[/] _[//]nring_ap_zero' IR n Hn) [=] b.
Proof.
 intros; rational.
Qed.

Definition Even_Partition a b Hab n (Hn : 0 <> n) : Partition a b Hab n.
Proof.
 intros.
 apply Build_Partition with (fun (i : nat) (Hi : i <= n) =>
   a[+]nring i[*] (b[-]a[/] _[//]nring_ap_zero' _ n Hn)).
    intros; simpl in |- *.
    rewrite H; algebra.
   intros; simpl in |- *.
   apply plus_resp_leEq_lft.
   apply mult_resp_leEq_rht.
    apply less_leEq; apply less_plusOne.
   apply shift_leEq_div.
    apply nring_pos; clear Hi; apply neq_O_lt; auto.
   apply shift_leEq_minus.
   astepl ([0][+]a).
   astepl a; assumption.
  intros; simpl in |- *; apply even_part_1; auto.
 intros; simpl in |- *; apply even_part_2; auto.
Defined.

Section Refinements.

Variables a b : IR.
Hypothesis Hab : a [<=] b.
Variables m n : nat.
Variable P : (Partition a b Hab n).
Variable Q : (Partition a b Hab m).

(**
We now define what it means for a partition [Q] to be a refinement of
[P] and prove the main property of refinements.
*)

Definition Refinement := {f : nat -> nat |
  f 0 = 0 /\ f n = m /\ (forall i j, i < j -> f i < f j) |
  forall i Hi, {H' : f i <= m | P i Hi [=] Q (f i) H'}}.

Lemma Refinement_prop : Refinement -> forall i (Hi : i <= m) (HSi : (S i) <= m),
 {j : nat | {Hj : j <= n | {HSj : S j <= n | P _ Hj [<=] Q _ Hi | Q _ HSi [<=] P _ HSj}}}.
Proof.
 intros H i Hi Hi'.
 elim H; clear H; intros f Hf.
 elim Hf; clear Hf; intros Hf0 Hf.
 elim Hf; clear Hf; intros Hfn Hfmon.
 intro Hf.
 cut {j : nat | f j <= i | S i <= f (S j)}.
  intro H.
  elim H; clear H; intros j Hj Hj'.
  exists j.
  cut (j < n).
   intro.
   cut (j <= n); [ intro Hj1 | auto with arith ].
   exists Hj1.
   elim (Hf j Hj1); intros H' HPts.
   cut (S j <= n); [ intro Hj2 | apply H ].
   elim (Hf (S j) Hj2); intros H'' HPts'.
   exists Hj2.
    eapply leEq_wdl.
     2: eapply eq_transitive_unfolded.
      2: apply eq_symmetric_unfolded; apply HPts.
     apply Partition_mon; assumption.
    apply prf1; auto.
   eapply leEq_wdr.
    2: eapply eq_transitive_unfolded.
     2: apply eq_symmetric_unfolded; apply HPts'.
    apply Partition_mon; assumption.
   apply prf1; auto.
  clear Hj' Hf Hf0.
  cut (i < f n).
   intro.
   cut (f j < f n); [ intro | apply Nat.le_lt_trans with i; auto ].
   apply not_ge.
   intro; red in H1.
   apply (le_not_lt (f j) (f n)); auto with arith.
   apply Hfmon.
   elim (le_lt_eq_dec _ _ H1); intro; auto.
   rewrite b0 in H0; elim (Nat.lt_irrefl (f j)); auto.
  rewrite <- Hfn in Hi'; auto.
 apply mon_fun_covers; auto.
 exists n; clear Hf Hfmon.
 rewrite Hfn; assumption.
Qed.

(**
We will also need to consider arbitrary sums %of the form
\[\sum_{i=0}^{n-1}f(x_i)(a_{i+1}-a_i)\]%#of
f(x<sub>i</sub>)(a<sub>i+1</sub>-a<sub>i</sub>)# where
$x_i\in[a_i,a_{i+1}]$#x<sub>i</sub>&isin;[a<sub>i</sub>,a<sub>i+1</sub>]#.
For this, we again need a choice function [x] which has to satisfy
some condition.  We define the condition and the sum for a fixed [P]:
*)

Definition Points_in_Partition (g : forall i, i < n -> IR) : CProp :=
  forall i Hi, Compact (prf2 _ _ _ _ P i (Nat.lt_le_incl _ _ Hi) Hi) (g i Hi).

Lemma Pts_part_lemma : forall g, Points_in_Partition g -> forall i Hi, compact a b Hab (g i Hi).
Proof.
 intros g H i H0.
 elim (H i H0); intros.
 split.
  eapply leEq_transitive.
   2: apply a0.
  apply leEq_wdl with (P 0 (Nat.le_0_l _)).
   apply Partition_mon; auto with arith.
  apply start.
 eapply leEq_transitive.
  apply b0.
 apply leEq_wdr with (P n (le_n _)).
  apply Partition_mon; auto with arith.
 apply finish.
Qed.

Definition Partition_Sum g F (H : Points_in_Partition g) (incF : included (Compact Hab) (Dom F)) :=
 Sumx (fun i Hi => F (g i Hi) (incF _ (Pts_part_lemma _ H i Hi)) [*]
     (P (S i) Hi[-]P i (Nat.lt_le_incl _ _ Hi))).

End Refinements.

Arguments Points_in_Partition [a b Hab n].
Arguments Partition_Sum [a b Hab n P g F].

(**
** Constructions

We now formalize some trivial and helpful constructions.

%\begin{convention}% We will assume a fixed compact interval [[a,b]], denoted by [I].
%\end{convention}%
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := compact a b Hab.
(* end hide *)

Section Getting_Points.

(**
From a partition we always have a canonical choice of points at which
to evaluate a function: just take all but the last points of the
partition.

%\begin{convention}% Let [Q] be a partition of [I] with [m] points.
%\end{convention}%
*)

Variable m : nat.
Variable Q : Partition a b Hab m.

Definition Partition_imp_points : forall i : nat, i < m -> IR.
Proof.
 intros.
 apply (Q i (Nat.lt_le_incl _ _ H)).
Defined.

Lemma Partition_imp_points_1 : Points_in_Partition Q Partition_imp_points.
Proof.
 red in |- *; intros.
 unfold Partition_imp_points in |- *; split.
  apply leEq_reflexive.
 apply prf2.
Qed.

Lemma Partition_imp_points_2 : nat_less_n_fun Partition_imp_points.
Proof.
 red in |- *; intros.
 unfold Partition_imp_points in |- *; simpl in |- *.
 apply prf1; auto.
Qed.

End Getting_Points.

(**
As a corollary, given any continuous function [F] and a natural number we have an immediate choice of a sum of [F] in [[a,b]].
*)

Variable F : PartIR.
Hypothesis contF : Continuous_I Hab F.

Definition Even_Partition_Sum (n : nat) (Hn : 0 <> n) : IR.
Proof.
 intros.
 apply Partition_Sum with a b Hab n (Even_Partition a b Hab n Hn)
   (Partition_imp_points _ (Even_Partition a b Hab n Hn)) F.
  apply Partition_imp_points_1.
 apply contin_imp_inc; assumption.
Defined.

End Definitions.

Arguments Partition [a b].
Arguments Partition_Dom [a b Hab n].
Arguments Mesh [a b Hab n].
Arguments AntiMesh [a b Hab n].
Arguments Pts [a b Hab lng].
Arguments Part_Mesh_List [n a b Hab].
Arguments Points_in_Partition [a b Hab n].
Arguments Partition_Sum [a b Hab n P g F].
Arguments Even_Partition [a b].
Arguments Even_Partition_Sum [a b].
Arguments Refinement [a b Hab m n].

#[global]
Hint Resolve start finish: algebra.

Section Lemmas.

(**
** Properties of the mesh

If a partition has more than one point then its mesh list is nonempty.
*)

Lemma length_Part_Mesh_List : forall n (a b : IR) (Hab : a [<=] b) (P : Partition Hab n),
 0 < n -> 0 < length (Part_Mesh_List P).
Proof.
 intro; case n; intros.
  exfalso; inversion H.
 simpl in |- *; auto with arith.
Qed.

(**
Any element of the auxiliary list defined to calculate the mesh of a partition has a very specific form.
*)

Lemma Part_Mesh_List_lemma : forall n (a b : IR) (Hab : a [<=] b) (P : Partition Hab n) x,
 member x (Part_Mesh_List P) ->
 {i : nat | {Hi : i <= n | {Hi' : S i <= n | x [=] P _ Hi'[-]P _ Hi}}}.
Proof.
 intro; induction  n as [| n Hrecn].
  simpl in |- *; intros.
  easy.
 intros a b Hab P x H.
 simpl in H; elim H; clear H; intro H0.
  elim (Hrecn _ _ _ _ _ H0); clear Hrecn.
  intros i H; elim H; clear H.
  intros Hi H; elim H; clear H.
  intros Hi' H.
  simpl in H.
  exists i; exists (le_S _ _ Hi); exists (le_S _ _ Hi').
  eapply eq_transitive_unfolded.
   apply H.
  apply cg_minus_wd; apply prf1; auto.
 exists n.
 exists (le_S _ _ (le_n n)).
 exists (le_n (S n)).
 eapply eq_transitive_unfolded.
  apply H0.
 apply cg_minus_wd; apply prf1; auto.
Qed.

(**
Mesh and antimesh are always nonnegative.
*)

Lemma Mesh_nonneg : forall n (a b : IR) (Hab : a [<=] b) (P : Partition Hab n), [0] [<=] Mesh P.
Proof.
 simple induction n.
  intros; unfold Mesh in |- *; simpl in |- *.
  apply leEq_reflexive.
 clear n; intros.
 unfold Mesh in |- *.
 apply leEq_transitive with (P _ (le_n (S n)) [-]P _ (le_S _ _ (le_n n))).
  apply shift_leEq_minus; astepl (P _ (le_S _ _ (le_n n))).
  apply prf2.
 apply maxlist_greater.
 right; algebra.
Qed.

Lemma AntiMesh_nonneg : forall n (a b : IR) (Hab : a [<=] b) (P : Partition Hab n),
 [0] [<=] AntiMesh P.
Proof.
 intro; induction  n as [| n Hrecn].
  intros; unfold AntiMesh in |- *; simpl in |- *.
  apply leEq_reflexive.
 intros.
 unfold AntiMesh in |- *.
 apply leEq_minlist.
  simpl in |- *; auto with arith.
 intros y H.
 simpl in H; elim H; clear H; intro H0.
  unfold AntiMesh in Hrecn.
  apply leEq_transitive with (minlist (Part_Mesh_List (Partition_Dom P))).
   2: apply minlist_smaller; assumption.
  apply Hrecn.
 eapply leEq_wdr.
  2: apply eq_symmetric_unfolded; apply H0.
 apply shift_leEq_minus; astepl (P _ (le_S _ _ (le_n n))).
 apply prf2.
Qed.

(**
Most important, [AntiMesh] and [Mesh] provide lower and upper bounds
for the distance between any two consecutive points in a partition.

%\begin{convention}% Let [I] be [[a,b]] and [P] be a partition of [I]
with [n] points.
%\end{convention}%
*)

Variables a b : IR.
(* begin hide *)
Let I := compact a b.
(* end hide *)
Hypothesis Hab : a [<=] b.

Variable n : nat.
Variable P : Partition Hab n.

Lemma Mesh_lemma : forall i H H', P (S i) H'[-]P i H [<=] Mesh P.
Proof.
 clear I; generalize n a b Hab P; clear P n Hab a b.
 simple induction n.
  intros; exfalso; inversion H'.
 clear n; intro m; intros.
 induction  m as [| m Hrecm].
  cut (0 = i); [ intro | inversion H'; auto; inversion H2 ].
  generalize H0 H'; clear H0 H'; rewrite <- H1.
  intros.
  unfold Mesh in |- *; simpl in |- *.
  apply eq_imp_leEq; apply cg_minus_wd; apply prf1; auto.
 elim (le_lt_eq_dec _ _ H'); intro H1.
  cut (i <= S m); [ intro | auto with arith ].
  cut (S i <= S m); [ intro | auto with arith ].
  set (P' := Partition_Dom P) in *.
  apply leEq_wdl with (P' _ H3[-]P' _ H2).
   2: simpl in |- *; apply cg_minus_wd; apply prf1; auto.
  apply leEq_transitive with (Mesh P').
   apply H.
  unfold Mesh in |- *; simpl in |- *; apply rht_leEq_Max.
 cut (i = S m); [ intro | auto with arith ].
 generalize H' H0; clear H0 H'.
 rewrite H2; intros.
 unfold Mesh in |- *; apply maxlist_greater; right.
 apply cg_minus_wd; apply prf1; auto.
Qed.

Lemma AntiMesh_lemma : forall i H H', AntiMesh P [<=] P (S i) H'[-]P i H.
Proof.
 clear I; generalize n a b Hab P; clear P n Hab a b.
 simple induction n.
  intros; exfalso; inversion H'.
 clear n; intro m; intros.
 induction  m as [| m Hrecm].
  cut (0 = i); [ intro | inversion H'; auto; inversion H2 ].
  generalize H0 H'; clear H0 H'; rewrite <- H1.
  intros.
  unfold AntiMesh in |- *; simpl in |- *.
  apply eq_imp_leEq; apply cg_minus_wd; apply prf1; auto.
 elim (le_lt_eq_dec _ _ H'); intro H1.
  cut (i <= S m); [ intro | auto with arith ].
  cut (S i <= S m); [ intro | auto with arith ].
  set (P' := Partition_Dom P) in *.
  apply leEq_wdr with (P' _ H3[-]P' _ H2).
   2: simpl in |- *; apply cg_minus_wd; apply prf1; auto.
  apply leEq_transitive with (AntiMesh P').
   2: apply H.
  unfold AntiMesh in |- *; simpl in |- *. unfold MIN.
  eapply leEq_wdr.
   2: apply cg_inv_inv.
  apply inv_resp_leEq; apply rht_leEq_Max.
 cut (i = S m); [ intro | auto with arith ].
 generalize H' H0; clear H0 H'.
 rewrite H2; intros.
 unfold AntiMesh in |- *; apply minlist_smaller; right.
 apply cg_minus_wd; apply prf1; auto.
Qed.

Lemma Mesh_leEq : forall m (Q : Partition Hab m), Refinement P Q -> Mesh Q [<=] Mesh P.
Proof.
 intro; case m.
  intros Q H.
  unfold Mesh at 1 in |- *; simpl in |- *.
  apply Mesh_nonneg.
 clear m; intros m Q H.
 unfold Mesh at 1 in |- *.
 apply maxlist_leEq.
  simpl in |- *; auto with arith.
 intros x H0.
 elim (Part_Mesh_List_lemma _ _ _ _ _ _ H0).
 clear H0. intros i H0.
 elim H0; clear H0; intros Hi H0.
 elim H0; clear H0; intros Hi' H0.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply H0.
 elim H; intros f Hf.
 elim Hf; clear Hf; intros Hf' Hf.
 cut {j : nat | {Hj : j <= n | {Hj' : S j <= n | P _ Hj [<=] Q _ Hi | Q _ Hi' [<=] P _ Hj'}}}.
  intro H1.
  elim H1; intros j Hj.
  elim Hj; clear H1 Hj; intros Hj Hjaux.
  elim Hjaux; clear Hjaux; intros Hj' Hjaux.
  intros HPts HPts'.
  apply leEq_transitive with (P _ Hj'[-]P _ Hj).
   unfold cg_minus in |- *; apply plus_resp_leEq_both.
    assumption.
   apply inv_resp_leEq; assumption.
  apply Mesh_lemma.
 apply Refinement_prop; assumption.
Qed.

End Lemmas.

Section Even_Partitions.

(** More technical stuff.  Two equal partitions have the same mesh.
*)

Lemma Mesh_wd : forall n a b b' (Hab : a [<=] b) (Hab' : a [<=] b')
 (P : Partition Hab n) (Q : Partition Hab' n),
 (forall i Hi, P i Hi [=] Q i Hi) -> Mesh P [=] Mesh Q.
Proof.
 simple induction n.
  intros.
  unfold Mesh in |- *; simpl in |- *; algebra.
 clear n; intro.
 case n.
  intros.
  unfold Mesh in |- *; simpl in |- *.
  apply cg_minus_wd; apply H0.
 clear n; intros.
 unfold Mesh in |- *.
 apply eq_transitive_unfolded with (Max (P _ (le_n (S (S n))) [-]P _ (le_S _ _ (le_n (S n))))
   (maxlist (Part_Mesh_List (Partition_Dom P)))).
  simpl in |- *; algebra.
 apply eq_transitive_unfolded with (Max (Q _ (le_n (S (S n))) [-]Q _ (le_S _ _ (le_n (S n))))
   (maxlist (Part_Mesh_List (Partition_Dom Q)))).
  2: simpl in |- *; algebra.
 apply Max_wd_unfolded.
  apply cg_minus_wd; apply H0.
 apply eq_transitive_unfolded with (Mesh (Partition_Dom P)).
  unfold Mesh in |- *; algebra.
 apply eq_transitive_unfolded with (Mesh (Partition_Dom Q)).
  apply H.
  intros.
  unfold Partition_Dom in |- *; simpl in |- *.
  apply H0.
 unfold Mesh in |- *; algebra.
Qed.

Lemma Mesh_wd' : forall n a b (Hab : a [<=] b) (P Q : Partition Hab n),
 (forall i Hi, P i Hi [=] Q i Hi) -> Mesh P [=] Mesh Q.
Proof.
 intros.
 apply Mesh_wd.
 intros; apply H.
Qed.

(**
The mesh of an even partition is easily calculated.
*)

Lemma even_partition_Mesh : forall m Hm a b (Hab : a [<=] b),
 Mesh (Even_Partition Hab m Hm) [=] (b[-]a[/] _[//]nring_ap_zero' _ _ Hm).
Proof.
 simple induction m.
  intros; exfalso; apply Hm; auto.
 intros.
 unfold Mesh in |- *.
 elim (le_lt_dec n 0); intro.
  cut (0 = n); [ intro | auto with arith ].
  generalize Hm; clear H a0 Hm.
  rewrite <- H0; intros.
  simpl in |- *.
  rational.
 apply eq_transitive_unfolded with (Max (a[+]nring (S n) [*] (b[-]a[/] _[//]nring_ap_zero' _ _ Hm) [-]
   (a[+]nring n[*] (b[-]a[/] _[//]nring_ap_zero' _ _ Hm)))
     (maxlist (Part_Mesh_List (Partition_Dom (Even_Partition Hab _ Hm))))).
  cut (n = S (pred n)); [ intro | apply S_pred with 0; auto ].
  generalize Hm; rewrite H0; clear Hm; intro.
  simpl in |- *; algebra.
 eapply eq_transitive_unfolded.
  apply Max_comm.
 simpl in |- *.
 eapply eq_transitive_unfolded.
  apply leEq_imp_Max_is_rht.
  2: rational.
 apply eq_imp_leEq.
 rstepr (b[-]a[/] nring n[+][1][//]nring_ap_zero' _ _ Hm).
 apply eq_transitive_unfolded with (Mesh (Partition_Dom (Even_Partition Hab _ Hm))).
  simpl in |- *; algebra.
 cut (0 <> n); intro.
  eapply eq_transitive_unfolded.
   apply Mesh_wd' with (Q := Even_Partition (part_pred_lemma _ _ Hab (S n) (Even_Partition Hab _ Hm) n
     (le_n_Sn n)) _ H0).
   intros; simpl in |- *; rational.
  eapply eq_transitive_unfolded.
   apply H.
  simpl in |- *; rational.
 apply (lt_O_neq n); auto.
Qed.

(**
** Miscellaneous
%\begin{convention}% Throughout this section, let [a,b:IR] and [I] be [[a,b]].
%\end{convention}%
*)

Variables a b : IR.
(* begin hide *)
Let I := compact a b.
(* end hide *)
Hypothesis Hab : a [<=] b.

(**
An interesting property: in a partition, if [ai [<] aj] then [i < j].
*)

Lemma Partition_Points_mon : forall n (P : Partition Hab n) i j Hi Hj,
 P i Hi [<] P j Hj -> i < j.
Proof.
 intros.
 cut (~ j <= i); intro.
  apply not_ge; auto.
 exfalso.
 apply less_irreflexive_unfolded with (x := P i Hi).
 apply less_leEq_trans with (P j Hj).
  assumption.
 apply local_mon'_imp_mon'_le with (f := fun (i : nat) (Hi : i <= n) => P i Hi).
   intros; apply prf2.
  intro; intros; apply prf1; assumption.
 assumption.
Qed.

Lemma refinement_resp_mult : forall m n Hm Hn, {k : nat | m = n * k} ->
 Refinement (Even_Partition Hab n Hn) (Even_Partition Hab m Hm).
Proof.
 intros m n Hm Hn H.
 elim H; intros k Hk.
 red in |- *.
 cut (0 <> k); intro.
  exists (fun i : nat => i * k); repeat split.
    symmetry  in |- *; assumption.
   intros.
   apply mult_lt_compat_r.
    assumption.
   apply neq_O_lt; auto.
  intros.
  cut (i * k <= m).
   intro.
   exists H1.
   simpl in |- *.
   apply bin_op_wd_unfolded.
    algebra.
   generalize Hm; rewrite Hk.
   clear Hm; intro.
   rstepl (nring i[*]nring k[*] (b[-]a[/] _[//]
     mult_resp_ap_zero _ _ _ (nring_ap_zero' _ _ Hn) (nring_ap_zero' _ _ H0))).
   apply mult_wd.
    apply eq_symmetric_unfolded; apply nring_comm_mult.
   apply div_wd.
    algebra.
   apply eq_symmetric_unfolded; apply nring_comm_mult.
  rewrite Hk.
  apply Nat.mul_le_mono_r; assumption.
 apply Hm.
 rewrite Hk.
 rewrite <- H0.
 auto.
Qed.

(**
%\begin{convention}% Assume [m,n] are positive natural numbers and
denote by [P] and [Q] the even partitions with, respectively, [m] and
[n] points.
%\end{convention}%

Even partitions always have a common refinement.
*)

Variables m n : nat.
Hypothesis Hm : 0 <> m.
Hypothesis Hn : 0 <> n.

(* begin hide *)
Let P := Even_Partition Hab m Hm.
Let Q := Even_Partition Hab n Hn.
(* end hide *)

Lemma even_partition_refinement : {N : nat | {HN : 0 <> N |
 Refinement P (Even_Partition Hab N HN) |
 Refinement Q (Even_Partition Hab N HN)}}.
Proof.
 exists (m * n).
 cut (0 <> m * n); intro.
  exists H.
   unfold P in |- *; apply refinement_resp_mult.
   exists n; auto.
  unfold Q in |- *; apply refinement_resp_mult.
  exists m; auto with arith.
 clear P Q.
 cut (nring (R:=IR) (m * n) [#] [0]).
  rewrite <- H; simpl in |- *.
  apply ap_irreflexive_unfolded.
 astepl (nring m[*]nring (R:=IR) n).
 apply mult_resp_ap_zero; apply Greater_imp_ap; astepl (nring (R:=IR) 0);
   apply nring_less; apply neq_O_lt; auto.
Qed.

End Even_Partitions.

Section More_Definitions.

(**
** Separation

Some auxiliary definitions.  A partition is said to be separated if all its points are distinct.
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.

Definition _Separated n (P : Partition Hab n) := forall i Hi H', P i Hi [<] P (S i) H'.

(**
Two partitions are said to be (mutually) separated if they are both
separated and all their points are distinct (except for the
endpoints).

%\begin{convention}% Let [P,Q] be partitions of [I] with,
respectively, [n] and [m] points.
%\end{convention}%
*)

Variables n m : nat.

Variable P : Partition Hab n.
Variable Q : Partition Hab m.

Definition Separated := _Separated _ P and _Separated _ Q and
 (forall i j, 0 < i -> 0 < j -> i < n -> j < m -> forall Hi Hj, P i Hi [#] Q j Hj).

End More_Definitions.

Arguments _Separated [a b Hab n].
Arguments Separated [a b Hab n m].

Section Sep_Partitions.

Variables a b : IR.
(* begin hide *)
Let I := compact a b.
(* end hide *)
Hypothesis Hab : a [<=] b.

(**
The antimesh of a separated partition is always positive.
*)

Lemma pos_AntiMesh : forall n (P : Partition Hab n),
 0 < n -> _Separated P -> [0] [<] AntiMesh P.
Proof.
 intro; case n; clear n.
  intros P H H0; exfalso; apply (Nat.lt_irrefl _ H).
 intros n P H H0.
 unfold AntiMesh in |- *.
 apply less_minlist.
  simpl in |- *; auto with arith.
 intros y H1.
 elim (Part_Mesh_List_lemma _ _ _ _ _ _ H1); intros i Hi.
 elim Hi; clear Hi; intros Hi Hi'.
 elim Hi'; clear Hi'; intros Hi' H'.
 eapply less_wdr.
  2: apply eq_symmetric_unfolded; apply H'.
 apply shift_less_minus; astepl (P i Hi).
 apply H0.
Qed.

(**
A partition can have only one point iff the endpoints of the interval
are the same; moreover, if the partition is separated and the
endpoints of the interval are the same then it must have one point.
*)

Lemma partition_length_zero : Partition Hab 0 -> a [=] b.
Proof.
 intro H.
 Step_final (H 0 (Nat.le_0_l 0)).
Qed.

Lemma _Separated_imp_length_zero : forall n (P : Partition Hab n),
 _Separated P -> a [=] b -> 0 = n.
Proof.
 intros n P H H0.
 cut (~ 0 <> n); [ auto with zarith | intro ].
 cut (0 < n); [ intro | apply neq_O_lt; auto ].
 cut (a [#] b).
  exact (eq_imp_not_ap _ _ _ H0).
 astepl (P _ (Nat.le_0_l _)).
 astepr (P _ (le_n _)).
 apply less_imp_ap.
 apply local_mon_imp_mon_le with (f := fun (i : nat) (H : i <= n) => P i H).
  exact H.
 assumption.
Qed.

Lemma partition_less_imp_gt_zero : forall n (P : Partition Hab n), a [<] b -> 0 < n.
Proof.
 intros n P H.
 cut (0 <> n); intro.
  apply neq_O_lt; auto.
 exfalso.
 cut (a [=] b).
  intro; apply less_irreflexive_unfolded with (x := a).
  astepr b; assumption.
 apply partition_length_zero.
 rewrite H0; apply P.
Qed.

End Sep_Partitions.
