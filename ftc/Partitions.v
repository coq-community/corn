(* $Id$ *)

Require Export Continuity.

(** printing Partition_Sum %\ensuremath{\sum_P}% #&sum;<sub>P</sub># *)

Section Definitions.

(** *Partitions

We now begin to lay the way for the definition of integral.  This will be done in the Riemann way, through the definition of a sequence of sums that is proved to be convergent; in order to do that, we first need to do a bit of work on partitions.

**Definitions

A partition is defined as a record type.  For each compact interval $[a,b]$#[a,b]# and each natural number [n], a partition of $[a,b]$#[a,b]# with $n+1$#n+1# points is a choice of real numbers [a [=] a0 [<=] a1 [<=] an [=] b]; the following specification works as follows:
 - [Pts] is the function that chooses the points (it is declared as a coercion);
 - [prf1] states that [Pts] is a setoid function;
 - [prf2] states that the points are ordered;
 - [start] requires that [a0 [=] a] and
 - [finish] requires that [an [=] b].

*)

Record Partition (a b : IR) (Hab : a[<=]b) (lng : nat) : Type := 
  {Pts :> forall i : nat, i <= lng -> IR;
   prf1 :
    forall i j : nat,
    i = j -> forall (Hi : i <= lng) (Hj : j <= lng), Pts i Hi[=]Pts j Hj;
   prf2 :
    forall (i : nat) (H : i <= lng) (H' : S i <= lng),
    Pts i H[<=]Pts (S i) H';
   start : forall H : 0 <= lng, Pts 0 H[=]a;
   finish : forall H : lng <= lng, Pts lng H[=]b}.

(**
Two immediate consequences of this are that [ai [<=] aj] whenever [(le i j)] and that [ai] is in $[a,b]$#[a,b]# for all [i].
*)

Lemma Partition_mon :
 forall a b Hab lng (P : Partition a b Hab lng) (i j : nat) Hi Hj,
 i <= j -> P i Hi[<=]P j Hj.
intros; induction  j as [| j Hrecj].
cut (i = 0); [ intro | auto with arith ].
apply eq_imp_leEq; apply prf1; auto.
elim (le_lt_eq_dec _ _ H); intro H1.
cut (j <= lng); [ intro | clear Hrecj; omega ].
apply leEq_transitive with (Pts _ _ _ _ P j H0).
apply Hrecj; clear Hrecj; auto with arith.
apply prf2.
apply eq_imp_leEq; apply prf1; assumption.
Qed.

Lemma Partition_in_compact :
 forall a b Hab lng (P : Partition a b Hab lng) (i : nat) (H : i <= lng),
 compact a b Hab (P i H).
intros.
split.
apply leEq_wdl with (P _ (le_O_n _)).
apply Partition_mon; auto with arith.
apply start.
apply leEq_wdr with (P _ (le_n _)).
apply Partition_mon; auto with arith.
apply finish.
Qed.

(**
Each partition of $[a,b]$#[a,b]# implies a partition of the interval $[a,a_{n-1}]$#[a,a(n-1)]#.  This partition will play an important role in much of our future work, so we take some care to define it.
*)

Lemma part_pred_lemma :
 forall a b Hab lng (P : Partition a b Hab lng) (i : nat) (Hi : i <= lng),
 a[<=]P i Hi.
intros.
apply leEq_wdl with (P 0 (le_O_n _)).
apply Partition_mon; auto with arith.
apply start.
Qed.

Definition Partition_Dom a b Hab n P :
  Partition a _ (part_pred_lemma a b Hab (S n) P n (le_n_Sn n)) n.
intros.
apply Build_Partition with (fun (i : nat) (Hi : i <= n) => P i (le_S _ _ Hi)).
intros; simpl in |- *; apply prf1; assumption.
intros; simpl in |- *; apply prf2.
intros; simpl in |- *; apply start.
intros; simpl in |- *; apply prf1; auto.
Defined.

(**
The mesh of a partition is the greatest distance between two consecutive points.  For convenience's sake we also define the dual concept, which is very helpful in some situations.  In order to do this, we begin by building a list with all the distances between consecutive points; next we only need to extract the maximum and the minimum of this list. Notice that this list is nonempty except in the case when [a [=] b] and [n=0]; this means that the convention we took of defining the minimum and maximum of the empty list to be 0 actually helps us in this case.
*)

Definition Part_Mesh_List n a b Hab (P : Partition a b Hab n) : list IR.
intro; induction  n as [| n Hrecn]; intros.
apply nil.
apply cons.
apply (P _ (le_n (S n))[-]P _ (le_S _ _ (le_n n))).
apply
 Hrecn with a (P _ (le_n_Sn n)) (part_pred_lemma _ _ _ _ P n (le_n_Sn n)).
apply Partition_Dom.
Defined.

Definition Mesh a b Hab n P := maxlist (Part_Mesh_List n a b Hab P).

Definition AntiMesh a b Hab n P := minlist (Part_Mesh_List n a b Hab P).

(**
Even partitions (partitions where all the points are evenly spaced) will also play a central role in our work; the first two lemmas are presented simply to make the definition of even partition lighter.
*)

Lemma even_part_1 :
 forall (a b : IR) (n : nat) (Hn : 0 <> n),
 a[+]nring 0[*](b[-]a[/] _[//]nring_ap_zero' _ n Hn)[=]a.
intros; rational.
Qed.

Lemma even_part_2 :
 forall (a b : IR) (n : nat) (Hn : 0 <> n),
 a[+]nring n[*](b[-]a[/] _[//]nring_ap_zero' _ n Hn)[=]b.
intros; rational.
Qed.

Definition Even_Partition a b Hab n (Hn : 0 <> n) : Partition a b Hab n.
intros.
apply
 Build_Partition
  with
    (fun (i : nat) (Hi : i <= n) =>
     a[+]nring i[*](b[-]a[/] _[//]nring_ap_zero' _ n Hn)).
intros; simpl in |- *.
rewrite H; Algebra.
intros; simpl in |- *.
apply plus_resp_leEq_lft.
apply mult_resp_leEq_rht.
apply less_leEq; apply less_plusOne.
apply shift_leEq_div.
apply nring_pos; clear H; apply neq_O_lt; auto.
apply shift_leEq_minus.
AStepl (Zero[+]a).
AStepl a; assumption.
intros; simpl in |- *; apply even_part_1; auto.
intros; simpl in |- *; apply even_part_2; auto.
Defined.

(**
We will also need to consider arbitrary sums %of the form 
\[\sum_{i=0}^{n-1}f(x_i)(a_{i+1}-a_i)\]%#of f(xi)(a(i+1)-a(i))# where $x_i\in[a_i,a_{i+1}]$#xi&in;[ai,a(i+1)]#.  For this, we again need a choice function [x] which has to satisfy some condition.  We define the condition and the sum:
*)

Definition Points_in_Partition a b Hab n (P : Partition a b Hab n)
  (g : forall i : nat, i < n -> IR) : CProp :=
  forall (i : nat) (H : i < n),
  Compact (prf2 _ _ _ _ P i (lt_le_weak _ _ H) H) (g i H).

Lemma Pts_part_lemma :
 forall a b Hab n P g,
 Points_in_Partition a b Hab n P g ->
 forall (i : nat) (H : i < n), compact a b Hab (g i H).
intros a b Hab n P g H i H0.
elim (H i H0); intros.
split.
eapply leEq_transitive.
2: apply a0.
apply leEq_wdl with (P 0 (le_O_n _)).
apply Partition_mon; auto with arith.
apply start.
eapply leEq_transitive.
apply b0.
apply leEq_wdr with (P n (le_n _)).
apply Partition_mon; auto with arith.
apply finish.
Qed.

Definition Partition_Sum a b Hab n (P : Partition a b Hab n) g F
  (H : Points_in_Partition _ _ _ _ P g)
  (incF : included (Compact Hab) (Dom F)) :=
  Sumx
    (fun (i : nat) (Hi : i < n) =>
     F (g i Hi) (incF _ (Pts_part_lemma _ _ _ _ _ _ H i Hi))[*]
     (P (S i) Hi[-]P i (lt_le_weak _ _ Hi))).

(** **Constructions

We now formalize some trivial and helpful constructions.

%\begin{convention}% We will assume a fixed compact interval $[a,b]$#[a,b]#, denoted by [I].
%\end{convention}%
*)

Variables a b : IR.
Hypothesis Hab : a[<=]b.
(* begin hide *)
Let I := compact a b Hab.
(* end hide *)

Section Getting_Points.

(**
From a partition we always have a canonical choice of points at which to evaluate a function: just take all but the last points of the partition.

%\begin{convention}% Let [Q] be a partition of [I] with [m] points.
%\end{convention}%
*)

Variable m : nat.
Variable Q : Partition a b Hab m.

Definition Partition_imp_points : forall i : nat, i < m -> IR.
intros.
apply (Q i (lt_le_weak _ _ H)).
Defined.

Lemma Partition_imp_points_1 :
 Points_in_Partition _ _ _ _ Q Partition_imp_points.
red in |- *; intros.
unfold Partition_imp_points in |- *; split.
apply leEq_reflexive.
apply prf2.
Qed.

Lemma Partition_imp_points_2 : nat_less_n_fun _ _ Partition_imp_points.
red in |- *; intros.
unfold Partition_imp_points in |- *; simpl in |- *.
apply prf1; auto.
Qed.

End Getting_Points.

(**
As a corollary, given any continuous function [F] and a natural number we have an immediate choice of a sum of [F] in $[a,b]$#[a,b]#.
*)

Variable F : PartIR.
Hypothesis contF : Continuous_I Hab F.

Definition Even_Partition_Sum (n : nat) (Hn : 0 <> n) : IR.
intros.
apply
 Partition_Sum
  with
    a
    b
    Hab
    n
    (Even_Partition a b Hab n Hn)
    (Partition_imp_points _ (Even_Partition a b Hab n Hn))
    F.
apply Partition_imp_points_1.
apply contin_imp_inc; assumption.
Defined.

End Definitions.

Implicit Arguments Partition [a b].
Implicit Arguments Partition_Dom [a b Hab n].
Implicit Arguments Mesh [a b Hab n].
Implicit Arguments AntiMesh [a b Hab n].
Implicit Arguments Pts [a b Hab lng].
Implicit Arguments Part_Mesh_List [n a b Hab].
Implicit Arguments Points_in_Partition [a b Hab n].
Implicit Arguments Partition_Sum [a b Hab n P g F].
Implicit Arguments Even_Partition [a b].
Implicit Arguments Even_Partition_Sum [a b].

Hint Resolve start finish: algebra.

Section Lemmas.

(** **Lemmas

Finally, we include some important lemmas about partitions.

If a partition has more than one point then its mesh list is nonempty.
*)

Lemma length_Part_Mesh_List :
 forall (n : nat) (a b : IR) (Hab : a[<=]b) (P : Partition Hab n),
 0 < n -> 0 < length (Part_Mesh_List P).
intro; case n; intros.
elimtype False; inversion H.
simpl in |- *; auto with arith.
Qed.

(**
Any element of the auxiliary list defined to calculate the mesh of a partition has a very specific form.
*)

Lemma Part_Mesh_List_lemma :
 forall (n : nat) (a b : IR) (Hab : a[<=]b) (P : Partition Hab n) (x : IR),
 member x (Part_Mesh_List P) ->
 {i : nat | {Hi : i <= n | {Hi' : S i <= n | x[=]P _ Hi'[-]P _ Hi}}}.
intro; induction  n as [| n Hrecn].
simpl in |- *; intros.
elimtype CFalse; assumption.
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

Lemma Mesh_nonneg :
 forall (n : nat) (a b : IR) (Hab : a[<=]b) (P : Partition Hab n),
 Zero[<=]Mesh P.
simple induction n.
intros; unfold Mesh in |- *; simpl in |- *.
apply leEq_reflexive.
clear n; intros.
unfold Mesh in |- *.
apply leEq_transitive with (P _ (le_n (S n))[-]P _ (le_S _ _ (le_n n))).
apply shift_leEq_minus; AStepl (P _ (le_S _ _ (le_n n))).
apply prf2.
apply maxlist_greater.
right; Algebra.
Qed.

Lemma AntiMesh_nonneg :
 forall (n : nat) (a b : IR) (Hab : a[<=]b) (P : Partition Hab n),
 Zero[<=]AntiMesh P.
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
apply shift_leEq_minus; AStepl (P _ (le_S _ _ (le_n n))).
apply prf2.
Qed.

(**
Most important, AntiMesh and Mesh provide lower and upper bounds for the distance between any two consecutive points in a partition.

%\begin{convention}% Let [I] be $[a,b]$#[a,b]# and [P] be a partition of [I] with [n] points.
%\end{convention}%
*)

Variables a b : IR.
(* begin hide *)
Let I := compact a b.
(* end hide *)
Hypothesis Hab : a[<=]b.

Variable n : nat.
Variable P : Partition Hab n.

Lemma Mesh_lemma : forall (i : nat) H H', P (S i) H'[-]P i H[<=]Mesh P.
clear I; generalize n a b Hab P; clear P n Hab a b.
simple induction n.
intros; elimtype False; inversion H'.
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

Lemma AntiMesh_lemma : forall i H H', AntiMesh P[<=]P (S i) H'[-]P i H.
clear I; generalize n a b Hab P; clear P n Hab a b.
simple induction n.
intros; elimtype False; inversion H'.
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
unfold AntiMesh in |- *; simpl in |- *.
eapply leEq_wdr.
2: apply cg_inv_inv.
apply inv_resp_leEq; apply rht_leEq_Max.
cut (i = S m); [ intro | auto with arith ].
generalize H' H0; clear H0 H'.
rewrite H2; intros.
unfold AntiMesh in |- *; apply minlist_smaller; right.
apply cg_minus_wd; apply prf1; auto.
Qed.

(**
Finally, we define what it means for a partition [Q] to be a refinement of [P] and prove the two main properties of refinements.
*)

Definition Refinement (m : nat) (Q : Partition Hab m) :=
  {f : nat -> nat |
  f 0 = 0 /\ f n = m /\ (forall i j : nat, i < j -> f i < f j) |
  forall (i : nat) (H : i <= n), {H' : f i <= m | P i H[=]Q (f i) H'}}.

Lemma Refinement_prop :
 forall m Q,
 Refinement m Q ->
 forall (i : nat) (Hi : i <= m) (Hi' : S i <= m),
 {j : nat |
 {Hj : j <= n | {Hj' : S j <= n | P _ Hj[<=]Q _ Hi | Q _ Hi'[<=]P _ Hj'}}}.
intros m Q H i Hi Hi'.
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
cut (f j < f n); [ intro | apply le_lt_trans with i; auto ].
apply not_ge.
intro; red in H1.
apply (le_not_lt (f j) (f n)); auto with arith.
apply Hfmon.
elim (le_lt_eq_dec _ _ H1); intro; auto.
rewrite b0 in H0; elim (lt_irrefl (f j)); auto.
rewrite <- Hfn in Hi'; auto.
apply mon_fun_covers; auto.
exists n; clear Hf Hfmon.
rewrite Hfn; assumption.
Qed.

Lemma Mesh_leEq : forall m Q, Refinement m Q -> Mesh Q[<=]Mesh P.
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
cut
 {j : nat |
 {Hj : j <= n | {Hj' : S j <= n | P _ Hj[<=]Q _ Hi | Q _ Hi'[<=]P _ Hj'}}}.
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

Implicit Arguments Refinement [a b Hab n m].