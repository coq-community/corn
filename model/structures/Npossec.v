(* $Id: Npossec.v,v 1.3 2004/04/06 15:46:05 lcf Exp $ *)

(** printing Npos $\mathbb{N}^{+}$ #N<SUP>+</SUP># *)

Require Export Nsec.
Require Import Arith.

(** **[Npos]
The positive natural numbers have some nice properties. Addition as well 
as multiplication preserve the feature of being positive.
*)

Lemma plus_resp_Npos0 : forall x y : nat, x <> 0 -> y <> 0 -> (x+y) <> 0.
intros x y H H0.
unfold not in |- *.
intros H1.
unfold not in H.
apply H.
omega.
Qed.

Lemma Npos_is_suc : forall y : nat, y <> 0 -> exists m : nat, y = S m.
intros y H.
exists (pred y).
unfold pred in |- *.
induction  y as [| y Hrecy].
intuition.
intuition.
Qed.

Lemma mult_resp_Npos0 : forall x y : nat, x <> 0 -> y <> 0 -> (x*y) <> 0.
intros x y H H0.
set (H1 := Npos_is_suc y H0) in *.
elim H1.
intros y0 H2.
rewrite H2 in H1.
rewrite H2 in H0.
rewrite H2.
generalize y0.
clear H1 H0 H2 y0 y.
intro y0.
induction  y0 as [| y0 Hrecy0].
rewrite mult_comm.
rewrite mult_1_l.
exact H.

rewrite <- mult_n_Sm.
cut (0 <> (x*S y0+x) -> (x*S y0+x) <> 0).
intro H3.
apply H3.
apply lt_O_neq.
cut ((x*S y0+x) > 0).
unfold gt in |- *.
intuition.
apply gt_trans with (x*S y0).
apply gt_le_trans with (x*S y0+0).
apply plus_gt_compat_l. 
omega.
omega.
unfold gt in |- *.
apply neq_O_lt.
cut ((x*S y0) <> 0).
auto.
apply Hrecy0.
auto.
Qed.
