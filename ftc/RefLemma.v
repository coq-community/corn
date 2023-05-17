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

Require Export CoRN.ftc.RefSeparating.
Require Export CoRN.ftc.RefSeparated.
Require Export CoRN.ftc.RefSepRef.

Section Refinement_Lemma.

(**
* The Refinement Lemmas

Here we resume the results proved in four different files.  The aim is to prove the following result (last part of Theorem 2.9 of Bishop 1967):

%\noindent\textbf{%#<b>#Theorem#</b>#%}% Let [f] be a continuous function on a
compact interval [[a,b]] with modulus of continuity%\footnote{%# (#From our
point of view, the modulus of continuity is simply the proof that [f] is
continuous.#)#%}% [lia].
Let [P] be a partition of [[a,b]] and [eps [>] [0]] be such that
[mesh(P)  [<]  lia(eps)].
Then
%\[\left|S(f,P)-\int_a^bf(x)dx\right|\leq\varepsilon(b-a),\]%#|S(f,P)-&int;f(x)dx|&le;&epsilon;(b-a)#
where [S(f,P)] denotes any sum of the function [f] respecting the partition
[P] (as previously defined).

The proof of this theorem relies on the fact that for any two partitions [P]
and [R] of [[a,b]] it is possible to define a partition [Q] which is
``almost'' a common refinement of [P] and [R]---that is, given [eps [>] [0]]
it is possible to define [Q] such that for every point [x] of either [P] or
[R] there is a point [y] of [Q] such that [|x[-]y|  [<]  eps].
This requires three separate constructions (done in three separate files)
which are then properly combined to give the final result.  We recommend the
reader to ignore this technical constructions.

First we prove that if [P] and [R] are both
separated (though not necessarily separated from each other) then we can
define a partition [P'] arbitrarily close to [P] (that is, such that given
[alpha [>] [0]] and [xi [>] [0]] [P'] satisfies both
[mesh(P')  [<]  mesh(P) [+] xi] and for every choice of points [x_i] respecting
[P] there is a choice of points [x'_i] respecting [P'] such that
[|S(f,P)-S(f,P')|  [<]  alpha]) that is separated from [R].

Then we prove that given any partition [P]
and assuming [a  [#]  b] we can define a partition [P'] arbitrarily close to
[P] (in the same sense as above) which is separated.

Finally we prove that every two separated
partitions [P] and [R] have a common refinement---as every two points in [P]
and [R] are apart, we can decide which one is smaller.  We use here the
technical results about ordering that we proved in the file [IntegralLemmas.v].

Using the results from these files, we prove our main lemma in several steps
(and versions).

%\begin{convention}% Throughout this section:
 - [a,b:IR] and [I] denotes [[a,b]];
 - [F] is a partial function continuous in [I].

%\end{convention}%
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variable F : PartIR.
Hypothesis contF : Continuous_I Hab F.
Hypothesis incF : included (Compact Hab) (Dom F).

(* begin hide *)
Let contF' := contin_prop _ _ _ _ contF.
(* end hide *)

Section First_Refinement_Lemma.

(**
This is the first part of the proof of Theorem 2.9.

%\begin{convention}%
 - [P, Q] are partitions of [I] with, respectively, [n] and [m] points;
 - [Q] is a refinement of [P];
 - [e] is a positive real number;
 - [d] is the modulus of continuity of [F] for [e];
 - the mesh of [P] is less or equal to [d];
 - [fP] and [fQ] are choices of points respecting the partitions [P] and [Q],
respectively.

%\end{convention}%
*)

Variable e : IR.
Hypothesis He : [0] [<] e.

(* begin hide *)
Let d := proj1_sig2T _ _ _ (contF' e He).
(* end hide *)

Variables m n : nat.
Variable P : Partition Hab n.
Hypothesis HMesh : Mesh P [<=] d.

Variable Q : Partition Hab m.
Hypothesis Href : Refinement P Q.

Variable fP : forall i : nat, i < n -> IR.
Hypothesis HfP : Points_in_Partition P fP.
Hypothesis HfP' : nat_less_n_fun fP.

Variable fQ : forall i : nat, i < m -> IR.
Hypothesis HfQ : Points_in_Partition Q fQ.
Hypothesis HfQ' : nat_less_n_fun fQ.

(* begin hide *)
Let sub := proj1_sig2T _ _ _ Href.

Lemma RL_sub_0 : sub 0 = 0.
Proof.
 elim (proj2a_sig2T _ _ _ Href); auto.
Qed.

Lemma RL_sub_n : sub n = m.
Proof.
 elim (proj2a_sig2T _ _ _ Href); intros.
 elim H0; auto.
Qed.

Lemma RL_sub_mon : forall i j : nat, i < j -> sub i < sub j.
Proof.
 elim (proj2a_sig2T _ _ _ Href); intros.
 elim H0; intros.
 elim H1; auto.
Qed.

Lemma RL_sub_mon' : forall i j : nat, i <= j -> sub i <= sub j.
Proof.
 intros.
 elim (le_lt_eq_dec _ _ H); intro.
  apply Nat.lt_le_incl; apply RL_sub_mon; assumption.
 rewrite b0; apply le_n.
Qed.

Lemma RL_sub_hyp :
  forall (i : nat) (H : i <= n), {H' : sub i <= m | P i H [=] Q (sub i) H'}.
Proof.
 apply (proj2b_sig2T _ _ _ Href).
Qed.

Lemma RL_sub_S : forall i : nat, 0 < sub (S i).
Proof.
 rewrite <- RL_sub_0.
 intro; apply RL_sub_mon; apply Nat.lt_0_succ.
Qed.

Let H : forall i j : nat, i < n -> j <= pred (sub (S i)) -> j < m.
Proof.
 intros.
 cut (S i <= n); [ intro | apply H ].
 elim (le_lt_eq_dec _ _ H1); clear H1; intro.
  cut (sub (S i) < sub n); [ intro | apply RL_sub_mon; assumption ].
  rewrite <- RL_sub_n.
  apply Nat.le_lt_trans with (sub (S i)); auto; eapply Nat.le_trans; [ apply H0 | apply Nat.le_pred_l ].
 cut (0 < sub (S i)); [ intro | apply RL_sub_S ].
 rewrite <- RL_sub_n.
 rewrite <- b0.
 rewrite <- (Nat.lt_succ_pred _ _ H1); auto with arith.
Qed.

Let H' : forall i j : nat, i < n -> j <= pred (sub (S i)) -> S j <= m.
Proof.
 intros; exact (H _ _ H0 H1).
Qed.

Let H0 : forall i : nat, sub i < sub (S i).
Proof.
 intro; apply RL_sub_mon; apply Nat.lt_succ_diag_r.
Qed.

Lemma RL_sub_SS : forall i : nat, sub i <= S (pred (sub (S i))).
Proof.
 intro; cut (sub i < sub (S i)); [ intro | apply H0 ].
 rewrite (Nat.lt_succ_pred _ _ H1); apply Nat.lt_le_incl; apply H0.
Qed.

Definition RL_h : nat -> IR.
Proof.
 intro i.
 elim (le_lt_dec i m); intro.
  apply (Q _ a0).
 apply ZeroR.
Defined.

Definition RL_g : nat -> IR.
Proof.
 intro i.
 elim (le_lt_dec m i); intro.
  apply ZeroR.
 apply (Q _ b0[-]Q _ (Nat.lt_le_incl _ _ b0)).
Defined.

Notation g := RL_g.
Notation h := RL_h.

Lemma ref_calc1 :
  forall (i : nat) (Hi : i < n),
  Sum2
    (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
     Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj'))) [=]
  P _ Hi[-]P _ (Nat.lt_le_incl _ _ Hi).
Proof.
 intros.
 unfold Sum2 in |- *.
 elim (RL_sub_hyp (S i) Hi); intros P1 HP1.
 elim (RL_sub_hyp i (Nat.lt_le_incl _ _ Hi)); intros P2 HP2.
 apply eq_transitive_unfolded with (Q _ P1[-]Q _ P2).
  2: apply eq_symmetric_unfolded; apply cg_minus_wd; [ apply HP1 | apply HP2 ].
 cut (sub (S i) = S (pred (sub (S i)))).
  2: symmetry; apply Nat.lt_succ_pred with 0; apply RL_sub_S.
 intro.
 generalize P1 HP1; clear HP1 P1. pattern (sub (S i)) at 1 2 11 in |- *.
 rewrite H1; intros.
 eapply eq_transitive_unfolded.
  apply str_Mengolli_Sum_gen with (f := h).
   apply RL_sub_SS.
  intros j Hj Hj'.
  elim (le_lt_dec j (pred (sub (S i)))); intro; simpl in |- *.
   elim (le_lt_dec (sub i) j); intro; simpl in |- *.
    unfold h in |- *.
    apply cg_minus_wd.
     elim (le_lt_dec (S j) m); intro; simpl in |- *.
      apply prf1; auto.
     cut (S j <= m); [ intro | apply H' with i; assumption ].
     exfalso; apply (le_not_lt _ _ H2 b0).
    elim (le_lt_dec j m); intro; simpl in |- *.
     apply prf1; auto.
    cut (j < m); [ intro | apply H with i; assumption ].
    exfalso; apply le_not_lt with m j; auto with arith.
   exfalso; apply le_not_lt with (sub i) j; auto with arith.
  exfalso; apply (le_not_lt _ _ Hj' b0).
 unfold h in |- *.
 apply cg_minus_wd.
  elim (le_lt_dec (S (pred (sub (S i)))) m); intro; simpl in |- *.
   apply prf1; auto.
  exfalso.
  apply (le_not_lt _ _ P1 b0).
 elim (le_lt_dec (sub i) m); intro; simpl in |- *.
  apply prf1; auto.
 exfalso.
 apply (le_not_lt _ _ P2 b0).
Qed.

Notation just1 := (incF _ (Pts_part_lemma _ _ _ _ _ _ HfP _ _)).
Notation just2 := (incF _ (Pts_part_lemma _ _ _ _ _ _ HfQ _ _)).

Lemma ref_calc2 :
  AbsIR (Partition_Sum HfP incF[-]Partition_Sum HfQ incF) [=]
  AbsIR
    (Sumx
       (fun (i : nat) (Hi : i < n) =>
        Part F (fP i Hi) just1[*]
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))) [-]
     Sumx
       (fun (i : nat) (Hi : i < n) =>
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           Part F (fQ j (H _ _ Hi Hj')) just2[*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))).
Proof.
 apply AbsIR_wd; unfold Partition_Sum in |- *.
 apply cg_minus_wd.
  apply Sumx_wd; intros.
  apply mult_wdr.
  apply eq_symmetric_unfolded; apply ref_calc1.
 apply eq_symmetric_unfolded; unfold Sum2 in |- *.
 apply eq_transitive_unfolded with (Sumx (fun (j : nat) (Hj : j < m) => part_tot_nat_fun _ _
   (fun (i : nat) (H : i < m) => Part F (fQ i H) just2[*] (Q _ H[-]Q _ (Nat.lt_le_incl _ _ H))) j)).
  apply str_Sumx_Sum_Sum with (g := fun (i : nat) (Hi : i < n) (i0 : nat) =>
    sumbool_rect (fun _ : {sub i <= i0} + {i0 < sub i} => IR) (fun _ : sub i <= i0 => sumbool_rect
      (fun _ : {i0 <= pred (sub (S i))} + {pred (sub (S i)) < i0} => IR)
        (fun a1 : i0 <= pred (sub (S i)) => Part F (fQ i0 (H i i0 Hi a1)) just2[*]
          (Q (S i0) (H' i i0 Hi a1) [-] Q i0 (Nat.lt_le_incl i0 m (H i i0 Hi a1))))
            (fun _ : pred (sub (S i)) < i0 => [0]) (le_lt_dec i0 (pred (sub (S i)))))
              (fun _ : i0 < sub i => [0]) (le_lt_dec (sub i) i0)) (h := part_tot_nat_fun _ _
                (fun (i : nat) (H : i < m) =>
                  Part F (fQ i H) just2[*] (Q _ H[-]Q _ (Nat.lt_le_incl _ _ H)))).
     exact RL_sub_0.
    exact RL_sub_mon.
   intros.
   elim (le_lt_dec (sub i) j); intro; simpl in |- *.
    elim (le_lt_dec j (pred (sub (S i)))); intro; simpl in |- *.
     unfold part_tot_nat_fun in |- *.
     elim (le_lt_dec m j); intro; simpl in |- *.
      exfalso.
      cut (0 < sub (S i)); [ intro | apply RL_sub_S ].
      cut (sub (S i) <= m); intros.
       apply (le_not_lt _ _ H4); apply Nat.le_lt_trans with j; auto.
      rewrite <- RL_sub_n.
      apply RL_sub_mon'; apply Hi.
     apply mult_wd.
      apply pfwdef.
      apply HfQ'; auto.
     apply cg_minus_wd; apply prf1; auto.
    exfalso; apply (le_not_lt _ _ b0).
    rewrite (Nat.lt_succ_pred _ _ (RL_sub_S i)); auto.
   exfalso; apply (le_not_lt _ _ H1 b0).
  symmetry  in |- *; apply RL_sub_n.
 apply Sumx_wd; intros.
 unfold part_tot_nat_fun in |- *.
 elim (le_lt_dec m i); intro; simpl in |- *.
  exfalso; apply le_not_lt with m i; auto.
 apply mult_wd.
  apply pfwdef; apply HfQ'; auto.
 apply cg_minus_wd; apply prf1; auto.
Qed.

Lemma ref_calc3 :
  AbsIR
    (Sumx
       (fun (i : nat) (Hi : i < n) =>
        Part F (fP i Hi) just1[*]
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))) [-]
     Sumx
       (fun (i : nat) (Hi : i < n) =>
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           Part F (fQ j (H _ _ Hi Hj')) just2[*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))) [=]
  AbsIR
    (Sumx
       (fun (i : nat) (Hi : i < n) =>
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           Part F (fP i Hi) just1[*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj'))))) [-]
     Sumx
       (fun (i : nat) (Hi : i < n) =>
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           Part F (fQ j (H _ _ Hi Hj')) just2[*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))).
Proof.
 apply AbsIR_wd.
 apply cg_minus_wd; apply Sumx_wd; intros.
  apply eq_symmetric_unfolded; apply Sum2_comm_scal' with
    (f := fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
      Q (S j) (H' _ _ H1 Hj') [-]Q j (Nat.lt_le_incl _ _ (H _ _ H1 Hj'))).
  apply RL_sub_SS.
 algebra.
Qed.

Lemma ref_calc4 :
  AbsIR
    (Sumx
       (fun (i : nat) (Hi : i < n) =>
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           Part F (fP i Hi) just1[*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj'))))) [-]
     Sumx
       (fun (i : nat) (Hi : i < n) =>
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           Part F (fQ j (H _ _ Hi Hj')) just2[*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))) [=]
  AbsIR
    (Sumx
       (fun (i : nat) (Hi : i < n) =>
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           Part F (fP i Hi) just1[*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj'))) [-]
           Part F (fQ j (H _ _ Hi Hj')) just2[*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))).
Proof.
 apply AbsIR_wd.
 eapply eq_transitive_unfolded.
  apply Sumx_minus_Sumx.
 apply Sumx_wd; intros.
 eapply eq_transitive_unfolded.
  apply Sum2_minus_Sum2.
  apply RL_sub_SS.
 algebra.
Qed.

Lemma ref_calc5 :
  AbsIR
    (Sumx
       (fun (i : nat) (Hi : i < n) =>
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           Part F (fP i Hi) just1[*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj'))) [-]
           Part F (fQ j (H _ _ Hi Hj')) just2[*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))) [=]
  AbsIR
    (Sumx
       (fun (i : nat) (Hi : i < n) =>
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           (Part F (fP i Hi) just1[-]Part F (fQ j (H _ _ Hi Hj')) just2) [*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))).
Proof.
 apply AbsIR_wd; apply Sumx_wd; intros.
 apply Sum2_wd; intros.
  apply RL_sub_SS.
 algebra.
Qed.

Lemma ref_calc6 :
  AbsIR
    (Sumx
       (fun (i : nat) (Hi : i < n) =>
        Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           (Part F (fP i Hi) just1[-]Part F (fQ j (H _ _ Hi Hj')) just2) [*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))) [<=]
  Sumx
    (fun (i : nat) (Hi : i < n) =>
     AbsIR
       (Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           (Part F (fP i Hi) just1[-]Part F (fQ j (H _ _ Hi Hj')) just2) [*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))).
Proof.
 eapply leEq_wdr.
  apply triangle_SumxIR.
 apply Sumx_wd.
 intros.
 apply AbsIR_wd.
 apply Sum2_wd.
  apply RL_sub_SS.
 intros j Hj Hj'.
 algebra.
Qed.

Lemma ref_calc7 :
  Sumx
    (fun (i : nat) (Hi : i < n) =>
     AbsIR
       (Sum2
          (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
           (Part F (fP i Hi) just1[-]Part F (fQ j (H _ _ Hi Hj')) just2) [*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))) [<=]
  Sumx
    (fun (i : nat) (Hi : i < n) =>
     Sum2
       (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
        AbsIR
          ((Part F (fP i Hi) just1[-]Part F (fQ j (H _ _ Hi Hj')) just2) [*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))).
Proof.
 apply Sumx_resp_leEq; intros.
 eapply leEq_wdr.
  apply triangle_Sum2IR.
  apply RL_sub_SS.
 algebra.
Qed.

Lemma ref_calc8 :
  Sumx
    (fun (i : nat) (Hi : i < n) =>
     Sum2
       (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
        AbsIR
          ((Part F (fP i Hi) just1[-]Part F (fQ j (H _ _ Hi Hj')) just2) [*]
           (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj')))))) [<=]
  Sumx
    (fun (i : nat) (Hi : i < n) =>
     Sum2
       (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
        e[*] (Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj'))))).
Proof.
 apply Sumx_resp_leEq; intros.
 apply Sum2_resp_leEq.
  apply RL_sub_SS.
 intros j Hj Hj'.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
 apply mult_resp_leEq_both.
    apply AbsIR_nonneg.
   apply AbsIR_nonneg.
  generalize (proj2b_sig2T _ _ _ (contF' e He)); fold d in |- *; intros.
  apply H2.
    unfold I in |- *; apply Pts_part_lemma with n P; assumption.
   unfold I in |- *; apply Pts_part_lemma with m Q; assumption.
  apply leEq_transitive with (Mesh P).
   2: assumption.
  apply leEq_transitive with (AbsIR (P (S i) H1[-]P i (Nat.lt_le_incl _ _ H1))).
   2: eapply leEq_wdl.
    3: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
    2: apply Mesh_lemma.
   2: apply shift_leEq_minus; astepl (P i (Nat.lt_le_incl _ _ H1)); apply prf2.
  apply compact_elements with (prf2 _ _ _ _ P i (Nat.lt_le_incl _ _ H1) H1).
   apply HfP.
  elim (HfQ j (H _ _ H1 Hj')); intros.
  split.
   elim (RL_sub_hyp i (Nat.lt_le_incl _ _ H1)); intros.
   eapply leEq_wdl.
    2: apply eq_symmetric_unfolded; apply p.
   apply leEq_transitive with (Q j (Nat.lt_le_incl _ _ (H i j H1 Hj'))).
    apply Partition_mon; assumption.
   assumption.
  elim (RL_sub_hyp (S i) H1); intros.
  eapply leEq_wdr.
   2: apply eq_symmetric_unfolded; apply p.
  apply leEq_transitive with (Q _ (H i j H1 Hj')).
   assumption.
  apply Partition_mon.
  rewrite <- (Nat.lt_succ_pred _ _ (RL_sub_S i)); auto with arith.
 apply eq_imp_leEq; apply AbsIR_eq_x.
 apply shift_leEq_minus; astepl (Q j (Nat.lt_le_incl _ _ (H _ _ H1 Hj'))); apply prf2.
Qed.
(* end hide *)

Lemma first_refinement_lemma : AbsIR (Partition_Sum HfP incF[-]Partition_Sum HfQ incF) [<=] e[*] (b[-]a).
Proof.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply ref_calc2.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply ref_calc3.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply ref_calc4.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply ref_calc5.
 eapply leEq_transitive.
  apply ref_calc6.
 eapply leEq_transitive.
  apply ref_calc7.
 eapply leEq_transitive.
  apply ref_calc8.
 apply leEq_wdl with (e[*] Sumx (fun (i : nat) (Hi : i < n) => Sum2
   (fun (j : nat) (Hj : sub i <= j) (Hj' : j <= pred (sub (S i))) =>
     Q _ (H' _ _ Hi Hj') [-]Q _ (Nat.lt_le_incl _ _ (H _ _ Hi Hj'))))).
  apply mult_resp_leEq_lft.
   2: apply less_leEq; assumption.
  apply leEq_wdl with (Sumx (fun (i : nat) (Hi : i < n) => P _ Hi[-]P _ (Nat.lt_le_incl _ _ Hi))).
   2: apply Sumx_wd; intros.
   2: apply eq_symmetric_unfolded; apply ref_calc1.
  eapply leEq_wdl.
   2: apply eq_symmetric_unfolded; apply Mengolli_Sum with (f := fun (i : nat) (Hi : i <= n) => P i Hi).
    eapply leEq_transitive.
     apply leEq_AbsIR.
    eapply leEq_wdr.
     2: apply AbsIR_eq_x.
     2: apply shift_leEq_minus; astepl a; assumption.
    apply compact_elements with Hab; apply Partition_in_compact.
   red in |- *; intros; apply prf1; auto.
  intros; apply cg_minus_wd; apply prf1; auto.
 apply eq_symmetric_unfolded; eapply eq_transitive_unfolded.
  2: apply Sumx_comm_scal'.
 apply Sumx_wd; intros.
 eapply eq_transitive_unfolded.
  2: apply Sum2_comm_scal'.
  algebra.
 apply RL_sub_SS.
Qed.

End First_Refinement_Lemma.

Section Second_Refinement_Lemma.

(**
This is inequality (2.6.7).

%\begin{convention}%
 - [P, Q, R] are partitions of [I] with, respectively, [j, n] and [k] points;
 - [Q] is a common refinement of [P] and [R];
 - [e, e'] are positive real numbers;
 - [d, d'] are the moduli of continuity of [F] for [e, e'];
 - the Mesh of [P] is less or equal to [d];
 - the Mesh of [R] is less or equal to [d'];
 - [fP, fQ] and [fR] are choices of points respecting the partitions [P, Q]
and [R], respectively.

%\end{convention}%
*)

Variables n j k : nat.

Variable P : Partition Hab j.
Variable Q : Partition Hab n.
Variable R : Partition Hab k.

Hypothesis HrefP : Refinement P Q.
Hypothesis HrefR : Refinement R Q.

Variables e e' : IR.
Hypothesis He : [0] [<] e.
Hypothesis He' : [0] [<] e'.

(* begin hide *)
Let d := proj1_sig2T _ _ _ (contF' e He).
Let d' := proj1_sig2T _ _ _ (contF' e' He').
(* end hide *)

Hypothesis HMeshP : Mesh P [<=] d.
Hypothesis HMeshR : Mesh R [<=] d'.

Variable fP : forall i : nat, i < j -> IR.
Hypothesis HfP : Points_in_Partition P fP.
Hypothesis HfP' : nat_less_n_fun fP.

Variable fR : forall i : nat, i < k -> IR.
Hypothesis HfR : Points_in_Partition R fR.
Hypothesis HfR' : nat_less_n_fun fR.

Lemma second_refinement_lemma :
 AbsIR (Partition_Sum HfP incF[-]Partition_Sum HfR incF) [<=] e[*] (b[-]a) [+]e'[*] (b[-]a).
Proof.
 set (HfQ := Partition_imp_points_1 _ _ _ _ Q) in *.
 set (H' := Partition_imp_points_2 _ _ _ _ Q) in *.
 apply leEq_wdl with (AbsIR (Partition_Sum HfP incF[-]Partition_Sum HfQ incF[+]
   (Partition_Sum HfQ incF[-]Partition_Sum HfR incF))).
  2: apply AbsIR_wd; rational.
 eapply leEq_transitive.
  apply triangle_IR.
 apply plus_resp_leEq_both.
  apply first_refinement_lemma with He; assumption.
 eapply leEq_wdl.
  2: apply AbsIR_minus.
 apply first_refinement_lemma with He'; assumption.
Qed.

End Second_Refinement_Lemma.

Section Third_Refinement_Lemma.

(**
This is an approximation of inequality (2.6.7), but without assuming the existence of a common refinement of [P] and [R].

%\begin{convention}%
 - [P, R] are partitions of [I] with, respectively, [n] and [m] points;
 - [e, e'] are positive real numbers;
 - [d, d'] are the moduli of continuity of [F] for [e, e'];
 - the Mesh of [P] is less than [d];
 - the Mesh of [R] is less than [d'];
 - [fP] and [fR] are choices of points respecting the partitions [P] and [R],
respectively;
 - [beta] is a positive real number.

%\end{convention}%
*)

Variables n m : nat.

Variable P : Partition Hab n.
Variable R : Partition Hab m.

Variables e e' : IR.
Hypothesis He : [0] [<] e.
Hypothesis He' : [0] [<] e'.

(* begin hide *)
Let d := proj1_sig2T _ _ _ (contF' e He).
Let d' := proj1_sig2T _ _ _ (contF' e' He').
(* end hide *)

Hypothesis HMeshP : Mesh P [<] d.
Hypothesis HMeshR : Mesh R [<] d'.

Variable fP : forall i : nat, i < n -> IR.
Hypothesis HfP : Points_in_Partition P fP.
Hypothesis HfP' : nat_less_n_fun fP.

Variable fR : forall i : nat, i < m -> IR.
Hypothesis HfR : Points_in_Partition R fR.
Hypothesis HfR' : nat_less_n_fun fR.

Hypothesis Hab' : a [<] b.

Variable beta : IR.
Hypothesis Hbeta : [0] [<] beta.

(* begin hide *)
Let alpha := beta [/]ThreeNZ.

Lemma RL_alpha : [0] [<] alpha.
Proof.
 unfold alpha in |- *; apply pos_div_three; assumption.
Qed.

Let csi1 := Min (b[-]a) ((d[-]Mesh P) [/]TwoNZ).

Lemma RL_csi1 : [0] [<] csi1.
Proof.
 unfold csi1 in |- *; apply less_Min.
  apply shift_less_minus; astepl a; assumption.
 apply pos_div_two.
 apply shift_less_minus.
 astepl (Mesh P); assumption.
Qed.

Let delta1 :=
  Min csi1
    (alpha[/] _[//]
     mult_resp_ap_zero IR _ _ (nring_ap_zero _ n (SPap_n _ _ _ Hab' _ P))
       (max_one_ap_zero (Norm_Funct contF))).

Lemma RL_delta1 : delta1 [/]TwoNZ [<] b[-]a.
Proof.
 apply shift_div_less'.
  apply pos_two.
 apply leEq_less_trans with (b[-]a).
  unfold delta1 in |- *; clear delta1.
  apply leEq_transitive with csi1.
   apply Min_leEq_lft.
  unfold csi1 in |- *.
  apply Min_leEq_lft.
 astepl ([0][+] (b[-]a)); rstepr (b[-]a[+] (b[-]a)).
 apply plus_resp_less_rht.
 apply shift_less_minus; astepl a; assumption.
Qed.

Let P' := sep__part _ _ _ F contF Hab' _ P _ RL_alpha _ RL_csi1 RL_delta1.

Lemma RL_P'_sep : _Separated P'.
Proof.
 red in |- *; intros.
 unfold P' in |- *; apply sep__part_mon.
Qed.

Lemma RL_P'_Mesh : Mesh P' [<] d.
Proof.
 unfold P' in |- *.
 eapply leEq_less_trans.
  apply sep__part_mon_Mesh.
 unfold csi1 in |- *.
 apply shift_plus_less'; eapply leEq_less_trans.
  apply Min_leEq_rht.
 apply pos_div_two'.
 apply shift_less_minus.
 astepl (Mesh P); assumption.
Qed.

Let fP' := sep__part_pts _ _ _ F contF Hab' _ P _ RL_alpha _ RL_csi1 fP.

Lemma RL_fP'_in_P' : Points_in_Partition P' fP'.
Proof.
 unfold fP', P' in |- *; apply sep__part_pts_in_Partition.
 assumption.
Qed.

Lemma RL_P'_P_sum :
  AbsIR (Partition_Sum HfP incF[-]Partition_Sum RL_fP'_in_P' incF) [<=] alpha.
Proof.
 apply leEq_wdl with (AbsIR (Partition_Sum HfP incF[-] Partition_Sum
   (sep__part_pts_in_Partition _ _ _ F contF Hab' _ P _ RL_alpha _ RL_csi1 RL_delta1 _ HfP) incF)).
  apply sep__part_Sum.
  assumption.
 apply AbsIR_wd; apply cg_minus_wd.
  algebra.
 unfold Partition_Sum in |- *; apply Sumx_wd; intros.
 algebra.
Qed.

Let csi2 := Min (b[-]a) ((d'[-]Mesh R) [/]TwoNZ).

Lemma RL_csi2 : [0] [<] csi2.
Proof.
 unfold csi2 in |- *; apply less_Min.
  apply shift_less_minus; astepl a; assumption.
 apply pos_div_two.
 apply shift_less_minus.
 astepl (Mesh R); assumption.
Qed.

Let delta2 :=
  Min csi2
    (alpha[/] _[//]
     mult_resp_ap_zero IR _ _ (nring_ap_zero _ m (SPap_n _ _ _ Hab' _ R))
       (max_one_ap_zero (Norm_Funct contF))).

Lemma RL_delta2 : delta2 [/]TwoNZ [<] b[-]a.
Proof.
 apply shift_div_less'.
  apply pos_two.
 apply leEq_less_trans with (b[-]a).
  unfold delta2 in |- *; clear delta2.
  apply leEq_transitive with csi2.
   apply Min_leEq_lft.
  unfold csi2 in |- *.
  apply Min_leEq_lft.
 astepl ([0][+] (b[-]a)); rstepr (b[-]a[+] (b[-]a)).
 apply plus_resp_less_rht.
 apply shift_less_minus; astepl a; assumption.
Qed.

Let R' := sep__part _ _ _ F contF Hab' _ R _ RL_alpha _ RL_csi2 RL_delta2.

Lemma RL_R'_sep : _Separated R'.
Proof.
 red in |- *; intros.
 unfold R' in |- *; apply sep__part_mon.
Qed.

Lemma RL_R'_Mesh : Mesh R' [<] d'.
Proof.
 unfold R' in |- *.
 eapply leEq_less_trans.
  apply sep__part_mon_Mesh.
 unfold csi2 in |- *.
 apply shift_plus_less'; eapply leEq_less_trans.
  apply Min_leEq_rht.
 apply pos_div_two'.
 apply shift_less_minus.
 astepl (Mesh R); assumption.
Qed.

Let fR' := sep__part_pts _ _ _ F contF Hab' _ R _ RL_alpha _ RL_csi2 fR.

Lemma RL_fR'_in_R' : Points_in_Partition R' fR'.
Proof.
 unfold fR', R' in |- *; apply sep__part_pts_in_Partition.
 assumption.
Qed.

Lemma RL_R'_R_sum :
  AbsIR (Partition_Sum HfR incF[-]Partition_Sum RL_fR'_in_R' incF) [<=] alpha.
Proof.
 apply leEq_wdl with (AbsIR (Partition_Sum HfR incF[-] Partition_Sum
   (sep__part_pts_in_Partition _ _ _ F contF Hab' _ R _ RL_alpha _ RL_csi2 RL_delta2 _ HfR) incF)).
  apply sep__part_Sum.
  assumption.
 apply AbsIR_wd; apply cg_minus_wd.
  algebra.
 unfold Partition_Sum in |- *; apply Sumx_wd; intros.
 algebra.
Qed.

Let csi3 := d[-]Mesh P'.

Lemma RL_csi3 : [0] [<] csi3.
Proof.
 unfold csi3 in |- *.
 apply shift_less_minus; astepl (Mesh P').
 apply RL_P'_Mesh.
Qed.

Let Q :=
  sep__sep_part _ _ _ F contF Hab' _ _ _ _ RL_P'_sep RL_R'_sep _ RL_alpha _ RL_csi3.

Lemma RL_Q_Mesh : Mesh Q [<=] d.
Proof.
 unfold Q in |- *; eapply leEq_wdr.
  apply sep__sep_Mesh.
 unfold csi3 in |- *; rational.
Qed.

Lemma RL_Q_sep : Separated Q R'.
Proof.
 unfold Q in |- *; apply sep__sep_lemma.
Qed.

Let fQ :=
  sep__sep_points _ _ _ F contF Hab' _ _ _ _ RL_P'_sep RL_R'_sep _ RL_alpha _ RL_csi3
    fP'.

Lemma RL_fQ_in_Q : Points_in_Partition Q fQ.
Proof.
 unfold Q, fQ in |- *; apply sep__sep_points_lemma.
 apply RL_fP'_in_P'.
Qed.

Lemma RL_Q_P'_sum :
  AbsIR (Partition_Sum RL_fP'_in_P' incF[-]Partition_Sum RL_fQ_in_Q incF) [<=] alpha.
Proof.
 apply leEq_wdl with (AbsIR (Partition_Sum RL_fP'_in_P' incF[-] Partition_Sum
   (sep__sep_points_lemma _ _ _ F contF Hab' _ _ _ _ RL_P'_sep RL_R'_sep _
     RL_alpha _ RL_csi3 _ RL_fP'_in_P') incF)).
  unfold Q, fQ in |- *; apply sep__sep_Sum.
 apply AbsIR_wd.
 unfold Partition_Sum in |- *; apply cg_minus_wd.
  algebra.
 apply Sumx_wd; intros.
 algebra.
Qed.
(* end hide *)

Lemma third_refinement_lemma :
 AbsIR (Partition_Sum HfP incF[-]Partition_Sum HfR incF) [<=] e[*] (b[-]a) [+]e'[*] (b[-]a) [+]beta.
Proof.
 apply leEq_wdl with (AbsIR (Partition_Sum HfP incF[-]Partition_Sum RL_fP'_in_P' incF[+]
   (Partition_Sum RL_fP'_in_P' incF[-]Partition_Sum RL_fQ_in_Q incF) [+]
     (Partition_Sum RL_fQ_in_Q incF[-]Partition_Sum RL_fR'_in_R' incF) [+]
       (Partition_Sum RL_fR'_in_R' incF[-]Partition_Sum HfR incF))).
  apply leEq_wdr with (alpha[+]alpha[+] (e[*] (b[-]a) [+]e'[*] (b[-]a)) [+]alpha).
   2: unfold alpha in |- *; rational.
  eapply leEq_transitive.
   apply triangle_IR.
  apply plus_resp_leEq_both.
   eapply leEq_transitive.
    apply triangle_IR.
   apply plus_resp_leEq_both.
    eapply leEq_transitive.
     apply triangle_IR.
    apply plus_resp_leEq_both.
     apply RL_P'_P_sum.
    apply RL_Q_P'_sum.
   2: eapply leEq_wdl.
    3: apply AbsIR_minus.
   2: apply RL_R'_R_sum.
  2: apply AbsIR_wd; rational.
 eapply second_refinement_lemma with (Q := Separated_Refinement _ _ _ _ _ _ _ RL_Q_sep) (He := He)
   (He' := He').
    apply Separated_Refinement_lft.
   apply Separated_Refinement_rht.
  apply RL_Q_Mesh.
 apply less_leEq; apply RL_R'_Mesh.
Qed.

End Third_Refinement_Lemma.

Section Fourth_Refinement_Lemma.

(* begin hide *)
Let Fa := Part F a (incF _ (compact_inc_lft a b Hab)).

Notation just := (fun z => incF _ (Pts_part_lemma _ _ _ _ _ _ z _ _)).

Lemma RL_sum_lemma_aux :
  forall (n : nat) (P : Partition Hab n) fP (HfP : Points_in_Partition P fP),
  Partition_Sum HfP incF [=]
  Fa[*] (b[-]a) [-]
  Sumx
    (fun (i : nat) (Hi : i < n) =>
     (Fa[-]Part F (fP i Hi) (just HfP)) [*] (P _ Hi[-]P _ (Nat.lt_le_incl _ _ Hi))).
Proof.
 intros; apply eq_transitive_unfolded with (Sumx (fun (i : nat) (Hi : i < n) =>
   Fa[*] (P _ Hi[-]P _ (Nat.lt_le_incl _ _ Hi))) [-] Sumx (fun (i : nat) (Hi : i < n) =>
     (Fa[-]Part F (fP i Hi) (just HfP)) [*] (P _ Hi[-]P _ (Nat.lt_le_incl _ _ Hi)))).
  eapply eq_transitive_unfolded.
   2: apply eq_symmetric_unfolded; apply Sumx_minus_Sumx.
  unfold Partition_Sum in |- *; apply Sumx_wd; intros.
  eapply eq_transitive_unfolded.
   2: apply ring_distl_minus.
  apply mult_wdl.
  rstepr (Part F (fP i H) (just HfP)); algebra.
 apply cg_minus_wd.
  2: algebra.
 astepr (Fa[*]b[-]Fa[*]a).
 eapply eq_transitive_unfolded.
  apply Mengolli_Sum with (f := fun (i : nat) (Hi : i <= n) => Fa[*]P i Hi).
   red in |- *; intros.
   apply mult_wdr.
   apply prf1; auto.
  intros; algebra.
 apply cg_minus_wd; apply mult_wdr.
  apply finish.
 apply start.
Qed.
(* end hide *)

(**
Finally, this is inequality (2.6.7) exactly as stated (same conventions as
above)
*)

Variables n m : nat.

Variable P : Partition Hab n.
Variable R : Partition Hab m.

Variables e e' : IR.
Hypothesis He : [0] [<] e.
Hypothesis He' : [0] [<] e'.

(* begin hide *)
Let d := proj1_sig2T _ _ _ (contF' e He).
Let d' := proj1_sig2T _ _ _ (contF' e' He').
(* end hide *)

Hypothesis HMeshP : Mesh P [<] d.
Hypothesis HMeshR : Mesh R [<] d'.

Variable fP : forall i : nat, i < n -> IR.
Hypothesis HfP : Points_in_Partition P fP.
Hypothesis HfP' : nat_less_n_fun fP.

Variable fR : forall i : nat, i < m -> IR.
Hypothesis HfR : Points_in_Partition R fR.
Hypothesis HfR' : nat_less_n_fun fR.

(* begin show *)
Hypothesis Hab' : b[-]a [<] Min d d'.
(* end show *)

Lemma fourth_refinement_lemma :
 AbsIR (Partition_Sum HfP incF[-]Partition_Sum HfR incF) [<=] e[*] (b[-]a) [+]e'[*] (b[-]a).
Proof.
 generalize (proj2b_sig2T _ _ _ (contF' e He));
   generalize (proj2a_sig2T _ _ _ (contF' e He)); fold d in |- *; intros Hd Hdd.
 generalize (proj2b_sig2T _ _ _ (contF' e' He'));
   generalize (proj2a_sig2T _ _ _ (contF' e' He')); fold d' in |- *; intros Hd' Hdd'.
 apply leEq_wdl with (AbsIR (Fa[*] (b[-]a) [-] Sumx (fun (i : nat) (Hi : i < n) =>
   (Fa[-]Part F (fP i Hi) (just HfP)) [*] (P _ Hi[-]P _ (Nat.lt_le_incl _ _ Hi))) [-] (Fa[*] (b[-]a) [-]
     Sumx (fun (j : nat) (Hj : j < m) => (Fa[-]Part F (fR j Hj) (just HfR)) [*]
       (R _ Hj[-]R _ (Nat.lt_le_incl _ _ Hj)))))).
  2: apply AbsIR_wd; apply eq_symmetric_unfolded.
  2: apply cg_minus_wd; apply RL_sum_lemma_aux.
 apply leEq_wdl with (AbsIR (Sumx (fun (j : nat) (Hj : j < m) =>
   (Fa[-]Part F (fR j Hj) (just HfR)) [*] (R _ Hj[-]R _ (Nat.lt_le_incl _ _ Hj))) [-] Sumx
     (fun (i : nat) (Hi : i < n) => (Fa[-]Part F (fP i Hi) (just HfP)) [*]
       (P _ Hi[-]P _ (Nat.lt_le_incl _ _ Hi))))).
  2: apply AbsIR_wd; rational.
 rstepr (e'[*] (b[-]a) [+]e[*] (b[-]a)).
 eapply leEq_transitive.
  apply triangle_IR_minus.
 apply plus_resp_leEq_both.
  eapply leEq_transitive.
   apply triangle_SumxIR.
  apply leEq_wdr with (Sumx (fun (i : nat) (Hi : i < m) => e'[*] (R _ Hi[-]R _ (Nat.lt_le_incl _ _ Hi)))).
   apply Sumx_resp_leEq; intros.
   eapply leEq_wdl.
    2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
   apply mult_resp_leEq_both; try apply AbsIR_nonneg.
    unfold Fa in |- *; apply Hdd'; unfold I in |- *.
      apply compact_inc_lft.
     apply Pts_part_lemma with m R; assumption.
    apply leEq_transitive with (AbsIR (b[-]a)).
     apply compact_elements with Hab.
      apply compact_inc_lft.
     apply Pts_part_lemma with m R; assumption.
    eapply leEq_wdl.
     2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
     2: apply shift_leEq_minus; astepl a; assumption.
    eapply leEq_transitive.
     apply less_leEq; apply Hab'.
    apply Min_leEq_rht.
   apply eq_imp_leEq; apply AbsIR_eq_x.
   apply shift_leEq_minus; astepl (R i (Nat.lt_le_incl _ _ H)); apply prf2.
  eapply eq_transitive_unfolded.
   apply Sumx_comm_scal' with (f := fun (i : nat) (Hi : i < m) => R _ Hi[-]R _ (Nat.lt_le_incl _ _ Hi)).
  apply mult_wdr.
  eapply eq_transitive_unfolded.
   apply Mengolli_Sum with (f := fun (i : nat) (Hi : i <= m) => R i Hi).
    red in |- *; intros.
    apply prf1; auto.
   intros; algebra.
  apply cg_minus_wd; [ apply finish | apply start ].
 eapply leEq_transitive.
  apply triangle_SumxIR.
 apply leEq_wdr with (Sumx (fun (i : nat) (Hi : i < n) => e[*] (P _ Hi[-]P _ (Nat.lt_le_incl _ _ Hi)))).
  apply Sumx_resp_leEq; intros.
  eapply leEq_wdl.
   2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
  apply mult_resp_leEq_both; try apply AbsIR_nonneg.
   unfold Fa in |- *; apply Hdd; unfold I in |- *.
     apply compact_inc_lft.
    apply Pts_part_lemma with n P; assumption.
   apply leEq_transitive with (AbsIR (b[-]a)).
    apply compact_elements with Hab.
     apply compact_inc_lft.
    apply Pts_part_lemma with n P; assumption.
   eapply leEq_wdl.
    2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
    2: apply shift_leEq_minus; astepl a; assumption.
   eapply leEq_transitive.
    apply less_leEq; apply Hab'.
   apply Min_leEq_lft.
  apply eq_imp_leEq; apply AbsIR_eq_x.
  apply shift_leEq_minus; astepl (P i (Nat.lt_le_incl _ _ H)); apply prf2.
 eapply eq_transitive_unfolded.
  apply Sumx_comm_scal' with (f := fun (i : nat) (Hi : i < n) => P _ Hi[-]P _ (Nat.lt_le_incl _ _ Hi)).
 apply mult_wdr.
 eapply eq_transitive_unfolded.
  apply Mengolli_Sum with (f := fun (i : nat) (Hi : i <= n) => P i Hi).
   red in |- *; intros.
   apply prf1; auto.
  intros; algebra.
 apply cg_minus_wd; [ apply finish | apply start ].
Qed.

End Fourth_Refinement_Lemma.

Section Main_Refinement_Lemma.

(** We finish by presenting Theorem 9. *)

Variables n m : nat.

Variable P : Partition Hab n.
Variable R : Partition Hab m.

Variables e e' : IR.
Hypothesis He : [0] [<] e.
Hypothesis He' : [0] [<] e'.

(* begin hide *)
Let d := proj1_sig2T _ _ _ (contF' e He).
Let d' := proj1_sig2T _ _ _ (contF' e' He').
(* end hide *)

Hypothesis HMeshP : Mesh P [<] d.
Hypothesis HMeshR : Mesh R [<] d'.

Variable fP : forall i : nat, i < n -> IR.
Hypothesis HfP : Points_in_Partition P fP.
Hypothesis HfP' : nat_less_n_fun fP.

Variable fR : forall i : nat, i < m -> IR.
Hypothesis HfR : Points_in_Partition R fR.
Hypothesis HfR' : nat_less_n_fun fR.

Lemma refinement_lemma : AbsIR (Partition_Sum HfP incF[-]Partition_Sum HfR incF) [<=] e[*] (b[-]a) [+]e'[*] (b[-]a).
Proof.
 cut ([0] [<] Min d d').
  intro H; elim (less_cotransitive_unfolded _ _ _ H (b[-]a)); intro.
   astepr (e[*] (b[-]a) [+]e'[*] (b[-]a) [+][0]).
   apply shift_leEq_plus'.
   apply approach_zero_weak.
   intros beta Hbeta.
   apply shift_minus_leEq.
   astepr (e[*] (b[-]a) [+]e'[*] (b[-]a) [+]beta).
   apply third_refinement_lemma with (He := He) (He' := He'); try assumption.
   astepl ([0][+]a); apply shift_plus_less; assumption.
  apply fourth_refinement_lemma with He He'.
  assumption.
 apply less_Min.
  unfold d in |- *; apply proj2a_sig2T.
 unfold d' in |- *; apply proj2a_sig2T.
Qed.

End Main_Refinement_Lemma.

End Refinement_Lemma.
