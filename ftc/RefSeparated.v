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

(* begin hide *)

Require Export CoRN.ftc.COrdLemmas.
Require Export CoRN.ftc.Partitions.

Section Separating__Separated.

Variables a b : IR.
Hypothesis Hab : a[<=]b.
Let I := compact a b Hab.

Variable F : PartIR.
Hypothesis contF : Continuous_I Hab F.
Hypothesis incF : included (Compact Hab) (Dom F).

Hypothesis Hab' : a[<]b.
Variables m n : nat.
Variable P : Partition Hab n.
Variable R : Partition Hab m.

Hypothesis HP : _Separated P.
Hypothesis HR : _Separated R.

Lemma RS_pos_n : 0 < n.
Proof.
 apply partition_less_imp_gt_zero with a b Hab; assumption.
Qed.

Lemma RS_pos_m : 0 < m.
Proof.
 apply partition_less_imp_gt_zero with a b Hab; assumption.
Qed.

Variable alpha : IR.
Hypothesis Halpha : [0][<]alpha.

Let e := alpha [/]TwoNZ[/] _[//]max_one_ap_zero (b[-]a).

Lemma RS_He : [0][<]e.
Proof.
 unfold e in |- *; apply div_resp_pos.
  apply pos_max_one.
 apply pos_div_two; assumption.
Qed.

Let contF' := contin_prop _ _ _ _ contF.

Let d : IR.
Proof.
 elim (contF' e RS_He).
 intros; apply x.
Defined.

Lemma RS_Hd : [0][<]d.
Proof.
 unfold d in |- *; elim (contF' e RS_He); auto.
Qed.

Lemma RS_Hd' :
  forall x y : IR,
  I x ->
  I y -> forall Hx Hy, AbsIR (x[-]y)[<=]d -> AbsIR (F x Hx[-]F y Hy)[<=]e.
Proof.
 unfold d in |- *; elim (contF' e RS_He); auto.
Qed.

Variable csi : IR.
Hypothesis Hcsi : [0][<]csi.

Let M := Norm_Funct contF.

Let deltaP := AntiMesh P.
Let deltaR := AntiMesh R.
Let delta :=
  Min (Min deltaP deltaR)
    (Min (alpha [/]TwoNZ[/] _[//]max_one_ap_zero (nring n[*]M)) (Min csi d)).

Lemma RS_delta_deltaP : delta[<=]deltaP.
Proof.
 unfold delta in |- *; eapply leEq_transitive.
  apply Min_leEq_lft.
 apply Min_leEq_lft.
Qed.

Lemma RS_delta_deltaR : delta[<=]deltaR.
Proof.
 unfold delta in |- *; eapply leEq_transitive.
  apply Min_leEq_lft.
 apply Min_leEq_rht.
Qed.

Lemma RS_delta_csi : delta[<=]csi.
Proof.
 unfold delta in |- *; eapply leEq_transitive.
  apply Min_leEq_rht.
 eapply leEq_transitive.
  apply Min_leEq_rht.
 apply Min_leEq_lft.
Qed.

Lemma RS_delta_d : delta[<=]d.
Proof.
 unfold delta in |- *; eapply leEq_transitive.
  apply Min_leEq_rht.
 eapply leEq_transitive; apply Min_leEq_rht.
Qed.

Lemma RS_delta_pos : [0][<]delta.
Proof.
 unfold delta in |- *; apply less_Min; apply less_Min.
    unfold deltaP in |- *; apply pos_AntiMesh; [ apply RS_pos_n | assumption ].
   unfold deltaR in |- *; apply pos_AntiMesh; [ apply RS_pos_m | assumption ].
  apply div_resp_pos.
   apply pos_max_one.
  apply pos_div_two; assumption.
 apply less_Min.
  assumption.
 apply RS_Hd.
Qed.

Section Defining_ai'.

Variable i : nat.
Hypothesis Hi : i <= n.

Lemma separation_conseq :
  forall (j : nat) (Hj : j <= m),
  AbsIR (P i Hi[-]R j Hj)[<]delta [/]TwoNZ ->
  forall j' : nat,
  j <> j' -> forall Hj' : j' <= m, delta [/]TwoNZ[<]AbsIR (P i Hi[-]R j' Hj').
Proof.
 intros j Hj H; intros.
 elim (Cnat_total_order _ _ H0); clear H0; intro H0.
  elim (le_lt_dec j' m); intro.
   cut (S j <= m); [ intro | clear H; apply Nat.le_trans with j'; auto ].
   eapply less_wdr.
    2: apply AbsIR_minus.
   cut (R (S j) H1[<=]R j' Hj'); intros.
    eapply less_wdr.
     2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
     rstepr (R _ Hj'[-]R _ H1[+](R _ H1[-]R _ Hj)[+](R _ Hj[-]P i Hi)).
     rstepl ([0][+]delta[+][--](delta [/]TwoNZ)).
     apply plus_resp_leEq_less.
      apply plus_resp_leEq_both.
       apply shift_leEq_minus; astepl (R _ H1).
       assumption.
      apply leEq_transitive with deltaR.
       apply RS_delta_deltaR.
      unfold deltaR in |- *; apply AntiMesh_lemma.
     rstepl ([--](delta [/]TwoNZ)).
     rstepr ([--](P i Hi[-]R j Hj)).
     apply inv_resp_less.
     eapply leEq_less_trans.
      apply leEq_AbsIR.
     assumption.
    apply shift_leEq_minus; astepl (P i Hi).
    eapply leEq_transitive.
     2: apply H2.
    apply less_leEq; apply less_transitive_unfolded with (R j Hj[+]delta [/]TwoNZ).
     apply shift_less_plus'.
     eapply leEq_less_trans; [ apply leEq_AbsIR | apply H ].
    apply shift_plus_less'.
    apply less_leEq_trans with delta.
     apply pos_div_two'; exact RS_delta_pos.
    apply leEq_transitive with deltaR.
     apply RS_delta_deltaR.
    unfold deltaR in |- *; apply AntiMesh_lemma.
   apply local_mon_imp_mon'_le with (f := fun (i : nat) (Hi : i <= m) => R i Hi).
     intros; apply HR.
    red in |- *; intros; apply prf1; auto.
   assumption.
  exfalso; apply (le_not_lt j' m); auto.
 elim (le_lt_dec j 0); intro.
  exfalso; apply lt_n_O with j'; red in |- *; apply Nat.le_trans with j; auto.
 generalize Hj H H0; clear H0 H Hj.
 set (jj := pred j) in *.
 cut (j = S jj); [ intro | unfold jj in |- *; apply S_pred with 0; auto ].
 rewrite H; intros.
 cut (jj <= m); [ intro | auto with arith ].
 cut (R j' Hj'[<=]R jj H2); intros.
  eapply less_wdr.
   2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
   rstepr (P i Hi[-]R _ Hj[+](R _ Hj[-]R jj H2)[+](R jj H2[-]R j' Hj')).
   rstepl ([--](delta [/]TwoNZ)[+]delta[+][0]).
   apply plus_resp_less_leEq.
    apply plus_resp_less_leEq.
     eapply less_wdr.
      2: apply cg_inv_inv.
     apply inv_resp_less; eapply leEq_less_trans.
      2: apply H0.
     apply inv_leEq_AbsIR.
    eapply leEq_transitive.
     apply RS_delta_deltaR.
    unfold deltaR in |- *; apply AntiMesh_lemma.
   apply shift_leEq_minus; eapply leEq_wdl.
    apply H3.
   algebra.
  apply shift_leEq_minus; astepl (R j' Hj').
  eapply leEq_transitive.
   apply H3.
  apply less_leEq; apply less_transitive_unfolded with (R _ Hj[-]delta [/]TwoNZ).
   apply shift_less_minus; apply shift_plus_less'.
   apply less_leEq_trans with delta.
    apply pos_div_two'; exact RS_delta_pos.
   eapply leEq_transitive.
    apply RS_delta_deltaR.
   unfold deltaR in |- *; apply AntiMesh_lemma.
  apply shift_minus_less; apply shift_less_plus'.
  eapply leEq_less_trans.
   2: apply H0.
  eapply leEq_wdr.
   2: apply AbsIR_minus.
  apply leEq_AbsIR.
 apply local_mon_imp_mon'_le with (f := fun (i : nat) (Hi : i <= m) => R i Hi).
   intros; apply HR.
  red in |- *; intros; apply prf1; auto.
 auto with arith.
Qed.

Let pred1 (j : nat) (Hj : j <= m) :=
  forall Hi' : i <= n, AbsIR (P i Hi'[-]R j Hj)[<]delta [/]TwoNZ.
Let pred2 (j : nat) (Hj : j <= m) :=
  forall Hi' : i <= n, delta [/]FourNZ[<]AbsIR (P i Hi'[-]R j Hj).

Lemma sep__sep_aux_lemma :
 {j : nat | {Hj : j <= m | pred1 j Hj}}
 or (forall (j : nat) (Hj : j <= m), pred2 j Hj).
Proof.
 apply finite_or_elim.
   red in |- *; unfold pred1 in |- *; do 3 intro.
   rewrite H; intros H0 H' H1 Hi'.
   eapply less_wdl.
    apply H1 with (Hi' := Hi').
   apply AbsIR_wd; apply cg_minus_wd; apply prf1; auto.
  red in |- *; unfold pred2 in |- *; intros. rename X into H1.
  eapply less_wdr.
   apply H1 with (Hi' := Hi').
  apply AbsIR_wd; apply cg_minus_wd; apply prf1; auto.
 intros j Hj.
 cut (pred2 j Hj or pred1 j Hj).
  intro H; inversion_clear H; [ right | left ]; assumption.
 unfold pred1, pred2 in |- *.
 cut (forall Hi' : i <= n, delta [/]FourNZ[<]AbsIR (P i Hi'[-]R j Hj)
   or AbsIR (P i Hi'[-]R j Hj)[<]delta [/]TwoNZ). intro H.
  elim (le_lt_dec i n); intro.
   elim (H a0); intro.
    left; intro.
    eapply less_wdr.
     apply a1.
    apply AbsIR_wd; apply cg_minus_wd; apply prf1; auto.
   right; intro.
   eapply less_wdl.
    apply b0.
   apply AbsIR_wd; apply cg_minus_wd; apply prf1; auto.
  left; intro.
  exfalso; apply le_not_lt with i n; auto.
 intros.
 apply less_cotransitive_unfolded.
 rstepl ((delta [/]TwoNZ) [/]TwoNZ).
 apply pos_div_two'; apply pos_div_two; apply RS_delta_pos.
Qed.

Hypothesis Hi0 : 0 < i.
Hypothesis Hin : i < n.

Definition sep__sep_fun_i : IR.
Proof.
 elim sep__sep_aux_lemma; intros.
  2: apply (P i Hi).
 apply (P i Hi[+]delta [/]TwoNZ).
Defined.

Lemma sep__sep_leEq : forall Hi' : i <= n, P i Hi'[<=]sep__sep_fun_i.
Proof.
 unfold sep__sep_fun_i in |- *.
 elim sep__sep_aux_lemma; intros; simpl in |- *.
  2: apply eq_imp_leEq; apply prf1; auto.
 apply leEq_wdl with (P i Hi).
  2: apply prf1; auto.
 apply shift_leEq_plus'; astepl ZeroR.
 astepr (delta [/]TwoNZ).
 apply less_leEq; apply pos_div_two; exact RS_delta_pos.
Qed.

Lemma sep__sep_less : forall Hi' : S i <= n, sep__sep_fun_i[<]P (S i) Hi'.
Proof.
 unfold sep__sep_fun_i in |- *.
 elim sep__sep_aux_lemma; intros; simpl in |- *.
  2: apply HP.
 apply shift_plus_less'.
 apply less_leEq_trans with delta.
  astepl (delta [/]TwoNZ).
  apply pos_div_two'; exact RS_delta_pos.
 apply leEq_transitive with deltaP.
  apply RS_delta_deltaP.
 unfold deltaP in |- *; apply AntiMesh_lemma.
Qed.

Lemma sep__sep_ap : forall (j : nat) (Hj : j <= m), sep__sep_fun_i[#]R j Hj.
Proof.
 intros.
 unfold sep__sep_fun_i in |- *; elim sep__sep_aux_lemma; intro; simpl in |- *.
  2: apply zero_minus_apart; apply AbsIR_cancel_ap_zero; apply Greater_imp_ap.
  elim a0; intros j' H.
  elim H; clear a0 H; intros Hj' H.
  unfold pred1 in H.
  rstepr (P i Hi[+](R j Hj[-]P i Hi)).
  apply op_lft_resp_ap.
  apply un_op_strext_unfolded with AbsIR.
  apply ap_wdl_unfolded with (delta [/]TwoNZ).
   2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
   2: apply less_leEq; apply pos_div_two; exact RS_delta_pos.
  eapply ap_wdr_unfolded.
   2: apply AbsIR_minus.
  elim (le_lt_dec j j'); intro.
   elim (le_lt_eq_dec _ _ a0); clear a0; intro.
    apply less_imp_ap; apply separation_conseq with j' Hj'.
     apply H.
    intro; rewrite H0 in a0; apply (lt_irrefl _ a0).
   apply Greater_imp_ap.
   eapply less_wdl.
    apply H with (Hi' := Hi).
   apply AbsIR_wd.
   apply cg_minus_wd.
    algebra.
   apply prf1; auto.
  apply less_imp_ap; apply separation_conseq with j' Hj'.
   apply H.
  intro; rewrite H0 in b0; apply (lt_irrefl _ b0).
 unfold pred2 in b0.
 eapply less_transitive_unfolded.
  2: apply b0.
 apply pos_div_four; exact RS_delta_pos.
Qed.

End Defining_ai'.

Definition sep__sep_fun : forall i : nat, i <= n -> IR.
Proof.
 intros.
 elim (le_lt_dec i 0); intro.
  apply a.
 elim (le_lt_eq_dec _ _ H); intro.
  apply (sep__sep_fun_i i H).
 apply b.
Defined.

Lemma sep__sep_fun_i_delta :
 forall (i : nat) (Hi Hi' : i <= n) (Hi0 : i < n),
 AbsIR (sep__sep_fun_i i Hi[-]P i Hi')[<=]delta [/]TwoNZ.
Proof.
 intros.
 unfold sep__sep_fun_i in |- *.
 elim (sep__sep_aux_lemma i); intro; simpl in |- *.
  apply eq_imp_leEq.
  eapply eq_transitive_unfolded.
   2: apply AbsIR_eq_x.
   apply AbsIR_wd.
   rstepr (P i Hi'[+]delta [/]TwoNZ[-]P i Hi').
   apply cg_minus_wd.
    apply bin_op_wd_unfolded.
     apply prf1; auto.
    algebra.
   algebra.
  astepr (delta [/]TwoNZ); apply less_leEq; apply pos_div_two; exact RS_delta_pos.
 apply leEq_wdl with ZeroR.
  astepr (delta [/]TwoNZ); apply less_leEq; apply pos_div_two; exact RS_delta_pos.
 eapply eq_transitive_unfolded.
  apply eq_symmetric_unfolded; apply AbsIRz_isz.
 apply AbsIR_wd.
 astepl (P i Hi[-]P i Hi).
 apply cg_minus_wd; apply prf1; auto.
Qed.

Lemma sep__sep_fun_delta :
 forall (i : nat) (Hi Hi' : i <= n),
 AbsIR (sep__sep_fun i Hi[-]P i Hi')[<=]delta [/]TwoNZ.
Proof.
 intros.
 unfold sep__sep_fun in |- *.
 elim (le_lt_dec i 0); intro; simpl in |- *.
  cut (i = 0); [ intro | auto with arith ].
  generalize Hi'; rewrite H; intros.
  apply leEq_wdl with ZeroR.
   astepr (delta [/]TwoNZ); apply less_leEq; apply pos_div_two; exact RS_delta_pos.
  eapply eq_transitive_unfolded.
   apply eq_symmetric_unfolded; apply AbsIRz_isz.
  apply AbsIR_wd.
  astepl (a[-]a).
  apply cg_minus_wd; [ algebra | apply eq_symmetric_unfolded; apply start ].
 elim (le_lt_eq_dec _ _ Hi); intro; simpl in |- *.
  apply sep__sep_fun_i_delta; assumption.
 generalize Hi'; rewrite b1; intros.
 apply leEq_wdl with ZeroR.
  astepr (delta [/]TwoNZ); apply less_leEq; apply pos_div_two; exact RS_delta_pos.
 eapply eq_transitive_unfolded.
  apply eq_symmetric_unfolded; apply AbsIRz_isz.
 apply AbsIR_wd.
 astepl (b[-]b).
 apply cg_minus_wd; [ algebra | apply eq_symmetric_unfolded; apply finish ].
Qed.

Lemma sep__sep_mon_i :
 forall (i : nat) (Hi : i <= n) (Hi' : S i <= n) (Hi0 : i < n),
 sep__sep_fun_i i Hi[<]sep__sep_fun_i (S i) Hi'.
Proof.
 intros.
 apply less_leEq_trans with (P (S i) Hi0).
  apply sep__sep_less.
 apply sep__sep_leEq.
Qed.

Lemma sep__sep_mon :
 forall (i : nat) (Hi : i <= n) (Hi' : S i <= n),
 sep__sep_fun i Hi[<]sep__sep_fun (S i) Hi'.
Proof.
 intros.
 unfold sep__sep_fun in |- *.
 elim (le_lt_dec (S i) 0); intro; simpl in |- *.
  exfalso; apply (le_Sn_O _ a0).
 elim (le_lt_dec i 0); intro; simpl in |- *.
  elim (le_lt_eq_dec _ _ Hi'); intro; simpl in |- *.
   apply less_leEq_trans with (P (S i) Hi').
    apply leEq_less_trans with (P i Hi).
     elim (Partition_in_compact _ _ _ _ P i Hi); intros; auto.
    apply HP.
   apply sep__sep_leEq.
  assumption.
 elim (le_lt_eq_dec _ _ Hi); intro; simpl in |- *.
  elim (le_lt_eq_dec _ _ Hi'); intro; simpl in |- *.
   apply sep__sep_mon_i; assumption.
  eapply less_wdr.
   2: apply finish with (p := P) (H := le_n n).
  eapply less_wdr.
   apply sep__sep_less with (Hi' := Hi').
  generalize Hi'; rewrite b2.
  intro; apply prf1; auto.
 exfalso; rewrite b2 in Hi'; apply (le_Sn_n _ Hi').
Qed.

Lemma sep__sep_fun_i_wd :
 forall i j : nat,
 i = j ->
 forall (Hi : i <= n) (Hj : j <= n),
 sep__sep_fun_i i Hi[=]sep__sep_fun_i j Hj.
Proof.
 do 3 intro.
 rewrite <- H.
 intros.
 unfold sep__sep_fun_i in |- *.
 elim (sep__sep_aux_lemma i); intros; simpl in |- *.
  apply bin_op_wd_unfolded; [ apply prf1; auto | algebra ].
 apply prf1; auto.
Qed.

Lemma sep__sep_fun_wd :
 forall i j : nat,
 i = j ->
 forall (Hi : i <= n) (Hj : j <= n), sep__sep_fun i Hi[=]sep__sep_fun j Hj.
Proof.
 intros.
 unfold sep__sep_fun in |- *.
 elim (le_lt_dec i 0); elim (le_lt_dec j 0); intros; simpl in |- *.
    algebra.
   exfalso; apply (lt_irrefl 0); apply Nat.lt_le_trans with j; auto; rewrite <- H; auto.
  exfalso; apply (lt_irrefl 0); apply Nat.lt_le_trans with j; auto; rewrite <- H; auto.
 elim (le_lt_eq_dec _ _ Hi); elim (le_lt_eq_dec _ _ Hj); intros; simpl in |- *.
    apply sep__sep_fun_i_wd; auto.
   exfalso; rewrite H in a0; rewrite b2 in a0; apply (lt_irrefl _ a0).
  exfalso; rewrite <- H in a0; rewrite b2 in a0; apply (lt_irrefl _ a0).
 algebra.
Qed.

Definition sep__sep_part : Partition Hab n.
Proof.
 apply Build_Partition with sep__sep_fun.
    exact sep__sep_fun_wd.
   intros; apply less_leEq; apply sep__sep_mon.
  intros; unfold sep__sep_fun in |- *.
  elim (le_lt_dec 0 0); intro; simpl in |- *.
   algebra.
  exfalso; inversion b0.
 intros; unfold sep__sep_fun in |- *.
 elim (le_lt_dec n 0); intro; simpl in |- *.
  apply partition_length_zero with Hab.
  cut (n = 0); [ intro | auto with arith ].
  rewrite <- H0; apply P.
 elim (le_lt_eq_dec _ _ H); intro; simpl in |- *.
  exfalso; apply (lt_irrefl _ a0).
 algebra.
Defined.

Lemma sep__sep_lemma : Separated sep__sep_part R.
Proof.
 repeat split; unfold _Separated in |- *; intros.
   apply sep__sep_mon.
  apply HR.
 unfold sep__sep_part in |- *; simpl in |- *.
 unfold sep__sep_fun in |- *; simpl in |- *.
 elim (le_lt_dec i 0); intro; simpl in |- *.
  exfalso; apply lt_irrefl with 0; apply Nat.lt_le_trans with i; auto.
 elim (le_lt_eq_dec _ _ Hi); intro; simpl in |- *.
  apply sep__sep_ap.
 exfalso; rewrite b1 in H1; apply (lt_irrefl _ H1).
Qed.

Variable g : forall i : nat, i < n -> IR.
Hypothesis gP : Points_in_Partition P g.

Definition sep__sep_points (i : nat) (Hi : i < n) : IR.
Proof.
 intros.
 apply (Max (sep__sep_fun_i i (lt_le_weak _ _ Hi)) (g i Hi)).
Defined.

Lemma sep__sep_points_lemma :
 Points_in_Partition sep__sep_part sep__sep_points.
Proof.
 red in |- *; intros.
 split.
  unfold sep__sep_part in |- *; simpl in |- *.
  unfold sep__sep_fun, sep__sep_points in |- *.
  elim (le_lt_dec i 0); intro; simpl in |- *.
   apply leEq_transitive with (g i Hi).
    elim (Pts_part_lemma _ _ _ _ _ _ gP i Hi); intros; assumption.
   apply rht_leEq_Max.
  elim (le_lt_eq_dec _ _ (lt_le_weak _ _ Hi)); intro; simpl in |- *.
   eapply leEq_wdl.
    apply lft_leEq_Max.
   apply sep__sep_fun_i_wd; auto.
  exfalso; rewrite b1 in Hi; apply (lt_irrefl _ Hi).
 unfold sep__sep_part in |- *; simpl in |- *.
 unfold sep__sep_fun, sep__sep_points in |- *.
 elim (le_lt_dec (S i) 0); intro; simpl in |- *.
  exfalso; inversion a0.
 elim (le_lt_eq_dec _ _ Hi); intro; simpl in |- *.
  apply Max_leEq.
   apply less_leEq; apply sep__sep_mon_i; assumption.
  apply leEq_transitive with (P (S i) Hi).
   elim (gP i Hi); intros; auto.
  apply sep__sep_leEq.
 apply Max_leEq.
  unfold sep__sep_fun_i in |- *.
  elim (sep__sep_aux_lemma i); intro; simpl in |- *.
   apply leEq_transitive with (P (S i) Hi).
    apply shift_plus_leEq'.
    apply leEq_transitive with delta.
     astepl (delta [/]TwoNZ); apply less_leEq; apply pos_div_two'; exact RS_delta_pos.
    apply leEq_transitive with deltaP.
     apply RS_delta_deltaP.
    unfold deltaP in |- *; apply AntiMesh_lemma.
   elim (Partition_in_compact _ _ _ _ P (S i) Hi); intros; assumption.
  elim (Partition_in_compact _ _ _ _ P i (lt_le_weak _ _ Hi)); intros; assumption.
 elim (Pts_part_lemma _ _ _ _ _ _ gP i Hi); intros; assumption.
Qed.

Lemma sep__sep_aux :
  forall (i : nat) (H : i < n) Hg Hs,
  AbsIR (F (g i H) Hg[-]F (sep__sep_points i H) Hs)[<=]e.
Proof.
 intros.
 apply RS_Hd'.
   unfold I in |- *; apply Pts_part_lemma with n P; assumption.
  unfold I in |- *; apply Pts_part_lemma with n sep__sep_part; apply sep__sep_points_lemma.
 unfold sep__sep_points in |- *; simpl in |- *.
 eapply leEq_wdl.
  2: apply AbsIR_minus.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
  apply shift_minus_leEq; apply Max_leEq.
   unfold sep__sep_fun_i in |- *.
   elim sep__sep_aux_lemma; intro; simpl in |- *.
    apply leEq_transitive with (P i (lt_le_weak _ _ H)[+]delta).
     apply plus_resp_leEq_lft.
     apply less_leEq; astepl (delta [/]TwoNZ); apply pos_div_two'; exact RS_delta_pos.
    eapply leEq_wdr.
     2: apply cag_commutes_unfolded.
    apply plus_resp_leEq_both.
     elim (gP i H); intros; assumption.
    apply RS_delta_d.
   astepl ([0][+]P i (lt_le_weak _ _ H)).
   apply plus_resp_leEq_both.
    apply less_leEq; exact RS_Hd.
   elim (gP i H); intros; auto.
  apply shift_leEq_plus; astepl ZeroR; apply less_leEq; exact RS_Hd.
 apply shift_leEq_minus.
 eapply leEq_wdl.
  apply rht_leEq_Max.
 algebra.
Qed.

Notation just1 := (incF _ (Pts_part_lemma _ _ _ _ _ _ gP _ _)).
Notation just2 :=
  (incF _ (Pts_part_lemma _ _ _ _ _ _ sep__sep_points_lemma _ _)).

Lemma sep__sep_Sum :
 AbsIR (Partition_Sum gP incF[-]Partition_Sum sep__sep_points_lemma incF)[<=]
 alpha.
Proof.
 unfold Partition_Sum in |- *; simpl in |- *.
 rstepr (alpha [/]TwoNZ[+]alpha [/]TwoNZ).
 apply leEq_transitive with (e[*](b[-]a)[+]nring n[*]M[*]delta).
  apply leEq_wdr with (e[*] Sumx (fun (i : nat) (Hi : i < n) => P _ Hi[-]P _ (lt_le_weak _ _ Hi))[+]
    Sumx (fun (i : nat) (Hi : i < n) => M[*]delta)).
   apply leEq_transitive with (Sumx (fun (i : nat) (Hi : i < n) =>
     AbsIR (F (g i Hi) just1[-]F (sep__sep_points i Hi) just2)[*] (P _ Hi[-]P _ (lt_le_weak _ _ Hi)))[+]
       Sumx (fun (i : nat) (Hi : i < n) => AbsIR (F (sep__sep_points i Hi) just2)[*]
         (AbsIR (sep__sep_fun _ Hi[-]P _ Hi)[+]
           AbsIR (P _ (lt_le_weak _ _ Hi)[-]sep__sep_fun _ (lt_le_weak _ _ Hi))))).
    apply leEq_transitive with (AbsIR (Sumx (fun (i : nat) (Hi : i < n) =>
      F (g i Hi) just1[*](P _ Hi[-]P _ (lt_le_weak _ _ Hi))[-] F (sep__sep_points i Hi) just2[*]
        (P _ Hi[-]P _ (lt_le_weak _ _ Hi))))[+] AbsIR (Sumx (fun (i : nat) (Hi : i < n) =>
          F (sep__sep_points i Hi) just2[*] (sep__sep_fun _ Hi[-]P _ Hi[+]
            (P _ (lt_le_weak _ _ Hi)[-]sep__sep_fun _ (lt_le_weak _ _ Hi)))))).
     eapply leEq_wdl.
      apply triangle_IR_minus.
     apply eq_symmetric_unfolded.
     apply AbsIR_wd.
     eapply eq_transitive_unfolded.
      apply Sumx_minus_Sumx.
     eapply eq_transitive_unfolded.
      2: apply eq_symmetric_unfolded; apply Sumx_minus_Sumx.
     apply Sumx_wd; intros.
     astepl (F (g i H) just1[*](P _ H[-]P _ (lt_le_weak _ _ H))[-] F (sep__sep_points i H) just2[*]
       (sep__sep_fun _ H[-]sep__sep_fun _ (lt_le_weak _ _ H))).
     rational.
    apply plus_resp_leEq_both.
     eapply leEq_wdr.
      apply triangle_SumxIR.
     apply Sumx_wd; intros.
     apply eq_transitive_unfolded with (AbsIR (F (g i H) just1[-]F (sep__sep_points i H) just2)[*]
       AbsIR (P _ H[-]P _ (lt_le_weak _ _ H))).
      eapply eq_transitive_unfolded.
       2: apply AbsIR_resp_mult.
      apply AbsIR_wd; algebra.
     apply mult_wdr.
     apply AbsIR_eq_x.
     apply shift_leEq_minus; astepl (P i (lt_le_weak _ _ H)); apply prf2.
    eapply leEq_transitive.
     apply triangle_SumxIR.
    apply Sumx_resp_leEq; intros.
    eapply leEq_wdl.
     2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
    apply mult_resp_leEq_lft.
     apply triangle_IR.
    apply AbsIR_nonneg.
   apply plus_resp_leEq_both.
    eapply leEq_wdr.
     2: apply Sumx_comm_scal'.
    apply Sumx_resp_leEq; intros.
    apply mult_resp_leEq_rht.
     apply sep__sep_aux.
    apply shift_leEq_minus; astepl (P i (lt_le_weak _ _ H)); apply prf2.
   apply Sumx_resp_leEq; intros.
   apply mult_resp_leEq_both.
      apply AbsIR_nonneg.
     astepl (ZeroR[+][0]); apply plus_resp_leEq_both; apply AbsIR_nonneg.
    unfold I, M in |- *; apply norm_bnd_AbsIR.
    apply Pts_part_lemma with n sep__sep_part; apply sep__sep_points_lemma.
   rstepr (delta [/]TwoNZ[+]delta [/]TwoNZ).
   apply plus_resp_leEq_both.
    apply sep__sep_fun_delta.
   eapply leEq_wdl.
    2: apply AbsIR_minus.
   apply sep__sep_fun_delta.
  apply bin_op_wd_unfolded.
   apply mult_wdr.
   eapply eq_transitive_unfolded.
    apply Mengolli_Sum with (f := fun (i : nat) (Hi : i <= n) => P i Hi).
     red in |- *; intros; apply prf1; auto.
    intros; algebra.
   apply cg_minus_wd.
    apply finish.
   apply start.
  astepr (nring n[*](M[*]delta)); apply sumx_const.
 apply plus_resp_leEq_both.
  unfold e in |- *.
  apply leEq_wdl with (alpha [/]TwoNZ[*](b[-]a[/] _[//]max_one_ap_zero (b[-]a))).
   rstepr (alpha [/]TwoNZ[*][1]).
   apply mult_resp_leEq_lft.
    apply shift_div_leEq.
     apply pos_max_one.
    astepr (Max (b[-]a) [1]); apply lft_leEq_Max.
   apply less_leEq; apply pos_div_two; assumption.
  simpl in |- *; rational.
 apply leEq_transitive with (Max (nring n[*]M) [1][*]delta).
  apply mult_resp_leEq_rht.
   apply lft_leEq_Max.
  apply less_leEq; apply RS_delta_pos.
 apply shift_mult_leEq' with (max_one_ap_zero (nring n[*]M)).
  apply pos_max_one.
 unfold delta in |- *.
 eapply leEq_transitive.
  apply Min_leEq_rht.
 apply Min_leEq_lft.
Qed.

Lemma sep__sep_Mesh : Mesh sep__sep_part[<=]Mesh P[+]csi.
Proof.
 unfold Mesh in |- *.
 apply maxlist_leEq.
  apply length_Part_Mesh_List.
  exact RS_pos_n.
 intros x H.
 elim (Part_Mesh_List_lemma _ _ _ _ _ _ H); intros i Hi.
 elim Hi; clear Hi; intros Hi Hi'.
 elim Hi'; clear Hi'; intros Hi' Hx.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply Hx.
 unfold sep__sep_part in |- *; simpl in |- *.
 unfold sep__sep_fun in |- *; simpl in |- *.
 elim (le_lt_dec (S i) 0); intro; simpl in |- *.
  exfalso; inversion a0.
 elim (le_lt_eq_dec _ _ Hi'); intro; simpl in |- *.
  elim (le_lt_dec i 0); intro; simpl in |- *.
   cut (i = 0); [ intro | auto with arith ].
   unfold sep__sep_fun_i in |- *; simpl in |- *.
   elim (sep__sep_aux_lemma (S i)); intro; simpl in |- *.
    generalize Hi'; rewrite H0; clear Hx Hi'; intro.
    apply leEq_wdl with (P 1 Hi'[+]delta [/]TwoNZ[-]P 0 (le_O_n _)).
     rstepl (P 1 Hi'[-]P 0 (le_O_n _)[+]delta [/]TwoNZ).
     apply plus_resp_leEq_both.
      fold (Mesh P) in |- *; apply Mesh_lemma.
     apply leEq_transitive with delta.
      apply less_leEq; apply pos_div_two'; exact RS_delta_pos.
     apply RS_delta_csi.
    apply cg_minus_wd; [ algebra | apply start ].
   generalize Hi'; rewrite H0; clear Hx Hi'; intro.
   apply leEq_wdl with (P 1 Hi'[-]P 0 (le_O_n _)).
    fold (Mesh P) in |- *; apply leEq_transitive with (Mesh P[+][0]).
     astepr (Mesh P); apply Mesh_lemma.
    apply plus_resp_leEq_lft.
    apply less_leEq; assumption.
   apply cg_minus_wd; [ algebra | apply start ].
  elim (le_lt_eq_dec _ _ Hi); intro; simpl in |- *.
   unfold sep__sep_fun_i in |- *.
   elim (sep__sep_aux_lemma (S i)); elim (sep__sep_aux_lemma i); intros; simpl in |- *.
      rstepl (P (S i) Hi'[-]P i Hi).
      fold (Mesh P) in |- *; apply leEq_transitive with (Mesh P[+][0]).
       astepr (Mesh P); apply Mesh_lemma.
      apply plus_resp_leEq_lft.
      apply less_leEq; assumption.
     rstepl (P _ Hi'[-]P _ Hi[+]delta [/]TwoNZ).
     apply plus_resp_leEq_both.
      fold (Mesh P) in |- *; apply Mesh_lemma.
     apply leEq_transitive with delta.
      apply less_leEq; apply pos_div_two'; exact RS_delta_pos.
     apply RS_delta_csi.
    rstepl (P _ Hi'[-]P _ Hi[-]delta [/]TwoNZ).
    unfold cg_minus at 1 in |- *; apply plus_resp_leEq_both.
     fold (Mesh P) in |- *; apply Mesh_lemma.
    apply leEq_transitive with ZeroR.
     astepr ([--]ZeroR); apply inv_resp_leEq.
     apply less_leEq; apply pos_div_two; exact RS_delta_pos.
    apply leEq_transitive with delta.
     apply less_leEq; exact RS_delta_pos.
    apply RS_delta_csi.
   fold (Mesh P) in |- *; apply leEq_transitive with (Mesh P[+][0]).
    astepr (Mesh P); apply Mesh_lemma.
   apply plus_resp_leEq_lft.
   apply less_leEq; assumption.
  exfalso; rewrite b2 in a0; apply lt_irrefl with (S n);
    apply Nat.lt_trans with (S n); auto with arith.
 elim (le_lt_dec i 0); intro; simpl in |- *.
  cut (i = 0); [ intro | auto with arith ].
  rewrite H0 in b1.
  clear Hx; rewrite H0 in Hi'.
  apply leEq_wdl with (P 1 Hi'[-]P 0 (le_O_n n)).
   fold (Mesh P) in |- *; apply leEq_transitive with (Mesh P[+][0]).
    astepr (Mesh P); apply Mesh_lemma.
   apply plus_resp_leEq_lft.
   apply less_leEq; assumption.
  apply cg_minus_wd.
   generalize Hi'; rewrite b1; intro; apply finish.
  apply start.
 elim (le_lt_eq_dec _ _ Hi); intro; simpl in |- *.
  unfold sep__sep_fun_i in |- *.
  elim (sep__sep_aux_lemma i); intro; simpl in |- *.
   apply leEq_wdl with (P (S i) Hi'[-](P i Hi[+]delta [/]TwoNZ)).
    rstepl (P (S i) Hi'[-]P i Hi[-]delta [/]TwoNZ).
    unfold cg_minus at 1 in |- *; apply plus_resp_leEq_both.
     fold (Mesh P) in |- *; apply Mesh_lemma.
    apply leEq_transitive with ZeroR.
     astepr ([--]ZeroR); apply inv_resp_leEq.
     apply less_leEq; apply pos_div_two; exact RS_delta_pos.
    apply leEq_transitive with delta.
     apply less_leEq; exact RS_delta_pos.
    apply RS_delta_csi.
   apply cg_minus_wd.
    generalize Hi'; rewrite b1; intro; apply finish.
   algebra.
  apply leEq_wdl with (P (S i) Hi'[-]P i Hi).
   fold (Mesh P) in |- *; apply leEq_transitive with (Mesh P[+][0]).
    astepr (Mesh P); apply Mesh_lemma.
   apply plus_resp_leEq_lft.
   apply less_leEq; assumption.
  apply cg_minus_wd.
   generalize Hi'; rewrite b1; intro; apply finish.
  algebra.
 exfalso; rewrite b3 in b1; apply n_Sn with n; auto.
Qed.

End Separating__Separated.
(* end hide *)
