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
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *)
(* begin hide *)
(* in this file the  concrete canonical isomorphism -in te sense of
   R_morphisms.v - between two arbitrary model of real numbers is built *)

Require Export CoRN.reals.Q_dense.
Require Export CoRN.reals.R_morphism.

Lemma less_pres_Lim :
 forall (IR : CReals) (g h : R_COrdField IR), Lim g[<]Lim h -> g[<]h.
Proof.
 do 3 intro. intro H.
 simpl in |- *.
 red in |- *.
 cut (SeqLimit (CS_seq IR g) (Lim g)).
  intro H0.
  cut (SeqLimit (CS_seq IR h) (Lim h)).
   intro H1.
   red in H0.
   cut {N : nat | forall m : nat,
     N <= m -> AbsSmall ((Lim h[-]Lim g) [/]ThreeNZ) (CS_seq IR g m[-]Lim g)}.
    intro H2.
    case H2.
    intro N1.
    intro H3.
    red in H1.
    cut {N : nat | forall m : nat,
      N <= m -> AbsSmall ((Lim h[-]Lim g) [/]ThreeNZ) (CS_seq IR h m[-]Lim h)}.
     intro H4.
     case H4.
     intro N2.
     intro H5.
     exists (N1 + N2).
     exists ((Lim h[-]Lim g) [/]FourNZ).
      apply pos_div_four.
      apply shift_zero_less_minus.
      assumption.
     intros.
     cut (AbsSmall ((Lim h[-]Lim g) [/]ThreeNZ) (CS_seq IR h n[-]Lim h)).
      intro.
      cut (AbsSmall ((Lim h[-]Lim g) [/]ThreeNZ) (CS_seq IR g n[-]Lim g)).
       intro.
       elim H7.
       intros H9 H10.
       elim H8.
       intros H11 H12.
       apply leEq_transitive with ((Lim h[-]Lim g) [/]ThreeNZ).
        apply mult_cancel_leEq with (Twelve:IR).
         astepl (nring (R:=IR) 0); apply nring_less; auto with arith.
        rstepl ([0][+]Three[*](Lim h[-]Lim g)).
        rstepr (Lim h[-]Lim g[+]Three[*](Lim h[-]Lim g)).
        apply plus_resp_leEq.
        apply shift_zero_leEq_minus; apply less_leEq; auto.
       apply plus_cancel_leEq_rht with (z := Lim g[-]Lim h).
       rstepr (CS_seq IR h n[-]Lim h[+](Lim g[-]CS_seq IR g n)).
       rstepl ([--]((Lim h[-]Lim g) [/]ThreeNZ)[+][--]((Lim h[-]Lim g) [/]ThreeNZ)).
       apply plus_resp_leEq_both.
        assumption.
       rstepr ([--](CS_seq IR g n[-]Lim g)).
       apply inv_resp_leEq.
       assumption.
      apply H3.
      apply le_trans with (m := N1 + N2).
       apply le_plus_l.
      assumption.
     apply H5.
     apply le_trans with (m := N1 + N2).
      apply le_plus_r.
     assumption.
    apply H1.
    apply div_resp_pos.
     apply pos_three.
    apply shift_zero_less_minus.
    assumption.
   apply H0.
   apply div_resp_pos.
    apply pos_three.
   apply shift_zero_less_minus.
   assumption.
  apply Lim_Cauchy.
 apply Lim_Cauchy.
Qed.

Lemma Lim_pres_less :
 forall (IR : CReals) (g h : R_COrdField IR), g[<]h -> Lim g[<]Lim h.
Proof.
 do 3 intro.  intro H.
 apply plus_cancel_less with (z := [--](Lim g)).
 astepl ([0]:IR).
 astepr (Lim h[-]Lim g).
 simpl in H.
 red in H.
 case H.
 intro N.
 intro H0.
 case H0.
 intros e H1 H3.
 set (H2 := True) in *. (* dummy *)
 cut (SeqLimit (CS_seq IR g) (Lim g)).
  intro H4.
  cut (SeqLimit (CS_seq IR h) (Lim h)).
   intro H5.
   red in H4.
   cut {N : nat | forall m : nat, N <= m -> AbsSmall (e [/]ThreeNZ) (CS_seq IR g m[-]Lim g)}.
    intro H6.
    red in H5.
    cut {N : nat | forall m : nat, N <= m -> AbsSmall (e [/]ThreeNZ) (CS_seq IR h m[-]Lim h)}.
     intro H7.
     case H6.
     intro N1.
     intro H8.
     case H7.
     intro N2.
     intro H9.
     cut (AbsSmall (e [/]ThreeNZ) (CS_seq IR g (N + (N1 + N2))[-]Lim g)).
      intro H10.
      cut (AbsSmall (e [/]ThreeNZ) (CS_seq IR h (N + (N1 + N2))[-]Lim h)).
       intro H11.
       elim H10.
       intros H12 H13.
       elim H11.
       intros H14 H15.
       apply less_leEq_trans with (y := e [/]ThreeNZ).
        apply pos_div_three.
        assumption.
       rstepr (Lim h[-]CS_seq IR h (N + (N1 + N2))[+]
         (CS_seq IR h (N + (N1 + N2))[-]CS_seq IR g (N + (N1 + N2)))[+]
           (CS_seq IR g (N + (N1 + N2))[-]Lim g)).
       rstepl ([--](e [/]ThreeNZ)[+]e[+][--](e [/]ThreeNZ)).
       apply plus_resp_leEq_both.
        apply plus_resp_leEq_both.
         rstepr ([--](CS_seq IR h (N + (N1 + N2))[-]Lim h)).
         apply inv_resp_leEq.
         assumption.
        apply H3.
        apply le_plus_l.
       assumption.
      apply H9.
      rewrite -> plus_comm with (m := N2).
      rewrite -> plus_permute with (m := N2).
      apply le_plus_l.
     apply H8.
     rewrite -> plus_permute with (m := N1).
     apply le_plus_l.
    apply H5.
    apply pos_div_three.
    assumption.
   apply H4.
   apply pos_div_three.
   assumption.
  apply Lim_Cauchy.
 apply Lim_Cauchy.
Qed.


Lemma inj_seq_less :
 forall (IR : CReals) (g h : R_COrdField Q_as_COrdField),
 g[<]h ->
 (Build_CauchySeq IR (fun m : nat => inj_Q IR (CS_seq Q_as_COrdField g m))
    (inj_Q_Cauchy IR g)
  :R_COrdField IR)[<]
 Build_CauchySeq IR (fun m : nat => inj_Q IR (CS_seq Q_as_COrdField h m))
   (inj_Q_Cauchy IR h).
Proof.
 do 3 intro.  intro H.
 simpl in |- *.
 red in |- *.
 simpl in H.
 red in H.
 case H.
 intros N H2.
 case H2.
 intros e H1 H3.
 set (H0 := True) in *. (* dummy *)
 exists N.
 exists (inj_Q IR e).
  apply less_wdl with (x := inj_Q IR [0]).
   apply inj_Q_less.
   assumption.
  simpl in |- *.
  rational.
 intros.
 simpl in |- *.
 apply leEq_wdr with (y := inj_Q IR (CS_seq Q_as_COrdField h n[-]CS_seq Q_as_COrdField g n)).
  apply inj_Q_leEq.
  apply H3.
  assumption.
 apply inj_Q_minus.
Qed.

Lemma less_inj_seq :
 forall (IR : CReals) (g h : R_COrdField Q_as_COrdField),
 (Build_CauchySeq IR (fun m : nat => inj_Q IR (CS_seq Q_as_COrdField g m))
    (inj_Q_Cauchy IR g)
  :R_COrdField IR)[<]
 Build_CauchySeq IR (fun m : nat => inj_Q IR (CS_seq Q_as_COrdField h m))
   (inj_Q_Cauchy IR h) -> g[<]h.
Proof.
 do 3 intro.  intro H.
 simpl in |- *.
 red in |- *.
 simpl in H.
 red in H.
 simpl in H.
 case H.
 intros N H2.
 case H2.
 intros e H1 H6.
 set (H0 := True) in *. (* dummy *)
 case (Q_dense_in_CReals IR e).
  assumption.
 intro q.
 set (H3 := True) in *. (* dummy *)
 intros H4 H5.
 exists N.
 exists q.
  apply less_inj_Q with (R1 := IR).
  simpl in |- *.
  rstepl ([0]:IR).
  assumption.
 intros.
 apply leEq_inj_Q with (R1 := IR).
 apply leEq_transitive with (y := e).
  apply less_leEq; assumption.
 apply leEq_wdr with (y := inj_Q IR (CS_seq Q_as_COrdField h n)[-]
   inj_Q IR (CS_seq Q_as_COrdField g n)).
  apply H6.
  assumption.
 apply eq_symmetric_unfolded.
 apply inj_Q_minus.
Qed.

Theorem SeqLimit_unique :
 forall (IR : CReals) (g : CauchySeq IR) (y : IR), SeqLimit g y -> y[=]Lim g.
Proof.
 do 3 intro.  intro H.
 apply not_ap_imp_eq.
 intro H0.
 case (ap_imp_less IR y (Lim g) H0).
  intro H1.
  red in H.
  cut {N : nat | forall m : nat, N <= m -> AbsSmall ((Lim g[-]y) [/]ThreeNZ) (CS_seq IR g m[-]y)}.
   intro H2.
   case H2.
   intro N1.
   intro H3.
   cut (SeqLimit g (Lim g)).
    intro H4.
    red in H4.
    cut {N : nat | forall m : nat, N <= m -> AbsSmall ((Lim g[-]y) [/]ThreeNZ) (CS_seq IR g m[-]Lim g)}.
     intro H5.
     case H5.
     intro N2.
     intro H6.
     apply less_irreflexive_unfolded with (x := y[-]Lim g).
     rstepr ([0][+](CS_seq _ g (N1 + N2)[-]Lim g)[+](y[-]CS_seq _ g (N1 + N2))).
     rstepl ((y[-]Lim g) [/]ThreeNZ[+](y[-]Lim g) [/]ThreeNZ[+](y[-]Lim g) [/]ThreeNZ).
     apply plus_resp_less_leEq.
      apply plus_resp_less_leEq.
       apply shift_div_less.
        apply pos_three.
       apply shift_minus_less; rstepr (Lim g); auto.
      elim (H6 (N1 + N2)); intros.
       rstepl ([--]((Lim g[-]y) [/]ThreeNZ)); auto.
      apply le_plus_r.
     elim (H3 (N1 + N2)); intros.
      apply inv_cancel_leEq.
      rstepr ((Lim g[-]y) [/]ThreeNZ); rstepl (g (N1 + N2)[-]y); auto.
     apply le_plus_l.
    apply H4.
    apply pos_div_three.
    apply shift_zero_less_minus.
    assumption.
   apply Lim_Cauchy.
  apply H.
  apply pos_div_three.
  apply shift_zero_less_minus.
  assumption.
 intro.
 red in H.
 cut {N : nat | forall m : nat, N <= m -> AbsSmall ((y[-]Lim g) [/]ThreeNZ) (CS_seq IR g m[-]y)}.
  intro H2.
  case H2.
  intro N1.
  intro H3.
  cut (SeqLimit g (Lim g)).
   intro H4.
   red in H4.
   cut {N : nat | forall m : nat, N <= m -> AbsSmall ((y[-]Lim g) [/]ThreeNZ) (CS_seq IR g m[-]Lim g)}.
    intro H5.
    case H5.
    intro N2.
    intros.
    apply less_irreflexive_unfolded with (x := Lim g[-]y).
    rstepr ([0][+](Lim g[-]CS_seq _ g (N1 + N2))[+](CS_seq _ g (N1 + N2)[-]y)).
    rstepl ((Lim g[-]y) [/]ThreeNZ[+](Lim g[-]y) [/]ThreeNZ[+](Lim g[-]y) [/]ThreeNZ).
    apply plus_resp_less_leEq.
     apply plus_resp_less_leEq.
      apply shift_div_less.
       apply pos_three.
      apply shift_minus_less; rstepr y; auto.
     elim (a (N1 + N2)); intros.
      apply inv_cancel_leEq.
      rstepr ((y[-]Lim g) [/]ThreeNZ); rstepl (g (N1 + N2)[-]Lim g); auto.
     apply le_plus_r.
    elim (H3 (N1 + N2)); intros.
     rstepl ([--]((y[-]Lim g) [/]ThreeNZ)); auto.
    apply le_plus_l.
   apply H4.
   apply pos_div_three.
   apply shift_zero_less_minus.
   assumption.
  apply Lim_Cauchy.
 apply H.
 apply pos_div_three.
 apply shift_zero_less_minus.
 assumption.
Qed.


Lemma Lim_well_def :
 forall (IR : CReals) (g h : R_COrdField IR), g[=]h -> Lim g[=]Lim h.
Proof.
 intros.
 apply SeqLimit_unique with (y := Lim g).
 red in |- *.
 intros e H0.
 cut (Not (g[#]h)).
  intro.
  cut (forall e : IR, [0][<]e -> {N : nat |
    forall m : nat, N <= m -> AbsSmall e (CS_seq IR g m[-]CS_seq IR h m)}).
   intro H2.
   cut {N : nat | forall m : nat, N <= m -> AbsSmall (e [/]TwoNZ) (CS_seq IR g m[-]CS_seq IR h m)}.
    intro H3.
    cut (SeqLimit (CS_seq IR g) (Lim g)).
     intro H4.
     red in H4.
     cut {N : nat | forall m : nat, N <= m -> AbsSmall (e [/]TwoNZ) (CS_seq IR g m[-]Lim g)}.
      intro H5.
      case H3.
      intro N1.
      intro H6.
      case H5.
      intro N2.
      intro H7.
      exists (N1 + N2).
      intros.
      rstepl (e [/]TwoNZ[+]e [/]TwoNZ).
      rstepr (CS_seq IR h m[-]CS_seq IR g m[+](CS_seq IR g m[-]Lim g)).
      apply AbsSmall_plus.
       apply AbsSmall_minus.
       apply H6.
       apply le_trans with (m := N1 + N2).
        apply le_plus_l.
       assumption.
      apply H7.
      apply le_trans with (m := N1 + N2).
       apply le_plus_r.
      assumption.
     apply H4.
     apply pos_div_two.
     assumption.
    apply Lim_Cauchy.
   apply H2.
   apply pos_div_two.
   assumption.
  intros.
  apply Eq_alt_2_1.
   assumption.
  assumption.
 apply eq_imp_not_ap.
 assumption.
Qed.




Lemma Lim_one_one :
 forall (IR : CReals) (g h : R_COrdField IR), Lim g[=]Lim h -> g[=]h.
Proof.
 intros.
 apply not_ap_imp_eq.
 apply Eq_alt_2_2 with (x := g) (y := h).
 intros.
 cut (SeqLimit (CS_seq IR g) (Lim g)).
  intro H1.
  red in H1.
  cut (SeqLimit (CS_seq IR h) (Lim h)).
   intro H2.
   red in H2.
   cut {N : nat | forall m : nat, N <= m -> AbsSmall (e [/]TwoNZ) (CS_seq IR g m[-]Lim g)}.
    intro H3.
    cut {N : nat | forall m : nat, N <= m -> AbsSmall (e [/]TwoNZ) (CS_seq IR h m[-]Lim h)}.
     intro H4.
     case H3.
     intro N1.
     intro H5.
     case H4.
     intro N2.
     intro H6.
     exists (N1 + N2).
     intros m H7.
     rstepl (e [/]TwoNZ[+]e [/]TwoNZ).
     astepr (CS_seq IR g m[-]Lim g[+](Lim h[-]CS_seq IR h m)).
      apply AbsSmall_plus.
       apply H5.
       apply le_trans with (m := N1 + N2).
        apply le_plus_l.
       assumption.
      apply AbsSmall_minus.
      apply H6.
      apply le_trans with (m := N1 + N2).
       apply le_plus_r.
      assumption.
     apply eq_transitive_unfolded with (y := CS_seq IR g m[-]CS_seq IR h m[+](Lim h[-]Lim g)).
      rational.
     astepr (CS_seq IR g m[-]CS_seq IR h m[+][0]).
     apply bin_op_wd_unfolded.
      apply eq_reflexive_unfolded.
     apply cg_cancel_rht with (x := Lim g).
     apply eq_transitive_unfolded with (y := Lim h).
      apply eq_symmetric_unfolded.
      apply cg_cancel_mixed.
     astepr (Lim g).
     apply eq_symmetric_unfolded.
     assumption.
    apply H2.
    apply pos_div_two.
    assumption.
   apply H1.
   apply pos_div_two.
   assumption.
  apply Lim_Cauchy.
 apply Lim_Cauchy.
Qed.


Lemma inj_seq_well_def :
 forall (IR : CReals) (g h : R_COrdField Q_as_COrdField),
 g[=]h ->
 (Build_CauchySeq IR (fun m : nat => inj_Q IR (CS_seq _ g m))
    (inj_Q_Cauchy IR g)
  :R_COrdField IR)[=]
 Build_CauchySeq IR (fun m : nat => inj_Q IR (CS_seq _ h m))
   (inj_Q_Cauchy IR h).
Proof.
 intros.
 apply not_ap_imp_eq.
 apply Eq_alt_2_2 with (x := Build_CauchySeq IR (fun m : nat => inj_Q IR (CS_seq _ g m))
   (inj_Q_Cauchy IR g)) (y := Build_CauchySeq IR (fun m : nat => inj_Q IR (CS_seq Q_as_COrdField h m))
     (inj_Q_Cauchy IR h)).
 intros.
 simpl in |- *.
 case (Q_dense_in_CReals IR (e [/]TwoNZ)).
  apply pos_div_two.
  assumption.
 intro q.
 set (H1 := True) in *. (* dummy *)
 intros H2 H3.
 cut {N : nat | forall m : nat, N <= m ->
   AbsSmall q (CS_seq Q_as_COrdField g m[-]CS_seq Q_as_COrdField h m)}.
  intro H4.
  case H4.
  intro N.
  intro H5.
  exists N.
  intros.
  apply AbsSmall_wdr_unfolded with
    (y := inj_Q IR (CS_seq Q_as_COrdField g m[-]CS_seq Q_as_COrdField h m)).
   apply AbsSmall_leEq_trans with (inj_Q IR q).
    apply less_leEq; apply less_transitive_unfolded with (e [/]TwoNZ).
     assumption.
    apply pos_div_two'; auto.
   apply inj_Q_AbsSmall.
   apply H5.
   assumption.
  apply inj_Q_minus.
 apply Eq_alt_2_1.
  change (Not (g[#]h)) in |- *.
  apply eq_imp_not_ap.
  assumption.
 apply less_inj_Q with (R1 := IR).
 apply less_wdl with ([0]:IR).
  assumption.
 simpl in |- *.
 rational.
Qed.


Lemma inj_Q_one_one :
 forall (IR : CReals) (g h : R_COrdField Q_as_COrdField),
 (Build_CauchySeq IR (fun m : nat => inj_Q IR (CS_seq _ g m))
    (inj_Q_Cauchy IR g)
  :R_COrdField IR)[=]
 Build_CauchySeq IR (fun m : nat => inj_Q IR (CS_seq _ h m))
   (inj_Q_Cauchy IR h) -> g[=]h.
Proof.
 intros.
 apply not_ap_imp_eq.
 apply Eq_alt_2_2 with (x := g) (y := h).
 intros.
 cut {N : nat | forall m : nat, N <= m -> AbsSmall (inj_Q IR e) (CS_seq IR (Build_CauchySeq IR
   (fun m : nat => inj_Q IR (CS_seq Q_as_COrdField g m)) (inj_Q_Cauchy IR g)) m[-] CS_seq IR
     (Build_CauchySeq IR (fun m : nat => inj_Q IR (CS_seq Q_as_COrdField h m))
       (inj_Q_Cauchy IR h)) m)}.
  intro H1.
  case H1.
  intro N.
  intros.
  exists N.
  intros.
  cut (AbsSmall (inj_Q IR e) (CS_seq IR (Build_CauchySeq IR
    (fun m0 : nat => inj_Q IR (CS_seq Q_as_COrdField g m0)) (inj_Q_Cauchy IR g)) m[-] CS_seq IR
      (Build_CauchySeq IR (fun m0 : nat => inj_Q IR (CS_seq Q_as_COrdField h m0))
        (inj_Q_Cauchy IR h)) m)).
   intro.
   cut (AbsSmall (inj_Q IR e) (inj_Q IR (CS_seq Q_as_COrdField g m[-]CS_seq Q_as_COrdField h m))).
    intro H5.
    apply AbsSmall_inj_Q with IR.
    auto.
   apply AbsSmall_wdr_unfolded with (inj_Q IR (CS_seq Q_as_COrdField g m)[-]
     inj_Q IR (CS_seq Q_as_COrdField h m)).
    assumption.
   apply eq_symmetric_unfolded.
   apply inj_Q_minus.
  apply a.
  assumption.
 apply Eq_alt_2_1.
  change (Not ((Build_CauchySeq IR (fun m : nat => inj_Q IR (CS_seq Q_as_COrdField g m))
    (inj_Q_Cauchy IR g) :R_COrdField IR)[#] Build_CauchySeq IR
      (fun m : nat => inj_Q IR (CS_seq Q_as_COrdField h m)) (inj_Q_Cauchy IR h))) in |- *.
  apply eq_imp_not_ap.
  assumption.
 apply less_wdl with (inj_Q IR [0]).
  apply inj_Q_less.
  assumption.
 simpl in |- *.
 rational.
Qed.



Lemma Lim_pres_plus :
 forall (IR : CReals) (g h : R_COrdField IR), Lim (g[+]h)[=]Lim g[+]Lim h.
Proof.
 intros.
 apply eq_symmetric_unfolded.
 apply SeqLimit_unique with (g := g[+]h).
 red in |- *.
 simpl in |- *.
 intros.
 cut {N : nat | forall m : nat, N <= m -> AbsSmall (e [/]TwoNZ) (CS_seq IR g m[-]Lim g)}.
  intro H2.
  case H2.
  intro N1.
  intro H3.
  cut {N : nat | forall m : nat, N <= m -> AbsSmall (e [/]TwoNZ) (CS_seq IR h m[-]Lim h)}.
   intro H4.
   case H4.
   intro N2.
   intro H5.
   exists (N1 + N2).
   intros.
   rstepr (CS_seq IR g m[-]Lim g[+](CS_seq IR h m[-]Lim h)).
   rstepl (e [/]TwoNZ[+]e [/]TwoNZ).
   apply AbsSmall_plus.
    apply H3.
    apply le_trans with (m := N1 + N2).
     apply le_plus_l.
    assumption.
   apply H5.
   apply le_trans with (m := N1 + N2).
    apply le_plus_r.
   assumption.
  apply (ax_Lim _ _ (crl_proof IR) h).
  apply pos_div_two.
  assumption.
 apply (ax_Lim _ _ (crl_proof IR) g).
 apply pos_div_two.
 assumption.
Qed.


Lemma G_pres_plus :
 forall (IR : CReals) (x y : IR),
 (Build_CauchySeq Q_as_COrdField (fun m : nat => G IR (x[+]y) m)
    (CS_seq_G IR (x[+]y))
  :R_COrdField Q_as_COrdField)[=]
 Build_CauchySeq Q_as_COrdField (fun m : nat => G IR x m[+]G IR y m)
   (CS_seq_plus Q_as_COrdField (fun n : nat => G IR x n)
      (fun n : nat => G IR y n) (CS_seq_G IR x) (CS_seq_G IR y)).
Proof.
 intros.
 apply not_ap_imp_eq.
 apply Eq_alt_2_2 with (x := Build_CauchySeq Q_as_COrdField (fun m : nat => G IR (x[+]y) m)
   (CS_seq_G IR (x[+]y))) (y := Build_CauchySeq Q_as_COrdField (fun m : nat => G IR x m[+]G IR y m)
     (CS_seq_plus Q_as_COrdField (fun n : nat => G IR x n) (fun n : nat => G IR y n) (CS_seq_G IR x) (
       CS_seq_G IR y))).
 intros e H.
 unfold CS_seq at 1 in |- *.
 unfold CS_seq in |- *.
 cut (SeqLimit (inj_Q_G_as_CauchySeq IR x) x).
  intro H0.
  cut (SeqLimit (inj_Q_G_as_CauchySeq IR y) y).
   intro H1.
   red in H0.
   cut {N : nat | forall m : nat, N <= m -> AbsSmall (inj_Q IR (e [/]ThreeNZ))
     (CS_seq IR (inj_Q_G_as_CauchySeq IR x) m[-]x)}.
    intro H2.
    case H2.
    intro N1.
    intros.
    red in H1.
    cut {N : nat | forall m : nat, N <= m -> AbsSmall (inj_Q IR (e [/]ThreeNZ))
      (CS_seq IR (inj_Q_G_as_CauchySeq IR y) m[-]y)}.
     intro H4.
     case H4.
     intro N2.
     intro H5.
     cut (SeqLimit (inj_Q_G_as_CauchySeq IR (x[+]y)) (x[+]y)).
      intro H6.
      red in H6.
      cut {N : nat | forall m : nat, N <= m -> AbsSmall (inj_Q IR (e [/]ThreeNZ))
        (CS_seq IR (inj_Q_G_as_CauchySeq IR (x[+]y)) m[-](x[+]y))}.
       intro H7.
       case H7.
       intro K.
       intro H8.
       exists (K + (N1 + N2)).
       intros.
       apply AbsSmall_inj_Q with (R1 := IR).
       apply AbsSmall_wdr_unfolded with (y := inj_Q IR (G IR (x[+]y) m)[-]
         (inj_Q _ (G IR x m)[+]inj_Q _ (G IR y m))).
        rstepr (inj_Q _ (G IR (x[+]y) m)[-](x[+]y)[+](x[-]inj_Q _ (G IR x m))[+] (y[-]inj_Q _ (G IR y m))).
        apply AbsSmall_wdl_unfolded with (x := inj_Q IR (e [/]ThreeNZ)[+]inj_Q IR (e [/]ThreeNZ)[+]
          inj_Q IR (e [/]ThreeNZ)).
         apply AbsSmall_plus.
          apply AbsSmall_plus.
           change (AbsSmall (inj_Q IR (e [/]ThreeNZ)) (CS_seq IR (inj_Q_G_as_CauchySeq IR (x[+]y)) m[-](x[+]y)))
             in |- *.
           apply H8.
           apply le_trans with (m := K + (N1 + N2)).
            apply le_plus_l.
           assumption.
          apply AbsSmall_minus.
          change (AbsSmall (inj_Q IR (e [/]ThreeNZ)) (CS_seq IR (inj_Q_G_as_CauchySeq IR x) m[-]x)) in |- *.
          apply a.
          apply le_trans with (m := K + (N1 + N2)).
           rewrite -> plus_permute with (m := N1).
           apply le_plus_l.
          assumption.
         apply AbsSmall_minus.
         change (AbsSmall (inj_Q IR (e [/]ThreeNZ)) (CS_seq IR (inj_Q_G_as_CauchySeq IR y) m[-]y)) in |- *.
         apply H5.
         apply le_trans with (m := K + (N1 + N2)).
          rewrite -> plus_comm with (m := N2).
          rewrite -> plus_permute with (m := N2).
          apply le_plus_l.
         assumption.
        apply eq_transitive_unfolded with (y := inj_Q IR (e [/]ThreeNZ[+]e [/]ThreeNZ[+]e [/]ThreeNZ)).
         apply eq_transitive_unfolded with
           (y := inj_Q _ (e [/]ThreeNZ[+]e [/]ThreeNZ)[+]inj_Q IR (e [/]ThreeNZ)).
          apply bin_op_wd_unfolded.
           apply eq_symmetric_unfolded.
           apply inj_Q_plus.
          apply eq_reflexive_unfolded.
         apply eq_symmetric_unfolded.
         apply inj_Q_plus.
        apply inj_Q_wd.
        rational.
       apply eq_transitive_unfolded with (y := inj_Q IR (G IR (x[+]y) m)[-]inj_Q IR (G IR x m[+]G IR y m)).
        apply cg_minus_wd.
         apply eq_reflexive_unfolded.
        apply eq_symmetric_unfolded.
        apply inj_Q_plus.
       apply eq_symmetric_unfolded.
       apply inj_Q_minus.
      apply H6.
      apply less_wdl with (x := inj_Q IR [0]).
       apply inj_Q_less.
       apply div_resp_pos.
        apply pos_three.
       assumption.
      simpl in |- *.
      rational.
     apply x_is_SeqLimit_G.
    apply H1.
    apply less_wdl with (x := inj_Q IR [0]).
     apply inj_Q_less.
     apply div_resp_pos.
      apply pos_three.
     assumption.
    simpl in |- *.
    rational.
   apply H0.
   apply less_wdl with (x := inj_Q IR [0]).
    apply inj_Q_less.
    apply div_resp_pos.
     apply pos_three.
    assumption.
   simpl in |- *.
   rational.
  apply x_is_SeqLimit_G.
 apply x_is_SeqLimit_G.
Qed.

(* This theorem can be avoided but it is interesting *)
Theorem nonarchemaedian_bound_for_Lim :
 forall (IR : CReals) (g : CauchySeq IR),
 {H : IR | [0][<]H | AbsSmall H (Lim g)}.
Proof.
 intros.
 case (CS_seq_bounded IR (CS_seq IR g) (CS_proof IR g)).
 intro K.
 set (H := True) in *. (* dummy *)
 intros H0 H1.
 case H1.
 intro M.
 intro H2.
 exists ([1][+]K).
  apply plus_resp_pos.
   apply pos_one.
  apply leEq_not_eq.
   apply (AbsSmall_nonneg IR K (CS_seq IR g M)).
   apply H2.
   constructor.
  apply ap_symmetric_unfolded; apply pos_ap_zero; auto.
 cut (SeqLimit g (Lim g)).
  intro H3.
  red in H3.
  case (H3 [1]).
   apply pos_one.
  intro N.
  intros.
  rstepr (Lim g[-]CS_seq IR g (N + M)[+]CS_seq IR g (N + M)).
  apply AbsSmall_plus.
   apply AbsSmall_minus.
   apply a.
   apply le_plus_l.
  apply H2.
  apply le_plus_r.
 apply Lim_Cauchy.
Qed.

Lemma Lim_pres_mult :
 forall (IR : CReals) (g h : R_COrdField IR), Lim (g[*]h)[=]Lim g[*]Lim h.
Proof.
 intros.
 apply eq_symmetric_unfolded.
 apply SeqLimit_unique with (g := g[*]h).
 red in |- *.
 simpl in |- *.
 intros.
 case (CS_seq_bounded IR (CS_seq IR g) (CS_proof IR g)).
 intro K.
 set (H2 := True) in *. (* dummy *)
 intros H3 H4.
 case H4.
 intro M1.
 intro H5.
 case (nonarchemaedian_bound_for_Lim _ h).
 intro L.
 set (H6 := True) in *. (* dummy *)
 intros H7 H8.
 cut (Six[*]K[#][0]).
  intro H9.
  cut (Six[*]L[#][0]).
   intro H10.
   case (ax_Lim _ _ (crl_proof IR) g (e[/] Six[*]L[//]H10)).
    apply div_resp_pos.
     apply mult_resp_pos.
      apply pos_nring_S.
     assumption.
    assumption.
   intro N1.
   intro H11.
   case (ax_Lim _ _ (crl_proof IR) h (e[/] Six[*]K[//]H9)).
    apply div_resp_pos.
     apply mult_resp_pos.
      apply pos_nring_S.
     apply leEq_not_eq.
      apply (AbsSmall_nonneg IR K (CS_seq IR g M1)).
      apply H5.
      constructor.
     apply less_imp_ap; auto.
    assumption.
   intro N2.
   intro H12.
   exists (N1 + (N2 + M1)).
   intros m H13.
   rstepr (CS_seq IR g m[*](CS_seq IR h m[-]Lim h)[+]Lim h[*](CS_seq IR g m[-]Lim g)).
   rstepl (Three[*](K[*](e[/] Six[*]K[//]H9))[+]Three[*](L[*](e[/] Six[*]L[//]H10))).
   apply AbsSmall_plus.
    apply AbsSmall_mult.
     apply H5.
     apply le_trans with (m := N1 + (N2 + M1)).
      rewrite -> plus_comm with (m := M1).
      rewrite -> plus_permute with (m := M1).
      apply le_plus_l.
     assumption.
    apply H12.
    apply le_trans with (m := N1 + (N2 + M1)).
     rewrite -> plus_permute with (m := N2).
     apply le_plus_l.
    assumption.
   apply AbsSmall_mult.
    assumption.
   apply H11.
   apply le_trans with (m := N1 + (N2 + M1)).
    apply le_plus_l.
   assumption.
  apply Greater_imp_ap.
  apply mult_resp_pos.
   apply pos_nring_S.
  assumption.
 apply Greater_imp_ap.
 apply mult_resp_pos.
  apply pos_nring_S.
 apply leEq_not_eq.
  apply (AbsSmall_nonneg IR K (CS_seq IR g M1)).
  apply H5.
  constructor.
 apply less_imp_ap; auto.
Qed.


Lemma G_pres_mult :
 forall (IR : CReals) (x y : IR),
 (Build_CauchySeq Q_as_COrdField (fun m : nat => G IR (x[*]y) m)
    (CS_seq_G IR (x[*]y))
  :R_COrdField Q_as_COrdField)[=]
 Build_CauchySeq Q_as_COrdField (fun m : nat => G IR x m[*]G IR y m)
   (CS_seq_mult Q_as_COrdField _ _ (CS_proof _ (G_as_CauchySeq IR x))
      (CS_proof _ (G_as_CauchySeq IR y))).
Proof.
 intros.
 apply not_ap_imp_eq.
 simpl in |- *.
 apply Eq_alt_2_2.
 intros.
 unfold CS_seq at 1 in |- *.
 unfold CS_seq in |- *.
 cut (SeqLimit (inj_Q_G_as_CauchySeq IR x) x).
  intro H0.
  cut (SeqLimit (inj_Q_G_as_CauchySeq IR y) y).
   intro H1.
   cut (SeqLimit (inj_Q_G_as_CauchySeq IR (x[*]y)) (x[*]y)).
    intro H2.
    case (CS_seq_bounded Q_as_COrdField (G IR y) (CS_seq_G IR y)).
    intro K.
    set (H3 := True) in *. (* dummy *)
    intros H4 H5.
    case H5.
    intro M1.
    intro H6.
    case (nonarchemaedian_bound_for_Lim _ (inj_Q_G_as_CauchySeq IR x)).
    intro L.
    set (H7 := True) in *. (* dummy *)
    intros H8 H9.
    cut (Twelve[*]inj_Q IR K[#][0]).
     intro H10.
     cut (Twelve[*]L[#][0]).
      intro H11.
      red in H0.
      case (H0 (inj_Q IR e[/] Twelve[*]inj_Q IR K[//]H10)).
       apply div_resp_pos.
        apply mult_resp_pos.
         apply pos_nring_S.
        apply less_wdl with (x := inj_Q IR [0]).
         apply inj_Q_less.
         apply leEq_not_eq.
          apply (AbsSmall_nonneg Q_as_COrdField K (G IR y M1)).
          apply H6.
          constructor.
         apply less_imp_ap; auto.
        simpl in |- *.
        rational.
       apply less_wdl with (x := inj_Q IR [0]).
        apply inj_Q_less.
        assumption.
       simpl in |- *.
       rational.
      intro N1.
      intro H12.
      red in H1.
      case (H1 (inj_Q IR e[/] Twelve[*]L[//]H11)).
       apply div_resp_pos.
        apply mult_resp_pos.
         apply pos_nring_S.
        assumption.
       apply less_wdl with (x := inj_Q IR [0]).
        apply inj_Q_less.
        assumption.
       simpl in |- *.
       rational.
      intro N2.
      intro H13.
      red in H2.
      case (H2 (inj_Q IR e [/]TwoNZ)).
       apply div_resp_pos.
        apply pos_two.
       apply less_wdl with (x := inj_Q IR [0]).
        apply inj_Q_less.
        assumption.
       simpl in |- *.
       rational.
      intro N3.
      intro H14.
      exists (N1 + (N2 + (N3 + M1))).
      intros.
      apply (AbsSmall_inj_Q IR).
      apply AbsSmall_wdr_unfolded with (y := inj_Q IR (G IR (x[*]y) m)[-]
        inj_Q IR (G IR x m)[*]inj_Q IR (G IR y m)).
       rstepr (inj_Q IR (G IR (x[*]y) m)[-]x[*]y[+]x[*](y[-]inj_Q IR (G IR y m))[+]
         inj_Q IR (G IR y m)[*](x[-]inj_Q IR (G IR x m))).
       rstepl (inj_Q IR e [/]TwoNZ[+]Three[*](L[*](inj_Q IR e[/] Twelve[*]L[//]H11))[+]
         Three[*](inj_Q IR K[*](inj_Q IR e[/] Twelve[*]inj_Q IR K[//]H10))).
       apply AbsSmall_plus.
        apply AbsSmall_plus.
         unfold inj_Q_G_as_CauchySeq in H14.
         unfold CS_seq at 1 in H14.
         apply H14.
         apply le_trans with (m := N1 + (N2 + (N3 + M1))).
          rewrite -> plus_permute with (m := N3).
          rewrite -> plus_permute with (m := N3).
          apply le_plus_l.
         assumption.
        apply AbsSmall_mult.
         apply AbsSmall_wdr_unfolded with (y := Lim (inj_Q_G_as_CauchySeq IR x)).
          assumption.
         apply eq_symmetric_unfolded.
         apply SeqLimit_unique.
         apply x_is_SeqLimit_G.
        apply AbsSmall_minus.
        unfold inj_Q_G_as_CauchySeq in H13.
        unfold CS_seq at 1 in H13.
        apply H13.
        apply le_trans with (m := N1 + (N2 + (N3 + M1))).
         rewrite ->  plus_permute with (m := N2).
         apply le_plus_l.
        assumption.
       apply AbsSmall_mult.
        apply inj_Q_AbsSmall.
        apply H6.
        apply le_trans with (m := N1 + (N2 + (N3 + M1))).
         rewrite -> plus_comm with (m := M1).
         rewrite -> plus_permute with (m := M1).
         rewrite -> plus_permute with (m := M1).
         apply le_plus_l.
        assumption.
       apply AbsSmall_minus.
       unfold inj_Q_G_as_CauchySeq in H12.
       unfold CS_seq at 1 in H12.
       apply H12.
       apply le_trans with (m := N1 + (N2 + (N3 + M1))).
        apply le_plus_l.
       assumption.
      apply eq_transitive_unfolded with (y := inj_Q IR (G IR (x[*]y) m)[-]inj_Q IR (G IR x m[*]G IR y m)).
       apply cg_minus_wd.
        apply eq_reflexive_unfolded.
       apply eq_symmetric_unfolded.
       apply inj_Q_mult.
      apply eq_symmetric_unfolded.
      apply inj_Q_minus.
     apply Greater_imp_ap.
     apply mult_resp_pos.
      apply pos_nring_S.
     assumption.
    apply Greater_imp_ap.
    apply mult_resp_pos.
     apply pos_nring_S.
    apply less_wdl with (x := inj_Q IR [0]).
     apply inj_Q_less.
     apply leEq_not_eq.
      apply (AbsSmall_nonneg Q_as_COrdField K (G IR y M1)).
      apply H6.
      constructor.
     apply less_imp_ap; auto.
    simpl in |- *.
    rational.
   apply x_is_SeqLimit_G.
  apply x_is_SeqLimit_G.
 apply x_is_SeqLimit_G.
Qed.




Section Concrete_iso_between_Creals.

Variables R1 R2 : CReals.


Lemma image_Cauchy12 :
 forall x : R1, Cauchy_prop (fun n : nat => inj_Q R2 (G R1 x n)).
Proof.
 intros.
 change (Cauchy_prop (fun n : nat => inj_Q R2 (CS_seq Q_as_COrdField (G_as_CauchySeq R1 x) n)))
   in |- *.
 apply inj_Q_Cauchy.
Qed.

Lemma image_Cauchy21 :
 forall y : R2, Cauchy_prop (fun n : nat => inj_Q R1 (G R2 y n)).
Proof.
 intros.
 change (Cauchy_prop (fun n : nat => inj_Q R1 (CS_seq Q_as_COrdField (G_as_CauchySeq R2 y) n)))
   in |- *.
 apply inj_Q_Cauchy.
Qed.

Definition image_G_as_CauchySeq12 (x : R1) :=
  Build_CauchySeq R2 (fun n : nat => inj_Q R2 (G R1 x n)) (image_Cauchy12 x).


Definition image_G_as_CauchySeq21 (y : R2) :=
  Build_CauchySeq R1 (fun n : nat => inj_Q R1 (G R2 y n)) (image_Cauchy21 y).

Definition f12 (x : R1) := Lim (image_G_as_CauchySeq12 x).
Definition g21 (y : R2) := Lim (image_G_as_CauchySeq21 y).

           (*------- ISO FROM R1 TO R2 -------*)

Theorem f12_is_inverse_g21 : forall y : R2, y[=]f12 (g21 y).
Proof.
 intro.
 unfold f12 in |- *.
 cut (y[=]Lim (inj_Q_G_as_CauchySeq R2 y)).
  intro.
  apply eq_transitive_unfolded with (y := Lim (inj_Q_G_as_CauchySeq R2 y)).
   assumption.
  apply Lim_well_def.
  unfold inj_Q_G_as_CauchySeq in |- *.
  unfold image_G_as_CauchySeq12 in |- *.
  change ((Build_CauchySeq R2 (fun m : nat => inj_Q R2 (CS_seq Q_as_COrdField (G_as_CauchySeq R2 y) m))
    (CS_seq_inj_Q_G R2 y) :R_COrdField R2)[=] Build_CauchySeq R2 (fun n : nat =>
      inj_Q R2 (CS_seq Q_as_COrdField (G_as_CauchySeq R1 (g21 y)) n))
        (image_Cauchy12 (g21 y))) in |- *.
  change ((Build_CauchySeq R2 (fun m : nat => inj_Q R2 (CS_seq Q_as_COrdField (G_as_CauchySeq R2 y) m))
    (inj_Q_Cauchy R2 (G_as_CauchySeq R2 y)) :R_COrdField R2)[=] Build_CauchySeq R2 (fun n : nat =>
      inj_Q R2 (CS_seq Q_as_COrdField (G_as_CauchySeq R1 (g21 y)) n))
        (inj_Q_Cauchy R2 (G_as_CauchySeq R1 (g21 y)))) in |- *.
  apply inj_seq_well_def with (g := G_as_CauchySeq R2 y) (h := G_as_CauchySeq R1 (g21 y)).
  apply inj_Q_one_one with (IR := R1).
  change ((Build_CauchySeq R1 (fun m : nat => inj_Q R1 (G R2 y m)) (image_Cauchy21 y)
    :R_COrdField R1)[=] Build_CauchySeq R1 (fun n : nat => inj_Q R1 (G R1 (g21 y) n))
      (CS_seq_inj_Q_G R1 (g21 y))) in |- *.
  change ((image_G_as_CauchySeq21 y:R_COrdField R1)[=] inj_Q_G_as_CauchySeq R1 (g21 y)) in |- *.
  apply Lim_one_one with (IR := R1).
  apply eq_transitive_unfolded with (y := g21 y).
   apply eq_reflexive_unfolded.
  apply SeqLimit_unique.
  apply x_is_SeqLimit_G.
 apply SeqLimit_unique.
 apply x_is_SeqLimit_G.
Qed.


Theorem f12_is_surjective : map_is_surjective R1 R2 f12.
Proof.
 intro.
 exists (g21 y).
 apply f12_is_inverse_g21.
Qed.



Theorem f12_strong_ext : fun_strext f12.
Proof.
 intros.
 red in |- *.
 unfold f12 in |- *.
 intros x y H.
 case (ap_imp_less R2 (Lim (image_G_as_CauchySeq12 x)) (Lim (image_G_as_CauchySeq12 y)) H).
  intro.
  apply less_imp_ap.
  apply less_wdl with (x := Lim (inj_Q_G_as_CauchySeq R1 x)).
   apply less_wdr with (y := Lim (inj_Q_G_as_CauchySeq R1 y)).
    apply Lim_pres_less.
    unfold inj_Q_G_as_CauchySeq in |- *.
    change ((Build_CauchySeq R1 (fun m : nat => inj_Q R1 (CS_seq Q_as_COrdField (G_as_CauchySeq R1 x) m))
      (inj_Q_Cauchy R1 (G_as_CauchySeq R1 x)) :R_COrdField R1)[<] Build_CauchySeq R1 (fun n : nat =>
        inj_Q R1 (CS_seq Q_as_COrdField (G_as_CauchySeq R1 y) n))
          (inj_Q_Cauchy R1 (G_as_CauchySeq R1 y))) in |- *.
    apply inj_seq_less.
    apply less_inj_seq with (IR := R2).
    change ((image_G_as_CauchySeq12 x:R_COrdField R2)[<]
      (image_G_as_CauchySeq12 y:R_COrdField R2)) in |- *.
    apply less_pres_Lim.
    assumption.
   apply eq_symmetric_unfolded.
   apply SeqLimit_unique.
   apply x_is_SeqLimit_G.
  apply eq_symmetric_unfolded.
  apply SeqLimit_unique.
  apply x_is_SeqLimit_G.
 intro.
 apply Greater_imp_ap.
 apply less_wdl with (x := Lim (inj_Q_G_as_CauchySeq R1 y)).
  apply less_wdr with (y := Lim (inj_Q_G_as_CauchySeq R1 x)).
   apply Lim_pres_less.
   unfold inj_Q_G_as_CauchySeq in |- *.
   change ((Build_CauchySeq R1 (fun m : nat => inj_Q R1 (CS_seq Q_as_COrdField (G_as_CauchySeq R1 y) m))
     (inj_Q_Cauchy R1 (G_as_CauchySeq R1 y)) :R_COrdField R1)[<] Build_CauchySeq R1 (fun n : nat =>
       inj_Q R1 (CS_seq Q_as_COrdField (G_as_CauchySeq R1 x) n))
         (inj_Q_Cauchy R1 (G_as_CauchySeq R1 x))) in |- *.
   apply inj_seq_less.
   apply less_inj_seq with (IR := R2).
   change ((image_G_as_CauchySeq12 y:R_COrdField R2)[<]
     (image_G_as_CauchySeq12 x:R_COrdField R2)) in |- *.
   apply less_pres_Lim.
   assumption.
  apply eq_symmetric_unfolded.
  apply SeqLimit_unique.
  apply x_is_SeqLimit_G.
 apply eq_symmetric_unfolded.
 apply SeqLimit_unique.
 apply x_is_SeqLimit_G.
Qed.

Theorem f12_pres_less :
 fun_pres_relation R1 R2 f12 (cof_less (c:=R1)) (cof_less (c:=R2)).
Proof.
 red in |- *.
 intros.
 unfold f12 in |- *.
 apply Lim_pres_less.
 unfold image_G_as_CauchySeq12 in |- *.
 change ((Build_CauchySeq R2 (fun m : nat => inj_Q R2 (CS_seq Q_as_COrdField (G_as_CauchySeq R1 x) m))
   (inj_Q_Cauchy R2 (G_as_CauchySeq R1 x)) :R_COrdField R2)[<] Build_CauchySeq R2 (fun n : nat =>
     inj_Q R2 (CS_seq Q_as_COrdField (G_as_CauchySeq R1 y) n))
       (inj_Q_Cauchy R2 (G_as_CauchySeq R1 y))) in |- *.
 apply inj_seq_less.
 apply less_inj_seq with (IR := R1).
 change ((inj_Q_G_as_CauchySeq R1 x:R_COrdField R1)[<]
   (inj_Q_G_as_CauchySeq R1 y:R_COrdField R1)) in |- *.
 apply less_pres_Lim.
 apply less_wdl with (x := x).
  apply less_wdr with (y := y).
   assumption.
  apply SeqLimit_unique.
  apply x_is_SeqLimit_G.
 apply SeqLimit_unique.
 apply x_is_SeqLimit_G.
Qed.


Theorem f12_pres_plus :
 fun_pres_bin_fun R1 R2 f12 (csg_op (c:=R1)) (csg_op (c:=R2)).
Proof.
 red in |- *.
 intros.
 unfold f12 in |- *.
 apply eq_transitive_unfolded with (y := Lim ((image_G_as_CauchySeq12 x:R_COrdField R2)[+]
   image_G_as_CauchySeq12 y)).
  apply Lim_well_def.
  unfold image_G_as_CauchySeq12 in |- *.
  apply eq_transitive_unfolded with (S := R_COrdField R2:CSetoid)
    (y := Build_CauchySeq R2 (fun m : nat => inj_Q R2 (G R1 x m[+]G R1 y m)) (inj_Q_Cauchy R2
      (Build_CauchySeq Q_as_COrdField (fun m : nat => G R1 x m[+]G R1 y m)
        (CS_seq_plus Q_as_COrdField (fun n : nat => G R1 x n) (fun n : nat => G R1 y n) (CS_seq_G R1 x)
          (CS_seq_G R1 y)))) :R_COrdField R2).
   change ((Build_CauchySeq R2 (fun n : nat =>
     inj_Q R2 (CS_seq Q_as_COrdField (G_as_CauchySeq R1 (x[+]y)) n))
       (inj_Q_Cauchy R2 (G_as_CauchySeq R1 (x[+]y))) :R_COrdField R2)[=] Build_CauchySeq R2
         (fun m : nat => inj_Q R2 (CS_seq Q_as_COrdField (Build_CauchySeq Q_as_COrdField
           (fun m : nat => G R1 x m[+]G R1 y m) (CS_seq_plus Q_as_COrdField (fun n : nat => G R1 x n)
             (fun n : nat => G R1 y n) (CS_seq_G R1 x) ( CS_seq_G R1 y))) m)) (inj_Q_Cauchy R2
               (Build_CauchySeq Q_as_COrdField (fun m : nat => G R1 x m[+]G R1 y m)
                 (CS_seq_plus Q_as_COrdField (fun n : nat => G R1 x n)
                   (fun n : nat => G R1 y n) (CS_seq_G R1 x) ( CS_seq_G R1 y))))) in |- *.
   apply inj_seq_well_def.
   unfold G_as_CauchySeq in |- *.
   apply G_pres_plus.
  (* Cauchy inj_Q plus *)
  apply not_ap_imp_eq.
  apply Eq_alt_2_2 with (x := Build_CauchySeq R2 (fun m : nat => inj_Q R2 (G R1 x m[+]G R1 y m))
    (inj_Q_Cauchy R2 (Build_CauchySeq Q_as_COrdField (fun m : nat => G R1 x m[+]G R1 y m)
      (CS_seq_plus Q_as_COrdField (fun n : nat => G R1 x n) (fun n : nat => G R1 y n) (CS_seq_G R1 x)
        (CS_seq_G R1 y)))) :R_COrdField R2) (y := Build_CauchySeq R2
          (fun m : nat => inj_Q R2 (G R1 x m)[+]inj_Q R2 (G R1 y m))
            (CS_seq_plus R2 (fun n : nat => inj_Q R2 (G R1 x n)) (fun n : nat => inj_Q R2 (G R1 y n)) (
              image_Cauchy12 x) (image_Cauchy12 y)) :R_COrdField R2).
  intros.
  exists 0.
  intros.
  unfold CS_seq in |- *.
  apply AbsSmall_wdr_unfolded with (y := [0]:R2).
   split.
    rstepr ([--]([0]:R2)).
    apply inv_resp_leEq.
    apply less_leEq.
    assumption.
   apply less_leEq.
   assumption.
  apply cg_cancel_rht with (x := inj_Q R2 (G R1 x m)[+]inj_Q R2 (G R1 y m)).
  astepl (inj_Q R2 (G R1 x m)[+]inj_Q R2 (G R1 y m)).
  apply eq_transitive_unfolded with (y := inj_Q R2 (G R1 x m[+]G R1 y m)).
   apply eq_symmetric_unfolded.
   apply inj_Q_plus.
  apply cg_cancel_mixed.
 (* End of Cauchy inj_Q plus *)
 apply Lim_pres_plus.
Qed.



Theorem f12_pres_mult :
 fun_pres_bin_fun R1 R2 f12 (cr_mult (c:=R1)) (cr_mult (c:=R2)).
Proof.
 red in |- *.
 intros.
 unfold f12 in |- *.
 apply eq_transitive_unfolded with (y := Lim ((image_G_as_CauchySeq12 x:R_COrdField R2)[*]
   image_G_as_CauchySeq12 y)).
  apply Lim_well_def.
  unfold image_G_as_CauchySeq12 in |- *.
  apply eq_transitive_unfolded with (S := R_COrdField R2:CSetoid)
    (y := Build_CauchySeq R2 (fun m : nat => inj_Q R2 (G R1 x m[*]G R1 y m)) (inj_Q_Cauchy R2
      (Build_CauchySeq Q_as_COrdField (fun m : nat => G R1 x m[*]G R1 y m)
        (CS_seq_mult Q_as_COrdField _ _ (CS_proof _ (G_as_CauchySeq R1 x))
          (CS_proof _ (G_as_CauchySeq R1 y))))) :R_COrdField R2).
   change ((Build_CauchySeq R2 (fun n : nat =>
     inj_Q R2 (CS_seq Q_as_COrdField (G_as_CauchySeq R1 (x[*]y)) n))
       (inj_Q_Cauchy R2 (G_as_CauchySeq R1 (x[*]y))) :R_COrdField R2)[=] Build_CauchySeq R2
         (fun m : nat => inj_Q R2 (CS_seq Q_as_COrdField (Build_CauchySeq Q_as_COrdField
           (fun m : nat => G R1 x m[*]G R1 y m) (CS_seq_mult Q_as_COrdField _ _
             (CS_proof _ (G_as_CauchySeq R1 x)) (CS_proof _ (G_as_CauchySeq R1 y)))) m))
               (inj_Q_Cauchy R2 (Build_CauchySeq Q_as_COrdField (fun m : nat => G R1 x m[*]G R1 y m)
                 (CS_seq_mult Q_as_COrdField _ _ (CS_proof _ (G_as_CauchySeq R1 x))
                   (CS_proof _ (G_as_CauchySeq R1 y)))))) in |- *.
   apply inj_seq_well_def.
   unfold G_as_CauchySeq in |- *.
   change ((Build_CauchySeq Q_as_COrdField (fun m : nat => G R1 (x[*]y) m) (CS_seq_G R1 (x[*]y))
     :R_COrdField Q_as_COrdField)[=] Build_CauchySeq Q_as_COrdField (fun m : nat => G R1 x m[*]G R1 y m)
       (CS_seq_mult Q_as_COrdField _ _ (CS_proof _ (G_as_CauchySeq R1 x))
         (CS_proof _ (G_as_CauchySeq R1 y)))) in |- *.
   apply G_pres_mult.
  (* Cauchy inj_Q mult *)
  apply not_ap_imp_eq.
  apply Eq_alt_2_2 with (x := Build_CauchySeq R2 (fun m : nat => inj_Q R2 (G R1 x m[*]G R1 y m))
    (inj_Q_Cauchy R2 (Build_CauchySeq Q_as_COrdField (fun m : nat => G R1 x m[*]G R1 y m)
      (CS_seq_mult Q_as_COrdField _ _ (CS_proof Q_as_COrdField (G_as_CauchySeq R1 x))
        (CS_proof Q_as_COrdField (G_as_CauchySeq R1 y)))))) (y := Build_CauchySeq R2
          (fun m : nat => inj_Q R2 (G R1 x m)[*]inj_Q R2 (G R1 y m))
            (CS_seq_mult R2 _ _ (CS_proof R2 (image_G_as_CauchySeq12 x))
              (CS_proof R2 (image_G_as_CauchySeq12 y)))).
  intros.
  exists 0.
  intros.
  unfold CS_seq in |- *.
  apply AbsSmall_wdr_unfolded with (y := [0]:R2).
   split.
    rstepr ([--]([0]:R2)).
    apply inv_resp_leEq.
    apply less_leEq.
    assumption.
   apply less_leEq.
   assumption.
  apply cg_cancel_rht with (x := inj_Q R2 (G R1 x m)[*]inj_Q R2 (G R1 y m)).
  astepl (inj_Q R2 (G R1 x m)[*]inj_Q R2 (G R1 y m)).
  apply eq_transitive_unfolded with (y := inj_Q R2 (G R1 x m[*]G R1 y m)).
   apply eq_symmetric_unfolded.
   apply inj_Q_mult.
  apply cg_cancel_mixed.
 (* End of Cauchy inj_Q mult *)
 apply Lim_pres_mult.
Qed.


        (*--------- ISO FROM R2 TO R1 ---------*)
Theorem g21_is_inverse_f12 : forall y : R1, y[=]g21 (f12 y).
Proof.
 intro.
 unfold g21 in |- *.
 cut (y[=]Lim (inj_Q_G_as_CauchySeq R1 y)).
  intro.
  apply eq_transitive_unfolded with (y := Lim (inj_Q_G_as_CauchySeq R1 y)).
   assumption.
  apply Lim_well_def.
  unfold inj_Q_G_as_CauchySeq in |- *.
  unfold image_G_as_CauchySeq21 in |- *.
  change ((Build_CauchySeq R1 (fun m : nat => inj_Q R1 (CS_seq Q_as_COrdField (G_as_CauchySeq R1 y) m))
    (CS_seq_inj_Q_G R1 y) :R_COrdField R1)[=] Build_CauchySeq R1 (fun n : nat =>
      inj_Q R1 (CS_seq Q_as_COrdField (G_as_CauchySeq R2 (f12 y)) n))
        (image_Cauchy21 (f12 y))) in |- *.
  change ((Build_CauchySeq R1 (fun m : nat => inj_Q R1 (CS_seq Q_as_COrdField (G_as_CauchySeq R1 y) m))
    (inj_Q_Cauchy R1 (G_as_CauchySeq R1 y)) :R_COrdField R1)[=] Build_CauchySeq R1 (fun n : nat =>
      inj_Q R1 (CS_seq Q_as_COrdField (G_as_CauchySeq R2 (f12 y)) n))
        (inj_Q_Cauchy R1 (G_as_CauchySeq R2 (f12 y)))) in |- *.
  apply inj_seq_well_def with (g := G_as_CauchySeq R1 y) (h := G_as_CauchySeq R2 (f12 y)).
  apply inj_Q_one_one with (IR := R2).
  change ((image_G_as_CauchySeq12 y:R_COrdField R2)[=] inj_Q_G_as_CauchySeq R2 (f12 y)) in |- *.
  apply Lim_one_one with (IR := R2).
  apply eq_transitive_unfolded with (y := f12 y).
   change (f12 y[=]f12 y) in |- *.
   apply eq_reflexive_unfolded.
  apply SeqLimit_unique.
  apply x_is_SeqLimit_G.
 apply SeqLimit_unique.
 apply x_is_SeqLimit_G.
Qed.


Theorem g21_is_surjective : map_is_surjective R2 R1 g21.
Proof.
 intro.
 exists (f12 y).
 apply g21_is_inverse_f12.
Qed.



Theorem g21_strong_ext : fun_strext g21.
Proof.
 intros.
 red in |- *.
 unfold g21 in |- *.
 intros x y H.
 case (ap_imp_less R1 (Lim (image_G_as_CauchySeq21 x)) (Lim (image_G_as_CauchySeq21 y)) H).
  intro.
  apply less_imp_ap.
  apply less_wdl with (x := Lim (inj_Q_G_as_CauchySeq R2 x)).
   apply less_wdr with (y := Lim (inj_Q_G_as_CauchySeq R2 y)).
    apply Lim_pres_less.
    unfold inj_Q_G_as_CauchySeq in |- *.
    change ((Build_CauchySeq R2 (fun m : nat => inj_Q R2 (CS_seq Q_as_COrdField (G_as_CauchySeq R2 x) m))
      (inj_Q_Cauchy R2 (G_as_CauchySeq R2 x)) :R_COrdField R2)[<] Build_CauchySeq R2 (fun n : nat =>
        inj_Q R2 (CS_seq Q_as_COrdField (G_as_CauchySeq R2 y) n))
          (inj_Q_Cauchy R2 (G_as_CauchySeq R2 y))) in |- *.
    apply inj_seq_less.
    apply less_inj_seq with (IR := R1).
    change ((image_G_as_CauchySeq21 x:R_COrdField R1)[<]
      (image_G_as_CauchySeq21 y:R_COrdField R1)) in |- *.
    apply less_pres_Lim.
    assumption.
   apply eq_symmetric_unfolded.
   apply SeqLimit_unique.
   apply x_is_SeqLimit_G.
  apply eq_symmetric_unfolded.
  apply SeqLimit_unique.
  apply x_is_SeqLimit_G.
 intro.
 apply Greater_imp_ap.
 apply less_wdl with (x := Lim (inj_Q_G_as_CauchySeq R2 y)).
  apply less_wdr with (y := Lim (inj_Q_G_as_CauchySeq R2 x)).
   apply Lim_pres_less.
   unfold inj_Q_G_as_CauchySeq in |- *.
   change ((Build_CauchySeq R2 (fun m : nat => inj_Q R2 (CS_seq Q_as_COrdField (G_as_CauchySeq R2 y) m))
     (inj_Q_Cauchy R2 (G_as_CauchySeq R2 y)) :R_COrdField R2)[<] Build_CauchySeq R2 (fun n : nat =>
       inj_Q R2 (CS_seq Q_as_COrdField (G_as_CauchySeq R2 x) n))
         (inj_Q_Cauchy R2 (G_as_CauchySeq R2 x))) in |- *.
   apply inj_seq_less.
   apply less_inj_seq with (IR := R1).
   change ((image_G_as_CauchySeq21 y:R_COrdField R1)[<]
     (image_G_as_CauchySeq21 x:R_COrdField R1)) in |- *.
   apply less_pres_Lim.
   assumption.
  apply eq_symmetric_unfolded.
  apply SeqLimit_unique.
  apply x_is_SeqLimit_G.
 apply eq_symmetric_unfolded.
 apply SeqLimit_unique.
 apply x_is_SeqLimit_G.
Qed.

Theorem g21_pres_less :
 fun_pres_relation R2 R1 g21 (cof_less (c:=R2)) (cof_less (c:=R1)).
Proof.
 red in |- *.
 intros.
 unfold g21 in |- *.
 apply Lim_pres_less.
 unfold image_G_as_CauchySeq21 in |- *.
 change ((Build_CauchySeq R1 (fun m : nat => inj_Q R1 (CS_seq Q_as_COrdField (G_as_CauchySeq R2 x) m))
   (inj_Q_Cauchy R1 (G_as_CauchySeq R2 x)) :R_COrdField R1)[<] Build_CauchySeq R1 (fun n : nat =>
     inj_Q R1 (CS_seq Q_as_COrdField (G_as_CauchySeq R2 y) n))
       (inj_Q_Cauchy R1 (G_as_CauchySeq R2 y))) in |- *.
 apply inj_seq_less.
 apply less_inj_seq with (IR := R2).
 change ((inj_Q_G_as_CauchySeq R2 x:R_COrdField R2)[<]
   (inj_Q_G_as_CauchySeq R2 y:R_COrdField R2)) in |- *.
 apply less_pres_Lim.
 apply less_wdl with (x := x).
  apply less_wdr with (y := y).
   assumption.
  apply SeqLimit_unique.
  apply x_is_SeqLimit_G.
 apply SeqLimit_unique.
 apply x_is_SeqLimit_G.
Qed.


Theorem g21_pres_plus :
 fun_pres_bin_fun R2 R1 g21 (csg_op (c:=R2)) (csg_op (c:=R1)).
Proof.
 red in |- *.
 intros.
 unfold g21 in |- *.
 apply eq_transitive_unfolded with (y := Lim ((image_G_as_CauchySeq21 x:R_COrdField R1)[+]
   image_G_as_CauchySeq21 y)).
  apply Lim_well_def.
  unfold image_G_as_CauchySeq21 in |- *.
  apply eq_transitive_unfolded with (S := R_COrdField R1:CSetoid)
    (y := Build_CauchySeq R1 (fun m : nat => inj_Q R1 (G R2 x m[+]G R2 y m)) (inj_Q_Cauchy R1
      (Build_CauchySeq Q_as_COrdField (fun m : nat => G R2 x m[+]G R2 y m)
        (CS_seq_plus Q_as_COrdField (fun n : nat => G R2 x n) (fun n : nat => G R2 y n) (CS_seq_G R2 x)
          (CS_seq_G R2 y)))) :R_COrdField R1).
   change ((Build_CauchySeq R1 (fun n : nat =>
     inj_Q R1 (CS_seq Q_as_COrdField (G_as_CauchySeq R2 (x[+]y)) n))
       (inj_Q_Cauchy R1 (G_as_CauchySeq R2 (x[+]y))) :R_COrdField R1)[=] Build_CauchySeq R1
         (fun m : nat => inj_Q R1 (CS_seq Q_as_COrdField (Build_CauchySeq Q_as_COrdField
           (fun m : nat => G R2 x m[+]G R2 y m) (CS_seq_plus Q_as_COrdField (fun n : nat => G R2 x n)
             (fun n : nat => G R2 y n) (CS_seq_G R2 x) ( CS_seq_G R2 y))) m)) (inj_Q_Cauchy R1
               (Build_CauchySeq Q_as_COrdField (fun m : nat => G R2 x m[+]G R2 y m)
                 (CS_seq_plus Q_as_COrdField (fun n : nat => G R2 x n)
                   (fun n : nat => G R2 y n) (CS_seq_G R2 x) ( CS_seq_G R2 y))))) in |- *.
   apply inj_seq_well_def.
   unfold G_as_CauchySeq in |- *.
   apply G_pres_plus.
  (* Cauchy inj_Q plus *)
  apply not_ap_imp_eq.
  apply Eq_alt_2_2 with (x := Build_CauchySeq R1 (fun m : nat => inj_Q R1 (G R2 x m[+]G R2 y m))
    (inj_Q_Cauchy R1 (Build_CauchySeq Q_as_COrdField (fun m : nat => G R2 x m[+]G R2 y m)
      (CS_seq_plus Q_as_COrdField (fun n : nat => G R2 x n) (fun n : nat => G R2 y n) (CS_seq_G R2 x)
        (CS_seq_G R2 y)))) :R_COrdField R1) (y := Build_CauchySeq R1
          (fun m : nat => inj_Q R1 (G R2 x m)[+]inj_Q R1 (G R2 y m))
            (CS_seq_plus R1 (fun n : nat => inj_Q R1 (G R2 x n)) (fun n : nat => inj_Q R1 (G R2 y n)) (
              image_Cauchy21 x) (image_Cauchy21 y)) :R_COrdField R1).
  intros.
  exists 0.
  intros.
  unfold CS_seq in |- *.
  apply AbsSmall_wdr_unfolded with (y := [0]:R1).
   split.
    rstepr ([--]([0]:R1)).
    apply inv_resp_leEq.
    apply less_leEq.
    assumption.
   apply less_leEq.
   assumption.
  apply cg_cancel_rht with (x := inj_Q R1 (G R2 x m)[+]inj_Q R1 (G R2 y m)).
  astepl (inj_Q R1 (G R2 x m)[+]inj_Q R1 (G R2 y m)).
  apply eq_transitive_unfolded with (y := inj_Q R1 (G R2 x m[+]G R2 y m)).
   apply eq_symmetric_unfolded.
   apply inj_Q_plus.
  apply cg_cancel_mixed.
 (* End of Cauchy inj_Q plus *)
 apply Lim_pres_plus.
Qed.



Theorem g21_pres_mult :
 fun_pres_bin_fun R2 R1 g21 (cr_mult (c:=R2)) (cr_mult (c:=R1)).
Proof.
 red in |- *.
 intros.
 unfold g21 in |- *.
 apply eq_transitive_unfolded with (y := Lim ((image_G_as_CauchySeq21 x:R_COrdField R1)[*]
   image_G_as_CauchySeq21 y)).
  apply Lim_well_def.
  unfold image_G_as_CauchySeq21 in |- *.
  apply eq_transitive_unfolded with (S := R_COrdField R1:CSetoid)
    (y := Build_CauchySeq R1 (fun m : nat => inj_Q R1 (G R2 x m[*]G R2 y m)) (inj_Q_Cauchy R1
      (Build_CauchySeq Q_as_COrdField (fun m : nat => G R2 x m[*]G R2 y m)
        (CS_seq_mult Q_as_COrdField _ _ (CS_proof _ (G_as_CauchySeq R2 x))
          (CS_proof _ (G_as_CauchySeq R2 y))))) :R_COrdField R1).
   change ((Build_CauchySeq R1 (fun n : nat =>
     inj_Q R1 (CS_seq Q_as_COrdField (G_as_CauchySeq R2 (x[*]y)) n))
       (inj_Q_Cauchy R1 (G_as_CauchySeq R2 (x[*]y))) :R_COrdField R1)[=] Build_CauchySeq R1
         (fun m : nat => inj_Q R1 (CS_seq Q_as_COrdField (Build_CauchySeq Q_as_COrdField
           (fun m : nat => G R2 x m[*]G R2 y m) (CS_seq_mult Q_as_COrdField _ _
             (CS_proof _ (G_as_CauchySeq R2 x)) (CS_proof _ (G_as_CauchySeq R2 y)))) m))
               (inj_Q_Cauchy R1 (Build_CauchySeq Q_as_COrdField (fun m : nat => G R2 x m[*]G R2 y m)
                 (CS_seq_mult Q_as_COrdField _ _ (CS_proof _ (G_as_CauchySeq R2 x))
                   (CS_proof _ (G_as_CauchySeq R2 y)))))) in |- *.
   apply inj_seq_well_def.
   unfold G_as_CauchySeq in |- *.
   change ((Build_CauchySeq Q_as_COrdField (fun m : nat => G R2 (x[*]y) m) (CS_seq_G R2 (x[*]y))
     :R_COrdField Q_as_COrdField)[=] Build_CauchySeq Q_as_COrdField (fun m : nat => G R2 x m[*]G R2 y m)
       (CS_seq_mult Q_as_COrdField _ _ (CS_proof _ (G_as_CauchySeq R2 x))
         (CS_proof _ (G_as_CauchySeq R2 y)))) in |- *.
   apply G_pres_mult.
  (* Cauchy inj_Q mult *)
  apply not_ap_imp_eq.
  apply Eq_alt_2_2 with (x := Build_CauchySeq R1 (fun m : nat => inj_Q R1 (G R2 x m[*]G R2 y m))
    (inj_Q_Cauchy R1 (Build_CauchySeq Q_as_COrdField (fun m : nat => G R2 x m[*]G R2 y m)
      (CS_seq_mult Q_as_COrdField (G_as_CauchySeq R2 x) (G_as_CauchySeq R2 y)
        (CS_proof Q_as_COrdField (G_as_CauchySeq R2 x))
          (CS_proof Q_as_COrdField (G_as_CauchySeq R2 y)))))) (y := Build_CauchySeq R1
            (fun m : nat => inj_Q R1 (G R2 x m)[*]inj_Q R1 (G R2 y m))
              (CS_seq_mult R1 (image_G_as_CauchySeq21 x) (image_G_as_CauchySeq21 y)
                (CS_proof R1 (image_G_as_CauchySeq21 x)) (CS_proof R1 (image_G_as_CauchySeq21 y)))).
  intros.
  exists 0.
  intros.
  unfold CS_seq in |- *.
  apply AbsSmall_wdr_unfolded with (y := [0]:R1).
   split.
    rstepr ([--]([0]:R1)).
    apply inv_resp_leEq.
    apply less_leEq.
    assumption.
   apply less_leEq.
   assumption.
  apply cg_cancel_rht with (x := inj_Q R1 (G R2 x m)[*]inj_Q R1 (G R2 y m)).
  astepl (inj_Q R1 (G R2 x m)[*]inj_Q R1 (G R2 y m)).
  apply eq_transitive_unfolded with (y := inj_Q R1 (G R2 x m[*]G R2 y m)).
   apply eq_symmetric_unfolded.
   apply inj_Q_mult.
  apply cg_cancel_mixed.
 (* End of Cauchy inj_Q mult *)
 apply Lim_pres_mult.
Qed.

(* Building Homomorphisms out of f12 and g21 *)


Definition f12_as_Homomorphism :=
  simplified_Homomorphism R1 R2 f12 f12_strong_ext f12_pres_less
    f12_pres_plus f12_pres_mult f12_is_surjective.

Definition g21_as_Homomorphism :=
  simplified_Homomorphism R2 R1 g21 g21_strong_ext g21_pres_less
    g21_pres_plus g21_pres_mult g21_is_surjective.


Lemma f12_inverse_lft :
 map_is_id R2 (Compose R2 R1 R2 g21_as_Homomorphism f12_as_Homomorphism).
Proof.
 red in |- *.
 intros.
 simpl in |- *.
 apply eq_symmetric_unfolded.
 apply f12_is_inverse_g21.
Qed.

Lemma g21_inverse_rht :
 map_is_id R1 (Compose R1 R2 R1 f12_as_Homomorphism g21_as_Homomorphism).
Proof.
 red in |- *.
 intros.
 simpl in |- *.
 apply eq_symmetric_unfolded.
 apply g21_is_inverse_f12.
Qed.



Definition Canonic_Isomorphism_between_CReals :=
  Build_Isomorphism R1 R2 f12_as_Homomorphism g21_as_Homomorphism
    f12_inverse_lft g21_inverse_rht.

End Concrete_iso_between_Creals.
(* end hide *)
