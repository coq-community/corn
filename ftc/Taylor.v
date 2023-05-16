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

Require Export CoRN.ftc.TaylorLemma.

Opaque Min Max N_Deriv.

Section More_Taylor_Defs.

(**
** General case

The generalization to arbitrary intervals just needs a few more definitions.

%\begin{convention}% Let [I] be a proper interval, [F:PartIR] and
[a,b:IR] be points of [I].
%\end{convention}%
*)

Variable I : interval.
Hypothesis pI : proper I.

Variable F : PartIR.

(* begin show *)
Let deriv_Sn b n Hf :=
 N_Deriv _ pI (S n) F Hf{*} [-C-] ([1][/] _[//]nring_fac_ap_zero _ n) {*} ( [-C-]b{-}FId) {^}n.
(* end show *)

Variables a b : IR.
Hypothesis Ha : I a.
Hypothesis Hb : I b.

(* begin show *)
Let fi n Hf i Hi :=
  N_Deriv _ pI _ _ (le_imp_Diffble_n _ _ _ _ (lt_n_Sm_le i n Hi) F Hf).

Let funct_i n Hf i Hi :=
  [-C-] (fi n Hf i Hi a Ha[/] _[//]nring_fac_ap_zero _ i) {*} (FId{-} [-C-]a) {^}i.
(* end show *)

Definition Taylor_Seq' n Hf := FSumx _ (funct_i n Hf).

(* begin hide *)
Lemma TaylorB : forall n Hf, Dom (Taylor_Seq' n Hf) b.
Proof.
 repeat split.
 apply FSumx_pred'; repeat split.
Qed.
(* end hide *)

Definition Taylor_Rem n Hf := F b (Diffble_n_imp_inc _ _ _ _ Hf b Hb) [-]
 Taylor_Seq' n Hf b (TaylorB n Hf).

(* begin hide *)
Lemma Taylor_Sumx_lemma : forall n x z y y', (forall H, y 0 H [=] z) ->
  (forall i H H', y' i H' [=] y (S i) H) ->
  x[-]Sumx (G:=IR) (n:=S n) y [=] x[-]z[-]Sumx (G:=IR) (n:=n) y'.
Proof.
 intro; induction  n as [| n Hrecn].
  intros; simpl in |- *.
  astepl (x[-] ([0][+]z)).
  rational.
 intros.
 astepl (x[-] (Sumx (fun i (l : i < S n) => y i (Nat.lt_lt_succ_r _ _ l)) [+] y (S n) (Nat.lt_succ_diag_r (S n)))).
 rstepl (x[-]Sumx (fun i (l : i < S n) => y i (Nat.lt_lt_succ_r _ _ l)) [-] y (S n) (Nat.lt_succ_diag_r (S n))).
 astepr (x[-]z[-] (Sumx (fun i (l : i < n) => y' i (Nat.lt_lt_succ_r _ _ l)) [+]y' n (Nat.lt_succ_diag_r n))).
 rstepr (x[-]z[-]Sumx (fun i (l : i < n) => y' i (Nat.lt_lt_succ_r _ _ l)) [-] y' n (Nat.lt_succ_diag_r n)).
 algebra.
Qed.

Lemma Taylor_lemma_ap : forall n Hf Hf' Ha',
 Taylor_Rem n Hf'[-]deriv_Sn b n Hf a Ha'[*] (b[-]a) [#] [0] -> a [#] b.
Proof.
 intros. rename X into H.
 set (Hpred := Diffble_n_imp_inc _ _ _ _ Hf') in *.
 cut (Taylor_Rem n Hf'[-]Part _ _ Ha'[*] (b[-]a) [#] [0][-][0]).
  2: astepr ZeroR; auto.
 clear H; intros. rename X into H.
 elim (cg_minus_strext _ _ _ _ _ H); clear H; intro H.
  unfold Taylor_Rem, Taylor_Seq', funct_i in H.
  cut (Dom (FSumx n (fun i (Hi : i < n) => [-C-] (fi n Hf' (S i) (lt_n_S _ _ Hi) a Ha[/] _[//]
    nring_fac_ap_zero IR (S i)) {*} (FId{-} [-C-]a) {^}S i)) b).
   2: apply FSumx_pred'; repeat split.
  intro H0.
  cut (F b (Hpred b Hb) [-]F a (Hpred a Ha) [#] [0] or Part _ _ H0 [#] [0]). intro H1.
   elim H1; clear H H1; intro H.
    apply pfstrx with (Hx := Hpred a Ha) (Hy := Hpred b Hb).
    apply ap_symmetric_unfolded; apply zero_minus_apart; auto.
   cut (ext_fun_seq' (fun i (Hi : i < n) => [-C-]
     (fi n Hf' (S i) (lt_n_S _ _ Hi) a Ha[/] _[//]nring_fac_ap_zero IR (S i)) {*}
       (FId{-} [-C-]a) {^}S i)).
    2: red in |- *; repeat split.
   intro H1.
   cut (Sumx (fun i (Hi : i < n) => Part _ _ (FSumx_pred n _ H1 _ H0 i Hi)) [#]
     Sumx (fun i (Hi : i < n) => [0])). intro H2.
    2: eapply ap_wdl_unfolded.
     2: eapply ap_wdr_unfolded.
      2: apply H.
     2: apply eq_symmetric_unfolded; eapply eq_transitive_unfolded; [ apply sumx_const | algebra ].
    2: exact (FSumx_char _ _ _ _ H1).
   simpl in H2.
   cut (nat_less_n_fun (fun i (Hi : i < n) =>
     (fi n Hf' (S i) (lt_n_S _ _ Hi) a Ha[/] _[//]nring_fac_ap_zero IR (S i)) [*]
       (nexp IR i (b[+][--]a) [*] (b[+][--]a)))); intros.
    cut (nat_less_n_fun (fun i (Hi : i < n) => ([0]:IR))); intros.
     elim (Sumx_strext _ _ _ _ H3 H4 H2); clear H H0 H1 H2 H3 H4; intros N HN.
     elim HN; clear HN; intros HN H.
     cut (b[+][--]a [#] [0]). intro H3.
      2: eapply cring_mult_ap_zero_op; eapply cring_mult_ap_zero_op; apply H.
     apply ap_symmetric_unfolded; apply zero_minus_apart; auto.
    red in |- *; algebra.
   red in |- *; do 3 intro.
   rewrite H3; intros; unfold fi in |- *.
   apply mult_wdl.
   apply div_wd.
    2: algebra.
   apply Feq_imp_eq with I.
    apply Derivative_n_unique with pI (S j) F; apply N_Deriv_lemma.
   auto.
  apply cg_minus_strext.
  astepr ZeroR.
  apply ap_wdl_unfolded with (Part _ _ (Hpred b Hb) [-]Part _ _ (TaylorB n Hf')); auto.
  unfold Taylor_Seq', funct_i in |- *.
  cut (ext_fun_seq' (fun i Hi => [-C-] (fi n Hf' i Hi a Ha[/] _[//]nring_fac_ap_zero IR i) {*}
    (FId{-} [-C-]a) {^}i)). intro H1.
   apply eq_transitive_unfolded with (Part _ _ (Hpred b Hb) [-] Sumx (fun i Hi =>
     Part _ _ (FSumx_pred _ _ H1 b (TaylorB n Hf') i Hi))).
    apply cg_minus_wd.
     algebra.
    exact (FSumx_char _ _ _ _ H1).
   cut (ext_fun_seq' (fun i (Hi : i < n) => [-C-]
     (fi n Hf' (S i) (lt_n_S _ _ Hi) a Ha[/] _[//]nring_fac_ap_zero IR (S i)) {*}
       (FId{-} [-C-]a) {^}S i)). intro H2.
    apply eq_transitive_unfolded with (Part _ _ (Hpred b Hb) [-]Part _ _ (Hpred a Ha) [-] Sumx
      (fun i (Hi : i < n) => Part _ _ (FSumx_pred _ _ H2 b H0 i Hi))).
     2: apply cg_minus_wd.
      2: algebra.
     2: apply eq_symmetric_unfolded; exact (FSumx_char _ _ _ _ H2).
    apply Taylor_Sumx_lemma.
     intros; simpl in |- *.
     unfold fi in |- *.
     rstepr ((Part _ _ (Hpred a Ha) [/] [0][+][1][//]nring_fac_ap_zero IR 0) [*][1]).
     apply mult_wdl; apply div_wd.
      2: algebra.
     apply Feq_imp_eq with I.
      apply Derivative_n_unique with pI 0 F.
       apply N_Deriv_lemma.
      split; auto.
      split; auto.
      intros; simpl in |- *.
      apply Feq_reflexive; Included.
     auto.
    intros; simpl in |- *.
    apply mult_wdl; apply div_wd.
     2: algebra.
    unfold fi in |- *.
    apply Feq_imp_eq with I.
     apply Derivative_n_unique with pI (S i) F; apply N_Deriv_lemma; auto.
    auto.
   repeat split.
  repeat split.
 apply ap_symmetric_unfolded; apply zero_minus_apart.
 eapply cring_mult_ap_zero_op; apply H.
Qed.
(* end hide *)

Theorem Taylor' : forall n Hf Hf' e, [0] [<] e -> {c : IR | Compact (Min_leEq_Max a b) c |
 forall Hc, AbsIR (Taylor_Rem n Hf'[-]deriv_Sn b n Hf c Hc[*] (b[-]a)) [<=] e}.
Proof.
 intros. rename X into H.
 cut (Dom (deriv_Sn b n Hf) a). intro H0.
  2: repeat split.
  2: simpl in |- *; auto.
 elim (less_cotransitive_unfolded _ _ _ H (AbsIR (Taylor_Rem n Hf'[-]Part _ _ H0[*] (b[-]a)))).
  intros.
  cut (a [#] b). intro H1.
   clear a0 H0.
   cut (Diffble_I_n (ap_imp_Min_less_Max _ _ H1) (S n) F). intro H0.
    2: apply included_imp_Diffble_n with I pI; auto.
    cut (Diffble_I_n (ap_imp_Min_less_Max _ _ H1) n F). intro H2.
     2: apply le_imp_Diffble_I with (S n); auto.
    elim (Taylor_lemma a b H1 F (Diffble_n_imp_inc _ _ _ _ Hf b Hb) e H n H2 H0).
    intros c H3 H4.
    exists c; auto.
    intro.
    cut (Dom (n_deriv_I _ _ _ _ _ H0{*} [-C-] ([1][/] _[//]nring_fac_ap_zero _ n) {*}
      ( [-C-]b{-}FId) {^}n) c). intro H5.
     2: repeat split.
     2: apply n_deriv_inc; auto.
    eapply leEq_wdl.
     apply (H4 H5).
    unfold Taylor_rem, Taylor_Rem in |- *.
    apply AbsIR_wd; repeat apply cg_minus_wd.
      algebra.
     simpl in |- *.
     repeat first [ apply bin_op_wd_unfolded | apply mult_wd | apply div_wd
       | apply eq_reflexive_unfolded ].
      apply FSumx_wd; intros; simpl in |- *.
      apply mult_wdl.
      apply div_wd.
       2: algebra.
      apply eq_transitive_unfolded with (PartInt (ProjT1 (Diffble_I_n_imp_deriv_n _ _ _ _ _
        (le_imp_Diffble_I _ _ _ _ _ (lt_n_Sm_le _ _ (Nat.lt_lt_succ_r _ _ Hi)) _ H2)))
          a (compact_Min_lft _ _ (less_leEq _ _ _ (ap_imp_Min_less_Max _ _ H1)))).
       simpl in |- *; algebra.
      apply Feq_imp_eq with (Compact (less_leEq _ _ _ (ap_imp_Min_less_Max _ _ H1))).
       apply Derivative_I_n_unique with i F.
        apply projT2.
       unfold fi in |- *.
       elim (N_Deriv_lemma _ _ _ _ (le_imp_Diffble_n I pI i n (lt_n_Sm_le _ _ (Nat.lt_lt_succ_r _ _ Hi)) _ Hf'));
         intros incF0 H'.
       elim H'; intros Hinc derivF; clear H'.
       apply derivF.
       simpl in |- *; Included.
      apply compact_Min_lft.
     apply eq_transitive_unfolded with (PartInt (ProjT1 (Diffble_I_n_imp_deriv_n _ _ _ _ _
       (le_imp_Diffble_I _ _ _ _ _ (lt_n_Sm_le _ _ (Nat.lt_succ_diag_r n)) _ H2)))
         a (compact_Min_lft _ _ (less_leEq _ _ _ (ap_imp_Min_less_Max _ _ H1)))).
      simpl in |- *; algebra.
     apply Feq_imp_eq with (Compact (less_leEq _ _ _ (ap_imp_Min_less_Max _ _ H1))).
      apply Derivative_I_n_unique with n F.
       apply projT2.
      unfold fi in |- *.
      elim (N_Deriv_lemma _ _ _ _ (le_imp_Diffble_n I pI n n (lt_n_Sm_le _ _ (Nat.lt_succ_diag_r n)) _ Hf'));
        intros incF0 H'.
      elim H'; intros Hinc derivF; clear H'.
      apply derivF.
      simpl in |- *; Included.
     apply compact_Min_lft.
    simpl in |- *.
    repeat apply mult_wdl.
    apply Feq_imp_eq with (Compact (less_leEq _ _ _ (ap_imp_Min_less_Max _ _ H1))).
     apply Derivative_I_n_unique with (S n) F.
      apply Derivative_I_n_wdr with (n_deriv_I _ _ _ _ _ H0).
       apply Derivative_I_n_unique with n (n_deriv_I _ _ _ _ _
         (le_imp_Diffble_I _ _ _ _ _ (le_n_S _ _ (Nat.le_0_l n)) _ H0)).
        cut (forall HS HSn, Derivative_I_n (ap_imp_Min_less_Max _ _ H1) n
          (n_deriv_I _ _ (ap_imp_Min_less_Max _ _ H1) 1 F HS)
            (n_deriv_I _ _ (ap_imp_Min_less_Max _ _ H1) (S n) F HSn)); auto.
        cut (S n = n + 1); [ intro | rewrite plus_comm; auto ].
        rewrite H6.
        intros; apply n_deriv_plus.
       eapply Derivative_I_n_wdl.
        2: apply n_deriv_lemma.
       apply Derivative_I_unique with F.
        apply projT2.
       apply Derivative_I_wdl with (n_deriv_I _ _ _ _ _ (le_imp_Diffble_I _ _ _ _ _ (Nat.le_0_l _) F H0)).
        simpl in |- *.
        FEQ.
        apply (included_trans _ (Compact (less_leEq IR (Min a b) (Max a b) (ap_imp_Min_less_Max a b H1))) I); Included.
       apply n_Sn_deriv.
      apply n_deriv_lemma.
     elim (N_Deriv_lemma _ _ _ _ Hf); intros incF0 H'.
     elim H'; intros Hinc derivF; clear H'.
     apply derivF.
     simpl in |- *; Included.
    elim H5; clear H5; intros H6 H7.
    elim H6; clear H6; intros H5 H8.
    exact (n_deriv_inc' _ _ _ _ _ _ _ _ H5).
   Included.
  cut (Taylor_Rem n Hf'[-]Part _ _ H0[*] (b[-]a) [#] [0]).
   intro H1; exact (Taylor_lemma_ap _ _ _ _ H1).
  astepr ZeroR; apply AbsIR_cancel_ap_zero; apply Greater_imp_ap; auto.
 intro.
 exists a.
  apply compact_Min_lft.
 intro; eapply leEq_wdl.
  apply less_leEq; apply b0.
 apply AbsIR_wd; rational.
Qed.

End More_Taylor_Defs.

Section Taylor_Theorem.

(**
And finally the ``nice'' version, when we know the expression of the
derivatives of [F].

%\begin{convention}% Let [f] be the sequence of derivatives of [F] of
order up to [n] and [F'] be the nth-derivative of [F].
%\end{convention}%
*)

Variable I : interval.
Hypothesis pI : proper I.

Variable F : PartIR.

Variable n : nat.
Variable f : forall i : nat, i < S n -> PartIR.

Hypothesis goodF : ext_fun_seq f.
Hypothesis goodF' : ext_fun_seq' f.

Hypothesis derF : forall i Hi, Derivative_n i I pI F (f i Hi).

Variable F' : PartIR.
Hypothesis derF' : Derivative_n (S n) I pI F F'.

Variables a b : IR.
Hypothesis Ha : I a.
Hypothesis Hb : I b.


(* begin show *)
Let funct_i i Hi := let HX := (Derivative_n_imp_inc' _ _ _ _ _ (derF i Hi) a Ha) in
[-C-] (f i Hi a HX [/] _[//] nring_fac_ap_zero _ i) {*} (FId{-} [-C-]a) {^}i.

Definition Taylor_Seq := FSumx _ funct_i.

Let deriv_Sn := F'{*} [-C-] ([1][/] _[//]nring_fac_ap_zero _ n) {*} ( [-C-]b{-}FId) {^}n.
(* end show *)

Lemma Taylor_aux : Dom Taylor_Seq b.
Proof.
 repeat split.
 apply FSumx_pred'; repeat split.
Qed.

Theorem Taylor : forall e, [0] [<] e -> forall Hb', {c : IR | Compact (Min_leEq_Max a b) c |
 forall Hc, AbsIR (F b Hb'[-]Part _ _ Taylor_aux[-]deriv_Sn c Hc[*] (b[-]a)) [<=] e}.
Proof.
 intros e H Hb'.
 cut (Diffble_n (S n) I pI F).
  intro Hf.
  cut (Diffble_n n I pI F).
   intro Hf'.
   elim (Taylor' I pI F _ _ Ha Hb n Hf Hf' e H); intros c Hc' Hc.
   exists c.
    auto.
   intros.
   cut (Dom (N_Deriv _ _ _ _ Hf{*} [-C-] ([1][/] _[//]nring_fac_ap_zero IR n) {*}
     ( [-C-]b{-}FId) {^}n) c). intro H0.
    eapply leEq_wdl.
     apply (Hc H0).
    apply AbsIR_wd; simpl in |- *; repeat simple apply cg_minus_wd.
     2: repeat simple apply mult_wdl.
     unfold Taylor_Rem in |- *; simpl in |- *.
     apply cg_minus_wd.
      algebra.
     apply bin_op_wd_unfolded.
      apply Feq_imp_eq with (Compact (Min_leEq_Max a b)).
       apply FSumx_wd'.
       unfold funct_i in |- *; intros; simpl in |- *.
       apply Feq_mult.
        FEQ.
        simpl in |- *.
        apply div_wd.
         apply Feq_imp_eq with I.
          apply Derivative_n_unique with pI i F.
           apply N_Deriv_lemma.
          apply derF.
         auto.
        algebra.
       apply Feq_reflexive; repeat split.
      apply compact_Min_rht.
     apply mult_wdl.
     apply div_wd.
      2: algebra.
     apply Feq_imp_eq with I.
      apply Derivative_n_unique with pI n F.
       apply N_Deriv_lemma.
      apply derF.
     auto.
    apply Feq_imp_eq with I.
     apply Derivative_n_unique with pI (S n) F.
      apply N_Deriv_lemma.
     assumption.
    cut (included (Compact (Min_leEq_Max a b)) I); Included.
   repeat split.
   Transparent N_Deriv.
   simpl in |- *.
   cut (included (Compact (Min_leEq_Max a b)) I); Included.
  apply Derivative_n_imp_Diffble_n with (f n (Nat.lt_succ_diag_r n)).
  apply derF.
 apply Derivative_n_imp_Diffble_n with F'.
 assumption.
Qed.

End Taylor_Theorem.
