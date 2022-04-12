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

Require Export CoRN.reals.Max_AbsIR.
Require Export CoRN.algebra.Expon.
Require Export CoRN.algebra.CPoly_ApZero.

Section More_Cauchy_Props.

(**
** Miscellaneous
*** More properties of Cauchy sequences
We will now define some special Cauchy sequences and prove some
more useful properties about them.

The sequence defined by $x_n=\frac2{n+1}$#x(n)=2/(n+1)#.
*)

Lemma twice_inv_seq_Lim : SeqLimit (R:=IR) (fun n => Two[*]one_div_succ n) [0].
 red in |- *; fold (Cauchy_Lim_prop2 (fun n : nat => Two[*]one_div_succ n) [0]) in |- *.
Proof.
 apply Cauchy_Lim_prop3_prop2.
 red in |- *; intro.
 exists (2 * S k); intros.
 astepr ((Two:IR) [*]one_div_succ m).
 apply AbsIR_imp_AbsSmall.
 apply leEq_wdl with ((Two:IR) [*]one_div_succ m).
  2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
  astepl (one_div_succ (R:=IR) m[*]Two).
  unfold one_div_succ in |- *; simpl in |- *; fold (Two:IR) in |- *.
  apply shift_mult_leEq with (two_ap_zero IR).
   apply pos_two.
  unfold Snring in |- *.
  rstepr ([1][/] nring (S k) [*]Two[//]
    mult_resp_ap_zero _ _ _ (nring_ap_zero _ (S k) (sym_not_eq (O_S k))) (two_ap_zero IR)).
  apply recip_resp_leEq.
   astepl (ZeroR[*][0]); apply mult_resp_less_both; try apply leEq_reflexive.
    apply pos_nring_S.
   apply pos_two.
  astepl ((Two:IR) [*]nring (S k)).
  apply leEq_transitive with (nring (R:=IR) m).
   apply leEq_wdl with (nring (R:=IR) (2 * S k)).
    apply nring_leEq.
    assumption.
   apply nring_comm_mult.
  simpl in |- *; astepl (nring (R:=IR) m[+][0]); apply plus_resp_leEq_lft;
    apply less_leEq; apply pos_one.
 astepl (ZeroR[*][0]); apply mult_resp_leEq_both; try apply leEq_reflexive.
  apply less_leEq; apply pos_two.
 apply less_leEq; apply one_div_succ_pos.
Qed.

Definition twice_inv_seq : CauchySeq IR.
Proof.
 apply Build_CauchySeq with (fun n : nat => Two[*]one_div_succ (R:=IR) n).
 apply Cauchy_prop2_prop.
 red in |- *; exists ZeroR.
 red in |- *; fold (SeqLimit (fun n : nat => Two[*]one_div_succ (R:=IR) n) [0]) in |- *.
 apply twice_inv_seq_Lim.
Defined.

(**
Next, we prove that the sequence of absolute values of a Cauchy
sequence is also Cauchy.
*)

Lemma Cauchy_Lim_abs : forall seq y, Cauchy_Lim_prop2 seq y ->
 Cauchy_Lim_prop2 (fun n => AbsIR (seq n)) (AbsIR y).
Proof.
 intros seq y H.
 red in |- *; red in H.
 intros eps He.
 elim (H eps He); clear H.
 intros N HN.
 exists N; intros.
 apply AbsIR_imp_AbsSmall.
 cut (AbsIR (seq m[-]y) [<=] eps).
  intro.
  2: apply AbsSmall_imp_AbsIR; apply HN; assumption.
 cut (seq m[-]y [<=] eps).
  2: eapply leEq_transitive; [ apply leEq_AbsIR | apply H0 ].
 intro.
 cut (y[-]seq m [<=] eps).
  2: eapply leEq_transitive; [ apply leEq_AbsIR | eapply leEq_wdl; [ apply H0 | apply AbsIR_minus ] ].
 intro.
 simpl in |- *; unfold ABSIR in |- *.
 apply Max_leEq.
  apply shift_minus_leEq.
  apply Max_leEq.
   apply shift_leEq_plus'.
   apply leEq_transitive with y.
    apply shift_minus_leEq; apply shift_leEq_plus'; assumption.
   apply lft_leEq_Max.
  apply shift_leEq_plus'.
  apply leEq_transitive with ( [--]y).
   apply shift_minus_leEq; apply shift_leEq_plus'.
   rstepl (y[-]seq m).
   assumption.
  apply rht_leEq_Max.
 astepr ( [--][--]eps); apply inv_resp_leEq.
 apply shift_leEq_minus; apply shift_plus_leEq'.
 apply leEq_wdr with (Max (seq m) [--] (seq m) [+]eps).
  apply Max_leEq.
   apply leEq_transitive with (seq m[+]eps).
    apply shift_leEq_plus'; assumption.
   apply plus_resp_leEq.
   apply lft_leEq_Max.
  apply leEq_transitive with ( [--] (seq m) [+]eps).
   apply shift_leEq_plus'; rstepl (seq m[-]y); assumption.
  apply plus_resp_leEq.
  apply rht_leEq_Max.
 unfold cg_minus in |- *.
 algebra.
Qed.

Lemma Cauchy_abs : forall seq : CauchySeq IR, Cauchy_prop (fun n => AbsIR (seq n)).
Proof.
 intro.
 apply Cauchy_prop2_prop.
 exists (AbsIR (Lim seq)).
 apply Cauchy_Lim_abs.
 apply Cauchy_complete.
Qed.

Lemma Lim_abs : forall seq : CauchySeq IR,
 Lim (Build_CauchySeq _ _ (Cauchy_abs seq)) [=] AbsIR (Lim seq).
Proof.
 intros.
 apply eq_symmetric_unfolded; apply Limits_unique.
 simpl in |- *; apply Cauchy_Lim_abs.
 apply Cauchy_complete.
Qed.

Lemma CS_seq_bounded' : forall seq : CauchySeqR,
 {K : IR | [0] [<] K | forall m : nat, AbsSmall K (seq m)}.
Proof.
 unfold CauchySeqR in |- *.
 intros.
 assert (X0 : {K : IR | [0] [<] K | {N : nat | forall m, N <= m -> AbsSmall K (seq m)}}).
  apply CS_seq_bounded; auto.
  apply (CS_proof _ seq).
 destruct X0 as [K1 K1_pos H1].
 destruct H1 as [N H1].
 exists (Max K1 (SeqBound0 seq N)).
  apply less_leEq_trans with K1; auto.
  apply lft_leEq_MAX.
 intros.
 elim (le_or_lt N m).
  intros.
  assert (AbsSmall (R:=IR) K1 (seq m)).
   apply H1. auto.
   apply AbsSmall_leEq_trans with K1; auto.
  apply lft_leEq_MAX.
 intros.
 apply AbsSmall_leEq_trans with (SeqBound0 seq N).
  apply rht_leEq_MAX.
 apply AbsSmall_leEq_trans with (AbsIR (seq m)).
  apply SeqBound0_greater; auto.
 apply AbsIR_imp_AbsSmall.
 apply leEq_reflexive.
Qed.

End More_Cauchy_Props.

Section Subsequences.

(**
*** Subsequences
We will now examine (although without formalizing it) the concept
of subsequence and some of its properties.

%\begin{convention}% Let [seq1,seq2:nat->IR].
%\end{convention}%

In order for [seq1] to be a subsequence of [seq2], there must be an
increasing function [f] growing to infinity such that
[forall (n :nat), (seq1 n) [=] (seq2 (f n))].  We assume [f] to be such a
function.

Finally, for some of our results it is important to assume that
[seq2] is monotonous.
*)

Variables seq1 seq2 : nat -> IR.
Variable f : nat -> nat.

Hypothesis monF : forall m n : nat, m <= n -> f m <= f n.
Hypothesis crescF : forall n : nat, {m : nat | n < m /\ f n < f m}.
Hypothesis subseq : forall n : nat, seq1 n [=] seq2 (f n).

Hypothesis mon_seq2 :
 (forall m n, m <= n -> seq2 m [<=] seq2 n) \/ (forall m n, m <= n -> seq2 n [<=] seq2 m).

Lemma unbnd_f : forall m, {n : nat | m < f n}.
Proof.
 simple induction m.
  elim (crescF 0).
  intros n Hn.
  exists n.
  inversion_clear Hn.
  apply le_lt_trans with (f 0); auto with arith.
 intros n H.
 elim H; clear H; intros n' Hn'.
 elim (crescF n').
 intros i Hi; elim Hi; clear Hi; intros Hi Hi'.
 exists i.
 apply le_lt_trans with (f n'); auto.
Qed.

(* begin hide *)
Let mon_F' : forall m n : nat, f m < f n -> m < n.
Proof.
 intros.
 cut (~ n <= m).
  intro; apply not_ge; auto.
 intro.
 cut (f n <= f m).
  apply lt_not_le; auto.
 apply monF; assumption.
Qed.
(* end hide *)

Lemma conv_subseq_imp_conv_seq : Cauchy_prop seq1 -> Cauchy_prop seq2.
Proof.
 intro H.
 red in |- *; red in H.
 intros e H0.
 elim (H e H0).
 intros N HN.
 exists (f N).
 intros.
 elim (unbnd_f m); intros i Hi.
 apply AbsIR_imp_AbsSmall.
 apply leEq_transitive with (AbsIR (seq2 (f i) [-]seq2 (f N))).
  elim mon_seq2; intro.
   eapply leEq_wdl.
    2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
    2: apply shift_leEq_minus; astepl (seq2 (f N)); apply H2; assumption.
   eapply leEq_wdr.
    2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
    2: apply shift_leEq_minus; astepl (seq2 (f N)); apply H2; apply le_trans with m; auto with arith.
   apply minus_resp_leEq.
   apply H2; auto with arith.
  eapply leEq_wdl.
   2: apply eq_symmetric_unfolded; apply AbsIR_eq_inv_x.
   2: apply shift_minus_leEq; astepr (seq2 (f N)); auto.
  eapply leEq_wdr.
   2: apply eq_symmetric_unfolded; apply AbsIR_eq_inv_x.
   2: apply shift_minus_leEq; astepr (seq2 (f N)); apply H2; apply le_trans with m; auto with arith.
  apply inv_resp_leEq; apply minus_resp_leEq.
  apply H2; auto with arith.
 apply leEq_wdl with (AbsIR (seq1 i[-]seq1 N)).
  apply AbsSmall_imp_AbsIR; apply HN.
  apply lt_le_weak.
  apply mon_F'; apply le_lt_trans with m; auto.
 apply AbsIR_wd; algebra.
Qed.

Lemma Cprop2_seq_imp_Cprop2_subseq : forall a,
 Cauchy_Lim_prop2 seq2 a -> Cauchy_Lim_prop2 seq1 a.
Proof.
 intros a H.
 red in |- *; red in H.
 intros eps H0.
 elim (H _ H0).
 intros N HN.
 elim (unbnd_f N); intros i Hi.
 exists i.
 intros.
 astepr (seq2 (f m) [-]a).
 apply HN.
 cut (f i <= f m).
  intros; apply le_trans with (f i); auto with arith.
 apply monF; assumption.
Qed.

Lemma conv_seq_imp_conv_subseq : Cauchy_prop seq2 -> Cauchy_prop seq1.
Proof.
 intro H.
 apply Cauchy_prop2_prop.
 cut (Cauchy_prop2 (Build_CauchySeq _ _ H)).
  intro H0.
  elim H0; intros a Ha; exists a.
  apply Cprop2_seq_imp_Cprop2_subseq.
  assumption.
 exists (Lim (Build_CauchySeq _ _ H)).
 apply Lim_Cauchy.
Qed.

Lemma Cprop2_subseq_imp_Cprop2_seq : forall a,
 Cauchy_Lim_prop2 seq1 a -> Cauchy_Lim_prop2 seq2 a.
Proof.
 intros.
 cut (Cauchy_prop seq1); intros.
  2: apply Cauchy_prop2_prop.
  2: exists a; assumption.
 cut (Cauchy_prop seq2); intros H1.
  2: apply conv_subseq_imp_conv_seq; assumption.
 cut (Cauchy_Lim_prop2 (Build_CauchySeq _ _ H1) (Lim (Build_CauchySeq _ _ H1))); intros.
  2: apply Cauchy_complete.
 cut (Cauchy_Lim_prop2 seq1 (Lim (Build_CauchySeq _ _ H1))); intros.
  2: apply Cprop2_seq_imp_Cprop2_subseq; assumption.
 cut (Lim (Build_CauchySeq _ _ H1) [=] a).
  intro H4.
  eapply Lim_wd.
   apply H4.
  assumption.
 apply Lim_unique with seq1; assumption.
Qed.

End Subsequences.

Section Cauchy_Subsequences.

Variables seq1 seq2 : CauchySeq IR.
Variable f : nat -> nat.

Hypothesis monF : forall m n : nat, m <= n -> f m <= f n.
Hypothesis crescF : forall n : nat, {m : nat | n < m /\ f n < f m}.
Hypothesis subseq : forall n : nat, seq1 n [=] seq2 (f n).

Hypothesis mon_seq2 :
 (forall m n, m <= n -> seq2 m [<=] seq2 n) \/ (forall m n, m <= n -> seq2 n [<=] seq2 m).

Lemma Lim_seq_eq_Lim_subseq : Lim seq1 [=] Lim seq2.
Proof.
 cut (Cauchy_Lim_prop2 seq1 (Lim seq2)).
  2: apply Cprop2_seq_imp_Cprop2_subseq with (CS_seq _ seq2) f; auto; apply Cauchy_complete.
 intro.
 apply eq_symmetric_unfolded.
 apply Limits_unique; assumption.
Qed.

Lemma Lim_subseq_eq_Lim_seq : Lim seq1 [=] Lim seq2.
Proof.
 cut (Cauchy_Lim_prop2 seq2 (Lim seq1)).
  2: exact (Cprop2_subseq_imp_Cprop2_seq seq1 seq2 f monF crescF subseq mon_seq2 _
    (Cauchy_complete seq1)).
 intro.
 apply Limits_unique; assumption.
Qed.

End Cauchy_Subsequences.

Section Properties_of_Exponentiation.

(**
*** More properties of Exponentiation

Finally, we prove that [x[^]n] grows to infinity if [x [>] [1]].
*)

Lemma power_big' : forall (R : COrdField) (x : R) n,
 [0] [<=] x -> [1][+]nring n[*]x [<=] ([1][+]x) [^]n.
Proof.
 intros.
 induction  n as [| n Hrecn]; intros.
  rstepl ([1]:R).
  astepr ([1]:R).
  apply leEq_reflexive.
 simpl in |- *.
 apply leEq_transitive with (([1][+]nring n[*]x) [*] ([1][+]x)).
  rstepr ([1][+] (nring n[+][1]) [*]x[+]nring n[*]x[^]2).
  astepl ([1][+] (nring n[+][1]) [*]x[+][0]).
  apply plus_resp_leEq_lft.
  apply mult_resp_nonneg.
   astepl (nring 0:R). apply nring_leEq. auto with arith.
   apply sqr_nonneg.
 apply mult_resp_leEq_rht.
  auto.
 apply less_leEq. astepl (([0]:R) [+][0]).
 apply plus_resp_less_leEq. apply pos_one. auto.
Qed.

Lemma power_big : forall x y : IR, [0] [<=] x -> [1] [<] y -> {N : nat | x [<=] y[^]N}.
Proof.
 intros.
 cut ([0] [<] y[-][1]). intro.
  cut (y[-][1] [#] [0]). intro H2.
   elim (Archimedes (x[-][1][/] y[-][1][//]H2)). intro N. intros. exists N.
   apply leEq_transitive with ([1][+]nring N[*] (y[-][1])).
    apply shift_leEq_plus'.
    astepr ((y[-][1]) [*]nring N).
    apply shift_leEq_mult' with H2. auto.
     auto.
   apply leEq_wdr with (([1][+] (y[-][1])) [^]N).
    apply power_big'. apply less_leEq. auto.
    apply un_op_wd_unfolded. rational.
   apply Greater_imp_ap. auto.
  apply shift_less_minus. astepl OneR. auto.
Qed.

Lemma qi_yields_zero : forall q : IR,
 [0] [<=] q -> q [<] [1] -> forall e, [0] [<] e -> {N : nat | q[^]N [<=] e}.
Proof.
 intros.
 cut ([0] [<] ([1][+]q) [/]TwoNZ). intro Haux.
  cut (([1][+]q) [/]TwoNZ [#] [0]). intro H2.
   cut (e [#] [0]). intro H3.
    elim (power_big ([1][/] e[//]H3) ([1][/] _[//]H2)). intro N. intros H4. exists N.
      cut ([0] [<] (([1][+]q) [/]TwoNZ) [^]N). intro H5.
       apply leEq_transitive with ((([1][+]q) [/]TwoNZ) [^]N).
        apply nexp_resp_leEq.
         auto.
        apply shift_leEq_div.
         apply pos_two.
        apply shift_leEq_plus.
        rstepl q. apply less_leEq. auto.
        astepl ([1][*] (([1][+]q) [/]TwoNZ) [^]N).
       set (H6 := pos_ap_zero _ _ H5) in *.
       apply shift_mult_leEq with H6. auto.
        rstepr (e[*] ([1][/] _[//]H6)).
       apply shift_leEq_mult' with H3. auto.
        astepr ([1][^]N[/] _[//]H6).
       astepr (([1][/] _[//]H2) [^]N). auto.
       apply nexp_resp_pos. apply pos_div_two.
      astepl ([0][+]ZeroR). apply plus_resp_less_leEq.
      apply pos_one. auto.
      apply less_leEq. apply recip_resp_pos. auto.
     apply shift_less_div. apply pos_div_two.
     astepl ([0][+]ZeroR). apply plus_resp_less_leEq.
     apply pos_one. auto.
     astepl (([1][+]q) [/]TwoNZ). apply shift_div_less.
    apply pos_two. rstepr ([1][+]OneR).
    apply plus_resp_less_lft. auto.
    apply Greater_imp_ap. auto.
   apply Greater_imp_ap. auto.
  apply pos_div_two.
 astepl ([0][+]ZeroR). apply plus_resp_less_leEq.
 apply pos_one. auto.
Qed.

Lemma qi_lim_zero : forall q : IR, [0] [<=] q -> q [<] [1] -> SeqLimit (fun i => q[^]i) [0].
Proof.
 intros q H H0.
 unfold SeqLimit in |- *. unfold AbsSmall in |- *. intros.
 elim (qi_yields_zero q H H0 e); auto.
 intro N. intros. exists (S N). intros. split.
 apply less_leEq.
  apply less_leEq_trans with ZeroR.
   astepr ( [--]ZeroR). apply inv_resp_less. auto.
   astepr (q[^]m).
  apply nexp_resp_nonneg. auto.
  astepl (q[^]m).
 replace m with (N + (m - N)).
  astepl (q[^]N[*]q[^] (m - N)). astepr (e[*][1]).
  apply mult_resp_leEq_both.
     apply nexp_resp_nonneg. auto.
     apply nexp_resp_nonneg. auto.
    auto.
  astepr (OneR[^] (m - N)).
  apply nexp_resp_leEq. auto. apply less_leEq. auto.
   auto with arith.
Qed.

End Properties_of_Exponentiation.

(**
*** [IR] has characteristic zero *)

Lemma char0_IR : Char0 IR.
Proof.
 apply char0_OrdField.
Qed.

Lemma poly_apzero_IR : forall f : cpoly_cring IR, f [#] [0] -> {c : IR | f ! c [#] [0]}.
Proof.
 intros.
 apply poly_apzero.
  exact char0_IR.
 auto.
Qed.

Lemma poly_IR_extensional : forall p q : cpoly_cring IR, (forall x, p ! x [=] q ! x) -> p [=] q.
Proof.
 intros.
 apply poly_extensional.
  exact char0_IR.
 auto.
Qed.
