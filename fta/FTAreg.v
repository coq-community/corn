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

Require Export KneserLemma.
Require Export CPoly_Shift.
Require Export CPoly_Contin1.

(**
* FTA for regular polynomials
** The Kneser sequence
%\begin{convention}% Let [n] be a positive natural number.
%\end{convention}%
*)

Section Seq_Exists.
Variable n : nat.
Hypothesis lt0n : 0 < n.

(**
%\begin{convention}% Let [qK] be a real between 0 and 1, with
[[
forall (p : CCX), (monic n p) -> forall (c : IR), ((AbsCC (p![0])) [<] c) ->
 {z:CC | ((AbsCC z) [^]n [<] c) | ((AbsCC (p!z)) [<] qK[*]c)}.
]]
Let [p] be a monic polynomial over the complex numbers with degree
[n], and let [c0] be such that [(AbsCC (p![0])) [<] c0].
%\end{convention}%
*)

Section Kneser_Sequence.
Variable qK : IR.
Variable zltq : [0] [<=] qK.
Variable qlt1 : qK [<] [1].
Hypothesis q_prop : forall p : cpoly CC, monic n p -> forall c : IR,
AbsCC p ! [0] [<] c -> {z : CC | AbsCC z[^]n [<=] c | AbsCC p ! z [<] qK[*]c}.

Variable p : cpoly CC.
Hypothesis mp : monic n p.

Variable c0 : IR.
Hypothesis p0ltc0 : AbsCC p ! [0] [<] c0.

Record Knes_tup : Type :=
 {z_el    :> CC;
  c_el    :  IR;
  Kt_prop : AbsCC p ! z_el [<] c_el}.

Record Knes_tupp (tup : Knes_tup) : Type :=
  {Kntup     :> Knes_tup;
   Ktp_prop  :  c_el Kntup [=] qK[*]c_el tup;
   Ktpp_prop :  AbsCC (Kntup[-]tup) [^]n [<=] c_el tup}.

Definition Knes_fun : forall tup : Knes_tup, Knes_tupp tup.
Proof.
 intro tup.
 elim tup.
 intros z c pzltc.
 cut (AbsCC (Shift z p) ! [0] [<] c).
  intro Hsh.
  generalize (q_prop (Shift z p) (Shift_monic z p n mp) c Hsh).
  intro Hex.
  elim Hex.
  intros z'; intros.
  cut (AbsCC p ! (z'[+]z) [<] qK[*]c).
   intro HH.
   apply (Build_Knes_tupp (Build_Knes_tup z c pzltc) (Build_Knes_tup (z'[+]z) (qK[*]c) HH)).
    simpl in |- *; algebra.
   simpl in |- *; apply leEq_wdl with (AbsCC z'[^]n).
    assumption.
   apply (nexp_wd IR (AbsCC z') (AbsCC (z'[+]z[-]z)) n).
   apply AbsCC_wd.
   rational.
  apply less_wdl with (AbsCC (Shift z p) ! z').
   assumption.
  apply AbsCC_wd.
  apply Shift_apply.
 apply less_wdl with (AbsCC p ! z).
  assumption.
 generalize (Shift_apply z p [0]).
 intro H3.
 apply eq_symmetric_unfolded.
 apply AbsCC_wd.
 apply eq_transitive_unfolded with p ! ([0][+]z).
  assumption.
 algebra.
Defined.

Fixpoint Knes_fun_it (i : nat) : Knes_tup :=
  match i with
  | O   => Build_Knes_tup [0] c0 p0ltc0
  | S j => Knes_fun (Knes_fun_it j):Knes_tup
  end.

Definition sK := Knes_fun_it:nat -> CC.

Lemma sK_c : forall tup : Knes_tup, c_el (Knes_fun tup) [=] qK[*]c_el tup.
Proof.
 intro tup.
 generalize (Ktp_prop tup (Knes_fun tup)).
 auto.
Qed.

Lemma sK_c0 : forall i : nat, c_el (Knes_fun_it i) [=] qK[^]i[*]c0.
Proof.
 simple induction i.
  simpl in |- *.
  rational.
 intros.
 simpl in |- *.
 generalize (sK_c (Knes_fun_it n0)).
 intro H1.
 apply eq_transitive_unfolded with (qK[*]c_el (Knes_fun_it n0)).
  assumption.
 rstepr (qK[*] (nexp IR n0 qK[*]c0)).
 apply mult_wdr.
 exact H.
Qed.

Lemma sK_prop1 : forall i : nat, AbsCC p ! (sK i) [<=] qK[^]i[*]c0.
Proof.
 unfold sK in |- *.
 simple induction i.
  simpl in |- *.
  rstepr c0.
  apply less_leEq; exact p0ltc0.
 intros.
 simpl in |- *.
 generalize (Kt_prop (Knes_fun (Knes_fun_it n0))).
 intro H2.
 apply leEq_wdr with (c_el (Knes_fun (Knes_fun_it n0))).
  apply less_leEq; assumption.
 generalize (sK_c (Knes_fun_it n0)).
 intro H3.
 eapply eq_transitive_unfolded.
  apply H3.
 generalize (sK_c0 n0).
 intro H4.
 rstepr (qK[*] (nexp IR n0 qK[*]c0)).
 apply mult_wdr.
 exact H4.
Qed.

Lemma sK_it : forall tup : Knes_tup, AbsCC (Knes_fun tup[-]tup) [^]n [<=] c_el tup.
Proof.
 intro tup.
 generalize (Ktpp_prop tup (Knes_fun tup)).
 auto.
Qed.

Lemma sK_prop2 : forall i : nat, AbsCC (sK (S i) [-]sK i) [^]n [<=] qK[^]i[*]c0.
Proof.
 unfold sK in |- *.
 simpl in |- *.
 intro i.
 generalize (sK_it (Knes_fun_it i)).
 intro H0.
 eapply leEq_wdr.
  apply H0.
 exact (sK_c0 i).
Qed.

End Kneser_Sequence.

Section Seq_Exists_Main.

(**
** Main results
*)

Lemma seq_exists : {q : IR | [0] [<=] q | q [<] [1] and (forall p : cpoly CC,
 monic n p -> forall c : IR, AbsCC p ! [0] [<] c -> {s : nat -> CC | forall i,
  AbsCC p ! (s i) [<=] q[^]i[*]c /\ AbsCC (s (S i) [-]s i) [^]n [<=] q[^]i[*]c})}.
Proof.
 elim (Kneser n lt0n).
 intros q; intros H H0.
 exists q.
  assumption.
 inversion_clear H0.
 rename X0 into H2.
 split. assumption.
  intros p mp c pzltc.
 exists (sK q H2 p mp c pzltc).
 split.
  exact (sK_prop1 q H2 p mp c pzltc i).
 exact (sK_prop2 q H2 p mp c pzltc i).
Qed.

End Seq_Exists_Main.

End Seq_Exists.

Section N_Exists.

Variable n : nat.
Hypothesis lt0n : 0 < n.
Variable q : IR.
Hypothesis zleq : [0] [<=] q.
Hypothesis qlt1 : q [<] [1].
Variable c : IR.
Hypothesis zltc : [0] [<] c.
(* begin hide *)
Let q_ : q[-][1] [#] [0] := qltone IR q qlt1.
(* end hide *)
Variable e : IR.
Variable zlte : [0] [<] e.

Lemma N_exists : {N : nat | forall m, N <= m -> (q[^]m[-]q[^]N[/] q[-][1][//]q_) [*]c [<=] e}.
Proof.
 cut ([0] [<] [1][-]q).
  intro H0.
  cut ([1][-]q [#] [0]).
   intro H3.
   cut (c [#] [0]).
    intro H1.
    cut ([0] [<] ([1][-]q) [*] (e[/] c[//]H1)).
     intro H2.
     elim (qi_yields_zero q zleq qlt1 (([1][-]q) [*] (e[/] c[//]H1)) H2).
     intros N HN.
     exists N.
     intros m leNm.
     rstepl ((q[^]N[-]q[^]m[/] [1][-]q[//]H3) [*]c).
     apply shift_mult_leEq with H1.
      assumption.
     apply shift_div_leEq'.
      assumption.
     apply leEq_transitive with (q[^]N).
      rstepl ([0][+] (q[^]N[-]q[^]m)).
      apply shift_plus_leEq.
      rstepr (q[^]m).
      apply nexp_resp_nonneg.
      assumption.
     assumption.
    apply mult_resp_pos.
     assumption.
    apply div_resp_pos.
     assumption.
    assumption.
   apply ap_symmetric_unfolded.
   apply less_imp_ap.
   assumption.
  apply ap_symmetric_unfolded.
  apply less_imp_ap.
  assumption.
 apply shift_less_minus.
 rstepl q.
 assumption.
Qed.

End N_Exists.

Section Seq_is_CC_CAuchy.

(**
** The Kneser sequence is Cauchy in [CC] *)

Variable n : nat.
Hypothesis lt0n : 0 < n.
Variable q : IR.
Hypothesis zleq : [0] [<=] q.
Hypothesis qlt1 : q [<] [1].
Variable c : IR.
Hypothesis zltc : [0] [<] c.

(** %\begin{convention}% Let:
 - [q_] prove [q[-][1] [#] [0]]
 - [nrtq := NRoot q n]
 - [nrtc := Nroot c n]
 - [nrtqlt1] prove [nrtq [<] [1]]
 - [nrtq_] prove [nrtq[-][1] [#] [0]]

%\end{convention}% *)

(* begin hide *)
Let q_ : q[-][1] [#] [0] := qltone IR q qlt1.
Let nrtq : IR := NRoot zleq lt0n.
Let nrtc : IR := NRoot (less_leEq _ _ _ zltc) lt0n.
Let nrtqlt1 : nrtq [<] [1] := NRoot_less_one q zleq n lt0n qlt1.
Let nrtq_ : nrtq[-][1] [#] [0] := qltone IR nrtq nrtqlt1.
(* end hide *)

Lemma zlt_nrtq : [0] [<=] nrtq.
Proof.
 unfold nrtq; apply NRoot_nonneg.
Qed.

Lemma zlt_nrtc : [0] [<] nrtc.
Proof.
 unfold nrtc; apply NRoot_pos; auto.
Qed.

Lemma nrt_pow : forall i (H : [0] [<=] q[^]i[*]c), NRoot H lt0n [=] nrtq[^]i[*]nrtc.
Proof.
 intros.
 apply root_unique with n.
    apply NRoot_nonneg.
   apply mult_resp_nonneg.
    apply nexp_resp_nonneg. exact zlt_nrtq.
    apply less_leEq. exact zlt_nrtc.
   auto.
 astepl (q[^]i[*]c).
 astepr ((nrtq[^]i) [^]n[*]nrtc[^]n).
 astepr (nrtq[^] (i * n) [*]nrtc[^]n).
 rewrite mult_comm.
 astepr ((nrtq[^]n) [^]i[*]nrtc[^]n).
 unfold nrtq in |- *. unfold nrtc in |- *.
 apply bin_op_wd_unfolded.
  apply un_op_wd_unfolded.
  algebra.
 algebra.
Qed.

Lemma abs_pow_ltRe : forall s, (forall i, AbsCC (s (S i) [-]s i) [^]n [<=] q[^]i[*]c) ->
 forall i, AbsIR (Re (s (S i)) [-]Re (s i)) [<=] nrtq[^]i[*]nrtc.
Proof.
 intros s H i.
 apply leEq_wdl with (AbsIR (Re (s (S i) [-]s i))).
  apply leEq_transitive with (AbsCC (s (S i) [-]s i)).
   apply absCC_absIR_re.
  generalize (H i).
  intro Hi.
  cut ([0] [<=] q[^]i[*]c).
   intro H0.
   cut (AbsCC (s (S i) [-]s i) [<=] NRoot H0 lt0n).
    intro H1.
    apply leEq_wdr with (NRoot H0 lt0n).
     assumption.
    apply nrt_pow.
   apply power_cancel_leEq with n.
     auto with arith.
    apply NRoot_nonneg.
   apply leEq_wdr with (q[^]i[*]c).
    exact (H i).
   algebra.
  apply mult_resp_nonneg.
   apply nexp_resp_nonneg.
   assumption.
  apply less_leEq; assumption.
 apply ABSIR_wd.
 apply Re_resp_inv.
Qed.

Lemma abs_pow_ltIm : forall s, (forall i, AbsCC (s (S i) [-]s i) [^]n [<=] q[^]i[*]c) ->
 forall i, AbsIR (Im (s (S i)) [-]Im (s i)) [<=] nrtq[^]i[*]nrtc.
Proof.
 intros s H i.
 apply leEq_wdl with (AbsIR (Im (s (S i) [-]s i))).
  apply leEq_transitive with (AbsCC (s (S i) [-]s i)).
   apply absCC_absIR_im.
  generalize (H i).
  intro Hi.
  cut ([0] [<=] q[^]i[*]c).
   intro H0.
   cut (AbsCC (s (S i) [-]s i) [<=] NRoot H0 lt0n).
    intro H1.
    apply leEq_wdr with (NRoot H0 lt0n).
     assumption.
    apply nrt_pow.
   apply power_cancel_leEq with n.
     auto with arith.
    apply NRoot_nonneg.
   apply leEq_wdr with (q[^]i[*]c).
    exact (H i).
   algebra.
  apply mult_resp_nonneg.
   apply nexp_resp_nonneg.
   assumption.
  apply less_leEq; assumption.
 apply ABSIR_wd.
 apply Im_resp_inv.
Qed.

Lemma SublemmaRe : forall s, (forall i, AbsCC (s (S i) [-]s i) [^]n [<=] q[^]i[*]c) -> forall N m,
 N <= m -> AbsIR (Re (s m) [-]Re (s N)) [<=] (nrtq[^]m[-]nrtq[^]N[/] nrtq[-][1][//]nrtq_) [*]nrtc.
Proof.
 intros s Hi N m leNm.
 elim (le_lt_eq_dec N m leNm).
  intro ltNm.
  generalize (diff_is_sum (fun j : nat => Re (s j)) N m ltNm).
  intro Hsum.
  generalize (ABSIR_wd _ _ Hsum). (* Use AbsIR_wd *)
  intro Habseq.
  apply leEq_wdl with (ABSIR (Sum N (pred m) (fun i : nat => Re (s (S i)) [-]Re (s i)))).
   2: apply eq_symmetric_unfolded; apply Habseq.
  cut (N <= S (pred m)). intro leNm'.
   (* FIXME was 2:Omega *) 2: clear nrtq_ nrtqlt1 nrtc nrtq; omega.
  generalize (triangle_SumIR N (pred m) (fun i : nat => Re (s (S i)) [-]Re (s i)) leNm').
  intro Htri.
  apply leEq_transitive with (Sum N (pred m)
    (fun i : nat => csf_fun IR IR AbsIR (Re (s (S i)) [-]Re (s i)))).
   exact Htri.
  generalize (Sum_pres_leEq (fun i : nat => AbsIR (Re (s (S i)) [-]Re (s i)))
    (fun i : nat => nrtq[^]i[*]nrtc) (abs_pow_ltRe s Hi) N ( pred m)).
  intro Hlt.
  apply leEq_transitive with (Sum N (pred m) (fun i : nat => nrtq[^]i[*]nrtc)).
   cut (N <= pred m).
    intro leNpm.
    exact (Hlt leNpm).
   generalize (S_pred m N ltNm).
   intro Heq.
   apply lt_n_Sm_le.
   rewrite <- Heq.
   assumption.
  generalize (Sum_c_exp nrtq nrtq_ N (pred m)).
  intro Hs.
  generalize (Sum_comm_scal (fun i : nat => nrtq[^]i) nrtc N (pred m)).
  intro Hs2.
  eapply leEq_wdl.
   2: apply eq_symmetric_unfolded; apply Hs2.
  apply mult_resp_leEq_rht.
   generalize (Sum_c_exp nrtq nrtq_ N (pred m)).
   intro Hs3.
   cut (S (pred m) = m).
    intro Heq.
    rewrite Heq in Hs3.
    apply eq_imp_leEq; assumption.
   generalize (S_pred m N ltNm).
   auto.
  exact (less_leEq _ _ _ zlt_nrtc).
 intro HNm.
 rewrite HNm.
 apply leEq_wdl with (AbsIR [0]).
  apply leEq_wdl with ZeroR.
   apply leEq_wdr with ZeroR.
    exact (leEq_reflexive _ _).
   rational.
  apply eq_symmetric_unfolded; exact AbsIRz_isz.
 apply ABSIR_wd.
 rational.
Qed.

Lemma SublemmaIm : forall s, (forall i, AbsCC (s (S i) [-]s i) [^]n [<=] q[^]i[*]c) -> forall N m,
 N <= m -> AbsIR (Im (s m) [-]Im (s N)) [<=] (nrtq[^]m[-]nrtq[^]N[/] nrtq[-][1][//]nrtq_) [*]nrtc.
Proof.
 intros s Hi N m leNm.
 elim (le_lt_eq_dec N m leNm).
  intro ltNm.
  generalize (diff_is_sum (fun j : nat => Im (s j)) N m ltNm).
  intro HSum.
  generalize (ABSIR_wd _ _ HSum). (* Use AbsIR_wd *)
  intro Habseq.
  apply leEq_wdl with (ABSIR (Sum N (pred m) (fun i : nat => Im (s (S i)) [-]Im (s i)))).
   2: apply eq_symmetric_unfolded; apply Habseq.
  cut (N <= S (pred m)). intro leNm'.
   (* FIXME was 2:Omega *) 2: clear nrtq_ nrtqlt1 nrtc nrtq; omega.
  generalize (triangle_SumIR N (pred m) (fun i : nat => Im (s (S i)) [-]Im (s i)) leNm').
  intro Htri.
  apply leEq_transitive with (Sum N (pred m)
    (fun i : nat => csf_fun IR IR AbsIR (Im (s (S i)) [-]Im (s i)))).
   exact Htri.
  generalize (Sum_pres_leEq (fun i : nat => AbsIR (Im (s (S i)) [-]Im (s i)))
    (fun i : nat => nrtq[^]i[*]nrtc) (abs_pow_ltIm s Hi) N ( pred m)).
  intro Hlt.
  apply leEq_transitive with (Sum N (pred m) (fun i : nat => nrtq[^]i[*]nrtc)).
   cut (N <= pred m).
    intro leNpm.
    exact (Hlt leNpm).
   generalize (S_pred m N ltNm).
   intro Heq.
   apply lt_n_Sm_le.
   simpl in |- *.
   rewrite <- Heq.
   assumption.
  generalize (Sum_c_exp nrtq nrtq_ N (pred m)).
  intro Hs.
  generalize (Sum_comm_scal (fun i : nat => nrtq[^]i) nrtc N (pred m)).
  intro Hs2.
  eapply leEq_wdl.
   2: apply eq_symmetric_unfolded; apply Hs2.
  apply mult_resp_leEq_rht.
   generalize (Sum_c_exp nrtq nrtq_ N (pred m)).
   intro Hs3.
   cut (S (pred m) = m).
    intro Heq.
    rewrite Heq in Hs3.
    apply eq_imp_leEq; assumption.
   generalize (S_pred m N ltNm).
   auto.
  exact (less_leEq _ _ _ zlt_nrtc).
 intro HNm.
 rewrite HNm.
 apply leEq_wdl with (AbsIR [0]).
  apply leEq_wdl with ZeroR.
   apply leEq_wdr with ZeroR.
    exact (leEq_reflexive _ _).
   rational.
  apply eq_symmetric_unfolded; exact AbsIRz_isz.
 apply ABSIR_wd.
 rational.
Qed.

Lemma seq_is_CC_Cauchy : forall s,
 (forall i, AbsCC (s (S i) [-]s i) [^]n [<=] q[^]i[*]c) -> CC_Cauchy_prop s.
Proof.
 unfold CC_Cauchy_prop in |- *.
 split.
  (* Prove (Cauchy_prop (seq_re s)) *)
  unfold Cauchy_prop in |- *.
  intros e zlte.
  generalize (N_exists (*n lt0n*)  nrtq zlt_nrtq nrtqlt1 nrtc zlt_nrtc e zlte).
  intro Hex.
  elim Hex.
  intros N HN.
  exists N.
  intros m leNm.
  apply AbsIR_imp_AbsSmall.
  generalize (SublemmaRe s H N m leNm).
  intro H2.
  generalize (HN m leNm).
  intro H3.
  eapply leEq_transitive.
   2: apply H3.
  rstepr ((nrtq[^]m[-]nrtq[^]N[/] nrtq[-][1][//]nrtq_) [*]nrtc).
  exact H2.
 (* Prove (Cauchy_prop (seq_im s)) *)
 unfold Cauchy_prop in |- *.
 intros e zlte.
 generalize (N_exists (*n lt0n*)  nrtq zlt_nrtq nrtqlt1 nrtc zlt_nrtc e zlte).
 intro Hex.
 elim Hex.
 intros N HN.
 exists N.
 intros m leNm.
 apply AbsIR_imp_AbsSmall.
 generalize (SublemmaIm s H N m leNm).
 intro H2.
 generalize (HN m leNm).
 intro H3.
 eapply leEq_transitive.
  2: apply H3.
 rstepr ((nrtq[^]m[-]nrtq[^]N[/] nrtq[-][1][//]nrtq_) [*]nrtc).
 exact H2.
Qed.

End Seq_is_CC_CAuchy.

Lemma FTA_monic : forall (p : cpoly CC) (n : nat),
 0 < n -> monic n p -> {c : CC | p ! c [=] [0]}.
Proof.
 intros p n H0n mon.
 generalize (seq_exists n H0n).
 intro H.
 elim H.
 intros q qnonneg Hq1.
 elim Hq1.
 intros qlt10 Hq2.
 generalize (Hq2 p mon).
 intro Hq3.
 cut ([0] [<] AbsCC p ! [0][+][1]).
  intro Hp.
  elim (Hq3 (AbsCC p ! [0][+][1])).
   intros s Hs.
   cut (forall i : nat, AbsCC (s (S i) [-]s i) [^]n [<=] q[^]i[*] (AbsCC p ! [0][+][1])).
    intro Hs2.
    cut (CC_Cauchy_prop s).
     intro Hs3.
     exists (LimCC (Build_CC_CauchySeq s Hs3)).
     apply CC_SeqLimit_uniq with (fun n : nat => p ! (s n)).
      exact (poly_pres_lim (fun x : CC => p ! x) (contin_polyCC p) (Build_CC_CauchySeq s Hs3)).
     generalize (seq_yields_zero q qnonneg qlt10 (AbsCC p ! [0][+][1]) Hp (fun n0 : nat => p ! (s n0))).
     intro H0. apply H0.
     intro i. generalize (Hs i).
     intro H1; inversion_clear H1; assumption.
    exact (seq_is_CC_Cauchy n H0n q qnonneg qlt10 (AbsCC p ! [0][+][1]) Hp s Hs2).
   intro i; generalize (Hs i); intro Ha; elim Ha; intros; assumption.
  exact (less_plusOne _ (AbsCC p ! [0])).
 apply zero_lt_posplus1.
 apply AbsCC_nonneg.
Qed.

Lemma FTA_reg : forall (p : cpoly CC) (n : nat),
 0 < n -> degree n p -> {c : CC | p ! c [=] [0]}.
Proof.
 intros p n H H0.
 elim (FTA_monic (poly_norm _ p n H0) n); auto.
  intros. exists x.
  apply poly_norm_apply with n H0; auto.
 apply poly_norm_monic; auto.
Qed.
