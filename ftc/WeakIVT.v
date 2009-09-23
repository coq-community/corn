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

(** printing ** %\ensuremath\times% #&times;# *)

(* begin hide *)
Infix "**" := prodT (at level 20).
(* end hide *)

Require Export Continuity.

(**
* IVT for Partial Functions

In general, we cannot prove the classically valid Intermediate Value
Theorem for arbitrary partial functions, which states that in any
interval [[a,b]], for any value [z] between [f(a)] and [f(b)]
there exists $x\in[a,b]$#x&isin;[a,b]# such that [f(x) [=] z].

However, as is usually the case, there are some good aproximation results.  We
will prove them here.
*)

Section Lemma1.

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variable F : PartIR.
Hypothesis contF : Continuous_I Hab F.

(**
** First Lemmas

%\begin{convention}% Let [a, b : IR] and [Hab : a [<=] b] and denote by [I]
the interval [[a,b]].  Let [F] be a continuous function on [I].
%\end{convention}%

We begin by proving that, if [f(a) [<] f(b)], then for every [y] in
[[f(a),f(b)]] there is an $x\in[a,b]$#x&isin;[a,b]# such that [f(x)] is close
enough to [z].
*)

Lemma Weak_IVT_ap_lft : forall Ha Hb (HFab : F a Ha [<] F b Hb) e,
 Zero [<] e -> forall z, Compact (less_leEq _ _ _ HFab) z ->
 {x : IR | Compact Hab x | forall Hx, AbsIR (F x Hx[-]z) [<=] e}.
Proof.
 intros Ha Hb HFab e H z H0.
 cut (a [<] b).
  intro Hab'.
  set (G := FAbs (F{-}[-C-]z)) in *.
  assert (H1 : Continuous_I Hab G).
   unfold G in |- *; Contin.
  set (m := glb_funct _ _ _ _ H1) in *.
  elim (glb_is_glb _ _ _ _ H1).
  fold m in |- *; intros.
  cut (forall x : IR, Compact Hab x -> forall Hx, m [<=] AbsIR (F x Hx[-]z));
    [ clear a0; intro a0 | intros ].
   elim (less_cotransitive_unfolded _ _ _ H m); intros.
    elim H0; clear H0; intros H0 H0'.
    cut (F a Ha[-]z [<=] [--]m); intros.
     cut (m [<=] F b Hb[-]z); intros.
      elimtype False.
      elim (contin_prop _ _ _ _ contF m a1); intros d H4 H5.
      set (incF := contin_imp_inc _ _ _ _ contF) in *.
      set (f := fun i Hi => F (compact_part _ _ Hab' d H4 i Hi)
        (incF _ (compact_part_hyp _ _ Hab Hab' d H4 i Hi)) [-]z) in *.
      set (n := compact_nat a b d H4) in *.
      cut (forall i Hi, f i Hi [<=] Zero).
       intros.
       apply (less_irreflexive_unfolded _ (F b Hb[-]z)).
       eapply less_leEq_trans.
        2: apply H3.
       apply leEq_less_trans with ZeroR.
        2: auto.
       apply leEq_wdl with (f _ (le_n n)); auto.
       unfold f, compact_part, n in |- *; simpl in |- *.
       apply cg_minus_wd; [ apply pfwdef; rational | algebra ].
      simple induction i.
       intros; unfold f, compact_part in |- *.
       apply leEq_wdl with (F a Ha[-]z).
        apply leEq_transitive with ( [--]m); auto.
        astepr ( [--]ZeroR); apply less_leEq; apply inv_resp_less; auto.
       apply cg_minus_wd; [apply pfwdef | idtac]; rational.
      intros i' Hrec HSi'.
      astepr (m[-]m).
      apply shift_leEq_minus'.
      cut (i' <= n); [ intro Hi' | auto with arith ].
      apply leEq_transitive with ( [--] (f _ Hi') [+]f _ HSi').
       apply plus_resp_leEq.
       cut ({m [<=] f _ Hi'} + {f _ Hi' [<=] [--]m}).
        intro; inversion_clear H6.
         elimtype False.
         apply (less_irreflexive_unfolded _ m).
         apply leEq_less_trans with ZeroR.
          eapply leEq_transitive; [ apply H7 | apply (Hrec Hi') ].
         auto.
        astepl ( [--][--]m); apply inv_resp_leEq; auto.
       apply leEq_distr_AbsIR.
        assumption.
       unfold f in |- *; apply a0; apply compact_part_hyp.
      rstepl (f _ HSi'[-]f _ Hi').
      eapply leEq_transitive.
       apply leEq_AbsIR.
      unfold f in |- *; simpl in |- *.
      apply leEq_wdl with (AbsIR (F _ (incF _ (compact_part_hyp _ _ Hab Hab' d H4 _ HSi')) [-]
        F _ (incF _ (compact_part_hyp _ _ Hab Hab' d H4 _ Hi')))).
       apply H5; try apply compact_part_hyp.
       eapply leEq_wdl.
        2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
        apply compact_leEq.
       apply less_leEq; apply compact_less.
      apply AbsIR_wd; rational.
     eapply leEq_wdr.
      2: apply AbsIR_eq_x.
      apply a0; apply compact_inc_rht.
     apply shift_leEq_minus; astepl z; auto.
    astepl ( [--][--] (F a Ha[-]z)); apply inv_resp_leEq.
    eapply leEq_wdr.
     2: apply AbsIR_eq_inv_x.
     apply a0; apply compact_inc_lft.
    apply shift_minus_leEq; astepr z; auto.
   elim (b0 (e[-]m)); intros.
    elim p; clear p b0; intros y Hy.
    elim Hy; intros.
    elim b0; clear b0; intros H2 H3.
    exists y; auto.
    intro.
    apply leEq_wdl with (G y H2).
     apply less_leEq.
     apply plus_cancel_less with ( [--]m).
     eapply less_wdl.
      apply q.
     unfold cg_minus in |- *; algebra.
    unfold G in |- *.
    apply eq_transitive_unfolded with (AbsIR (Part _ _ (ProjIR1 H2))).
     apply FAbs_char.
    apply AbsIR_wd; simpl in |- *; algebra.
   apply shift_less_minus; astepl m; auto.
  apply a0.
  exists x.
  split.
   auto.
  repeat split; auto.
  intro; unfold G in |- *.
  apply eq_transitive_unfolded with (AbsIR (Part _ _ (ProjIR1 Hy))).
   apply FAbs_char.
  apply AbsIR_wd; simpl in |- *; algebra.
 set (H1 := less_imp_ap _ _ _ HFab) in *.
 set (H2 := pfstrx _ _ _ _ _ _ H1) in *.
 elim (ap_imp_less _ _ _ H2); intro.
  auto.
 elimtype False.
 apply (less_irreflexive_unfolded _ a).
 apply leEq_less_trans with b; auto.
Qed.

End Lemma1.

Section Lemma2.

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variable F : PartIR.
Hypothesis contF : Continuous_I Hab F.

(**
If [f(b) [<] f(a)], a similar result holds:
*)

Lemma Weak_IVT_ap_rht : forall Ha Hb (HFab : F b Hb [<] F a Ha) e,
 Zero [<] e -> forall z, Compact (less_leEq _ _ _ HFab) z ->
 {x : IR | Compact Hab x | forall Hx, AbsIR (F x Hx[-]z) [<=] e}.
Proof.
 intros Ha Hb HFab e H z H0.
 set (G := {--}F) in *.
 assert (contG : Continuous_I Hab G).
  unfold G in |- *; Contin.
 assert (HGab : G a Ha [<] G b Hb).
  unfold G in |- *; simpl in |- *; apply inv_resp_less; auto.
 assert (H1 : Compact (less_leEq _ _ _ HGab) [--]z).
  inversion_clear H0; split; unfold G in |- *; simpl in |- *; apply inv_resp_leEq; auto.
 elim (Weak_IVT_ap_lft _ _ _ _ contG _ _ HGab _ H _ H1); intros x Hx.
 exists x; auto.
 intro; eapply leEq_wdl.
  apply (q Hx0).
 eapply eq_transitive_unfolded.
  apply AbsIR_minus.
 apply AbsIR_wd; unfold G in |- *; simpl in |- *; rational.
Qed.

End Lemma2.

Section IVT.

(**
** The IVT

We will now assume that [a [<] b] and that [F] is not only
continuous, but also strictly increasing in [I].  Under
these assumptions, we can build two sequences of values which
converge to [x0] such that [f(x0) [=] z].
*)

Variables a b : IR.
Hypothesis Hab' : a [<] b.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variable F : PartIR.
Hypothesis contF : Continuous_I Hab F.
(* begin hide *)
Let incF := contin_imp_inc _ _ _ _ contF.
(* end hide *)

(* begin show *)
Hypothesis incrF : forall x y, I x -> I y -> x [<] y -> forall Hx Hy, F x Hx [<] F y Hy.
(* end show *)

(* begin hide *)
Let Ha := compact_inc_lft _ _ Hab.
Let Hb := compact_inc_rht _ _ Hab.

Let HFab' := incrF _ _ Ha Hb Hab' (incF _ Ha) (incF _ Hb).
(* end hide *)

(* begin show *)
Variable z : IR.
Hypothesis Haz : F a (incF _ Ha) [<=] z.
Hypothesis Hzb : z [<=] F b (incF _ Hb).
(* end show *)

(** Given any two points [x [<] y] in [[a,b]] such that [x [<=] z [<=] y],
we can find [x' [<] y'] such that $|x'-y'|=\frac23|x-y|$#|x'-y'|=2/3|x-y|#
and [x' [<=] z [<=] y'].
*)

Lemma IVT_seq_lemma : forall (xy : IR ** IR) (x:=fstT xy) (y:=sndT xy)
   (Hxy : (I x) ** (I y)) (Hx := fstT Hxy) (Hy := sndT Hxy), x [<] y ->
 F x (incF _ Hx) [<=] z /\ z [<=] F y (incF _ Hy) ->
 {xy0 : IR ** IR | let x0 := fstT xy0 in let y0 := sndT xy0 in
 {Hxy0 : (I x0) ** (I y0) | x0 [<] y0 | let Hx0 := fstT Hxy0 in let Hy0 := sndT Hxy0 in
 F x0 (incF _ Hx0) [<=] z /\ z [<=] F y0 (incF _ Hy0) /\
 y0[-]x0 [=] Two [/]ThreeNZ[*] (y[-]x) /\ x [<=] x0 /\ y0 [<=] y}}.
Proof.
 (* begin hide *)
 intros xy x y Hxy Hx Hy H H0.
 set (x1 := (Two[*]x[+]y) [/]ThreeNZ) in *.
 set (y1 := (x[+]Two[*]y) [/]ThreeNZ) in *.
 assert (H1 : x1 [<] y1).
  unfold x1, y1 in |- *; apply lft_rht; auto.
 cut (I x1). intro H2. cut (I y1). intro H3.
  cut (F x1 (incF _ H2) [<] F y1 (incF _ H3)); [ intro H4 | auto ].
   elim (less_cotransitive_unfolded _ _ _ H4 z); intros.
    exists (pairT x1 y); exists (pairT H2 Hy); simpl in |- *; repeat split; auto.
         apply less_leEq_trans with y1.
          auto.
         apply less_leEq; unfold x1, y1 in |- *; apply rht_b; auto.
        apply less_leEq; auto.
       elim H0; auto.
      unfold x1 in |- *; apply smaller_rht.
     unfold x1 in |- *; apply less_leEq; apply a_lft; auto.
    apply leEq_reflexive.
   exists (pairT x y1); exists (pairT Hx H3); simpl in |- *; repeat split; auto.
        apply leEq_less_trans with x1.
         apply less_leEq; unfold x1, y1 in |- *; apply a_lft; auto.
        auto.
       elim H0; auto.
      apply less_leEq; auto.
     unfold y1 in |- *; apply smaller_lft; auto.
    apply leEq_reflexive.
   apply less_leEq; unfold y1 in |- *; apply rht_b; auto.
  unfold y1 in |- *; inversion_clear Hx; inversion_clear Hy; split.
   apply leEq_transitive with x; auto.
   apply less_leEq; apply less_transitive_unfolded with x1; unfold x1 in |- *;
     [ apply a_lft | apply lft_rht ]; auto.
  apply leEq_transitive with y; auto.
  apply less_leEq; apply rht_b; auto.
 unfold x1 in |- *; inversion_clear Hx; inversion_clear Hy; split.
  apply leEq_transitive with x; auto.
  apply less_leEq; apply a_lft; auto.
 apply leEq_transitive with y; auto.
 apply less_leEq; apply less_transitive_unfolded with y1; unfold y1 in |- *;
   [ apply lft_rht | apply rht_b ]; auto.
Qed.
(* end hide *)

(**
We now iterate this construction.
*)

Record IVT_aux_seq_type : Type :=
  {IVTseq1 : IR;
   IVTseq2 : IR;
   IVTH1   : I IVTseq1;
   IVTH2   : I IVTseq2;
   IVTprf  : IVTseq1 [<] IVTseq2;
   IVTz1   : F IVTseq1 (incF _ IVTH1) [<=] z;
   IVTz2   : z [<=] F IVTseq2 (incF _ IVTH2)}.

Definition IVT_iter : IVT_aux_seq_type -> IVT_aux_seq_type.
Proof.
 intro Haux; elim Haux; intros.
 elim (IVT_seq_lemma (pairT IVTseq3 IVTseq4) (pairT IVTH3 IVTH4) IVTprf0 (conj IVTz3 IVTz4)).
 intro x; elim x; simpl in |- *; clear x; intros.
 elim p.
 intro x; elim x; simpl in |- *; clear x; intros.
 inversion_clear q.
 inversion_clear H0.
 inversion_clear H2.
 inversion_clear H3.
 apply Build_IVT_aux_seq_type with a0 b0 a1 b1; auto.
Defined.

Definition IVT_seq : nat -> IVT_aux_seq_type.
Proof.
 intro n; induction  n as [| n Hrecn].
  apply Build_IVT_aux_seq_type with a b Ha Hb; auto.
 apply (IVT_iter Hrecn).
Defined.

(**
We now define the sequences built from this iteration, starting with [a] and [b].
*)

Definition a_seq (n : nat) := IVTseq1 (IVT_seq n).
Definition b_seq (n : nat) := IVTseq2 (IVT_seq n).

Definition a_seq_I (n : nat) : I (a_seq n) := IVTH1 (IVT_seq n).
Definition b_seq_I (n : nat) : I (b_seq n) := IVTH2 (IVT_seq n).

Lemma a_seq_less_b_seq : forall n : nat, a_seq n [<] b_seq n.
Proof.
 exact (fun n : nat => IVTprf (IVT_seq n)).
Qed.

Lemma a_seq_leEq_z : forall n : nat, F _ (incF _ (a_seq_I n)) [<=] z.
Proof.
 exact (fun n : nat => IVTz1 (IVT_seq n)).
Qed.

Lemma z_leEq_b_seq : forall n : nat, z [<=] F _ (incF _ (b_seq_I n)).
Proof.
 exact (fun n : nat => IVTz2 (IVT_seq n)).
Qed.

Lemma a_seq_mon : forall i : nat, a_seq i [<=] a_seq (S i).
Proof.
 intro.
 unfold a_seq in |- *.
 simpl in |- *.
 elim IVT_seq; simpl in |- *; intros.
 elim IVT_seq_lemma; simpl in |- *; intro.
 elim x; simpl in |- *; clear x; intros.
 elim p; clear p; intro.
 elim x; simpl in |- *; clear x; intros.
 case q; clear q; simpl in |- *; intros.
 case a2; clear a2; simpl in |- *; intros.
 case a2; clear a2; simpl in |- *; intros.
 case a2; auto.
Qed.

Lemma b_seq_mon : forall i : nat, b_seq (S i) [<=] b_seq i.
Proof.
 intro.
 unfold b_seq in |- *.
 simpl in |- *.
 elim IVT_seq; simpl in |- *; intros.
 elim IVT_seq_lemma; simpl in |- *; intro.
 elim x; simpl in |- *; clear x; intros.
 elim p; clear p; intro.
 elim x; simpl in |- *; clear x; intros.
 case q; clear q; simpl in |- *; intros.
 case a2; clear a2; simpl in |- *; intros.
 case a2; clear a2; simpl in |- *; intros.
 case a2; auto.
Qed.

Lemma a_seq_b_seq_dist_n : forall n, b_seq (S n) [-]a_seq (S n) [=] Two [/]ThreeNZ[*] (b_seq n[-]a_seq n).
Proof.
 intro.
 unfold a_seq, b_seq in |- *.
 simpl in |- *.
 elim IVT_seq; simpl in |- *; intros.
 elim IVT_seq_lemma; simpl in |- *; intro.
 elim x; simpl in |- *; clear x; intros.
 elim p; clear p; intro.
 elim x; simpl in |- *; clear x; intros.
 case q; clear q; simpl in |- *; intros.
 case a2; clear a2; simpl in |- *; intros.
 case a2; clear a2; simpl in |- *; intros.
 case a2; auto.
Qed.

Lemma a_seq_b_seq_dist : forall n, b_seq n[-]a_seq n [=] (Two [/]ThreeNZ) [^]n[*] (b[-]a).
Proof.
 simple induction n.
  simpl in |- *; algebra.
 clear n; intros.
 astepr (Two [/]ThreeNZ[*] (Two [/]ThreeNZ) [^]n[*] (b[-]a)).
 astepr (Two [/]ThreeNZ[*] ((Two [/]ThreeNZ) [^]n[*] (b[-]a))).
 astepr (Two [/]ThreeNZ[*] (b_seq n[-]a_seq n)).
 apply a_seq_b_seq_dist_n.
Qed.

Lemma a_seq_Cauchy : Cauchy_prop a_seq.
Proof.
 intros e H.
 elim (intervals_small' a b e H); intros i Hi.
 exists i; intros.
 apply AbsIR_imp_AbsSmall.
 eapply leEq_transitive.
  2: apply Hi.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
  2: apply shift_leEq_minus; astepl (a_seq i).
  2: apply local_mon'_imp_mon'; auto; exact a_seq_mon.
 eapply leEq_wdr.
  2: apply a_seq_b_seq_dist.
 apply minus_resp_leEq.
 apply less_leEq; apply a_b'.
   exact a_seq_mon.
  exact b_seq_mon.
 exact a_seq_less_b_seq.
Qed.

Lemma b_seq_Cauchy : Cauchy_prop b_seq.
Proof.
 intros e H.
 elim (intervals_small' a b e H); intros i Hi.
 exists i; intros.
 apply AbsIR_imp_AbsSmall.
 eapply leEq_transitive.
  2: apply Hi.
 eapply leEq_wdl.
  2: apply AbsIR_minus.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
  2: apply shift_leEq_minus; astepl (b_seq m).
  2: astepl ( [--][--] (b_seq m)); astepr ( [--][--] (b_seq i)).
  2: apply inv_resp_leEq; apply local_mon'_imp_mon' with (f := fun n : nat => [--] (b_seq n)); auto.
  2: intro; apply inv_resp_leEq; apply b_seq_mon.
 eapply leEq_wdr.
  2: apply a_seq_b_seq_dist.
 unfold cg_minus in |- *; apply plus_resp_leEq_lft.
 apply inv_resp_leEq.
 apply less_leEq; apply a_b'.
   exact a_seq_mon.
  exact b_seq_mon.
 exact a_seq_less_b_seq.
Qed.

Let xa := Lim (Build_CauchySeq _ _ a_seq_Cauchy).
Let xb := Lim (Build_CauchySeq _ _ b_seq_Cauchy).

Lemma a_seq_b_seq_lim : xa [=] xb.
Proof.
 unfold xa, xb in |- *; clear xa xb.
 apply cg_inv_unique_2.
 apply eq_symmetric_unfolded.
 eapply eq_transitive_unfolded.
  2: apply Lim_minus.
 simpl in |- *.
 apply Limits_unique.
 simpl in |- *.
 intros eps H.
 elim (intervals_small' a b eps H); intros i Hi.
 exists i; intros.
 apply AbsIR_imp_AbsSmall.
 eapply leEq_transitive.
  2: apply Hi.
 eapply leEq_wdl.
  2: apply AbsIR_minus.
 eapply leEq_wdl.
  2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
  2: apply shift_leEq_minus; astepl (a_seq m[-]b_seq m).
  2: apply shift_minus_leEq; astepr (b_seq m).
  2: apply less_leEq; apply a_seq_less_b_seq.
 eapply leEq_wdr.
  2: apply a_seq_b_seq_dist.
 rstepl (b_seq m[-]a_seq m).
 unfold cg_minus in |- *; apply plus_resp_leEq_both.
  astepl ( [--][--] (b_seq m)); astepr ( [--][--] (b_seq i)).
  apply inv_resp_leEq; apply local_mon'_imp_mon' with (f := fun n : nat => [--] (b_seq n)); auto.
  intro; apply inv_resp_leEq; apply b_seq_mon.
 apply inv_resp_leEq; apply local_mon'_imp_mon'; auto; exact a_seq_mon.
Qed.

Lemma xa_in_interval : I xa.
Proof.
 split.
  unfold xa in |- *.
  apply leEq_seq_so_leEq_Lim.
  simpl in |- *.
  intro; elim (a_seq_I i); auto.
 unfold xa in |- *.
 apply seq_leEq_so_Lim_leEq.
 simpl in |- *.
 intro; elim (a_seq_I i); auto.
Qed.

Lemma IVT_I : {x : IR | I x | forall Hx, F x Hx [=] z}.
Proof.
 exists xa.
  apply xa_in_interval.
 intro.
 apply cg_inv_unique_2; apply leEq_imp_eq.
  apply approach_zero.
  intros e H.
  apply leEq_less_trans with (e [/]TwoNZ).
   2: apply pos_div_two'; auto.
  elim (contin_prop _ _ _ _ contF _ (pos_div_two _ _ H)); intros d H0 H1.
  elim (Cauchy_complete (Build_CauchySeq _ _ a_seq_Cauchy) _ H0);
    fold xa in |- *; simpl in |- *; intros N HN.
  apply leEq_transitive with (F xa Hx[-]F (a_seq N) (incF _ (a_seq_I N))).
   unfold cg_minus in |- *; apply plus_resp_leEq_lft.
   apply inv_resp_leEq; apply a_seq_leEq_z.
  eapply leEq_wdl.
   2: apply AbsIR_eq_x.
   apply H1; auto.
     apply xa_in_interval.
    apply a_seq_I.
   apply AbsSmall_imp_AbsIR.
   apply AbsSmall_minus.
   auto.
  apply shift_leEq_minus; astepl (F _ (incF _ (a_seq_I N))).
  apply part_mon_imp_mon' with I; auto.
    apply a_seq_I.
   apply xa_in_interval.
  unfold xa in |- *.
  apply str_leEq_seq_so_leEq_Lim.
  exists N; intros; simpl in |- *.
  apply local_mon'_imp_mon'; auto; exact a_seq_mon.
 astepl ( [--]ZeroR); rstepr ( [--] (z[-]F xa Hx)).
 apply inv_resp_leEq.
 apply approach_zero.
 intros e H.
 apply leEq_less_trans with (e [/]TwoNZ).
  2: apply pos_div_two'; auto.
 elim (contin_prop _ _ _ _ contF _ (pos_div_two _ _ H)); intros d H0 H1.
 elim (Cauchy_complete (Build_CauchySeq _ _ b_seq_Cauchy) _ H0);
   fold xb in |- *; simpl in |- *; intros N HN.
 apply leEq_transitive with (F (b_seq N) (incF _ (b_seq_I N)) [-]F xa Hx).
  apply minus_resp_leEq; apply z_leEq_b_seq.
 eapply leEq_wdl.
  2: apply AbsIR_eq_x.
  apply H1; auto.
    apply b_seq_I.
   apply xa_in_interval.
  apply leEq_wdl with (AbsIR (b_seq N[-]xb)).
   2: apply AbsIR_wd; apply cg_minus_wd;
     [ algebra | apply eq_symmetric_unfolded; apply a_seq_b_seq_lim ].
  apply AbsSmall_imp_AbsIR.
  auto.
 apply shift_leEq_minus; astepl (F xa Hx).
 apply part_mon_imp_mon' with I; auto.
   apply xa_in_interval.
  apply b_seq_I.
 apply leEq_wdl with xb.
  2: apply eq_symmetric_unfolded; apply a_seq_b_seq_lim.
 unfold xb in |- *.
 apply str_seq_leEq_so_Lim_leEq.
 exists N; intros; simpl in |- *.
 astepl ( [--][--] (b_seq i)); astepr ( [--][--] (b_seq N)).
 apply inv_resp_leEq.
 apply local_mon'_imp_mon' with (f := fun n : nat => [--] (b_seq n)); auto.
 intro; apply inv_resp_leEq; apply b_seq_mon.
Qed.

End IVT.
