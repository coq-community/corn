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

Require Export MoreFunctions.
Require Export MoreFunSeries.

Section Maps_into_Compacts.

Section Part_Funct.

(**
* Composition

Preservation results for functional composition are treated in this
separate file.  We start by defining some auxiliary predicates, and
then prove the preservation of continuity through composition and the
chain rule for differentiation, both for compact and arbitrary
intervals.

%\begin{convention}% Throughout this section:
- [a, b : IR] and [I] will denote [[a,b]];
- [c, d : IR] and [J] will denote [[c,d]];
- [F, F', G, G'] will be partial functions.

%\end{convention}%

** Maps into Compacts

Both continuity and differentiability proofs require extra hypothesis
on the functions involved---namely, that every compact interval is
mapped into another compact interval.  We define this concept for
partial functions, and prove some trivial results.
*)

Variables F G : PartIR.
Variables a b : IR.
Hypothesis Hab : a [<=] b.

Variables c d : IR.
Hypothesis Hcd : c [<=] d.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

(* begin show *)
Hypothesis Hf : included (Compact Hab) (Dom F).
(* end show *)

Definition maps_into_compacts := included (Compact Hcd) (Dom G) and
 (forall x Hx, I x -> Compact Hcd (F x Hx)).

(* begin show *)
Hypothesis maps : maps_into_compacts.
(* end show *)

Lemma maps_lemma' : forall x Hx, I x -> Compact Hcd (F x Hx).
Proof.
 inversion_clear maps.
 assumption.
Qed.

Lemma maps_lemma : forall x, I x -> forall Hx, Compact Hcd (F x Hx).
Proof.
 intros.
 simpl in |- *.
 apply maps_lemma'.
 assumption.
Qed.

Lemma maps_lemma_inc : included (Compact Hcd) (Dom G).
Proof.
 inversion_clear maps.
 assumption.
Qed.

End Part_Funct.

End Maps_into_Compacts.

Section Mapping.

(**
As was the case for division of partial functions, this condition
completely characterizes the domain of the composite function.
*)

Variables F G : PartIR.
Variables a b : IR.
Hypothesis Hab : a [<=] b.

Variables c d : IR.
Hypothesis Hcd : c [<=] d.

(* begin show *)
Hypothesis Hf : included (Compact Hab) (Dom F).
Hypothesis Hg : included (Compact Hcd) (Dom G).
Hypothesis maps : maps_into_compacts F G a b Hab c d Hcd.
(* end show *)

Lemma included_comp : included (Compact Hab) (Dom (G[o]F)).
Proof.
 intros x H.
 simpl in |- *.
 exists (Hf x H).
 apply Hg.
 apply maps_lemma' with G a b Hab; assumption.
Qed.

End Mapping.

Section Interval_Continuity.

(**
** Continuity

We now prove that the composition of two continuous partial functions is continuous.
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variables c d : IR.
Hypothesis Hcd : c [<=] d.

Variables F G : PartIR.

(* begin show *)
Hypothesis contF : Continuous_I Hab F.
Hypothesis contG : Continuous_I Hcd G.
Hypothesis Hmap : maps_into_compacts F G a b Hab c d Hcd.
(* end show *)

Lemma Continuous_I_comp : Continuous_I Hab (G[o]F).
Proof.
 red in |- *.
 elim contF; intros incF contF'.
 elim contG; intros incG contG'.
 split.
  exact (included_comp F G a b Hab c d Hcd incF incG Hmap).
 intros e H.
 elim (contG' e H).
 intros dh H0 H1.
 elim (contF' dh H0).
 intros df H2 H3.
 exists df.
  assumption.
 intros x y H4 H5 Hx Hy H6.
 simpl in |- *.
 cut (forall x : IR, Compact Hab x -> forall Hx, Compact Hcd (F x Hx)). intro H7.
  apply leEq_wdl with (AbsIR (G _ (incG _ (H7 x H4 (incF x H4))) [-]
    G _ (incG _ (H7 y H5 (incF y H5))))).
   apply H1; simpl in |- *.
     apply H7; assumption.
    apply H7; assumption.
   apply H3; assumption.
  apply AbsIR_wd; rational.
 intros. apply maps_lemma with G a b Hab; simpl in |- *; assumption.
Qed.

End Interval_Continuity.

Section Derivative.

(**
** Derivative

We now work with the derivative relation and prove the chain rule for partial functions.
*)

Variables F F' G G' : PartIR.

Variables a b : IR.
Hypothesis Hab' : a [<] b.

Variables c d : IR.
Hypothesis Hcd' : c [<] d.

(* begin hide *)
Let Hab := less_leEq _ _ _ Hab'.
Let Hcd := less_leEq _ _ _ Hcd'.
Let I := Compact Hab.
(* end hide *)

(* begin show *)
Hypothesis derF : Derivative_I Hab' F F'.
Hypothesis derG : Derivative_I Hcd' G G'.
Hypothesis Hmap : maps_into_compacts F G a b Hab c d Hcd.
(* end show *)

Lemma included_comp' : included (Compact Hab) (Dom (G'[o]F)).
Proof.
 intros x H.
 simpl in |- *.
 exists (derivative_imp_inc _ _ _ _ _ derF x H).
 apply (derivative_imp_inc' _ _ _ _ _ derG).
 apply maps_lemma' with G a b Hab; assumption.
Qed.

Lemma maps' : maps_into_compacts F G' a b Hab c d Hcd.
Proof.
 inversion_clear Hmap.
 split.
  unfold Hcd in |- *; apply derivative_imp_inc' with G; assumption.
 assumption.
Qed.

Lemma Derivative_I_comp : Derivative_I Hab' (G[o]F) ((G'[o]F) {*}F').
Proof.
 elim derF; intros incF H1.
 elim H1; intros incF' H2.
 elim derG; intros incG H4.
 elim H4; intros incG' H5.
 clear H1 H4.
 apply Derivative_I_char.
   exact (included_comp _ _ _ _ _ _ _ _ incF incG Hmap).
  exact (included_FMult _ _ _ _ (included_comp _ _ _ _ _ _ _ _ incF incG' maps') incF').
 intros e He.
 set (contF' := deriv_imp_contin'_I _ _ _ _ _ Hab derF) in *.
 set (nF' := Norm_Funct contF') in *.
 cut ([0] [<] [1][+]nF'). intro H.
  cut ([1][+]nF'[#][0]).
   intro HnF'.
   2: apply Greater_imp_ap; assumption.
  set (alpha := ([1][/] _[//]HnF') [*]e [/]TwoNZ) in *.
  set (contG' := deriv_imp_contin'_I _ _ _ _ _ Hcd derG) in *.
  set (nH' := Norm_Funct contG') in *.
  cut ([0] [<] alpha).
   intro Halpha.
   cut ([0] [<] alpha[+]nH'). intro H0.
    cut (alpha[+]nH'[#][0]).
     intro HnH'.
     2: apply Greater_imp_ap; assumption.
    set (beta := ([1][/] _[//]HnH') [*]e [/]TwoNZ) in *.
    cut ([0] [<] beta).
     intro Hbeta.
     elim (H2 _ Hbeta).
     intros df H1 H3.
     elim (H5 _ Halpha).
     intros dg H4 H6.
     elim (contin_prop _ _ _ _ (deriv_imp_contin_I _ _ _ _ _ Hab derF) _ H4).
     intros dc H7 H8.
     exists (Min dc df).
      apply less_Min; assumption.
     intros x y H9 H10 Hx Hy Hx' H11.
     simpl in |- *.
     set (fx := F x (ProjT1 Hx)) in *.
     set (fy := F y (ProjT1 Hy)) in *.
     set (gfx := G fx (ProjT2 Hx)) in *.
     set (gfy := G fy (ProjT2 Hy)) in *.
     set (fx' := F' x (ProjIR2 Hx')) in *.
     set (gfx' := G' (F x (ProjT1 (ProjIR1 Hx'))) (ProjT2 (ProjIR1 Hx'))) in *.
     simpl in (value of fx'), (value of gfx'); fold fx' gfx' in |- *.
     apply leEq_wdl with (AbsIR (gfy[-]gfx[-]gfx'[*] (fy[-]fx) [+]gfx'[*] (fy[-]fx[-]fx'[*] (y[-]x)))).
      2: apply AbsIR_wd; rational.
     eapply leEq_transitive.
      apply triangle_IR.
     apply leEq_transitive with
       (alpha[*]nF'[*]AbsIR (y[-]x) [+]alpha[*]AbsIR (fy[-]fx[-]fx'[*] (y[-]x)) [+]
         nH'[*]AbsIR (fy[-]fx[-]fx'[*] (y[-]x))).
      apply plus_resp_leEq_both.
       apply leEq_transitive with (alpha[*]AbsIR (fy[-]fx)).
        unfold gfx' in |- *.
        cut (Dom G' fx). intro H12.
         apply leEq_wdl with (AbsIR (gfy[-]gfx[-]G' fx H12[*] (fy[-]fx))).
          unfold gfy, gfx in |- *; apply H6; unfold fx, fy in |- *.
            apply maps_lemma with G a b Hab; assumption.
           apply maps_lemma with G a b Hab; assumption.
          apply H8; try assumption.
          eapply leEq_transitive.
           apply H11.
          apply Min_leEq_lft.
         apply AbsIR_wd; unfold fx, fy, gfx, gfy in |- *; rational.
        apply (dom_wd _ G' _ fx (ProjT2 (ProjIR1 Hx'))).
        unfold fx in |- *; rational.
       rstepr (alpha[*] (nF'[*]AbsIR (y[-]x) [+]AbsIR (fy[-]fx[-]fx'[*] (y[-]x)))).
       apply mult_resp_leEq_lft.
        2: apply less_leEq; assumption.
       apply leEq_wdl with (AbsIR (fx'[*] (y[-]x) [+] (fy[-]fx[-]fx'[*] (y[-]x)))).
        2: apply un_op_wd_unfolded; rational.
       eapply leEq_transitive.
        apply triangle_IR.
       apply plus_resp_leEq.
       eapply leEq_wdl.
        2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
       apply mult_resp_leEq_rht.
        2: apply AbsIR_nonneg.
       unfold fx', nF', I in |- *; apply norm_bnd_AbsIR; assumption.
      eapply leEq_wdl.
       2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
      apply mult_resp_leEq_rht.
       2: apply AbsIR_nonneg.
      unfold gfx', nH' in |- *; apply norm_bnd_AbsIR; apply maps_lemma with G a b Hab; assumption.
     rstepl (alpha[*]nF'[*]AbsIR (y[-]x) [+] (alpha[+]nH') [*]AbsIR (fy[-]fx[-]fx'[*] (y[-]x))).
     rstepr (e [/]TwoNZ[*]ABSIR (y[-]x) [+]e [/]TwoNZ[*]ABSIR (y[-]x)).
     apply plus_resp_leEq_both.
      apply mult_resp_leEq_rht.
       2: apply AbsIR_nonneg.
      unfold alpha in |- *.
      rstepl ((nF'[/] _[//]HnF') [*]e [/]TwoNZ).
      astepr ([1][*]e [/]TwoNZ).
      apply mult_resp_leEq_rht.
       2: apply less_leEq; apply pos_div_two; assumption.
      apply shift_div_leEq'.
       apply leEq_less_trans with nF'.
        unfold nF' in |- *; apply positive_norm.
       astepr (nF'[+][1]); apply less_plusOne.
      apply less_leEq; rstepr (nF'[+][1]); apply less_plusOne.
     apply shift_mult_leEq' with HnH'.
      assumption.
     apply leEq_wdr with (beta[*]ABSIR (y[-]x)).
      2: unfold beta in |- *; rational.
     unfold fx, fy, fx' in |- *; apply H3; try assumption.
     eapply leEq_transitive.
      apply H11.
     apply Min_leEq_rht.
    unfold beta in |- *.
    astepl (ZeroR[*][0]); apply mult_resp_less_both; try apply leEq_reflexive.
     apply recip_resp_pos; assumption.
    apply pos_div_two; assumption.
   apply leEq_less_trans with nH'.
    unfold nH' in |- *; apply positive_norm.
   astepl ([0][+]nH'); apply plus_resp_less_rht; assumption.
  unfold alpha in |- *.
  astepl (ZeroR[*][0]); apply mult_resp_less_both; try apply leEq_reflexive.
   apply recip_resp_pos; assumption.
  apply pos_div_two; assumption.
 apply leEq_less_trans with nF'.
  unfold nF' in |- *; apply positive_norm.
 astepr (nF'[+][1]); apply less_plusOne.
Qed.

(**
The next lemma will be useful when we move on to differentiability.
*)

Lemma Diffble_I_comp_aux : Diffble_I Hab' (G[o]F).
Proof.
 elim derF; intros incF H1.
 elim H1; intros incF' H2.
 elim derG; intros incG H4.
 elim H4; intros incG' H5.
 clear H1 H4.
 exists (IntPartIR (included_FMult _ _ _ _ (included_comp _ _ _ _ _ _ _ _ incF incG' maps') incF')).
 eapply Derivative_I_wdr.
  2: apply Derivative_I_comp.
 FEQ.
 exact (included_FMult _ _ _ _ (included_comp _ _ _ _ _ _ _ _ incF incG' maps') incF').
Qed.

End Derivative.

Section Differentiability.

(**
** Differentiability

Finally, we move on to differentiability.
*)

Variables F G : PartIR.

Variables a b : IR.
Hypothesis Hab' : a [<] b.

Variables c d : IR.
Hypothesis Hcd' : c [<] d.

(* begin hide *)
Let Hab := less_leEq _ _ _ Hab'.
Let Hcd := less_leEq _ _ _ Hcd'.
Let I := Compact Hab.
(* end hide *)

(* begin show *)
Hypothesis diffF : Diffble_I Hab' F.
Hypothesis diffG : Diffble_I Hcd' G.
Hypothesis Hmap : maps_into_compacts F G a b Hab c d Hcd.
(* end show *)

Lemma Diffble_I_comp : Diffble_I Hab' (G[o]F).
Proof.
 elim diffF; intros f' derF.
 elim diffG; intros g' derG.
 apply Diffble_I_comp_aux with (PartInt f') (PartInt g') c d Hcd'; auto.
Qed.

End Differentiability.

Section Sequences.

(** **Sequences

Here we show that the limit of sequences of compositions is the composition of the limits.
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variables c d : IR.
Hypothesis Hcd : c [<=] d.

Variable f : nat -> PartIR.
Variable g : nat -> PartIR.
Hypothesis contf : forall n, Continuous_I Hab (f n).
Hypothesis contg : forall n, Continuous_I Hcd (g n).
Hypothesis rangef : forall n, forall (x : IR) (Hx : Dom (f n) x), I x -> Compact Hcd (f n x Hx).

(* begin hide *)
Let incf (n : nat) := contin_imp_inc _ _ _ _ (contf n).
Let incg (n : nat) := contin_imp_inc _ _ _ _ (contg n).
(* end hide *)

Section ExplicitLimit.

Variables F G : PartIR.

Hypothesis contF : Continuous_I Hab F.
Hypothesis contG : Continuous_I Hcd G.

Hypothesis convF : conv_fun_seq' _ _ Hab f F contf contF.
Hypothesis convG : conv_fun_seq' _ _ Hcd g G contg contG.

(* end hide *)
Let incF := contin_imp_inc _ _ _ _ contF.
Let incG := contin_imp_inc _ _ _ _ contG.
(* end hide *)

(* begin show *)
Hypothesis rangeF : forall (x : IR) (Hx : Dom F x), I x -> Compact Hcd (F x Hx).
(* end show *)

Lemma fun_Lim_seq_comp' : forall H H',
 conv_fun_seq' a b Hab (fun n => g n[o]f n) (G[o]F) H H'.
Proof.
 intros H H'.
 intros e He.
 destruct (convG _ (pos_div_two _ _ He)) as [N HN].
 destruct (CAnd_proj2 _ _ contG _ (pos_div_two _ _ He)) as [z Hz Hz0].
 destruct (convF _ Hz) as [M HM].
 exists (max N M).
 intros n Hn x Hx.
 assert (Hn0 : N <= n).
  apply le_trans with (max N M); auto with *.
 assert (Hn1 : M <= n).
  apply le_trans with (max N M); auto with *.
 apply AbsSmall_imp_AbsIR.
 assert (X:Continuous_I (a:=a) (b:=b) Hab (G[o]f n)).
  eapply Continuous_I_comp.
    apply contf.
   apply contG.
  (split; try assumption).
  apply (rangef n).
 rstepr (((g n[o]f n) x (contin_imp_inc a b Hab (g n[o]f n) (H n) x Hx)[-]
   ((G[o]f n) x (contin_imp_inc a b Hab _ X x Hx)))[+]
     (((G[o]f n) x (contin_imp_inc a b Hab _ X x Hx))[-]
       (G[o]F) x (contin_imp_inc a b Hab (G[o]F) H' x Hx))).
 apply AbsSmall_eps_div_two.
  apply AbsIR_imp_AbsSmall.
  simpl (AbsIR ((g n[o]f n) x (contin_imp_inc a b Hab (g n[o]f n) (H n) x Hx)[-]
    (G[o]f n) x (contin_imp_inc a b Hab (G[o]f n) X x Hx))).
  generalize (ProjT1 (contin_imp_inc a b Hab (g n[o]f n) (H n) x Hx))
    (ProjT1 (contin_imp_inc a b Hab (G[o]f n) X x Hx))
      (ProjT2 (contin_imp_inc a b Hab (g n[o]f n) (H n) x Hx))
        (ProjT2 (contin_imp_inc a b Hab (G[o]f n) X x Hx)).
  intros Y0 Y1 Y2 Y3.
  assert (fnx := pfwdef _ _ _ _ Y0 Y1 (eq_reflexive _ x)).
  assert (Y4 : Dom (g n) (f n x Y1)).
   apply (dom_wd _ (g n) (f n x Y0));assumption.
  stepl (ABSIR (g n (f n x Y1) Y4[-]G (f n x Y1) Y3)); [| apply AbsIR_wd; rational].
  generalize (rangef n x Y1 Hx).
  generalize (f n x Y1) Y4 Y3.
  clear Y0 Y1 Y2 Y3 fnx Y4.
  intros y Hy0 Hy1 Hy.
  stepl (ABSIR (g n y (contin_imp_inc c d Hcd (g n) (contg n) y Hy)[-]
    G y (contin_imp_inc c d Hcd G contG y Hy))); [| apply AbsIR_wd; rational].
  apply HN.
  assumption.
 apply AbsIR_imp_AbsSmall.
 simpl.
 apply Hz0.
   apply rangef; assumption.
  apply rangeF; assumption.
 stepl (AbsIR (f n x (contin_imp_inc a b Hab (f n) (contf n) x Hx)[-]
   F x (contin_imp_inc a b Hab F contF x Hx))); [| apply AbsIR_wd; rational].
 apply HM.
 assumption.
Qed.

End ExplicitLimit.

(**
The same is true if we don't make the limits explicit.
*)

(* begin hide *)
Hypothesis Hf : Cauchy_fun_seq _ _ _ _ contf.
Hypothesis Hg : Cauchy_fun_seq _ _ _ _ contg.
(* end hide *)

Lemma fun_Lim_seq_comp : forall H H', conv_fun_seq' a b Hab (fun n => g n[o]f n)
 (Cauchy_fun_seq_Lim _ _ _ _ _ Hg[o]Cauchy_fun_seq_Lim _ _ _ _ _ Hf) H H'.
Proof.
 intros H H' e H0.
 set (F := Cauchy_fun_seq_Lim _ _ _ _ _ Hf) in *.
 cut (Continuous_I Hab F). intro H1.
  2: unfold F in |- *; apply Cauchy_cont_Lim.
 cut (conv_fun_seq' _ _ _ _ _ contf H1).
  2: unfold F in |- *; apply Cauchy_conv_fun_seq'; assumption.
 intro Hf'.
 set (G := Cauchy_fun_seq_Lim _ _ _ _ _ Hg) in *.
 cut (Continuous_I Hcd G). intro H2.
  2: unfold G in |- *; apply Cauchy_cont_Lim.
 cut (conv_fun_seq' _ _ _ _ _ contg H2).
  2: unfold G in |- *; apply Cauchy_conv_fun_seq'; assumption.
 intro Hg'.
 assert (X: (forall (x : IR) (Hx : Dom F x), I x -> Compact Hcd (F x Hx)) ).
  intros x Hx Hx'.
  assert (X:=fun_conv_imp_seq_conv _ _ Hab _ contf _ H1 Hf' _ Hx' (fun n => incf n _ Hx') Hx).
  assert (X0:Cauchy_prop2 (fun n : nat => Part (f n) x ((fun n0 : nat => incf n0 x Hx') n))).
   exists (F x Hx).
   assumption.
  pose (cs:= (Build_CauchySeq _ _ (Cauchy_prop2_prop _ X0))).
  assert (X1:=Limits_unique cs _ X).
  apply compact_wd with (Lim cs);[|apply eq_symmetric; assumption].
  split;[apply leEq_seq_so_leEq_Lim|apply seq_leEq_so_Lim_leEq]; intros i; simpl;
    destruct (rangef i _ (incf i _ Hx') Hx'); assumption.
 apply (fun_Lim_seq_comp' _ _  H1 H2 Hf' Hg' X H); auto.
Qed.

End Sequences.

Section Series.
(** **Series

Here we show that the limit of series of composition by a constant function (on the right) is the composition with the limit.
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variables c d : IR.
Hypothesis Hcd : c [<=] d.

Variable g : nat -> PartIR.
Variable F : PartIR.
Hypothesis contF : Continuous_I Hab F.
(* begin hide *)
Let incF := contin_imp_inc _ _ _ _ contF.
(* end hide *)

Hypothesis convG : fun_series_convergent _ _ Hcd g.
Hypothesis rangeF : forall (x : IR) (Hx : Dom F x), Compact Hab x -> (Compact Hcd) (F x Hx).

Lemma conv_fun_series_comp : fun_series_convergent _ _ Hab (fun n => g n[o]F).
Proof.
 destruct convG as [contg X].
 assert (incg := fun (n : nat) => contin_imp_inc _ _ _ _ (contg n)).
 assert (incpsg : forall n : nat, included (Compact Hcd) (Dom (fun_seq_part_sum g n))).
  intros n.
  apply contin_imp_inc.
  apply fun_seq_part_sum_cont.
  assumption.
 assert (convG': forall H,  Cauchy_fun_seq _ _ Hcd (fun_seq_part_sum g) H).
  intros H.
  eapply Cauchy_fun_seq_wd.
   intros n; apply Feq_reflexive.
   apply incpsg.
  apply X.
 clear X.
 assert (X0:forall n, maps_into_compacts F (g n) _ _ Hab _ _ Hcd).
  intros n.
  split.
   apply incg.
  apply rangeF.
 set (H' := fun n : nat => Continuous_I_comp _ _ _ _ _ _ _ _ contF (contg n) (X0 n)) in *.
 exists H'.
 cut (forall n : nat, Continuous_I Hcd (fun_seq_part_sum g n)); [ intro H0 | Contin ].
 cut (forall n : nat, Continuous_I Hab ((fun_seq_part_sum g n)[o]F)); [ intro H1
   |intros n; eapply Continuous_I_comp with _ _ Hcd; Contin; split;[apply incpsg|apply rangeF]].
 apply Cauchy_fun_seq_wd with (fun n : nat => (fun_seq_part_sum g n)[o]F) H1.
  intros n.
  FEQ.
   apply contin_imp_inc; Contin.
  simpl.
  apply Sum0_wd; algebra.
 pose (G:=(Cauchy_fun_seq_Lim _ _ _ _ _ (convG' H0))).
 assert (contG:Continuous_I Hcd G).
  unfold G; Contin.
 assert (contGF:Continuous_I Hab (G[o]F)).
  apply Continuous_I_comp with c d Hcd; try assumption.
  split; try assumption.
  apply contin_imp_inc.
  assumption.
 apply conv_Cauchy_fun_seq' with (G[o]F) contGF.
 refine (fun_Lim_seq_comp' _ _ Hab _ _ Hcd _ _ (fun n => contF) H0 _ _ _ contF contG _ _ _ _ _).
    intros _; apply rangeF.
   apply fun_Lim_seq_const.
  apply (Cauchy_conv_fun_seq' _ _ _ _ _ (convG' H0)).
 assumption.
Qed.

Lemma Fun_Series_Sum_comp : forall H' : fun_series_convergent _ _ Hab (fun n => g n[o]F),
 Feq I (Fun_Series_Sum H') (Fun_Series_Sum convG[o]F).
Proof.
 intros H'.
 FEQ.
 simpl.
 apply series_sum_wd.
 algebra.
Qed.

End Series.

Section Generalized_Intervals.

(**
** Generalizations

We now generalize this results to arbitrary intervals.  We begin by generalizing the notion of mapping compacts into compacts.

%\begin{convention}% We assume [I,J] to be proper intervals.
%\end{convention}%
*)

Variables I J : interval.
Hypothesis pI : proper I.
Hypothesis pJ : proper J.

Definition maps_compacts_into_weak (F : PartIR) :=  forall a b Hab, included (compact a b Hab) I ->
 {c : IR | {d : IR | {Hcd : _ | included (Compact Hcd) J and
 (forall x Hx, Compact Hab x -> compact c d Hcd (F x Hx))}}}.

(**
Now everything comes naturally:
*)

Lemma comp_inc_lemma : forall F,
 maps_compacts_into_weak F -> forall x Hx, I x -> J (F x Hx).
Proof.
 intros F H x Hx H0.
 cut (included (Compact (leEq_reflexive _ x)) I). intro H1.
  elim (H _ _ _ H1); intros c Hc.
  elim Hc; clear Hc; intros d Hd.
  elim Hd; clear Hd; intros Hcd Hmap'.
  elim Hmap'; intros H2 H3.
  apply H2; apply H3; auto.
  split; apply leEq_reflexive.
 intros x0 H1.
 inversion_clear H1.
 apply iprop_wd with x; auto.
 apply leEq_imp_eq; auto.
Qed.

Variables F F' G G' : PartIR.
(* begin show *)
Hypothesis Hmap : maps_compacts_into_weak F.
(* end show *)

Lemma Continuous_comp : Continuous I F -> Continuous J G -> Continuous I (G[o]F).
Proof.
 intros H H0.
 elim H; clear H; intros incF contF.
 elim H0; clear H0; intros incG contG.
 split.
  intros x H.
  exists (incF _ H).
  apply incG.
  apply comp_inc_lemma; auto.
 intros a b Hab H.
 elim (Hmap _ _ Hab H); clear Hmap; intros c Hc.
 elim Hc; clear Hc; intros d Hd.
 elim Hd; clear Hd; intros Hcd Hmap'.
 inversion_clear Hmap'.
 apply Continuous_I_comp with c d Hcd; auto.
 red in |- *; intros.
 split; auto.
 Included.
Qed.

Definition maps_compacts_into (F : PartIR) :=  forall a b Hab, included (compact a b Hab) I ->
 {c : IR | {d : IR | {Hcd : _ | included (Compact (less_leEq _ _ _ Hcd)) J and
 (forall x Hx, Compact Hab x -> compact c d (less_leEq _ _ _ Hcd) (F x Hx))}}}.

Lemma maps_compacts_into_strict_imp_weak : forall F,
maps_compacts_into F -> maps_compacts_into_weak F.
Proof.
 intros X HX a b Hab Hinc.
 destruct (HX a b Hab Hinc) as [c [d [Hcd Hcd0]]].
 exists c.
 exists d.
 exists (less_leEq _ _ _ Hcd).
 assumption.
Qed.

(* begin show *)
Hypothesis Hmap' : maps_compacts_into F.
(* end show *)

Lemma Derivative_comp : Derivative I pI F F' -> Derivative J pJ G G' ->
 Derivative I pI (G[o]F) ((G'[o]F) {*}F').
Proof.
 clear Hmap.
 assert (Hmap := maps_compacts_into_strict_imp_weak F Hmap').
 intros H H0.
 elim H; clear H; intros incF H'.
 elim H'; clear H'; intros incF' derF.
 elim H0; clear H0; intros incG H'.
 elim H'; clear H'; intros incG' derG.
 split.
  simpl in |- *; red in |- *; intros x H; exists (incF _ H).
  apply incG; apply comp_inc_lemma; auto.
 split.
  apply included_FMult.
   simpl in |- *; red in |- *; intros x H; exists (incF _ H).
   apply incG'; apply comp_inc_lemma; auto.
  Included.
 intros a b Hab H.
 elim (Hmap' _ _ (less_leEq _ _ _ Hab) H); clear Hmap'; intros c Hc.
 elim Hc; clear Hc; intros d Hd.
 elim Hd; clear Hd; intros Hcd Hmap2.
 inversion_clear Hmap2.
 apply Derivative_I_comp with c d Hcd; auto.
 red in |- *; intros.
 split; auto.
 Included.
Qed.

Variable g : nat -> PartIR.

(* begin show *)
Hypothesis contF : Continuous I F.
Hypothesis convG : fun_series_convergent_IR J g.
(* end show *)

Lemma FSeries_Sum_comp_conv : fun_series_convergent_IR I (fun n => g n[o]F).
Proof.
 red in |- *; intros.
 destruct (Hmap a b Hab Hinc) as [c [d [Hcd [H0 H1]]]].
 apply conv_fun_series_comp with c d Hcd; auto.
 eapply included_imp_Continuous.
  apply contF.
 auto.
Qed.

Lemma FSeries_Sum_comp : forall H' : fun_series_convergent_IR I (fun n => g n[o]F),
 Feq I (FSeries_Sum H') (FSeries_Sum convG[o]F).
Proof.
 intros.
 apply included_Feq'; intros a b Hab Hinc.
 destruct (Hmap a b Hab Hinc) as [c [d [Hcd [H0 H1]]]].
 assert (H2:Continuous_I Hab F).
  eapply included_imp_Continuous.
   apply contF.
  auto.
 eapply Feq_transitive.
  apply (FSeries_Sum_char _ _ H' a b Hab Hinc).
 apply Feq_transitive with (Fun_Series_Sum (a:=c) (b:=d) (Hab:=Hcd) (f:=g) (convG _ _ _ H0)[o]F).
  apply Fun_Series_Sum_comp.
   auto.
  apply H1.
 eapply Feq_comp; try apply H1.
  apply Feq_reflexive.
  Included.
 apply Feq_symmetric.
 apply FSeries_Sum_char.
Qed.

Variable f : nat -> PartIR.

(* begin show *)
Hypothesis contf : forall n, Continuous I (f n).
Hypothesis contg : forall n, Continuous J (g n).
Hypothesis contG : Continuous J G.
Hypothesis Hmapf : forall a b Hab, included (compact a b Hab) I ->
{c : IR | {d : IR | {Hcd : _ | included (Compact Hcd) J and
 (forall n x Hx, Compact Hab x -> compact c d Hcd (f n x Hx))}}}.
(* end show *)

Lemma fun_Lim_seq_comp'_IR :
(conv_fun_seq'_IR _ _ _ contf contF) ->
(conv_fun_seq'_IR _ _ _ contg contG) ->
forall H H', conv_fun_seq'_IR I (fun n => g n[o]f n) (G[o]F) H H'.
Proof.
 red in |- *; intros.
 destruct (Hmapf a b Hab Hinc) as [c [d [Hcd [Hcd0 Hcd1]]]].
 eapply fun_Lim_seq_comp'.
    apply Hcd1.
   apply (X a b Hab Hinc).
  apply (X0 _ _ Hcd Hcd0).
 intros.
 assert (Y:forall n : nat, Dom (f n) x).
  intros n.
  refine (Continuous_imp_inc _ _ _ _ _).
   apply contf.
  Included.
 rename H0 into X1. 
 assert (Z:=fun_conv_imp_seq_conv _ _ _ _ _ _ _  (X a b Hab Hinc) x X1 Y Hx).
 pose (seq:= Build_CauchySeq2_y _ _ Z).
 assert (Z0:=Limits_unique seq (F x Hx) Z).
 apply (compact_wd c d Hcd (Lim seq)).
  assert (HcdX := fun n => Hcd1 n x (Y n) X1).
  split;[apply leEq_seq_so_leEq_Lim|apply seq_leEq_so_Lim_leEq];
    intros i; simpl; destruct (HcdX i); assumption.
 apply eq_symmetric; assumption.
Qed.

(* begin show *)
Hypothesis Hf : Cauchy_fun_seq_IR _ _ contf.
Hypothesis Hg : Cauchy_fun_seq_IR _ _ contg.
(* end show *)

Lemma fun_Lim_seq_comp_IR : forall H H', conv_fun_seq'_IR I (fun n => g n[o]f n)
 (Cauchy_fun_seq_Lim_IR _ _ _ Hg[o]Cauchy_fun_seq_Lim_IR _ _ _ Hf) H H'.
Proof.
 intros H H'.
 red; intros.
 destruct (Hmapf a b Hab Hinc) as [c [d [Hcd [Hcd0 Hcd1]]]].
 assert (X:forall n : nat, Continuous_I (a:=a) (b:=b) Hab (g n[o]f n)).
  intros n.
  apply Continuous_I_comp with c d Hcd.
    destruct (contf n) as [A B].
    apply B.
    assumption.
   destruct (contg n) as [A B].
   apply B.
   assumption.
  split.
   destruct (contg n) as [A B].
   eapply included_trans.
    apply Hcd0.
   assumption.
  apply Hcd1.
 assert (W:forall (x : IR) (Hx : Dom (Cauchy_fun_seq_Lim a b Hab f (fun n : nat =>
   included_imp_Continuous I (f n) (contf n) a b Hab Hinc) (Hf a b Hab Hinc)) x), Compact Hab x ->
     Compact Hcd (Cauchy_fun_seq_Lim a b Hab f
       (fun n : nat => included_imp_Continuous I (f n) (contf n) a b Hab Hinc)
         (Hf a b Hab Hinc) x Hx)).
  intros x Hx Habx.
  pose (Z:=fun i => contin_imp_inc a b Hab (f i)
    (included_imp_Continuous I (f i) (contf i) a b Hab Hinc) x Hx).
  simpl.
  assert (HcdX := fun n => Hcd1 n x (Z n) Habx).
  split;[apply leEq_seq_so_leEq_Lim|apply seq_leEq_so_Lim_leEq];
    intros i; simpl; destruct (HcdX i); assumption.
 assert (Z0:Continuous_I (a:=a) (b:=b) Hab (Cauchy_fun_seq_Lim c d Hcd g (fun n : nat =>
   included_imp_Continuous J (g n) (contg n) c d Hcd Hcd0) (Hg c d Hcd Hcd0)[o]
     Cauchy_fun_seq_Lim a b Hab f (fun n : nat =>
       included_imp_Continuous I (f n) (contf n) a b Hab Hinc) (Hf a b Hab Hinc))).
  apply Continuous_I_comp with c d Hcd; try apply Cauchy_cont_Lim.
  split.
   apply contin_imp_inc.
   apply Cauchy_cont_Lim.
  apply W.
 assert (Z:=fun_Lim_seq_comp _ _ Hab _ _ Hcd _ _ _ _ Hcd1 (Hf _ _ Hab Hinc) (Hg _ _ Hcd Hcd0) X Z0).
 eapply conv_fun_seq'_wdr;[|apply Z].
 clear Z Z0.
 apply Feq_comp with (Compact Hcd).
    apply W.
   intros x Hx Habx.
   simpl.
   pose (Z:=fun i => (Continuous_imp_inc I (f i) (contf i) x Hx)).
   assert (HcdX := fun n => Hcd1 n x (Z n) Habx).
   split;[apply leEq_seq_so_leEq_Lim|apply seq_leEq_so_Lim_leEq];
     intros i; simpl; destruct (HcdX i); assumption.
  apply Feq_symmetric.
  apply Cauchy_fun_seq_Lim_char.
 apply Feq_symmetric.
 apply Cauchy_fun_seq_Lim_char.
Qed.

End Generalized_Intervals.

Section Corollaries.

(**
Finally, some criteria to prove that a function with a specific domain maps compacts into compacts:
*)

Definition positive_fun P F := included P (Dom F) and
 {c : IR | [0] [<] c | forall y, P y -> forall Hy, c [<=] F y Hy}.

Definition negative_fun P F := included P (Dom F) and
 {c : IR | c [<] [0] | forall y, P y -> forall Hy, F y Hy [<=] c}.

Lemma positive_imp_maps_compacts_into : forall (J : interval) F,
 positive_fun J F -> Continuous J F -> maps_compacts_into J (openl [0]) F.
Proof.
 intros J F H H0 a b Hab H1.
 elim H; intros incF H2.
 elim H2; clear H H2 incF; intros MinF H H2.
 set (MaxF := Norm_Funct (included_imp_Continuous _ _ H0 _ _ _ H1) [+][1]) in *.
 cut (MinF [<] MaxF). intro H3.
  exists MinF; exists MaxF; exists H3.
  split.
   eapply included_trans.
    apply compact_map2 with (Hab' := Min_leEq_Max MinF MaxF).
   apply included_interval; simpl in |- *.
    auto.
   unfold MaxF in |- *; eapply leEq_less_trans.
    2: apply less_plusOne.
   apply positive_norm.
  intros; split.
   auto.
  unfold MaxF in |- *; eapply leEq_transitive.
   2: apply less_leEq; apply less_plusOne.
  eapply leEq_transitive.
   apply leEq_AbsIR.
  apply norm_bnd_AbsIR; auto.
 unfold MaxF in |- *; eapply leEq_less_trans.
  2: apply less_plusOne.
 apply leEq_transitive with (F a (Continuous_imp_inc _ _ H0 _ (H1 a (compact_inc_lft _ _ Hab)))).
  apply H2; auto.
  apply H1; apply compact_inc_lft.
 eapply leEq_transitive.
  apply leEq_AbsIR.
 apply norm_bnd_AbsIR; apply compact_inc_lft.
Qed.

Lemma negative_imp_maps_compacts_into : forall (J : interval) F,
 negative_fun J F -> Continuous J F -> maps_compacts_into J (openr [0]) F.
Proof.
 intros J F H H0 a b Hab H1.
 elim H; intros incF H2.
 elim H2; clear H H2 incF; intros MaxF H H2.
 set (MinF := [--] (Norm_Funct (included_imp_Continuous _ _ H0 _ _ _ H1)) [-][1]) in *.
 cut (MinF [<] MaxF). intro H3.
  exists MinF; exists MaxF; exists H3.
  split.
   eapply included_trans.
    apply compact_map2 with (Hab' := Min_leEq_Max MinF MaxF).
   apply included_interval; simpl in |- *.
    unfold MinF in |- *; eapply less_leEq_trans.
     apply minusOne_less.
    astepr ( [--]ZeroR); apply inv_resp_leEq; apply positive_norm.
   auto.
  intros; split.
   unfold MinF in |- *; eapply leEq_transitive.
    apply less_leEq; apply minusOne_less.
   astepr ( [--][--] (Part _ _ Hx)); apply inv_resp_leEq.
   eapply leEq_transitive.
    apply inv_leEq_AbsIR.
   apply norm_bnd_AbsIR; auto.
  auto.
 unfold MinF in |- *; eapply less_leEq_trans.
  apply minusOne_less.
 apply leEq_transitive with (F a (Continuous_imp_inc _ _ H0 _ (H1 a (compact_inc_lft _ _ Hab)))).
  2: apply H2; auto.
  2: apply H1; apply compact_inc_lft.
 astepr ( [--] [--] (Part _ _ (Continuous_imp_inc _ _ H0 _ (H1 _ (compact_inc_lft _ _ Hab)))));
   apply inv_resp_leEq.
 eapply leEq_transitive.
  apply inv_leEq_AbsIR.
 apply norm_bnd_AbsIR; apply compact_inc_lft.
Qed.

Lemma Continuous_imp_maps_compacts_into : forall J F,
 Continuous J F -> maps_compacts_into J realline F.
Proof.
 intros J F H a b Hab H0.
 set (ModF := Norm_Funct (included_imp_Continuous _ _ H _ _ _ H0)) in *.
 cut ( [--]ModF [<] ModF[+][1]). intro H1.
  exists ( [--]ModF); exists (ModF[+][1]); exists H1; split.
   repeat split.
  intros; unfold ModF in |- *; split.
   astepr ( [--][--] (Part _ _ Hx)); apply inv_resp_leEq.
   eapply leEq_transitive; [ apply inv_leEq_AbsIR | apply norm_bnd_AbsIR ]; auto.
  eapply leEq_transitive.
   2: apply less_leEq; apply less_plusOne.
  eapply leEq_transitive; [ apply leEq_AbsIR | apply norm_bnd_AbsIR ]; auto.
 unfold ModF in |- *.
 eapply leEq_less_trans; [ apply leEq_transitive with ZeroR | apply less_plusOne ].
  astepr ( [--]ZeroR); apply inv_resp_leEq; apply positive_norm.
 apply positive_norm.
Qed.

(**
As a corollary, we get the generalization of differentiability property.
*)

Lemma Diffble_comp : forall I J pI pJ F G, maps_compacts_into I J F ->
 Diffble I pI F -> Diffble J pJ G -> Diffble I pI (G[o]F).
Proof.
 intros I J pI pJ F G H H0 H1.
 apply Derivative_imp_Diffble with ((Deriv _ _ _ H1[o]F) {*}Deriv _ _ _ H0).
 apply Derivative_comp with J pJ; auto; apply Deriv_lemma.
Qed.

End Corollaries.

Hint Immediate included_comp: included.
Hint Immediate Continuous_I_comp Continuous_comp: continuous.
