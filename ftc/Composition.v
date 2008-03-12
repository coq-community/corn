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

Definition maps_into_compacts := c [<] d and included (Compact Hcd) (Dom G) and
 (forall x Hx, I x -> Compact Hcd (F x Hx)).

(* begin show *)
Hypothesis maps : maps_into_compacts.
(* end show *)

Lemma maps_lemma' : forall x Hx, I x -> Compact Hcd (F x Hx).
inversion_clear maps.
inversion_clear X0.
assumption.
Qed.

Lemma maps_lemma : forall x, I x -> forall Hx, Compact Hcd (F x Hx).
intros.
simpl in |- *.
apply maps_lemma'.
assumption.
Qed.

Lemma maps_lemma_less : c [<] d.
inversion_clear maps; assumption.
Qed.

Lemma maps_lemma_inc : included (Compact Hcd) (Dom G).
inversion_clear maps.
inversion_clear X0.
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
apply
 leEq_wdl
  with
    (AbsIR
       (G _ (incG _ (H7 x H4 (incF x H4))) [-]
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
intros x H.
simpl in |- *.
exists (derivative_imp_inc _ _ _ _ _ derF x H).
apply (derivative_imp_inc' _ _ _ _ _ derG).
apply maps_lemma' with G a b Hab; assumption.
Qed.

Lemma maps' : maps_into_compacts F G' a b Hab c d Hcd.
inversion_clear Hmap; inversion_clear X0.
split.
assumption.
split.
unfold Hcd in |- *; apply derivative_imp_inc' with G; assumption.
assumption.
Qed.

Lemma Derivative_I_comp : Derivative_I Hab' (G[o]F) ((G'[o]F) {*}F').
elim derF; intros incF H1.
elim H1; intros incF' H2.
elim derG; intros incG H4.
elim H4; intros incG' H5.
clear H1 H4.
apply Derivative_I_char.
exact (included_comp _ _ _ _ _ _ _ _ incF incG Hmap).
exact
 (included_FMult _ _ _ _ (included_comp _ _ _ _ _ _ _ _ incF incG' maps') incF').
intros e He.
set (contF' := deriv_imp_contin'_I _ _ _ _ _ Hab derF) in *.
set (nF' := Norm_Funct contF') in *.
cut (Zero [<] One[+]nF'). intro H.
cut (One[+]nF'[#]Zero).
intro HnF'.
2: apply Greater_imp_ap; assumption.
set (alpha := (One[/] _[//]HnF') [*]e [/]TwoNZ) in *.
set (contG' := deriv_imp_contin'_I _ _ _ _ _ Hcd derG) in *.
set (nH' := Norm_Funct contG') in *.
cut (Zero [<] alpha).
intro Halpha.
cut (Zero [<] alpha[+]nH'). intro H0.
cut (alpha[+]nH'[#]Zero).
intro HnH'.
2: apply Greater_imp_ap; assumption.
set (beta := (One[/] _[//]HnH') [*]e [/]TwoNZ) in *.
cut (Zero [<] beta).
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
apply
 leEq_wdl
  with
    (AbsIR (gfy[-]gfx[-]gfx'[*] (fy[-]fx) [+]gfx'[*] (fy[-]fx[-]fx'[*] (y[-]x)))).
2: apply AbsIR_wd; rational.
eapply leEq_transitive.
apply triangle_IR.
apply
 leEq_transitive
  with
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
unfold gfx', nH' in |- *; apply norm_bnd_AbsIR;
 apply maps_lemma with G a b Hab; assumption.
rstepl
 (alpha[*]nF'[*]AbsIR (y[-]x) [+]
  (alpha[+]nH') [*]AbsIR (fy[-]fx[-]fx'[*] (y[-]x))).
rstepr (e [/]TwoNZ[*]ABSIR (y[-]x) [+]e [/]TwoNZ[*]ABSIR (y[-]x)).
apply plus_resp_leEq_both.
apply mult_resp_leEq_rht.
2: apply AbsIR_nonneg.
unfold alpha in |- *.
rstepl ((nF'[/] _[//]HnF') [*]e [/]TwoNZ).
astepr (One[*]e [/]TwoNZ).
apply mult_resp_leEq_rht.
2: apply less_leEq; apply pos_div_two; assumption.
apply shift_div_leEq'.
apply leEq_less_trans with nF'.
unfold nF' in |- *; apply positive_norm.
astepr (nF'[+]One); apply less_plusOne.
apply less_leEq; rstepr (nF'[+]One); apply less_plusOne.
apply shift_mult_leEq' with HnH'.
assumption.
apply leEq_wdr with (beta[*]ABSIR (y[-]x)).
2: unfold beta in |- *; rational.
unfold fx, fy, fx' in |- *; apply H3; try assumption.
eapply leEq_transitive.
apply H11.
apply Min_leEq_rht.
unfold beta in |- *.
astepl (ZeroR[*]Zero); apply mult_resp_less_both; try apply leEq_reflexive.
apply recip_resp_pos; assumption.
apply pos_div_two; assumption.
apply leEq_less_trans with nH'.
unfold nH' in |- *; apply positive_norm.
astepl (Zero[+]nH'); apply plus_resp_less_rht; assumption.
unfold alpha in |- *.
astepl (ZeroR[*]Zero); apply mult_resp_less_both; try apply leEq_reflexive.
apply recip_resp_pos; assumption.
apply pos_div_two; assumption.
apply leEq_less_trans with nF'.
unfold nF' in |- *; apply positive_norm.
astepr (nF'[+]One); apply less_plusOne.
Qed.

(**
The next lemma will be useful when we move on to differentiability.
*)

Lemma Diffble_I_comp_aux : Diffble_I Hab' (G[o]F).
elim derF; intros incF H1.
elim H1; intros incF' H2.
elim derG; intros incG H4.
elim H4; intros incG' H5.
clear H1 H4.
exists
 (IntPartIR
    (included_FMult _ _ _ _ (included_comp _ _ _ _ _ _ _ _ incF incG' maps')
       incF')).
eapply Derivative_I_wdr.
2: apply Derivative_I_comp.
FEQ.
exact
 (included_FMult _ _ _ _ (included_comp _ _ _ _ _ _ _ _ incF incG' maps') incF').
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
elim diffF; intros f' derF.
elim diffG; intros g' derG.
apply Diffble_I_comp_aux with (PartInt f') (PartInt g') c d Hcd'; auto.
Qed.

End Differentiability.

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

Definition maps_compacts_into (F : PartIR) :=  forall a b Hab, included (compact a b Hab) I ->
 {c : IR | {d : IR | {Hcd : _ | included (Compact (less_leEq _ c d Hcd)) J and
 (forall x Hx, Compact Hab x -> Compact (less_leEq _ _ _ Hcd) (F x Hx))}}}.

(**
Now everything comes naturally:
*)

Lemma comp_inc_lemma : forall F,
 maps_compacts_into F -> forall x Hx, I x -> J (F x Hx).
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
Hypothesis Hmap : maps_compacts_into F.
(* end show *)

Lemma Continuous_comp : Continuous I F -> Continuous J G -> Continuous I (G[o]F).
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
apply Continuous_I_comp with c d (less_leEq _ _ _ Hcd); auto.
red in |- *; intros.
split; auto.
split; auto.
Included.
Qed.

(* begin show *)
Hypothesis Hmap' : maps_compacts_into F'.
(* end show *)

Lemma Derivative_comp : Derivative I pI F F' -> Derivative J pJ G G' ->
 Derivative I pI (G[o]F) ((G'[o]F) {*}F').
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
elim (Hmap _ _ (less_leEq _ _ _ Hab) H); clear Hmap; intros c Hc.
elim Hc; clear Hc; intros d Hd.
elim Hd; clear Hd; intros Hcd Hmap2.
inversion_clear Hmap2.
apply Derivative_I_comp with c d Hcd; auto.
red in |- *; intros.
split; auto.
split; auto.
Included.
Qed.

End Generalized_Intervals.

Section Corollaries.

(**
Finally, some criteria to prove that a function with a specific domain maps compacts into compacts:
*)

Definition positive_fun P F := included P (Dom F) and
 {c : IR | Zero [<] c | forall y, P y -> forall Hy, c [<=] F y Hy}.

Definition negative_fun P F := included P (Dom F) and
 {c : IR | c [<] Zero | forall y, P y -> forall Hy, F y Hy [<=] c}.

Lemma positive_imp_maps_compacts_into : forall (J : interval) F,
 positive_fun J F -> Continuous J F -> maps_compacts_into J (openl Zero) F.
intros J F H H0 a b Hab H1.
elim H; intros incF H2.
elim H2; clear H H2 incF; intros MinF H H2.
set (MaxF := Norm_Funct (included_imp_Continuous _ _ H0 _ _ _ H1) [+]One) in *.
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
apply
 leEq_transitive
  with (F a (Continuous_imp_inc _ _ H0 _ (H1 a (compact_inc_lft _ _ Hab)))).
apply H2; auto.
apply H1; apply compact_inc_lft.
eapply leEq_transitive.
apply leEq_AbsIR.
apply norm_bnd_AbsIR; apply compact_inc_lft.
Qed.

Lemma negative_imp_maps_compacts_into : forall (J : interval) F,
 negative_fun J F -> Continuous J F -> maps_compacts_into J (openr Zero) F.
intros J F H H0 a b Hab H1.
elim H; intros incF H2.
elim H2; clear H H2 incF; intros MaxF H H2.
set
 (MinF := [--] (Norm_Funct (included_imp_Continuous _ _ H0 _ _ _ H1)) [-]One)
 in *.
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
apply
 leEq_transitive
  with (F a (Continuous_imp_inc _ _ H0 _ (H1 a (compact_inc_lft _ _ Hab)))).
2: apply H2; auto.
2: apply H1; apply compact_inc_lft.
astepr
 ( [--]
  [--]
  (Part _ _ (Continuous_imp_inc _ _ H0 _ (H1 _ (compact_inc_lft _ _ Hab)))));
 apply inv_resp_leEq.
eapply leEq_transitive.
apply inv_leEq_AbsIR.
apply norm_bnd_AbsIR; apply compact_inc_lft.
Qed.

Lemma Continuous_imp_maps_compacts_into : forall J F,
 Continuous J F -> maps_compacts_into J realline F.
intros J F H a b Hab H0.
set (ModF := Norm_Funct (included_imp_Continuous _ _ H _ _ _ H0)) in *.
cut ( [--]ModF [<] ModF[+]One). intro H1.
exists ( [--]ModF); exists (ModF[+]One); exists H1; split.
repeat split.
intros; unfold ModF in |- *; split.
astepr ( [--][--] (Part _ _ Hx)); apply inv_resp_leEq.
eapply leEq_transitive; [ apply inv_leEq_AbsIR | apply norm_bnd_AbsIR ]; auto.
eapply leEq_transitive.
2: apply less_leEq; apply less_plusOne.
eapply leEq_transitive; [ apply leEq_AbsIR | apply norm_bnd_AbsIR ]; auto.
unfold ModF in |- *.
eapply leEq_less_trans;
 [ apply leEq_transitive with ZeroR | apply less_plusOne ].
astepr ( [--]ZeroR); apply inv_resp_leEq; apply positive_norm.
apply positive_norm.
Qed.

(**
As a corollary, we get the generalization of differentiability property.
*)

Lemma Diffble_comp : forall I J pI pJ F G, maps_compacts_into I J F ->
 Diffble I pI F -> Diffble J pJ G -> Diffble I pI (G[o]F).
intros I J pI pJ F G H H0 H1.
apply Derivative_imp_Diffble with ((Deriv _ _ _ H1[o]F) {*}Deriv _ _ _ H0).
apply Derivative_comp with J pJ; auto; apply Deriv_lemma.
Qed.

End Corollaries.

Hint Immediate included_comp: included.
Hint Immediate Continuous_I_comp Continuous_comp: continuous.
