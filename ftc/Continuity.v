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

(** printing Norm_Funct %\ensuremath{\|\cdot\|}% *)

Require Export CoRN.reals.NRootIR.
Require Export CoRN.ftc.FunctSums.
Require Import CoRN.tactics.CornTac.

Section Definitions_and_Basic_Results.

(**
* Continuity

Constructively, continuity is the most fundamental property of any
function---so strongly that no example is known of a constructive
function that is not continuous.  However, the classical definition of
continuity is not good for our purposes, as it is not true, for
example, that a function which is continuous in a compact interval is
uniformly continuous in that same interval (for a discussion of this
see Bishop 1967).  Thus, our notion of continuity will be the uniform
one#. #%\footnote{%Similar remarks apply to convergence of sequences
of functions, which we will define ahead, and elsewhere; we will
refrain from discussing this issue at those places.%}.%

%\begin{convention}% Throughout this section, [a] and [b] will be real
numbers, [I] will denote the compact interval [[a,b]] and
[F, G, H] will denote arbitrary partial functions with domains
respectively [P, Q] and [R].
%\end{convention}%

** Definitions and Basic Results

Here we define continuity and prove some basic properties of continuous functions.
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variable F : PartIR.
(* begin hide *)
Let P := Dom F.
(* end hide *)

Definition Continuous_I := included I P and (forall e, [0] [<] e -> {d : IR | [0] [<] d |
 forall x y, I x -> I y -> forall Hx Hy, AbsIR (x[-]y) [<=] d -> AbsIR (F x Hx[-]F y Hy) [<=] e}).

(**
For convenience, we distinguish the two properties of continuous functions.
*)

Lemma contin_imp_inc : Continuous_I -> included (Compact Hab) P.
Proof.
 intro H; elim H; intros; assumption.
Qed.

Lemma contin_prop : Continuous_I -> forall e, [0] [<] e -> {d : IR | [0] [<] d |
 forall x y, I x -> I y -> forall Hx Hy, AbsIR (x[-]y) [<=] d -> AbsIR (F x Hx[-]F y Hy) [<=] e}.
Proof.
 intro H; elim H; do 2 intro; assumption.
Qed.

(**
Assume [F] to be continuous in [I].  Then it has a least upper bound and a greater lower bound on [I].
*)

Hypothesis contF : Continuous_I.

(* begin hide *)
Let Hinc' := contin_imp_inc contF.
(* end hide *)

Lemma Continuous_I_imp_tb_image : totally_bounded (fun_image F I).
Proof.
 assert (H := compact_is_totally_bounded a b Hab).
 elim contF; intros H0 H1.
 split.
  elim H; clear H; intros H2 H3.
  elim H2; clear H2; intros x H.
  exists (Part F x (H0 _ H)).
  exists x; split.
   auto.
  split.
   apply H0; auto.
  algebra.
 intros e H2.
 elim (H1 _ H2).
 intros d H3 H4.
 clear H1.
 elim H; clear H.
 intros non_empty H.
 elim H with d; clear H.
  intros l Hl' Hl.
  2: assumption.
 exists (map2 F l (fun (x : IR) (Hx : member x l) => H0 x (Hl' x Hx))).
  intros x H.
  clear Hl; induction  l as [| a0 l Hrecl].
   elimtype False; assumption.
  simpl in H; elim H; clear H; intro H1.
   cut (forall x : IR, member x l -> compact a b Hab x).
    intro H.
    apply Hrecl with H.
    eapply map2_wd.
    apply H1.
   intros x0 H.
   apply Hl'; left; assumption.
  exists a0.
  split.
   apply Hl'; right; algebra.
  split.
   apply H0; apply Hl'; right; algebra.
  intro; eapply eq_transitive_unfolded.
   2: apply eq_symmetric_unfolded; apply H1.
  algebra.
 intros x H; simpl in |- *.
 elim H; intros x0 H1.
 elim H1; clear H1; intros Hy' H1.
 elim H1; intros Hy'' Hy.
 elim (Hl x0 Hy'); intros x1 Hx1 H5.
 exists (F x1 (H0 x1 (Hl' x1 Hx1))).
  apply map2_pres_member; assumption.
 astepr (F x0 Hy''[-]F x1 (H0 x1 (Hl' x1 Hx1))).
 apply AbsIR_imp_AbsSmall.
 apply H4.
   assumption.
  apply Hl'; assumption.
 apply AbsSmall_imp_AbsIR; assumption.
Qed.

Lemma Continuous_I_imp_lub : {x : IR | fun_lub_IR F I x}.
Proof.
 unfold fun_lub_IR in |- *.
 apply totally_bounded_has_lub.
 apply Continuous_I_imp_tb_image.
Qed.

Lemma Continuous_I_imp_glb : {x : IR | fun_glb_IR F I x}.
Proof.
 unfold fun_glb_IR in |- *.
 apply totally_bounded_has_glb.
 apply Continuous_I_imp_tb_image.
Qed.

(**
We now make this glb and lub into operators.
*)

Definition lub_funct := ProjT1 Continuous_I_imp_lub.
Definition glb_funct := ProjT1 Continuous_I_imp_glb.

(**
These operators have the expected properties.
*)

Lemma lub_is_lub : fun_lub_IR F I lub_funct.
Proof.
 exact (ProjT2 Continuous_I_imp_lub).
Qed.

Lemma glb_is_glb : fun_glb_IR F I glb_funct.
Proof.
 exact (ProjT2 Continuous_I_imp_glb).
Qed.

Lemma glb_prop : forall x : IR, I x -> forall Hx, glb_funct [<=] F x Hx.
Proof.
 intros.
 elim glb_is_glb.
 intros.
 apply a0.
 exists x.
 split; algebra.
Qed.

Lemma lub_prop : forall x : IR, I x -> forall Hx, F x Hx [<=] lub_funct.
Proof.
 intros.
 elim lub_is_lub.
 intros.
 apply a0.
 exists x.
 split; algebra.
Qed.

(**
The norm of a function is defined as being the supremum of its absolute value; that is equivalent to the following definition (which is often more convenient to use).
*)

Definition Norm_Funct := Max lub_funct [--]glb_funct.

(**
The norm effectively bounds the absolute value of a function.
*)

Lemma norm_bnd_AbsIR : forall x, I x -> forall Hx, AbsIR (F x Hx) [<=] Norm_Funct.
Proof.
 intros.
 generalize lub_is_lub.
 generalize glb_is_glb.
 intros; simpl in |- *; unfold ABSIR in |- *.
 apply Max_leEq.
  apply leEq_transitive with lub_funct.
   apply lub_prop; auto.
  unfold Norm_Funct in |- *; apply lft_leEq_Max.
 apply leEq_transitive with ( [--]glb_funct).
  apply inv_resp_leEq.
  apply glb_prop; auto.
 unfold Norm_Funct in |- *; apply rht_leEq_Max.
Qed.

(**
The following is another way of characterizing the norm:
*)

Lemma Continuous_I_imp_abs_lub : {z : IR | forall x, I x -> forall Hx, AbsIR (F x Hx) [<=] z}.
Proof.
 exists Norm_Funct.
 exact norm_bnd_AbsIR.
Qed.

(**
We now prove some basic properties of the norm---namely that it is positive, and that it provides a least upper bound for the absolute value of its argument.
*)

Lemma positive_norm : [0] [<=] Norm_Funct.
Proof.
 apply leEq_transitive with (AbsIR (FRestr Hinc' a (compact_inc_lft _ _ _))).
  apply AbsIR_nonneg.
 simpl in |- *; apply norm_bnd_AbsIR; unfold I in |- *; apply compact_inc_lft.
Qed.

Lemma norm_fun_lub : forall e, [0] [<] e -> {x : IR | I x and (forall Hx, Norm_Funct[-]e [<] AbsIR (F x Hx))}.
Proof.
 intros e H.
 cut {x : IR | I x and (forall Hx' : P x, Norm_Funct [<] AbsIR (F x Hx') [+]e)}.
  intro H0.
  elim H0; intros y Hy.
  elim Hy; clear H0 Hy; intros Hy Hy'.
  exists y; split.
   auto.
  intro; apply shift_minus_less; apply Hy'.
 generalize lub_is_lub.
 generalize glb_is_glb.
 intros H0 H1.
 cut {x : IR | I x and (forall Hx' : P x, F x Hx' [<] glb_funct[+]e [/]TwoNZ)}.
  cut {x : IR | I x and (forall Hx' : P x, lub_funct[-]e [/]TwoNZ [<] F x Hx')}.
   intros H2 H3.
   elim H2; intros x Hx.
   elim Hx; clear H2 Hx; intros Hx Hx0.
   elim H3; intros x' Hx'.
   elim Hx'; clear H3 Hx'; intros Hx' Hx'0.
   elim (less_cotransitive_unfolded _ _ _ (pos_div_two _ _ H) ( [--]glb_funct[-]lub_funct)); intro H2.
    exists x'; split.
     auto.
    unfold Norm_Funct in |- *.
    intro; eapply less_wdl.
     2: apply eq_symmetric_unfolded; apply leEq_imp_Max_is_rht.
     apply shift_less_plus.
     rstepl ( [--] (glb_funct[+]e)).
     eapply less_leEq_trans.
      2: apply inv_leEq_AbsIR.
     apply inv_resp_less.
     eapply less_transitive_unfolded.
      apply Hx'0 with (Hx' := Hx'1).
     apply plus_resp_less_lft.
     apply pos_div_two'; assumption.
    astepl ([0][+]lub_funct); apply less_leEq; apply shift_plus_less.
    assumption.
   exists x; split.
    auto.
   unfold Norm_Funct in |- *.
   intro; apply less_leEq_trans with (lub_funct[+]e [/]TwoNZ).
    apply Max_less.
     apply shift_less_plus'; astepl ZeroR.
     apply pos_div_two; assumption.
    apply shift_less_plus'; assumption.
   apply shift_leEq_plus.
   rstepl (lub_funct[-]e [/]TwoNZ).
   eapply leEq_transitive.
    apply less_leEq; apply Hx0 with (Hx' := Hx'1).
   apply leEq_AbsIR.
  elim H1; clear H1; intros H2 H3.
  elim (H3 _ (pos_div_two _ _ H)).
  intros x Hx; elim Hx; clear Hx; intros y Hx'; elim Hx'; clear Hx';
    intros Hx' Hx''; elim Hx''; clear Hx''; intros Hx'' Hx'''.
  exists y; split.
   auto.
  intro; apply shift_minus_less; apply shift_less_plus'.
  eapply less_wdl; [ apply q | algebra ].
 elim H0; clear H0; intros H2 H3.
 elim (H3 _ (pos_div_two _ _ H)).
 intros x Hx; elim Hx; clear Hx; intros y Hx'; elim Hx'; clear Hx';
   intros Hx' Hx''; elim Hx''; clear Hx''; intros Hx'' Hx'''.
 exists y; split.
  auto.
 intro; apply shift_less_plus'.
 eapply less_wdl; [ apply q | algebra ].
Qed.

Lemma leEq_Norm_Funct : forall e, (forall x, I x -> forall Hx, AbsIR (F x Hx) [<=] e) -> Norm_Funct [<=] e.
Proof.
 intros e H.
 astepr ([0][+]e); apply shift_leEq_plus.
 apply approach_zero_weak.
 intros d Hd.
 apply shift_minus_leEq.
 elim (norm_fun_lub d Hd); intros x Hx.
 elim Hx; clear Hx; intros Hx Hx'.
 apply plus_cancel_leEq_rht with ( [--] (AbsIR (F x (Hinc' x Hx)))).
 astepl (Norm_Funct[-]AbsIR (F x (Hinc' x Hx))).
 apply less_leEq; apply less_leEq_trans with d.
  apply shift_minus_less; apply shift_less_plus'; apply Hx'.
 rstepr (d[+] (e[-]AbsIR (F x (Hinc' x Hx)))).
 astepl (d[+][0]); apply plus_resp_leEq_lft.
 apply shift_leEq_minus; astepl (AbsIR (F x (Hinc' x Hx))); apply H; assumption.
Qed.

Lemma less_Norm_Funct : forall e, (forall x, I x -> forall Hx, AbsIR (F x Hx) [<] e) -> Norm_Funct [<=] e.
Proof.
 intros x H.
 apply leEq_Norm_Funct.
 intros; apply less_leEq; apply H; assumption.
Qed.

End Definitions_and_Basic_Results.

Arguments Continuous_I [a b].
Arguments Norm_Funct [a b Hab F].

Section Local_Results.

(**
** Algebraic Properties

We now state and prove some results about continuous functions.  Assume that [I] is included in the domain of both [F] and [G].
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variables F G : PartIR.

(* begin hide *)
Let P := Dom F.
Let Q := Dom G.
(* end hide *)

Hypothesis incF : included (Compact Hab) P.
Hypothesis incG : included (Compact Hab) Q.

(**
The first result does not require the function to be continuous; however, its preconditions are easily verified by continuous functions, which justifies its inclusion in this section.
*)

Lemma cont_no_sign_change : forall e, [0] [<] e -> forall x y, I x -> I y ->
 forall Hx Hy, AbsIR (F x Hx[-]F y Hy) [<=] e -> e [<] AbsIR (F x Hx) ->
 ([0] [<] F x Hx -> [0] [<] F y Hy) and (F x Hx [<] [0] -> F y Hy [<] [0]).
Proof.
 intros e H x y H0 H1 Hx Hy H2 H3.
 set (fx := F x Hx) in *.
 set (fy := F y Hy) in *.
 split; intro H4.
  cut (e [<] fx).
   intro H5.
   astepl (e[-]e).
   apply shift_minus_less; apply shift_less_plus'.
   apply less_leEq_trans with (fx[-]fy).
    apply minus_resp_less; assumption.
   eapply leEq_transitive; [ apply leEq_AbsIR | assumption ].
  elim (less_AbsIR _ _ H H3); intro H6.
   assumption.
  elimtype False.
  cut ([0] [<] [--]e).
   intro; cut (e [<] [0]).
    exact (less_antisymmetric_unfolded _ _ _ H).
   astepl ( [--][--]e); astepr ( [--]ZeroR); apply inv_resp_less; assumption.
  apply less_transitive_unfolded with fx; assumption.
 astepr (e[-]e).
 apply shift_less_minus.
 apply less_leEq_trans with (fy[-]fx).
  2: eapply leEq_transitive.
   3: apply H2.
  2: eapply leEq_wdr; [ apply leEq_AbsIR | apply AbsIR_minus ].
 unfold cg_minus in |- *; apply plus_resp_less_lft.
 elim (less_AbsIR _ _ H H3); intro H6.
  apply less_transitive_unfolded with ZeroR.
   apply less_transitive_unfolded with fx; assumption.
  astepl ( [--]ZeroR); apply inv_resp_less; assumption.
 astepl ( [--][--]e); apply inv_resp_less; assumption.
Qed.

Lemma cont_no_sign_change_pos : forall e, [0] [<] e -> forall x y, I x -> I y -> forall Hx Hy,
 AbsIR (F x Hx[-]F y Hy) [<=] e -> e [<] AbsIR (F x Hx) -> e [<] F x Hx -> [0] [<] F y Hy.
Proof.
 intros e H x y H0 H1 Hx Hy H2 H3 H4.
 elim (cont_no_sign_change e H x y H0 H1 Hx Hy H2 H3); intros H5 H6.
 apply H5.
 apply less_transitive_unfolded with e; auto.
Qed.

Lemma cont_no_sign_change_neg : forall e, [0] [<] e -> forall x y, I x -> I y -> forall Hx Hy,
 AbsIR (F x Hx[-]F y Hy) [<=] e -> e [<] AbsIR (F x Hx) -> F x Hx [<] [--]e -> F y Hy [<] [0].
Proof.
 intros e H x y H0 H1 Hx Hy H2 H3 H4.
 elim (cont_no_sign_change e H x y H0 H1 Hx Hy H2 H3); intros H5 H6.
 apply H6.
 apply less_transitive_unfolded with ( [--]e).
  assumption.
 astepr ( [--]ZeroR); apply inv_resp_less; assumption.
Qed.

(**
Being continuous is an extensional property.
*)

Lemma Continuous_I_wd : Feq I F G -> Continuous_I Hab F -> Continuous_I Hab G.
Proof.
 intros H H0.
 elim H0; clear H0; intros Hinc H0.
 elim H; clear H; intros incF' H'.
 elim H'; clear H'; intros incG' H.
 split.
  apply incG'.
 intros e He; elim (H0 e He); clear H0; intros d H0 H1.
 exists d.
  assumption.
 intros x y H2 H3 Hx Hy H4.
 apply leEq_wdl with (AbsIR (F x (incF' x H2) [-]F y (incF' y H3))).
  apply H1; assumption.
 simpl in H.
 apply AbsIR_wd.
 apply cg_minus_wd; apply H; assumption.
Qed.

(**
A continuous function remains continuous if you restrict its domain.
*)

Lemma included_imp_contin : forall c d Hcd,
 included (compact c d Hcd) (Compact Hab) -> Continuous_I Hab F -> Continuous_I Hcd F.
Proof.
 intros c d Hcd H H0.
 elim H0; clear H0; intros incF' contF.
 split.
  apply included_trans with (Compact Hab); [ apply H | apply incF' ].
 intros e He; elim (contF e He); intros e' H0 H1.
 exists e'.
  assumption.
 intros; apply H1.
   apply H; assumption.
  apply H; assumption.
 assumption.
Qed.

(**
Constant functions and identity are continuous.
*)

Lemma Continuous_I_const : forall c : IR, Continuous_I Hab [-C-]c.
Proof.
 intro.
 split.
  Included.
 intros; exists OneR.
  apply pos_one.
 intros.
 apply leEq_wdl with (AbsIR [0]).
  astepl ZeroR; apply less_leEq; assumption.
 algebra.
Qed.

Lemma Continuous_I_id : Continuous_I Hab FId.
Proof.
 split.
  Included.
 intros; exists e.
  assumption.
 intros; assumption.
Qed.

(**
Assume [F] and [G] are continuous in [I].  Then functions derived from these through algebraic operations are also continuous, provided (in the case of reciprocal and division) some extra conditions are met.
*)

Hypothesis contF : Continuous_I Hab F.
Hypothesis contG : Continuous_I Hab G.

Lemma Continuous_I_plus : Continuous_I Hab (F{+}G).
Proof.
 clear incF incG.
 elim contF; intros incF' contF'.
 elim contG; intros incG' contG'.
 split.
  Included.
 intros.
 elim (contF' (e [/]TwoNZ)).
  elim (contG' (e [/]TwoNZ)).
   clear contF contG contF' contG'.
   2: apply pos_div_two; assumption.
  2: apply pos_div_two; assumption.
 intros df H0 H1 dg H2 H3.
 exists (Min df dg).
  apply less_Min; assumption.
 intros.
 simpl in |- *.
 apply leEq_wdl with (AbsIR (F x (ProjIR1 Hx) [-]F y (ProjIR1 Hy) [+]
   (G x (ProjIR2 Hx) [-]G y (ProjIR2 Hy)))).
  rstepr (e [/]TwoNZ[+]e [/]TwoNZ).
  eapply leEq_transitive.
   apply triangle_IR.
  apply plus_resp_leEq_both.
   simpl in |- *; apply H3; try assumption.
   apply leEq_transitive with (Min df dg); [ assumption | apply Min_leEq_rht ].
  simpl in |- *; apply H1; try assumption.
  apply leEq_transitive with (Min df dg); [ assumption | apply Min_leEq_lft ].
 apply AbsIR_wd; rational.
Qed.

Lemma Continuous_I_inv : Continuous_I Hab {--}F.
Proof.
 clear incF.
 elim contF; intros incF' contF'.
 split.
  Included.
 intros e H.
 elim (contF' e H).
 intros d H0 H1.
 exists d.
  assumption.
 intros; simpl in |- *.
 apply leEq_wdl with (AbsIR (F x Hx[-]F y Hy)).
  apply H1; assumption.
 eapply eq_transitive_unfolded.
  apply AbsIR_inv.
 apply AbsIR_wd; rational.
Qed.

Lemma Continuous_I_mult : Continuous_I Hab (F{*}G).
Proof.
 clear incF incG.
 elim contF; intros incF' contF'.
 elim contG; intros incG' contG'.
 split; [ Included | intros e H ].
 cut {xf : IR | forall (x : IR) (Hx : I x) (Hx' : P x), AbsIR (F x Hx') [<=] xf}.
  cut {xg : IR | forall (x : IR) (Hx : I x) (Hx' : Q x), AbsIR (G x Hx') [<=] xg}.
   2: unfold I, Q in |- *; apply Continuous_I_imp_abs_lub; assumption.
  2: unfold I, P in |- *; apply Continuous_I_imp_abs_lub; assumption.
 intros H0 H1.
 elim H0; clear H0; intros x H2.
 elim H1; clear H1; intros x0 H0.
 elim (contF' (e [/]TwoNZ[/] Max x [1][//]max_one_ap_zero _)); clear contF.
  elim (contG' (e [/]TwoNZ[/] Max x0 [1][//]max_one_ap_zero _)); clear contG.
   intros dg H1 H3 df H4 H5.
   2: apply div_resp_pos.
    2: apply pos_max_one.
   2: apply pos_div_two; assumption.
  2: apply div_resp_pos.
   2: apply pos_max_one.
  2: apply pos_div_two; assumption.
 exists (Min df dg).
  apply less_Min; assumption.
 intros; simpl in |- *.
 rstepr (e [/]TwoNZ[+]e [/]TwoNZ).
 apply leEq_wdl with (AbsIR (F x1 (ProjIR1 Hx) [*] (G x1 (ProjIR2 Hx) [-]G y (ProjIR2 Hy)) [+]
   (F x1 (ProjIR1 Hx) [-]F y (ProjIR1 Hy)) [*]G y (ProjIR2 Hy))).
  eapply leEq_transitive.
   apply triangle_IR.
  apply plus_resp_leEq_both.
   eapply leEq_wdl.
    2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
   apply leEq_transitive with (x0[*]AbsIR (G x1 (ProjIR2 Hx) [-]G y (ProjIR2 Hy))).
    apply mult_resp_leEq_rht.
     apply H0; assumption.
    apply AbsIR_nonneg.
   apply leEq_transitive with (Max x0 [1][*]AbsIR (G x1 (ProjIR2 Hx) [-]G y (ProjIR2 Hy))).
    apply mult_resp_leEq_rht; [ apply lft_leEq_Max | apply AbsIR_nonneg ].
   astepl (AbsIR (G x1 (ProjIR2 Hx) [-]G y (ProjIR2 Hy)) [*]Max x0 [1]).
   apply shift_mult_leEq with (max_one_ap_zero x0);
     [ apply pos_max_one | simpl in |- *; apply H3 ]; try assumption.
   apply leEq_transitive with (Min df dg); [ assumption | apply Min_leEq_rht ].
  eapply leEq_wdl.
   2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
  apply leEq_transitive with (AbsIR (F x1 (ProjIR1 Hx) [-]F y (ProjIR1 Hy)) [*]x).
   apply mult_resp_leEq_lft; [ apply H2 | apply AbsIR_nonneg ]; assumption.
  apply leEq_transitive with (AbsIR (F x1 (ProjIR1 Hx) [-]F y (ProjIR1 Hy)) [*]Max x [1]).
   apply mult_resp_leEq_lft; [ apply lft_leEq_Max with (y := OneR) | apply AbsIR_nonneg ].
  apply shift_mult_leEq with (max_one_ap_zero x);
    [ apply pos_max_one | simpl in |- *; apply H5 ]; try assumption.
  apply leEq_transitive with (Min df dg); [ assumption | apply Min_leEq_lft ].
 apply AbsIR_wd; rational.
Qed.

Lemma Continuous_I_max : Continuous_I Hab (FMax F G).
Proof.
 clear incF incG.
 elim contF; intros incF contF'.
 elim contG; intros incG contG'.
 split.
  Included.
 intros e He.
 elim (contF' (e [/]TwoNZ) (pos_div_two _ _ He)); intros dF dFpos HdF.
 elim (contG' (e [/]TwoNZ) (pos_div_two _ _ He)); intros dG dGpos HdG.
 clear contF contG contF' contG'.
 exists (Min dF dG).
  apply less_Min; auto.
 intros x y Hx' Hy' Hx Hy Hxy.
 assert (AbsIR (x[-]y) [<=] dF).
  eapply leEq_transitive; [ apply Hxy | apply Min_leEq_lft ].
 assert (AbsIR (x[-]y) [<=] dG).
  eapply leEq_transitive; [ apply Hxy | apply Min_leEq_rht ].
 assert (HF := HdF x y Hx' Hy' (ProjIR1 Hx) (ProjIR1 Hy) H).
 assert (HG := HdG x y Hx' Hy' (ProjIR2 Hx) (ProjIR2 Hy) H0).
 Opaque AbsIR Max.
 simpl in |- *.
 Transparent AbsIR Max.
 set (Fx := F x (ProjIR1 Hx)) in *.
 set (Fy := F y (ProjIR1 Hy)) in *.
 set (Gx := G x (ProjIR2 Hx)) in *.
 set (Gy := G y (ProjIR2 Hy)) in *.
 elim (AbsIR_imp_AbsSmall _ _ HF); intros HF1 HF2.
 elim (AbsIR_imp_AbsSmall _ _ HG); intros HG1 HG2.
 apply leEq_wdl with (AbsIR (Max Fx Gx[-]Max Fx Gy[+] (Max Fx Gy[-]Max Fy Gy))).
  2: apply AbsIR_wd; rational.
 rstepr (e [/]TwoNZ[+]e [/]TwoNZ).
 eapply leEq_transitive.
  apply triangle_IR.
 apply plus_resp_leEq_both; apply AbsSmall_imp_AbsIR; split.
    apply shift_zero_leEq_minus'.
    rstepr (e [/]TwoNZ[+]Max Fx Gx[-]Max Fx Gy).
    apply shift_zero_leEq_minus.
    apply Max_leEq.
     apply leEq_transitive with (e [/]TwoNZ[+]Fx).
      apply shift_leEq_plus; astepl ZeroR; apply less_leEq; apply pos_div_two; auto.
     apply plus_resp_leEq_lft; apply lft_leEq_Max.
    apply leEq_transitive with (e [/]TwoNZ[+]Gx).
     2: apply plus_resp_leEq_lft; apply rht_leEq_Max.
    apply shift_leEq_plus.
    apply inv_cancel_leEq; rstepr (Gx[-]Gy); auto.
   apply shift_minus_leEq; apply Max_leEq.
    apply leEq_transitive with (e [/]TwoNZ[+]Fx).
     apply shift_leEq_plus; astepl ZeroR; apply less_leEq; apply pos_div_two; auto.
    apply plus_resp_leEq_lft; apply lft_leEq_Max.
   apply leEq_transitive with (e [/]TwoNZ[+]Gy).
    2: apply plus_resp_leEq_lft; apply rht_leEq_Max.
   apply shift_leEq_plus; auto.
  apply shift_zero_leEq_minus'.
  rstepr (e [/]TwoNZ[+]Max Fx Gy[-]Max Fy Gy).
  apply shift_zero_leEq_minus.
  apply Max_leEq.
   apply leEq_transitive with (e [/]TwoNZ[+]Fx).
    apply shift_leEq_plus.
    apply inv_cancel_leEq; rstepr (Fx[-]Fy); auto.
   apply plus_resp_leEq_lft; apply lft_leEq_Max.
  apply leEq_transitive with (e [/]TwoNZ[+]Gy).
   2: apply plus_resp_leEq_lft; apply rht_leEq_Max.
  apply shift_leEq_plus; astepl ZeroR; apply less_leEq; apply pos_div_two; auto.
 apply shift_minus_leEq; apply Max_leEq.
  apply leEq_transitive with (e [/]TwoNZ[+]Fy).
   apply shift_leEq_plus; auto.
  apply plus_resp_leEq_lft; apply lft_leEq_Max.
 apply leEq_transitive with (e [/]TwoNZ[+]Gy).
  apply shift_leEq_plus; astepl ZeroR; apply less_leEq; apply pos_div_two; auto.
 apply plus_resp_leEq_lft; apply rht_leEq_Max.
Qed.

(* begin show *)
Hypothesis Hg' : bnd_away_zero I G.
Hypothesis Hg'' : forall x Hx, I x -> G x Hx [#] [0].
(* end show *)

Lemma Continuous_I_recip : Continuous_I Hab {1/}G.
Proof.
 clear incF incG.
 elim contG; intros incG' contG'.
 split.
  Included; assumption.
 elim Hg'; intros Haux Hg2.
 elim Hg2; clear Haux Hg2; intros c H H0.
 intros.
 elim contG' with (c[*]c[*]e); clear contG contG'.
  intros d H2 H3.
  exists d.
   assumption.
  intros x y H4 H5 Hx Hy H6.
  simpl in |- *.
  set (Hxx := incG' x H4) in *.
  set (Hyy := incG' y H5) in *.
  apply leEq_wdl with (AbsIR (G y Hyy[-]G x Hxx[/] _[//]
    mult_resp_ap_zero _ _ _ (Hg'' x Hxx H4) (Hg'' y Hyy H5))).
   apply leEq_wdl with (AbsIR (G y Hyy[-]G x Hxx) [/] _[//] AbsIR_resp_ap_zero _
     (mult_resp_ap_zero _ _ _ (Hg'' x Hxx H4) (Hg'' y Hyy H5))).
    apply leEq_transitive with (AbsIR (G y Hyy[-]G x Hxx) [/] _[//]
      mult_resp_ap_zero _ _ _ (pos_ap_zero _ _ H) (pos_ap_zero _ _ H)).
     rstepl (AbsIR (G y Hyy[-]G x Hxx) [*] ([1][/] _[//] AbsIR_resp_ap_zero _
       (mult_resp_ap_zero _ _ _ (Hg'' x Hxx H4) (Hg'' y Hyy H5)))).
     rstepr (AbsIR (G y Hyy[-]G x Hxx) [*] ([1][/] _[//]
       mult_resp_ap_zero _ _ _ (pos_ap_zero _ _ H) (pos_ap_zero _ _ H))).
     apply mult_resp_leEq_lft.
      apply recip_resp_leEq.
       astepl (ZeroR[*][0]); apply mult_resp_less_both; try apply leEq_reflexive; assumption.
      eapply leEq_wdr.
       2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
      apply mult_resp_leEq_both; try (apply less_leEq; assumption).
       eapply leEq_wdr; [ apply (H0 x Hxx H4) | algebra ].
      eapply leEq_wdr; [ apply (H0 y Hyy H5) | algebra ].
     apply AbsIR_nonneg.
    apply shift_div_leEq'.
     astepl (ZeroR[*][0]); apply mult_resp_less_both; try apply leEq_reflexive; assumption.
    eapply leEq_wdl.
     2: apply AbsIR_minus.
    apply H3; assumption.
   apply eq_symmetric_unfolded; apply AbsIR_division.
  apply AbsIR_wd.
  rational.
 astepl (ZeroR[*][0]); apply mult_resp_less_both; try apply leEq_reflexive.
  astepl (ZeroR[*][0]); apply mult_resp_less_both; try apply leEq_reflexive; assumption.
 assumption.
Qed.

Lemma Continuous_I_NRoot : forall n Hn, (forall x Hx, I x -> [0][<=]F x Hx) ->
 Continuous_I Hab (FNRoot F n Hn).
Proof.
 intros n Hn H.
 split.
  Included.
 intros e He.
 destruct contF as [contF'' contF'].
 destruct (contF' (e[^]n)) as [d Hd H0]; clear contF contF'.
  apply nexp_resp_pos; assumption.
 exists d.
  assumption.
 intros x y Hx0 Hy0 Hx Hy Hxy.
 set (x':=FNRoot F n Hn x Hx).
 set (y':=FNRoot F n Hn y Hy).
 stepl (Max x' y'[-]Min x' y'); [|apply eq_symmetric;apply Abs_Max].
 apply shift_minus_leEq.
 apply power_cancel_leEq with n; try assumption.
  apply plus_resp_nonneg.
   apply less_leEq; assumption.
  apply leEq_Min; apply: NRoot_nonneg.
 apply leEq_transitive with (e[^]n[+]Min x' y'[^]n).
  apply shift_leEq_plus.
  set (Hx':=(ProjT1 (ext2_a IR (Dom F) (fun (x0 : IR) (Hx1 : Dom F x0) => [0][<=]F x0 Hx1) x Hx))).
  set (Hy':=(ProjT1 (ext2_a IR (Dom F) (fun (x0 : IR) (Hx1 : Dom F x0) => [0][<=]F x0 Hx1) y Hy))).
  stepl (AbsIR (F x Hx'[-]F y Hy')).
   apply H0; try assumption.
  stepr (AbsIR (x'[^]n[-]y'[^]n)).
   apply AbsIR_wd.
   apply: bin_op_wd_unfolded; apply eq_symmetric; try apply un_op_wd_unfolded; apply: NRoot_power.
  csetoid_rewrite (Abs_Max (x'[^]n) (y'[^]n)).
  apply: bin_op_wd_unfolded; try apply un_op_wd_unfolded.
   change (Max ((FId{^}n) x' True_constr) ((FId{^}n) y' True_constr)[=]((FId{^}n) (Max x' y') True_constr)).
   apply Max_monotone.
   simpl; intros r s _ _ X0 X1 X2.
   apply: nexp_resp_leEq; try assumption.
   eapply leEq_transitive;[|apply X0].
   apply leEq_Min; apply: NRoot_nonneg.
  change (Min ((FId{^}n) x' True_constr) ((FId{^}n) y' True_constr)[=]((FId{^}n) (Min x' y') True_constr)).
  apply Min_monotone.
  simpl; intros r s _ _ X0 X1 X2.
  apply: nexp_resp_leEq; try assumption.
  eapply leEq_transitive;[|apply X0].
  apply leEq_Min; apply: NRoot_nonneg.
 apply power_plus_leEq; try assumption.
  apply less_leEq; assumption.
 apply leEq_Min; apply: NRoot_nonneg.
Qed.

End Local_Results.

Hint Resolve contin_imp_inc: included.

Section Corolaries.

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variables F G : PartIR.

(* begin hide *)
Let P := Dom F.
Let Q := Dom G.
(* end hide *)

Hypothesis contF : Continuous_I Hab F.
Hypothesis contG : Continuous_I Hab G.

(**
The corresponding properties for subtraction, division and
multiplication by a scalar are easily proved as corollaries;
exponentiation is proved by induction, appealing to the results on
product and constant functions.
*)

Lemma Continuous_I_minus : Continuous_I Hab (F{-}G).
Proof.
 apply Continuous_I_wd with (F{+}{--}G).
  FEQ.
 apply Continuous_I_plus.
  apply contF.
 apply Continuous_I_inv; apply contG.
Qed.

Lemma Continuous_I_scal : forall c : IR, Continuous_I Hab (c{**}F).
Proof.
 intros.
 unfold Fscalmult in |- *.
 apply Continuous_I_mult.
  apply Continuous_I_const.
 apply contF.
Qed.

Lemma Continuous_I_nth : forall n : nat, Continuous_I Hab (F{^}n).
Proof.
 simple induction n.
  apply Continuous_I_wd with ( [-C-]OneR).
   apply FNth_zero'; apply contin_imp_inc; auto.
  apply Continuous_I_const.
 clear n; intros.
 apply Continuous_I_wd with (F{*}F{^}n).
  apply FNth_mult'; apply contin_imp_inc; auto.
 apply Continuous_I_mult; assumption.
Qed.

Lemma Continuous_I_min : Continuous_I Hab (FMin F G).
Proof.
 unfold FMin in |- *.
 apply Continuous_I_inv; apply Continuous_I_max; apply Continuous_I_inv; auto.
Qed.

Lemma Continuous_I_abs : Continuous_I Hab (FAbs F).
Proof.
 unfold FAbs in |- *.
 apply Continuous_I_max; try apply Continuous_I_inv; auto.
Qed.

Hypothesis Hg' : bnd_away_zero I G.
Hypothesis Hg'' : forall x Hx, I x -> G x Hx [#] [0].

Lemma Continuous_I_div : Continuous_I Hab (F{/}G).
Proof.
 apply Continuous_I_wd with (F{*}{1/}G).
  FEQ.
 apply Continuous_I_mult.
  assumption.
 apply Continuous_I_recip; assumption.
Qed.

End Corolaries.

Section Other.

Section Sums.

(**
We finally prove that the sum of an arbitrary family of continuous functions is still a continuous function.
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
Hypothesis Hab' : a [<] b.

(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Lemma Continuous_I_Sum0 : forall f : nat -> PartIR,
 (forall n, Continuous_I Hab (f n)) -> forall n, Continuous_I Hab (FSum0 n f).
Proof.
 intros.
 induction  n as [| n Hrecn].
  eapply Continuous_I_wd.
   apply FSum0_0.
   2: apply Continuous_I_const.
  intro; apply contin_imp_inc; auto.
 eapply Continuous_I_wd.
  apply FSum0_S.
  intro; apply contin_imp_inc; auto.
 apply Continuous_I_plus; auto.
Qed.

Lemma Continuous_I_Sumx : forall n (f : forall i, i < n -> PartIR),
 (forall i Hi, Continuous_I Hab (f i Hi)) -> Continuous_I Hab (FSumx n f).
Proof.
 intro; induction  n as [| n Hrecn]; intros f contF.
  simpl in |- *; apply Continuous_I_const.
 simpl in |- *; apply Continuous_I_plus.
  apply Hrecn.
  intros; apply contF.
 apply contF.
Qed.

Lemma Continuous_I_Sum : forall f : nat -> PartIR,
 (forall n, Continuous_I Hab (f n)) -> forall m n, Continuous_I Hab (FSum m n f).
Proof.
 intros.
 eapply Continuous_I_wd.
  apply Feq_symmetric; apply FSum_FSum0'.
  intro; apply contin_imp_inc; auto.
 apply Continuous_I_minus; apply Continuous_I_Sum0; auto.
Qed.

End Sums.

(**
For practical purposes, these characterization results are useful:
*)

Lemma lub_charact : forall a b Hab F (contF : Continuous_I Hab F) z,
 fun_lub_IR F (compact a b Hab) z -> z [=] lub_funct a b Hab F contF.
Proof.
 intros a b Hab F contF z H.
 elim H; intros Hz Hz'; clear H.
 assert (H := lub_is_lub _ _ _ _ contF).
 set (y := lub_funct _ _ _ _ contF) in *.
 elim H; intros Hy Hy'; clear H.
 apply leEq_imp_eq; apply shift_zero_leEq_minus'; apply inv_cancel_leEq;
   astepr ZeroR; apply approach_zero; intros e He.
  rstepl (z[-]y).
  apply shift_minus_less.
  elim (Hz' e He); intros x Hx.
  intro H.
  apply less_leEq_trans with (x[+]e).
   apply shift_less_plus'; auto.
  astepr (y[+]e).
  apply plus_resp_leEq; apply Hy.
  auto.
 rstepl (y[-]z).
 apply shift_minus_less.
 elim (Hy' e He); intros x Hx.
 intro H.
 apply less_leEq_trans with (x[+]e).
  apply shift_less_plus'; auto.
 astepr (z[+]e).
 apply plus_resp_leEq; apply Hz.
 auto.
Qed.

Lemma glb_charact : forall a b Hab F (contF : Continuous_I Hab F) z,
 fun_glb_IR F (compact a b Hab) z -> z [=] glb_funct a b Hab F contF.
Proof.
 intros a b Hab F contF z H.
 elim H; intros Hz Hz'; clear H.
 assert (H := glb_is_glb _ _ _ _ contF).
 set (y := glb_funct _ _ _ _ contF) in *.
 elim H; intros Hy Hy'; clear H.
 apply leEq_imp_eq; apply shift_zero_leEq_minus'; apply inv_cancel_leEq;
   astepr ZeroR; apply approach_zero; intros e He.
  rstepl (z[-]y).
  apply shift_minus_less.
  elim (Hy' e He); intros x Hx.
  intro H.
  apply leEq_less_trans with x.
   apply Hz; auto.
  apply shift_less_plus; auto.
 rstepl (y[-]z).
 apply shift_minus_less.
 elim (Hz' e He); intros x Hx.
 intro H.
 apply leEq_less_trans with x.
  apply Hy; auto.
 apply shift_less_plus; auto.
Qed.

(**
The following result is also extremely useful, as it allows us to set a lower bound on the glb of a function.
*)

Lemma leEq_glb : forall a b Hab (F : PartIR) contF x,
 (forall y, Compact Hab y -> forall Hy, x [<=] F y Hy) -> x [<=] glb_funct a b Hab F contF.
Proof.
 intros a b Hab F contF x H.
 elim (glb_is_glb _ _ _ _ contF); intros.
 astepr (glb_funct _ _ _ _ contF[+][0]); apply shift_leEq_plus'.
 apply approach_zero_weak.
 intros e H0.
 elim (b0 _ H0); intro y; intros.
 apply less_leEq; eapply leEq_less_trans.
  2: apply q.
 apply minus_resp_leEq.
 elim p; intros z Hz.
 elim Hz; intros H1 H2.
 elim H2; intros H3 H4.
 astepr (F z H3); auto.
Qed.

(**
The norm is also an extensional property.
*)

Lemma Norm_Funct_wd : forall a b Hab F G, Feq (compact a b Hab) F G ->
 forall contF contG, Norm_Funct (Hab:=Hab) (F:=F) contF [=] Norm_Funct (Hab:=Hab) (F:=G) contG.
Proof.
 intros a b Hab F G H contF contG.
 elim H; intros incF H''.
 elim H''; clear H''; intros incG H''.
 unfold Norm_Funct in |- *; apply bin_op_wd_unfolded.
  generalize (lub_is_lub _ _ _ _ contF); intro Hlub.
  apply lub_charact.
  elim Hlub; clear Hlub; intros H0 H1.
  split.
   intros x H2.
   apply H0.
   apply fun_image_wd with G.
    apply Feq_symmetric; auto.
   auto.
  intros e H2.
  elim (H1 e H2); intro x; intros.
  exists x.
   apply fun_image_wd with F; auto.
  auto.
 apply un_op_wd_unfolded.
 generalize (glb_is_glb _ _ _ _ contF); intro Hglb.
 apply glb_charact.
 elim Hglb; intros H0 H1.
 split.
  intros x H2.
  apply H0.
  apply fun_image_wd with G.
   apply Feq_symmetric; auto.
  auto.
 intros e H2.
 elim (H1 e H2); intro x; intros.
 exists x.
  apply fun_image_wd with F; auto.
 auto.
Qed.

(**
The value of the norm is covariant with the length of the interval.
*)

Lemma included_imp_norm_leEq : forall a b c d Hab Hcd F contF1 contF2,
 included (compact c d Hcd) (compact a b Hab) ->
 Norm_Funct (Hab:=Hcd) (F:=F) contF2 [<=] Norm_Funct (Hab:=Hab) (F:=F) contF1.
Proof.
 intros.
 apply leEq_Norm_Funct; intros.
 apply norm_bnd_AbsIR; auto.
Qed.

End Other.

Hint Resolve Continuous_I_const Continuous_I_id Continuous_I_plus
  Continuous_I_inv Continuous_I_minus Continuous_I_mult Continuous_I_scal
  Continuous_I_recip Continuous_I_max Continuous_I_min Continuous_I_div
  Continuous_I_nth Continuous_I_abs Continuous_I_NRoot: continuous.
