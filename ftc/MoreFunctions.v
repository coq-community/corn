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

(** printing FNorm %\ensuremath{\|\cdot\|_{\infty}}% *)

Require Export MoreIntervals.

Opaque Min Max.

Section Basic_Results.

(**
* More about Functions

Here we state all the main results about properties of functions that
we already proved for compact intervals in the more general setting of
arbitrary intervals.

%\begin{convention}% Let [I:interval] and [F,F',G,G'] be partial functions.
%\end{convention}%

** Continuity
*)

Variable I : interval.

(**
Trivial stuff.
*)

Lemma Continuous_imp_inc : forall F, Continuous I F -> included I (Dom F).
Proof.
 intros F H; elim H; intros; auto.
Qed.

(**
%\begin{convention}% Assume that [I] is compact and [F] is continuous in [I].
%\end{convention}%
*)

Hypothesis cI : compact_ I.
Variable F : PartIR.
Hypothesis contF : Continuous I F.

Lemma continuous_compact : forall H, Continuous_I (a:=Lend cI) (b:=Rend cI) H F.
Proof.
 intros.
 elim contF; intros incF contF'.
 Contin.
Qed.

(* begin show *)
Hypothesis Hinc : included I (Dom F).
(* end show *)

Lemma Continuous_I_imp_tb_image : totally_bounded (fun_image F I).
Proof.
 cut (Continuous_I (Lend_leEq_Rend _ cI) F). intro H.
  elim (Continuous_I_imp_tb_image _ _ _ _ H); intros.
  split; [ clear b | clear a ].
   elim a; intros x Hx.
   elim Hx; intros y Hy.
   elim Hy; clear a Hx Hy; intros Hy Hx.
   elim Hx; clear Hx; intros Hy'' Hx.
   exists x; exists y.
   split.
    exact (compact_interval_inc _ _ _ _ Hy).
   auto.
  intros e He.
  elim (b e He); intros l H0 H1.
  exists l; clear b; [ clear H1 | clear H0 ].
   intros x Hx.
   elim (H0 x Hx); intros y Hy.
   elim Hy; clear H0 Hy Hx; intros Hy Hx.
   elim Hx; clear Hx; intros Hy' Hx.
   exists y.
   split.
    exact (compact_interval_inc _ _ _ _ Hy).
   auto.
  intros x H0.
  apply H1.
  clear H1.
  elim H0; intros y Hy.
  elim Hy; clear H0 Hy; intros Hy Hx.
  elim Hx; clear Hx; intros Hy' Hx.
  exists y.
  split.
   exact (interval_compact_inc _ _ (Lend_leEq_Rend _ cI) _ Hy).
  auto.
 apply continuous_compact.
Qed.

Definition FNorm := Norm_Funct (continuous_compact (Lend_leEq_Rend _ cI)).

Lemma FNorm_bnd_AbsIR : forall x, I x -> forall Hx, AbsIR (F x Hx) [<=] FNorm.
Proof.
 intros; unfold FNorm in |- *.
 apply norm_bnd_AbsIR.
 apply interval_compact_inc; auto.
Qed.

End Basic_Results.

Hint Resolve Continuous_imp_inc: included.

Section Other_Results.

(**
The usual stuff.
*)

Variable I : interval.

Variables F G : PartIR.

Lemma Continuous_wd : Feq I F G -> Continuous I F -> Continuous I G.
Proof.
 intros H H0.
 elim H; intros incF H'.
 elim H'; clear H H'; intros incG eqFG.
 elim H0; clear H0; intros incF' contF.
 split.
  auto.
 intros.
 apply Continuous_I_wd with F.
  FEQ.
  simpl in |- *; algebra.
 auto.
Qed.

(* begin show *)
Hypothesis contF : Continuous I F.
Hypothesis contG : Continuous I G.
(* end show *)

Lemma included_imp_Continuous : forall a b Hab,
 included (compact a b Hab) I -> Continuous_I Hab F.
Proof.
 intros.
 elim contF; auto.
Qed.

Lemma Included_imp_Continuous : forall J : interval, included J I -> Continuous J F.
Proof.
 intros J H.
 split.
  exact (included_trans _ _ _ _ H (Continuous_imp_inc _ _ contF)).
 intros.
 apply included_imp_Continuous; Included.
Qed.

Lemma Continuous_const : forall c : IR, Continuous I [-C-]c.
Proof.
 split; Contin.
Qed.

Lemma Continuous_id : Continuous I FId.
Proof.
 split; Contin.
Qed.

Lemma Continuous_plus : Continuous I (F{+}G).
Proof.
 elim contF; intros incF' contF'.
 elim contG; intros incG' contG'.
 split; Contin.
Qed.

Lemma Continuous_inv : Continuous I {--}F.
Proof.
 elim contF; intros incF' contF'.
 split; Contin.
Qed.

Lemma Continuous_minus : Continuous I (F{-}G).
Proof.
 elim contF; intros incF' contF'.
 elim contG; intros incG' contG'.
 split; Contin.
Qed.

Lemma Continuous_mult : Continuous I (F{*}G).
Proof.
 elim contF; intros incF' contF'.
 elim contG; intros incG' contG'.
 split; Contin.
Qed.

Lemma Continuous_nth : forall n : nat, Continuous I (F{^}n).
Proof.
 elim contF; intros incF' contF'.
 split; Contin.
Qed.

Lemma Continuous_scal : forall c : IR, Continuous I (c{**}F).
Proof.
 elim contF; intros incF' contF'.
 split; Contin.
Qed.

Lemma Continuous_abs : Continuous I (FAbs F).
Proof.
 elim contF; intros incF' contF'.
 split; Contin.
Qed.

Lemma Continuous_recip : bnd_away_zero_in_P G I -> Continuous I {1/}G.
Proof.
 intro H.
 elim contG; intros incG' contG'.
 cut (forall x : IR, I x -> forall Hx, G x Hx [#] [0]). intro H0.
  split; Contin.
 intros x H0 Hx.
 apply bnd_imp_ap_zero with (Compact (leEq_reflexive _ x)); auto.
  apply H; auto.
  exact (compact_single_iprop I x H0).
 exact (compact_single_prop x).
Qed.

Lemma Continuous_NRoot : forall n H, (forall x : IR, I x -> forall Hx, [0][<=]F x Hx)
 -> Continuous I (FNRoot F n H).
Proof.
 intros n H.
 elim contF; intros incF' contF'.
 split; Contin.
Qed.

End Other_Results.

Hint Resolve continuous_compact Continuous_const Continuous_id
  Continuous_plus Continuous_inv Continuous_minus Continuous_mult
  Continuous_scal Continuous_nth Continuous_recip Continuous_abs Continuous_NRoot: continuous.

Hint Immediate included_imp_Continuous Included_imp_Continuous: continuous.

Section Corollaries.

Variable I : interval.

Hypothesis cI : compact_ I.
Variables F G : PartIR.

Hypothesis contF : Continuous I F.
Hypothesis contG : Continuous I G.

Lemma Continuous_div : bnd_away_zero_in_P G I -> Continuous I (F{/}G).
Proof.
 intros.
 apply Continuous_wd with (F{*}{1/}G).
  FEQ.
 Contin.
Qed.

Lemma FNorm_wd : Feq I F G -> FNorm I cI F contF [=] FNorm I cI G contG.
Proof.
 intro H; unfold FNorm in |- *; apply Norm_Funct_wd.
 eapply included_Feq.
  2: apply H.
 Included.
Qed.

End Corollaries.

Hint Resolve Continuous_div: continuous.

Section Sums.

Variable I : interval.

Lemma Continuous_Sumx : forall n (f : forall i, i < n -> PartIR),
 (forall i Hi, Continuous I (f i Hi)) -> Continuous I (FSumx n f).
Proof.
 intro; induction  n as [| n Hrecn]; intros f contF.
  simpl in |- *; Contin.
 simpl in |- *; Contin.
Qed.

(**
%\begin{convention}% Assume [f] is a sequence of continuous functions.
%\end{convention}%
*)

Variable f : nat -> PartIR.
Hypothesis contF : forall n : nat, Continuous I (f n).

Lemma Continuous_Sum0 : forall n : nat, Continuous I (FSum0 n f).
Proof.
 intros.
 induction  n as [| n Hrecn].
  eapply Continuous_wd.
   apply FSum0_0; Included.
  Contin.
 eapply Continuous_wd.
  apply FSum0_S; Included.
 Contin.
Qed.

Lemma Continuous_Sum : forall m n : nat, Continuous I (FSum m n f).
Proof.
 intros.
 eapply Continuous_wd.
  apply Feq_symmetric; apply FSum_FSum0'; Included.
 apply Continuous_minus; apply Continuous_Sum0.
Qed.

End Sums.

Hint Resolve Continuous_Sum0 Continuous_Sumx Continuous_Sum: continuous.

Section Basic_Properties.

(**
** Derivative

Derivative is not that much different.

%\begin{convention}% From this point on we assume [I] to be proper.
%\end{convention}%
*)

Variable I : interval.
Hypothesis pI : proper I.

Variables F G H : PartIR.

Lemma Derivative_wdl : Feq I F G -> Derivative I pI F H -> Derivative I pI G H.
Proof.
 intros H0 H1.
 elim H0; intros incF H0'.
 elim H0'; intros incG Heq.
 elim H1; intros incF' H1'.
 elim H1'; intros incH' derF.
 split.
  auto.
 split.
  auto.
 intros; apply Derivative_I_wdl with F; auto.
 apply included_Feq with I; auto.
Qed.

Lemma Derivative_wdr : Feq I F G -> Derivative I pI H F -> Derivative I pI H G.
Proof.
 intros H0 H1.
 elim H0; intros incF H0'.
 elim H0'; intros incG Heq.
 elim H1; intros incF' H1'.
 elim H1'; intros incH' derF.
 split.
  auto.
 split.
  auto.
 intros; apply Derivative_I_wdr with F; auto.
 apply included_Feq with I; auto.
Qed.

Lemma Derivative_unique : Derivative I pI F G -> Derivative I pI F H -> Feq I G H.
Proof.
 intros H0 H1.
 elim H0; intros incF H0'.
 elim H0'; intros incG derFG.
 elim H1; intros incF' H1'.
 elim H1'; intros incH derFH.
 apply included_Feq''; intros.
  auto.
 unfold Hab'; apply Derivative_I_unique with F; Deriv.
Qed.

Lemma Derivative_imp_inc : Derivative I pI F G -> included I (Dom F).
Proof.
 intro H0.
 inversion_clear H0; auto.
Qed.

Lemma Derivative_imp_inc' : Derivative I pI F G -> included I (Dom G).
Proof.
 intro H0.
 elim H0; intros H1 H2.
 inversion_clear H2; auto.
Qed.

Lemma Derivative_imp_Continuous : Derivative I pI F G -> Continuous I F.
Proof.
 intro H0.
 elim H0; intros incF H'.
 elim H'; intros incG derF.
 clear H0 H'.
 split.
  Included.
 intros a b Hab H0.
 elim (compact_proper_in_interval _ _ _ Hab H0 pI); intros a' Ha.
 elim Ha; clear Ha; intros b' Hb.
 elim Hb; clear Hb; intros Hab' H2 H3.
 apply included_imp_contin with (Hab := less_leEq _ _ _ Hab').
  auto.
 apply deriv_imp_contin_I with Hab' G; auto.
Qed.

Lemma Derivative_imp_Continuous' : Derivative I pI F G -> Continuous I G.
Proof.
 intro H0.
 elim H0; intros incF H'.
 elim H'; intros incG derF.
 clear H0 H'.
 split.
  Included.
 intros a b Hab H0.
 elim (compact_proper_in_interval _ _ _ Hab H0 pI); intros a' Ha.
 elim Ha; clear Ha; intros b' Hb.
 elim Hb; clear Hb; intros Hab' H2 H3.
 apply included_imp_contin with (Hab := less_leEq _ _ _ Hab').
  auto.
 apply deriv_imp_contin'_I with Hab' F; auto.
Qed.

End Basic_Properties.

Hint Immediate Derivative_imp_inc Derivative_imp_inc': included.
Hint Immediate Derivative_imp_Continuous Derivative_imp_Continuous':
  continuous.

Section More_Results.

Variable I : interval.
Hypothesis pI : proper I.

(**
%\begin{convention}% Assume that [F'] and [G'] are derivatives of [F] and [G], respectively, in [I].
%\end{convention}%
*)

Variables F F' G G' : PartIR.

Hypothesis derF : Derivative I pI F F'.
Hypothesis derG : Derivative I pI G G'.

Lemma included_imp_Derivative : forall a b Hab,
 included (Compact (less_leEq _ a b Hab)) I -> Derivative_I Hab F F'.
Proof.
 intros.
 elim derF; intros incF H'.
 elim H'; auto.
Qed.

Lemma Included_imp_Derivative : forall J (pJ : proper J), included J I -> Derivative J pJ F F'.
Proof.
 intros J pJ H.
 split.
  exact (included_trans _ _ _ _ H (Derivative_imp_inc _ _ _ _ derF)).
 split.
  exact (included_trans _ _ _ _ H (Derivative_imp_inc' _ _ _ _ derF)).
 intros.
 apply included_imp_Derivative; Included.
Qed.

Lemma Derivative_const : forall c : IR, Derivative I pI [-C-]c [-C-][0].
Proof.
 intros; split.
  Included.
 split; Deriv.
Qed.

Lemma Derivative_id : Derivative I pI FId [-C-][1].
Proof.
 split.
  Included.
 split; Deriv.
Qed.

Lemma Derivative_plus : Derivative I pI (F{+}G) (F'{+}G').
Proof.
 elim derF; intros incF H.
 elim H; intros incF' derivF.
 elim derG; intros incG H'.
 elim H'; intros incG' derivG.
 split.
  Included.
 split; Deriv.
Qed.

Lemma Derivative_inv : Derivative I pI {--}F {--}F'.
Proof.
 elim derF; intros incF H.
 elim H; intros incF' derivF.
 split.
  Included.
 split; Deriv.
Qed.

Lemma Derivative_minus : Derivative I pI (F{-}G) (F'{-}G').
Proof.
 elim derF; intros incF H.
 elim H; intros incF' derivF.
 elim derG; intros incG H'.
 elim H'; intros incG' derivG.
 split.
  Included.
 split; Deriv.
Qed.

Lemma Derivative_mult : Derivative I pI (F{*}G) (F{*}G'{+}F'{*}G).
Proof.
 elim derF; intros incF H.
 elim H; intros incF' derivF.
 elim derG; intros incG H'.
 elim H'; intros incG' derivG.
 split.
  Included.
 split.
  apply included_FPlus; Included.
 Deriv.
Qed.

Lemma Derivative_scal : forall c : IR, Derivative I pI (c{**}F) (c{**}F').
Proof.
 intro.
 elim derF; intros incF H.
 elim H; intros incF' derivF.
 split.
  Included.
 split; Deriv.
Qed.

Lemma Derivative_poly : forall p, Derivative I pI (FPoly _ p) (FPoly _ (_D_ p)).
Proof.
 intro.
 split.
  Included.
 split; Deriv.
Qed.

Lemma Derivative_nth : forall n, Derivative I pI (F{^}S n) (nring (S n) {**} (F'{*}F{^}n)).
Proof.
 elim derF; intros incF H.
 elim H; intros incF' derivF.
 split.
  Included.
 split; Deriv.
Qed.

Lemma Derivative_recip : bnd_away_zero_in_P G I -> Derivative I pI {1/}G {--} (G'{/}G{*}G).
Proof.
 elim derG; intros incG H'.
 elim H'; intros incG' derivG.
 clear derF derG H'.
 intro.
 cut (forall x : IR, I x -> forall Hx, Part G x Hx [#] [0]); intros.
  cut (forall x : IR, I x -> forall Hx, (G{*}G) x Hx [#] [0]); intros.
   split.
    Included.
   split; Deriv.
  simpl in |- *; apply mult_resp_ap_zero; auto.
 Included.
Qed.

End More_Results.

Section More_Corollaries.

Variable I : interval.
Hypothesis pI : proper I.

Variables F F' G G' : PartIR.

Hypothesis derF : Derivative I pI F F'.
Hypothesis derG : Derivative I pI G G'.

(* begin show *)
Hypothesis Gbnd : bnd_away_zero_in_P G I.
(* end show *)

Lemma Derivative_div : Derivative I pI (F{/}G) ((F'{*}G{-}F{*}G') {/}G{*}G).
Proof.
 elim derF; intros incF Hf.
 elim Hf; intros incF' Hf'.
 elim derG; intros incG derivG.
 elim derivG; intros incG' Hg'.
 clear Hf derivG.
 cut (forall x : IR, I x -> forall Hx, Part G x Hx [#] [0]); intros.
  split.
   Included.
  split.
   apply included_FDiv.
     apply included_FMinus; Included.
    Included.
   intros; simpl in |- *; apply mult_resp_ap_zero; auto.
  Deriv.
 Included.
Qed.

End More_Corollaries.

Section More_Sums.

Variable I : interval.
Hypothesis pI : proper I.

Lemma Derivative_Sumx : forall n (f f' : forall i, i < n -> PartIR),
 (forall i Hi Hi', Derivative I pI (f i Hi) (f' i Hi')) -> Derivative I pI (FSumx n f) (FSumx n f').
Proof.
 intro; induction  n as [| n Hrecn]; intros f f' derF.
  simpl in |- *; apply Derivative_const; auto.
 simpl in |- *; apply Derivative_plus; auto.
Qed.

(* begin show *)
Variables f f' : nat -> PartIR.
Hypothesis derF : forall n : nat, Derivative I pI (f n) (f' n).
(* end show *)

Lemma Derivative_Sum0 : forall n, Derivative I pI (FSum0 n f) (FSum0 n f').
Proof.
 intros.
 induction  n as [| n Hrecn].
  eapply Derivative_wdl.
   apply FSum0_0; Included.
  eapply Derivative_wdr.
   apply FSum0_0; Included.
  apply Derivative_const.
 eapply Derivative_wdl.
  apply FSum0_S; Included.
 eapply Derivative_wdr.
  apply FSum0_S; Included.
 apply Derivative_plus; auto.
Qed.

Lemma Derivative_Sum : forall m n, Derivative I pI (FSum m n f) (FSum m n f').
Proof.
 intros.
 eapply Derivative_wdl.
  apply Feq_symmetric; apply FSum_FSum0'; Included.
 eapply Derivative_wdr.
  apply Feq_symmetric; apply FSum_FSum0'; Included.
 apply Derivative_minus; apply Derivative_Sum0.
Qed.

End More_Sums.

Section Diffble_Basic_Properties.

(**
** Differentiability

Mutatis mutandis for differentiability.
*)

Variable I : interval.
Hypothesis pI : proper I.

Lemma Diffble_imp_inc : forall F, Diffble I pI F -> included I (Dom F).
Proof.
 intros F H.
 inversion_clear H.
 auto.
Qed.

Lemma Derivative_imp_Diffble : forall F F', Derivative I pI F F' -> Diffble I pI F.
Proof.
 intros F F' H.
 elim H; intros incF H'.
 elim H'; intros incF' derivF.
 split; auto.
 intros; apply deriv_imp_Diffble_I with F'; auto.
Qed.

Lemma Diffble_wd : forall F H, Feq I F H -> Diffble I pI F -> Diffble I pI H.
Proof.
 intros F H H0 H1.
 elim H0; intros incF H2.
 elim H2; intros incH eqFH.
 inversion_clear H1.
 split; auto.
 intros; apply Diffble_I_wd with F; auto.
 apply included_Feq with I; auto.
Qed.

Variables F G : PartIR.

Hypothesis diffF : Diffble I pI F.
Hypothesis diffG : Diffble I pI G.

(**
%\begin{convention}% Assume [F] and [G] are differentiable in [I].
%\end{convention}%
*)

Lemma included_imp_Diffble : forall a b Hab,
 included (Compact (less_leEq _ a b Hab)) I -> Diffble_I Hab F.
Proof.
 intros.
 elim diffF; auto.
Qed.

Lemma Included_imp_Diffble : forall J (pJ : proper J), included J I -> Diffble J pJ F.
Proof.
 intros J pJ H.
 split.
  exact (included_trans _ _ _ _ H (Diffble_imp_inc _ diffF)).
 intros; apply included_imp_Diffble; Included.
Qed.

Lemma Diffble_const : forall c : IR, Diffble I pI [-C-]c.
Proof.
 intro.
 split.
  Included.
 intros; apply Diffble_I_const.
Qed.

Lemma Diffble_id : Diffble I pI FId.
Proof.
 split.
  Included.
 intros; apply Diffble_I_id.
Qed.

Lemma Diffble_plus : Diffble I pI (F{+}G).
Proof.
 elim diffF; intros incF diffbleF.
 elim diffG; intros incG diffbleG.
 split.
  Included.
 intros; apply Diffble_I_plus; auto.
Qed.

Lemma Diffble_inv : Diffble I pI {--}F.
Proof.
 elim diffF; intros incF diffbleF.
 split.
  Included.
 intros; apply Diffble_I_inv; auto.
Qed.

Lemma Diffble_minus : Diffble I pI (F{-}G).
Proof.
 elim diffF; intros incF diffbleF.
 elim diffG; intros incG diffbleG.
 split.
  Included.
 intros; apply Diffble_I_minus; auto.
Qed.

Lemma Diffble_mult : Diffble I pI (F{*}G).
Proof.
 elim diffF; intros incF diffbleF.
 elim diffG; intros incG diffbleG.
 split.
  Included.
 intros; apply Diffble_I_mult; auto.
Qed.

Lemma Diffble_nth : forall n : nat, Diffble I pI (F{^}n).
Proof.
 elim diffF; intros incF diffbleF.
 split.
  Included.
 intros; apply Diffble_I_nth; auto.
Qed.

Lemma Diffble_scal : forall c : IR, Diffble I pI (c{**}F).
Proof.
 elim diffF; intros incF diffbleF.
 split.
  Included.
 intros; apply Diffble_I_scal; auto.
Qed.

Lemma Diffble_poly : forall p, Diffble I pI (FPoly _ p).
Proof.
 split.
  Included.
 intros; apply Diffble_I_poly; auto.
Qed.

Lemma Diffble_recip : bnd_away_zero_in_P G I -> Diffble I pI {1/}G.
Proof.
 elim diffG; intros incG diffbleG Gbnd.
 cut (forall x : IR, I x -> forall Hx, Part G x Hx [#] [0]); intros.
  split.
   Included.
  intros; apply Diffble_I_recip; auto.
 Included.
Qed.

End Diffble_Basic_Properties.

Hint Immediate Diffble_imp_inc: included.

Section Diffble_Corollaries.

Variable I : interval.
Hypothesis pI : proper I.

Variables F G : PartIR.

Hypothesis diffF : Diffble I pI F.
Hypothesis diffG : Diffble I pI G.

Lemma Diffble_div : bnd_away_zero_in_P G I -> Diffble I pI (F{/}G).
Proof.
 intro.
 apply Diffble_wd with (F{*}{1/}G).
  apply eq_imp_Feq.
    apply included_FMult.
     apply Diffble_imp_inc with pI; apply diffF.
    apply included_FRecip.
     apply Diffble_imp_inc with pI; apply diffG.
    Included.
   apply included_FDiv.
     apply Diffble_imp_inc with pI; apply diffF.
    apply Diffble_imp_inc with pI; apply diffG.
   Included.
  intros; simpl in |- *; rational.
 apply Diffble_mult; auto.
 apply Diffble_recip; auto.
Qed.

Lemma Diffble_Sum0 : forall f, (forall n, Diffble I pI (f n)) -> forall n, Diffble I pI (FSum0 n f).
Proof.
 intros f hypF n.
 split.
  intros x H n0.
  elim (hypF n0); intros.
  exact (a x H).
 intros; apply Diffble_I_Sum0; auto.
 intro; elim (hypF n0); auto.
Qed.

Lemma Diffble_Sumx : forall n f, ext_fun_seq' f ->
 (forall i Hi, Diffble I pI (f i Hi)) -> Diffble I pI (FSumx n f).
Proof.
 intros n f Hgood hypF.
 split.
  red in |- *; intros.
  apply FSumx_pred'; auto.
  intros.
  elim (hypF i Hi); auto.
 intros; apply Diffble_I_Sumx.
 intros i Hi; elim (hypF i Hi); auto.
Qed.

Lemma Diffble_Sum : forall f, (forall n, Diffble I pI (f n)) -> forall m n, Diffble I pI (FSum m n f).
Proof.
 intros f hypF m n.
 eapply Diffble_wd.
  apply Feq_symmetric; apply FSum_FSum0'.
  intro; apply Diffble_imp_inc with pI; auto.
 apply Diffble_minus; apply Diffble_Sum0; auto.
Qed.

End Diffble_Corollaries.

Section Nth_Derivative.

(**
** Nth Derivative

Higher order derivatives pose more interesting problems.  It turns out that it really becomes necessary to generalize our [n_deriv] operator to any interval.
*)

Variable I : interval.
Hypothesis pI : proper I.

Section Definitions.

(**
%\begin{convention}% Let [n:nat], [F:PartIR] and assume that [F] is n-times differentiable in [I].
%\end{convention}%
*)

Variable n : nat.
Variable F : PartIR.
Hypothesis diffF : Diffble_n n I pI F.

Definition N_Deriv_fun : forall x : IR, I x -> IR.
Proof.
 intros x H.
 set (J := compact_in_interval I pI x H) in *.
 elim diffF; intros incF diffbleF.
 set (a := Lend (compact_compact_in_interval I pI x H)) in *.
 set (b := Rend (compact_compact_in_interval I pI x H)) in *.
 fold J in (value of a), (value of b).
 cut (a [<] b). intro H0.
  cut (Diffble_I_n H0 n F). intro H1.
   apply (Part (n_deriv_I _ _ _ _ _ H1) x).
   apply n_deriv_inc.
   unfold a, b, J in |- *; apply iprop_compact_in_interval_inc2.
   apply iprop_compact_in_interval.
  apply diffbleF.
  apply (included_trans _ (Compact (less_leEq IR a b H0)) J); unfold a, b, J in |- *; Included.
 unfold a, b, J in |- *; apply proper_compact_in_interval'.
Defined.

Lemma N_Deriv_char
 (* begin hide *)
 :
 forall x Hx H,
 N_Deriv_fun x Hx [=]
 Part
   (n_deriv_I _ _
      (proper_compact_in_interval' _ _ _ _
         (compact_compact_in_interval I pI x Hx)) n F H) x
   (n_deriv_inc _ _ _ _ _ _ _
      (iprop_compact_in_interval_inc2 _ _ _ _
         (compact_compact_in_interval _ _ _ _)
         (less_leEq _ _ _
            (proper_compact_in_interval' _ _ _ _
               (compact_compact_in_interval _ _ _ _))) _
         (iprop_compact_in_interval _ _ _ _))).
Proof.
 intros.
 unfold N_Deriv_fun in |- *.
 elim diffF; intros; simpl in |- *.
 apply n_deriv_I_wd'.
    algebra.
   apply iprop_compact_in_interval'.
  apply iprop_compact_in_interval'.
 apply b.
 apply included_trans with (Compact (less_leEq _ _ _ (proper_compact_in_interval' _ _ _ _
   (compact_compact_in_interval I pI x Hx)))).
  2: Included.
 intros x0 H0.
 inversion_clear H0.
 split.
  eapply leEq_wdl.
   apply H1.
  eapply eq_transitive_unfolded.
   apply Min_comm.
  apply leEq_imp_Min_is_lft; apply eq_imp_leEq.
  apply compact_in_interval_wd1; algebra.
 eapply leEq_wdr.
  apply H2.
 apply leEq_imp_Max_is_rht; apply eq_imp_leEq.
 apply compact_in_interval_wd2; algebra.
Qed.
(* end hide *)

Lemma N_Deriv_strext : forall x y Hx Hy, N_Deriv_fun x Hx [#] N_Deriv_fun y Hy -> x [#] y.
Proof.
 intros x y Hx Hy H.
 elim diffF; intros incF diffbleF.
 cut (Diffble_I_n (proper_compact_in_interval2' _ _ _ _ _ _
   (compact_compact_in_interval2 I pI x y Hx Hy)) n F). intro H0.
  cut (Diffble_I_n (proper_compact_in_interval' _ _ _ _
    (compact_compact_in_interval I pI x Hx)) n F). intro H1.
   cut (Diffble_I_n (proper_compact_in_interval' _ _ _ _
     (compact_compact_in_interval I pI y Hy)) n F). intro H2.
    cut (Dom (n_deriv_I _ _ _ _ _ H0) x). intro H3.
     cut (Dom (n_deriv_I _ _ _ _ _ H0) y). intro H4.
      apply pfstrx with (Hx := H3) (Hy := H4).
      eapply ap_wdl_unfolded.
       eapply ap_wdr_unfolded.
        apply H.
       eapply eq_transitive_unfolded.
        apply (N_Deriv_char y Hy H2).
       apply n_deriv_I_wd'.
          algebra.
         apply iprop_compact_in_interval_inc2; apply iprop_compact_in_interval.
        apply iprop_compact_in_interval2_inc2; apply iprop_compact_in_interval2y.
       apply included_imp_diffble_n with (Hab' := proper_compact_in_interval2' _ _ _ _ _ _
         (compact_compact_in_interval2 I pI x y Hx Hy)).
        2: apply H0.
       red in |- *; intros z Hz.
       inversion_clear Hz; split.
        eapply leEq_wdl.
         apply H5.
        eapply eq_transitive_unfolded.
         apply Min_comm.
        apply leEq_imp_Min_is_lft.
        apply compact_in_interval_y_lft.
       eapply leEq_wdr.
        apply H6.
       apply leEq_imp_Max_is_rht.
       apply compact_in_interval_y_rht.
      eapply eq_transitive_unfolded.
       apply (N_Deriv_char x Hx H1).
      apply n_deriv_I_wd'.
         algebra.
        apply iprop_compact_in_interval_inc2; apply iprop_compact_in_interval.
       apply iprop_compact_in_interval2_inc2; apply iprop_compact_in_interval2x.
      apply included_imp_diffble_n with (Hab' := proper_compact_in_interval2' _ _ _ _ _ _
        (compact_compact_in_interval2 I pI x y Hx Hy)).
       2: apply H0.
      red in |- *; intros z Hz.
      inversion_clear Hz; split.
       eapply leEq_wdl.
        apply H5.
       eapply eq_transitive_unfolded.
        apply Min_comm.
       apply leEq_imp_Min_is_lft.
       apply compact_in_interval_x_lft.
      eapply leEq_wdr.
       apply H6.
      apply leEq_imp_Max_is_rht.
      apply compact_in_interval_x_rht.
     apply n_deriv_inc.
     apply iprop_compact_in_interval2_inc2; apply iprop_compact_in_interval2y.
    apply n_deriv_inc.
    apply iprop_compact_in_interval2_inc2; apply iprop_compact_in_interval2x.
   apply diffbleF.
   simpl in |- *; Included.
  apply diffbleF.
  simpl in |- *; Included.
 apply diffbleF.
 simpl in |- *; Included.
Qed.

Lemma N_Deriv_wd : forall x y Hx Hy, x [=] y -> N_Deriv_fun x Hx [=] N_Deriv_fun y Hy.
Proof.
 intros.
 apply not_ap_imp_eq. intro H0.
 cut (x [#] y).
  apply eq_imp_not_ap; auto.
 exact (N_Deriv_strext _ _ _ _ H0).
Qed.

Definition N_Deriv : PartIR.
Proof.
 apply Build_PartFunct with (pfpfun := N_Deriv_fun).
  apply iprop_wd.
 exact N_Deriv_strext.
Defined.

End Definitions.

Section Basic_Results.

(**
All the usual results hold.
*)

Lemma Diffble_n_wd : forall n F G, Feq I F G -> Diffble_n n I pI F -> Diffble_n n I pI G.
Proof.
 intros n F G H H0.
 elim H; intros incF H1.
 elim H1; intro incG.
 split.
  auto.
 intros; apply Diffble_I_n_wd with F.
  apply included_Feq with I; auto.
 elim H0; auto.
Qed.

Lemma Derivative_n_wdr : forall n F G H,
 Feq I G H -> Derivative_n n I pI F G -> Derivative_n n I pI F H.
Proof.
 intros n F G H H0 H1.
 elim H0; intros incG H2.
 elim H2; intros incH Heq.
 elim H1; intros incF H0'.
 elim H0'; intros incG' derivF.
 clear H2 H0'.
 split; auto.
 split; auto.
 intros; apply Derivative_I_n_wdr with G.
  apply included_Feq with I; auto.
 auto.
Qed.

Lemma Derivative_n_wdl : forall n F G H,
 Feq I F G -> Derivative_n n I pI F H -> Derivative_n n I pI G H.
Proof.
 intros n F G H H0 H1.
 elim H0; intros incG H2.
 elim H2; intros incH Heq.
 elim H1; intros incF H0'.
 elim H0'; intros incG' derivF.
 clear H2 H0'.
 split; auto.
 split; auto.
 intros; apply Derivative_I_n_wdl with F.
  apply included_Feq with I; auto.
 auto.
Qed.

Lemma Derivative_n_unique : forall n F G H,
 Derivative_n n I pI F G -> Derivative_n n I pI F H -> Feq I G H.
Proof.
 intros n F G H H0 H1.
 elim H0; intros incF H2.
 elim H2; intros incG derivFG.
 elim H1; intros incF' H3.
 elim H3; intros incH derivFH.
 FEQ. rename X into H4.
 apply Feq_imp_eq with (Compact (less_leEq _ _ _ (proper_compact_in_interval' _ _ _ _
   (compact_compact_in_interval I pI x H4)))).
  apply Derivative_I_n_unique with n F.
   apply derivFG.
   simpl in |- *; Included.
  apply derivFH.
  simpl in |- *; Included.
 apply interval_compact_inc.
 apply iprop_compact_in_interval.
Qed.

Lemma Diffble_n_imp_Diffble : forall n : nat, 0 < n -> forall F,
 Diffble_n n I pI F -> Diffble I pI F.
Proof.
 intros n H F H0.
 elim H0; intros incF diffF.
 split; auto.
 intros; apply Diffble_I_n_imp_diffble with n; auto.
Qed.

Lemma Derivative_n_imp_Diffble : forall n, 0 < n -> forall F F',
 Derivative_n n I pI F F' -> Diffble I pI F.
Proof.
 intros n H F F' H0.
 elim H0; intros incF H1.
 elim H1; intros incF' derivF.
 split; auto.
 intros; apply deriv_n_imp_diffble with n F'; auto.
Qed.

Lemma le_imp_Diffble_n : forall m n, m <= n -> forall F,
 Diffble_n n I pI F -> Diffble_n m I pI F.
Proof.
 intros m n H F H0.
 elim H0; intros incF diffF.
 split; auto.
 intros; apply le_imp_Diffble_I with n; auto.
Qed.

Lemma Diffble_n_imp_le : forall n, 0 < n -> forall F F',
 Diffble_n n I pI F -> Derivative I pI F F' -> Diffble_n (pred n) I pI F'.
Proof.
 intros n H F F' H0 H1.
 elim H0; intros incF diffF.
 elim H1; intros incFa H2.
 elim H2; intros incF' derivF.
 split; auto.
 intros; apply Diffble_I_imp_le with F; auto.
Qed.

Lemma Diffble_n_imp_inc : forall n F, Diffble_n n I pI F -> included I (Dom F).
Proof.
 intros n F H.
 inversion_clear H; auto.
Qed.

Lemma Derivative_n_imp_Diffble_n : forall n F F',
 Derivative_n n I pI F F' -> Diffble_n n I pI F.
Proof.
 intros n F F' H.
 elim H; intros incF H1.
 elim H1; intros incF' derivF.
 split; auto.
 intros; apply deriv_n_imp_Diffble_I_n with F'; auto.
Qed.

Lemma Derivative_n_imp_inc : forall n F F', Derivative_n n I pI F F' -> included I (Dom F).
Proof.
 intros n F F' H.
 inversion_clear H; auto.
Qed.

Lemma Derivative_n_imp_inc' : forall n F F', Derivative_n n I pI F F' -> included I (Dom F').
Proof.
 intros.
 inversion_clear X; inversion_clear X1; auto.
Qed.

Lemma included_imp_Derivative_n : forall n F F' a b Hab, Derivative_n n I pI F F' ->
 included (Compact (less_leEq _ a b Hab)) I -> Derivative_I_n Hab n F F'.
Proof.
 intros n F F' a b Hab H H0.
 elim H; intros incF H1.
 elim H1; auto.
Qed.

Lemma included_imp_Diffble_n : forall n F a b Hab, Diffble_n n I pI F ->
 included (Compact (less_leEq _ a b Hab)) I -> Diffble_I_n Hab n F.
Proof.
 intros.
 elim X; auto.
Qed.

Lemma Included_imp_Derivative_n : forall n (J : interval) pJ F F',
 included J I -> Derivative_n n I pI F F' -> Derivative_n n J pJ F F'.
Proof.
 intros n J pJ F F' H H0.
 elim H0; clear H0; intros H1 H2.
 elim H2; clear H2; intros H0 H3.
 split.
  Included.
 split.
  Included.
 intros; apply H3.
 Included.
Qed.

Lemma Included_imp_Diffble_n : forall n (J : interval) pJ F,
 included J I -> Diffble_n n I pI F -> Diffble_n n J pJ F.
Proof.
 intros n J pJ F H H0.
 elim H0; clear H0; intros H1 H2.
 split.
  Included.
 intros; apply H2.
 Included.
Qed.

Lemma Derivative_n_plus : forall J pJ n m k F G H, Derivative_n m J pJ F G ->
 Derivative_n n J pJ G H -> k = m + n -> Derivative_n k J pJ F H.
Proof.
 intros J pJ n m k F G H H0 H1 H2.
 elim H0; intros incF Hf.
 elim Hf; intros incG derFG.
 elim H1; intros incG' Hg.
 elim Hg; intros incH derGH.
 clear Hf Hg.
 split; auto.
 split; auto.
 intros; apply Derivative_I_n_plus with n m G; auto.
Qed.

End Basic_Results.

Section More_Results.

(**
Some new results hold, too:
*)

Lemma N_Deriv_Feq : forall n F diffF a b Hab H
 (incN : included (Compact (less_leEq _ _ _ Hab)) (Dom (N_Deriv n F diffF))),
 Feq (Compact (less_leEq _ _ _ Hab)) (N_Deriv n F diffF) (n_deriv_I a b Hab n F H).
Proof.
 intros.
 FEQ.
  apply n_deriv_inc.
 simpl in |- *.
 cut (Diffble_I_n (proper_compact_in_interval' _ _ _ _
   (compact_compact_in_interval I pI x Hx)) n F). intro H1.
  eapply eq_transitive_unfolded.
   apply (N_Deriv_char n F diffF x Hx H1).
  apply n_deriv_I_wd'; auto.
    algebra.
   apply iprop_compact_in_interval_inc2; apply iprop_compact_in_interval.
  apply included_imp_Diffble_n; auto.
  apply included_interval'.
     apply (included_compact_in_interval I pI x Hx).
     apply (iprop_compact_in_interval_inc1 _ _ _ _ (compact_compact_in_interval I pI x Hx)
       (Lend_leEq_Rend _ (compact_compact_in_interval I pI x Hx))).
     apply compact_inc_lft.
    apply (included_compact_in_interval I pI x Hx).
    apply (iprop_compact_in_interval_inc1 _ _ _ _ (compact_compact_in_interval I pI x Hx)
      (Lend_leEq_Rend _ (compact_compact_in_interval I pI x Hx))).
    apply compact_inc_rht.
   apply incN; apply compact_inc_lft.
  apply incN; apply compact_inc_rht.
 elim diffF; intros incF diffbleF.
 apply diffbleF; auto.
 eapply included_trans.
  apply iprop_compact_in_interval_inc1.
 Included.
Qed.

Lemma N_Deriv_lemma : forall n F H, Derivative_n n I pI F (N_Deriv n F H).
Proof.
 intros.
 elim H; intros incF diffF.
 split; auto.
 split; Included.
 intros a b Hab H0.
 cut (Diffble_I_n Hab n F). intro H1. 2: auto.
  eapply Derivative_I_n_wdr.
  apply Feq_symmetric; apply (N_Deriv_Feq n F (incF, diffF) _ _ Hab H1 H0).
 apply n_deriv_lemma.
Qed.

Lemma N_Deriv_S : forall n F H HS,
 Derivative I pI (N_Deriv n F H) (N_Deriv (S n) F HS).
Proof.
 intros n F H H'.
 split; Included.
 split; Included.
 elim H; intros incF diffFn.
 elim H'; intros incF' diffFSn.
 intros a b Hab H0.
 cut (Diffble_I_n Hab n F). intro H1. 2: auto.
  cut (Diffble_I_n Hab (S n) F). intro H2. 2: auto.
  eapply Derivative_I_wdl.
  apply Feq_symmetric; apply (N_Deriv_Feq n F (incF, diffFn) _ _ Hab H1 H0).
 eapply Derivative_I_wdr.
  apply Feq_symmetric; apply (N_Deriv_Feq _ _ (incF', diffFSn) _ _ Hab H2 H0).
 apply n_Sn_deriv.
Qed.

Lemma N_Deriv_plus : forall m n F H H',
 Derivative_n m I pI (N_Deriv n F H) (N_Deriv (m + n) F H').
Proof.
 intros.
 split; Included.
 split; Included.
 intros a b Hab H0.
 cut (Diffble_I_n Hab n F). intro H1.
  cut (Diffble_I_n Hab (m + n) F). intro H2.
   eapply Derivative_I_n_wdl.
    apply Feq_symmetric; apply (N_Deriv_Feq n F H _ _ Hab H1 H0).
   eapply Derivative_I_n_wdr.
    apply Feq_symmetric; apply (N_Deriv_Feq _ _ H' _ _ Hab H2 H0).
   apply n_deriv_plus.
  elim H'; auto.
 elim H; auto.
Qed.

(**
Some useful characterization results.
*)

Lemma Derivative_n_O : forall F, included I (Dom F) -> Derivative_n 0 I pI F F.
Proof.
 intros.
 split; Included.
 split; Included.
 intros.
 red in |- *; apply Feq_reflexive; Included.
Qed.

Lemma Derivative_n_Sn : forall F n fn fSn, Derivative_n n I pI F fn ->
 Derivative_n (S n) I pI F fSn -> Derivative I pI fn fSn.
Proof.
 intros F n fn fSn H H0.
 cut (Diffble_n n I pI F); [ intro H1 | eapply Derivative_n_imp_Diffble_n; apply H ].
 cut (Diffble_n (S n) I pI F); [ intro H2 | eapply Derivative_n_imp_Diffble_n; apply H0 ].
 apply Derivative_wdl with (N_Deriv _ _ H1).
  apply Derivative_n_unique with n F.
   apply N_Deriv_lemma.
  auto.
 apply Derivative_wdr with (N_Deriv _ _ H2).
  apply Derivative_n_unique with (S n) F.
   apply N_Deriv_lemma.
  auto.
 apply N_Deriv_S.
Qed.

End More_Results.

Section Derivating_Diffble.

(**
As a special case we get a differentiation operator%\ldots%#...#
*)

Variable F : PartIR.

(* begin show *)
Hypothesis diffF : Diffble I pI F.
(* end show *)

Lemma Diffble_imp_Diffble_n : Diffble_n 1 I pI F.
Proof.
 elim diffF; intros incF diffbleF.
 split; auto.
 intros a b Hab H; exists (diffbleF a b Hab H).
 simpl in |- *; Included.
Qed.

Definition Deriv := N_Deriv 1 F Diffble_imp_Diffble_n.

End Derivating_Diffble.

Section Corollaries.

(**
%\ldots%#...# for which the expected property also holds.
*)

Lemma Deriv_lemma : forall F diffF, Derivative I pI F (Deriv F diffF).
Proof.
 intros; unfold Deriv in |- *.
 apply Derivative_wdl with (N_Deriv 0 F
   (le_imp_Diffble_n 0 1 (le_n_Sn 0) F (Diffble_imp_Diffble_n _ diffF))).
  apply Derivative_n_unique with 0 F.
   apply N_Deriv_lemma.
  apply Derivative_n_O; elim diffF; auto.
 apply N_Deriv_S.
Qed.

(**
Some more interesting properties.
*)

Lemma Derivative_n_1 : forall F G, Derivative I pI F G -> Derivative_n 1 I pI F G.
Proof.
 intros F G H.
 cut (Diffble I pI F). intro H0.
  apply Derivative_n_wdr with (Deriv _ H0).
   apply Derivative_unique with pI F.
    apply Deriv_lemma.
   auto.
  unfold Deriv in |- *; apply N_Deriv_lemma.
 apply Derivative_imp_Diffble with G; auto.
Qed.

Lemma Derivative_n_chain : forall F f, Feq I F (f 0) ->
 (forall n, Derivative I pI (f n) (f (S n))) -> forall n, Derivative_n n I pI F (f n).
Proof.
 intros F f H H0 n.
 induction  n as [| n Hrecn].
  apply Derivative_n_wdr with F.
   auto.
  apply Derivative_n_O.
  elim H; auto.
 apply Derivative_n_plus with 1 n (f n); auto.
  apply Derivative_n_1; auto.
 rewrite plus_comm; auto.
Qed.

Lemma Derivative_n_imp_Continuous : forall n F G, 0 < n ->
 Derivative_n n I pI F G -> Continuous I F.
Proof.
 intros n F G H H0.
 cut (Diffble I pI F). intro H1.
  apply Derivative_imp_Continuous with pI (Deriv _ H1).
  apply Deriv_lemma.
 apply Diffble_n_imp_Diffble with n; auto.
 apply Derivative_n_imp_Diffble_n with G; auto.
Qed.

Lemma Derivative_n_imp_Continuous' : forall n F G, 0 < n ->
 Derivative_n n I pI F G -> Continuous I G.
Proof.
 intros n F G H H0.
 cut (Diffble_n (pred n) I pI F). intro H1.
  apply Derivative_imp_Continuous' with pI (N_Deriv _ _ H1).
  apply Derivative_wdr with (N_Deriv _ _ (Derivative_n_imp_Diffble_n _ _ _ H0)).
   apply Derivative_n_unique with n F; auto; apply N_Deriv_lemma.
  cut (n = S (pred n)); [ intro | apply S_pred with 0; auto ].
  generalize H0 H1. rewrite H2. intros.
  apply N_Deriv_S.
 apply le_imp_Diffble_n with n.
  auto with arith.
 apply Derivative_n_imp_Diffble_n with G; auto.
Qed.

End Corollaries.

End Nth_Derivative.

Hint Resolve Derivative_const Derivative_id Derivative_plus Derivative_inv
  Derivative_minus Derivative_mult Derivative_scal Derivative_nth
  Derivative_recip Derivative_div Derivative_Sumx Derivative_Sum0
  Derivative_Sum: derivate.

Hint Immediate Derivative_n_imp_inc Derivative_n_imp_inc' Diffble_n_imp_inc:
  included.

Hint Resolve Deriv_lemma N_Deriv_lemma: derivate.

Hint Immediate Derivative_n_imp_Continuous Derivative_n_imp_Continuous':
  continuous.
