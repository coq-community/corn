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

Require Export FunctSeries.
Require Export MoreFunctions.

(** printing FSeries_Sum %\ensuremath{\sum_{\infty}}% #&sum;'<sub>&infin;</sub># *)

Section Definitions.

(**
* More on Sequences and Series

We will now extend our convergence definitions and results for
sequences and series of functions defined in compact intervals to
arbitrary intervals.

%\begin{convention}% Throughout this file, [J] will be an interval,
[f, g] will be sequences of continuous (in [J]) functions and [F,G]
will be continuous (in [J]) functions.
%\end{convention}%

** Sequences

First we will consider the case of sequences.

*** Definitions

Some of the definitions do not make sense in this more general setting
(for instance, because the norm of a function is no longer defined),
but the ones which do we simply adapt in the usual way.
*)

Variable J : interval.
Variable f : nat -> PartIR.
Variable F : PartIR.

Hypothesis contf : forall n : nat, Continuous J (f n).
Hypothesis contF : Continuous J F.

Definition Cauchy_fun_seq_IR :=  forall a b Hab (Hinc : included (compact a b Hab) J),
  Cauchy_fun_seq _ _ _ f (fun n => included_imp_Continuous _ _ (contf n) _ _ _ Hinc).

Definition conv_fun_seq_IR := forall a b Hab (Hinc : included (Compact Hab) J),
  conv_fun_seq a b Hab f (fun n => included_imp_Continuous _ _ (contf n) _ _ _ Hinc).

Definition conv_fun_seq'_IR := forall a b Hab (Hinc : included (Compact Hab) J),
  conv_fun_seq' a b Hab f F
    (fun n => included_imp_Continuous _ _ (contf n) _ _ _ Hinc)
    (included_imp_Continuous _ _ contF _ _ _ Hinc).

Definition Cauchy_fun_seq2_IR := forall a b Hab (Hinc : included (compact a b Hab) J),
  Cauchy_fun_seq2 _ _ _ f (fun n => included_imp_Continuous _ _ (contf n) _ _ _ Hinc).

(**
The equivalences between these definitions still hold.
*)

Lemma conv_Cauchy_fun_seq'_IR : conv_fun_seq'_IR -> Cauchy_fun_seq_IR.
Proof.
 intro H.
 red in |- *; red in H.
 intros.
 apply conv_Cauchy_fun_seq' with F (included_imp_Continuous _ _ contF _ _ _ Hinc); auto.
Qed.

Lemma Cauchy_fun_seq_seq2_IR : Cauchy_fun_seq_IR -> Cauchy_fun_seq2_IR.
Proof.
 intro H.
 red in |- *; red in H.
 intros.
 apply Cauchy_fun_seq_seq2; auto.
Qed.

Lemma Cauchy_fun_seq2_seq_IR : Cauchy_fun_seq2_IR -> Cauchy_fun_seq_IR.
Proof.
 intro H.
 red in |- *; red in H.
 intros.
 apply Cauchy_fun_seq2_seq; auto.
Qed.

Lemma Cauchy_fun_real_IR : Cauchy_fun_seq_IR -> forall x Hx,
 Cauchy_prop (fun n => Part _ _ (Continuous_imp_inc _ _ (contf n) x Hx)).
Proof.
 intros H x Hx.
 red in H.
 cut (included (compact_single x) J). intro H0.
  set (contf' := fun i : nat => included_imp_Continuous J (f i) (contf i) _ _ (leEq_reflexive _ x) H0)
    in *.
  apply Cauchy_prop_wd with (fun n : nat => Part (f n) x ((fun i : nat =>
    contin_imp_inc _ _ (leEq_reflexive _ x) (f i) (contf' i)) n x (compact_single_prop x))).
   apply Cauchy_fun_real.
   unfold contf' in |- *; simpl in |- *; apply H.
  intro; simpl in |- *; algebra.
 apply compact_single_iprop; auto.
Qed.

End Definitions.

Section More_Definitions.

(**
Limit is defined and works in the same way as before.
*)

Variable J : interval.
Variable f : nat -> PartIR.

Hypothesis contf : forall n : nat, Continuous J (f n).
(* begin show *)
Hypothesis conv : Cauchy_fun_seq_IR J f contf.
(* end show *)

Definition Cauchy_fun_seq_Lim_IR : PartIR.
Proof.
 apply Build_PartFunct with (pfpfun := fun (x : IR) (Hx : J x) =>
   Lim (Build_CauchySeq _ _ (Cauchy_fun_real_IR _ _ _ conv x Hx))).
  apply iprop_wd.
 intros x y Hx Hy H.
 elim (Lim_strext _ _ H).
 intros n Hn.
 simpl in Hn.
 exact (pfstrx _ _ _ _ _ _ Hn).
Defined.

Lemma Cauchy_fun_seq_Lim_char : forall a b Hab (Hinc : included (Compact Hab) J),
 Feq (Compact Hab) Cauchy_fun_seq_Lim_IR
  (Cauchy_fun_seq_Lim _ _ _ _ _ (conv a b Hab Hinc)).
Proof.
 intros.
 FEQ.
 simpl in |- *.
 apply Lim_wd'; intros; simpl in |- *; algebra.
Qed.

End More_Definitions.

Section Irrelevance_of_Proofs.

(**
*** Basic Properties

Proofs are irrelevant as before---they just have to be present.
*)

Variable J : interval.
Variable f : nat -> PartIR.
(* begin show *)
Hypotheses contf contf0 : forall n : nat, Continuous J (f n).
(* end show *)

Variable F : PartIR.
(* begin show *)
Hypotheses contF contF0 : Continuous J F.
(* end show *)

Lemma conv_fun_seq'_wd_IR : conv_fun_seq'_IR _ _ _ contf contF ->
 conv_fun_seq'_IR _ _ _ contf0 contF0.
 intro H.
 red in |- *; intros.
 eapply conv_fun_seq'_wd.
 apply (H a b Hab Hinc).
Qed.

Lemma Cauchy_fun_seq2_wd_IR : Cauchy_fun_seq2_IR _ _ contf ->
 Cauchy_fun_seq2_IR _ _ contf0.
Proof.
 intro H.
 red in |- *; intros.
 eapply Cauchy_fun_seq2_wd.
 apply (H a b Hab Hinc).
Qed.

Lemma conv_fun_seq_wd_IR : conv_fun_seq_IR _ _ contf ->
 conv_fun_seq_IR _ _ contf0.
Proof.
 intro H.
 red in |- *; intros.
 eapply conv_fun_seq_wd.
 apply (H a b Hab Hinc).
Qed.

End Irrelevance_of_Proofs.

Opaque Cauchy_fun_seq_Lim_IR.

Section More_Properties.

Variable J : interval.
Variables f g : nat -> PartIR.

(* begin show *)
Hypotheses contf contf0 : forall n : nat, Continuous J (f n).
Hypotheses contg contg0 : forall n : nat, Continuous J (g n).
(* end show *)

Lemma Cauchy_conv_fun_seq'_IR : forall H contf',
 conv_fun_seq'_IR _ _ (Cauchy_fun_seq_Lim_IR _ _ contf H) contf contf'.
Proof.
 intros.
 red in |- *; intros.
 eapply conv_fun_seq'_wdr.
  apply Feq_symmetric.
  apply (Cauchy_fun_seq_Lim_char J f contf H a b Hab Hinc).
 apply Cauchy_conv_fun_seq' with (H := H a b Hab Hinc)
   (contf' := Cauchy_cont_Lim _ _ _ _ _ (H a b Hab Hinc)).
Qed.

Variables F G : PartIR.
(* begin show *)
Hypotheses contF contF0 : Continuous J F.
Hypotheses contG contG0 : Continuous J G.
(* end show *)

Lemma conv_fun_seq'_wdl_IR : (forall n, Feq J (f n) (g n)) ->
 conv_fun_seq'_IR _ _ _ contf contF -> conv_fun_seq'_IR _ _ _ contg contF0.
Proof.
 intros H H0 a b Hab Hinc.
 eapply conv_fun_seq'_wdl with (f := f).
  2: apply (H0 a b Hab Hinc).
 intro; elim (H n); intros.
 inversion_clear b0.
 apply eq_imp_Feq; Included.
Qed.

Lemma conv_fun_seq'_wdr_IR : Feq J F G ->
 conv_fun_seq'_IR _ _ _ contf contF -> conv_fun_seq'_IR _ _ _ contf0 contG.
Proof.
 intros H H0 a b Hab Hinc.
 eapply conv_fun_seq'_wdr with (F := F).
  2: apply (H0 a b Hab Hinc).
 apply included_Feq with J; auto.
Qed.

Lemma conv_fun_seq'_wdl'_IR : (forall n, Feq J (f n) (g n)) ->
 conv_fun_seq'_IR _ _ _ contf contF -> conv_fun_seq'_IR _ _ _ contg contF.
Proof.
 intros H H0 a b Hab Hinc.
 eapply conv_fun_seq'_wdl' with (f := f); auto.
 intro; elim (H n); intros.
 inversion_clear b0.
 apply eq_imp_Feq; Included.
Qed.

Lemma conv_fun_seq'_wdr'_IR : Feq J F G ->
 conv_fun_seq'_IR _ _ _ contf contF -> conv_fun_seq'_IR _ _ _ contf contG.
Proof.
 intros H H0 a b Hab Hinc.
 eapply conv_fun_seq'_wdr' with (F := F).
  2: apply (H0 a b Hab Hinc).
 apply included_Feq with J; auto.
Qed.

Lemma Cauchy_cont_Lim_IR : forall H, Continuous J (Cauchy_fun_seq_Lim_IR _ _ contf H).
Proof.
 intros.
 split; Included.
 intros a b Hab H0; eapply Continuous_I_wd.
  apply Feq_symmetric.
  apply (Cauchy_fun_seq_Lim_char J f contf H a b Hab H0).
 Contin.
Qed.

Lemma Cauchy_conv_fun_seq_IR : Cauchy_fun_seq_IR _ _ contf ->
 conv_fun_seq_IR _ _ contf.
Proof.
 intros H a b Hab Hinc.
 eapply Cauchy_conv_fun_seq.
 apply (H a b Hab Hinc).
Qed.

Lemma conv_Cauchy_fun_seq_IR : conv_fun_seq_IR _ _ contf ->
 Cauchy_fun_seq_IR _ _ contf.
Proof.
 intros H a b Hab Hinc.
 eapply conv_Cauchy_fun_seq.
 apply (H a b Hab Hinc).
Qed.

End More_Properties.

Hint Resolve Cauchy_cont_Lim_IR: continuous.

Section Algebraic_Properties.

(**
*** Algebraic Properties

Algebraic operations still work well.
*)

Variable J : interval.
Variables f g : nat -> PartIR.

Hypothesis contf : forall n : nat, Continuous J (f n).
Hypothesis contg : forall n : nat, Continuous J (g n).

Lemma FLim_unique_IR : forall F G HF HG,
 conv_fun_seq'_IR J f F contf HF -> conv_fun_seq'_IR J f G contf HG -> Feq J F G.
Proof.
 intros F G HF HG H H0.
 apply included_Feq'.
 intros a b Hab H1.
 apply FLim_unique with f (fun n : nat => included_imp_Continuous _ _ (contf n) _ _ _ H1)
   (included_imp_Continuous _ _ HF _ _ _ H1) (included_imp_Continuous _ _ HG _ _ _ H1); auto.
Qed.

Lemma Cauchy_fun_seq_wd_IR : (forall n, Feq J (f n) (g n)) ->
 Cauchy_fun_seq_IR _ _ contf -> Cauchy_fun_seq_IR _ _ contg.
Proof.
 intros H H0 a b Hab Hinc.
 eapply Cauchy_fun_seq_wd with (f := f).
  2: apply (H0 a b Hab Hinc).
 intro; apply included_Feq with J; auto.
Qed.

Lemma fun_Lim_seq_const_IR : forall H contH contH',
 conv_fun_seq'_IR J (fun n => H) H contH contH'.
Proof.
 exists 0; intros.
 eapply leEq_wdl.
  2: eapply eq_transitive_unfolded.
   2: apply eq_symmetric_unfolded; apply AbsIRz_isz.
  apply less_leEq; assumption.
 apply AbsIR_wd; rational.
Qed.

Lemma fun_Cauchy_prop_const_IR : forall H (contH:Continuous J H), Cauchy_fun_seq_IR J (fun n => H) (fun n => contH).
Proof.
 intros.
 apply conv_Cauchy_fun_seq'_IR with H (contH).
 apply fun_Lim_seq_const_IR.
Qed.

Variables F G : PartIR.
Hypothesis contF : Continuous J F.
Hypothesis contG : Continuous J G.

(* begin show *)
Hypothesis convF : conv_fun_seq'_IR _ _ _ contf contF.
Hypothesis convG : conv_fun_seq'_IR _ _ _ contg contG.
(* end show *)

Lemma fun_Lim_seq_plus'_IR : forall H H',
 conv_fun_seq'_IR J (fun n => f n{+}g n) (F{+}G) H H'.
Proof.
 intros.
 red in |- *; intros.
 eapply fun_Lim_seq_plus'.
  apply (convF a b Hab Hinc).
 apply (convG a b Hab Hinc).
Qed.

Lemma fun_Lim_seq_minus'_IR : forall H H',
 conv_fun_seq'_IR J (fun n => f n{-}g n) (F{-}G) H H'.
Proof.
 intros.
 red in |- *; intros.
 eapply fun_Lim_seq_minus'.
  apply (convF a b Hab Hinc).
 apply (convG a b Hab Hinc).
Qed.

Lemma fun_Lim_seq_mult'_IR : forall H H',
 conv_fun_seq'_IR J (fun n => f n{*}g n) (F{*}G) H H'.
Proof.
 intros.
 red in |- *; intros.
 eapply fun_Lim_seq_mult'.
  apply (convF a b Hab Hinc).
 apply (convG a b Hab Hinc).
Qed.

End Algebraic_Properties.

Section More_Algebraic_Properties.

(**
If we work with the limit function things fit in just as well.
*)

Variable J : interval.
Variables f g : nat -> PartIR.

Hypothesis contf : forall n : nat, Continuous J (f n).
Hypothesis contg : forall n : nat, Continuous J (g n).

(* begin show *)
Hypothesis Hf : Cauchy_fun_seq_IR _ _ contf.
Hypothesis Hg : Cauchy_fun_seq_IR _ _ contg.
(* end show *)

Lemma fun_Lim_seq_plus_IR : forall H H', conv_fun_seq'_IR J (fun n => f n{+}g n)
 (Cauchy_fun_seq_Lim_IR _ _ _ Hf{+}Cauchy_fun_seq_Lim_IR _ _ _ Hg) H H'.
Proof.
 intros.
 red in |- *; intros.
 cut (Continuous_I Hab (Cauchy_fun_seq_Lim _ _ _ _ _ (Hf a b Hab Hinc))); [ intro H0 | Contin ].
 cut (Continuous_I Hab (Cauchy_fun_seq_Lim _ _ _ _ _ (Hg a b Hab Hinc))); [ intro H1 | Contin ].
 eapply conv_fun_seq'_wdr with (contF := Continuous_I_plus _ _ _ _ _ H0 H1).
  apply Feq_symmetric; apply Feq_plus; apply Cauchy_fun_seq_Lim_char.
 apply fun_Lim_seq_plus with (Hf := Hf a b Hab Hinc) (Hg := Hg a b Hab Hinc)
   (H := fun n : nat => included_imp_Continuous _ _ (H n) _ _ _ Hinc).
Qed.

Lemma fun_Cauchy_prop_plus : forall H, Cauchy_fun_seq_IR J (fun n => f n{+}g n) H.
Proof.
 intro.
 cut (Continuous J (Cauchy_fun_seq_Lim_IR _ _ _ Hf{+}Cauchy_fun_seq_Lim_IR _ _ _ Hg));
   [ intro H0 | Contin ].
 apply conv_Cauchy_fun_seq'_IR
   with (Cauchy_fun_seq_Lim_IR _ _ _ Hf{+}Cauchy_fun_seq_Lim_IR _ _ _ Hg) H0.
 apply fun_Lim_seq_plus_IR.
Qed.

Lemma fun_Lim_seq_inv_IR : forall H H',
 conv_fun_seq'_IR J (fun n => {--} (f n)) {--} (Cauchy_fun_seq_Lim_IR _ _ _ Hf) H H'.
Proof.
 intros.
 red in |- *; intros.
 cut (Continuous_I Hab (Cauchy_fun_seq_Lim _ _ _ _ _ (Hf a b Hab Hinc))); [ intro H0 | Contin ].
 intros.
 eapply conv_fun_seq'_wdr with (contF := Continuous_I_inv _ _ _ _ H0).
  apply Feq_symmetric; apply Feq_inv; apply Cauchy_fun_seq_Lim_char.
 apply fun_Lim_seq_inv with (Hf := Hf a b Hab Hinc)
   (H := fun n : nat => included_imp_Continuous _ _ (H n) _ _ _ Hinc).
Qed.

Lemma fun_Cauchy_prop_inv : forall H, Cauchy_fun_seq_IR J (fun n => {--} (f n)) H.
Proof.
 intro.
 cut (Continuous J {--} (Cauchy_fun_seq_Lim_IR _ _ _ Hf)); [ intro H0 | Contin ].
 apply conv_Cauchy_fun_seq'_IR with ( {--} (Cauchy_fun_seq_Lim_IR _ _ _ Hf)) H0.
 apply fun_Lim_seq_inv_IR.
Qed.

Lemma fun_Lim_seq_minus_IR : forall H H', conv_fun_seq'_IR J (fun n => f n{-}g n)
 (Cauchy_fun_seq_Lim_IR _ _ _ Hf{-}Cauchy_fun_seq_Lim_IR _ _ _ Hg) H H'.
Proof.
 intros.
 red in |- *; intros.
 cut (Continuous_I Hab (Cauchy_fun_seq_Lim _ _ _ _ _ (Hf a b Hab Hinc))); [ intro H0 | Contin ].
 cut (Continuous_I Hab (Cauchy_fun_seq_Lim _ _ _ _ _ (Hg a b Hab Hinc))); [ intro H1 | Contin ].
 intros.
 eapply conv_fun_seq'_wdr with (contF := Continuous_I_minus _ _ _ _ _ H0 H1).
  apply Feq_symmetric; apply Feq_minus; apply Cauchy_fun_seq_Lim_char.
 apply fun_Lim_seq_minus with (Hf := Hf a b Hab Hinc) (Hg := Hg a b Hab Hinc)
   (H := fun n : nat => included_imp_Continuous _ _ (H n) _ _ _ Hinc).
Qed.

Lemma fun_Cauchy_prop_minus : forall H, Cauchy_fun_seq_IR J (fun n => f n{-}g n) H.
Proof.
 intro.
 cut (Continuous J (Cauchy_fun_seq_Lim_IR _ _ _ Hf{-}Cauchy_fun_seq_Lim_IR _ _ _ Hg));
   [ intro H0 | Contin ].
 apply conv_Cauchy_fun_seq'_IR
   with (Cauchy_fun_seq_Lim_IR _ _ _ Hf{-}Cauchy_fun_seq_Lim_IR _ _ _ Hg) H0.
 apply fun_Lim_seq_minus_IR.
Qed.

Lemma fun_Lim_seq_mult_IR : forall H H', conv_fun_seq'_IR J (fun n => f n{*}g n)
 (Cauchy_fun_seq_Lim_IR _ _ _ Hf{*}Cauchy_fun_seq_Lim_IR _ _ _ Hg) H H'.
Proof.
 intros.
 red in |- *; intros.
 cut (Continuous_I Hab (Cauchy_fun_seq_Lim _ _ _ _ _ (Hf a b Hab Hinc))); [ intro H0 | Contin ].
 cut (Continuous_I Hab (Cauchy_fun_seq_Lim _ _ _ _ _ (Hg a b Hab Hinc))); [ intro H1 | Contin ].
 intros.
 eapply conv_fun_seq'_wdr with (contF := Continuous_I_mult _ _ _ _ _ H0 H1).
  apply Feq_symmetric; apply Feq_mult; apply Cauchy_fun_seq_Lim_char.
 apply fun_Lim_seq_mult with (Hf := Hf a b Hab Hinc) (Hg := Hg a b Hab Hinc)
   (H := fun n : nat => included_imp_Continuous _ _ (H n) _ _ _ Hinc).
Qed.

Lemma fun_Cauchy_prop_mult : forall H, Cauchy_fun_seq_IR J (fun n => f n{*}g n) H.
Proof.
 intro.
 cut (Continuous J (Cauchy_fun_seq_Lim_IR _ _ _ Hf{*}Cauchy_fun_seq_Lim_IR _ _ _ Hg));
   [ intro H0 | Contin ].
 apply conv_Cauchy_fun_seq'_IR
   with (Cauchy_fun_seq_Lim_IR _ _ _ Hf{*}Cauchy_fun_seq_Lim_IR _ _ _ Hg) H0.
 apply fun_Lim_seq_mult_IR.
Qed.

End More_Algebraic_Properties.

Section Other.

(**
*** Miscellaneous

Finally, we define a mapping between sequences of real numbers and sequences of (constant) functions and prove that convergence is preserved.
*)

Definition seq_to_funseq (x : nat -> IR) n : PartIR := [-C-] (x n).

Lemma funseq_conv : forall J x y, nonvoid J -> conv_fun_seq'_IR J
 (seq_to_funseq x) [-C-]y (fun n => Continuous_const _ _) (Continuous_const _ _) ->
 Cauchy_Lim_prop2 x y.
Proof.
 intros J x y H H0 eps H1.
 elim (nonvoid_point J H); intros x0 Hx0.
 cut (included (compact_single x0) J).
  2: apply compact_single_iprop; auto.
 intro H2.
 elim (H0 _ _ (leEq_reflexive _ _) H2 eps).
  intros N HN.
  exists N; intros.
  simpl in HN.
  apply AbsIR_imp_AbsSmall.
  apply HN with x0.
   auto.
  fold (compact_single x0) in |- *.
  apply compact_single_prop.
 auto.
Qed.

(**
Another interesting fact: if a sequence of constant functions converges then it must converge to a constant function.
*)

Lemma fun_const_Lim : forall J f F contf contF, proper J ->
 conv_fun_seq'_IR J f F contf contF -> (forall n, {c : IR | Feq J (f n) [-C-]c}) ->
 {c : IR | Feq J F [-C-]c}.
Proof.
 intros J f F contf contF pJ H H0.
 set (incF := Continuous_imp_inc _ _ contF) in *.
 set (incf := fun n : nat => Continuous_imp_inc _ _ (contf n)) in *.
 elim (nonvoid_point _ (proper_nonvoid _ pJ)); intros x0 Hx0.
 exists (Part F x0 (incF x0 Hx0)).
 FEQ. rename X into H1.
 simpl in |- *.
 apply cg_inv_unique_2; apply AbsIR_approach_zero.
 intros e H2.
 cut (included (Compact (Min_leEq_Max x x0)) J).
  2: apply included_interval; auto.
 intro Hinc.
 elim (H _ _ _ Hinc _ (pos_div_two _ _ H2)); intros N HN.
 set (Fx := Part _ _ Hx) in *.
 set (Fa := Part _ _ (incF x0 Hx0)) in *.
 set (fx := Part _ _ (incf N x H1)) in *.
 set (fa := Part _ _ (incf N x0 Hx0)) in *.
 apply leEq_wdl with (AbsIR (Fx[-]fx[+] (fx[-]fa) [+] (fa[-]Fa))).
  2: apply AbsIR_wd; rational.
 rstepr (e [/]TwoNZ[+]Zero[+]e [/]TwoNZ).
 eapply leEq_transitive.
  apply triangle_IR.
 apply plus_resp_leEq_both.
  eapply leEq_transitive.
   apply triangle_IR.
  apply plus_resp_leEq_both.
   eapply leEq_wdl.
    2: apply AbsIR_minus.
   eapply leEq_wdl.
    apply (HN N (le_n N) x (compact_Min_lft _ _ _)).
   unfold Fx, fx in |- *; apply AbsIR_wd; rational.
  elim (H0 N); intros c Hc.
  apply eq_imp_leEq.
  eapply eq_transitive_unfolded.
   2: apply AbsIRz_isz.
  elim Hc; clear Hc; intros H5 H3.
  elim H3; clear H3; intros H6 H4.
  apply AbsIR_wd; unfold fx, fa in |- *; astepr (c[-]c).
  apply cg_minus_wd; simpl in H4; apply H4; auto.
 eapply leEq_wdl.
  apply (HN N (le_n N) x0 (compact_Min_rht _ _ _)).
 unfold Fa, fa in |- *; apply AbsIR_wd; rational.
Qed.

End Other.

Section Series_Definitions.

(**
** Series

We now consider series of functions defined in arbitrary intervals.

Convergence is defined as expected---through convergence in every compact interval.
*)

Variable J : interval.
Variable f : nat -> PartIR.

Definition fun_series_convergent_IR := forall a b Hab (Hinc : included (Compact Hab) J),
  fun_series_convergent a b Hab f.

Lemma fun_series_conv_imp_conv_IR : fun_series_convergent_IR ->
 forall x, J x -> forall Hx, convergent (fun n : nat => f n x (Hx n)).
Proof.
 intros H x H0 Hx.
 apply fun_series_conv_imp_conv with (Hab := leEq_reflexive _ x).
  apply H.
  fold (compact_single x) in |- *; apply compact_single_iprop; auto.
 apply compact_single_prop.
Qed.

(* begin show *)
Hypothesis H : fun_series_convergent_IR.
(* end show *)

Lemma fun_series_inc_IR : forall x, J x -> forall n, Dom (f n) x.
Proof.
 intros x H0 n.
 elim (H _ _ (leEq_reflexive _ x) (compact_single_iprop J x H0)).
 intros contF CauchyF.
 apply (contin_imp_inc _ _ _ _ (contF n)).
 apply compact_single_prop.
Qed.

(** Assume [h(x)] is the pointwise series of [f(x)] *)

(* begin hide *)
Let h (x : IR) (Hx : J x) := series_sum _
    (fun_series_conv_imp_conv _ _ _ _
       (H _ _ (leEq_reflexive _ x) (compact_single_iprop J x Hx)) x
       (compact_single_prop x) (fun_series_inc_IR x Hx)).
(* end hide *)

Lemma FSeries_Sum_strext_IR : forall x y Hx Hy, h x Hx [#] h y Hy -> x [#] y.
Proof.
 unfold h in |- *; clear h; intros x y Hx Hy H0.
 unfold series_sum in H0.
 elim (Lim_strext _ _ H0); intros N HN.
 simpl in HN; unfold seq_part_sum in HN.
 elim (Sum0_strext _ _ _ _ HN); intros.
 exact (pfstrx _ _ _ _ _ _ q).
Qed.

Definition FSeries_Sum : PartIR.
Proof.
 apply Build_PartFunct with (pfpfun := h).
  apply iprop_wd.
 exact FSeries_Sum_strext_IR.
Defined.

Lemma FSeries_Sum_char : forall a b Hab (Hinc : included (Compact Hab) J),
 Feq (Compact Hab) FSeries_Sum (Fun_Series_Sum (H a b Hab Hinc)).
Proof.
 intros; FEQ.
 simpl in |- *; Included.
 simpl in |- *; unfold h in |- *.
 apply series_sum_wd; intros; algebra.
Qed.

End Series_Definitions.

Implicit Arguments FSeries_Sum [J f].

Section More_Series_Definitions.

Variable J : interval.
Variable f : nat -> PartIR.

(**
Absolute convergence still exists.
*)

Definition fun_series_abs_convergent_IR :=
 fun_series_convergent_IR J (fun n => FAbs (f n)).

End More_Series_Definitions.

Section Convergence_Results.

(**
As before, any series converges to its sum.
*)

Variable J : interval.
Variable f : nat -> PartIR.

Lemma FSeries_conv : forall (convF : fun_series_convergent_IR J f) H H',
 conv_fun_seq'_IR J (fun n => FSum0 n f) (FSeries_Sum convF) H H'.
Proof.
 intros.
 red in |- *; intros.
 elim (convF _ _ _ Hinc); intros Hcont Hconv.
 apply conv_fun_seq'_wdr with (f := fun n : nat => FSum0 n f)
   (contf := fun n : nat => included_imp_Continuous _ _ (H n) _ _ _ Hinc)
     (contF := Fun_Series_Sum_cont _ _ _ _ (convF _ _ _ Hinc)).
  apply Feq_symmetric; apply FSeries_Sum_char.
 apply conv_fun_seq'_wdl with (f := fun_seq_part_sum f)
   (contf := fun n : nat => included_imp_Continuous _ _ (H n) _ _ _ Hinc)
     (contF := Fun_Series_Sum_cont _ _ _ _ (convF _ _ _ Hinc)).
  intro; apply Feq_reflexive.
  red in |- *; intros.
  simpl in |- *; intros.
  apply (contin_imp_inc _ _ _ _ (Hcont n0)); auto.
 apply fun_series_conv.
Qed.

Lemma convergent_imp_inc : fun_series_convergent_IR J f -> forall n, included J (Dom (f n)).
Proof.
 intros H n.
 apply included_imp_inc.
 intros a b Hab H0.
 red in H.
 elim (H _ _ _ H0); intros.
 apply contin_imp_inc; auto.
Qed.

Lemma convergent_imp_Continuous : fun_series_convergent_IR J f -> forall n,
 Continuous J (f n).
Proof.
 intros H n.
 split.
  exact (convergent_imp_inc H n).
 intros a b Hab H0; auto.
 elim (H a b Hab H0); auto.
Qed.

Lemma Continuous_FSeries_Sum : forall H, Continuous J (FSeries_Sum (J:=J) (f:=f) H).
Proof.
 intros.
 split; Included.
 intros a b Hab H0.
 eapply Continuous_I_wd.
  apply Feq_symmetric; apply (FSeries_Sum_char _ _ H _ _ _ H0).
 eapply Continuous_I_wd.
  apply Fun_Series_Sum_char.
 apply Cauchy_cont_Lim.
Qed.

End Convergence_Results.

Hint Resolve convergent_imp_inc: included.
Hint Resolve convergent_imp_Continuous Continuous_FSeries_Sum: continuous.

Section Operations.

(**
** Algebraic Operations

Convergence is well defined and preserved by operations.
*)

Variable J : interval.

Lemma conv_fun_const_series_IR : forall x : nat -> IR, convergent x ->
 fun_series_convergent_IR J (fun n => [-C-] (x n)).
Proof.
 intros.
 red in |- *; intros.
 apply conv_fun_const_series; auto.
Qed.

Lemma fun_const_series_Sum_IR : forall y H
 (H' : fun_series_convergent_IR J (fun n => [-C-] (y n))) x Hx, FSeries_Sum H' x Hx [=] series_sum y H.
Proof.
 intros.
 simpl in |- *.
 apply series_sum_wd.
 algebra.
Qed.

Lemma conv_zero_fun_series_IR : fun_series_convergent_IR J (fun n => [-C-]Zero).
Proof.
 apply conv_fun_const_series_IR with (x := fun n : nat => ZeroR).
 apply conv_zero_series.
Qed.

Lemma FSeries_Sum_zero_IR : forall (H : fun_series_convergent_IR J (fun n => [-C-]Zero))
   x Hx, FSeries_Sum H x Hx [=] Zero.
Proof.
 intros.
 simpl in |- *.
 apply series_sum_zero.
Qed.

Variables f g : nat -> PartIR.

Lemma fun_series_convergent_wd_IR : (forall n, Feq J (f n) (g n)) ->
 fun_series_convergent_IR J f -> fun_series_convergent_IR J g.
Proof.
 intros.
 red in |- *; intros.
 apply fun_series_convergent_wd with f.
  intros; apply included_Feq with J; auto.
 auto.
Qed.

(* begin show *)
Hypothesis convF : fun_series_convergent_IR J f.
Hypothesis convG : fun_series_convergent_IR J g.
(* end show *)

Lemma FSeries_Sum_wd' : (forall n, Feq J (f n) (g n)) -> Feq J (FSeries_Sum convF) (FSeries_Sum convG).
Proof.
 intros H.
 apply included_Feq'; intros a b Hab H0.
 eapply Feq_transitive.
  apply (FSeries_Sum_char _ _ convF a b Hab H0).
 eapply Feq_transitive.
  2: apply Feq_symmetric; apply (FSeries_Sum_char _ _ convG a b Hab H0).
 apply Fun_Series_Sum_wd'.
 intro; apply included_Feq with J; auto.
Qed.

Lemma FSeries_Sum_plus_conv : fun_series_convergent_IR J (fun n => f n{+}g n).
Proof.
 red in |- *; intros.
 apply conv_fun_series_plus; auto.
Qed.

Lemma FSeries_Sum_plus : forall H : fun_series_convergent_IR J (fun n => f n{+}g n),
 Feq J (FSeries_Sum H) (FSeries_Sum convF{+}FSeries_Sum convG).
Proof.
 intros.
 apply included_Feq'; intros a b Hab H0.
 eapply Feq_transitive.
  apply (FSeries_Sum_char _ _ H a b Hab H0).
 eapply Feq_transitive.
  apply Fun_Series_Sum_plus with (convF := convF a b Hab H0) (convG := convG a b Hab H0).
 apply Feq_symmetric; apply Feq_plus; apply FSeries_Sum_char.
Qed.

Lemma FSeries_Sum_inv_conv : fun_series_convergent_IR J (fun n => {--} (f n)).
Proof.
 red in |- *; intros.
 apply conv_fun_series_inv; auto.
Qed.

Lemma FSeries_Sum_inv : forall H : fun_series_convergent_IR J (fun n => {--} (f n)),
 Feq J (FSeries_Sum H) {--} (FSeries_Sum convF).
Proof.
 intros.
 apply included_Feq'; intros a b Hab H0.
 eapply Feq_transitive.
  apply (FSeries_Sum_char _ _ H a b Hab H0).
 eapply Feq_transitive.
  apply Fun_Series_Sum_inv with (convF := convF a b Hab H0).
 apply Feq_symmetric; apply Feq_inv; apply FSeries_Sum_char.
Qed.

Lemma FSeries_Sum_minus_conv : fun_series_convergent_IR J (fun n => f n{-}g n).
Proof.
 red in |- *; intros.
 apply conv_fun_series_minus; auto.
Qed.

Lemma FSeries_Sum_minus : forall H : fun_series_convergent_IR J (fun n => f n{-}g n),
 Feq J (FSeries_Sum H) (FSeries_Sum convF{-}FSeries_Sum convG).
Proof.
 intros.
 apply included_Feq'; intros a b Hab H0.
 eapply Feq_transitive.
  apply (FSeries_Sum_char _ _ H a b Hab H0).
 eapply Feq_transitive.
  apply Fun_Series_Sum_min with (convF := convF a b Hab H0) (convG := convG a b Hab H0).
 apply Feq_symmetric; apply Feq_minus; apply FSeries_Sum_char.
Qed.

(**
%\begin{convention}% Let [c:IR] and [H:PartIR] be continuous in [J].
%\end{convention}%
*)

Variable c : IR.
Variable H : PartIR.
Hypothesis contH : Continuous J H.

Lemma FSeries_Sum_scal_conv : fun_series_convergent_IR J (fun n => H{*}f n).
Proof.
 red in |- *; intros.
 apply conv_fun_series_scal; auto.
 eapply included_imp_Continuous.
  apply contH.
 auto.
Qed.

Lemma FSeries_Sum_scal : forall H' : fun_series_convergent_IR J (fun n => H{*}f n),
 Feq J (FSeries_Sum H') (H{*}FSeries_Sum convF).
Proof.
 intros.
 apply included_Feq'; intros a b Hab H0.
 cut (Continuous_I Hab H). intro H1.
  eapply Feq_transitive.
   apply (FSeries_Sum_char _ _ H' a b Hab H0).
  eapply Feq_transitive.
   apply Fun_Series_Sum_scal with (convF := convF a b Hab H0).
   auto.
  apply Feq_symmetric; apply Feq_mult.
   apply Feq_reflexive; Included.
  apply FSeries_Sum_char.
 eapply included_imp_Continuous.
  apply contH.
 auto.
Qed.

End Operations.

Section Convergence_Criteria.

(**
*** Convergence Criteria

The most important tests for convergence of series still apply: the
comparison test (in both versions) and the ratio test.
*)

Variable J : interval.
Variable f : nat -> PartIR.
Hypothesis contF : forall n, Continuous J (f n).

Lemma fun_str_comparison_IR : forall g : nat -> PartIR, fun_series_convergent_IR J g ->
 {k : nat | forall n, k <= n -> forall x, J x -> forall Hx Hx', AbsIR (f n x Hx) [<=] g n x Hx'} ->
 fun_series_convergent_IR J f.
Proof.
 intros g H H0 a b Hab H1.
 apply fun_str_comparison with g.
   intro; apply included_imp_Continuous with J; auto.
  auto.
 elim H0; clear H0; intros k Hk.
 exists k; intros.
 apply Hk; auto.
Qed.

Lemma fun_comparison_IR : forall g : nat -> PartIR, fun_series_convergent_IR J g ->
 (forall n x, J x -> forall Hx Hx', AbsIR (f n x Hx) [<=] g n x Hx') ->
 fun_series_convergent_IR J f.
Proof.
 intros g H H0.
 apply fun_str_comparison_IR with g; auto.
 exists 0; intros; apply H0; auto.
Qed.

Lemma abs_imp_conv_IR : fun_series_abs_convergent_IR J f ->
 fun_series_convergent_IR J f.
Proof.
 intro H.
 apply fun_comparison_IR with (fun n => FAbs (f n)).
  apply H.
 intros; apply eq_imp_leEq; apply eq_symmetric_unfolded; apply FAbs_char.
Qed.

Lemma fun_ratio_test_conv_IR : {N : nat | {c : IR | c [<] One | Zero [<=] c /\ (forall x,
  J x -> forall n, N <= n -> forall Hx Hx', AbsIR (f (S n) x Hx') [<=] c[*]AbsIR (f n x Hx))}} ->
 fun_series_convergent_IR J f.
Proof.
 intro H.
 red in |- *; intros.
 apply fun_ratio_test_conv.
  intro; apply included_imp_Continuous with J; auto.
 elim H; intros N HN.
 elim HN; clear H HN; intros c Hc H.
 inversion_clear H.
 exists N; exists c; repeat split; auto.
Qed.

End Convergence_Criteria.

Section Power_Series.

(** ***Power Series

The geometric series converges on the open interval (-1, 1)
*)

Lemma fun_power_series_conv_IR : fun_series_convergent_IR (olor ([--]One) One) (fun (i:nat) => Fid IR{^}i).
Proof.
 intros a b Hab H.
 apply fun_ratio_test_conv.
  intros n.
  Contin.
 exists 0%nat.
 exists (Max (AbsIR a) (AbsIR b)).
  destruct (H a) as [Ha0 Ha1].
   split; assumption || apply leEq_reflexive.
  destruct (H b) as [Hb0 Hb1].
   split; assumption || apply leEq_reflexive.
  apply Max_less; apply AbsIR_less; assumption.
 split.
  eapply leEq_transitive.
   apply AbsIR_nonneg.
  apply lft_leEq_Max.
 simpl.
 intros x Hx n Hn _ _.
 rstepr (ABSIR (nexp IR n x)[*]MAX (ABSIR a) (ABSIR b)).
 change (AbsIR (nexp IR n x[*]x)[<=]AbsIR (nexp IR n x)[*]Max (AbsIR a) (AbsIR b)).
 stepl (AbsIR (nexp IR n x)[*]AbsIR x); [| apply eq_symmetric; apply AbsIR_resp_mult].
 apply mult_resp_leEq_lft;[|apply AbsIR_nonneg].
 apply AbsSmall_imp_AbsIR.
 destruct Hx.
 split.
  apply leEq_transitive with a;[|assumption].
  rstepr ([--][--]a).
  apply inv_resp_leEq.
  apply leEq_transitive with (AbsIR a).
   apply inv_leEq_AbsIR.
  apply lft_leEq_Max.
 apply leEq_transitive with b;[assumption|].
 apply leEq_transitive with (AbsIR b).
  apply leEq_AbsIR.
 apply rht_leEq_Max.
Qed.

End Power_Series.

Section Insert_Series.

(**
*** Translation

When working in particular with power series and Taylor series, it is
sometimes useful to ``shift'' all the terms in the series one position
forward, that is, replacing each $f_{i+1}$#f<sub>i+1</sub># with
$f_i$#f<sub>i</sub># and inserting the null function in the first
position.  This does not affect convergence or the sum of the series.
*)

Variable J : interval.
Variable f : nat -> PartIR.
Hypothesis convF : fun_series_convergent_IR J f.

Definition insert_series n : PartIR :=
  match n with
  | O => [-C-]Zero
  | S p => f p
  end.

Lemma insert_series_cont : forall n, Continuous J (insert_series n).
Proof.
 intro; elim n; intros.
  simpl in |- *; apply Continuous_const.
 simpl in |- *; apply convergent_imp_Continuous; auto.
Qed.

Lemma insert_series_sum_char : forall n x Hx Hx',
 fun_seq_part_sum f n x Hx [=] fun_seq_part_sum insert_series (S n) x Hx'.
Proof.
 intro; induction  n as [| n Hrecn].
  intros; simpl in |- *; algebra.
 intros; simpl in |- *; simpl in Hrecn; algebra.
Qed.

Lemma insert_series_conv : fun_series_convergent_IR J insert_series.
Proof.
 intros a b Hab Hinc.
 elim (convF _ _ _ Hinc); intros Hcont HCauchy.
 exists (fun n => included_imp_Continuous _ _ (insert_series_cont n) _ _ _ Hinc).
 intros e H.
 elim (HCauchy e H); intros N HN.
 exists (S N); do 4 intro.
 cut (m = S (pred m)); [ intro | apply S_pred with 0; apply lt_le_trans with (S N); auto with arith ].
 cut (n = S (pred n)); [ intro | apply S_pred with 0; apply lt_le_trans with (S N); auto with arith ].
 generalize H0 H1; clear H1 H0.
 rewrite H2; rewrite H3; clear H2 H3.
 intros.
 cut (N <= pred m); [ intro | auto with arith ].
 cut (N <= pred n); [ intro | auto with arith ].
 eapply leEq_wdl.
  apply (HN _ _ H2 H3 x Hx).
 apply AbsIR_wd.
 apply cg_minus_wd; apply insert_series_sum_char.
Qed.

Lemma insert_series_sum : Feq J (FSeries_Sum convF) (FSeries_Sum insert_series_conv).
Proof.
 set (contF := convergent_imp_Continuous _ _ convF) in *.
 apply FLim_unique_IR with (fun n => FSum0 n f) (fun n => Continuous_Sum0 _ _ contF n)
   (Continuous_FSeries_Sum _ _ convF) (Continuous_FSeries_Sum _ _ insert_series_conv).
  apply FSeries_conv.
 red in |- *; intros.
 assert (convS := FSeries_conv _ _ insert_series_conv (Continuous_Sum0 _ _ insert_series_cont)
   (Continuous_FSeries_Sum _ _ insert_series_conv) _ _ _ Hinc).
 intros e H.
 elim (convS e H); intros N HN.
 clear convS; exists N; intros.
 eapply leEq_wdl.
  apply (HN (S n) (le_S _ _ H0) _ Hx).
 apply AbsIR_wd; apply cg_minus_wd.
  2: algebra.
 apply eq_symmetric_unfolded.
 eapply eq_transitive_unfolded.
  eapply eq_transitive_unfolded.
   2: apply (insert_series_sum_char n x (contin_imp_inc _ _ _ _
     (included_imp_Continuous _ _ (Continuous_Sum0 _ _ contF n) _ _ _ Hinc) _ Hx)
       (contin_imp_inc _ _ _ _ (included_imp_Continuous _ _
         (Continuous_Sum0 _ _ insert_series_cont (S n)) _ _ _ Hinc) _ Hx)).
  unfold fun_seq_part_sum in |- *; algebra.
 unfold fun_seq_part_sum in |- *; algebra.
Qed.

End Insert_Series.

