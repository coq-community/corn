
Require Export Continuity.
Require Export PartInterval.

Section Definitions.

(** *Sequences of Functions

In this file we define some more operators on functions, namely
sequences and limits.  These concepts are defined only for continuous
functions.

%\begin{convention}% Throughout this section:
 - [a] and [b] will be real numbers and the interval [[a,b]]
will be denoted by [I];
 - [f, g] and [h] will denote sequences of continuous functions;
 - [F, G] and [H] will denote continuous functions.

%\end{convention}%

**Definitions

A sequence of functions is simply an object of type [nat->PartIR].
However, we will be interested mostly in convergent and Cauchy
sequences.  Several definitions of these concepts will be formalized;
they mirror the several different ways in which a Cauchy sequence can
be defined.  For a discussion on the different notions of convergent
see Bishop 1967.
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variable f : nat -> PartIR.
Variable F : PartIR.

Hypothesis contf : forall n : nat, Continuous_I Hab (f n).
Hypothesis contF : Continuous_I Hab F.

(* begin hide *)
Let incf (n : nat) := contin_imp_inc _ _ _ _ (contf n).
Let incF := contin_imp_inc _ _ _ _ contF.
(* end hide *)

Definition Cauchy_fun_seq := forall e, Zero [<] e -> {N : nat | forall m n, N <= m -> N <= n ->
 forall x Hx, AbsIR (f m x (incf m x Hx) [-]f n x (incf n x Hx)) [<=] e}.

Definition conv_fun_seq' := forall e, Zero [<] e -> {N : nat | forall n, N <= n ->
 forall x Hx, AbsIR (f n x (incf n x Hx) [-]F x (incF x Hx)) [<=] e}.

Definition conv_norm_fun_seq := forall k, {N : nat | forall n, N <= n ->
 Norm_Funct (Continuous_I_minus _ _ _ _ _ (contf n) contF) [<=] one_div_succ k}.

Definition Cauchy_fun_seq1 := forall k, {N : nat | forall m n, N <= m -> N <= n ->
 Norm_Funct (Continuous_I_minus _ _ _ _ _ (contf m) (contf n)) [<=] one_div_succ k}.

Definition Cauchy_fun_seq' := forall k, {N : nat | forall m n, N <= m -> N <= n ->
  forall x Hx, AbsIR (Part _ _ (incf m x Hx) [-]Part _ _ (incf n x Hx)) [<=] one_div_succ k}.

Definition Cauchy_fun_seq2 := forall e, Zero [<] e -> {N : nat | forall m, N <= m ->
  forall x Hx, AbsIR (Part _ _ (incf m x Hx) [-]Part _ _ (incf N x Hx)) [<=] e}.

(**
These definitions are all shown to be equivalent.
*)

Lemma Cauchy_fun_seq_seq' : Cauchy_fun_seq -> Cauchy_fun_seq'.
intro H.
red in |- *; red in H.
intro.
exact (H (one_div_succ k) (one_div_succ_pos _ k)).
Qed.

Lemma Cauchy_fun_seq'_seq : Cauchy_fun_seq' -> Cauchy_fun_seq.
intro H.
red in |- *; red in H.
intros e He.
elim (Archimedes (One[/] e[//]pos_ap_zero _ _ He)).
intros i Hei.
cut (Zero [<] nring (R:=IR) i).
intro Hi.
elim (H i).
intros N HN; exists N.
intros.
apply leEq_transitive with (one_div_succ (R:=IR) i).
apply HN; assumption.
unfold one_div_succ in |- *.
rstepr (One[/] _[//]recip_ap_zero _ _ (pos_ap_zero _ _ He)).
unfold Snring in |- *.
apply recip_resp_leEq.
apply recip_resp_pos; assumption.
apply less_leEq; apply leEq_less_trans with (nring (R:=IR) i).
assumption.
simpl in |- *; apply less_plusOne.
apply less_leEq_trans with (One[/] e[//]pos_ap_zero _ _ He).
apply recip_resp_pos; assumption.
assumption.
Qed.

Lemma conv_Cauchy_fun_seq' : conv_fun_seq' -> Cauchy_fun_seq.
intro H.
red in |- *; red in H.
intros e He.
elim (H _ (pos_div_two _ _ He)).
intros N HN.
exists N; intros.
apply
 leEq_wdl
  with
    (AbsIR
       (f m x (incf m x Hx) [-]F x (incF x Hx) [+]
        (F x (incF x Hx) [-]f n x (incf n x Hx)))).
2: apply AbsIR_wd; rational.
eapply leEq_transitive.
apply triangle_IR.
rstepr (e [/]TwoNZ[+]e [/]TwoNZ).
apply plus_resp_leEq_both.
apply HN; assumption.
eapply leEq_wdl.
2: apply AbsIR_minus.
apply HN; assumption.
Qed.

Lemma Cauchy_fun_seq_seq2 : Cauchy_fun_seq -> Cauchy_fun_seq2.
intro H.
red in |- *; red in H.
intros e H0.
elim (H e H0); intros N HN; exists N.
intros; apply HN; auto with arith.
Qed.

Lemma Cauchy_fun_seq2_seq : Cauchy_fun_seq2 -> Cauchy_fun_seq.
intro H.
red in |- *; red in H.
intros e H0.
elim (H _ (pos_div_two _ _ H0)); intros N HN; exists N; intros.
apply
 leEq_wdl
  with
    (AbsIR
       (Part _ _ (incf m x Hx) [-]Part _ _ (incf N x Hx) [-]
        (Part _ _ (incf n x Hx) [-]Part _ _ (incf N x Hx)))).
2: apply AbsIR_wd; rational.
eapply leEq_transitive.
apply triangle_IR_minus.
rstepr (e [/]TwoNZ[+]e [/]TwoNZ).
apply plus_resp_leEq_both; apply HN; auto with arith.
Qed.

Lemma conv_fun_seq'_norm : conv_fun_seq' -> conv_norm_fun_seq.
intro H.
red in |- *; red in H.
intro.
elim (H (one_div_succ k) (one_div_succ_pos _ k)).
intros N HN.
exists N.
intros.
apply leEq_Norm_Funct.
fold I in |- *; intros x H1 Hx.
eapply leEq_wdl.
apply (HN n H0 x H1).
apply AbsIR_wd; simpl in |- *; rational.
Qed.

Lemma conv_fun_norm_seq : conv_norm_fun_seq -> conv_fun_seq'.
intro H.
red in |- *; red in H.
intros e He.
elim (Archimedes (One[/] _[//]pos_ap_zero _ _ He)).
intros k Hk.
elim (H k); clear H.
intros N HN.
exists N.
intros.
cut (Dom (f n{-}F) x). intro H0.
apply leEq_wdl with (AbsIR ((f n{-}F) x H0)).
eapply leEq_transitive.
2: apply leEq_transitive with (one_div_succ (R:=IR) k).
2: apply HN with (n := n); assumption.
apply norm_bnd_AbsIR; assumption.
unfold one_div_succ in |- *.
unfold Snring in |- *.
apply less_leEq; apply swap_div with (pos_ap_zero _ _ He).
apply pos_nring_S.
assumption.
eapply leEq_less_trans.
apply Hk.
simpl in |- *; apply less_plusOne.
apply AbsIR_wd; simpl in |- *; rational.
split.
apply incf; assumption.
apply incF; assumption.
Qed.

Lemma Cauchy_fun_seq1_seq' : Cauchy_fun_seq1 -> Cauchy_fun_seq'.
intro H.
red in |- *; red in H.
intro.
elim (H k); clear H; intros N HN.
exists N; intros.
eapply leEq_transitive.
2: apply HN with (m := m) (n := n); assumption.
cut (Dom (f m{-}f n) x). intro H1.
apply leEq_wdl with (AbsIR (Part _ _ H1)).
apply norm_bnd_AbsIR; assumption.
apply AbsIR_wd; simpl in |- *; rational.
split; simpl in |- *; apply incf; assumption.
Qed.

Lemma Cauchy_fun_seq'_seq1 : Cauchy_fun_seq' -> Cauchy_fun_seq1.
intro H.
red in |- *; red in H.
intro.
elim (H k); clear H; intros N HN.
exists N; intros.
apply leEq_Norm_Funct.
intros x H1 Hx.
eapply leEq_wdl.
apply (HN m n H H0 x H1).
apply AbsIR_wd; simpl in |- *; rational.
Qed.

Lemma Cauchy_fun_seq_seq1 : Cauchy_fun_seq -> Cauchy_fun_seq1.
intro.
apply Cauchy_fun_seq'_seq1.
apply Cauchy_fun_seq_seq'.
assumption.
Qed.

Lemma Cauchy_fun_seq1_seq : Cauchy_fun_seq1 -> Cauchy_fun_seq.
intro.
apply Cauchy_fun_seq'_seq.
apply Cauchy_fun_seq1_seq'.
assumption.
Qed.

(**
A Cauchy sequence of functions is pointwise a Cauchy sequence.
*)

Lemma Cauchy_fun_real : Cauchy_fun_seq -> forall x Hx,
 Cauchy_prop (fun n => Part _ _ (incf n x Hx)).
intros H x Hx.
red in |- *; red in H.
intros e He.
elim (H _ He); clear H; intros N HN.
exists N.
intros.
apply AbsIR_imp_AbsSmall.
apply HN.
assumption.
apply le_n.
Qed.

End Definitions.

Section More_Definitions.

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variable f : nat -> PartIR.
Hypothesis contf : forall n : nat, Continuous_I Hab (f n).

(**
We can also say that [f] is simply convergent if it converges to some
continuous function.  Notice that we do not quantify directly over
partial functions, for reasons which were already explained.
*)

Definition conv_fun_seq := {f' : CSetoid_fun (subset (Compact Hab)) IR |
 {contf' : Continuous_I Hab (PartInt f') |
  conv_fun_seq' a b Hab f (PartInt f') contf contf'}}.

(**
It is useful to extract the limit as a partial function:
*)

(* begin show *)
Hypothesis H : Cauchy_fun_seq _ _ _ f contf.
(* end show *)

Definition Cauchy_fun_seq_Lim : PartIR.
apply
 Build_PartFunct
  with
    (pfpfun := fun x Hx =>
               Lim
                 (Build_CauchySeq _
                    (fun n : nat =>
                     Part _ _ (contin_imp_inc _ _ _ _ (contf n) x Hx))
                    (Cauchy_fun_real _ _ _ _ contf H x Hx))).
unfold I in |- *; apply compact_wd.
intros x y Hx Hy H0.
elim (Lim_strext _ _ H0).
intros n Hn.
simpl in Hn.
exact (pfstrx _ _ _ _ _ _ Hn).
Defined.

End More_Definitions.

Section Irrelevance_of_Proofs.

(** **Irrelevance of Proofs

This section contains a number of technical results stating mainly that being a Cauchy sequence or converging to some limit is a property of the sequence itself and independent of the proofs we supply of its continuity or the continuity of its limit.
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variable f : nat -> PartIR.
(* begin show *)
Hypotheses contf contf0 : forall n : nat, Continuous_I Hab (f n).
(* end show *)

Variable F : PartIR.
(* begin show *)
Hypotheses contF contF0 : Continuous_I Hab F.
(* end show *)

Lemma conv_fun_seq'_wd : conv_fun_seq' _ _ _ _ _ contf contF ->
 conv_fun_seq' _ _ _ _ _ contf0 contF0.
intros H e H0.
elim (H e H0); intros N HN.
exists N; intros.
eapply leEq_wdl.
apply (HN n H1 x Hx).
apply AbsIR_wd; rational.
Qed.

Lemma Cauchy_fun_seq'_wd : Cauchy_fun_seq' _ _ _ _ contf ->
 Cauchy_fun_seq' _ _ _ _ contf0.
intros H k.
elim (H k); intros N HN.
exists N; intros.
eapply leEq_wdl.
apply (HN m n H0 H1 x Hx).
apply AbsIR_wd; rational.
Qed.

Lemma Cauchy_fun_seq2_wd : Cauchy_fun_seq2 _ _ _ _ contf ->
 Cauchy_fun_seq2 _ _ _ _ contf0.
intros H e H0.
elim (H e H0); intros N HN.
exists N; intros.
eapply leEq_wdl.
apply (HN m H1 x Hx).
apply AbsIR_wd; rational.
Qed.

Lemma conv_norm_fun_seq_wd : conv_norm_fun_seq _ _ _ _ _ contf contF ->
 conv_norm_fun_seq _ _ _ _ _ contf0 contF0.
intros H k.
elim (H k); intros N HN.
exists N; intros.
eapply leEq_wdl.
apply (HN n H0).
apply Norm_Funct_wd.
apply Feq_reflexive; Included.
Qed.

Lemma Cauchy_fun_seq1_wd : Cauchy_fun_seq1 _ _ _ _ contf ->
 Cauchy_fun_seq1 _ _ _ _ contf0.
intros H k.
elim (H k); intros N HN.
exists N; intros.
eapply leEq_wdl.
apply (HN m n H0 H1).
apply Norm_Funct_wd.
apply Feq_reflexive; Included.
Qed.

End Irrelevance_of_Proofs.

Section More_Proof_Irrelevance.

Lemma conv_fun_seq_wd : forall a b Hab f contf contf0,
 conv_fun_seq a b Hab f contf -> conv_fun_seq a b Hab f contf0.
intros a b Hab f contf contf0 H.
elim H; intros f' Hf'.
exists f'.
elim Hf'; intros contf' H0.
exists contf'.
eapply conv_fun_seq'_wd.
apply H0.
Qed.

End More_Proof_Irrelevance.

Section More_Properties.

(** **Other Properties

Still more technical details---a convergent sequence converges to its
limit; the limit is a continuous function; and convergence is well
defined with respect to functional equality in the interval [[a,b]].
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variables f g : nat -> PartIR.
(* begin show *)
Hypotheses contf contf0 : forall n, Continuous_I Hab (f n).
Hypotheses contg contg0 : forall n, Continuous_I Hab (g n).
(* end show *)

Lemma Cauchy_conv_fun_seq' : forall H contf',
 conv_fun_seq' _ _ _ _ (Cauchy_fun_seq_Lim _ _ _ f contf H) contf contf'.
intros H contf' e H0.
elim (H e H0).
intros N HN.
exists N.
intros.
set (incf := fun n : nat => contin_imp_inc _ _ _ _ (contf n)) in *.
set (incf' := contin_imp_inc _ _ _ _ contf') in *.
apply
 leEq_wdl
  with
    (AbsIR
       (Lim (Cauchy_const (f n x (incf n x Hx))) [-]
        Part (Cauchy_fun_seq_Lim _ _ _ _ _ H) x (incf' x Hx))).
2: apply AbsIR_wd; apply cg_minus_wd.
2: apply eq_symmetric_unfolded; apply Lim_const.
2: algebra.
simpl in |- *.
apply
 leEq_wdl
  with
    (AbsIR
       (Lim
          (Build_CauchySeq IR _
             (Cauchy_minus (Cauchy_const (Part _ _ (incf n x Hx)))
                (Build_CauchySeq _ _
                   (Cauchy_fun_real _ _ _ _ _ H x (incf' x Hx))))))).
2: apply AbsIR_wd; apply Lim_minus.
eapply leEq_wdl.
2: apply Lim_abs.
simpl in |- *.
apply str_seq_leEq_so_Lim_leEq.
exists N; intros.
simpl in |- *.
eapply leEq_wdl.
apply (HN n i H1 H2 x Hx).
apply AbsIR_wd; rational.
Qed.

Variables F G : PartIR.
(* begin show *)
Hypotheses contF contF0 : Continuous_I Hab F.
Hypotheses contG contG0 : Continuous_I Hab G.
(* end show *)

Lemma conv_fun_seq'_wdl : (forall n, Feq I (f n) (g n)) ->
 conv_fun_seq' _ _ _ _ _ contf contF -> conv_fun_seq' _ _ _ _ _ contg contF0.
intros H H0 e H1.
elim (H0 e H1); intros N HN.
exists N; intros.
eapply leEq_wdl.
apply (HN n H2 x Hx).
apply AbsIR_wd; apply cg_minus_wd.
elim (H n); intros Haux inc.
inversion_clear inc.
auto.
algebra.
Qed.

Lemma conv_fun_seq'_wdr : Feq I F G ->
 conv_fun_seq' _ _ _ _ _ contf contF -> conv_fun_seq' _ _ _ _ _ contf0 contG.
intros H H0 e H1.
elim (H0 e H1); intros N HN.
exists N; intros.
eapply leEq_wdl.
apply (HN n H2 x Hx).
apply AbsIR_wd; apply cg_minus_wd.
algebra.
elim H; intros Haux inc.
inversion_clear inc.
auto.
Qed.

Lemma conv_fun_seq'_wdl' : (forall n, Feq I (f n) (g n)) ->
 conv_fun_seq' _ _ _ _ _ contf contF -> conv_fun_seq' _ _ _ _ _ contg contF.
intros H H0 e H1.
elim (H0 e H1); intros N HN.
exists N; intros.
eapply leEq_wdl.
apply (HN n H2 x Hx).
apply AbsIR_wd; apply cg_minus_wd.
elim (H n); intros Haux inc.
inversion_clear inc.
auto.
algebra.
Qed.

Lemma conv_fun_seq'_wdr' : Feq I F G ->
 conv_fun_seq' _ _ _ _ _ contf contF -> conv_fun_seq' _ _ _ _ _ contf contG.
intros H H0 e H1.
elim (H0 e H1); intros N HN.
exists N; intros.
eapply leEq_wdl.
apply (HN n H2 x Hx).
apply AbsIR_wd; apply cg_minus_wd.
algebra.
elim H; intros Haux inc.
inversion_clear inc.
auto.
Qed.

Lemma Cauchy_fun_seq_wd : (forall n, Feq I (f n) (g n)) ->
 Cauchy_fun_seq _ _ _ _ contf -> Cauchy_fun_seq _ _ _ _ contg.
intros H H0 e H1.
elim (H0 e H1); clear H0; intros N HN.
exists N; intros.
eapply leEq_wdl.
apply (HN m n H0 H2 x Hx).
elim (H n); intros.
inversion_clear b0.
elim (H m); intros.
inversion_clear b0.
apply AbsIR_wd; algebra.
Qed.

Lemma Cauchy_cont_Lim : forall H : Cauchy_fun_seq a b Hab f contf,
 Continuous_I Hab (Cauchy_fun_seq_Lim _ _ _ _ contf H).
intros.
split.
Included.
intros e He.
elim (H _ (pos_div_three _ _ He)); intros N HN.
elim (contf N); intros incf contf'.
elim (contf' _ (pos_div_three _ _ He)).
intros d H0 H1.
exists d.
assumption.
intros x y H2 H3 Hx Hy H4.
cut (forall x y z w : IR, AbsIR (x[-]w) [=] AbsIR (x[-]y[+] (y[-]z) [+] (z[-]w)));
 intros.
2: apply AbsIR_wd; rational.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded;
    apply H5 with (y := Part _ _ (incf x H2)) (z := Part _ _ (incf y H3)).
rstepr (e [/]ThreeNZ[+]e [/]ThreeNZ[+]e [/]ThreeNZ).
eapply leEq_transitive.
apply triangle_IR.
apply plus_resp_leEq_both.
eapply leEq_transitive.
apply triangle_IR.
apply plus_resp_leEq_both.
apply
 leEq_wdl
  with (AbsIR (Part _ _ Hx[-]Lim (Cauchy_const (Part _ _ (incf x H2))))).
2: apply AbsIR_wd; apply cg_minus_wd.
2: algebra.
2: apply eq_symmetric_unfolded; apply Lim_const.
simpl in |- *.
apply
 leEq_wdl
  with
    (AbsIR
       (Lim
          (Build_CauchySeq IR _
             (Cauchy_minus
                (Build_CauchySeq _ _ (Cauchy_fun_real _ _ _ _ _ H x Hx))
                (Cauchy_const (Part _ _ (incf x H2))))))).
2: apply AbsIR_wd; apply Lim_minus.
eapply leEq_wdl.
2: apply Lim_abs.
simpl in |- *.
apply str_seq_leEq_so_Lim_leEq.
exists N; intros.
simpl in |- *.
eapply leEq_wdl.
apply (HN i N) with (x := x) (Hx := Hx); auto with arith.
apply AbsIR_wd; rational.
apply H1; assumption.
apply
 leEq_wdl
  with
    (AbsIR
       (Lim (Cauchy_const (Part _ _ (incf y H3))) [-]
        Part (Cauchy_fun_seq_Lim _ _ _ _ _ H) y Hy)).
2: apply AbsIR_wd; apply cg_minus_wd.
2: apply eq_symmetric_unfolded; apply Lim_const.
2: algebra.
simpl in |- *.
apply
 leEq_wdl
  with
    (AbsIR
       (Lim
          (Build_CauchySeq IR _
             (Cauchy_minus (Cauchy_const (Part _ _ (incf y H3)))
                (Build_CauchySeq _ _ (Cauchy_fun_real _ _ _ _ _ H y Hy)))))).
2: apply AbsIR_wd; apply Lim_minus.
eapply leEq_wdl.
2: apply Lim_abs.
simpl in |- *.
apply str_seq_leEq_so_Lim_leEq.
exists N; intros.
simpl in |- *.
eapply leEq_wdl.
apply (HN N i) with (x := y) (Hx := Hy); auto.
apply AbsIR_wd; rational.
Qed.

Lemma Cauchy_conv_fun_seq : Cauchy_fun_seq _ _ _ _ contf ->
 conv_fun_seq _ _ _ _ contf.
intro H.
cut (Continuous_I Hab (Cauchy_fun_seq_Lim _ _ _ _ _ H)). intro H0.
exists (IntPartIR (contin_imp_inc _ _ _ _ H0)).
cut (Continuous_I Hab (PartInt (IntPartIR (contin_imp_inc _ _ _ _ H0)))).
2: eapply Continuous_I_wd.
3: apply Cauchy_cont_Lim with (H := H).
2: FEQ.
2: simpl in |- *; apply Lim_wd'; intros; algebra.
intro H2; exists H2.
intros e H1.
elim (Cauchy_conv_fun_seq' H H0 e H1); intros N HN.
exists N; intros.
eapply leEq_wdl.
apply (HN n H3 x Hx).
apply AbsIR_wd; apply cg_minus_wd.
algebra.
simpl in |- *; apply Lim_wd'; intros; simpl in |- *; rational.
simpl in |- *; algebra.
simpl in |- *; apply Cauchy_cont_Lim.
Qed.

Lemma conv_Cauchy_fun_seq : conv_fun_seq _ _ _ _ contf ->
 Cauchy_fun_seq _ _ _ _ contf.
intro H.
elim H; intros ff Hff.
inversion_clear Hff.
apply conv_Cauchy_fun_seq' with (PartInt ff) x.
unfold I in |- *; eapply conv_fun_seq'_wd.
apply X.
Qed.

(**
More interesting is the fact that a convergent sequence of functions converges pointwise as a sequence of real numbers.
*)

Lemma fun_conv_imp_seq_conv : conv_fun_seq' _ _ _ _ _ contf contF -> forall x,
 Compact Hab x -> forall Hxf HxF, Cauchy_Lim_prop2 (fun n => f n x (Hxf n)) (F x HxF).
intros H x H0 Hxf HxF eps H1.
elim (H eps H1).
intros N HN.
exists N; intros.
apply AbsIR_imp_AbsSmall.
eapply leEq_wdl.
apply (HN m H2 x H0).
apply AbsIR_wd; algebra.
Qed.

(**
And a sequence of real numbers converges iff the corresponding sequence of constant functions converges to the corresponding constant function.
*)

Lemma seq_conv_imp_fun_conv : forall x y, Cauchy_Lim_prop2 x y ->
 forall Hf HF, conv_fun_seq' a b Hab (fun n => [-C-] (x n)) [-C-]y Hf HF.
intros x y H Hf HF e H0.
elim (H e H0); intros N HN.
exists N; intros; simpl in |- *.
apply AbsSmall_imp_AbsIR.
auto.
Qed.

End More_Properties.

Hint Resolve Cauchy_cont_Lim: continuous.

Section Algebraic_Properties.

(** **Algebraic Properties

We now study how convergence is affected by algebraic operations, and some algebraic properties of the limit function.
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variables f g : nat -> PartIR.
Hypothesis contf : forall n, Continuous_I Hab (f n).
Hypothesis contg : forall n, Continuous_I Hab (g n).

(**
First, the limit function is unique.
*)

Lemma FLim_unique : forall F G HF HG, conv_fun_seq' a b Hab f F contf HF ->
 conv_fun_seq' a b Hab f G contf HG -> Feq (Compact Hab) F G.
intros F G HF HG H H0.
cut (Cauchy_fun_seq _ _ Hab _ contf). intro H1.
apply Feq_transitive with (Cauchy_fun_seq_Lim _ _ _ _ _ H1).
FEQ.
simpl in |- *.
apply Limits_unique.
simpl in |- *.
eapply
 fun_conv_imp_seq_conv
                       with
                       (Hab := Hab)
                      (Hxf := 
                        fun n : nat =>
                        contin_imp_inc _ _ Hab _ (contf n) x Hx'); 
 auto.
apply H.
apply Feq_symmetric.
FEQ.
simpl in |- *.
apply Limits_unique.
simpl in |- *.
eapply
 fun_conv_imp_seq_conv
                       with
                       (Hab := Hab)
                      (Hxf := 
                        fun n : nat =>
                        contin_imp_inc _ _ Hab _ (contf n) x Hx'); 
 auto.
apply H0.
apply conv_Cauchy_fun_seq' with F HF; auto.
Qed.

(** Constant sequences (not sequences of constant functions!) always converge.
*)

Lemma fun_Lim_seq_const : forall H contH contH',
 conv_fun_seq' a b Hab (fun n => H) H contH contH'.
exists 0; intros.
eapply leEq_wdl.
2: eapply eq_transitive_unfolded.
2: apply eq_symmetric_unfolded; apply AbsIRz_isz.
apply less_leEq; assumption.
apply AbsIR_wd; rational.
Qed.

Lemma fun_Cauchy_prop_const : forall H contH,
 Cauchy_fun_seq a b Hab (fun n => H) contH.
intros.
apply conv_Cauchy_fun_seq' with H (contH 0).
apply fun_Lim_seq_const.
Qed.

(**
We now prove that if two sequences converge than their sum (difference, product) also converge to the sum (difference, product) of their limits.
*)

Variables F G : PartIR.
Hypothesis contF : Continuous_I Hab F.
Hypothesis contG : Continuous_I Hab G.

(* begin show *)
Hypothesis convF : conv_fun_seq' a b Hab f F contf contF.
Hypothesis convG : conv_fun_seq' a b Hab g G contg contG.
(* end show *)

(* begin hide *)
Let incf (n : nat) := contin_imp_inc _ _ _ _ (contf n).
Let incg (n : nat) := contin_imp_inc _ _ _ _ (contg n).
Let incF := contin_imp_inc _ _ _ _ contF.
Let incG := contin_imp_inc _ _ _ _ contG.
(* end hide *)

Lemma fun_Lim_seq_plus' : forall H H',
 conv_fun_seq' a b Hab (fun n => f n{+}g n) (F{+}G) H H'.
intros H H' e H0.
elim (convF _ (pos_div_two _ _ H0)); intros Nf HNf.
elim (convG _ (pos_div_two _ _ H0)); intros Ng HNg.
cut (Nf <= max Nf Ng); [ intro | apply le_max_l ].
cut (Ng <= max Nf Ng); [ intro | apply le_max_r ].
exists (max Nf Ng); intros.
apply
 leEq_wdl
  with
    (AbsIR
       (Part _ _ (incf n x Hx) [+]Part _ _ (incg n x Hx) [-]
        (Part _ _ (incF x Hx) [+]Part _ _ (incG x Hx)))).
2: apply AbsIR_wd; simpl in |- *; algebra.
apply
 leEq_wdl
  with
    (AbsIR
       (Part _ _ (incf n x Hx) [-]Part _ _ (incF x Hx) [+]
        (Part _ _ (incg n x Hx) [-]Part _ _ (incG x Hx)))).
2: apply AbsIR_wd; simpl in |- *; rational.
rstepr (e [/]TwoNZ[+]e [/]TwoNZ).
eapply leEq_transitive.
apply triangle_IR.
apply plus_resp_leEq_both.
unfold incf in |- *; apply HNf; apply le_trans with (max Nf Ng); auto.
unfold incg in |- *; apply HNg; apply le_trans with (max Nf Ng); auto.
Qed.

Lemma fun_Lim_seq_minus' : forall H H',
 conv_fun_seq' a b Hab (fun n => f n{-}g n) (F{-}G) H H'.
intros H H' e H0.
elim (convF _ (pos_div_two _ _ H0)); intros Nf HNf.
elim (convG _ (pos_div_two _ _ H0)); intros Ng HNg.
cut (Nf <= max Nf Ng); [ intro | apply le_max_l ].
cut (Ng <= max Nf Ng); [ intro | apply le_max_r ].
exists (max Nf Ng); intros.
apply
 leEq_wdl
  with
    (AbsIR
       (Part _ _ (incf n x Hx) [-]Part _ _ (incg n x Hx) [-]
        (Part _ _ (incF x Hx) [-]Part _ _ (incG x Hx)))).
2: apply AbsIR_wd; simpl in |- *; algebra.
apply
 leEq_wdl
  with
    (AbsIR
       (Part _ _ (incf n x Hx) [-]Part _ _ (incF x Hx) [-]
        (Part _ _ (incg n x Hx) [-]Part _ _ (incG x Hx)))).
2: apply AbsIR_wd; simpl in |- *; rational.
rstepr (e [/]TwoNZ[+]e [/]TwoNZ).
eapply leEq_transitive.
apply triangle_IR_minus.
apply plus_resp_leEq_both.
unfold incf in |- *; apply HNf; apply le_trans with (max Nf Ng); auto.
unfold incg in |- *; apply HNg; apply le_trans with (max Nf Ng); auto.
Qed.

Lemma fun_Lim_seq_mult' : forall H H',
 conv_fun_seq' a b Hab (fun n => f n{*}g n) (F{*}G) H H'.
intros.
set (nF := Norm_Funct contF) in *.
set (nG := Norm_Funct contG) in *.
red in |- *; intros.
set (ee := Min e One) in *.
cut (Zero [<] ee); intros.
set (eg := ee [/]ThreeNZ[/] _[//]max_one_ap_zero nF) in *.
set (ef := ee [/]ThreeNZ[/] _[//]max_one_ap_zero nG) in *.
cut (Zero [<] eg).
intro Heg.
cut (Zero [<] ef).
intro Hef.
elim (convF _ Hef); intros NF HNF; clear convF.
elim (convG _ Heg); intros NG HNG; clear convG.
cut (NF <= max NF NG); [ intro | apply le_max_l ].
cut (NG <= max NF NG); [ intro | apply le_max_r ].
exists (max NF NG); intros.
apply leEq_transitive with ee.
2: unfold ee in |- *; apply Min_leEq_lft.
apply
 leEq_wdl
  with
    (AbsIR
       (Part _ _ (incf n x Hx) [*]Part _ _ (incg n x Hx) [-]
        Part _ _ (incF x Hx) [*]Part _ _ (incG x Hx))).
2: apply AbsIR_wd; simpl in |- *; algebra.
apply
 leEq_wdl
  with
    (AbsIR
       (Part _ _ (incF x Hx) [*]
        (Part _ _ (incg n x Hx) [-]Part _ _ (incG x Hx)) [+]
        (Part _ _ (incf n x Hx) [-]Part _ _ (incF x Hx)) [*]
        (Part _ _ (incg n x Hx) [-]Part _ _ (incG x Hx)) [+]
        Part _ _ (incG x Hx) [*]
        (Part _ _ (incf n x Hx) [-]Part _ _ (incF x Hx)))).
2: apply AbsIR_wd; simpl in |- *; rational.
rstepr (ee [/]ThreeNZ[+]ee [/]ThreeNZ[+]ee [/]ThreeNZ).
eapply leEq_transitive.
apply triangle_IR.
apply plus_resp_leEq_both.
eapply leEq_transitive.
apply triangle_IR.
apply plus_resp_leEq_both.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
apply
 leEq_transitive
  with (Max nF One[*]AbsIR (Part _ _ (incg n x Hx) [-]Part _ _ (incG x Hx))).
apply mult_resp_leEq_rht.
apply leEq_transitive with nF.
unfold nF in |- *; apply norm_bnd_AbsIR; assumption.
apply lft_leEq_Max.
apply AbsIR_nonneg.
eapply shift_mult_leEq'.
apply pos_max_one.
unfold eg in HNG; unfold incg in |- *; apply HNG;
 apply le_trans with (max NF NG); auto.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
apply leEq_transitive with (ee [/]ThreeNZ[*]ee [/]ThreeNZ).
2: astepr (ee [/]ThreeNZ[*]One); apply mult_resp_leEq_lft.
apply mult_resp_leEq_both; try apply AbsIR_nonneg.
eapply leEq_transitive.
unfold incf in |- *; apply HNF; apply le_trans with (max NF NG); auto.
unfold ef in |- *.
apply shift_div_leEq.
apply pos_max_one.
astepl (ee [/]ThreeNZ[*]One); apply mult_resp_leEq_lft.
apply rht_leEq_Max.
apply less_leEq; apply shift_less_div; astepl ZeroR;
 [ apply pos_three | assumption ].
eapply leEq_transitive.
unfold incg in |- *; apply HNG; apply le_trans with (max NF NG); auto.
unfold eg in |- *.
apply shift_div_leEq.
apply pos_max_one.
astepl (ee [/]ThreeNZ[*]One); apply mult_resp_leEq_lft.
apply rht_leEq_Max.
apply less_leEq; apply shift_less_div; astepl ZeroR;
 [ apply pos_three | assumption ].
apply shift_div_leEq.
apply pos_three.
astepr (Three:IR).
unfold ee in |- *; apply leEq_transitive with OneR.
apply Min_leEq_rht.
apply less_leEq; apply one_less_three.
apply less_leEq; apply shift_less_div.
apply pos_three.
astepl ZeroR; assumption.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_resp_mult.
apply
 leEq_transitive
  with (Max nG One[*]AbsIR (Part _ _ (incf n x Hx) [-]Part _ _ (incF x Hx))).
apply mult_resp_leEq_rht.
apply leEq_transitive with nG.
unfold nG in |- *; apply norm_bnd_AbsIR; assumption.
apply lft_leEq_Max.
apply AbsIR_nonneg.
eapply shift_mult_leEq'.
apply pos_max_one.
unfold ef in HNF; unfold incf in |- *; apply HNF;
 apply le_trans with (max NF NG); auto.
unfold ef in |- *.
apply div_resp_pos.
apply pos_max_one.
apply shift_less_div; astepl ZeroR; [ apply pos_three | assumption ].
unfold eg in |- *.
apply div_resp_pos.
apply pos_max_one.
apply shift_less_div; astepl ZeroR; [ apply pos_three | assumption ].
unfold ee in |- *; apply less_Min.
assumption.
apply pos_one.
Qed.

End Algebraic_Properties.

Section More_Algebraic_Properties.

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variables f g : nat -> PartIR.
Hypothesis contf : forall n : nat, Continuous_I Hab (f n).
Hypothesis contg : forall n : nat, Continuous_I Hab (g n).

(**
The same is true if we don't make the limits explicit.
*)

(* begin hide *)
Hypothesis Hf : Cauchy_fun_seq _ _ _ _ contf.
Hypothesis Hg : Cauchy_fun_seq _ _ _ _ contg.
(* end hide *)

Lemma fun_Lim_seq_plus : forall H H', conv_fun_seq' a b Hab (fun n => f n{+}g n)
 (Cauchy_fun_seq_Lim _ _ _ _ _ Hf{+}Cauchy_fun_seq_Lim _ _ _ _ _ Hg) H H'.
intros H H' e H0.
set (F := Cauchy_fun_seq_Lim _ _ _ _ _ Hf) in *.
cut (Continuous_I Hab F). intro H1.
2: unfold F in |- *; apply Cauchy_cont_Lim.
cut (conv_fun_seq' _ _ _ _ _ contf H1).
2: unfold F in |- *; apply Cauchy_conv_fun_seq'; assumption.
intro Hf'.
set (G := Cauchy_fun_seq_Lim _ _ _ _ _ Hg) in *.
cut (Continuous_I Hab G). intro H2.
2: unfold G in |- *; apply Cauchy_cont_Lim.
cut (conv_fun_seq' _ _ _ _ _ contg H2).
2: unfold G in |- *; apply Cauchy_conv_fun_seq'; assumption.
intro Hg'.
apply fun_Lim_seq_plus' with contf contg H1 H2; auto.
Qed.

Lemma fun_Cauchy_prop_plus : forall H, Cauchy_fun_seq a b Hab (fun n => f n{+}g n) H.
intro.
cut
 (Continuous_I Hab
    (Cauchy_fun_seq_Lim _ _ _ _ _ Hf{+}Cauchy_fun_seq_Lim _ _ _ _ _ Hg));
 [ intro H0 | Contin ].
apply
 conv_Cauchy_fun_seq'
  with (Cauchy_fun_seq_Lim _ _ _ _ _ Hf{+}Cauchy_fun_seq_Lim _ _ _ _ _ Hg) H0.
apply fun_Lim_seq_plus.
Qed.

Lemma fun_Lim_seq_minus : forall H H', conv_fun_seq' a b Hab (fun n => f n{-}g n)
 (Cauchy_fun_seq_Lim _ _ _ _ _ Hf{-}Cauchy_fun_seq_Lim _ _ _ _ _ Hg) H H'.
intros.
set (F := Cauchy_fun_seq_Lim _ _ _ _ _ Hf) in *.
cut (Continuous_I Hab F). intro H0.
2: unfold F in |- *; apply Cauchy_cont_Lim.
cut (conv_fun_seq' _ _ _ _ _ contf H0).
2: unfold F in |- *; apply Cauchy_conv_fun_seq'; assumption.
intro Hf'.
set (G := Cauchy_fun_seq_Lim _ _ _ _ _ Hg) in *.
cut (Continuous_I Hab G). intro H1.
2: unfold G in |- *; apply Cauchy_cont_Lim.
cut (conv_fun_seq' _ _ _ _ _ contg H1).
2: unfold G in |- *; apply Cauchy_conv_fun_seq'; assumption.
intro Hg'.
apply fun_Lim_seq_minus' with contf contg H0 H1; auto.
Qed.

Lemma fun_Cauchy_prop_minus : forall H, Cauchy_fun_seq a b Hab (fun n => f n{-}g n) H.
intro.
cut
 (Continuous_I Hab
    (Cauchy_fun_seq_Lim _ _ _ _ _ Hf{-}Cauchy_fun_seq_Lim _ _ _ _ _ Hg));
 [ intro H0 | Contin ].
apply
 conv_Cauchy_fun_seq'
  with (Cauchy_fun_seq_Lim _ _ _ _ _ Hf{-}Cauchy_fun_seq_Lim _ _ _ _ _ Hg) H0.
apply fun_Lim_seq_minus.
Qed.

Lemma fun_Lim_seq_mult : forall H H', conv_fun_seq' a b Hab (fun n => f n{*}g n)
 (Cauchy_fun_seq_Lim _ _ _ _ _ Hf{*}Cauchy_fun_seq_Lim _ _ _ _ _ Hg) H H'.
intros.
set (F := Cauchy_fun_seq_Lim _ _ _ _ _ Hf) in *.
cut (Continuous_I Hab F); [ intro H0 | unfold F in |- *; Contin ].
cut (conv_fun_seq' _ _ _ _ _ contf H0).
2: unfold F in |- *; apply Cauchy_conv_fun_seq'; assumption.
intro convF.
set (G := Cauchy_fun_seq_Lim _ _ _ _ _ Hg) in *.
cut (Continuous_I Hab G); [ intro H1 | unfold G in |- *; Contin ].
cut (conv_fun_seq' _ _ _ _ _ contg H1).
2: unfold G in |- *; apply Cauchy_conv_fun_seq'; assumption.
intro convG.
cut (Continuous_I Hab F);
 [ intro HF' | unfold F, I in |- *; apply Cauchy_cont_Lim; assumption ].
cut (Continuous_I Hab G);
 [ intro HG' | unfold G, I in |- *; apply Cauchy_cont_Lim; assumption ].
apply fun_Lim_seq_mult' with contf contg H0 H1; auto.
Qed.

Lemma fun_Cauchy_prop_mult : forall H, Cauchy_fun_seq a b Hab (fun n => f n{*}g n) H.
intro H.
cut
 (Continuous_I Hab
    (Cauchy_fun_seq_Lim _ _ _ _ _ Hf{*}Cauchy_fun_seq_Lim _ _ _ _ _ Hg));
 [ intro H0 | Contin ].
apply
 conv_Cauchy_fun_seq'
  with (Cauchy_fun_seq_Lim _ _ _ _ _ Hf{*}Cauchy_fun_seq_Lim _ _ _ _ _ Hg) H0.
apply fun_Lim_seq_mult.
Qed.

End More_Algebraic_Properties.

Section Still_More_Algebraic_Properties.

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variable f : nat -> PartIR.
Hypothesis contf : forall n, Continuous_I Hab (f n).
Hypothesis Hf : Cauchy_fun_seq _ _ _ _ contf.

(**
As a corollary, we get the analogous property for the sequence of algebraic inverse functions.
*)

Lemma fun_Lim_seq_inv : forall H H', conv_fun_seq' a b Hab
 (fun n => {--} (f n)) {--} (Cauchy_fun_seq_Lim _ _ _ _ _ Hf) H H'.
intros.
cut (forall n : nat, Continuous_I Hab ( [-C-]Zero{-}f n)). intro H0.
unfold I in |- *;
 eapply conv_fun_seq'_wdl with (fun n : nat => [-C-]Zero{-}f n) H0 H'.
intro H1; FEQ; try (apply contin_imp_inc; apply contf).
cut
 (Continuous_I Hab
    (Cauchy_fun_seq_Lim _ _ _ _ _
       (fun_Cauchy_prop_const a b Hab [-C-]Zero
          (fun n : nat => Continuous_I_const _ _ _ _)) {-}
     Cauchy_fun_seq_Lim _ _ _ _ _ Hf)).
intros H1.
apply
 conv_fun_seq'_wdr
  with
    H0
    (Cauchy_fun_seq_Lim _ _ _ _ _
       (fun_Cauchy_prop_const a b Hab [-C-]Zero
          (fun n : nat => Continuous_I_const _ _ _ _)) {-}
     Cauchy_fun_seq_Lim _ _ _ _ _ Hf)
    H1.
apply eq_imp_Feq.
Included.
Included.
intros; simpl in |- *.
astepr
 (Zero[-]Lim (Build_CauchySeq _ _ (Cauchy_fun_real _ _ _ _ contf Hf x Hx'))).
apply cg_minus_wd.
eapply eq_transitive_unfolded.
2: apply eq_symmetric_unfolded; apply Lim_const.
apply Lim_wd'; intros; simpl in |- *; algebra.
apply Lim_wd'; intros; simpl in |- *; rational.
apply fun_Lim_seq_minus with (f := fun n : nat => [-C-]Zero:PartIR).
Contin.
Contin.
Qed.

Lemma fun_Cauchy_prop_inv : forall H, Cauchy_fun_seq a b Hab (fun n => {--} (f n)) H.
intro.
cut (Continuous_I Hab {--} (Cauchy_fun_seq_Lim _ _ _ _ _ Hf));
 [ intro H0 | Contin ].
apply conv_Cauchy_fun_seq' with ( {--} (Cauchy_fun_seq_Lim _ _ _ _ _ Hf)) H0.
apply fun_Lim_seq_inv.
Qed.

End Still_More_Algebraic_Properties.

Hint Resolve Continuous_I_Sum Continuous_I_Sumx Continuous_I_Sum0: continuous.
