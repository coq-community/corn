(* $Id$ *)

Require Export Intervals.
Require Export DiffTactics1.

Section Definitions.

(** printing Feq %\ensuremath{\approx}% #&asymp;# *)

(** *Equality of Partial Functions

** Definitions

In some contexts (namely when quantifying over partial functions) we need to refer explicitly to the subsetoid of elements satisfying a given predicate rather than to the predicate itself.  The following definition makes this possible.
*)

Definition subset (P : IR -> CProp) : CSetoid := Build_SubCSetoid IR P.

(**
The core of our work will revolve around the following fundamental notion: two functions are equal in a given domain (predicate) iff they coincide on every point of that domain#. #%\footnote{%Notice that, according to our definition of partial function, it is equivalent to prove the equality for every proof or for a specific proof.  Typically it is easier to consider a generic case%.}%.  This file is concerned with proving the main properties of this equality relation.
*)

Definition Feq (P : IR -> CProp) (F G : PartIR) :=
  included P (Dom F)
  and included P (Dom G)
      and (forall x : IR, P x -> forall Hx Hx', F x Hx[=]G x Hx').

(**
Notice that, because the quantification over the proofs is universal, we must require explicitly that the predicate be included in the domain of each function; otherwise the basic properties of equality (like, for example, transitivity) would fail to hold#. #%\footnote{%To see this it is enough to realize that the empty function would be equal to every other function in every domain.%}.%  The way to circumvent this would be to quantify existentially over the proofs; this, however, would have two major disadvantages: first, proofs of equality would become very cumbersome and clumsy; secondly (and most important), we often need to prove the inclusions from an equality hypothesis, and this definition allows us to do it in a very easy way.  Also, the pointwise equality is much nicer to use from this definition than in an existentially quantified one.
*)

End Definitions.

Section Equality_Results.

(** **Properties of Inclusion

We will now prove the main properties of the equality relation.

%\begin{convention}% Let [I,R:IR->CProp] and [F,G:PartIR], and denote by [P] and [Q], respectively, the domains of [F] and [G].
%\end{convention}%
*)

Variable I : IR -> CProp.
Variables F G : PartIR.

(* begin hide *)
Let P := Dom F.
Let Q := Dom G.
(* end hide *)

Variable R : IR -> CProp.

(**
We start with two lemmas which make it much easier to prove and use this definition:
*)

Lemma eq_imp_Feq :
 included I P ->
 included I Q ->
 (forall x : IR, I x -> forall Hx Hx', F x Hx[=]G x Hx') -> Feq I F G.
intros.
split.
assumption.
split; assumption.
Qed.

Lemma Feq_imp_eq :
 Feq I F G -> forall x : IR, I x -> forall Hx Hx', F x Hx[=]G x Hx'.
intros H x Hx1 Hx Hx'.
elim H; intros H0 H1.
elim H1; auto.
Qed.

(**
Next, we show how the inclusion relation works with the operations on partial functions (the first lemma applies, obviously, to total functions).
*)

Lemma included_IR : included I (fun x : IR => CTrue).
split.
Qed.

Lemma included_FPlus :
 included R P -> included R Q -> included R (Dom (F{+}G)).
intros; simpl in |- *; apply included_conj; assumption.
Qed.

Lemma included_FPlus' : included R (Dom (F{+}G)) -> included R P.
intro H; simpl in H; eapply included_conj_lft; apply H.
Qed.

Lemma included_FPlus'' : included R (Dom (F{+}G)) -> included R Q.
intro H; simpl in H; eapply included_conj_rht; apply H.
Qed.

Lemma included_FInv : included R P -> included R (Dom {--}F).
intro; simpl in |- *; assumption.
Qed.

Lemma included_FInv' : included R (Dom {--}F) -> included R P.
intro; simpl in |- *; assumption.
Qed.

Lemma included_FMinus :
 included R P -> included R Q -> included R (Dom (F{-}G)).
intros; simpl in |- *; apply included_conj; assumption.
Qed.

Lemma included_FMinus' : included R (Dom (F{-}G)) -> included R P.
intro H; simpl in H; eapply included_conj_lft; apply H.
Qed.

Lemma included_FMinus'' : included R (Dom (F{-}G)) -> included R Q.
intro H; simpl in H; eapply included_conj_rht; apply H.
Qed.

Lemma included_FMult :
 included R P -> included R Q -> included R (Dom (F{*}G)).
intros; simpl in |- *; apply included_conj; assumption.
Qed.

Lemma included_FMult' : included R (Dom (F{*}G)) -> included R P.
intro H; simpl in H; eapply included_conj_lft; apply H.
Qed.

Lemma included_FMult'' : included R (Dom (F{*}G)) -> included R Q.
intro H; simpl in H; eapply included_conj_rht; apply H.
Qed.

Lemma included_FRecip :
 included R Q ->
 (forall x : IR, R x -> forall Hx, G x Hx[#]Zero) -> included R (Dom {1/}G).
intros H H0.
simpl in |- *.
unfold extend in |- *.
split.
apply H; assumption.
intros; apply H0; assumption.
Qed.

Lemma included_FRecip' : included R (Dom {1/}G) -> included R Q.
intro H; simpl in H; eapply included_extend; apply H.
Qed.

Lemma included_FDiv :
 included R P ->
 included R Q ->
 (forall x : IR, R x -> forall Hx, G x Hx[#]Zero) -> included R (Dom (F{/}G)).
intros HP HQ Hx.
simpl in |- *.
apply included_conj.
assumption.
unfold extend in |- *.
split.
apply HQ; assumption.
intros; apply Hx; assumption.
Qed.

Lemma included_FDiv' : included R (Dom (F{/}G)) -> included R P.
intro H; simpl in H; eapply included_conj_lft; apply H.
Qed.

Lemma included_FDiv'' : included R (Dom (F{/}G)) -> included R Q.
intro H; simpl in H; eapply included_extend; eapply included_conj_rht;
 apply H.
Qed.

Lemma included_FComp :
 included R P ->
 (forall (x : IR) (Hx : R x) (Hx' : P x), Q (F x Hx')) ->
 included R (Dom (G[o]F)).
intros HP HQ.
simpl in |- *.
red in |- *; intros x Hx.
exists (HP x Hx).
apply HQ.
assumption.
Qed.

Lemma included_FComp' : included R (Dom (G[o]F)) -> included R P.
intro H; simpl in H; red in |- *; intros x Hx.
elim (H x Hx); auto.
Qed.

Lemma included_FScalMult :
 included R P -> forall c : IR, included R (Dom (c{**}F)).
intros; simpl in |- *; apply included_conj.
red in |- *; intros; auto.
assumption.
Qed.

Lemma included_FScalMult' :
 forall c : IR, included R (Dom (c{**}F)) -> included R P.
intros c H; simpl in H; eapply included_conj_rht; apply H.
Qed.

Lemma included_FNth :
 included R P -> forall n : nat, included R (Dom (F{^}n)).
auto.
Qed.

Lemma included_FNth' :
 forall n : nat, included R (Dom (F{^}n)) -> included R (Dom F).
auto.
Qed.

Lemma included_FMax :
 included R P -> included R Q -> included R (Dom (FMax F G)).
intros; simpl in |- *; apply included_conj; assumption.
Qed.

Lemma included_FMax' : included R (Dom (FMax F G)) -> included R P.
intro H; simpl in H; eapply included_conj_lft; apply H.
Qed.

Lemma included_FMax'' : included R (Dom (FMax F G)) -> included R Q.
intro H; simpl in H; eapply included_conj_rht; apply H.
Qed.

Lemma included_FMin :
 included R P -> included R Q -> included R (Dom (FMin F G)).
intros; simpl in |- *; apply included_conj; assumption.
Qed.

Lemma included_FMin' : included R (Dom (FMin F G)) -> included R P.
intro H; simpl in H; eapply included_conj_lft; apply H.
Qed.

Lemma included_FMin'' : included R (Dom (FMin F G)) -> included R Q.
intro H; simpl in H; eapply included_conj_rht; apply H.
Qed.

Lemma included_FAbs : included R P -> included R (Dom (FAbs F)).
intros; simpl in |- *; apply included_conj; assumption.
Qed.

Lemma included_FAbs' : included R (Dom (FAbs F)) -> included R P.
intro H; simpl in H; eapply included_conj_lft; apply H.
Qed.

End Equality_Results.

Section Some_More.

(**
Also, if two function coincide on a given subset then they coincide in any smaller subset.
*)

Lemma included_Feq : forall P Q F G, included P Q -> Feq Q F G -> Feq P F G.
intros P Q F G H H0.
elim H0; clear H0; intros H0 H1.
elim H1; clear H1; intros H1 H2.
apply eq_imp_Feq.
eapply included_trans.
apply H.
assumption.
eapply included_trans.
apply H.
assumption.
intros; apply H2.
apply H; assumption.
Qed.

End Some_More.

Hint Resolve included_IR included_refl included_refl' compact_map1
  compact_map2 compact_map3 included_compact included2_compact
  included3_compact included_FPlus included_FInv included_FMinus
  included_FMult included_FRecip included_FDiv included_FMax included_FMin
  included_FAbs included_FScalMult included_FNth included_FComp: included.

Hint Immediate included_trans included_FPlus' included_FPlus'' included_FInv'
  included_FMinus' included_FMinus'' included_FMult' included_FMult''
  included_FRecip' included_FMax' included_FMin' included_FAbs'
  included_FMax'' included_FMin'' included_FDiv' included_FDiv''
  included_FScalMult' included_FNth' included_FComp': included.

Section Away_from_Zero.

Section Definitions.

(** **Away from Zero

Before we prove our main results about the equality we have to do some work on division.  A function is said to be bounded away from zero in a set if there exists a positive lower bound for the set of absolute values of its image of that set.

%\begin{convention}% Let [I:IR->CProp], [F:PartIR] and denote by [P] the domain of [F].
%\end{convention}%
*)

Variable I : IR -> CProp.
Variable F : PartIR.
(* begin hide *)
Let P := Dom F.
(* end hide *)

Definition bnd_away_zero :=
  included I P
  and {c : IR | Zero[<]c |
      forall (y : IR) (Hy : I y) (Hy' : P y), c[<=]AbsIR (F y Hy')}.

(**
If [F] is bounded away from zero in [I] then [F] is necessarily apart from zero in [I]; also this means that [I] is included in the domain of [{1/}F].
*)

(* begin show *)
Hypothesis Hf : bnd_away_zero.
(* end show *)

Lemma bnd_imp_ap_zero :
 forall (x : IR) (Hx : I x) (Hx' : P x), F x Hx'[#]Zero.
intros.
apply AbsIR_cancel_ap_zero.
apply Greater_imp_ap.
elim Hf; intros.
inversion_clear b.
eapply less_leEq_trans; auto.
auto.
Qed.

Lemma bnd_imp_inc_recip : included I (Dom {1/}F).
intros x Hx.
elim Hf; intros H H0.
split.
apply (H x Hx).
intro.
apply (bnd_imp_ap_zero x Hx H1).
Qed.

Lemma bnd_imp_inc_div :
 forall G, included I (Dom G) -> included I (Dom (G{/}F)).
intros G HG x Hx.
split; auto.
elim Hf; intros H0 H1.
split.
apply (H0 x Hx).
intro.
apply (bnd_imp_ap_zero x Hx H).
Qed.

End Definitions.

(**
Boundedness away from zero is preserved through restriction of the set.

%\begin{convention}% Let [F] be a partial function and [P,Q] be predicates.
%\end{convention}%
*)

Variable F : PartIR.
Variables P Q : IR -> CProp.

Lemma included_imp_bnd :
 included Q P -> bnd_away_zero P F -> bnd_away_zero Q F.
intros H H0.
elim H0; clear H0; intros H1 H2; split.
apply included_trans with P; auto.
elim H2; intros c Hc Hc'.
exists c; auto.
Qed.

Lemma FRestr_bnd :
 forall HP H,
 included Q P ->
 bnd_away_zero Q F -> bnd_away_zero Q (Frestr (F:=F) (P:=P) HP H).
intros HP H H0 H1.
elim H1; clear H1; intros H2 H3; split.
auto.
elim H3; intro c; intros.
exists c; simpl in |- *; auto.
Qed.

(**
A function is said to be bounded away from zero everywhere if it is bounded away from zero in every compact subinterval of its domain; a similar definition is made for arbitrary sets, which will be necessary for future work.
*)

Definition bnd_away_zero_everywhere (G : PartIR) :=
  forall (a b : IR) Hab,
  included (compact a b Hab) (Dom G) -> bnd_away_zero (compact a b Hab) G.

Definition bnd_away_zero_in_P :=
  forall (a b : IR) Hab,
  included (compact a b Hab) P -> bnd_away_zero (compact a b Hab) F.

(**
An immediate consequence:
*)

Lemma bnd_in_P_imp_ap_zero :
 pred_well_def _ P ->
 bnd_away_zero_in_P -> forall x : IR, P x -> forall Hx, F x Hx[#]Zero.
intros H H0 x H1 Hx.
apply bnd_imp_ap_zero with (Compact (leEq_reflexive _ x)).
apply H0.
red in |- *; intros x0 H2.
cut (x[=]x0); intros.
apply H with x; auto.
inversion_clear H2; apply leEq_imp_eq; auto.
split; apply leEq_reflexive.
Qed.

Lemma FRestr_bnd' :
 forall HP H,
 bnd_away_zero_everywhere F ->
 bnd_away_zero_everywhere (Frestr (F:=F) (P:=P) HP H).
intros HP H H0 a b Hab H1.
elim (H0 a b Hab); intros.
split.
auto.
elim b0; intro c; intros.
exists c; simpl in |- *; auto.
apply included_trans with P; simpl in H1; auto.
Qed.

End Away_from_Zero.

Hint Resolve bnd_imp_inc_recip bnd_imp_inc_div: included.
Hint Immediate bnd_in_P_imp_ap_zero: included.

Ltac FEQ :=
  apply eq_imp_Feq;
   [ Included | Included | intros; try (simpl in |- *; rational) ].

Section More_on_Equality.

(** **Properties of Equality

We are now finally able to prove the main properties of the equality relation.  We begin by showing it to be an equivalence relation.

%\begin{convention}% Let [I] be a predicate and [F,F',G,G',H] be partial functions.
%\end{convention}%
*)

Variable I : IR -> CProp.

Section Feq_Equivalence.

Variables F G H : PartIR.

Lemma Feq_reflexive : included I (Dom F) -> Feq I F F.
intro; FEQ.
Qed.

Lemma Feq_symmetric : Feq I F G -> Feq I G F.
intro H0.
elim H0; intros H' H1.
elim H1; intros incF incG.
FEQ; Algebra.
Qed.

Lemma Feq_transitive : Feq I F G -> Feq I G H -> Feq I F H.
intro H0.
elim H0; intros incF H'.
elim H'; intros incG H1.
clear H0 H'.
intro H0.
elim H0; intros incG' H'.
elim H'; intros incH H2.
clear H0 H'.
FEQ.
Step_final (G x (incG x X)).
Qed.

End Feq_Equivalence.

Section Operations.

(**
Also it is preserved through application of functional constructors and restriction.
*)

Variables F F' G G' : PartIR.

Lemma Feq_plus : Feq I F F' -> Feq I G G' -> Feq I (F{+}G) (F'{+}G').
intros H0 H1.
elim H0; intros incF H0'.
elim H0'; clear H0 H0'; intros incG H2.
elim H1; intros incF' H1'.
elim H1'; clear H1 H1'; intros incG' H1.
FEQ; simpl in |- *; Algebra.
Qed.

Lemma Feq_inv : Feq I F F' -> Feq I {--}F {--}F'.
intro H0.
elim H0; intros incF H0'.
elim H0'; clear H0 H0'; intros incF' H1.
FEQ; simpl in |- *; Algebra.
Qed.

Lemma Feq_minus : Feq I F F' -> Feq I G G' -> Feq I (F{-}G) (F'{-}G').
intros H0 H1.
elim H0; intros incF H0'.
elim H0'; clear H0 H0'; intros incG H2.
elim H1; intros incF' H1'.
elim H1'; clear H1 H1'; intros incG' H0.
FEQ; simpl in |- *; Algebra.
Qed.

Lemma Feq_mult : Feq I F F' -> Feq I G G' -> Feq I (F{*}G) (F'{*}G').
intros H0 H1.
elim H0; intros incF H0'.
elim H0'; clear H0 H0'; intros incG H2.
elim H1; intros incF' H1'.
elim H1'; clear H1 H1'; intros incG' H0.
FEQ; simpl in |- *; Algebra.
Qed.

Lemma Feq_nth : forall n : nat, Feq I F F' -> Feq I (F{^}n) (F'{^}n).
intros n H0.
elim H0; intros incF H0'.
elim H0'; clear H0 H0'; intros incF' H1.
FEQ.
AStepl (F x Hx[^]n); Step_final (Part F' x Hx'[^]n).
Qed.

Lemma Feq_recip : bnd_away_zero I F -> Feq I F F' -> Feq I {1/}F {1/}F'.
intros Hbnd H0.
elim H0; intros incF H0'.
elim H0'; clear H0 H0'; intros incF' H1.
FEQ.
apply included_FRecip.
auto.
intros x H Hx; apply ap_well_def_lft_unfolded with (F x (incF x H)).
apply bnd_imp_ap_zero with I; assumption.
auto.
simpl in |- *; Algebra.
Qed.

Lemma Feq_recip' : bnd_away_zero I F -> Feq I F' F -> Feq I {1/}F' {1/}F.
intros.
apply Feq_symmetric; apply Feq_recip.
assumption.
apply Feq_symmetric; assumption.
Qed.

Lemma Feq_div :
 bnd_away_zero I G -> Feq I F F' -> Feq I G G' -> Feq I (F{/}G) (F'{/}G').
intros Hbnd H0 H1.
elim H0; intros incF H0'.
elim H0'; clear H0 H0'; intros incF' H2.
elim H1; intros incG H1'.
elim H1'; clear H1 H1'; intros incG' H0.
FEQ.
apply included_FDiv; auto.
intros x H Hx; apply ap_well_def_lft_unfolded with (G x (incG x H)).
apply bnd_imp_ap_zero with I; assumption.
auto.
simpl in |- *; Algebra.
Qed.

Lemma Feq_div' :
 bnd_away_zero I G -> Feq I F' F -> Feq I G' G -> Feq I (F'{/}G') (F{/}G).
intros.
apply Feq_symmetric; apply Feq_div.
assumption.
apply Feq_symmetric; assumption.
apply Feq_symmetric; assumption.
Qed.

(**
Notice that in the case of division we only need to require boundedness away from zero for one of the functions (as they are equal); thus the two last lemmas are stated in two different ways, as according to the context one or the other condition may be easier to prove.

Finally, the restriction of a function is well defined.
*)

Lemma FRestr_wd : forall Iwd Hinc, Feq I F (Frestr (F:=F) (P:=I) Iwd Hinc).
intros.
FEQ.
Qed.

End Operations.

End More_on_Equality.

Section Nth_Power.

(** **Nth Power

We finish this group of lemmas with characterization results for the power function (similar to those already proved for arbitrary rings).  The characterization is done at first pointwise and later using the equality relation.

%\begin{convention}% Let [F] be a partial function with domain [P] and [Q] be a predicate on the real numbers assumed to be included in [P].
%\end{convention}%
*)

Variable F : PartIR.
(* begin hide *)
Let P := Dom F.
(* end hide *)

Variable Q : IR -> CProp.
Hypothesis H : included Q (fun x : IR => CTrue).
Hypothesis Hf : included Q (Dom F).

Lemma FNth_zero :
 forall x : IR, Q x -> forall Hx Hx', [-C-]One x Hx[=](F{^}0) x Hx'.
intros.
Algebra.
Qed.

Variable n : nat.
Hypothesis H' : included Q (Dom (F{*}F{^}n)).

Lemma FNth_mult :
 forall x : IR, Q x -> forall Hx Hx', (F{*}F{^}n) x Hx[=](F{^}S n) x Hx'.
intros.
simpl in |- *.
eapply eq_transitive_unfolded.
2: apply mult_commutes.
apply mult_wd.
rational.
change (F x (ProjIR2 Hx)[^]n[=]F x Hx'[^]n) in |- *.
apply nexp_wd; rational.
Qed.

End Nth_Power.

Section Strong_Nth_Power.

(**
%\begin{convention}% Let [a,b] be real numbers such that [I]$=[a,b]$#=[a,b]# is included in the domain of [F].
%\end{convention}%
*)

Variables a b : IR.
Hypothesis Hab : a[<=]b.
(* begin hide *)
Let I := compact a b Hab.
(* end hide *)

Variable F : PartIR.
Hypothesis incF : included I (Dom F).

Lemma FNth_zero' : Feq I [-C-]One (F{^}0).
FEQ.
Qed.

Lemma FNth_mult' : forall n : nat, Feq I (F{*}F{^}n) (F{^}S n).
intro; FEQ.
simpl in |- *.
eapply eq_transitive_unfolded.
2: apply mult_commutes.
apply bin_op_wd_unfolded.
rational.
change (F x (ProjIR2 Hx)[^]n[=]F x Hx'[^]n) in |- *.
apply nexp_wd; rational.
Qed.

End Strong_Nth_Power.

(**
The image of a set is extensional.
*)

Lemma fun_image_wd :
 forall (F G : PartIR) (P : IR -> CProp),
 Feq P F G -> forall x : IR, fun_image F P x -> fun_image G P x.
intros F G P H x H0.
elim H; clear H; intros H H1.
elim H1; clear H1; intros H2 H3.
elim H0; intros y Hy.
exists y.
elim Hy; intros H4 H1.
elim H1; clear Hy H1; intros H5 H6.
split; auto.
split; auto.
intro; Step_final (F y H5).
Qed.
