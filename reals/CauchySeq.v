(* $Id: CauchySeq.v,v 1.8 2004/04/23 10:01:04 lcf Exp $ *)

(** printing IR %\ensuremath{\mathbb R}% *)
(** printing PartIR %\ensuremath{\mathbb R\!\not\rightarrow\!\mathbb R}% *)
(** printing ZeroR %\ensuremath{\mathbf0}% #0# *)
(** printing OneR %\ensuremath{\mathbf1}% #1# *)
(** printing AbsIR %\ensuremath{|\cdot|_{\mathbb R}}% *)

Require Export CReals.

(** *Real Number Structures
%\begin{convention}% Let [IR] be a structure for real numbers.
%\end{convention}%
*)

(*
Require Export R_CReals.
Definition IR : CReals := Concrete_R.
Opaque IR.
*)

Axiom IR : CReals.

Notation PartIR := (PartFunct IR).
Notation ProjIR1 := (prj1 IR _ _ _).
Notation ProjIR2 := (prj2 IR _ _ _).

Load "Transparent_algebra".

(* begin hide *)
Notation ZeroR := (Zero:IR).
Notation OneR := (One:IR).
(* end hide *)

Section CReals_axioms.
(** ** [CReals] axioms *)

Lemma CReals_is_CReals : is_CReals IR (Lim (IR:=IR)).
unfold Lim in |- *.
elim IR; intros.
exact crl_proof.
Qed.

(** First properties which follow trivially from the axioms.  *)

Lemma Lim_Cauchy : forall s : CauchySeq IR, SeqLimit s (Lim s).
elim CReals_is_CReals; auto.
Qed.

Lemma Archimedes : forall x : IR, {n : nat | x [<=] nring n}.
elim CReals_is_CReals; auto.
Qed.

Lemma Archimedes' : forall x : IR, {n : nat | x [<] nring n}.
intro x.
elim (Archimedes (x[+]One)); intros n Hn.
exists n.
apply less_leEq_trans with (x[+]One); auto.
apply less_plusOne.
Qed.

(** A stronger version, which often comes in useful.  *)

Lemma str_Archimedes : forall x : IR,
 Zero [<=] x -> {n : nat | x [<=] nring n /\ (2 <= n -> nring n[-]Two [<=] x)}.
intros.
elim (Archimedes x); intros n Hn.
induction  n as [| n Hrecn].
exists 0; split; auto.
intro; elimtype False; omega.

clear Hrecn.
induction  n as [| n Hrecn].
exists 1.
split; intros; [ assumption | eapply leEq_transitive ].
2: apply H.
simpl in |- *.
rstepl ([--]OneR); astepr ([--]ZeroR); apply less_leEq; apply inv_resp_less;
 apply pos_one.
cut (nring (R:=IR) n [<] nring (S n)).
intros H0.
cut (nring n [<] x or x [<] nring (S n)).
intros H1.
elim H1; intros.
exists (S (S n)).
split.
assumption.
intros.
simpl in |- *; rstepl (nring (R:=IR) n); apply less_leEq; assumption.
apply Hrecn; apply less_leEq; assumption.
apply less_cotransitive_unfolded; assumption.
simpl in |- *; apply less_plusOne.
Qed.

Definition CauchySeqR := CauchySeq IR.

End CReals_axioms.

Section Cauchy_Defs.

(** ** Cauchy sequences
*** Alternative definitions
This section gives several definitions of Cauchy sequences. There
are no lemmas in this section.

The current definition of Cauchy ([Cauchy_prop]) is:

%\[\forall \epsilon>0. \exists N. \forall m\geq N. |seq_m - seq_N|\leq\varepsilon\]%
#for all e&gt;0 there exists N such that for all m&ge; N |seqm-seqN|&le; e#

Variant 1 of Cauchy ([Cauchy_prop1]) is:

%\[\forall k. \exists N. \forall m \geq N. |seq_m - seq_N|\leq1/(k+1)\]%
#for all k there exists N such that for all m &ge; N |seqm-seqN| &le; 1/(k+1)#

In all of the following variants the limit occurs in the definition.
Therefore it is useful to define an auxiliary predicate
[Cauchy_Lim_prop?], in terms of which [Cauchy_prop?] is defined.

Variant 2 of Cauchy ([Cauchy_prop2]) is [exists y, (Cauchy_Lim_prop2 seq y)]
where
[[
Cauchy_Lim_prop2 seq y := forall eps [>] Zero, exists N, forall m >= N, (AbsIR seq m - y) [<=] eps
]]

Note that [Cauchy_Lim_prop2] equals [seqLimit].

Variant 3 of Cauchy ([Cauchy_prop3]) reads [exists y, (Cauchy_Lim_prop3 seq y)]
where
[[
Cauchy_Lim_prop3 seq y := forall k, exists N, forall m >= N, (AbsIR seq m - y) [<=] One[/] (k[+]1)
]]

The following variant is more restricted.

Variant 4 of Cauchy ([Cauchy_prop4]): [exists y, (Cauchy_Lim_prop4 seq y)]
where
[[
Cauchy_Lim_prop4 seq y := forall k, (AbsIR seq m - y) [<=] One[/] (k[+]1)
]]

So
[[
Cauchy_prop4 -> Cauchy_prop3 Iff Cauchy_prop2 Iff Cauchy_prop1 Iff Cauchy_prop
]]
Note: we don't know which formulations are useful.

The inequalities are stated with [[<=]] rather than with [<] for the
following reason: both formulations are equivalent, as is well known;
and [[<=]] being a negative statement, this makes proofs
sometimes easier and program extraction much more efficient.
*)

Definition Cauchy_prop1 (seq : nat -> IR) := forall k,
 {N : nat | forall m, N <= m -> AbsSmall (one_div_succ k) (seq m[-]seq N)}.

Definition Cauchy_Lim_prop2 (seq : nat -> IR) (y : IR) := forall eps,
  Zero [<] eps -> {N : nat | forall m, N <= m -> AbsSmall eps (seq m[-]y)}.

Definition Cauchy_prop2 (seq : nat -> IR) := {y : IR | Cauchy_Lim_prop2 seq y}.

Definition Cauchy_Lim_prop3 (seq : nat -> IR) (y : IR) := forall k,
  {N : nat | forall m, N <= m -> AbsSmall (one_div_succ k) (seq m[-]y)}.

Definition Cauchy_prop3 (seq : nat -> IR) := {y : IR | Cauchy_Lim_prop3 seq y}.

Definition Cauchy_Lim_prop4 (seq : nat -> IR) (y : IR) := forall m,
 AbsSmall (one_div_succ m) (seq m[-]y).

Definition Cauchy_prop4 (seq : nat -> IR) := {y : IR | Cauchy_Lim_prop4 seq y}.

End Cauchy_Defs.

Section Inequalities.
(** *** Inequalities of Limits

The next lemma is equal to lemma [Lim_Cauchy].  *)

Lemma Cauchy_complete : forall seq : CauchySeq IR, Cauchy_Lim_prop2 seq (Lim seq).
exact Lim_Cauchy.
Qed.

Lemma less_Lim_so_less_seq : forall (seq : CauchySeq IR) y,
 y [<] Lim seq -> {N : nat | forall m, N <= m -> y [<] seq m}.
intros seq y H.
elim (Cauchy_complete seq ((Lim seq[-]y) [/]TwoNZ)).
intro N.
intros H0.
split with N.
intros m H1.
generalize (H0 _ H1). intro H2.
unfold AbsSmall in H2.
elim H2.
intros.

apply plus_cancel_less with ([--] (Lim seq)).
rstepl ([--] (Lim seq[-]y)).
rstepr (seq m[-]Lim seq).
eapply less_leEq_trans.
2: apply H3.
apply inv_resp_less; apply pos_div_two'.
apply shift_less_minus; astepl y; auto.

apply pos_div_two.
apply shift_less_minus; astepl y; auto.
Qed.

Lemma Lim_less_so_seq_less : forall (seq : CauchySeq IR) y,
 Lim seq [<] y -> {N : nat | forall m, N <= m -> seq m [<] y}.
intros.
elim (Cauchy_complete seq ((y[-]Lim seq) [/]TwoNZ)).
intro N.
intros H0.
split with N.
intros m H1.
generalize (H0 _ H1); intro H2.
unfold AbsSmall in H2.
elim H2.
intros H3 H4.

apply plus_cancel_less with ([--] (Lim seq)).
eapply leEq_less_trans.
apply H4.
apply pos_div_two'.
apply shift_less_plus; rstepl (Lim seq); auto.

apply pos_div_two.
apply shift_less_minus; astepl (Lim seq); auto.
Qed.

Lemma Lim_less_Lim_so_seq_less_seq : forall seq1 seq2 : CauchySeq IR,
 Lim seq1 [<] Lim seq2 -> {N : nat | forall m, N <= m -> seq1 m [<] seq2 m}.
intros.
set (Av := (Lim seq1[+]Lim seq2) [/]TwoNZ) in |- *.
cut (Lim seq1 [<] Av); try intro H0.
cut (Av [<] Lim seq2); try intro H1.
generalize (Lim_less_so_seq_less _ _ H0); intro H2.
generalize (less_Lim_so_less_seq _ _ H1); intro H3.
elim H2; intro N1; intro H4.
elim H3; intro N2; intro H5.
exists (max N1 N2); intros.
apply less_leEq_trans with Av.
apply H4.
apply le_trans with (max N1 N2).
apply le_max_l.
assumption.
apply less_leEq.
apply H5.
apply le_trans with (max N1 N2).
apply le_max_r.
assumption.
unfold Av in |- *.
apply Average_less_Greatest.
assumption.
unfold Av in |- *.
apply Smallest_less_Average.
assumption.
Qed.

(** The next lemma follows from [less_Lim_so_less_seq] with [y := (y[+] (Lim seq)) [/]TwoNZ].  *)

Lemma less_Lim_so : forall (seq : CauchySeq IR) y, y [<] Lim seq ->
 {eps : IR | Zero [<] eps | {N : nat | forall m, N <= m -> y[+]eps [<] seq m}}.
intros.
elim (less_Lim_so_less_seq seq ((y[+]Lim seq) [/]TwoNZ)).
intros x H0.
exists ((Lim seq[-]y) [/]TwoNZ).
apply pos_div_two.
apply shift_zero_less_minus.
assumption.
exists x.
intros.
rstepl ((y[+]Lim seq) [/]TwoNZ).
apply H0.
assumption.
apply Average_less_Greatest.
assumption.
Qed.

Lemma Lim_less_so : forall (seq : CauchySeq IR) y, Lim seq [<] y ->
 {eps : IR | Zero [<] eps | {N : nat | forall m, N <= m -> seq m[+]eps [<] y}}.
intros.
elim (Lim_less_so_seq_less seq ((Lim seq[+]y) [/]TwoNZ)). 
intros x H0.
exists ((y[-]Lim seq) [/]TwoNZ).
apply pos_div_two.
apply shift_zero_less_minus.
assumption.
exists x.
intros.
apply shift_plus_less.
rstepr ((Lim seq[+]y) [/]TwoNZ).
apply H0.
assumption.
apply Smallest_less_Average.
assumption.
Qed.

Lemma leEq_seq_so_leEq_Lim : forall (seq : CauchySeqR) y, (forall i, y [<=] seq i) -> y [<=] Lim seq.
intros.
unfold leEq in |- *.
intro H0.
generalize (Lim_less_so_seq_less _ _ H0); intro H1.
elim H1; intros N H2.
apply (H N).
apply H2.
auto with arith.
Qed.

Lemma str_leEq_seq_so_leEq_Lim : forall (seq : CauchySeq IR) y,
 (exists N : nat, (forall i, N <= i -> y [<=] seq i)) -> y [<=] Lim seq.
intros.
red in |- *; intro H0.
generalize (Lim_less_so_seq_less _ _ H0).
elim H; intros N HN.
intro H1.
elim H1; intros M HM.
cut (y [<] y).
apply less_irreflexive_unfolded.
apply leEq_less_trans with (seq (max N M)).
apply HN; apply le_max_l.
apply HM; apply le_max_r.
Qed.

Lemma Lim_leEq_Lim : forall seq1 seq2 : CauchySeqR,
 (forall i, seq1 i [<=] seq2 i) -> Lim seq1 [<=] Lim seq2.
intros.
unfold leEq in |- *.
intro H0.
generalize (Lim_less_Lim_so_seq_less_seq _ _ H0); intro H1.
elim H1; intros N H2.
apply (H N).
apply H2.
auto with arith.
Qed.

Lemma seq_leEq_so_Lim_leEq : forall (seq : CauchySeqR) y, (forall i, seq i [<=] y) -> Lim seq [<=] y.
intros.
unfold leEq in |- *.
intro H0.
generalize (less_Lim_so_less_seq _ _ H0); intro H1.
elim H1; intros N H2.
apply (H N).
apply H2.
auto with arith.
Qed.

Lemma str_seq_leEq_so_Lim_leEq : forall (seq : CauchySeq IR) y,
 (exists N : nat, (forall i, N <= i -> seq i [<=] y)) -> Lim seq [<=] y.
intros.
red in |- *; intro H0.
generalize (less_Lim_so_less_seq _ _ H0).
elim H; intros N HN.
intro H1.
elim H1; intros M HM.
cut (y [<] y).
apply less_irreflexive_unfolded.
apply less_leEq_trans with (seq (max N M)).
apply HM; apply le_max_r.
apply HN; apply le_max_l.
Qed.

Lemma Limits_unique : forall (seq : CauchySeq IR) y,
 Cauchy_Lim_prop2 seq y -> y [=] Lim seq.
intros seq y H.
apply not_ap_imp_eq.
unfold not in |- *; intro H0.
generalize (ap_imp_less _ _ _ H0); intro H1.
elim H1; intro H2.
elim (less_Lim_so _ _ H2); intro eps; intros H4 H5.
elim H5; intro N; intro H6.
unfold Cauchy_Lim_prop2 in H.
elim (H _ H4); intro N'; intro H7.
generalize (le_max_l N N'); intro H8.
generalize (le_max_r N N'); intro H9.
generalize (H6 _ H8); intro H10.
generalize (H7 _ H9); intro H11.
elim H11; intros H12 H13.
apply less_irreflexive_unfolded with (x := y[+]eps).
eapply less_leEq_trans.
apply H10.
apply plus_cancel_leEq_rht with ([--]y).
rstepr eps.
exact H13.

(* Second case similar to first case *)
elim (Lim_less_so _ _ H2); intro eps; intros H4 H5.
elim H5; intro N; intros H6.
unfold Cauchy_Lim_prop2 in H.
elim (H _ H4); intro N'; intros H7.
generalize (le_max_l N N'); intro H8.
generalize (le_max_r N N'); intro H9.
generalize (H6 _ H8); intro H10.
generalize (H7 _ H9); intro H11.
elim H11; intros H12 H13.
apply less_irreflexive_unfolded with (x := y).
eapply leEq_less_trans.
2: apply H10.
apply plus_cancel_leEq_rht with ([--]y[-]eps).
rstepl ([--]eps).
rstepr (seq (max N N') [-]y).
assumption.
Qed.

Lemma Lim_wd : forall (seq : nat -> IR) x y,
 x [=] y -> Cauchy_Lim_prop2 seq x -> Cauchy_Lim_prop2 seq y.
intros seq x y H H0.
red in |- *; red in H0.
intros eps H1.
elim (H0 _ H1).
intros N HN.
exists N.
intros.
astepr (seq m[-]x).
apply HN; assumption.
Qed.

Lemma Lim_strext : forall seq1 seq2 : CauchySeq IR,
 Lim seq1 [#] Lim seq2 -> {n : nat | seq1 n [#] seq2 n}.
intros seq1 seq2 H.
cut ({n : nat | seq1 n [<] seq2 n} or {n : nat | seq2 n [<] seq1 n}).
intro H0; inversion_clear H0; rename X into H1; elim H1; intros n Hn.
exists n; apply less_imp_ap; assumption.
exists n; apply Greater_imp_ap; assumption.
cut (Lim seq1 [<] Lim seq2 or Lim seq2 [<] Lim seq1). intros H0.
2: apply ap_imp_less; assumption.
inversion_clear H0; [ left | right ].
cut {n : nat | forall m : nat, n <= m -> seq1 m [<] seq2 m}.
2: apply Lim_less_Lim_so_seq_less_seq; assumption.
intro H0; elim H0; intros N HN.
exists N; apply HN; auto with arith.
cut {n : nat | forall m : nat, n <= m -> seq2 m [<] seq1 m}.
2: apply Lim_less_Lim_so_seq_less_seq; assumption.
intro H0; elim H0; intros N HN.
exists N; apply HN; auto with arith.
Qed.

Lemma Lim_ap_imp_seq_ap : forall seq1 seq2 : CauchySeq IR,
 Lim seq1 [#] Lim seq2 -> {N : nat | forall m, N <= m -> seq1 m [#] seq2 m}.
intros seq1 seq2 H.
elim (ap_imp_less _ _ _ H); intro.
elim (Lim_less_Lim_so_seq_less_seq _ _ a); intros N HN.
exists N; intros.
apply less_imp_ap; apply HN; assumption.
elim (Lim_less_Lim_so_seq_less_seq _ _ b); intros N HN.
exists N; intros.
apply Greater_imp_ap; apply HN; assumption.
Qed.

Lemma Lim_ap_imp_seq_ap' : forall seq1 seq2 : CauchySeq IR,
 Lim seq1 [#] Lim seq2 -> {N : nat | seq1 N [#] seq2 N}.
intros seq1 seq2 H.
elim (Lim_ap_imp_seq_ap _ _ H); intros N HN.
exists N; apply HN.
apply le_n.
Qed.

End Inequalities.

Section Equiv_Cauchy.

(** *** Equivalence of formulations of Cauchy *)

Lemma Cauchy_prop1_prop : forall seq, Cauchy_prop1 seq -> Cauchy_prop seq.
intros seq H.
unfold Cauchy_prop1 in H.
unfold Cauchy_prop in |- *.
intros.
cut (e [#] Zero).
intro eNZ.
elim (Archimedes (One[/] e[//]eNZ)).
intros x H1.
elim (H x).
intros x0 H2.
split with x0.
intros m H3.
generalize (H2 _ H3).
intro.
apply AbsSmall_leEq_trans with (one_div_succ (R:=IR) x).

unfold one_div_succ in |- *.
unfold Snring in |- *.
apply shift_div_leEq'.
apply nring_pos.
auto with arith.

astepr (e[*]nring (S x)).
apply leEq_transitive with (e[*]nring x).
apply shift_leEq_mult' with eNZ.
assumption.

assumption.

apply less_leEq.
apply mult_resp_less_lft.
apply nring_less.
auto.

assumption.

assumption.
apply pos_ap_zero.
assumption.
Qed.

Lemma Cauchy_prop2_prop : forall seq, Cauchy_prop2 seq -> Cauchy_prop seq.
intros seq H.
unfold Cauchy_prop in |- *.
intros e H0.
unfold Cauchy_prop2 in H.
elim H.
intro y; intros H1.
unfold Cauchy_Lim_prop2 in H1.
elim (H1 (e [/]TwoNZ)).
intro N.
intros H2.
exists N.
intros m H3.
generalize (H2 _ H3); intro H4.
generalize (le_n N); intro H5.
generalize (H2 _ H5); intro H6.
generalize (AbsSmall_minus _ _ _ _ H6); intro H7.
generalize (AbsSmall_plus _ _ _ _ _ H4 H7); intro H8.
rstepl (e [/]TwoNZ[+]e [/]TwoNZ).
rstepr (seq m[-]y[+] (y[-]seq N)).
assumption.
apply pos_div_two.
assumption.
Qed.

Lemma Cauchy_Lim_prop3_prop2 : forall seq y,
 Cauchy_Lim_prop3 seq y -> Cauchy_Lim_prop2 seq y.
intros seq y H.
unfold Cauchy_Lim_prop2 in |- *.
intros eps H0.
unfold Cauchy_Lim_prop3 in H.
generalize (pos_ap_zero _ _ H0); intro Heps.
elim (Archimedes (One[/] eps[//]Heps)).
intro K; intros H1.
elim (H K).
intro N; intros H2.
exists N.
intros m H3.
generalize (H2 _ H3); intro H4.
apply AbsSmall_leEq_trans with (one_div_succ (R:=IR) K); try assumption.
unfold one_div_succ in |- *.
unfold Snring in |- *.
apply shift_div_leEq'.
apply nring_pos.
auto with arith.
apply leEq_transitive with (eps[*]nring K).
apply shift_leEq_mult' with Heps; assumption.

astepl (nring K[*]eps).
apply less_leEq.
apply mult_resp_less; try assumption.
apply nring_less.
auto with arith.
Qed.

Lemma Cauchy_prop3_prop2 : forall seq, Cauchy_prop3 seq -> Cauchy_prop2 seq.
unfold Cauchy_prop2 in |- *.
unfold Cauchy_prop3 in |- *.
intros seq H.
elim H; intros x H0.
exists x.
apply Cauchy_Lim_prop3_prop2.
assumption.
Qed.

Lemma Cauchy_prop3_prop : forall seq, Cauchy_prop3 seq -> Cauchy_prop seq.
intros.
apply Cauchy_prop2_prop.
apply Cauchy_prop3_prop2.
assumption.
Qed.

Definition Build_CauchySeq1 : forall seq, Cauchy_prop1 seq -> CauchySeqR.
intros.
unfold CauchySeqR in |- *.
apply Build_CauchySeq with seq.
apply Cauchy_prop1_prop.
assumption.
Defined.

Lemma Cauchy_Lim_prop4_prop3 : forall seq y,
 Cauchy_Lim_prop4 seq y -> Cauchy_Lim_prop3 seq y.
intros.
unfold Cauchy_Lim_prop4 in H.
unfold Cauchy_Lim_prop3 in |- *.
intros.
exists k.
intros.
apply AbsSmall_leEq_trans with (one_div_succ (R:=IR) m).
2: apply H.
apply one_div_succ_resp_leEq.
assumption.
Qed.

Lemma Cauchy_Lim_prop4_prop2 : forall seq y,
 Cauchy_Lim_prop4 seq y -> Cauchy_Lim_prop2 seq y.
intros.
apply Cauchy_Lim_prop3_prop2.
apply Cauchy_Lim_prop4_prop3.
assumption.
Qed.

Lemma Cauchy_prop4_prop3 : forall seq, Cauchy_prop4 seq -> Cauchy_prop3 seq.
unfold Cauchy_prop4 in |- *.
unfold Cauchy_prop3 in |- *.
intros seq H.
elim H; intros.
exists x.
apply Cauchy_Lim_prop4_prop3.
assumption.
Qed.

Lemma Cauchy_prop4_prop : forall seq, Cauchy_prop4 seq -> Cauchy_prop seq.
intros.
apply Cauchy_prop3_prop.
apply Cauchy_prop4_prop3.
assumption.
Qed.

Definition Build_CauchySeq4 : forall seq, Cauchy_prop4 seq -> CauchySeqR.
intros.
unfold CauchySeqR in |- *.
apply Build_CauchySeq with seq.
apply Cauchy_prop4_prop.
assumption.
Defined.

Definition Build_CauchySeq4_y : forall seq y, Cauchy_Lim_prop4 seq y -> CauchySeqR.
intros.
apply Build_CauchySeq4 with seq.
unfold Cauchy_prop4 in |- *.
exists y.
assumption.
Defined.

Lemma Lim_CauchySeq4 : forall seq y H, Lim (Build_CauchySeq4_y seq y H) [=] y.
intros.
apply eq_symmetric_unfolded.
apply Limits_unique.
apply Cauchy_Lim_prop3_prop2.
apply Cauchy_Lim_prop4_prop3.
unfold Build_CauchySeq4_y in |- *.
unfold Build_CauchySeq4 in |- *.
unfold CS_seq in |- *.
assumption.
Qed.

Definition Build_CauchySeq2 : forall seq, Cauchy_prop2 seq -> CauchySeqR.
intros.
unfold CauchySeqR in |- *.
apply Build_CauchySeq with seq.
apply Cauchy_prop2_prop.
assumption.
Defined.

Definition Build_CauchySeq2_y : forall seq y, Cauchy_Lim_prop2 seq y -> CauchySeqR.
intros.
apply Build_CauchySeq2 with seq.
unfold Cauchy_prop2 in |- *.
exists y.
assumption.
Defined.

Lemma Lim_CauchySeq2 : forall seq y H, Lim (Build_CauchySeq2_y seq y H) [=] y.
intros.
apply eq_symmetric_unfolded.
apply Limits_unique.
unfold Build_CauchySeq2_y in |- *.
unfold Build_CauchySeq2 in |- *.
unfold CS_seq in |- *.
assumption.
Qed.

(** Well definedness. *)

Lemma Cauchy_prop_wd : forall seq1 seq2 : nat -> IR,
 Cauchy_prop seq1 -> (forall n, seq1 n [=] seq2 n) -> Cauchy_prop seq2.
intros seq1 seq2 H H0.
red in |- *.  intros e H1.
elim (H e H1).
intros N Hn; exists N; intros.
astepr (seq1 m[-]seq1 N).
apply Hn; assumption.
Qed.

Lemma Cauchy_Lim_prop2_wd : forall seq1 seq2 c, Cauchy_Lim_prop2 seq1 c ->
 (forall n, seq1 n [=] seq2 n) -> Cauchy_Lim_prop2 seq2 c.
intros seq1 seq2 c H H0.
red in |- *. intros eps H1.
elim (H eps H1).
intros N Hn; exists N; intros.
astepr (seq1 m[-]c).
apply Hn; assumption.
Qed.

Lemma Lim_wd' : forall seq1 seq2 : CauchySeqR,
 (forall n, seq1 n [=] seq2 n) -> Lim seq1 [=] Lim seq2.
intros.
cut (Cauchy_Lim_prop2 seq1 (Lim seq2)).
intro.
apply eq_symmetric_unfolded.
apply Limits_unique; assumption.
apply Cauchy_Lim_prop2_wd with (seq2:nat -> IR).
apply Cauchy_complete.
intro; apply eq_symmetric_unfolded; Algebra.
Qed.

Lemma Lim_unique : forall seq x y,
 Cauchy_Lim_prop2 seq x -> Cauchy_Lim_prop2 seq y -> x [=] y.
intros.
cut (Cauchy_prop seq); [ intro | apply Cauchy_prop2_prop; exists y; auto ].
apply eq_transitive_unfolded with (Lim (Build_CauchySeq _ _ X1)).
apply Limits_unique; auto.
apply eq_symmetric_unfolded; apply Limits_unique; auto.
Qed.

End Equiv_Cauchy.

Section Cauchy_props.

(** *** Properties of Cauchy sequences

Some of these lemmas are now obsolete, because they were reproved for arbitrary ordered fields$\ldots$#...#

We begin by defining the constant sequence and proving that it is Cauchy with the expected limit.
*)

Definition Cauchy_const : IR -> CauchySeq IR.
intro x.
apply Build_CauchySeq with (fun n : nat => x).
intros; exists 0.
intros; astepr ZeroR.
apply zero_AbsSmall; apply less_leEq; assumption.
Defined.

Lemma Lim_const : forall x : IR, x [=] Lim (Cauchy_const x).
intros.
apply Limits_unique.
red in |- *; intro; exists 0.
intros; unfold Cauchy_const in |- *; simpl in |- *.
astepr ZeroR; apply zero_AbsSmall; apply less_leEq; assumption.
Qed.

Lemma Cauchy_Lim_plus : forall seq1 seq2 y1 y2,
 Cauchy_Lim_prop2 seq1 y1 -> Cauchy_Lim_prop2 seq2 y2 ->
 Cauchy_Lim_prop2 (fun n => seq1 n [+] seq2 n) (y1 [+] y2).
intros seq1 seq2 y1 y2 H H0.
unfold Cauchy_Lim_prop2 in |- *.
intros eps H1.
cut (Zero [<] eps [/]TwoNZ).
intro H2.
elim (H _ H2); intros x H3.
elim (H0 _ H2); intros x0 H4.
exists (max x x0).
intros.
rstepr (seq1 m[-]y1[+] (seq2 m[-]y2)).
apply AbsSmall_eps_div_two.
apply H3.
apply le_trans with (max x x0).
apply le_max_l.
assumption.

apply H4.
apply le_trans with (max x x0).
apply le_max_r.
assumption.

apply pos_div_two.
assumption.
Qed.

Lemma Cauchy_plus : forall seq1 seq2 : CauchySeqR,
 Cauchy_prop (fun n => seq1 n [+] seq2 n).
intros.
apply Cauchy_prop2_prop.
unfold Cauchy_prop2 in |- *.
exists (Lim seq1[+]Lim seq2).
apply Cauchy_Lim_plus.
apply Cauchy_complete.
apply Cauchy_complete.
Qed.

Lemma Lim_plus : forall seq1 seq2 : CauchySeqR,
 Lim (Build_CauchySeq _ _ (Cauchy_plus seq1 seq2)) [=] Lim seq1 [+] Lim seq2.
intros.
apply eq_symmetric_unfolded.
apply Limits_unique.
simpl in |- *.
apply Cauchy_Lim_plus.
apply Cauchy_complete.
apply Cauchy_complete.
Qed.

Lemma Cauchy_Lim_inv : forall seq y,
 Cauchy_Lim_prop2 seq y -> Cauchy_Lim_prop2 (fun n => [--] (seq n)) [--]y.
intros seq y H.
unfold Cauchy_Lim_prop2 in |- *.
intros eps H0.
elim (H _ H0); intros x H1.
exists x.
intros.
rstepr ([--] (seq m[-]y)).
apply inv_resp_AbsSmall.
apply H1.
assumption.
Qed.

Lemma Cauchy_inv : forall seq : CauchySeqR, Cauchy_prop (fun n => [--] (seq n)).
intros.
apply Cauchy_prop2_prop.
unfold Cauchy_prop2 in |- *.
exists ([--] (Lim seq)).
apply Cauchy_Lim_inv.
apply Cauchy_complete.
Qed.

Lemma Lim_inv : forall seq : CauchySeqR,
 Lim (Build_CauchySeq _ _ (Cauchy_inv seq)) [=] [--] (Lim seq).
intros.
apply eq_symmetric_unfolded.
apply Limits_unique.
simpl in |- *.
apply Cauchy_Lim_inv.
apply Cauchy_complete.
Qed.

Lemma Cauchy_Lim_minus : forall seq1 seq2 y1 y2,
 Cauchy_Lim_prop2 seq1 y1 -> Cauchy_Lim_prop2 seq2 y2 ->
 Cauchy_Lim_prop2 (fun n => seq1 n[-]seq2 n) (y1[-]y2).
intros.
unfold cg_minus in |- *.
change
  (Cauchy_Lim_prop2 (fun n : nat => seq1 n[+] (fun m : nat => [--] (seq2 m)) n)
     (y1[+][--]y2)) in |- *.
apply Cauchy_Lim_plus.
assumption.
apply Cauchy_Lim_inv.
assumption.
Qed.

Lemma Cauchy_minus : forall seq1 seq2 : CauchySeqR,
 Cauchy_prop (fun n => seq1 n[-]seq2 n).
intros.
apply Cauchy_prop2_prop.
unfold Cauchy_prop2 in |- *.
exists (Lim seq1[-]Lim seq2).
apply Cauchy_Lim_minus.
apply Cauchy_complete.
apply Cauchy_complete.
Qed.

Lemma Lim_minus : forall seq1 seq2 : CauchySeqR,
 Lim (Build_CauchySeq _ _ (Cauchy_minus seq1 seq2)) [=] Lim seq1[-]Lim seq2.
intros.
apply eq_symmetric_unfolded.
apply Limits_unique.
simpl in |- *.
apply Cauchy_Lim_minus.
apply Cauchy_complete.
apply Cauchy_complete.
Qed.

Lemma Cauchy_Lim_mult : forall seq1 seq2 y1 y2,
 Cauchy_Lim_prop2 seq1 y1 -> Cauchy_Lim_prop2 seq2 y2 ->
 Cauchy_Lim_prop2 (fun n => seq1 n [*] seq2 n) (y1 [*] y2).
unfold Cauchy_Lim_prop2 in |- *. intros. rename X into H. rename X0 into H0. rename X1 into H1.
elim (mult_contin _ y1 y2 eps H1). intro c. intros H2 H3.
elim H3. clear H3. intro d. intros H3 H4.
elim (H c H2). clear H. intro N1. intros H.
elim (H0 d H3). clear H0. intro N2. intros H0.
cut {N : nat | N1 <= N /\ N2 <= N}. intro H5.
elim H5. clear H5. intro N. intro H5. elim H5. clear H5. intros.
exists N. intros.
apply AbsSmall_wdr_unfolded with ([--] (y1[*]y2[-]seq1 m[*]seq2 m)).
apply inv_resp_AbsSmall.
apply H4; clear H4; intros.
apply AbsSmall_wdr_unfolded with ([--] (seq1 m[-]y1)).
apply inv_resp_AbsSmall.
apply H. apply le_trans with N; auto.
rational.
apply AbsSmall_wdr_unfolded with ([--] (seq2 m[-]y2)).
apply inv_resp_AbsSmall.
apply H0. apply le_trans with N; auto.
rational.
rational.
elim (le_lt_dec N1 N2); intros.
exists N2. auto.
exists N1. split. auto. auto with arith.
Qed.

Lemma Cauchy_mult : forall seq1 seq2 : CauchySeqR,
 Cauchy_prop (fun n => seq1 n [*] seq2 n).
intros.
apply Cauchy_prop2_prop.
unfold Cauchy_prop2 in |- *.
exists (Lim seq1[*]Lim seq2).
apply Cauchy_Lim_mult.
apply Cauchy_complete.
apply Cauchy_complete.
Qed.

Lemma Lim_mult : forall seq1 seq2 : CauchySeqR,
 Lim (Build_CauchySeq _ _ (Cauchy_mult seq1 seq2)) [=] Lim seq1 [*] Lim seq2.
intros.
apply eq_symmetric_unfolded.
apply Limits_unique.
simpl in |- *.
apply Cauchy_Lim_mult.
apply Cauchy_complete.
apply Cauchy_complete.
Qed.

End Cauchy_props.
