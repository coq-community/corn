(* $Id: Intervals.v,v 1.10 2004/04/23 10:01:04 lcf Exp $ *)

Require Export CSetoidInc.
Require Export RealLists.

Section Intervals.

(** * Intervals
In this section we define (compact) intervals of the real line and
some useful functions to work with them.

** Definitions

We start by defining the compact interval [[a,b]] as being the set of
points less or equal than [b] and greater or equal than [a].  We
require [a [<=] b], as we want to work only in nonempty intervals.
*)

Definition compact (a b : IR) (Hab : a [<=] b) (x : IR) := a [<=] x and x [<=] b.

(**
%\begin{convention}% Let [a,b : IR] and [Hab : a [<=] b].
%\end{convention}%

As expected, both [a] and [b] are members of [[a,b]].  Also they are
members of the interval [[Min(a,b),Max(a,b)]].
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.

Lemma compact_inc_lft : compact a b Hab a.
intros; split; [ apply leEq_reflexive | auto ].
Qed.

Lemma compact_inc_rht : compact a b Hab b.
intros; split; [ auto | apply leEq_reflexive ].
Qed.

Lemma compact_Min_lft : forall Hab', compact (Min a b) (Max a b) Hab' a.

split; [ apply Min_leEq_lft | apply lft_leEq_Max ].
Qed.

Lemma compact_Min_rht : forall Hab', compact (Min a b) (Max a b) Hab' b.

split; [ apply Min_leEq_rht | apply rht_leEq_Max ].
Qed.

(**
As we will be interested in taking functions with domain in a compact
interval, we want this predicate to be well defined.
*)

Lemma compact_wd : pred_wd IR (compact a b Hab).
intros; red in |- *; intros.
inversion_clear X; split.
apply leEq_wdr with x; assumption.
apply leEq_wdl with x; assumption.
Qed.

(**
Also, it will sometimes be necessary to rewrite the endpoints of an interval.
*)

Lemma compact_wd' : forall (a' b' : IR) Hab' (x : IR),
 a [=] a' -> b [=] b' -> compact a b Hab x -> compact a' b' Hab' x.
intros. rename X into H1.
inversion_clear H1; split.
apply leEq_wdl with a; auto.
apply leEq_wdr with b; auto.
Qed.

(**
As we identify subsets with predicates, inclusion is simply implication.
*)

(**
Finally, we define a restriction operator that takes a function [F]
and a well defined predicate [P] included in the domain of [F] and
returns the restriction $F|_P$# of F to P#.
*)

Definition Frestr F P (HP : pred_wd IR P) (H : included P (Dom F)) : PartIR.
intros.
apply Build_PartFunct with P (fun (x : IR) (Hx : P x) => Part F x (H x Hx)).
assumption.
intros. exact (pfstrx _ _ _ _ _ _ X).
Defined.

End Intervals.

Notation Compact := (compact _ _).
Implicit Arguments Frestr [F P].
Notation FRestr := (Frestr (compact_wd _ _ _)).

Section More_Intervals.

Lemma included_refl' : forall a b Hab Hab', included (compact a b Hab) (compact a b Hab').
intros.
red in |- *; intros.
inversion_clear X; split; auto.
Qed.

(** We prove some inclusions of compact intervals.  *)

Definition compact_map1 : forall a b Hab Hab',
 included (compact (Min a b) (Max a b) Hab') (compact a b Hab).
intros.
red in |- *; intros x H.
red in |- *; red in H.
inversion_clear H.
split.
eapply leEq_wdl; [ apply H0 | apply leEq_imp_Min_is_lft; auto ].
eapply leEq_wdr; [ apply H1 | apply leEq_imp_Max_is_rht; auto ].
Defined.

Definition compact_map2 : forall a b Hab Hab',
 included (compact a b Hab) (compact (Min a b) (Max a b) Hab').
intros.
red in |- *; intros x H.
red in |- *; red in H.
inversion_clear H.
split.
eapply leEq_transitive; [ apply Min_leEq_lft | apply H0 ].
eapply leEq_transitive; [ apply H1 | apply rht_leEq_Max ].
Defined.

Definition compact_map3 : forall a b e Hab Hab', Zero [<] e ->
 included (compact a (b[-]e) Hab') (compact a b Hab).
intros; red in |- *. rename X into H.
intros.  rename X into H0. inversion_clear H0; split.
auto.
eapply leEq_transitive.
apply H2.
apply shift_minus_leEq.
apply shift_leEq_plus'.
astepl ZeroR; apply less_leEq; assumption.
Qed.

End More_Intervals.

Hint Resolve included_refl' compact_map1 compact_map2 compact_map3 : included.

Section Totally_Bounded.

(** ** Totally Bounded

Totally bounded sets will play an important role in what is
to come.  The definition (equivalent to the classical one) states that
[P] is totally bounded iff
%\[\forall_{\varepsilon>0}\exists_{x_1,\ldots,x_n}\forall_{y\in P}
\exists_{1\leq i\leq n}|y-x_i|<\varepsilon\]%#&forall;e&gt;0
&exist;x<sub>1</sub>,...,x<sub>n</sub>&forall;y&isin;P&exist;
1&le;i&le;n.|y-x<sub>i</sub>|&lt;e#.

Notice the use of lists for quantification.
*)

Definition totally_bounded (P : IR -> CProp) : CProp := {x : IR | P x} and (forall e,
 Zero [<] e -> {l : list IR | forall x, member x l -> P x |
 forall x, P x -> {y : IR | member y l | AbsSmall e (x[-]y)}}).

(**
This definition is classically, but not constructively, equivalent to
the definition of compact (if completeness is assumed); the next
result, classically equivalent to the Heine-Borel theorem, justifies
that we take the definition of totally bounded to be the relevant one
and that we defined compacts as we did.
*)

Lemma compact_is_totally_bounded : forall a b Hab, totally_bounded (compact a b Hab).
intros; split.
exists a.
apply compact_inc_lft.
cut
 (forall (n : nat) (a b e : IR) (Hab : a [<=] b) (He : Zero [<] e),
  (b[-]a[/] e[//]pos_ap_zero _ _ He) [<=] nring n ->
  (2 <= n -> nring n[-]Two [<=] (b[-]a[/] e[//]pos_ap_zero _ _ He)) ->
  {l : list IR | forall x : IR, member x l -> compact a b Hab x |
  forall x : IR,
  compact a b Hab x -> {y : IR | member y l | AbsIR (x[-]y) [<=] e}}).
intros H e He.
elim (str_Archimedes (b[-]a[/] _[//]pos_ap_zero _ _ (pos_div_two _ _ He))).
intros n Hn.
inversion_clear Hn.
elim (H n a b _ Hab (pos_div_two _ _ He)).
intros l Hl' Hl.
2: assumption.
2: assumption.
exists l.
assumption.
intros x Hx; elim (Hl x Hx).
intros y Hy Hy'.
exists y.
assumption.
apply AbsIR_imp_AbsSmall.
apply leEq_transitive with (e [/]TwoNZ).
assumption.
apply less_leEq; apply pos_div_two'; assumption.
apply shift_leEq_div;
 [ apply pos_div_two; assumption | apply shift_leEq_minus ].
rstepl a; assumption.
clear Hab a b; intro n; induction  n as [| n Hrecn].
intros.
exists (cons a (nil _)).
intros x H1.
inversion H1. rename X into H2.
elim H2.
apply compact_wd with a; algebra.
apply compact_inc_lft.
intros.
exists a.
right; algebra.
apply leEq_wdl with ZeroR.
apply less_leEq; auto.
astepl (AbsIR Zero).
apply AbsIR_wd.
apply leEq_imp_eq. rename X into H1.
apply shift_leEq_minus; astepl a; elim H1; auto.
apply shift_minus_leEq.
apply leEq_transitive with b. rename X into H1.
elim H1; auto.
apply shift_leEq_plus.
apply mult_cancel_leEq with (One[/] _[//]pos_ap_zero _ _ He).
apply recip_resp_pos; auto.
astepr ZeroR.
rstepl (b[-]a[/] _[//]pos_ap_zero _ _ He); auto.
clear Hrecn; induction  n as [| n Hrecn].
intros.
exists (cons a (nil IR)).
intros x H1.
inversion_clear H1. rename X into H2.
elim H2.
apply compact_wd with a; [ apply compact_inc_lft | algebra ].
intros x Hx; inversion_clear Hx.
exists a.
simpl in |- *; right; algebra.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
apply leEq_transitive with (b[-]a).
apply minus_resp_leEq; assumption.
rstepr (e[*]nring 1); eapply shift_leEq_mult'; [ assumption | apply H ].
apply shift_leEq_minus; astepl a.
assumption.
clear Hrecn; induction  n as [| n Hrecn].
intros.
set (enz := pos_ap_zero _ _ He) in *.
exists (cons ((a[+]b) [/]TwoNZ) (nil IR)).
intros x H1.
inversion_clear H1. rename X into H2.
inversion_clear H2.
apply compact_wd with ((a[+]b) [/]TwoNZ); [ split | algebra ].
astepl (a[+]Zero); apply shift_plus_leEq'.
apply mult_cancel_leEq with (Two:IR).
apply pos_two.
astepl ZeroR.
rstepr (b[-]a).
apply shift_leEq_minus; astepl a; auto.
astepr (b[+]Zero); apply shift_leEq_plus'.
apply mult_cancel_leEq with (Two:IR).
apply pos_two.
astepr ZeroR.
rstepl (a[-]b).
apply shift_minus_leEq; astepr b; auto.
intros.
exists ((a[+]b) [/]TwoNZ).
right; algebra.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply Abs_Max.
apply shift_minus_leEq; apply Max_leEq; apply shift_leEq_plus';
 apply leEq_Min.
apply shift_minus_leEq; apply shift_leEq_plus'.
astepl ZeroR; apply less_leEq; auto.
apply shift_minus_leEq.
apply leEq_transitive with b. rename X into H1.
elim H1; auto.
apply shift_leEq_plus'.
apply mult_cancel_leEq with (Two:IR).
apply pos_two.
apply shift_leEq_mult' with enz.
auto.
rstepl (b[-]a[/] e[//]enz); auto.
apply leEq_transitive with a.
2: rename X into H1; elim H1; auto.
apply shift_minus_leEq; apply shift_leEq_plus'.
apply mult_cancel_leEq with (Two:IR).
apply pos_two.
apply shift_leEq_mult' with enz.
auto.
rstepl (b[-]a[/] e[//]enz); auto.
apply shift_minus_leEq; apply shift_leEq_plus'.
astepl ZeroR; apply less_leEq; auto.
intros.
set (b' := b[-]e) in *.
cut (a [<=] b'); intros.
elim (Hrecn a b' e H1 He).
intros l Hl' Hl.
exists (cons b' l).
intros.
unfold b' in H1; apply compact_map3 with (e := e) (Hab' := H1) (b := b).
assumption. rename X into H2.
simpl in H2; inversion_clear H2.
apply Hl'; assumption.
apply compact_wd with b'; [ apply compact_inc_rht | algebra ].
intros.
cut (x [<] b' or b'[-]e [<] x). intros H3.
inversion_clear H3.
cut (compact a b' H1 x). intros H3.
elim (Hl x H3).
intros y Hy Hy'.
exists y.
left; assumption.
auto. rename X into H2.
inversion_clear H2; split.
assumption.
apply less_leEq; auto.
exists b'.
right; algebra.
simpl in |- *; unfold ABSIR in |- *.
apply Max_leEq.
apply shift_minus_leEq; unfold b' in |- *.
rstepr b. rename X into H2.
elim H2; auto.
rstepl (b'[-]x); apply shift_minus_leEq; apply shift_leEq_plus';
 apply less_leEq; assumption.
cut (b'[-]e [<] x or x [<] b'); [ tauto | apply less_cotransitive_unfolded ].
apply shift_minus_less; apply shift_less_plus'; astepl ZeroR; assumption.

unfold b' in |- *.
rstepl ((b[-]a[/] e[//]pos_ap_zero _ _ He) [-]One).
apply shift_minus_leEq.
astepr (nring (R:=IR) (S (S (S n)))); auto.
intro.
unfold b' in |- *.
rstepr ((b[-]a[/] e[//]pos_ap_zero _ _ He) [-]One).
apply shift_leEq_minus.
rstepl (nring (R:=IR) (S (S n)) [+]One[-]Two).
auto with arith.

unfold b' in |- *.
apply shift_leEq_minus; apply shift_plus_leEq'.
astepl (One[*]e); apply shift_mult_leEq with (pos_ap_zero _ _ He).
auto.
apply leEq_transitive with (nring (R:=IR) (S (S (S n))) [-]Two).
apply shift_leEq_minus; rstepl (Three:IR); apply nring_leEq; auto with arith.
auto with arith.
Qed.

(**
Suprema and infima will be needed throughout; we define them here both
for arbitrary subsets of [IR] and for images of functions.
*)

Definition set_glb_IR (P : IR -> CProp) a : CProp := (forall x, P x -> a [<=] x) and
 (forall e, Zero [<] e -> {x : IR | P x | x[-]a [<] e}).

Definition set_lub_IR (P : IR -> CProp) a : CProp := (forall x, P x -> x [<=] a) and
 (forall e, Zero [<] e -> {x : IR | P x | a[-]x [<] e}).

Definition fun_image F (P : IR -> CProp) x : CProp := {y : IR |
 P y and Dom F y and (forall Hy, F y Hy [=] x)}.
  
Definition fun_glb_IR F (P : IR -> CProp) a : CProp :=
 set_glb_IR (fun_image F P) a.

Definition fun_lub_IR F (P : IR -> CProp) a : CProp :=
 set_lub_IR (fun_image F P) a.

(* begin hide *)
Let aux_seq_lub (P : IR -> CProp) (H : totally_bounded P) :
  forall k : nat,
  Build_SubCSetoid IR
    (fun x : IR =>
     P x and (forall y : IR, P y -> y[-]x [<=] Two[*]one_div_succ k)).
intros P H; elim H; clear H; intros non_empty H k.
elim (H (one_div_succ k) (one_div_succ_pos IR k)).
intros l Hl' Hl; clear H.
cut {y : IR | member y l | maxlist l[-]one_div_succ k [<=] y}.
intro H; inversion_clear H.
2: apply maxlist_leEq_eps.
2: inversion_clear non_empty.
2: elim (Hl x).
2: intros.
2: exists x0.
2: tauto.
2: assumption.
2: apply one_div_succ_pos.
exists x; split.
apply Hl'; assumption.
intros y Hy.
elim (Hl y Hy).
intros z Hz Hz'.
rstepl (y[-]z[+] (z[-]x)).
rstepr (one_div_succ (R:=IR) k[+]one_div_succ k).
apply plus_resp_leEq_both.
apply leEq_transitive with (AbsIR (y[-]z)).
apply leEq_AbsIR.
apply AbsSmall_imp_AbsIR; assumption.
apply shift_minus_leEq.
apply leEq_transitive with (maxlist l).
apply maxlist_greater; assumption.
apply shift_leEq_plus'.
assumption.
Qed.

Let aux_seq_lub_prop :
  forall (P : IR -> CProp) (H : totally_bounded P),
  (forall k : nat, P (scs_elem _ _ (aux_seq_lub P H k)))
  and (forall (k : nat) (y : IR),
       P y -> y[-]scs_elem _ _ (aux_seq_lub P H k) [<=] Two[*]one_div_succ k).
intros;
 cut
  (forall k : nat,
   P (scs_elem _ _ (aux_seq_lub P H k))
   and (forall y : IR,
        P y -> y[-]scs_elem _ _ (aux_seq_lub P H k) [<=] Two[*]one_div_succ k)).
intro H0.
split; intro; elim (H0 k); intros.
assumption.
apply b; assumption.
intro; apply scs_prf.
Qed.
(* end hide *)

(**
The following are probably the most important results in this section.
*)

Lemma totally_bounded_has_lub : forall P,
 totally_bounded P -> {z : IR | set_lub_IR P z}.
intros P tot_bnd.
red in tot_bnd.
elim tot_bnd; intros non_empty H.
cut
 {sequence : nat -> IR | forall k : nat, P (sequence k) |
 forall (k : nat) (x : IR), P x -> x[-]sequence k [<=] Two[*]one_div_succ k}.
intros H0.
elim H0.
intros seq Hseq Hseq'.
cut (Cauchy_prop seq).
intro H1.
set (seq1 := Build_CauchySeq IR seq H1) in *.
exists (Lim seq1).
split; intros.
apply shift_leEq_rht.
astepl ( [--]ZeroR); rstepr ( [--] (x[-]Lim seq1)).
apply inv_resp_leEq.
set (seq2 := Cauchy_const x) in *.
apply leEq_wdl with (Lim seq2[-]Lim seq1).
2: apply cg_minus_wd;
    [ unfold seq2 in |- *; apply eq_symmetric_unfolded; apply Lim_const
    | algebra ].
apply
 leEq_wdl
  with
    (Lim
       (Build_CauchySeq IR (fun n : nat => seq2 n[-]seq1 n)
          (Cauchy_minus seq2 seq1))).
apply leEq_transitive with (Lim twice_inv_seq).
apply Lim_leEq_Lim; intro; simpl in |- *.
apply Hseq'; assumption.
apply eq_imp_leEq.
apply eq_symmetric_unfolded; apply Limits_unique.
red in |- *; fold (SeqLimit twice_inv_seq Zero) in |- *.
apply twice_inv_seq_Lim.
apply Lim_minus.
cut (Cauchy_Lim_prop2 seq (Lim seq1)).
intro H4; red in H4. rename X into H2.
elim (H4 (e [/]TwoNZ) (pos_div_two _ _ H2)); clear H4.
intros n Hn.
exists (seq n).
apply Hseq.
apply leEq_less_trans with (AbsIR (Lim seq1[-]seq n)).
apply leEq_AbsIR.
apply leEq_less_trans with (e [/]TwoNZ).
apply AbsSmall_imp_AbsIR.
apply AbsSmall_minus; simpl in |- *; apply Hn.
apply le_n.
apply pos_div_two'; auto.
cut (Cauchy_Lim_prop2 seq1 (Lim seq1)); intros.
rename X0 into H3.
red in |- *; red in H3.
intros eps Heps; elim (H3 eps Heps); clear H3; intros.
exists x.
intros m Hm; elim (p m Hm); clear p.
intros.
astepr (seq1 m[-]Lim seq1).
apply AbsIR_eq_AbsSmall; assumption.
red in |- *; fold (SeqLimit seq1 (Lim seq1)) in |- *.
apply ax_Lim.
apply crl_proof.
red in |- *; intros. rename X into H1.
elim (Archimedes (One[/] e[//]pos_ap_zero _ _ H1)).
intros n Hn.
exists (S (2 * n)); intros.
cut (Zero [<] nring (R:=IR) n); intros.
apply AbsIR_eq_AbsSmall. rename X into H3.
apply leEq_transitive with ( [--] (One[/] nring n[//]pos_ap_zero _ _ H3)).
apply inv_resp_leEq.
apply shift_div_leEq.
assumption.
eapply shift_leEq_mult'; [ assumption | apply Hn ].
rstepr ( [--] (seq (S (2 * n)) [-]seq m)); apply inv_resp_leEq.
apply leEq_transitive with (Two[*]one_div_succ (R:=IR) m).
auto.
apply leEq_transitive with (one_div_succ (R:=IR) n).
unfold one_div_succ in |- *.
unfold Snring in |- *.
rstepl
 (One[/] nring (S m) [/]TwoNZ[//]
  div_resp_ap_zero_rev _ _ _ _ (nring_ap_zero IR (S m) (sym_not_eq (O_S m)))).
apply recip_resp_leEq.
apply pos_nring_S.
apply shift_leEq_div.
apply pos_two.
simpl in |- *; fold (Two:IR) in |- *.
rstepl (Two[*]nring (R:=IR) n[+]One[+]One).
apply plus_resp_leEq.
apply leEq_wdl with (nring (R:=IR) (S (2 * n))).
apply nring_leEq; assumption.
Step_final (nring (R:=IR) (2 * n) [+]One).
unfold one_div_succ in |- *; unfold Snring in |- *; apply recip_resp_leEq.
assumption.
simpl in |- *; apply less_leEq; apply less_plusOne.
apply leEq_transitive with (Two[*]one_div_succ (R:=IR) (S (2 * n))).
auto.
apply less_leEq. rename X into H3.
apply less_leEq_trans with (One[/] nring n[//]pos_ap_zero _ _ H3).
astepl (one_div_succ (R:=IR) (S (2 * n)) [*]Two).
unfold one_div_succ in |- *; unfold Snring in |- *.
apply shift_mult_less with (two_ap_zero IR).
apply pos_two.
rstepr
 (One[/] Two[*]nring n[//]
  mult_resp_ap_zero _ _ _ (two_ap_zero IR) (pos_ap_zero _ _ H3)).
apply recip_resp_less.
astepl (ZeroR[*]Zero); apply mult_resp_less_both; try apply leEq_reflexive;
 [ apply pos_two | assumption ].
apply less_wdr with (Two[*]nring (R:=IR) n[+]One[+]One).
apply less_transitive_unfolded with (Two[*]nring (R:=IR) n[+]One);
 apply less_plusOne.
astepr (nring (R:=IR) (S (2 * n)) [+]One).
Step_final (nring (R:=IR) (2 * n) [+]One[+]One).
rstepr
 (One[/] One[/] e[//]pos_ap_zero _ _ H1[//]
  div_resp_ap_zero_rev _ _ _ _ (one_ap_zero IR)).
apply recip_resp_leEq; [ apply recip_resp_pos; assumption | assumption ].
eapply less_leEq_trans.
2: apply Hn.
apply recip_resp_pos; assumption.
elim (aux_seq_lub_prop P tot_bnd).
exists (fun k : nat => scs_elem _ _ (aux_seq_lub P tot_bnd k)); auto.
Qed.

(* begin hide *)
Let aux_seq_glb (P : IR -> CProp) (H : totally_bounded P) :
  forall k : nat,
  Build_SubCSetoid IR
    (fun x : IR =>
     P x and (forall y : IR, P y -> x[-]y [<=] Two[*]one_div_succ k)).
intros P H; elim H; clear H; intros non_empty H k.
elim (H (one_div_succ k) (one_div_succ_pos IR k)).
intros l Hl' Hl; clear H.
cut {y : IR | member y l | y [<=] minlist l[+]one_div_succ k}.
intro H; inversion_clear H.
2: apply minlist_leEq_eps.
2: inversion_clear non_empty.
2: elim (Hl x).
2: intros.
2: exists x0.
2: tauto.
2: assumption.
2: apply one_div_succ_pos.
exists x; split.
apply Hl'; assumption.
intros y Hy.
elim (Hl y Hy).
intros z Hz Hz'.
rstepl (x[-]z[+] (z[-]y)).
rstepr (one_div_succ (R:=IR) k[+]one_div_succ k).
apply plus_resp_leEq_both.
apply shift_minus_leEq.
apply shift_leEq_plus'.
apply leEq_transitive with (minlist l).
apply shift_minus_leEq.
assumption.
apply minlist_smaller; assumption.
apply leEq_transitive with (AbsIR (y[-]z)).
rstepl ( [--] (y[-]z)); apply inv_leEq_AbsIR.
apply AbsSmall_imp_AbsIR; assumption.
Qed.

Let aux_seq_glb_prop :
  forall (P : IR -> CProp) (H : totally_bounded P),
  (forall k : nat, P (scs_elem _ _ (aux_seq_glb P H k)))
  and (forall (k : nat) (y : IR),
       P y -> scs_elem _ _ (aux_seq_glb P H k) [-]y [<=] Two[*]one_div_succ k).
intros;
 cut
  (forall k : nat,
   P (scs_elem _ _ (aux_seq_glb P H k))
   and (forall y : IR,
        P y -> scs_elem _ _ (aux_seq_glb P H k) [-]y [<=] Two[*]one_div_succ k)).
intro H0.
split; intro k; elim (H0 k); intros.
assumption.
apply b; assumption.
intro; apply scs_prf.
Qed.
(* end hide *)

Lemma totally_bounded_has_glb : forall P : IR -> CProp,
 totally_bounded P -> {z : IR | set_glb_IR P z}.
intros P tot_bnd.
red in tot_bnd.
elim tot_bnd; intros non_empty H.
cut
 {sequence : nat -> IR | forall k : nat, P (sequence k) |
 forall (k : nat) (x : IR), P x -> sequence k[-]x [<=] Two[*]one_div_succ k}.
intros H0.
elim H0.
clear H0; intros seq H0 H1.
cut (Cauchy_prop seq).
intro H2.
set (seq1 := Build_CauchySeq IR seq H2) in *.
exists (Lim seq1).
split; intros.
apply shift_leEq_rht.
astepl ( [--]ZeroR); rstepr ( [--] (Lim seq1[-]x)).
apply inv_resp_leEq.
set (seq2 := Cauchy_const x) in *.
apply leEq_wdl with (Lim seq1[-]Lim seq2).
2: apply cg_minus_wd;
    [ algebra
    | unfold seq2 in |- *; apply eq_symmetric_unfolded; apply Lim_const ].
apply
 leEq_wdl
  with
    (Lim
       (Build_CauchySeq IR (fun n : nat => seq1 n[-]seq2 n)
          (Cauchy_minus seq1 seq2))).
apply leEq_transitive with (Lim twice_inv_seq).
apply Lim_leEq_Lim; intro.
simpl in |- *.
apply H1; assumption.
apply eq_imp_leEq.
apply eq_symmetric_unfolded; apply Limits_unique.
red in |- *; fold (SeqLimit twice_inv_seq Zero) in |- *.
apply twice_inv_seq_Lim.
apply Lim_minus.
cut (Cauchy_Lim_prop2 seq (Lim seq1)).
intro H4; red in H4. rename X into H3.
elim (H4 (e [/]TwoNZ) (pos_div_two _ _ H3)); clear H4.
intros n Hn.
exists (seq n).
apply H0.
apply leEq_less_trans with (AbsIR (Lim seq1[-]seq n)).
rstepl ( [--] (Lim seq1[-]seq n)).
apply inv_leEq_AbsIR.
apply leEq_less_trans with (e [/]TwoNZ).
apply AbsSmall_imp_AbsIR.
apply AbsSmall_minus; simpl in |- *; apply Hn.
apply le_n.
apply pos_div_two'; auto.
cut (Cauchy_Lim_prop2 seq1 (Lim seq1)); intros.
rename X0 into H4.
red in |- *; red in H4.
intros eps Heps; elim (H4 eps Heps); clear H4; intros.
exists x.
intros m Hm; elim (p m Hm); clear p.
intros.
astepr (seq1 m[-]Lim seq1).
apply AbsIR_eq_AbsSmall; assumption.
red in |- *; fold (SeqLimit seq1 (Lim seq1)) in |- *.
apply ax_Lim.
apply crl_proof.
red in |- *; intros e H2.
elim (Archimedes (One[/] e[//]pos_ap_zero _ _ H2)).
intros n Hn.
exists (S (2 * n)); intros.
cut (Zero [<] nring (R:=IR) n); intros.
apply AbsIR_eq_AbsSmall.
rename X into H4.
apply leEq_transitive with ( [--] (One[/] nring n[//]pos_ap_zero _ _ H4)).
apply inv_resp_leEq.
apply shift_div_leEq.
assumption.
eapply shift_leEq_mult'; [ assumption | apply Hn ].
apply less_leEq.
rstepr ( [--] (seq (S (2 * n)) [-]seq m)); apply inv_resp_less.
apply leEq_less_trans with (Two[*]one_div_succ (R:=IR) (S (2 * n))).
apply H1; apply H0.
astepl (one_div_succ (R:=IR) (S (2 * n)) [*]Two).
unfold one_div_succ in |- *; unfold Snring in |- *.
apply shift_mult_less with (two_ap_zero IR).
apply pos_two.
rstepr
 (One[/] Two[*]nring n[//]
  mult_resp_ap_zero _ _ _ (two_ap_zero IR) (pos_ap_zero _ _ H4)).
apply recip_resp_less.
astepl (ZeroR[*]Zero); apply mult_resp_less_both; try apply leEq_reflexive;
 [ apply pos_two | assumption ].
apply less_wdr with (Two[*]nring (R:=IR) n[+]One[+]One).
apply less_transitive_unfolded with (Two[*]nring (R:=IR) n[+]One);
 apply less_plusOne.
astepr (nring (R:=IR) (S (2 * n)) [+]One).
Step_final (nring (R:=IR) (2 * n) [+]One[+]One).
apply leEq_transitive with (Two[*]one_div_succ (R:=IR) m).
apply H1; apply H0.
apply leEq_transitive with (one_div_succ (R:=IR) n).
unfold one_div_succ in |- *.
unfold Snring in |- *.
rstepl
 (One[/] nring (R:=IR) (S m) [/]TwoNZ[//]
  div_resp_ap_zero_rev _ _ _ _ (nring_ap_zero IR (S m) (sym_not_eq (O_S m)))).
apply recip_resp_leEq.
apply pos_nring_S.
apply shift_leEq_div.
apply pos_two.
simpl in |- *; fold (Two:IR) in |- *.
rstepl (Two[*]nring (R:=IR) n[+]One[+]One).
apply plus_resp_leEq.
apply leEq_wdl with (nring (R:=IR) (S (2 * n))).
apply nring_leEq; assumption.
Step_final (nring (R:=IR) (2 * n) [+]One).
unfold one_div_succ in |- *; unfold Snring in |- *.
rstepr
 (One[/] One[/] e[//]pos_ap_zero _ _ H2[//]
  div_resp_ap_zero_rev _ _ _ _ (one_ap_zero IR)).
apply recip_resp_leEq.
apply recip_resp_pos; assumption.
apply leEq_transitive with (nring (R:=IR) n);
 [ assumption | simpl in |- *; apply less_leEq; apply less_plusOne ].
eapply less_leEq_trans.
2: apply Hn.
apply recip_resp_pos; assumption.
elim (aux_seq_glb_prop P tot_bnd).
exists (fun k : nat => scs_elem _ _ (aux_seq_glb P tot_bnd k)); auto.
Qed.

End Totally_Bounded.

Section Compact.

(** ** Compact sets

In this section we dwell a bit farther into the definition of compactness
and explore some of its properties.

The following characterization of inclusion can be very useful:
*)

Lemma included_compact : forall (a b c d : IR) Hab Hcd, compact a b Hab c ->
 compact a b Hab d -> included (compact c d Hcd) (compact a b Hab).
repeat intro. rename X into H. rename X0 into H0. rename X1 into H1.
inversion_clear H.
inversion_clear H0.
inversion_clear H1.
split.
apply leEq_transitive with c; auto.
apply leEq_transitive with d; auto.
Qed.

(**
At several points in our future development of a theory we will need
to partition a compact interval in subintervals of length smaller than
some predefined value [eps]. Although this seems a
consequence of every compact interval being totally bounded, it is in
fact a stronger property.  In this section we perform that
construction (requiring the endpoints of the interval to be distinct)
and prove some of its good properties.

%\begin{convention}% Let [a,b : IR], [Hab : (a [<=] b)] and denote by [I]
the compact interval [[a,b]].  Also assume that [a [<] b], and let [e] be
a positive real number.
%\end{convention}%
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := compact a b Hab.
(* end hide *)

Hypothesis Hab' : a [<] b.

Variable e : IR.
Hypothesis He : Zero [<] e.

(**
We start by finding a natural number [n] such that [(b[-]a) [/] n [<] e].
*)

Definition compact_nat := ProjT1 (Archimedes (b[-]a[/] e[//]pos_ap_zero _ _ He)).

(** Obviously such an [n] must be greater than zero.*)

Lemma pos_compact_nat : Zero [<] nring (R:=IR) compact_nat.

apply less_leEq_trans with (b[-]a[/] e[//]pos_ap_zero _ _ He).
rstepr ((b[-]a) [*] (One[/] e[//]pos_ap_zero _ _ He)).
apply mult_resp_pos.
apply shift_less_minus; astepl a; assumption.
apply recip_resp_pos; assumption.
unfold compact_nat in |- *; apply proj2_sigT.
Qed.

(**
We now define a sequence on [n] points in [[a,b]] by
[x_i [=] Min(a,b) [+]i[*] (b[-]a) [/]n] and
prove that all of its points are really in that interval.
*)

Definition compact_part (i : nat) : i <= compact_nat -> IR.
intros.
apply (a[+]nring i[*] (b[-]a[/] _[//]pos_ap_zero _ _ pos_compact_nat)).
Defined.

Lemma compact_part_hyp : forall i Hi, compact a b Hab (compact_part i Hi).
intros; unfold compact_part in |- *.
split.
astepl (a[+]Zero); apply plus_resp_leEq_lft.
astepl (ZeroR[*]Zero); apply mult_resp_leEq_both; try apply leEq_reflexive.
apply nring_nonneg.
apply shift_leEq_div.
apply pos_compact_nat.
apply shift_leEq_minus; rstepl a; apply less_leEq; assumption.
rstepr
 (a[+]nring compact_nat[*] (b[-]a[/] _[//]pos_ap_zero _ _ pos_compact_nat)).
apply plus_resp_leEq_lft.
apply mult_resp_leEq_rht; try apply nring_nonneg.
apply nring_leEq; assumption.
apply shift_leEq_div.
apply pos_compact_nat.
apply shift_leEq_minus; rstepl a; apply less_leEq; assumption.
Qed.

(**
This sequence is strictly increasing and each two consecutive points
are apart by less than [e].*)

Lemma compact_less : forall i Hi HSi, Zero [<] compact_part (S i) HSi[-]compact_part i Hi.
intros i H1 H2.
apply shift_less_minus; astepl (compact_part _ H1).
unfold compact_part in |- *.
apply plus_resp_less_lft.
apply mult_resp_less.
simpl in |- *; apply less_plusOne.
apply div_resp_pos.
apply pos_compact_nat.
apply shift_less_minus; astepl a; assumption.
Qed.

Lemma compact_leEq : forall i Hi HSi, compact_part (S i) HSi[-]compact_part i Hi [<=] e.
intros i H1 H2.
unfold compact_part in |- *; simpl in |- *.
rstepl (b[-]a[/] _[//]pos_ap_zero _ _ pos_compact_nat).
apply shift_div_leEq.
apply pos_compact_nat.
apply shift_leEq_mult' with (pos_ap_zero _ _ He).
assumption.
exact (ProjT2 (Archimedes _)).
Qed.

(** When we proceed to integration, this lemma will also be useful: *)

Lemma compact_partition_lemma : forall n Hn i, i <= n ->
 Compact Hab (a[+]nring i[*] (b[-]a[/] _[//]nring_ap_zero' _ n Hn)).
intros n Hn i H; split.
apply shift_leEq_plus'.
astepl ZeroR.
apply mult_resp_nonneg.
apply nring_nonneg.
apply shift_leEq_div.
apply nring_pos; apply neq_O_lt; auto.
apply shift_leEq_minus.
rstepl a; assumption.
apply shift_plus_leEq'.
rstepr (nring n[*] (b[-]a[/] _[//]nring_ap_zero' _ _ Hn)).
astepl (Zero[+]nring i[*] (b[-]a[/] _[//]nring_ap_zero' _ _ Hn)).
apply shift_plus_leEq.
rstepr ((nring n[-]nring i) [*] (b[-]a[/] _[//]nring_ap_zero' _ _ Hn)).
apply mult_resp_nonneg.
apply shift_leEq_minus.
astepl (nring (R:=IR) i).
apply nring_leEq; assumption.
apply shift_leEq_div.
apply nring_pos; apply neq_O_lt; auto.
apply shift_leEq_minus.
rstepl a; assumption.
Qed.

(** The next lemma provides an upper bound for the distance between two points in an interval: *)

Lemma compact_elements : forall x y : IR,
 Compact Hab x -> Compact Hab y -> AbsIR (x[-]y) [<=] AbsIR (b[-]a).
clear Hab' He e.
do 2 intro; intros Hx Hy.
apply leEq_wdr with (b[-]a).
2: apply eq_symmetric_unfolded; apply AbsIR_eq_x.
2: apply shift_leEq_minus; astepl a; auto.
eapply leEq_wdl.
2: apply eq_symmetric_unfolded; apply Abs_Max.
inversion_clear Hx.
inversion_clear Hy.
unfold cg_minus in |- *; apply plus_resp_leEq_both.
apply Max_leEq; auto.
apply inv_resp_leEq.
apply leEq_Min; auto.
Qed.

Opaque Min Max.

(** The following is a variation on the previous lemma: *)

Lemma compact_elements' : forall c d Hcd x y, Compact Hab x ->
 compact c d Hcd y -> AbsIR (x[-]y) [<=] AbsIR (Max b d[-]Min a c).
do 5 intro; intros Hx Hy.
eapply leEq_transitive.
2: apply leEq_AbsIR.
inversion_clear Hx.
inversion_clear Hy.
simpl in |- *; unfold ABSIR in |- *; apply Max_leEq.
unfold cg_minus in |- *; apply plus_resp_leEq_both.
apply leEq_transitive with b; auto; apply lft_leEq_Max.
apply inv_resp_leEq; apply leEq_transitive with c; auto; apply Min_leEq_rht.
rstepl (y[-]x).
unfold cg_minus in |- *; apply plus_resp_leEq_both.
apply leEq_transitive with d; auto; apply rht_leEq_Max.
apply inv_resp_leEq; apply leEq_transitive with a; auto; apply Min_leEq_lft.
Qed.

(** The following lemma is a bit more specific: it shows that we can
also estimate the distance from the center of a compact interval to
any of its points. *)

Lemma compact_bnd_AbsIR : forall x y d H,
 compact (x[-]d) (x[+]d) H y -> AbsIR (x[-]y) [<=] d.
intros x y d H H0.
inversion_clear H0.
simpl in |- *; unfold ABSIR in |- *.
apply Max_leEq.
apply shift_minus_leEq; apply shift_leEq_plus'; auto.
rstepl (y[-]x).
apply shift_minus_leEq.
astepr (x[+]d); auto.
Qed.

(** Finally, two more useful lemmas to prove inclusion of compact
intervals.  They will be necessary for the definition and proof of the
elementary properties of the integral.  *)

Lemma included2_compact : forall x y Hxy, Compact Hab x -> Compact Hab y ->
 included (compact (Min x y) (Max x y) Hxy) (Compact Hab).
do 3 intro. intros H H0.
inversion_clear H.
inversion_clear H0.
apply included_compact; split.
apply leEq_Min; auto.
apply leEq_transitive with y.
apply Min_leEq_rht.
auto.
apply leEq_transitive with y.
auto.
apply rht_leEq_Max.
apply Max_leEq; auto.
Qed.

Lemma included3_compact : forall x y z Hxyz,
 Compact Hab x -> Compact Hab y -> Compact Hab z ->
 included (compact (Min (Min x y) z) (Max (Max x y) z) Hxyz) (Compact Hab).
do 4 intro. intros H H0 H1.
inversion_clear H.
inversion_clear H0.
inversion_clear H1.
apply included_compact; split.
repeat apply leEq_Min; auto.
apply leEq_transitive with z.
apply Min_leEq_rht.
auto.
apply leEq_transitive with z.
auto.
apply rht_leEq_Max.
repeat apply Max_leEq; auto.
Qed.

End Compact.

Hint Resolve included_compact included2_compact included3_compact : included.
