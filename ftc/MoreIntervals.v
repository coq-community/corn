
Require Export NthDerivative.

Opaque Min Max.

Section Intervals.

(** printing realline %\ensuremath{\RR}% #(-&infin;,+&infin;)# *)
(** printing openl %\ensuremath{(\cdot,+\infty)}% #(&sdot;,+&infin;)# *)
(** printing openr %\ensuremath{(-\infty,\cdot)}% #(-&infin;,&sdot;)# *)
(** printing closel %\ensuremath{[\cdot,+\infty)}% #[&sdot;,+&infin;)# *)
(** printing closer %\ensuremath{(-\infty,\cdot]}% #(-&infin;,&sdot;]# *)
(** printing olor %\ensuremath{(\cdot,\cdot)}% #(&sdot;,&sdot;)# *)
(** printing clor %\ensuremath{[\cdot,\cdot)}% #[&sdot;,&sdot;)# *)
(** printing olcr %\ensuremath{(\cdot,\cdot]}% #(&sdot;,&sdot;]# *)
(** printing clcr %\ensuremath{[\cdot,\cdot]}% #[&sdot;,&sdot;]# *)

(** *Generalized Intervals

At this stage we have enough material to begin generalizing our
concepts in preparation for the fundamental theorem of calculus and
the definition of the main (non-polynomial) functions of analysis.

In order to define functions via power series (or any other kind of
series) we need to formalize a notion of convergence more general than
the one we already have on compact intervals.  This is necessary for
practical reasons: we want to define a single exponential function
with domain [IR], not several exponential functions defined on compact
intervals which we prove to be the same wherever their domains
overlap.  In a similar way, we want to define indefinite integrals on
infinite domains and not only on compact intervals.

Unfortunately, proceeding in a way analogous to how we defined the
concept of global continuity will lead us nowhere; the concept turns
out to be to general, and the behaviour on too small domains
(typically intervals [[a,a']] where [a [=] a'] is neither
provably true nor provably false) will be unsatisfactory.

There is a special family of sets, however, where this problems can be
avoided: intervals.  Intervals have some nice properties that allow us
to prove good results, namely the facts that if [a] and [b] are
elements of an interval [I] then so are [Min(a,b)] and
[Max(a,b)] (which is in general not true) and also the
compact interval [[a,b]] is included in [I].  Furthermore, all
intervals are characterized by simple, well defined predicates, and
the nonempty and proper concepts become very easy to define.

**Definitions and Basic Results

We define an inductive type of intervals with nine constructors,
corresponding to the nine basic types of intervals.  The reason why so
many constructors are needed is that we do not have a notion of real
line, for many reasons which we will not discuss here.  Also it seems
simple to directly define finite intervals than to define then later
as intersections of infinite intervals, as it would only mess things
up.

The compact interval which we will define here is obviously the same
that we have been working with all the way through; why, then, the
different formulation?  The reason is simple: if we had worked with
intervals from the beginning we would have had case definitions at
every spot, and our lemmas and proofs would have been very awkward.
Also, it seems more natural to characterize a compact interval by two
real numbers (and a proof) than as a particular case of a more general
concept which doesn't have an intuitive interpretation.  Finally, the
definitions we will make here will have the elegant consequence that
from this point on we can work with any kind of intervals in exactly
the same way.
*)

Inductive interval : Type :=
  | realline         : interval
  | openl      : IR -> interval
  | openr      : IR -> interval
  | closel     : IR -> interval
  | closer     : IR -> interval
  | olor : IR -> IR -> interval
  | olcr : IR -> IR -> interval
  | clor : IR -> IR -> interval
  | clcr : IR -> IR -> interval.

(**
To each interval a predicate (set) is assigned by the following map:
*)

Definition iprop (I : interval) (x : IR) : CProp :=
  match I with
  | realline => CTrue
  | openr b  => x [<] b
  | openl a  => a [<] x
  | closer b => x [<=] b
  | closel a => a [<=] x
  | olor a b => a [<] x and x [<] b
  | olcr a b => a [<] x and x [<=] b
  | clor a b => a [<=] x and x [<] b
  | clcr a b => a [<=] x and x [<=] b
  end.

(* begin hide *)
Coercion iprop : interval >-> Funclass.
(* end hide *)

(**
This map is made into a coercion, so that intervals
%\emph{%#<i>#are%}%#</i># really subsets of reals.

We now define what it means for an interval to be nonvoid, proper,
finite and compact in the obvious way.
*)

Definition nonvoid (I : interval) : CProp :=
  match I with
  | realline => CTrue
  | openr b  => CTrue
  | openl a  => CTrue
  | closer b => CTrue
  | closel a => CTrue
  | olor a b => a [<] b
  | olcr a b => a [<] b
  | clor a b => a [<] b
  | clcr a b => a [<=] b
  end.

Definition proper (I : interval) : CProp :=
  match I with
  | realline => CTrue
  | openr b  => CTrue
  | openl a  => CTrue
  | closer b => CTrue
  | closel a => CTrue
  | olor a b => a [<] b
  | olcr a b => a [<] b
  | clor a b => a [<] b
  | clcr a b => a [<] b
  end.

Definition finite (I : interval) : CProp :=
  match I with
  | realline => CFalse
  | openr b  => CFalse
  | openl a  => CFalse
  | closer b => CFalse
  | closel a => CFalse
  | olor a b => CTrue
  | olcr a b => CTrue
  | clor a b => CTrue
  | clcr a b => CTrue
  end.

Definition compact_ (I : interval) : CProp :=
  match I with
  | realline => CFalse
  | openr b  => CFalse
  | openl a  => CFalse
  | closer b => CFalse
  | closel a => CFalse
  | olor a b => CFalse
  | olcr a b => CFalse
  | clor a b => CFalse
  | clcr a b => a [<=] b
  end.

(** Finite intervals have a left end and a right end. *)

Definition left_end (I : interval) : finite I -> IR.
intro.
elim I; intros; rename X into H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
apply c.
apply c.
apply c.
apply c.
Defined.

Definition right_end (I : interval) : finite I -> IR.
intro.
elim I; intros; rename X into H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
apply c0.
apply c0.
apply c0.
apply c0.
Defined.

(**
Some trivia: compact intervals are finite; proper intervals are nonvoid; an interval is nonvoid iff it contains some point.
*)

Lemma compact_finite : forall I : interval, compact_ I -> finite I.
intros; induction  I as [| c| c| c| c| c c0| c c0| c c0| c c0]; simpl in |- *;
 auto.
Qed.

Lemma proper_nonvoid : forall I : interval, proper I -> nonvoid I.
intro.
elim I; simpl in |- *; intros; auto.
apply less_leEq; auto.
Qed.

Lemma nonvoid_point : forall I : interval, nonvoid I -> {x : IR | I x}.
intro.
elim I; simpl in |- *; intros; try rename X into H.
exists ZeroR; auto.
exists (c[+]One); apply less_plusOne.
exists (c[-]One); apply shift_minus_less; apply less_plusOne.
exists c; apply leEq_reflexive.
exists c; apply leEq_reflexive.
exists (c[+] (c0[-]c) [/]TwoNZ); split.
astepl (c[+]Zero); apply plus_resp_less_lft.
apply div_resp_pos.
apply pos_two.
apply shift_less_minus; astepl c; auto.
rstepr (c[+] (c0[-]c)).
apply plus_resp_less_lft.
apply pos_div_two'.
apply shift_less_minus; astepl c; auto.
exists c0; split; auto; apply leEq_reflexive.
exists c; split; auto; apply leEq_reflexive.
exists c; split; [ apply leEq_reflexive | auto ].
Qed.

Lemma nonvoid_char : forall (I : interval) (x : IR), I x -> nonvoid I.
intro; induction I; simpl in |- *; intros x H; auto; inversion_clear H.
apply less_transitive_unfolded with x; auto.
apply less_leEq_trans with x; auto.
apply leEq_less_trans with x; auto.
apply leEq_transitive with x; auto.
Qed.

(**
For practical reasons it helps to define left end and right end of compact intervals.
*)

Definition Lend I (H : compact_ I) := left_end I (compact_finite I H).

Definition Rend I (H : compact_ I) := right_end I (compact_finite I H).

(** In a compact interval, the left end is always less than or equal
to the right end.
*)

Lemma Lend_leEq_Rend : forall I cI, Lend I cI [<=] Rend I cI.
intro; elim I; simpl in |- *; intros; try inversion cI; auto.
Qed.

(**
Some nice characterizations of inclusion:
*)

Lemma compact_included : forall a b Hab (I : interval),
 I a -> I b -> included (compact a b Hab) I.
induction I; red in |- *; simpl in |- *; intros X X0 x X1; 
 try inversion_clear X; try inversion_clear X0; try inversion_clear X1.
auto.
apply less_leEq_trans with a; auto.
apply leEq_less_trans with b; auto.
apply leEq_transitive with a; auto.
apply leEq_transitive with b; auto.
split; [ apply less_leEq_trans with a | apply leEq_less_trans with b ]; auto.
split; [ apply less_leEq_trans with a | apply leEq_transitive with b ]; auto.
split; [ apply leEq_transitive with a | apply leEq_less_trans with b ]; auto.
split; [ apply leEq_transitive with a | apply leEq_transitive with b ]; auto.
Qed.

Lemma included_interval' : forall (I : interval) x y z w, I x -> I y -> I z -> I w ->
 forall H, included (compact (Min x z) (Max y w) H) I.
intros I x y z w; induction I; simpl in |- *; intros X X0 X1 X2 H; 
 red in |- *; intros t Ht;
 inversion_clear Ht; simpl in |- *; try inversion_clear X;
 try inversion_clear X0; try inversion_clear X1; try inversion_clear X2;
 try split.
apply less_leEq_trans with (Min x z); try apply less_Min; auto.
apply leEq_less_trans with (Max y w); try apply Max_less; auto.
apply leEq_transitive with (Min x z); try apply leEq_Min; auto.
apply leEq_transitive with (Max y w); try apply Max_leEq; auto.
apply less_leEq_trans with (Min x z); try apply less_Min; auto.
apply leEq_less_trans with (Max y w); try apply Max_less; auto.
apply less_leEq_trans with (Min x z); try apply less_Min; auto.
apply leEq_transitive with (Max y w); try apply Max_leEq; auto.
apply leEq_transitive with (Min x z); try apply leEq_Min; auto.
apply leEq_less_trans with (Max y w); try apply Max_less; auto.
apply leEq_transitive with (Min x z); try apply leEq_Min; auto.
apply leEq_transitive with (Max y w); try apply Max_leEq; auto.
Qed.

Lemma included_interval : forall (I : interval) x y, I x -> I y ->
 forall H, included (compact (Min x y) (Max x y) H) I.
intros; apply included_interval'; auto.
Qed.

(**
A weirder inclusion result.
*)

Lemma included3_interval : forall (I : interval) x y z Hxyz, I x -> I y -> I z ->
 included (compact (Min (Min x y) z) (Max (Max x y) z) Hxyz) I.
intros I x y z Hxyz H H0 H1.
apply included_interval'; auto.
apply (included_interval I x y H H0 (Min_leEq_Max _ _)).
apply compact_inc_lft.
apply (included_interval I x y H H0 (Min_leEq_Max _ _)).
apply compact_inc_rht.
Qed.

(**
Finally, all intervals are characterized by well defined predicates.
*)

Lemma iprop_wd : forall I : interval, pred_wd _ I.
induction I; unfold iprop in |- *; red in |- *; intros x y X X0;
 try inversion_clear X; try inversion X0.
auto.
astepr x; auto.
astepl x; auto.
astepr x; auto.
astepl x; auto.
split.
astepr x; auto.
astepl x; auto.
split.
astepr x; auto.
astepl x; auto.
split.
astepr x; auto.
astepl x; auto.
split.
astepr x; auto.
astepl x; auto.
Qed.

End Intervals.

Implicit Arguments Lend [I].
Implicit Arguments Rend [I].

Section Compact_Constructions.

Section Single_Compact_Interval.

(** **Constructions with Compact Intervals

Several important constructions are now discussed.

We begin by defining the compact interval [[x,x]].

%\begin{convention}% Let [P:IR->CProp] be well defined, and [x:IR]
such that [P(x)] holds.
%\end{convention}%
*)

Variable P : IR -> CProp.
Hypothesis wdP : pred_wd IR P.
Variable x : IR.

Hypothesis Hx : P x.

Definition compact_single := Compact (leEq_reflexive _ x).

(**
This interval contains [x] and only (elements equal to) [x]; furthermore, for every (well-defined) [P], if $x\in P$#x&isin;P# then $[x,x]\subseteq P$#[x,x]&sube;P#.
*)

Lemma compact_single_prop : compact_single x.
split; apply leEq_reflexive.
Qed.

Lemma compact_single_pt : forall y : IR, compact_single y -> x [=] y.
intros y H.
inversion_clear H; apply leEq_imp_eq; auto.
Qed.

Lemma compact_single_inc : included compact_single P.
red in |- *; intros.
apply wdP with x.
auto.
apply compact_single_pt; auto.
Qed.

End Single_Compact_Interval.

(**
The special case of intervals is worth singling out, as one of the hypothesis becomes a theorem.
*)

Definition compact_single_iprop I := compact_single_inc _ (iprop_wd I).

(**
Now for more interesting and important results.

Let [I] be a proper interval and [x] be a point of [I].  Then there is
a proper compact interval [[a,b]] such that $x\in[a,b]\subseteq
I$#x&isin;[a,b]&sube;I#.
*)

Section Proper_Compact_with_One_or_Two_Points.

(* begin hide *)
Let cip1' : forall c x : IR, c [<=] x -> x[-] (x[-]c) [/]TwoNZ [<=] x.
intros.
astepr (x[-]Zero).
unfold cg_minus at 1 3 in |- *; apply plus_resp_leEq_lft.
apply inv_resp_leEq; apply shift_leEq_div.
apply pos_two.
apply shift_leEq_minus; rstepl c; auto.
Qed.

Let cip1'' : forall c x : IR, c [<] x -> x[-] (x[-]c) [/]TwoNZ [<] x.
intros.
astepr (x[-]Zero).
unfold cg_minus at 1 3 in |- *; apply plus_resp_less_lft.
apply inv_resp_less; apply shift_less_div.
apply pos_two.
apply shift_less_minus; rstepl c; auto.
Qed.

Let cip1''' : forall c0 x : IR, x [<=] c0 -> x [<=] x[+] (c0[-]x) [/]TwoNZ.
intros.
astepl (x[+]Zero).
apply plus_resp_leEq_lft.
apply shift_leEq_div.
apply pos_two.
apply shift_leEq_minus; rstepl x; auto.
Qed.

Let cip1'''' : forall c0 x : IR, x [<] c0 -> x [<] x[+] (c0[-]x) [/]TwoNZ.
intros.
astepl (x[+]Zero).
apply plus_resp_less_lft.
apply shift_less_div.
apply pos_two.
apply shift_less_minus; rstepl x; auto.
Qed.

Let cip2 :
  forall c x x0 : IR, c [<=] x -> x[-] (x[-]c) [/]TwoNZ [<=] x0 -> c [<=] x0.
intros.
apply leEq_transitive with (c[+] (x[-]c) [/]TwoNZ).
astepl (c[+]Zero); apply plus_resp_leEq_lft.
apply shift_leEq_div.
apply pos_two.
apply shift_leEq_minus; rstepl c; auto.
eapply leEq_wdl.
apply H0.
rational.
Qed.

Let cip2' : forall c x x0 : IR, c [<] x -> x[-] (x[-]c) [/]TwoNZ [<=] x0 -> c [<] x0.
intros c x x0 H H0.
apply less_leEq_trans with (c[+] (x[-]c) [/]TwoNZ).
astepl (c[+]Zero); apply plus_resp_less_lft.
apply shift_less_div.
apply pos_two.
apply shift_less_minus; rstepl c; auto.
eapply leEq_wdl.
apply H0.
rational.
Qed.

Let cip2'' :
  forall c x x0 : IR, c [<=] x -> x[-] (x[-]c) [/]TwoNZ [<] x0 -> c [<] x0.
intros c x x0 H H0.
apply leEq_less_trans with (c[+] (x[-]c) [/]TwoNZ).
astepl (c[+]Zero); apply plus_resp_leEq_lft.
apply shift_leEq_div.
apply pos_two.
apply shift_leEq_minus; rstepl c; auto.
eapply less_wdl.
apply H0.
rational.
Qed.

Let cip2''' :
  forall c x x0 : IR, c [<] x -> x[-] (x[-]c) [/]TwoNZ [<] x0 -> c [<] x0.
intros c x x0 H H0.
apply cip2'' with x.
apply less_leEq; auto.
auto.
Qed.

Let cip3 :
  forall c0 x x0 : IR, x [<=] c0 -> x0 [<=] x[+] (c0[-]x) [/]TwoNZ -> x0 [<=] c0.
intros c0 x x0 H H0.
eapply leEq_transitive.
apply H0.
rstepl (c0[-] (c0[-]x) [/]TwoNZ).
astepr (c0[-]Zero); unfold cg_minus at 1 3 in |- *; apply plus_resp_leEq_lft.
apply inv_resp_leEq.
apply shift_leEq_div.
apply pos_two.
apply shift_leEq_minus; rstepl x; auto.
Qed.

Let cip3' :
  forall c0 x x0 : IR, x [<] c0 -> x0 [<=] x[+] (c0[-]x) [/]TwoNZ -> x0 [<] c0.
intros c0 x x0 H H0.
eapply leEq_less_trans.
apply H0.
rstepl (c0[-] (c0[-]x) [/]TwoNZ).
astepr (c0[-]Zero); unfold cg_minus at 1 3 in |- *; apply plus_resp_less_lft.
apply inv_resp_less.
apply shift_less_div.
apply pos_two.
apply shift_less_minus; rstepl x; auto.
Qed.

Let cip3'' :
  forall c0 x x0 : IR, x [<=] c0 -> x0 [<] x[+] (c0[-]x) [/]TwoNZ -> x0 [<] c0.
intros c0 x x0 H H0.
eapply less_leEq_trans.
apply H0.
rstepl (c0[-] (c0[-]x) [/]TwoNZ).
astepr (c0[-]Zero); unfold cg_minus at 1 3 in |- *; apply plus_resp_leEq_lft.
apply inv_resp_leEq.
apply shift_leEq_div.
apply pos_two.
apply shift_leEq_minus; rstepl x; auto.
Qed.

Let cip3''' :
  forall c0 x x0 : IR, x [<] c0 -> x0 [<] x[+] (c0[-]x) [/]TwoNZ -> x0 [<] c0.
intros c0 x x0 H H0.
apply cip3'' with x; try apply less_leEq; auto.
Qed.
(* end hide *)

Definition compact_in_interval I (pI : proper I) x (Hx : I x) : interval.
intros; elim I; intros.
apply (clcr x (x[+]One)).
apply (clcr x (x[+]One)).
apply (clcr (x[-]One) x).
apply (clcr x (x[+]One)).
apply (clcr (x[-]One) x).
apply (clcr (x[-] (x[-]c) [/]TwoNZ) (x[+] (c0[-]x) [/]TwoNZ)).
apply (clcr (x[-] (x[-]c) [/]TwoNZ) (x[+] (c0[-]x) [/]TwoNZ)).
apply (clcr (x[-] (x[-]c) [/]TwoNZ) (x[+] (c0[-]x) [/]TwoNZ)).
apply (clcr c c0).
Defined.

Lemma compact_compact_in_interval : forall I pI x Hx,
 compact_ (compact_in_interval I pI x Hx).
intro.
elim I; simpl in |- *; intros; try inversion_clear Hx; try apply ts;
 apply less_leEq.
apply less_plusOne.
apply less_plusOne.
apply shift_minus_less; apply less_plusOne.
apply less_plusOne.
apply shift_minus_less; apply less_plusOne.
eapply less_transitive_unfolded; [ apply cip1'' | apply cip1'''' ]; auto.
eapply less_leEq_trans; [ apply cip1'' | apply cip1''' ]; auto.
eapply leEq_less_trans; [ apply cip1' | apply cip1'''' ]; auto.
auto.
Qed.

Lemma proper_compact_in_interval : forall I pI x Hx,
 proper (compact_in_interval I pI x Hx).
intro.
elim I; simpl in |- *; intros; try inversion_clear Hx.
apply less_plusOne.
apply less_plusOne.
apply shift_minus_less; apply less_plusOne.
apply less_plusOne.
apply shift_minus_less; apply less_plusOne.
eapply less_transitive_unfolded; [ apply cip1'' | apply cip1'''' ]; auto.
eapply less_leEq_trans; [ apply cip1'' | apply cip1''' ]; auto.
eapply leEq_less_trans; [ apply cip1' | apply cip1'''' ]; auto.
auto.
Qed.

Lemma proper_compact_in_interval' : forall I pI x Hx
 (H : compact_ (compact_in_interval I pI x Hx)), Lend H [<] Rend H.
do 4 intro.
cut (proper (compact_in_interval I pI x Hx)).
2: apply proper_compact_in_interval.
elim (compact_in_interval I pI x Hx); intros; try inversion H.
simpl in |- *; simpl in H; auto.
Qed.

Lemma included_compact_in_interval : forall I pI x Hx,
 included (compact_in_interval I pI x Hx) I.
induction I; simpl in |- *; intros X x X0; try inversion_clear Hx; red in |- *;
 simpl in |- *; intros x0 X1; try inversion_clear X; try inversion_clear X0;
 try inversion_clear X1; auto.
apply less_leEq_trans with x; auto.
apply leEq_less_trans with x; auto.
apply leEq_transitive with x; auto.
apply leEq_transitive with x; auto.
split.
apply cip2' with x; auto.
apply cip3' with x; auto.
split.
apply cip2' with x; auto.
apply cip3 with x; auto.
split.
apply cip2 with x; auto.
apply cip3' with x; auto.
Qed.

Lemma iprop_compact_in_interval : forall I pI x Hx, compact_in_interval I pI x Hx x.
intro.
elim I; simpl in |- *; intros; try inversion_clear Hx; split; auto;
 try apply leEq_reflexive.
apply less_leEq; apply less_plusOne.
apply less_leEq; apply less_plusOne.
apply less_leEq; apply shift_minus_less; apply less_plusOne.
apply less_leEq; apply less_plusOne.
apply less_leEq; apply shift_minus_less; apply less_plusOne.
apply less_leEq; apply cip1''; auto.
apply less_leEq; apply cip1''''; auto.
apply less_leEq; apply cip1''; auto.
apply less_leEq; apply cip1''''; auto.
Qed.

Lemma iprop_compact_in_interval' : forall I pI x Hx
 (H : compact_ (compact_in_interval I pI x Hx)) H', compact (Lend H) (Rend H) H' x.
do 4 intro.
cut (compact_in_interval I pI x Hx x).
2: apply iprop_compact_in_interval.
elim (compact_in_interval I pI x Hx); intros; try inversion H.
simpl in |- *; auto.
Qed.

Lemma iprop_compact_in_interval_inc1 : forall I pI x Hx
 (H : compact_ (compact_in_interval I pI x Hx)) H',
 included (compact (Lend H) (Rend H) H') (compact_in_interval I pI x Hx).
do 4 intro.
elim (compact_in_interval I pI x Hx); intros; try inversion H.
unfold compact in |- *; simpl in |- *; Included.
Qed.

Lemma iprop_compact_in_interval_inc2 : forall I pI x Hx
 (H : compact_ (compact_in_interval I pI x Hx)) H',
 included (compact_in_interval I pI x Hx) (compact (Lend H) (Rend H) H').
do 4 intro.
elim (compact_in_interval I pI x Hx); intros; try inversion H.
unfold compact in |- *; simpl in |- *; Included.
Qed.

(**
If [x [=] y] then the construction yields the same interval whether we
use [x] or [y] in its definition.  This property is required at some
stage, which is why we formalized this result as a functional
definition rather than as an existential formula.
*)

Lemma compact_in_interval_wd1 : forall I pI x Hx y Hy
 (H : compact_ (compact_in_interval I pI x Hx))
 (H' : compact_ (compact_in_interval I pI y Hy)),
 x [=] y -> Lend H [=] Lend H'.
intro I; elim I; simpl in |- *; intros; algebra.
Qed.

Lemma compact_in_interval_wd2 : forall I pI x Hx y Hy
 (H : compact_ (compact_in_interval I pI x Hx))
 (H' : compact_ (compact_in_interval I pI y Hy)),
 x [=] y -> Rend H [=] Rend H'.
intro I; elim I; simpl in |- *; intros; algebra.
Qed.

(**
We can make an analogous construction for two points.
*)

Definition compact_in_interval2 I (pI : proper I) x y : I x -> I y -> interval.
intros.
set (z1 := Min x y) in *.
set (z2 := Max x y) in *.
elim I; intros.
apply (clcr z1 (z2[+]One)).
apply (clcr z1 (z2[+]One)).
apply (clcr (z1[-]One) z2).
apply (clcr z1 (z2[+]One)).
apply (clcr (z1[-]One) z2).
apply (clcr (z1[-] (z1[-]c) [/]TwoNZ) (z2[+] (c0[-]z2) [/]TwoNZ)).
apply (clcr (z1[-] (z1[-]c) [/]TwoNZ) (z2[+] (c0[-]z2) [/]TwoNZ)).
apply (clcr (z1[-] (z1[-]c) [/]TwoNZ) (z2[+] (c0[-]z2) [/]TwoNZ)).
apply (clcr c c0).
Defined.

Lemma compact_compact_in_interval2 : forall I pI x y Hx Hy,
 compact_ (compact_in_interval2 I pI x y Hx Hy).
intro.
elim I; simpl in |- *; intros; try inversion_clear Hx; try inversion_clear Hy;
 try apply ts; apply less_leEq.
apply leEq_less_trans with (Max x y);
 [ apply Min_leEq_Max | apply less_plusOne ].
apply leEq_less_trans with (Max x y);
 [ apply Min_leEq_Max | apply less_plusOne ].
apply shift_minus_less; apply leEq_less_trans with (Max x y);
 [ apply Min_leEq_Max | apply less_plusOne ].
apply leEq_less_trans with (Max x y);
 [ apply Min_leEq_Max | apply less_plusOne ].
apply shift_minus_less; apply leEq_less_trans with (Max x y);
 [ apply Min_leEq_Max | apply less_plusOne ].
eapply less_transitive_unfolded;
 [ apply cip1''
 | eapply leEq_less_trans; [ apply Min_leEq_Max | apply cip1'''' ] ];
 try apply less_Min; try apply Max_less; auto.
eapply less_leEq_trans;
 [ apply cip1''
 | eapply leEq_transitive; [ apply Min_leEq_Max | apply cip1''' ] ];
 try apply less_Min; try apply Max_leEq; auto.
eapply leEq_less_trans;
 [ apply cip1'
 | eapply leEq_less_trans; [ apply Min_leEq_Max | apply cip1'''' ] ];
 try apply leEq_Min; try apply Max_less; auto.
auto.
Qed.

Lemma proper_compact_in_interval2 : forall I pI x y Hx Hy,
 proper (compact_in_interval2 I pI x y Hx Hy).
intro.
elim I; simpl in |- *; intros; try inversion_clear Hx; try inversion_clear Hy.
apply leEq_less_trans with (Max x y);
 [ apply Min_leEq_Max | apply less_plusOne ].
apply leEq_less_trans with (Max x y);
 [ apply Min_leEq_Max | apply less_plusOne ].
apply shift_minus_less; apply leEq_less_trans with (Max x y);
 [ apply Min_leEq_Max | apply less_plusOne ].
apply leEq_less_trans with (Max x y);
 [ apply Min_leEq_Max | apply less_plusOne ].
apply shift_minus_less; apply leEq_less_trans with (Max x y);
 [ apply Min_leEq_Max | apply less_plusOne ].
eapply less_transitive_unfolded;
 [ apply cip1''
 | eapply leEq_less_trans; [ apply Min_leEq_Max | apply cip1'''' ] ];
 try apply less_Min; try apply Max_less; auto.
eapply less_leEq_trans;
 [ apply cip1''
 | eapply leEq_transitive; [ apply Min_leEq_Max | apply cip1''' ] ];
 try apply less_Min; try apply Max_leEq; auto.
eapply leEq_less_trans;
 [ apply cip1'
 | eapply leEq_less_trans; [ apply Min_leEq_Max | apply cip1'''' ] ];
 try apply leEq_Min; try apply Max_less; auto.
auto.
Qed.

Lemma proper_compact_in_interval2' : forall I pI x y Hx Hy H,
 Lend (I:=compact_in_interval2 I pI x y Hx Hy) H [<] 
   Rend (I:=compact_in_interval2 I pI x y Hx Hy) H.
do 6 intro.
cut (proper (compact_in_interval2 I pI x y Hx Hy)).
2: apply proper_compact_in_interval2.
elim (compact_in_interval2 I pI x y Hx Hy); intros; try inversion H.
simpl in |- *; simpl in H; auto.
Qed.

Lemma included_compact_in_interval2 : forall I pI x y Hx Hy,
 included (compact_in_interval2 I pI x y Hx Hy) I.
induction I; simpl in |- *; intros; try inversion_clear Hx as (H,H0);
 try inversion_clear Hy as (H1,H2); red in |- *; simpl in |- *;
 intros x0 X; try inversion_clear X; auto.
apply less_leEq_trans with (Min x y); try apply less_Min; auto.
apply leEq_less_trans with (Max x y); try apply Max_less; auto.
apply leEq_transitive with (Min x y); try apply leEq_Min; auto.
apply leEq_transitive with (Max x y); try apply Max_leEq; auto.
split.
apply cip2' with (Min x y); try apply less_Min; auto.
apply cip3' with (Max x y); try apply Max_less; auto.
split.
apply cip2' with (Min x y); try apply less_Min; auto.
apply cip3 with (Max x y); try apply Max_leEq; auto.
split.
apply cip2 with (Min x y); try apply leEq_Min; auto.
apply cip3' with (Max x y); try apply Max_less; auto.
Qed.

Lemma iprop_compact_in_interval2x : forall I pI x y Hx Hy,
 compact_in_interval2 I pI x y Hx Hy x.
intro.
elim I; simpl in |- *; intros; try inversion_clear Hx; try inversion_clear Hy;
 split; auto; try apply Min_leEq_lft; try apply lft_leEq_Max.
apply less_leEq; apply leEq_less_trans with (Max x y);
 [ apply lft_leEq_Max | apply less_plusOne ].
apply less_leEq; apply leEq_less_trans with (Max x y);
 [ apply lft_leEq_Max | apply less_plusOne ].
apply less_leEq; apply shift_minus_less; apply leEq_less_trans with x;
 [ apply Min_leEq_lft | apply less_plusOne ].
apply less_leEq; apply leEq_less_trans with (Max x y);
 [ apply lft_leEq_Max | apply less_plusOne ].
apply less_leEq; apply shift_minus_less; apply leEq_less_trans with x;
 [ apply Min_leEq_lft | apply less_plusOne ].
apply less_leEq; eapply less_leEq_trans;
 [ apply cip1'' | apply Min_leEq_lft ]; try apply less_Min; 
 auto.
apply less_leEq; apply leEq_less_trans with (Max x y);
 [ apply lft_leEq_Max | apply cip1'''' ]; try apply Max_less; 
 auto.
apply less_leEq; eapply less_leEq_trans;
 [ apply cip1'' | apply Min_leEq_lft ]; try apply less_Min; 
 auto.
apply leEq_transitive with (Max x y); [ apply lft_leEq_Max | apply cip1''' ];
 try apply Max_leEq; auto.
eapply leEq_transitive; [ apply cip1' | apply Min_leEq_lft ];
 try apply leEq_Min; auto.
apply less_leEq; apply leEq_less_trans with (Max x y);
 [ apply lft_leEq_Max | apply cip1'''' ]; try apply Max_less; 
 auto.
Qed.

Lemma iprop_compact_in_interval2y : forall I pI x y Hx Hy,
 compact_in_interval2 I pI x y Hx Hy y.
intro.
elim I; simpl in |- *; intros; try inversion_clear Hx; try inversion_clear Hy;
 split; auto; try apply Min_leEq_rht; try apply rht_leEq_Max.
apply less_leEq; apply leEq_less_trans with (Max x y);
 [ apply rht_leEq_Max | apply less_plusOne ].
apply less_leEq; apply leEq_less_trans with (Max x y);
 [ apply rht_leEq_Max | apply less_plusOne ].
apply less_leEq; apply shift_minus_less; apply leEq_less_trans with y;
 [ apply Min_leEq_rht | apply less_plusOne ].
apply less_leEq; apply leEq_less_trans with (Max x y);
 [ apply rht_leEq_Max | apply less_plusOne ].
apply less_leEq; apply shift_minus_less; apply leEq_less_trans with y;
 [ apply Min_leEq_rht | apply less_plusOne ].
apply less_leEq; eapply less_leEq_trans;
 [ apply cip1'' | apply Min_leEq_rht ]; try apply less_Min; 
 auto.
apply less_leEq; apply leEq_less_trans with (Max x y);
 [ apply rht_leEq_Max | apply cip1'''' ]; try apply Max_less; 
 auto.
apply less_leEq; eapply less_leEq_trans;
 [ apply cip1'' | apply Min_leEq_rht ]; try apply less_Min; 
 auto.
apply leEq_transitive with (Max x y); [ apply rht_leEq_Max | apply cip1''' ];
 try apply Max_leEq; auto.
eapply leEq_transitive; [ apply cip1' | apply Min_leEq_rht ];
 try apply leEq_Min; auto.
apply less_leEq; apply leEq_less_trans with (Max x y);
 [ apply rht_leEq_Max | apply cip1'''' ]; try apply Max_less; 
 auto.
Qed.

Lemma iprop_compact_in_interval2x' : forall I pI x y Hx Hy
 (H : compact_ (compact_in_interval2 I pI x y Hx Hy)) H',
 compact (Lend H) (Rend H) H' x.
do 6 intro.
cut (compact_in_interval2 I pI x y Hx Hy x).
2: apply iprop_compact_in_interval2x.
elim (compact_in_interval2 I pI x y Hx Hy); intros; try inversion H.
simpl in |- *; auto.
Qed.

Lemma iprop_compact_in_interval2y' : forall I pI x y Hx Hy
 (H : compact_ (compact_in_interval2 I pI x y Hx Hy)) H',
 compact (Lend H) (Rend H) H' y.
do 6 intro.
cut (compact_in_interval2 I pI x y Hx Hy y).
2: apply iprop_compact_in_interval2y.
elim (compact_in_interval2 I pI x y Hx Hy); intros; try inversion H.
simpl in |- *; auto.
Qed.

Lemma iprop_compact_in_interval2_inc1 : forall I pI x y Hx Hy
 (H : compact_ (compact_in_interval2 I pI x y Hx Hy)) H',
 included (compact (Lend H) (Rend H) H') (compact_in_interval2 I pI x y Hx Hy).
do 6 intro.
elim (compact_in_interval2 I pI x y Hx Hy); intros; try inversion H.
unfold compact in |- *; unfold iprop in |- *; simpl in |- *; Included.
Qed.

Lemma iprop_compact_in_interval2_inc2 : forall I pI x y Hx Hy
 (H : compact_ (compact_in_interval2 I pI x y Hx Hy)) H',
 included (compact_in_interval2 I pI x y Hx Hy) (compact (Lend H) (Rend H) H').
do 6 intro.
elim (compact_in_interval2 I pI x y Hx Hy); intros; try inversion H.
unfold compact in |- *; unfold iprop in |- *; simpl in |- *; Included.
Qed.

Lemma compact_in_interval_x_lft : forall I pI x y Hx Hy H H',
 Lend (I:=compact_in_interval2 I pI x y Hx Hy) H [<=] 
   Lend (I:=compact_in_interval I pI x Hx) H'.
intro I; elim I; simpl in |- *; intros; try apply minus_resp_leEq;
 try apply Min_leEq_lft; try apply leEq_reflexive;
 (rstepl (c[+] (Min x y[-]c) [/]TwoNZ); rstepr (c[+] (x[-]c) [/]TwoNZ);
   apply plus_resp_leEq_lft; apply div_resp_leEq;
   [ apply pos_two | apply minus_resp_leEq; apply Min_leEq_lft ]).
Qed.

Lemma compact_in_interval_y_lft : forall I pI x y Hx Hy H H',
 Lend (I:=compact_in_interval2 I pI x y Hx Hy) H [<=] 
   Lend (I:=compact_in_interval I pI y Hy) H'.
intro I; elim I; simpl in |- *; intros; try apply minus_resp_leEq;
 try apply Min_leEq_rht; try apply leEq_reflexive;
 (rstepl (c[+] (Min x y[-]c) [/]TwoNZ); rstepr (c[+] (y[-]c) [/]TwoNZ);
   apply plus_resp_leEq_lft; apply div_resp_leEq;
   [ apply pos_two | apply minus_resp_leEq; apply Min_leEq_rht ]).
Qed.

Lemma compact_in_interval_x_rht : forall I pI x y Hx Hy H H',
 Rend (I:=compact_in_interval I pI x Hx) H [<=] 
   Rend (I:=compact_in_interval2 I pI x y Hx Hy) H'.
intro I; elim I; simpl in |- *; intros; try apply plus_resp_leEq;
 try apply lft_leEq_Max; try apply leEq_reflexive;
 (rstepl (c0[-] (c0[-]x) [/]TwoNZ); rstepr (c0[-] (c0[-]Max x y) [/]TwoNZ);
   unfold cg_minus in |- *; apply plus_resp_leEq_lft; 
   apply inv_resp_leEq; apply div_resp_leEq;
   [ apply pos_two
   | apply plus_resp_leEq_lft; apply inv_resp_leEq; apply lft_leEq_Max ]).
Qed.

Lemma compact_in_interval_y_rht : forall I pI x y Hx Hy H H',
 Rend (I:=compact_in_interval I pI y Hy) H [<=] 
   Rend (I:=compact_in_interval2 I pI x y Hx Hy) H'.
intro I; elim I; simpl in |- *; intros; try apply plus_resp_leEq;
 try apply rht_leEq_Max; try apply leEq_reflexive;
 (rstepl (c0[-] (c0[-]y) [/]TwoNZ); rstepr (c0[-] (c0[-]Max x y) [/]TwoNZ);
   unfold cg_minus in |- *; apply plus_resp_leEq_lft; 
   apply inv_resp_leEq; apply div_resp_leEq;
   [ apply pos_two
   | apply plus_resp_leEq_lft; apply inv_resp_leEq; apply rht_leEq_Max ]).
Qed.

End Proper_Compact_with_One_or_Two_Points.

(**
Compact intervals are exactly compact intervals(!).
*)

Lemma interval_compact_inc : forall I (cI : compact_ I) H,
 included I (compact (Lend cI) (Rend cI) H).
intro.
elim I; intros; try inversion cI.
generalize c c0 cI H; clear H cI c0 c.
simpl in |- *; intros a b Hab Hab'.
intros x H.
simpl in H.
inversion_clear H; split; auto.
Qed.

Lemma compact_interval_inc : forall I (cI : compact_ I) H,
 included (compact (Lend cI) (Rend cI) H) I.
intro.
elim I; intros; try inversion cI.
generalize c c0 cI H; clear H cI c0 c.
simpl in |- *; intros a b Hab.
intros H x H0.
inversion_clear H0; split; auto.
Qed.

(**
A generalization of the previous results: if $[a,b]\subseteq J$#[a,b]&sube;J#
and [J] is proper, then we can find a proper interval [[a',b']] such that
$[a,b]\subseteq[a',b']\subseteq J$#[a,b]&sube;[a',b']&sube;J#.
*)

Lemma compact_proper_in_interval : forall (J : interval) a b Hab,
 included (compact a b Hab) J -> proper J -> {a' : IR | {b' : IR | {Hab' : _ |
 included (compact a' b' (less_leEq _ _ _ Hab')) J |
   included (Compact Hab) (Compact (less_leEq _ _ _ Hab'))}}}.
intros J a b Hab H H0.
exists
 (Lend
    (compact_compact_in_interval2 J H0 a b (H _ (compact_inc_lft _ _ Hab))
       (H _ (compact_inc_rht _ _ Hab)))).
exists
 (Rend
    (compact_compact_in_interval2 J H0 a b (H _ (compact_inc_lft _ _ Hab))
       (H _ (compact_inc_rht _ _ Hab)))).
exists
 (proper_compact_in_interval2' _ _ _ _ _ _
    (compact_compact_in_interval2 J H0 a b (H _ (compact_inc_lft _ _ Hab))
       (H _ (compact_inc_rht _ _ Hab)))).
eapply included_trans.
apply compact_interval_inc.
apply included_compact_in_interval2.
apply included_compact.
apply iprop_compact_in_interval2x'.
apply iprop_compact_in_interval2y'.
Qed.

End Compact_Constructions.

Section Functions.

(** **Properties of Functions in Intervals

We now define notions of continuity, differentiability and so on on
arbitrary intervals.  As expected, a function [F] has property [P] in
the (proper) interval [I] iff it has property [P] in every compact
interval included in [I].  We can formalize this in a nice way using
previously defined concepts.

%\begin{convention}% Let [n:nat] and [I:interval].
%\end{convention}%
*)

Variable n : nat.
Variable I : interval.

Definition Continuous F := included I (Dom F) and (forall a b (Hab : a [<=] b),
 included (Compact Hab) I -> Continuous_I Hab F).

Definition Derivative (pI : proper I) F G := included I (Dom F) and included I (Dom G) and (forall a b Hab,
 included (Compact (less_leEq _ a b Hab)) I -> Derivative_I Hab F G).

Definition Diffble (pI : proper I) F := included I (Dom F) and (forall a b Hab,
 included (Compact (less_leEq _ a b Hab)) I -> Diffble_I Hab F).

Definition Derivative_n (pI : proper I) F G := included I (Dom F) and included I (Dom G) and
 (forall a b Hab, included (Compact (less_leEq _ a b Hab)) I -> Derivative_I_n Hab n F G).

Definition Diffble_n (pI : proper I) F := included I (Dom F) and (forall a b Hab,
 included (Compact (less_leEq _ a b Hab)) I -> Diffble_I_n Hab n F).

End Functions.

Section Reflexivity_Properties.

(**
In the case of compact intervals, this definitions collapse to the old ones.
*)

Lemma Continuous_Int :
 forall (I : interval) (cI : compact_ I) H (F : PartIR),
 Continuous_I (a:=Lend cI) (b:=Rend cI) H F -> Continuous I F.
intros I cI H F H0.
cut (included I (compact (Lend cI) (Rend cI) H)).
2: apply interval_compact_inc; auto.
cut (included (compact (Lend cI) (Rend cI) H) I).
2: apply compact_interval_inc; auto.
generalize cI H H0; clear H0 H cI.
elim I; intros; try inversion cI.
generalize c c0 cI H H0 X X0; clear X0 X H0 H cI c0 c.
simpl in |- *; intros a b Hab Hab' contF inc1 inc2.
split.
apply included_trans with (Compact Hab'); Included.
intros.
apply included_imp_contin with (Hab := Hab'); Included.
Qed.

Lemma Int_Continuous :
 forall (I : interval) (cI : compact_ I) H (F : PartIR),
 Continuous I F -> Continuous_I (a:=Lend cI) (b:=Rend cI) H F.
intro.
elim I; intros; try inversion cI.
generalize c c0 cI H F X; clear X F H cI c0 c.
simpl in |- *; intros a b Hab Hab' F contF.
inversion_clear contF.
Contin.
Qed.

Lemma Derivative_Int :
 forall (I : interval) (cI : compact_ I) (pI : proper I) H (F F' : PartIR),
 Derivative_I (a:=Lend cI) (b:=Rend cI) H F F' -> Derivative I pI F F'.
do 4 intro.
cut (included I (compact (Lend cI) (Rend cI) (less_leEq _ _ _ H))).
2: apply interval_compact_inc; auto.
cut (included (compact (Lend cI) (Rend cI) (less_leEq _ _ _ H)) I).
2: apply compact_interval_inc; auto.
generalize cI pI H; clear H cI pI.
elim I; intros; try inversion cI.
generalize c c0 cI pI H X X0 F F' X1; clear X1 F' F X0 X H pI cI c0 c.
simpl in |- *; intros a b Hab Hnonv Hab' inc1 inc2 F F' derF.
split.
apply included_trans with (Compact (less_leEq _ _ _ Hab')); Included.
split.
apply included_trans with (Compact (less_leEq _ _ _ Hab')); Included.
intros c d Hcd' Hinc.
apply included_imp_deriv with (Hab := Hab'); Included.
Qed.

Lemma Int_Derivative :
 forall (I : interval) (cI : compact_ I) (pI : proper I) H (F F' : PartIR),
 Derivative I pI F F' -> Derivative_I (a:=Lend cI) (b:=Rend cI) H F F'.
intro.
elim I; intros; try inversion cI.
generalize c c0 cI pI H F F' X; clear X F' F H pI cI c0 c.
simpl in |- *; intros a b Hab Hnonv Hab' F F' derF.
elim derF; intros H H0.
elim H0; intros H1 H2.
Included.
Qed.

Lemma Diffble_Int :
 forall (I : interval) (cI : compact_ I) (pI : proper I) H (F : PartIR),
 Diffble_I (a:=Lend cI) (b:=Rend cI) H F -> Diffble I pI F.
do 4 intro.
cut (included I (compact (Lend cI) (Rend cI) (less_leEq _ _ _ H))).
2: apply interval_compact_inc; auto.
cut (included (compact (Lend cI) (Rend cI) (less_leEq _ _ _ H)) I).
2: apply compact_interval_inc; auto.
generalize cI pI H; clear H pI cI.
elim I; intros; try inversion cI.
generalize c c0 cI pI H X X0 F X1; clear X1 F X0 X H pI cI c0 c.
simpl in |- *; intros a b Hab Hnonv Hab' inc1 inc2 F diffF.
red in |- *; simpl in |- *.
split.
apply included_trans with (Compact (less_leEq _ _ _ Hab')); Included.
intros c d Hcd' Hinc.
apply included_imp_diffble with (Hab := Hab'); auto.
Qed.

Lemma Int_Diffble :
 forall (I : interval) (cI : compact_ I) (pI : proper I) H (F : PartIR),
 Diffble I pI F -> Diffble_I (a:=Lend cI) (b:=Rend cI) H F.
intro.
elim I; intros; try inversion cI.
generalize c c0 cI pI H F X; clear X F H pI cI c0 c.
simpl in |- *; intros a b Hab Hnonv Hab' F diffF.
inversion_clear diffF.
Included.
Qed.

End Reflexivity_Properties.

Section Lemmas.

(**
Interestingly, inclusion and equality in an interval are also characterizable in a similar way:
*)

Lemma included_imp_inc : forall (J : interval) P,
 (forall a b Hab, included (compact a b Hab) J -> included (compact a b Hab) P) -> included J P.
intros J P H x H0.
apply (H _ _ (leEq_reflexive _ _) (compact_single_iprop J x H0)).
apply compact_inc_lft.
Qed.

Lemma included_Feq'' : forall I F G, proper I -> (forall a b Hab (Hab':=(less_leEq _ a b Hab)),
 included (Compact Hab') I -> Feq (Compact Hab') F G) -> Feq I F G.
intros I F G H H0.
apply eq_imp_Feq.
intros x H1.
elim (compact_proper_in_interval I x x (leEq_reflexive _ x)); Included.
2: exact (compact_single_iprop I x H1).
intros a Ha.
elim Ha; clear Ha.
intros b Hb.
elim Hb; clear Hb.
intros Hab H2 H3.
elim (H0 _ _ _ H2); intros.
apply a0; apply H3; apply compact_single_prop.
intros x H1.
elim (compact_proper_in_interval I x x (leEq_reflexive _ x)); Included.
2: exact (compact_single_iprop I x H1).
intros a Ha.
elim Ha; clear Ha.
intros b Hb.
elim Hb; clear Hb.
intros Hab H2 H3.
elim (H0 _ _ _ H2); intros.
inversion_clear b0.
apply X; apply H3; apply compact_single_prop.
intros x H1 Hx Hx'.
elim (compact_proper_in_interval I x x (leEq_reflexive _ x)); Included.
2: exact (compact_single_iprop I x H1).
intros a Ha.
elim Ha; clear Ha.
intros b Hb.
elim Hb; clear Hb.
intros Hab H2 H3.
elim (H0 _ _ _ H2); intros.
inversion_clear b0.
apply H4; apply H3; apply compact_single_prop.
Qed.

Lemma included_Feq' : forall (I : interval) F G,
 (forall a b Hab, included (compact a b Hab) I -> Feq (Compact Hab) F G) -> Feq I F G.
intros I F G H.
apply eq_imp_Feq.
intros x H0.
elim (H x x (leEq_reflexive _ x) (compact_single_iprop I x H0)); intros.
apply a; apply compact_single_prop.
intros x H0.
elim (H x x (leEq_reflexive _ x) (compact_single_iprop I x H0)); intros.
inversion_clear b.
apply X; apply compact_single_prop.
intros x H0 Hx Hx'.
elim (H x x (leEq_reflexive _ x) (compact_single_iprop I x H0)); intros.
inversion_clear b.
apply H1; apply compact_single_prop.
Qed.

End Lemmas.

Hint Resolve included_interval included_interval' included3_interval
  compact_single_inc compact_single_iprop included_compact_in_interval
  iprop_compact_in_interval_inc1 iprop_compact_in_interval_inc2
  included_compact_in_interval2 iprop_compact_in_interval2_inc1
  iprop_compact_in_interval2_inc2 interval_compact_inc compact_interval_inc
  iprop_wd: included.
