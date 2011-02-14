(* Copyright © 1998-2008
 * Henk Barendregt
 * Luís Cruz-Filipe
 * Herman Geuvers
 * Mariusz Giero
 * Rik van Ginneken
 * Dimitri Hendriks
 * Sébastien Hinderer
 * Cezary Kaliszyk
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

(** printing != %\ensuremath{\mathrel\#}% *)
(** printing == %\ensuremath{\equiv}% #&equiv;# *)
(** printing [=] %\ensuremath{\equiv}% #&equiv;# *)
(** printing [~=] %\ensuremath{\mathrel{\not\equiv}}% #&ne;# *)
(** printing [#] %\ensuremath{\mathrel\#}% *)
(** printing ex_unq %\ensuremath{\exists^1}% #&exist;<sup>1</sup># *)
(** printing [o] %\ensuremath\circ% #&sdot;# *)
(** printing [-C-] %\ensuremath\diamond% *)

(**
* Setoids
Definition of a constructive setoid with apartness,
i.e.%\% a set with an equivalence relation and an apartness relation compatible with it.
*)

Require Import CornTac.
Require Export CLogic.
Require Export Step.
Require Export RSetoid.

Delimit Scope corn_scope with corn.
Open Scope corn_scope.

Definition Relation := Trelation.

Implicit Arguments Treflexive [A].
Implicit Arguments Creflexive [A].

Implicit Arguments Tsymmetric [A].
Implicit Arguments Csymmetric [A].
Implicit Arguments Ttransitive [A].
Implicit Arguments Ctransitive [A].

(* begin hide *)
Set Implicit Arguments.
Unset Strict Implicit.
(* end hide *)

(**
** Relations necessary for Setoids
%\begin{convention}% Let [A:Type].
%\end{convention}%

Notice that their type depends on the main logical connective.
*)

Section Properties_of_relations.
Variable A : Type.

Definition irreflexive (R : Crelation A) : Prop := forall x : A, Not (R x x).

Definition cotransitive (R : Crelation A) : CProp := forall x y : A,
 R x y -> forall z : A, R x z or R z y.

Definition tight_apart (eq : Relation A) (ap : Crelation A) : Prop := forall x y : A,
 Not (ap x y) <-> eq x y.

Definition antisymmetric (R : Crelation A) : Prop := forall x y : A,
 R x y -> Not (R y x).

End Properties_of_relations.
(* begin hide *)
Set Strict Implicit.
Unset Implicit Arguments.
(* end hide *)

(**
** Definition of Setoid

Apartness, being the main relation, needs to be [CProp]-valued.  Equality,
as it is characterized by a negative statement, lives in [Prop]. *)

Record is_CSetoid (A : Type) (eq : Relation A) (ap : Crelation A) : CProp :=
  {ax_ap_irreflexive  : irreflexive ap;
   ax_ap_symmetric    : Csymmetric ap;
   ax_ap_cotransitive : cotransitive ap;
   ax_ap_tight        : tight_apart eq ap}.

Record CSetoid : Type := makeCSetoid
  {cs_crr   :> RSetoid;
   cs_ap    :  Crelation cs_crr;
   cs_proof :  is_CSetoid cs_crr (@st_eq cs_crr) cs_ap}.

Notation cs_eq := st_eq (only parsing).
Implicit Arguments cs_ap [c].

Infix "[=]" := cs_eq (at level 70, no associativity).
Infix "[#]" := cs_ap (at level 70, no associativity).

(* End_SpecReals *)

Definition cs_neq (S : CSetoid) : Relation S := fun x y : S => ~ x [=] y.

Implicit Arguments cs_neq [S].

Infix "[~=]" := cs_neq (at level 70, no associativity).

(**
%\begin{nameconvention}%
In the names of lemmas, we refer to [ [=] ] by [eq], [ [~=] ] by
[neq], and [ [#] ] by [ap].
%\end{nameconvention}%

** Setoid axioms
We want concrete lemmas that state the axiomatic properties of a setoid.
%\begin{convention}%
Let [S] be a setoid.
%\end{convention}%
*)

(* Begin_SpecReals *)

Section CSetoid_axioms.
Variable S : CSetoid.

Lemma CSetoid_is_CSetoid : is_CSetoid S (cs_eq (r:=S)) (cs_ap (c:=S)).
Proof cs_proof S.

Lemma ap_irreflexive : irreflexive (cs_ap (c:=S)).
Proof.
 elim CSetoid_is_CSetoid; auto.
Qed.

Lemma ap_symmetric : Csymmetric (cs_ap (c:=S)).
Proof.
 elim CSetoid_is_CSetoid; auto.
Qed.

Lemma ap_cotransitive : cotransitive (cs_ap (c:=S)).
Proof.
 elim CSetoid_is_CSetoid; auto.
Qed.

Lemma ap_tight : tight_apart (cs_eq (r:=S)) (cs_ap (c:=S)).
Proof.
 elim CSetoid_is_CSetoid; auto.
Qed.

End CSetoid_axioms.

(**
** Setoid basics%\label{section:setoid-basics}%
%\begin{convention}% Let [S] be a setoid.
%\end{convention}%
*)

Lemma is_CSetoid_Setoid : forall S eq ap, is_CSetoid S eq ap -> Setoid_Theory S eq.
Proof.
 intros S eq ap p.
 destruct p.
 split.
   firstorder.
  intros a b. red in ax_ap_tight0 .
  repeat rewrite <- ax_ap_tight0.
  firstorder.
 intros a b c. red in ax_ap_tight0 .
 repeat rewrite <- ax_ap_tight0.
 intros H H0 H1.
 destruct (ax_ap_cotransitive0 _ _ H1 b); auto.
Qed.

Definition Build_CSetoid (X:Type) (eq:Relation X) (ap:Crelation X) (p:is_CSetoid X eq ap) : CSetoid.
Proof.
 exists (Build_RSetoid (is_CSetoid_Setoid _ _ _ p)) ap.
 assumption.
Defined.

Section CSetoid_basics.
Variable S : CSetoid.

(* End_SpecReals *)

(**
In `there exists a unique [a:S] such that %\ldots%#...#', we now mean unique with respect to the setoid equality. We use [ex_unq] to denote unique existence.
*)

Definition ex_unq (P : S -> CProp) := {x : S | forall y : S, P y -> x [=] y | P x}.

Lemma eq_reflexive : Treflexive (cs_eq (r:=S)).
Proof.
 intro x.
 reflexivity.
Qed.

Lemma eq_symmetric : Tsymmetric (cs_eq (r:=S)).
Proof.
 intro x; intros y H.
 symmetry; assumption.
Qed.

Lemma eq_transitive : Ttransitive (cs_eq (r:=S)).
Proof.
 intro x; intros y z H H0.
 transitivity y; assumption.
Qed.

(**
%\begin{shortcoming}%
The lemma [eq_reflexive] above is convertible to
[eq_reflexive_unfolded] below. We need the second version too,
because the first cannot be applied when an instance of reflexivity is needed.
(``I have complained bitterly about this.'' RP)
%\end{shortcoming}%
tes
%\begin{nameconvention}%
If lemma [a] is just an unfolding of lemma [b], the name of [a] is the name
[b] with the suffix ``[_unfolded]''.
%\end{nameconvention}%
*)

Lemma eq_reflexive_unfolded : forall x : S, x [=] x.
Proof eq_reflexive.

Lemma eq_symmetric_unfolded : forall x y : S, x [=] y -> y [=] x.
Proof eq_symmetric.

Lemma eq_transitive_unfolded : forall x y z : S, x [=] y -> y [=] z -> x [=] z.
Proof eq_transitive.

Lemma eq_wdl : forall x y z : S, x [=] y -> x [=] z -> z [=] y.
Proof.
 intros. now apply (eq_transitive _ x);[apply: eq_symmetric|].
Qed.


Lemma ap_irreflexive_unfolded : forall x : S, Not (x [#] x).
Proof ap_irreflexive S.

Lemma ap_cotransitive_unfolded : forall a b : S, a [#] b -> forall c : S, a [#] c or c [#] b.
Proof.
 intros a b H c.
 exact (ap_cotransitive _ _ _ H c).
Qed.

Lemma ap_symmetric_unfolded : forall x y : S, x [#] y -> y [#] x.
Proof ap_symmetric S.

(**
We would like to write
[[
Lemma eq_equiv_not_ap : forall (x y:S), (x [=] y) iff Not (x [#] y).
]]
In Coq, however, this lemma cannot be easily applied.
Therefore we have to split the lemma into the following two lemmas [eq_imp_not_ap] and [not_ap_imp_eq].
For this we should fix the Prop CProp problem.
*)

Lemma eq_imp_not_ap : forall x y : S, x [=] y -> Not (x [#] y).
Proof.
 intros x y.
 elim (ap_tight S x y).
 intros H1 H2.
 assumption.
Qed.

Lemma not_ap_imp_eq : forall x y : S, Not (x [#] y) -> x [=] y.
Proof.
 intros x y.
 elim (ap_tight S x y).
 intros H1 H2.
 assumption.
Qed.

Lemma neq_imp_notnot_ap : forall x y : S, x [~=] y -> ~ Not (x [#] y).
Proof.
 intros x y H H0.
 now apply: H; apply: not_ap_imp_eq.
Qed.

Lemma notnot_ap_imp_neq : forall x y : S, ~ Not (x [#] y) -> x [~=] y.
Proof.
 intros x y H H0.
 now apply H; apply eq_imp_not_ap.
Qed.

Lemma ap_imp_neq : forall x y : S, x [#] y -> x [~=] y.
Proof.
 intros x y H H1.
 now apply (eq_imp_not_ap _ _ H1).
Qed.

Lemma not_neq_imp_eq : forall x y : S, ~ x [~=] y -> x [=] y.
Proof.
 intros x y H.
 apply: not_ap_imp_eq.
 intros H0.
 apply: H. now apply: ap_imp_neq.
Qed.

Lemma eq_imp_not_neq : forall x y : S, x [=] y -> ~ x [~=] y.
Proof.
 intros x y H H0. easy.
Qed.

End CSetoid_basics.

Section product_csetoid.
(**
** The product of setoids *)

Definition prod_ap (A B : CSetoid) (c d : prodT A B) : CProp.
Proof.
 destruct c as [a b], d as [a0 b0].
 exact (cs_ap (c:=A) a a0 or cs_ap (c:=B) b b0).
Defined.

Definition prod_eq (A B : CSetoid) (c d : prodT A B) : Prop.
Proof.
 destruct c as [a b], d as [a0 b0].
 exact (a [=] a0 /\ b [=] b0).
Defined.


Lemma prodcsetoid_is_CSetoid : forall A B : CSetoid,
 is_CSetoid (prodT A B) (prod_eq A B) (prod_ap A B).
Proof.
 (* Can be shortened *)
 intros A B.
 apply (Build_is_CSetoid _ (prod_eq A B) (prod_ap A B)).
    intros x. case x. intros c c0 H.
    elim H.
     intros H1.
     now apply: (ap_irreflexive A _ H1).
    apply (ap_irreflexive B _ ).
   intros x y. case x. case y.
   intros c c0 c1 c2 H.
   elim H.
    intros.
    left.
    now apply ap_symmetric.
   intros.
   right.
   now apply ap_symmetric.
  intros x y. case x. case y.
  intros c c0 c1 c2 H z. case z.
  intros c3 c4.
  generalize H.
  intros.
  elim H.
   intros.
   cut (c1 [#] c3 or c3 [#] c).
    intros [H1|H2].
     left.
     now left.
    intros.
    right.
    now left.
   now apply: ap_cotransitive.
  intros.
  cut (c2 [#] c4 or c4 [#] c0).
   intros [H1|H2].
    left; now right.
   now right;right.
  now apply: ap_cotransitive.
 intros x y. case x. case y.
 intros c c0 c1 c2.
 split.
  intros.
  split.
   apply not_ap_imp_eq.
   intros H1. now cut (c1 [#] c or c2 [#] c0);[|left].
   apply not_ap_imp_eq. intros H1. now cut (c1 [#] c or c2 [#] c0);[|right].
  intros.
 elim H.
 intros H0 H1 H2.
 now elim H2;apply eq_imp_not_ap.
Qed.

Definition ProdCSetoid (A B : CSetoid) : CSetoid := Build_CSetoid
 (prodT A B) (prod_eq A B) (prod_ap A B) (prodcsetoid_is_CSetoid A B).

End product_csetoid.
Implicit Arguments ex_unq [S].

Hint Resolve eq_reflexive_unfolded ap_irreflexive_unfolded: algebra_r.
Hint Resolve eq_symmetric_unfolded ap_symmetric_unfolded: algebra_s.
Hint Resolve eq_transitive_unfolded ap_cotransitive_unfolded: algebra_c.

Declare Left Step eq_wdl.
Declare Right Step eq_transitive_unfolded.

(**
** Relations and predicates
Here we define the notions of well-definedness and strong extensionality
on predicates and relations.

%\begin{convention}% Let [S] be a setoid.
%\end{convention}%

%\begin{nameconvention}%
- ``well-defined'' is abbreviated to [well_def] (or [wd]).
- ``strongly extensional'' is abbreviated to [strong_ext] (or [strext]).

%\end{nameconvention}%
*)

Section CSetoid_relations_and_predicates.
Variable S : CSetoid.

(**
*** Predicates

At this stage, we consider [CProp]- and [Prop]-valued predicates on setoids.

%\begin{convention}% Let [P] be a predicate on (the carrier of) [S].
%\end{convention}%
*)

Section CSetoidPredicates.
Variable P : S -> CProp.

Definition pred_strong_ext : CProp := forall x y : S, P x -> P y or x [#] y.

Definition pred_wd : CProp := forall x y : S, P x -> x [=] y -> P y.

End CSetoidPredicates.

Record wd_pred : Type :=
  {wdp_pred     :> S -> CProp;
   wdp_well_def :  pred_wd wdp_pred}.

Record CSetoid_predicate : Type :=
 {csp_pred   :> S -> CProp;
  csp_strext :  pred_strong_ext csp_pred}.

Lemma csp_wd : forall P : CSetoid_predicate, pred_wd P.
Proof.
 intro P.
 intro x; intros y H H0.
 elim (csp_strext P x y H).
  auto.
 set (eq_imp_not_ap _ _ _ H0); contradiction.
Qed.

(** Similar, with [Prop] instead of [CProp]. *)

Section CSetoidPPredicates.
Variable P : S -> Prop.

Definition pred_strong_ext' : CProp := forall x y : S, P x -> P y or x [#] y.

Definition pred_wd' : Prop := forall x y : S, P x -> x [=] y -> P y.

End CSetoidPPredicates.

(**
*** Definition of a setoid predicate *)

Record CSetoid_predicate' : Type :=
 {csp'_pred   :> S -> Prop;
  csp'_strext :  pred_strong_ext' csp'_pred}.

Lemma csp'_wd : forall P : CSetoid_predicate', pred_wd' P.
Proof.
 intro P.
 intro x; intros y H H0.
 elim (csp'_strext P x y H).
  auto.
 set (eq_imp_not_ap _ _ _ H0); contradiction.
Qed.

(**
*** Relations
%\begin{convention}%
Let [R] be a relation on (the carrier of) [S].
%\end{convention}% *)

Section CsetoidRelations.
Variable R : S -> S -> Prop.

Definition rel_wdr : Prop := forall x y z : S, R x y -> y [=] z -> R x z.

Definition rel_wdl : Prop := forall x y z : S, R x y -> x [=] z -> R z y.

Definition rel_strext : CProp := forall x1 x2 y1 y2 : S,
 R x1 y1 -> (x1 [#] x2 or y1 [#] y2) or R x2 y2.

Definition rel_strext_lft : CProp := forall x1 x2 y : S, R x1 y -> x1 [#] x2 or R x2 y.

Definition rel_strext_rht : CProp := forall x y1 y2 : S, R x y1 -> y1 [#] y2 or R x y2.

Lemma rel_strext_imp_lftarg : rel_strext -> rel_strext_lft.
Proof.
 intros H x1 x2 y H0.
 generalize (H x1 x2 y y).
 intros H1.
 elim (H1 H0);[|auto].
 intros [H2|H3];[auto|].
 elim (ap_irreflexive S _ H3).
Qed.

Lemma rel_strext_imp_rhtarg : rel_strext -> rel_strext_rht.
Proof.
 intros H x y1 y2 H0.
 generalize (H x x y1 y2 H0). intros [[H1|H2]|H3]; auto.
 elim (ap_irreflexive _ _ H1).
Qed.

Lemma rel_strextarg_imp_strext :
 rel_strext_rht -> rel_strext_lft -> rel_strext.
Proof.
 intros H H0 x1 x2 y1 y2 H1.
 elim (H x1 y1 y2 H1); intro H2;[|elim (H0 x1 x2 y2 H2)];auto.

Qed.

End CsetoidRelations.

(**
*** Definition of a setoid relation
The type of relations over a setoid.  *)

Record CSetoid_relation : Type :=
  {csr_rel    :> S -> S -> Prop;
   csr_wdr    :  rel_wdr csr_rel;
   csr_wdl    :  rel_wdl csr_rel;
   csr_strext :  rel_strext csr_rel}.

(**
*** [CProp] Relations
%\begin{convention}%
Let [R] be a relation on (the carrier of) [S].
%\end{convention}%
*)

Section CCsetoidRelations.

Variable R : S -> S -> CProp.

Definition Crel_wdr : CProp := forall x y z : S, R x y -> y [=] z -> R x z.

Definition Crel_wdl : CProp := forall x y z : S, R x y -> x [=] z -> R z y.

Definition Crel_strext : CProp := forall x1 x2 y1 y2 : S,
 R x1 y1 -> R x2 y2 or x1 [#] x2 or y1 [#] y2.

Definition Crel_strext_lft : CProp := forall x1 x2 y : S, R x1 y -> R x2 y or x1 [#] x2.

Definition Crel_strext_rht : CProp := forall x y1 y2 : S, R x y1 -> R x y2 or y1 [#] y2.

Lemma Crel_strext_imp_lftarg : Crel_strext -> Crel_strext_lft.
Proof.
 intros H x1 x2 y H0. generalize (H x1 x2 y y).
 intros [H1|H2];auto.
 case H2. auto. intro H3. elim (ap_irreflexive _ _ H3).
Qed.

Lemma Crel_strext_imp_rhtarg : Crel_strext -> Crel_strext_rht.
Proof.
 intros H x y1 y2 H0.
 generalize (H x x y1 y2 H0). intros [H1|H2];auto.
 case H2; auto. intro H3. elim (ap_irreflexive _ _ H3).
Qed.

Lemma Crel_strextarg_imp_strext :
 Crel_strext_rht -> Crel_strext_lft -> Crel_strext.
Proof.
 intros H H0 x1 x2 y1 y2 H1.
 elim (H x1 y1 y2 H1); auto.
 intro H2.
 elim (H0 x1 x2 y2 H2); auto.
Qed.

End CCsetoidRelations.

(**
*** Definition of a [CProp] setoid relation

The type of relations over a setoid.  *)

Record CCSetoid_relation : Type :=
 {Ccsr_rel    :> S -> S -> CProp;
  Ccsr_strext :  Crel_strext Ccsr_rel}.

Lemma Ccsr_wdr : forall R : CCSetoid_relation, Crel_wdr R.
Proof.
 intro R.
 intros x y z H H0.
 elim (Ccsr_strext R x x y z H);auto.
 intros [H1|H2]. elim (ap_irreflexive _ _ H1).
  set (eq_imp_not_ap _ _ _ H0). contradiction.
Qed.

Lemma Ccsr_wdl : forall R : CCSetoid_relation, Crel_wdl R.
Proof.
 intros R x y z H H0.
 elim (Ccsr_strext R x z y y H);auto.
 intros [H1|H2]; [set (eq_imp_not_ap _ _ _ H0); contradiction| elim (ap_irreflexive _ _ H2)].
Qed.

Lemma ap_wdr : Crel_wdr (cs_ap (c:=S)).
Proof.
 intros x y z H H0.
 generalize (eq_imp_not_ap _ _ _ H0); intro H1.
 elim (ap_cotransitive _ _ _ H z); intro H2.
  assumption.
 elim H1.
 now apply: ap_symmetric.
Qed.

Lemma ap_wdl : Crel_wdl (cs_ap (c:=S)).
Proof.
 intros x y z H H0.
 generalize (ap_wdr y x z); intro H1.
 apply ap_symmetric.
 now apply H1;[apply ap_symmetric|].
Qed.

Lemma ap_wdr_unfolded : forall x y z : S, x [#] y -> y [=] z -> x [#] z.
Proof ap_wdr.

Lemma ap_wdl_unfolded : forall x y z : S, x [#] y -> x [=] z -> z [#] y.
Proof ap_wdl.

Lemma ap_strext : Crel_strext (cs_ap (c:=S)).
Proof.
 intros x1 x2 y1 y2 H.
 case (ap_cotransitive _ _ _ H x2); intro H0;auto.
 case (ap_cotransitive _ _ _ H0 y2); intro H1;auto.
 right; right.
 now apply ap_symmetric.
Qed.

Definition predS_well_def (P : S -> CProp) : CProp := forall x y : S,
 P x -> x [=] y -> P y.

End CSetoid_relations_and_predicates.

Declare Left Step ap_wdl_unfolded.
Declare Right Step ap_wdr_unfolded.

(**
** Functions between setoids
Such functions must preserve the setoid equality
and be strongly extensional w.r.t.%\% the apartness, i.e.%\%
if [f(x,y) [#] f(x1,y1)], then  [x [#] x1 + y [#] y1].
For every arity this has to be defined separately.
%\begin{convention}%
Let [S1], [S2] and [S3] be setoids.
%\end{convention}%

First we consider unary functions.  *)

Section CSetoid_functions.
Variables S1 S2 S3 : CSetoid.


Section unary_functions.

(**
In the following two definitions,
[f] is a function from (the carrier of) [S1] to
(the carrier of) [S2].  *)

Variable f : S1 -> S2.

Definition fun_wd : Prop := forall x y : S1, x [=] y -> f x [=] f y.

Definition fun_strext : CProp := forall x y : S1, f x [#] f y -> x [#] y.

Lemma fun_strext_imp_wd : fun_strext -> fun_wd.
Proof.
 intros H x y H0.
 apply not_ap_imp_eq.
 intro H1.
 generalize (H _ _ H1); intro H2.
 now generalize (eq_imp_not_ap _ _ _ H0).
Qed.

End unary_functions.

Record CSetoid_fun : Type :=
  {csf_fun    :> S1 -> S2;
   csf_strext :  fun_strext csf_fun}.

Lemma csf_wd : forall f : CSetoid_fun, fun_wd f.
Proof.
 intro f.
 apply fun_strext_imp_wd.
 apply csf_strext.
Qed.

Lemma csf_wd_unfolded: forall (f : CSetoid_fun) (x y : S1), x[=]y -> f x[=]f y.
Proof csf_wd.

Definition Const_CSetoid_fun : S2 -> CSetoid_fun.
Proof.
 intro c; apply (Build_CSetoid_fun (fun x : S1 => c)); intros x y H.
 elim (ap_irreflexive _ _ H).
Defined.

Section binary_functions.

(**
Now we consider binary functions.
In the following two definitions,
[f] is a function from [S1] and [S2] to [S3].
*)
Variable f : S1 -> S2 -> S3.

Definition bin_fun_wd : Prop := forall x1 x2 y1 y2,
 x1 [=] x2 -> y1 [=] y2 -> f x1 y1 [=] f x2 y2.

Definition bin_fun_strext : CProp := forall x1 x2 y1 y2,
 f x1 y1 [#] f x2 y2 -> x1 [#] x2 or y1 [#] y2.

Lemma bin_fun_strext_imp_wd : bin_fun_strext -> bin_fun_wd.
Proof.
 intros H x1 x2 y1 y2 H0 H1.
 apply not_ap_imp_eq.
 intro H2.
 generalize (H _ _ _ _ H2); intro H3.
 elim H3; intro H4.
  now set (eq_imp_not_ap _ _ _ H0).
 now set (eq_imp_not_ap _ _ _ H1).
Qed.

End binary_functions.

Record CSetoid_bin_fun : Type :=
 {csbf_fun    :> S1 -> S2 -> S3;
  csbf_strext :  bin_fun_strext csbf_fun}.

Lemma csbf_wd : forall f : CSetoid_bin_fun, bin_fun_wd f.
Proof.
 intro f. apply: bin_fun_strext_imp_wd.
 apply csbf_strext.
Qed.

Lemma csbf_wd_unfolded : forall (f : CSetoid_bin_fun) (x x' : S1) (y y' : S2),
 x [=] x' -> y [=] y' -> f x y [=] f x' y'.
Proof csbf_wd.

Lemma csf_strext_unfolded : forall (f : CSetoid_fun) (x y : S1), f x [#] f y -> x [#] y.
Proof csf_strext.

End CSetoid_functions.

Lemma bin_fun_is_wd_fun_lft : forall S1 S2 S3 (f : CSetoid_bin_fun S1 S2 S3) (c : S2),
 fun_wd _ _ (fun x : S1 => f x c).
Proof.
 intros S1 S2 S3 f c x y H.
 now apply csbf_wd; [|apply eq_reflexive].
Qed.

Lemma bin_fun_is_wd_fun_rht : forall S1 S2 S3 (f : CSetoid_bin_fun S1 S2 S3) (c : S1),
 fun_wd _ _ (fun x : S2 => f c x).
Proof.
 intros S1 S2 S3 f c x y H. now apply csbf_wd; [apply eq_reflexive|].
Qed.

Lemma bin_fun_is_strext_fun_lft : forall S1 S2 S3 (f : CSetoid_bin_fun S1 S2 S3) (c : S2),
 fun_strext _ _ (fun x : S1 => f x c).
Proof.
 intros S1 S2 S3 f c x y H. cut (x [#] y or c [#] c). intros [H1|H2];auto.
 now set (ap_irreflexive _ c H2).
 eapply csbf_strext. apply H.
Defined.

Lemma bin_fun_is_strext_fun_rht : forall S1 S2 S3 (f : CSetoid_bin_fun S1 S2 S3) (c : S1),
 fun_strext _ _ (fun x : S2 => f c x).
Proof.
 intros S1 S2 S3 op c x y H. cut (c [#] c or x [#] y). intro Hv. elim Hv. intro Hf.
 generalize (ap_irreflexive _ c Hf). tauto. auto.
   eapply csbf_strext. apply H.
Defined.

Definition bin_fun2fun_rht (S1 S2 S3:CSetoid) (f : CSetoid_bin_fun S1 S2 S3) (c : S1) : CSetoid_fun S2 S3 :=
  Build_CSetoid_fun _ _ (fun x : S2 => f c x) (bin_fun_is_strext_fun_rht _ _ _ f c).

Definition bin_fun2fun_lft (S1 S2 S3:CSetoid) (f : CSetoid_bin_fun S1 S2 S3) (c : S2) : CSetoid_fun S1 S3 :=
  Build_CSetoid_fun _ _ (fun x : S1 => f x c) (bin_fun_is_strext_fun_lft _ _ _ f c).

Hint Resolve csf_wd_unfolded csbf_wd_unfolded csf_strext_unfolded: algebra_c.

Implicit Arguments fun_wd [S1 S2].
Implicit Arguments fun_strext [S1 S2].

(**
** The unary and binary (inner) operations on a csetoid
An operation is a function with domain(s) and co-domain equal.

%\begin{nameconvention}%
The word ``unary operation'' is abbreviated to [un_op];
``binary operation'' is abbreviated to [bin_op].
%\end{nameconvention}%

%\begin{convention}%
Let [S] be a setoid.
%\end{convention}%
*)

Section csetoid_inner_ops.
Variable S : CSetoid.

(** Properties of binary operations *)

Definition commutes (f : S -> S -> S) : Prop := forall x y : S, f x y [=] f y x.

Definition associative (f : S -> S -> S) : Prop := forall x y z : S,
 f x (f y z) [=] f (f x y) z.

(** Well-defined unary operations on a setoid.  *)

Definition un_op_wd := fun_wd (S1:=S) (S2:=S).

Definition un_op_strext := fun_strext (S1:=S) (S2:=S).

Definition CSetoid_un_op  := CSetoid_fun S S.

Definition Build_CSetoid_un_op := Build_CSetoid_fun S S.

Lemma id_strext : un_op_strext (fun x : S => x).
Proof. now repeat intro. Qed.

Lemma id_pres_eq : un_op_wd (fun x : S => x).
Proof. now repeat intro. Qed.

Definition id_un_op := Build_CSetoid_un_op (fun x : S => x) id_strext.

(* begin hide *)
Identity Coercion un_op_fun : CSetoid_un_op >-> CSetoid_fun.
(* end hide *)

Definition cs_un_op_strext := csf_strext S S.

(** Well-defined binary operations on a setoid.  *)

Definition bin_op_wd := bin_fun_wd S S S.
Definition bin_op_strext := bin_fun_strext S S S.

Definition CSetoid_bin_op : Type := CSetoid_bin_fun S S S.
Definition Build_CSetoid_bin_op := Build_CSetoid_bin_fun S S S.

Definition cs_bin_op_wd := csbf_wd S S S.
Definition cs_bin_op_strext := csbf_strext S S S.

(* begin hide *)
Identity Coercion bin_op_bin_fun : CSetoid_bin_op >-> CSetoid_bin_fun.
(* end hide *)

Lemma bin_op_is_wd_un_op_lft : forall (op : CSetoid_bin_op) (c : S),
 un_op_wd (fun x : S => op x c).
Proof.
 apply bin_fun_is_wd_fun_lft.
Qed.

Lemma bin_op_is_wd_un_op_rht : forall (op : CSetoid_bin_op) (c : S),
 un_op_wd (fun x : S => op c x).
Proof.
 apply bin_fun_is_wd_fun_rht.
Qed.

Lemma bin_op_is_strext_un_op_lft : forall (op : CSetoid_bin_op) (c : S),
 un_op_strext (fun x : S => op x c).
Proof. apply bin_fun_is_strext_fun_lft. Defined.

Lemma bin_op_is_strext_un_op_rht : forall (op : CSetoid_bin_op) (c : S),
 un_op_strext (fun x : S => op c x).
Proof. apply bin_fun_is_strext_fun_rht. Defined.

Definition bin_op2un_op_rht (op : CSetoid_bin_op) (c : S) : CSetoid_un_op :=
  bin_fun2fun_rht _ _ _ op c.

Definition bin_op2un_op_lft (op : CSetoid_bin_op) (c : S) : CSetoid_un_op :=
  bin_fun2fun_lft _ _ _ op c.

Lemma un_op_wd_unfolded : forall (op : CSetoid_un_op) (x y : S),
 x [=] y -> op x [=] op y.
Proof csf_wd S S.

Lemma un_op_strext_unfolded : forall (op : CSetoid_un_op) (x y : S),
 op x [#] op y -> x [#] y.
Proof cs_un_op_strext.

Lemma bin_op_wd_unfolded : forall (op : CSetoid_bin_op) (x1 x2 y1 y2 : S),
 x1 [=] x2 -> y1 [=] y2 -> op x1 y1 [=] op x2 y2.
Proof cs_bin_op_wd.

Lemma bin_op_strext_unfolded : forall (op : CSetoid_bin_op) (x1 x2 y1 y2 : S),
 op x1 y1 [#] op x2 y2 -> x1 [#] x2 or y1 [#] y2.
Proof cs_bin_op_strext.

End csetoid_inner_ops.

Implicit Arguments commutes [S].
Implicit Arguments associative [S].

(* Needs to be unfolded to be used as a Hint *)
Hint Resolve ap_wdr_unfolded ap_wdl_unfolded  bin_op_wd_unfolded un_op_wd_unfolded : algebra_c.

(**
** The binary outer operations on a csetoid
%\begin{convention}%
Let [S1] and [S2] be setoids.
%\end{convention}%
*)

Section csetoid_outer_ops.
Variables S1 S2 : CSetoid.

(**
Well-defined outer operations on a setoid.
*)
Definition outer_op_well_def := bin_fun_wd S1 S2 S2.
Definition outer_op_strext := bin_fun_strext S1 S2 S2.

Definition CSetoid_outer_op : Type := CSetoid_bin_fun S1 S2 S2.
Definition Build_CSetoid_outer_op := Build_CSetoid_bin_fun S1 S2 S2.
Definition csoo_wd := csbf_wd S1 S2 S2.
Definition csoo_strext := csbf_strext S1 S2 S2.
Lemma csoo_wd_unfolded : forall (op : CSetoid_outer_op) x1 x2 y1 y2,
 x1 [=] x2 -> y1 [=] y2 -> op x1 y1 [=] op x2 y2.
Proof csoo_wd.

(* begin hide *)
Identity Coercion outer_op_bin_fun : CSetoid_outer_op >-> CSetoid_bin_fun.
(* end hide *)

End csetoid_outer_ops.
Hint Resolve csoo_wd_unfolded: algebra_c.

(**
** Subsetoids
%\begin{convention}%
Let [S] be a setoid, and [P] a predicate on the carrier of [S].
%\end{convention}%
*)

Section SubCSetoids.
Variable S : CSetoid.
Variable P : S -> CProp.

Record subcsetoid_crr : Type :=
 {scs_elem :> S;
  scs_prf  :  P scs_elem}.

(** Though [scs_elem] is declared as a coercion, it does not satisfy the
uniform inheritance condition and will not be inserted.  However it will
also not be printed, which is handy.
*)

Definition restrict_relation (R : Relation S) : Relation subcsetoid_crr :=
  fun a b : subcsetoid_crr =>
  match a, b with
  | Build_subcsetoid_crr x _, Build_subcsetoid_crr y _ => R x y
  end.

Definition Crestrict_relation (R : Crelation S) : Crelation subcsetoid_crr :=
  fun a b : subcsetoid_crr =>
  match a, b with
  | Build_subcsetoid_crr x _, Build_subcsetoid_crr y _ => R x y
  end.

Definition subcsetoid_eq : Relation subcsetoid_crr :=
  restrict_relation (cs_eq (r:=S)).

Definition subcsetoid_ap : Crelation subcsetoid_crr :=
  Crestrict_relation (cs_ap (c:=S)).

Remark subcsetoid_equiv : Tequiv _ subcsetoid_eq.
Proof.
 split.
  (* reflexive *)
  intros a; case a.
  intros x s. apply (eq_reflexive S).
  (* transitive *)
  split.
  intros a b c; case a.
  intros x s; case b.
  intros y t; case c.
  intros z u. apply eq_transitive.
  (* symmetric *)
  intros a b; case a.
 intros x s; case b.
 intros y t. apply eq_symmetric.
Qed.

Lemma subcsetoid_is_CSetoid : is_CSetoid _ subcsetoid_eq subcsetoid_ap.
Proof.
 apply (Build_is_CSetoid _ subcsetoid_eq subcsetoid_ap).
    (* irreflexive *)
    intro x. case x. intros. apply ap_irreflexive.
    (* symmetric *)
    intros x y. case x. case y. intros.
   exact (ap_symmetric S _ _ X).
  (* cotransitive *)
  intros x y. case x. case y. intros; case z. intros.
  exact (ap_cotransitive S _ _ X scs_elem2).
 (* tight *)
 intros x y. case x. case y. intros.
 exact (ap_tight S scs_elem1 scs_elem0).
Qed.

Definition Build_SubCSetoid : CSetoid := Build_CSetoid
 subcsetoid_crr subcsetoid_eq subcsetoid_ap subcsetoid_is_CSetoid.

(**
*** Subsetoid unary operations
%\begin{convention}%
Let [f] be a unary setoid operation on [S].
%\end{convention}%
*)

Section SubCSetoid_unary_operations.
Variable f : CSetoid_un_op S.
Definition un_op_pres_pred : CProp := forall x : S, P x -> P (f x).

(**
%\begin{convention}%
Assume [pr:un_op_pres_pred].
%\end{convention}% *)

Variable pr : un_op_pres_pred.

Definition restr_un_op (a : subcsetoid_crr) : subcsetoid_crr :=
  match a with
  | Build_subcsetoid_crr x p => Build_subcsetoid_crr (f x) (pr x p)
  end.

Lemma restr_un_op_wd : un_op_wd Build_SubCSetoid restr_un_op.
Proof.
 intros x y. case y. case x. intros. now apply: (csf_wd _ _ f).
Qed.

Lemma restr_un_op_strext : un_op_strext Build_SubCSetoid restr_un_op.
Proof.
 intros x y. case y. case x. intros. exact (cs_un_op_strext _ f _ _ X).
Qed.

Definition Build_SubCSetoid_un_op : CSetoid_un_op Build_SubCSetoid :=
  Build_CSetoid_un_op Build_SubCSetoid restr_un_op restr_un_op_strext.

End SubCSetoid_unary_operations.


(**
*** Subsetoid binary operations
%\begin{convention}%
Let [f] be a binary setoid operation on [S].
%\end{convention}%
*)

Section SubCSetoid_binary_operations.

Variable f : CSetoid_bin_op S.

Definition bin_op_pres_pred : CProp := forall x y : S, P x -> P y -> P (f x y).

(**
%\begin{convention}%
Assume [bin_op_pres_pred].
%\end{convention}%
*)

Variable pr : bin_op_pres_pred.

Definition restr_bin_op (a b : subcsetoid_crr) : subcsetoid_crr :=
  match a, b with
  | Build_subcsetoid_crr x p, Build_subcsetoid_crr y q =>
      Build_subcsetoid_crr (f x y) (pr x y p q)
  end.

Lemma restr_bin_op_well_def : bin_op_wd Build_SubCSetoid restr_bin_op.
Proof.
 intros x1 x2 y1 y2. case y2. case y1. case x2. case x1. intros.
 exact (cs_bin_op_wd _ f _ _ _ _ H H0).
Qed.

Lemma restr_bin_op_strext : bin_op_strext Build_SubCSetoid restr_bin_op.
Proof.
 intros x1 x2 y1 y2. case y2. case y1. case x2. case x1. intros.
 exact (cs_bin_op_strext _ f _ _ _ _ X).
Qed.

Definition Build_SubCSetoid_bin_op : CSetoid_bin_op Build_SubCSetoid :=
  Build_CSetoid_bin_op Build_SubCSetoid restr_bin_op restr_bin_op_strext.


Lemma restr_f_assoc : associative f -> associative Build_SubCSetoid_bin_op.
Proof.
 intros assf x y z. case z. case y. case x. intros. apply: assf.
Qed.


End SubCSetoid_binary_operations.

End SubCSetoids.

(* begin hide *)
Ltac Step_final x := apply eq_transitive with x; algebra.
(* end hide *)

Tactic Notation "Step_final" constr(c) :=  Step_final c.

(**
** Miscellaneous
*)

Lemma proper_caseZ_diff_CS : forall (S : CSetoid) (f : nat -> nat -> S),
 (forall m n p q : nat, m + q = n + p -> f m n [=] f p q) ->
 forall m n : nat, caseZ_diff (m - n) f [=] f m n.
Proof.
 intro CS. intros.
 pattern m, n in |- *.
 apply nat_double_ind.
   intro. replace (0%nat - n0)%Z with (- n0)%Z;auto. rewrite caseZ_diff_Neg; reflexivity.
   intros. replace (S n0 - 0%nat)%Z with (S n0:Z);auto. rewrite caseZ_diff_Pos; reflexivity.
  intros. generalize (H (S n0) (S m0) n0 m0); intro.
 cut (S n0 + m0 = S m0 + n0).
  intro. generalize (H1 H2); intro.
  apply eq_transitive with (f n0 m0).
   apply eq_transitive with (caseZ_diff (n0 - m0) f);auto.
   replace (S n0 - S m0)%Z with (n0 - m0)%Z.
    apply eq_reflexive.
   repeat rewrite Znat.inj_S; clear H1; auto with zarith.
  now apply eq_symmetric.
 clear H1; auto with zarith.
Qed.

(**
Finally, we characterize functions defined on the natural numbers also as setoid functions, similarly to what we already did for predicates.
*)

Definition nat_less_n_fun (S : CSetoid) (n : nat) (f : forall i : nat, i < n -> S) :=
  forall i j : nat, i = j -> forall (H : i < n) (H' : j < n), f i H [=] f j H'.

Definition nat_less_n_fun' (S : CSetoid) (n : nat) (f : forall i : nat, i <= n -> S) :=
  forall i j : nat, i = j -> forall (H : i <= n) (H' : j <= n), f i H [=] f j H'.

Implicit Arguments nat_less_n_fun [S n].
Implicit Arguments nat_less_n_fun' [S n].

Add Parametric Relation c : (cs_crr c) (@cs_eq c)
  reflexivity proved by (eq_reflexive c)
  symmetry proved by (eq_symmetric c)
  transitivity proved by (eq_transitive c)
  as CSetoid_eq_Setoid.

Add Parametric Morphism (c1 c2 c3 : CSetoid) f: (csbf_fun c1 c2 c3 f) with signature (@cs_eq c1) ==> (@cs_eq c2) ==> (@cs_eq c3) as csbf_fun_wd.
Proof.
 intros x1 x2 Hx y1 y2 Hy.
 now apply csbf_wd.
Qed.

Add Parametric Morphism (c1 c2 : CSetoid) f: (@csf_fun c1 c2 f) with signature (@cs_eq c1) ==> (@cs_eq c2) as csf_fun_wd.
Proof.
 intros x1 x2 Hx.
 now apply csf_wd.
Qed.
