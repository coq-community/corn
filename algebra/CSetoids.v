(* $Id.v,v 1.18 2002/11/25 14:43:42 lcf Exp $ *)

(** printing [=] %\ensuremath{\equiv}% #&equiv;# *)
(** printing [~=] %\ensuremath{\not\equiv}% #&ne;# *)
(** printing [#] %\ensuremath{\#}% *)
(** printing ex_unq %\ensuremath{\exists^1}% #&exist;<sup>1</sup># *)
(** printing [o] %\ensuremath\circ% #&sdot;# *)
(** printing [-C-] %\ensuremath\diamond% *)

(* Begin_SpecReals *)

(** *Setoids
Definition of a constructive setoid with apartness,
i.e.%\% a set with an equivalence relation and an apartness relation compatible with it.
*)

Require Export CLogic.
Require Export Step.

(* begin hide *)
Definition Relation := Trelation.
(* end hide *)

(* End_SpecReals *)

Implicit Arguments Treflexive [A].
Implicit Arguments Creflexive [A].

(* Begin_SpecReals *)

Implicit Arguments Tsymmetric [A].
Implicit Arguments Csymmetric [A].
Implicit Arguments Ttransitive [A].
Implicit Arguments Ctransitive [A].

Set Implicit Arguments.
Unset Strict Implicit.

(** **Relations necessary for Setoids
%\begin{convention}%
Let [A:Type].
%\end{convention}%

Notice that their type depends on the main logical connective.
*)
Section Properties_of_relations.
Variable A : Type.

Definition irreflexive (R : Crelation A) : Prop := forall x : A, Not (R x x).

Definition cotransitive (R : Crelation A) : CProp :=
  forall x y : A, R x y -> forall z : A, R x z or R z y.

Definition tight_apart (eq : Relation A) (ap : Crelation A) : Prop :=
  forall x y : A, Not (ap x y) <-> eq x y.

Definition antisymmetric (R : Crelation A) : Prop :=
  forall x y : A, R x y -> Not (R y x).

End Properties_of_relations.
Set Strict Implicit.
Unset Implicit Arguments.

(** **Definition of Setoid

Apartness, being the main relation, needs to be [CProp]-valued.  Equality,
as it is characterized by a negative statement, lives in [Prop]. *)

Record is_CSetoid (A : Type) (eq : Relation A) (ap : Crelation A) : CProp := 
  {ax_ap_irreflexive : irreflexive ap;
   ax_ap_symmetric : Csymmetric ap;
   ax_ap_cotransitive : cotransitive ap;
   ax_ap_tight : tight_apart eq ap}.

Record CSetoid : Type := 
  {cs_crr :> Type;
   cs_eq : Relation cs_crr;
   cs_ap : Crelation cs_crr;
   cs_proof : is_CSetoid cs_crr cs_eq cs_ap}.

Implicit Arguments cs_eq [c].
Implicit Arguments cs_ap [c].

Infix "[=]" := cs_eq (at level 70, no associativity).
Infix "[#]" := cs_ap (at level 70, no associativity).

(* begin hide *)
(* Syntax is discontinued Syntax constr level 8 :
                           cs_eq_infix
                           [<<(APPLIST (CONST <CSetoids#2>. cs_eq)
                                 (EXPL 1 (ISEVAR )) $_ $e1 $e2)>>] -> [ [<hov
                           1>$e1 [0 1] " [=] " $e2] ] *)

(* Syntax is discontinued Syntax constr level 8 :
                           cs_ap_infix
                           [<<(APPLIST (CONST <CSetoids#2>. cs_ap)
                                 (EXPL 1 (ISEVAR )) $_ $e1 $e2)>>] -> [ [<hov
                           1>$e1 [0 1] " [#] " $e2] ] *)
(* end hide *)
(* End_SpecReals *)

Definition cs_neq (S : CSetoid) : Relation S := fun x y : S => ~ x[=]y.

Implicit Arguments cs_neq [S].

Infix "[~=]" := cs_neq (at level 70, no associativity).

(**
%\begin{nameconvention}%
In the names of lemmas, we refer to [ [=] ] by [eq], [[~=]] by
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

Lemma CSetoid_is_CSetoid : is_CSetoid S (cs_eq (c:=S)) (cs_ap (c:=S)).
Proof cs_proof S.

Lemma ap_irreflexive : irreflexive (cs_ap (c:=S)).
elim CSetoid_is_CSetoid; auto.
Qed.

Lemma ap_symmetric : Csymmetric (cs_ap (c:=S)).
elim CSetoid_is_CSetoid; auto.
Qed.

Lemma ap_cotransitive : cotransitive (cs_ap (c:=S)).
elim CSetoid_is_CSetoid; auto.
Qed.

Lemma ap_tight : tight_apart (cs_eq (c:=S)) (cs_ap (c:=S)).
elim CSetoid_is_CSetoid; auto.
Qed.

End CSetoid_axioms.

(* End_SpecReals *)

(** **Setoid basics%\label{section:setoid-basics}%
%\begin{convention}%
Let [S] be a setoid.
%\end{convention}%
*)

(* Begin_SpecReals *)

Section CSetoid_basics.
Variable S : CSetoid.

(* End_SpecReals *)

(**
In `there exists a unique [a:S] such that %\ldots%#...#', we now mean unique with respect to the setoid equality. We use [ex_unq] to denote unique existence.
*)

Definition ex_unq (P : S -> CProp) :=
  {x : S | forall y : S, P y -> x[=]y | P x}.

Lemma eq_reflexive : Treflexive (cs_eq (c:=S)).
intro x.
generalize (ap_tight S x x); intro H.
generalize (ap_irreflexive S x); intro H0.
inversion_clear H; auto.
Qed.

Lemma eq_symmetric : Tsymmetric (cs_eq (c:=S)).
intro x; intros y H.
generalize (ap_tight S x y); intro H0.
generalize (ap_tight S y x); intro H1.
generalize (ap_symmetric S y x); intro H2.
elim H0; clear H0; intros H3 H4.
elim H1; clear H1; intros H0 H5.
apply H0; intro H6.
apply H4; auto.
Qed.

Lemma eq_transitive : Ttransitive (cs_eq (c:=S)).
intro x; intros y z H H0.
generalize (ap_tight S x y); intro H1.
generalize (ap_tight S y z); intro H2.
generalize (ap_tight S x z); intro H3.
elim H3; intros H4 H5.
apply H4.
intro H6.
generalize (ap_cotransitive _ _ _ H6 y); intro H7.
elim H1; clear H1; intros H1' H1''.
elim H2; clear H2; intros H2' H2''.
elim H3; clear H3; intros H3' H3''.
elim H7; clear H7; intro H1.
generalize H1; apply H1''; auto.
generalize H1; apply H2''; auto.
Qed.

(**
%\begin{shortcoming}%
The lemma [eq_reflexive] above is convertible to
[eq_reflexive_unfolded] below. We need the second version too,
because the first cannot be applied when an instance of reflexivity is needed.
(``I have complained bitterly about this.'' RP)
%\end{shortcoming}%

%\begin{nameconvention}%
If lemma [a] is just an unfolding of lemma [b], the name of [a] is the name
[b] with the suffix ``[_unfolded]''.
%\end{nameconvention}%
*)

Lemma eq_reflexive_unfolded : forall x : S, x[=]x.
Proof eq_reflexive.

Lemma eq_symmetric_unfolded : forall x y : S, x[=]y -> y[=]x.
Proof eq_symmetric.

Lemma eq_transitive_unfolded : forall x y z : S, x[=]y -> y[=]z -> x[=]z.
Proof eq_transitive.

Lemma eq_wdl : forall x y z : S, x[=]y -> x[=]z -> z[=]y.
intros.
apply eq_transitive_unfolded with x; auto.
apply eq_symmetric_unfolded; auto.
Qed.

(* Begin_SpecReals *)

Lemma ap_irreflexive_unfolded : forall x : S, Not (x[#]x).
Proof ap_irreflexive S.

(* End_SpecReals *)

Lemma ap_cotransitive_unfolded :
 forall a b : S, a[#]b -> forall c : S, a[#]c or c[#]b.
intros a b H c.
exact (ap_cotransitive _ _ _ H c).
Qed.

Lemma ap_symmetric_unfolded : forall x y : S, x[#]y -> y[#]x.
Proof ap_symmetric S.

(**
%\begin{shortcoming}%
We would like to write
[[
Lemma eq_equiv_not_ap : (x,y:S)(x [=] y) <->~(x [#] y).
]]
In Coq, however, this lemma cannot be easily applied.
Therefore we have to split the lemma into the following two lemmas [eq_imp_not_ap] and [not_ap_imp_eq].
%\end{shortcoming}%
*)

Lemma eq_imp_not_ap : forall x y : S, x[=]y -> Not (x[#]y).
intros x y.
elim (ap_tight S x y).
intros H1 H2.
assumption.
Qed.

Lemma not_ap_imp_eq : forall x y : S, Not (x[#]y) -> x[=]y.
intros x y.
elim (ap_tight S x y).
intros H1 H2.
assumption.
Qed.

Lemma neq_imp_notnot_ap : forall x y : S, x[~=]y -> ~ Not (x[#]y).
intros x y H.
intro H0.
unfold cs_neq in H.
apply H.
apply not_ap_imp_eq.
assumption.
Qed.

Lemma notnot_ap_imp_neq : forall x y : S, ~ Not (x[#]y) -> x[~=]y.
intros x y H.
intro H0.
apply H.
apply eq_imp_not_ap.
assumption.
Qed.

Lemma ap_imp_neq : forall x y : S, x[#]y -> x[~=]y.
intros x y H; intro H1.
apply (eq_imp_not_ap _ _ H1).
assumption.
Qed.

Lemma not_neq_imp_eq : forall x y : S, ~ x[~=]y -> x[=]y.
intros x y H.
apply not_ap_imp_eq.
intro H0.
elim H.
apply ap_imp_neq.
assumption.
Qed.

Lemma eq_imp_not_neq : forall x y : S, x[=]y -> ~ x[~=]y.
intros x y H.
intro H0.
auto.
Qed.

(* Begin_SpecReals *)

End CSetoid_basics.

(* End_SpecReals *)


Section product_csetoid.
(** **The product of setoids *)

Definition prod_ap (A B : CSetoid) (c d : prodT A B) : CProp.
intros A B H0 H1.
elim H0.
intros.
elim H1.
intros.
exact (cs_ap (c:=A) a a0 or cs_ap (c:=B) b b0).
Defined.

Definition prod_eq (A B : CSetoid) (c d : prodT A B) : Prop.
intros A B H0 H1.
elim H0.
intros.
elim H1.
intros.
exact (a[=]a0 /\ b[=]b0).
Defined.


Lemma prodcsetoid_is_CSetoid :
 forall A B : CSetoid, is_CSetoid (prodT A B) (prod_eq A B) (prod_ap A B).
intros A B.
apply (Build_is_CSetoid _ (prod_eq A B) (prod_ap A B)).
red in |- *.
intros.
case x.
unfold Not in |- *.
unfold prod_ap in |- *.
unfold prodT_rect in |- *.
intros c c0 H.
elim H.
intros.
apply (ap_irreflexive_unfolded A _ a).

intros.
apply (ap_irreflexive_unfolded B _ b).

red in |- *.
intros x y.
case x.
case y.
unfold prod_ap in |- *.
unfold prodT_rect in |- *.
intros c c0 c1 c2 H.
elim H.
intros.
left.
apply ap_symmetric_unfolded.
exact a.

intros.
right.
apply ap_symmetric_unfolded.
exact b.

red in |- *.
intros x y.
case x.
case y.
intros c c0 c1 c2 H z.
case z.
intros.
generalize H.
unfold prod_ap in |- *.
unfold prodT_rect in |- *.
intros.
elim H.
intros.
cut (c1[#]c3 or c3[#]c).
intros H1.
elim H1.
intros.
left.
left.
exact a0.

intros.
right.
left.
exact b.
apply (ap_cotransitive A).
exact a.

intros.
cut (c2[#]c4 or c4[#]c0).
intros H1.
elim H1.
intros.
left.
right.
exact a.

intros.
right.
right.
exact b0.

apply (ap_cotransitive B).
exact b.

red in |- *.
intros.
case x.
case y.
unfold prod_ap in |- *.
unfold prod_rect in |- *.
intros.
unfold prod_eq in |- *.
simpl in |- *.
split.
unfold Not in |- *.
intros.
split.
apply not_ap_imp_eq.
red in |- *.
intros H0.
cut (c1[#]c or c2[#]c0).
intros H1.
exact (H H1).
left.
exact H0.

apply not_ap_imp_eq.
red in |- *.
intros H0.
cut (c1[#]c or c2[#]c0).
intros H1.
exact (H H1).
right.
exact H0.

intros.
elim H.
unfold Not in |- *.
intros H0 H1 H2.
elim H2.
exact (eq_imp_not_ap A c1 c H0).

exact (eq_imp_not_ap B c2 c0 H1).
Qed.

Definition ProdCSetoid (A B : CSetoid) : CSetoid :=
  Build_CSetoid (prodT A B) (prod_eq A B) (prod_ap A B)
    (prodcsetoid_is_CSetoid A B).

End product_csetoid.
Implicit Arguments ex_unq [S].

Hint Resolve eq_reflexive_unfolded: algebra_r.
Hint Resolve eq_symmetric_unfolded: algebra_s.

Declare Left Step eq_wdl.
Declare Right Step eq_transitive_unfolded.

(* Begin_SpecReals *)

(** **Relations and predicates
Here we define the notions of well-definedness and strong extensionality
on predicates and relations.

%\begin{convention}%
Let [S] be a setoid.
%\end{convention}%

%\begin{nameconvention}%
- ``well-defined'' is abbreviated to [well_def] (or [wd]).
- ``strongly extensional'' is abbreviated to [strong_ext] (or [strext]).

%\end{nameconvention}%
*)

Section CSetoid_relations_and_predicates.
Variable S : CSetoid.

(* End_SpecReals *)

(** ***Predicates

At this stage, we should really consider [CProp]- and [Prop]-valued predicates
on setoids; however, for our applications, we will only need to consider the first type,
so that is all we introduce.

%\begin{convention}%
Let [P] be a predicate on (the carrier of) [S].
%\end{convention}%
*)

Section CSetoidPredicates.
Variable P : S -> CProp.

Definition pred_strong_ext : CProp := forall x y : S, P x -> P y or x[#]y.

Definition pred_well_def : CProp := forall x y : S, P x -> x[=]y -> P y.

End CSetoidPredicates.

(** ***Definition of a setoid predicate *)

Record CSetoid_predicate : Type := 
  {csp_pred :> S -> CProp; csp_strext : pred_strong_ext csp_pred}.

Lemma csp_wd : forall P : CSetoid_predicate, pred_well_def P.
intro P.
intro x; intros y H H0.
elim (csp_strext P x y H).

auto.

intro H1.
elimtype False.
generalize H1.
exact (eq_imp_not_ap _ _ _ H0).
Qed.


(* Begin_SpecReals *)

(** ***Relations
%\begin{convention}%
Let [R] be a relation on (the carrier of) [S].
%\end{convention}% *)

Section CsetoidRelations.
Variable R : S -> S -> Prop.

Definition rel_well_def_rht : Prop :=
  forall x y z : S, R x y -> y[=]z -> R x z.

Definition rel_well_def_lft : Prop :=
  forall x y z : S, R x y -> x[=]z -> R z y.

Definition rel_strong_ext : CProp :=
  forall x1 x2 y1 y2 : S, R x1 y1 -> (x1[#]x2 or y1[#]y2) or R x2 y2.

(* End_SpecReals *)

Definition rel_strong_ext_lft : CProp :=
  forall x1 x2 y : S, R x1 y -> x1[#]x2 or R x2 y.
Definition rel_strong_ext_rht : CProp :=
  forall x y1 y2 : S, R x y1 -> y1[#]y2 or R x y2.

Lemma rel_strext_imp_lftarg : rel_strong_ext -> rel_strong_ext_lft.
Proof.
unfold rel_strong_ext, rel_strong_ext_lft in |- *; intros H x1 x2 y H0.
generalize (H x1 x2 y y).
intros H1.
elim (H1 H0).

intro H3.
elim H3.

auto.

intro H4.
elim (ap_irreflexive S _ H4).

auto.
Qed.

Lemma rel_strext_imp_rhtarg : rel_strong_ext -> rel_strong_ext_rht.
unfold rel_strong_ext, rel_strong_ext_rht in |- *; intros H x y1 y2 H0.
generalize (H x x y1 y2 H0); intro H1.
elim H1; intro H2.

elim H2; intro H3.
elim (ap_irreflexive _ _ H3).

auto.

auto.
Qed.

Lemma rel_strextarg_imp_strext :
 rel_strong_ext_rht -> rel_strong_ext_lft -> rel_strong_ext.
unfold rel_strong_ext, rel_strong_ext_lft, rel_strong_ext_rht in |- *;
 intros H H0 x1 x2 y1 y2 H1.
elim (H x1 y1 y2 H1); intro H2.

auto.

elim (H0 x1 x2 y2 H2); auto.
Qed.

(* Begin_SpecReals *)

End CsetoidRelations.

(** ***Definition of a setoid relation
The type of relations over a setoid.  *)

Record CSetoid_relation : Type := 
  {csr_rel :> S -> S -> Prop;
   csr_wdr : rel_well_def_rht csr_rel;
   csr_wdl : rel_well_def_lft csr_rel;
   csr_strext : rel_strong_ext csr_rel}.

(** ***[CProp] Relations
%\begin{convention}%
Let [R] be a relation on (the carrier of) [S].
%\end{convention}%
*)

Section CCsetoidRelations.

Variable R : S -> S -> CProp.

Definition Crel_well_def_rht : CProp :=
  forall x y z : S, R x y -> y[=]z -> R x z.

Definition Crel_well_def_lft : CProp :=
  forall x y z : S, R x y -> x[=]z -> R z y.

Definition Crel_strong_ext : CProp :=
  forall x1 x2 y1 y2 : S, R x1 y1 -> R x2 y2 or x1[#]x2 or y1[#]y2.

(* End_SpecReals *)

Definition Crel_strong_ext_lft : CProp :=
  forall x1 x2 y : S, R x1 y -> R x2 y or x1[#]x2.

Definition Crel_strong_ext_rht : CProp :=
  forall x y1 y2 : S, R x y1 -> R x y2 or y1[#]y2.

Lemma Crel_strext_imp_lftarg : Crel_strong_ext -> Crel_strong_ext_lft.
Proof.
unfold Crel_strong_ext, Crel_strong_ext_lft in |- *; intros H x1 x2 y H0.
generalize (H x1 x2 y y).
intro H1.
elim (H1 H0).

auto.

intro H3.
elim H3; intro H4.

auto.
elim (ap_irreflexive _ _ H4).
Qed.

Lemma Crel_strext_imp_rhtarg : Crel_strong_ext -> Crel_strong_ext_rht.
unfold Crel_strong_ext, Crel_strong_ext_rht in |- *; intros H x y1 y2 H0.
generalize (H x x y1 y2 H0); intro H1.
elim H1; intro H2.

auto.

elim H2; intro H3.

elim (ap_irreflexive _ _ H3).

auto.
Qed.

Lemma Crel_strextarg_imp_strext :
 Crel_strong_ext_rht -> Crel_strong_ext_lft -> Crel_strong_ext.
unfold Crel_strong_ext, Crel_strong_ext_lft, Crel_strong_ext_rht in |- *;
 intros H H0 x1 x2 y1 y2 H1.
elim (H x1 y1 y2 H1); auto.
intro H2.
elim (H0 x1 x2 y2 H2); auto.
Qed.

(* Begin_SpecReals *)

End CCsetoidRelations.

(** ***Definition of a [CProp] setoid relation

The type of relations over a setoid.  *)

Record CCSetoid_relation : Type := 
  {Ccsr_rel :> S -> S -> CProp; Ccsr_strext : Crel_strong_ext Ccsr_rel}.

Lemma Ccsr_wdr : forall R : CCSetoid_relation, Crel_well_def_rht R.
intro R.
red in |- *; intros x y z H H0.
elim (Ccsr_strext R x x y z H).

auto.

intro H1; elimtype False.
elim H1; intro H2.

exact (ap_irreflexive_unfolded _ _ H2).

generalize H2.
exact (eq_imp_not_ap _ _ _ H0).
Qed.

Lemma Ccsr_wdl : forall R : CCSetoid_relation, Crel_well_def_lft R.
intro R.
red in |- *; intros x y z H H0.
elim (Ccsr_strext R x z y y H).

auto.

intro H1; elimtype False.
elim H1; intro H2.

generalize H2.
exact (eq_imp_not_ap _ _ _ H0).

exact (ap_irreflexive_unfolded _ _ H2).
Qed.

(* End_SpecReals *)

Lemma ap_well_def_rht : Crel_well_def_rht (cs_ap (c:=S)).
red in |- *; intros x y z H H0.
generalize (eq_imp_not_ap _ _ _ H0); intro H1.
elim (ap_cotransitive_unfolded _ _ _ H z); intro H2.

assumption.

elim H1.
apply ap_symmetric_unfolded.
assumption.
Qed.

Lemma ap_well_def_lft : Crel_well_def_lft (cs_ap (c:=S)).
red in |- *; intros x y z H H0.
generalize (ap_well_def_rht y x z); intro H1.
apply ap_symmetric_unfolded.
apply H1.

apply ap_symmetric_unfolded.
assumption.

assumption.
Qed.

Lemma ap_well_def_rht_unfolded : forall x y z : S, x[#]y -> y[=]z -> x[#]z.
Proof ap_well_def_rht.

Lemma ap_well_def_lft_unfolded : forall x y z : S, x[#]y -> x[=]z -> z[#]y.
Proof ap_well_def_lft.

Lemma ap_strong_ext : Crel_strong_ext (cs_ap (c:=S)).
red in |- *; intros x1 x2 y1 y2 H.
case (ap_cotransitive_unfolded _ _ _ H x2); intro H0.

auto.

case (ap_cotransitive_unfolded _ _ _ H0 y2); intro H1.

auto.

right; right.
apply ap_symmetric_unfolded.
assumption.
Qed.

Definition predS_well_def (P : S -> CProp) : CProp :=
  forall x y : S, P x -> x[=]y -> P y.

(* Begin_SpecReals *)

End CSetoid_relations_and_predicates.

Declare Left Step ap_well_def_lft_unfolded.
Declare Right Step ap_well_def_rht_unfolded.

(* End_SpecReals *)

(** **Functions between setoids
Such functions must preserve the setoid equality
and be strongly extensional w.r.t.%\% the apartness, i.e.%\%
if [f(x,y) [#] f(x1,y1)], then  [x [#] x1 + y [#] y1].
For every arity this has to be defined separately.
%\begin{convention}%
Let [S1], [S2] and [S3] be setoids.
%\end{convention}%

First we consider unary functions.  *)

(* Begin_SpecReals *)

Section CSetoid_functions.
Variables S1 S2 S3 : CSetoid.


Section unary_functions.

(**
In the following two definitions,
[f] is a function from (the carrier of) [S1] to
(the carrier of) [S2].  *)

Variable f : S1 -> S2.

Definition fun_well_def : Prop := forall x y : S1, x[=]y -> f x[=]f y.

Definition fun_strong_ext : CProp := forall x y : S1, f x[#]f y -> x[#]y.

(* End_SpecReals *)

Lemma fun_strong_ext_imp_well_def : fun_strong_ext -> fun_well_def.
unfold fun_strong_ext in |- *.
unfold fun_well_def in |- *.
intros H x y H0.
apply not_ap_imp_eq.
intro H1.
generalize (H _ _ H1); intro H2.
generalize (eq_imp_not_ap _ _ _ H0); intro H3.
elim H3; assumption.
Qed.

(* Begin_SpecReals *)

End unary_functions.

Record CSetoid_fun : Type := 
  {csf_fun :> S1 -> S2; csf_strext : fun_strong_ext csf_fun}.

Lemma csf_wd : forall f : CSetoid_fun, fun_well_def f.
intro f.
apply fun_strong_ext_imp_well_def.
apply csf_strext.
Qed.

(* End_SpecReals *)

Definition Const_CSetoid_fun : S2 -> CSetoid_fun.
intro c; apply (Build_CSetoid_fun (fun x : S1 => c)); red in |- *;
 intros x y H.
(* str ext *)
elim (ap_irreflexive _ _ H).
Defined.

(* Begin_SpecReals *)

Section binary_functions.

(**
Now we consider binary functions.
In the following two definitions,
[f] is a function from [S1] and [S2] to [S3].
*)
Variable f : S1 -> S2 -> S3.

Definition bin_fun_well_def : Prop :=
  forall (x1 x2 : S1) (y1 y2 : S2), x1[=]x2 -> y1[=]y2 -> f x1 y1[=]f x2 y2.

Definition bin_fun_strong_ext : CProp :=
  forall (x1 x2 : S1) (y1 y2 : S2), f x1 y1[#]f x2 y2 -> x1[#]x2 or y1[#]y2.

(* End_SpecReals *)

Lemma bin_fun_strong_ext_imp_well_def :
 bin_fun_strong_ext -> bin_fun_well_def.
unfold bin_fun_strong_ext in |- *.
unfold bin_fun_well_def in |- *.
intros H x1 x2 y1 y2 H0 H1.
apply not_ap_imp_eq.
intro H2.
generalize (H _ _ _ _ H2); intro H3.
elim H3; intro H4.

generalize (eq_imp_not_ap _ _ _ H0); intro H5.
elim H5; assumption.

generalize (eq_imp_not_ap _ _ _ H1); intro H5.
elim H5; assumption.
Qed.

(* Begin_SpecReals *)

End binary_functions.

Record CSetoid_bin_fun : Type := 
  {csbf_fun :> S1 -> S2 -> S3; csbf_strext : bin_fun_strong_ext csbf_fun}.

Lemma csbf_wd : forall f : CSetoid_bin_fun, bin_fun_well_def f.
intro f.
apply bin_fun_strong_ext_imp_well_def.
apply csbf_strext.
Qed.

Lemma csetoid_fun_wd_unfolded :
 forall (f : CSetoid_fun) (x x' : S1), x[=]x' -> f x[=]f x'.
intros f x x' H.
apply (csf_wd f x x').
assumption.
Qed.

Lemma csetoid_fun_strext_unfolded :
 forall (f : CSetoid_fun) (x y : S1), f x[#]f y -> x[#]y.
intros f x y H.
apply (csf_strext f x y).
assumption.
Qed.

Lemma csetoid_bin_fun_wd_unfolded :
 forall (f : CSetoid_bin_fun) (x x' : S1) (y y' : S2),
 x[=]x' -> y[=]y' -> f x y[=]f x' y'.
intros f x x' y y' H H0.
apply (csbf_wd f x x' y y'); assumption.
Qed.

End CSetoid_functions.

(* End_SpecReals *)

Hint Resolve csetoid_fun_wd_unfolded csetoid_bin_fun_wd_unfolded: algebra_c.

Implicit Arguments fun_well_def [S1 S2].
Implicit Arguments fun_strong_ext [S1 S2].

(* Begin_SpecReals *)

(** **The unary and binary (inner) operations on a csetoid
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

Definition commutes (f : S -> S -> S) : Prop := forall x y : S, f x y[=]f y x.

Definition associative (f : S -> S -> S) : Prop :=
  forall x y z : S, f x (f y z)[=]f (f x y) z.

(** Well-defined unary operations on a setoid.  *)

Definition un_op_well_def := fun_well_def (S1:=S) (S2:=S).
Definition un_op_strong_ext := fun_strong_ext (S1:=S) (S2:=S).

Definition CSetoid_un_op : Type := CSetoid_fun S S.
Definition Build_CSetoid_un_op := Build_CSetoid_fun S S.

(* End_SpecReals *)

Lemma id_strext : un_op_strong_ext (fun x : S => x).
unfold un_op_strong_ext in |- *.
unfold fun_strong_ext in |- *.
auto.
Qed.

Lemma id_pres_eq : un_op_well_def (fun x : S => x).
unfold un_op_well_def in |- *.
unfold fun_well_def in |- *.
auto.
Qed.

Definition id_un_op := Build_CSetoid_un_op (fun x : S => x) id_strext.
(* begin hide *)
Identity Coercion un_op_fun : CSetoid_un_op >-> CSetoid_fun.
(* end hide *)
(* Begin_SpecReals *)

Definition un_op_strext := csf_strext S S.

(* End_SpecReals *)

Lemma un_op_wd_unfolded :
 forall (op : CSetoid_un_op) (x y : S), x[=]y -> op x[=]op y.
Proof csf_wd S S.

Lemma un_op_strext_unfolded :
 forall (op : CSetoid_un_op) (x y : S), op x[#]op y -> x[#]y.
exact un_op_strext.
Qed.

(** Well-defined binary operations on a setoid.  *)

Definition bin_op_well_def := bin_fun_well_def S S S.
Definition bin_op_strong_ext := bin_fun_strong_ext S S S.

(* Begin_SpecReals *)

Definition CSetoid_bin_op : Type := CSetoid_bin_fun S S S.
Definition Build_CSetoid_bin_op := Build_CSetoid_bin_fun S S S.

(* End_SpecReals *)

Definition bin_op_wd := csbf_wd S S S.
Definition bin_op_strext := csbf_strext S S S.

(* Begin_SpecReals *)
(* begin hide *)
Identity Coercion bin_op_bin_fun : CSetoid_bin_op >-> CSetoid_bin_fun.
(* end hide *)
(* End_SpecReals *)

Lemma bin_op_wd_unfolded :
 forall (op : CSetoid_bin_op) (x1 x2 y1 y2 : S),
 x1[=]x2 -> y1[=]y2 -> op x1 y1[=]op x2 y2.
exact bin_op_wd.
Qed.

Lemma bin_op_strext_unfolded :
 forall (op : CSetoid_bin_op) (x1 x2 y1 y2 : S),
 op x1 y1[#]op x2 y2 -> x1[#]x2 or y1[#]y2.
exact bin_op_strext.
Qed.

Lemma bin_op_is_wd_un_op_lft :
 forall (op : CSetoid_bin_op) (c : S), un_op_well_def (fun x : S => op x c).
Proof.
intros op c. unfold un_op_well_def in |- *. unfold fun_well_def in |- *.
intros x y H. apply bin_op_wd_unfolded. trivial. apply eq_reflexive_unfolded.
Qed.

Lemma bin_op_is_wd_un_op_rht :
 forall (op : CSetoid_bin_op) (c : S), un_op_well_def (fun x : S => op c x).
Proof.
intros op c. unfold un_op_well_def in |- *. unfold fun_well_def in |- *.
intros x y H. apply bin_op_wd_unfolded. apply eq_reflexive_unfolded. trivial.
Qed.

Lemma bin_op_is_strext_un_op_lft :
 forall (op : CSetoid_bin_op) (c : S), un_op_strong_ext (fun x : S => op x c).
Proof.
intros op c. unfold un_op_strong_ext in |- *. unfold fun_strong_ext in |- *.
intros x y H. cut (x[#]y or c[#]c). intro Hv. elim Hv. trivial. intro Hf.
generalize (ap_irreflexive_unfolded _ c Hf). intro. elim H0.
apply bin_op_strext_unfolded with op. trivial.
Qed.

Lemma bin_op_is_strext_un_op_rht :
 forall (op : CSetoid_bin_op) (c : S), un_op_strong_ext (fun x : S => op c x).
Proof.
intros op c. unfold un_op_strong_ext in |- *. unfold fun_strong_ext in |- *.
intros x y H. cut (c[#]c or x[#]y). intro Hv. elim Hv. intro Hf.
generalize (ap_irreflexive_unfolded _ c Hf). tauto. auto.
apply bin_op_strext_unfolded with op. trivial.
Qed.

Definition bin_op2un_op_rht (op : CSetoid_bin_op) (c : S) : CSetoid_un_op :=
  Build_CSetoid_un_op (fun x : S => op c x) (bin_op_is_strext_un_op_rht op c).

Definition bin_op2un_op_lft (op : CSetoid_bin_op) (c : S) : CSetoid_un_op :=
  Build_CSetoid_un_op (fun x : S => op x c) (bin_op_is_strext_un_op_lft op c).

(* Begin_SpecReals *)

End csetoid_inner_ops.

(* End_SpecReals *)

Implicit Arguments commutes [S].

(* Begin_SpecReals *)

Implicit Arguments associative [S].

(* End_SpecReals *)

Hint Resolve bin_op_wd_unfolded un_op_wd_unfolded: algebra_c.

(** **The binary outer operations on a csetoid
%\begin{convention}%
Let [S1] and [S2] be setoids.
%\end{convention}%
*)

Section csetoid_outer_ops.
Variables S1 S2 : CSetoid.

(**
Well-defined outer operations on a setoid.
*)
Definition outer_op_well_def := bin_fun_well_def S1 S2 S2.
Definition outer_op_strong_ext := bin_fun_strong_ext S1 S2 S2.

Definition CSetoid_outer_op : Type := CSetoid_bin_fun S1 S2 S2.
Definition Build_CSetoid_outer_op := Build_CSetoid_bin_fun S1 S2 S2.
Definition csoo_wd := csbf_wd S1 S2 S2.
Definition csoo_strext := csbf_strext S1 S2 S2.

(* begin hide *)
Identity Coercion outer_op_bin_fun : CSetoid_outer_op >-> CSetoid_bin_fun.
(* end hide *)

Lemma csoo_wd_unfolded :
 forall (op : CSetoid_outer_op) (x1 x2 : S1) (y1 y2 : S2),
 x1[=]x2 -> y1[=]y2 -> op x1 y1[=]op x2 y2.
exact csoo_wd.
Qed.

End csetoid_outer_ops.
Hint Resolve csoo_wd_unfolded: algebra_c.

(* Begin_SpecReals *)

(** **Subsetoids
%\begin{convention}%
Let [S] be a setoid, and [P] a predicate on the carrier of [S].
%\end{convention}%
*)

Section SubCSetoids.
Variable S : CSetoid.
Variable P : S -> CProp.

Record subcsetoid_crr : Type :=  {scs_elem :> S; scs_prf : P scs_elem}.

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
  restrict_relation (cs_eq (c:=S)).

Definition subcsetoid_ap : Crelation subcsetoid_crr :=
  Crestrict_relation (cs_ap (c:=S)).

(* End_SpecReals *)

Remark subcsetoid_equiv : Tequiv _ subcsetoid_eq.
unfold subcsetoid_eq in |- *; split.
(* reflexive *)
red in |- *; intros a; case a.
intros x s; red in |- *.
apply (eq_reflexive S).
(* transitive *)
split.
red in |- *; intros a b c; case a.
intros x s; case b.
intros y t; case c.
intros z u; simpl in |- *.
exact (eq_transitive _ x y z).
(* symmetric *)
red in |- *.
intros a b; case a.
intros x s; case b.
intros y t; simpl in |- *.
exact (eq_symmetric _ x y).
Qed.

(* Begin_SpecReals *)

Lemma subcsetoid_is_CSetoid : is_CSetoid _ subcsetoid_eq subcsetoid_ap.
apply (Build_is_CSetoid _ subcsetoid_eq subcsetoid_ap).
(* irreflexive *)
red in |- *; intros. case x. unfold Not in |- *; intros.
exact (ap_irreflexive_unfolded S _ X).
(* symmetric *)
red in |- *; intros x y. case x. case y. intros.
exact (ap_symmetric S _ _ X).
(* cotransitive *)
red in |- *; intros x y. case x. case y. intros; case z. intros.
exact (ap_cotransitive S _ _ X scs_elem2).
(* tight *)
red in |- *; intros. case x. case y. intros.
exact (ap_tight S scs_elem1 scs_elem0).
Qed.

Definition Build_SubCSetoid : CSetoid :=
  Build_CSetoid subcsetoid_crr subcsetoid_eq subcsetoid_ap
    subcsetoid_is_CSetoid.

(* End_SpecReals *)

(** ***Subsetoid unary operations
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

Lemma restr_un_op_well_def : un_op_well_def Build_SubCSetoid restr_un_op.
red in |- *. red in |- *. intros x y. case y. case x. intros.
  exact (un_op_wd_unfolded _ f _ _ H).
Qed.

Lemma restr_un_op_strong_ext : un_op_strong_ext Build_SubCSetoid restr_un_op.
red in |- *. red in |- *. intros x y. case y. case x. intros.
  exact (un_op_strext _ f _ _ X).
Qed.

Definition Build_SubCSetoid_un_op : CSetoid_un_op Build_SubCSetoid :=
  Build_CSetoid_un_op Build_SubCSetoid restr_un_op restr_un_op_strong_ext.

End SubCSetoid_unary_operations.


(** ***Subsetoid binary operations
%\begin{convention}%
Let [f] be a binary setoid operation on [S].
%\end{convention}%
*)

Section SubCSetoid_binary_operations.

Variable f : CSetoid_bin_op S.

Definition bin_op_pres_pred : CProp :=
  forall x y : S, P x -> P y -> P (f x y).

(**
%\begin{convention}%
Assume [un_op_pres_pred].
%\end{convention}%
*)

Variable pr : bin_op_pres_pred.

Definition restr_bin_op (a b : subcsetoid_crr) : subcsetoid_crr :=
  match a, b with
  | Build_subcsetoid_crr x p, Build_subcsetoid_crr y q =>
      Build_subcsetoid_crr (f x y) (pr x y p q)
  end.

Lemma restr_bin_op_well_def : bin_op_well_def Build_SubCSetoid restr_bin_op.
red in |- *. red in |- *. intros x1 x2 y1 y2. case y2. case y1. case x2. case x1. intros.
  exact (bin_op_wd _ f _ _ _ _ H H0).
Qed.

Lemma restr_bin_op_strong_ext :
 bin_op_strong_ext Build_SubCSetoid restr_bin_op.
red in |- *. red in |- *. intros x1 x2 y1 y2. case y2. case y1. case x2. case x1. intros.
  exact (bin_op_strext _ f _ _ _ _ X).
Qed.

Definition Build_SubCSetoid_bin_op : CSetoid_bin_op Build_SubCSetoid :=
  Build_CSetoid_bin_op Build_SubCSetoid restr_bin_op restr_bin_op_strong_ext.


Lemma restr_f_assoc : associative f -> associative Build_SubCSetoid_bin_op.
intro. red in |- *. intros x y z. case z. case y. case x. intros.
simpl in |- *.
apply H.
Qed.


End SubCSetoid_binary_operations.


(* Begin_SpecReals *)

End SubCSetoids.

(* End_SpecReals *)

Ltac Step_final x := apply eq_transitive_unfolded with x; Algebra.

Tactic Notation "Step_final" constr(c) :=  Step_final c.

(** **Miscellaneous
*)

Lemma proper_caseZ_diff_CS :
 forall (S : CSetoid) (f : nat -> nat -> S),
 (forall m n p q : nat, m + q = n + p -> f m n[=]f p q) ->
 forall m n : nat, caseZ_diff (m - n) f[=]f m n.
intro CS.
intros.
pattern m, n in |- *.
apply nat_double_ind.
intro.
replace (0%nat - n0)%Z with (- n0)%Z.
rewrite caseZ_diff_Neg.
apply eq_reflexive_unfolded.
simpl in |- *.
reflexivity.
intros.
replace (S n0 - 0%nat)%Z with (S n0:Z).
rewrite caseZ_diff_Pos.
apply eq_reflexive_unfolded.
simpl in |- *.
reflexivity.
intros.
generalize (H (S n0) (S m0) n0 m0); intro.
cut (S n0 + m0 = S m0 + n0).
intro.
generalize (H1 H2); intro.
apply eq_transitive_unfolded with (f n0 m0).
apply eq_transitive_unfolded with (caseZ_diff (n0 - m0) f).
replace (S n0 - S m0)%Z with (n0 - m0)%Z.
apply eq_reflexive_unfolded.
repeat rewrite Znat.inj_S.
clear H1; auto with zarith.
assumption.
apply eq_symmetric_unfolded.
assumption.
clear H1; auto with zarith.
Qed.

(**
Finally, we characterize functions defined on the natural numbers also as setoid functions, similarly to what we already did for predicates.
*)

Definition nat_less_n_fun (S : CSetoid) (n : nat)
  (f : forall i : nat, i < n -> S) :=
  forall i j : nat, i = j -> forall (H : i < n) (H' : j < n), f i H[=]f j H'.

Definition nat_less_n_fun' (S : CSetoid) (n : nat)
  (f : forall i : nat, i <= n -> S) :=
  forall i j : nat,
  i = j -> forall (H : i <= n) (H' : j <= n), f i H[=]f j H'.
