(* $Id$ *)

(** printing Zero %\ensuremath{\mathbf0}% #0# *)

Require Export CSemiGroups.

(* Begin_SpecReals *)

(**
* Monoids %\label{section:monoids}%
** Definition of monoids
*)

Definition is_rht_unit (S : CSetoid) (op : CSetoid_bin_op S) 
  (zero : S) : Prop := forall x : S, op x zero[=]x.

(* End_SpecReals *)

Definition is_lft_unit (S : CSetoid) (op : CSetoid_bin_op S) 
  (zero : S) : Prop := forall x : S, op zero x[=]x.

Implicit Arguments is_lft_unit [S].

(* Begin_SpecReals *)

Implicit Arguments is_rht_unit [S].

Record is_CMonoid (M : CSemiGroup) (zero : M) : Prop := 
  {runit : is_rht_unit (csg_op (c:=M)) zero;
   lunit : is_lft_unit (csg_op (c:=M)) zero}.

Record CMonoid : Type := 
  {cm_crr :> CSemiGroup;
   cm_unit : cm_crr;
   cm_proof : is_CMonoid cm_crr cm_unit}.

(**
%\begin{nameconvention}%
In the names of lemmas, we will denote [Zero] with [zero].
We denote [ [#]  Zero] in the names of lemmas by [ap_zero]
(and not, e.g.%\% [nonzero]).
%\end{nameconvention}%
*)

(* Begin_SpecReals *)

(**
The predicate "non-zero" is defined.
In lemmas we will continue to write [x [#] Zero], rather than
[(nonZeroP x)], but the predicate is useful for some high-level definitions,
e.g. for the setoid of non-zeros.
*)

Notation Zero := (cm_unit _).
(* Syntax is discontinued Syntax constr level 1 :
                           cm_unit_constant
                           [<<(APPLIST (CONST <CMonoids#2>. cm_unit) $e0)>>]
                           -> [ "Zero" ] *)

Definition nonZeroP (M : CMonoid) (x : M) : CProp := x[#]Zero.

(* End_SpecReals *)

Implicit Arguments nonZeroP [M].

(**
** Monoid axioms
%\begin{convention}%
Let [M] be a monoid.
%\end{convention}%
*)
Section CMonoid_axioms.
Variable M : CMonoid.

Lemma CMonoid_is_CMonoid : is_CMonoid M (cm_unit M).
elim M; auto.
Qed.

Lemma cm_rht_unit : is_rht_unit csg_op (Zero:M).
elim CMonoid_is_CMonoid; auto.
Qed.

Lemma cm_lft_unit : is_lft_unit csg_op (Zero:M).
elim CMonoid_is_CMonoid; auto.
Qed.

End CMonoid_axioms.

(**
** Monoid basics
%\begin{convention}%
Let [M] be a monoid.
%\end{convention}%
*)
Section CMonoid_basics.
Variable M : CMonoid.

Lemma cm_rht_unit_unfolded : forall x : M, x[+]Zero[=]x.
Proof cm_rht_unit M.

Lemma cm_lft_unit_unfolded : forall x : M, Zero[+]x[=]x.
Proof cm_lft_unit M.

Hint Resolve cm_rht_unit_unfolded cm_lft_unit_unfolded: algebra.

Lemma cm_unit_unique_lft : forall x : M, is_lft_unit csg_op x -> x[=]Zero.
intros x h. red in h.
Step_final (x[+]Zero).
Qed.

Lemma cm_unit_unique_rht : forall x : M, is_rht_unit csg_op x -> x[=]Zero.
intros x h. red in h.
Step_final (Zero[+]x).
Qed.

(* Begin_SpecReals *)

(**
The proof component of the monoid is irrelevant.
*)
Lemma is_CMonoid_proof_irr :
 forall (S : CSetoid) (zero : S) (plus : CSetoid_bin_op S)
   (p q : associative plus),
 is_CMonoid (Build_CSemiGroup S plus p) zero ->
 is_CMonoid (Build_CSemiGroup S plus q) zero.
intros S one mult p q H.
elim H; intros runit0 lunit0.
simpl in runit0.
simpl in lunit0.
apply Build_is_CMonoid; simpl in |- *; assumption.
Qed.

(* End_SpecReals *)

(**
** Submonoids
%\begin{convention}%
Let [P] a predicate on [M] containing [Zero] and closed under [[+]].
%\end{convention}%
*)

Section SubCMonoids.
Variable P : M -> CProp.
Variable Punit : P Zero.
Variable op_pres_P : bin_op_pres_pred _ P csg_op.

Let subcrr : CSemiGroup := Build_SubCSemiGroup _ _ op_pres_P.

Lemma ismon_scrr : is_CMonoid subcrr (Build_subcsetoid_crr _ _ _ Punit).
split; red in |- *.

(* right unit *)
intro x. case x. intros scs_elem scs_prf.
apply (cm_rht_unit_unfolded scs_elem).

(* left unit *)
intro x. case x. intros scs_elem scs_prf.
apply (cm_lft_unit_unfolded scs_elem).
Qed.

Definition Build_SubCMonoid : CMonoid := Build_CMonoid subcrr _ ismon_scrr.

End SubCMonoids.

End CMonoid_basics.

Hint Resolve cm_rht_unit_unfolded cm_lft_unit_unfolded: algebra.
