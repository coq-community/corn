(* $Id$ *)

(** printing [-] %\ensuremath-% #&minus;# *)
(** printing [--] %\ensuremath-% #&minus;# *)
(** printing {-} %\ensuremath-% #&minus;# *)
(** printing {--} %\ensuremath-% #&minus;# *)
(** printing [+][--] %\ensuremath{+-}% #+&minus;# *)
(** printing {+}{--} %\ensuremath{+-}% #+&minus;# *)

Require Export CMonoids.

(* Begin_SpecReals *)

(**
* Groups
** Definition of the notion of Group
*)
Definition is_inverse (S : CSetoid) (op : CSetoid_bin_op S) 
  (one x x_inv : S) : Prop := op x x_inv[=]one /\ op x_inv x[=]one.

Implicit Arguments is_inverse [S].

Definition is_CGroup (G : CMonoid) (inv : CSetoid_un_op G) :=
  forall x : G, is_inverse csg_op Zero x (inv x).

Record CGroup : Type := 
  {cg_crr :> CMonoid;
   cg_inv : CSetoid_un_op cg_crr;
   cg_proof : is_CGroup cg_crr cg_inv}.

(* End_SpecReals *)

(* Begin_SpecReals *)


Implicit Arguments cg_inv [c].
Notation "[--] x" := (cg_inv x) (at level 2, right associativity).

Definition cg_minus (G : CGroup) (x y : G) := x[+][--]y.

(**
%\begin{nameconvention}%
In the names of lemmas, we will denote [[--]] with [inv],
and [[-]] with [minus].
%\end{nameconvention}%
*)

Implicit Arguments cg_minus [G].
Infix "[-]" := cg_minus (at level 50, left associativity).

(* End_SpecReals *)

(**
** Group axioms
%\begin{convention}%
Let [G] be a group.
%\end{convention}%
*)
Section CGroup_axioms.
Variable G : CGroup.

Lemma cg_inverse : forall x : G, is_inverse csg_op Zero x [--]x.
Proof cg_proof G.

End CGroup_axioms.

(**
** Group basics
General properties of groups.
%\begin{convention}%
Let [G] be a group.
%\end{convention}%
*)
Section CGroup_basics.
Variable G : CGroup.

Lemma cg_rht_inv_unfolded : forall x : G, x[+][--]x[=]Zero.
intro x; elim (cg_inverse G x); auto.
Qed.

Lemma cg_lft_inv_unfolded : forall x : G, [--]x[+]x[=]Zero.
intro x; elim (cg_inverse G x); auto.
Qed.

Lemma cg_minus_correct : forall x : G, x[-]x[=]Zero.
intro x.
unfold cg_minus in |- *.
apply cg_rht_inv_unfolded.
Qed.
Hint Resolve cg_rht_inv_unfolded cg_lft_inv_unfolded cg_minus_correct:
  algebra.

Lemma cg_inverse' : forall x : G, is_inverse csg_op Zero [--]x x.
intro x.
split; Algebra.
Qed.

(* Hints for Auto *)
Lemma cg_minus_unfolded : forall x y : G, x[-]y[=]x[+][--]y.
Algebra.
Qed.
Hint Resolve cg_minus_unfolded: algebra.

Lemma cg_minus_wd : forall x x' y y' : G, x[=]x' -> y[=]y' -> x[-]y[=]x'[-]y'.
intros x x' y y' H H0.
unfold cg_minus in |- *.
Step_final (x[+][--]y').
Qed.
Hint Resolve cg_minus_wd: algebra_c.

Lemma cg_minus_strext :
 forall x x' y y' : G, x[-]y[#]x'[-]y' -> x[#]x' or y[#]y'.
intros x x' y y' H. cut (x[#]x' or [--]y[#][--]y').
intro H0. elim H0.
 left; trivial.
intro H1.
right; exact (un_op_strext G cg_inv y y' H1).

apply bin_op_strext_unfolded with (csg_op (c:=G)). trivial.
Qed.

Definition cg_minus_is_csetoid_bin_op : CSetoid_bin_op G :=
  Build_CSetoid_bin_op G (cg_minus (G:=G)) cg_minus_strext.

Lemma grp_inv_assoc : forall x y : G, x[+]y[-]y[=]x.
intros x y; unfold cg_minus in |- *.
AStepl (x[+](y[+][--]y)).
Step_final (x[+]Zero).
Qed.
Hint Resolve grp_inv_assoc: algebra.

Lemma cg_inv_unique : forall x y : G, x[+]y[=]Zero -> y[=][--]x.
Proof.
intros x y H.
AStepl (Zero[+]y).
AStepl ([--]x[+]x[+]y).
AStepl ([--]x[+](x[+]y)).
Step_final ([--]x[+]Zero).
Qed.

Lemma cg_inv_inv : forall x : G, [--][--]x[=]x.
Proof.
intro x.
AStepl (Zero[+][--][--]x).
AStepl (x[+][--]x[+][--][--]x).
AStepl (x[+]([--]x[+][--][--]x)).
Step_final (x[+]Zero).
Qed.
Hint Resolve cg_inv_inv: algebra.

Lemma cg_cancel_lft : forall x y z : G, x[+]y[=]x[+]z -> y[=]z.
Proof.
intros x y z H.
AStepl (Zero[+]y).
AStepl ([--]x[+]x[+]y).
AStepl ([--]x[+](x[+]y)).
AStepl ([--]x[+](x[+]z)).
AStepl ([--]x[+]x[+]z).
Step_final (Zero[+]z).
Qed.

Lemma cg_cancel_rht : forall x y z : G, y[+]x[=]z[+]x -> y[=]z.
Proof.
intros x y z H.
AStepl (y[+]Zero).
AStepl (y[+](x[+][--]x)).
AStepl (y[+]x[+][--]x).
AStepl (z[+]x[+][--]x).
AStepl (z[+](x[+][--]x)).
Step_final (z[+]Zero).
Qed.

Lemma cg_inv_unique' : forall x y : G, x[+]y[=]Zero -> x[=][--]y.
Proof.
intros x y H.
AStepl (x[+]Zero).
AStepl (x[+](y[+][--]y)).
AStepl (x[+]y[+][--]y).
Step_final (Zero[+][--]y).
Qed.

Lemma cg_inv_unique_2 : forall x y : G, x[-]y[=]Zero -> x[=]y.
intros x y H.
generalize (cg_inv_unique _ _ H); intro H0.
AStepl ([--][--]x).
Step_final ([--][--]y).
Qed.

Lemma cg_zero_inv : [--](Zero:G)[=]Zero.
apply eq_symmetric_unfolded; apply cg_inv_unique; Algebra.
Qed.

Hint Resolve cg_zero_inv: algebra.

Lemma cg_inv_zero : forall x : G, x[-]Zero[=]x.
intro x.
unfold cg_minus in |- *.
Step_final (x[+]Zero).
Qed.

Lemma cg_inv_op : forall x y : G, [--](x[+]y)[=][--]y[+][--]x.
intros x y.
apply (eq_symmetric G).
apply cg_inv_unique.
AStepl (x[+]y[+][--]y[+][--]x).
AStepl (x[+](y[+][--]y)[+][--]x).
AStepl (x[+]Zero[+][--]x).
Step_final (x[+][--]x).
Qed.

(**
Useful for interactive proof development.
*)

Lemma x_minus_x : forall x y : G, x[=]y -> x[-]y[=]Zero.
intros x y H; Step_final (x[-]x).
Qed.

(**
** Sub-groups
%\begin{convention}%
Let [P] be a predicate on [G] containing
[Zero] and closed under [[+]] and [[--]].
%\end{convention}%
*)
Section SubCGroups.
Variable P : G -> CProp.
Variable Punit : P Zero.
Variable op_pres_P : bin_op_pres_pred _ P csg_op.
Variable inv_pres_P : un_op_pres_pred _ P cg_inv.

Let subcrr : CMonoid := Build_SubCMonoid _ _ Punit op_pres_P.
Let subinv : CSetoid_un_op subcrr := Build_SubCSetoid_un_op _ _ _ inv_pres_P.

Lemma isgrp_scrr : is_CGroup subcrr subinv.
red in |- *. intro x. case x. intros. split; simpl in |- *; Algebra.
Qed.

Definition Build_SubCGroup : CGroup := Build_CGroup subcrr _ isgrp_scrr.

End SubCGroups.

End CGroup_basics.

Hint Resolve cg_rht_inv_unfolded cg_lft_inv_unfolded: algebra.
Hint Resolve cg_inv_inv cg_minus_correct cg_zero_inv cg_inv_zero: algebra.
Hint Resolve cg_minus_unfolded grp_inv_assoc cg_inv_op: algebra.
Hint Resolve cg_minus_wd: algebra_c.

(**
** Associative properties of groups
%\begin{convention}%
Let [G] be a group.
%\end{convention}%
*)
Section Assoc_properties.
Variable G : CGroup.

Lemma assoc_2 : forall x y z : G, x[+](y[-]z)[=]x[+]y[-]z.
intros x y z; unfold cg_minus in |- *; Algebra.
Qed.

Lemma zero_minus : forall x : G, Zero[-]x[=][--]x.
intro x.
unfold cg_minus in |- *.
Algebra.
Qed.

Lemma cg_cancel_mixed : forall x y : G, x[=]x[-]y[+]y.
 intros x y.
 unfold cg_minus in |- *.
 AStepr (x[+]([--]y[+]y)).
 Step_final (x[+]Zero).
Qed.

Lemma plus_resp_eq : forall x y z : G, y[=]z -> x[+]y[=]x[+]z.
Algebra.
Qed.

End Assoc_properties.

Hint Resolve assoc_2 minus_plus zero_minus cg_cancel_mixed plus_resp_eq:
  algebra.


(**
** Apartness in Constructive Groups
Specific properties of apartness.
%\begin{convention}%
Let [G] be a group.
%\end{convention}%
*)
Section cgroups_apartness.
Variable G : CGroup.

Lemma cg_add_ap_zero : forall x y : G, x[+]y[#]Zero -> x[#]Zero or y[#]Zero.
intros x y H.
apply (bin_op_strext _ csg_op x Zero y Zero).
AStepr (Zero:G).
auto.
Qed.

Lemma op_rht_resp_ap : forall x y z : G, x[#]y -> x[+]z[#]y[+]z.
intros x y z H.
cut (x[+]z[-]z[#]y[+]z[-]z).
intros h.
case (bin_op_strext _ _ _ _ _ _ h).
 auto.
intro contra; elim (ap_irreflexive _ _ contra).

AStepl x; AStepr y. auto.
Qed.

Lemma cg_ap_cancel_rht : forall x y z : G, x[+]z[#]y[+]z -> x[#]y.
intros x y z H.
apply ap_well_def_rht_unfolded with (y[+]z[-]z).
 apply ap_well_def_lft_unfolded with (x[+]z[-]z).
  apply (op_rht_resp_ap _ _ [--]z H).
 AStepr (x[+]Zero).
 Step_final (x[+](z[-]z)).
AStepr (y[+]Zero).
Step_final (y[+](z[-]z)).
Qed.

Lemma plus_cancel_ap_rht : forall x y z : G, x[+]z[#]y[+]z -> x[#]y.
Proof cg_ap_cancel_rht.

Lemma minus_ap_zero : forall x y : G, x[#]y -> x[-]y[#]Zero.
intros x y H.
AStepr (y[-]y).
unfold cg_minus in |- *.
apply op_rht_resp_ap; assumption.
Qed.

Lemma zero_minus_apart : forall x y : G, x[-]y[#]Zero -> x[#]y.
unfold cg_minus in |- *. intros x y H.
cut (x[+][--]y[#]y[+][--]y). intros h.
apply (cg_ap_cancel_rht _ _ _ h).

AStepr (Zero:G). auto.
Qed.

Lemma inv_resp_ap_zero : forall x : G, x[#]Zero -> [--]x[#]Zero.
intros x H.
AStepl (Zero[+][--]x).
AStepl (Zero[-]x).
apply minus_ap_zero.
apply (ap_symmetric G).
auto.
Qed.

Lemma inv_resp_ap : forall x y : G, x[#]y -> [--]x[#][--]y.
intros x y H.
apply (csf_strext _ _ (cg_inv (c:=G))).
AStepl x.
AStepr y.
auto.
Qed.

Lemma minus_resp_ap_rht : forall x y z : G, x[#]y -> x[-]z[#]y[-]z.
intros x y z H.
unfold cg_minus in |- *.
apply op_rht_resp_ap.
assumption.
Qed.

Lemma minus_resp_ap_lft : forall x y z : G, x[#]y -> z[-]x[#]z[-]y.
intros x y z H.
AStepl ([--](x[-]z)).
 2: unfold cg_minus in |- *; Step_final ([--][--]z[+][--]x).
AStepr ([--](y[-]z)).
 2: unfold cg_minus in |- *; Step_final ([--][--]z[+][--]y).
apply inv_resp_ap.
apply minus_resp_ap_rht.
auto.
Qed.

Lemma minus_cancel_ap_rht : forall x y z : G, x[-]z[#]y[-]z -> x[#]y.
unfold cg_minus in |- *.
intros x y z H.
exact (plus_cancel_ap_rht _ _ _ H).
Qed.

End cgroups_apartness.
Hint Resolve op_rht_resp_ap: algebra.
Hint Resolve minus_ap_zero zero_minus_apart inv_resp_ap_zero: algebra.

Section CGroup_Ops.

(**
** Functional operations

As before, we lift our group operations to the function space of the group.

%\begin{convention}%
Let [G] be a group and [F,F':(PartFunct G)] with domains given respectively
by [P] and [Q].
%\end{convention}%
*)

Variable G : CGroup.

Variables F F' : PartFunct G.

(* begin hide *)
Let P := Dom F.
Let Q := Dom F'.
(* end hide *)

Section Part_Function_Inv.

Lemma part_function_inv_strext :
 forall (x y : G) (Hx : P x) (Hy : P y), [--](F x Hx)[#][--](F y Hy) -> x[#]y.
intros x y Hx Hy H.
apply pfstrx with F Hx Hy.
apply un_op_strext_unfolded with (cg_inv (c:=G)); assumption.
Qed.

Definition Finv :=
  Build_PartFunct G _ (dom_wd _ F) (fun (x : G) (Hx : P x) => [--](F x Hx))
    part_function_inv_strext.

End Part_Function_Inv.

Section Part_Function_Minus.

Lemma part_function_minus_strext :
 forall (x y : G) (Hx : Conj P Q x) (Hy : Conj P Q y),
 F x (prj1 G _ _ _ Hx)[-]F' x (prj2 G _ _ _ Hx)[#]
 F y (prj1 G _ _ _ Hy)[-]F' y (prj2 G _ _ _ Hy) -> 
 x[#]y.
intros x y Hx Hy H.
cut
 (F x (prj1 G _ _ _ Hx)[#]F y (prj1 G _ _ _ Hy)
  or F' x (prj2 G _ _ _ Hx)[#]F' y (prj2 G _ _ _ Hy)).
intro H0.
elim H0; intro H1; exact (pfstrx _ _ _ _ _ _ H1).

apply cg_minus_strext; auto.
Qed.

Definition Fminus :=
  Build_PartFunct G _ (conj_wd _ _ _ (dom_wd _ F) (dom_wd _ F'))
    (fun (x : G) (Hx : Conj P Q x) =>
     F x (prj1 G _ _ _ Hx)[-]F' x (prj2 G _ _ _ Hx))
    part_function_minus_strext.

End Part_Function_Minus.

End CGroup_Ops.

Implicit Arguments Finv [G].
Notation "{--} x" := (Finv x) (at level 2, right associativity).

Implicit Arguments Fminus [G].
Infix "{-}" := Fminus (at level 50, left associativity).

