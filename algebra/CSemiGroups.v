(* $Id$ *)

(** printing [+] %\ensuremath+% #+# *)
(** printing {+} %\ensuremath+% #+# *)
Require Export CSetoidFun.

(* Begin_SpecReals *)

(** *Semigroups

**Definition of the notion of semigroup
*)

Definition is_CSemiGroup (A : CSetoid) (op : CSetoid_bin_op A) :=
  associative op.

Record CSemiGroup : Type := 
  {csg_crr :> CSetoid;
   csg_op : CSetoid_bin_op csg_crr;
   csg_proof : is_CSemiGroup csg_crr csg_op}.

(**
%\begin{nameconvention}%
In the %{\em %names%}% of lemmas, we will denote [[+]] with [plus].
%\end{nameconvention}%
*)

Implicit Arguments csg_op [c].
Infix "[+]" := csg_op (at level 50, left associativity).
(* End_SpecReals *)

(** **Semigroup axioms
The axiomatic properties of a semi group.

%\begin{convention}%
Let [G] be a semi-group.
%\end{convention}%
*)
Section CSemiGroup_axioms.
Variable G : CSemiGroup.

Lemma CSemiGroup_is_CSemiGroup : is_CSemiGroup G csg_op.
elim G; auto.
Qed.

Lemma plus_assoc : associative (csg_op (c:=G)).
exact CSemiGroup_is_CSemiGroup.
Qed.

End CSemiGroup_axioms.

(* Begin_SpecReals *)

(** **Semigroup basics

%\begin{convention}%
Let [G] be a semi-group.
%\end{convention}%
*)
Section CSemiGroup_basics.
Variable G : CSemiGroup.

(* End_SpecReals *)

Lemma plus_assoc_unfolded :
 forall (G : CSemiGroup) (x y z : G), x[+](y[+]z)[=]x[+]y[+]z.
(* End_Tex_Verb *)
exact CSemiGroups.plus_assoc.
Qed.

End CSemiGroup_basics.

(* End_SpecReals *)

Hint Resolve plus_assoc_unfolded: algebra.

(** **Functional operations
We can also define a similar addition operator, which will be denoted by [{+}], on partial functions.

%\begin{convention}% Whenever possible, we will denote the functional construction corresponding to an algebraic operation by the same symbol enclosed in curly braces.
%\end{convention}%

At this stage, we will always consider automorphisms; we %{\em %could%}% treat this in a more general setting, but we feel that it wouldn't really be a useful effort.

%\begin{convention}% Let [G:CSemiGroup] and [F,F':(PartFunct G)] and denote by [P] and [Q], respectively, the predicates characterizing their domains.
%\end{convention}%
*)

Section Part_Function_Plus.

Variable G : CSemiGroup.
Variables F F' : PartFunct G.

(* begin hide *)
Let P := Dom F.
Let Q := Dom F'.
(* end hide *)

Lemma part_function_plus_strext :
 forall (x y : G) (Hx : Conj P Q x) (Hy : Conj P Q y),
 F x (prj1 G _ _ _ Hx)[+]F' x (prj2 G _ _ _ Hx)[#]
 F y (prj1 G _ _ _ Hy)[+]F' y (prj2 G _ _ _ Hy) -> 
 x[#]y.
intros x y Hx Hy H.
elim (bin_op_strext_unfolded _ _ _ _ _ _ H); intro H1;
 exact (pfstrx _ _ _ _ _ _ H1).
Qed.

Definition Fplus :=
  Build_PartFunct G _ (conj_wd _ _ _ (dom_wd _ F) (dom_wd _ F'))
    (fun (x : G) (Hx : Conj P Q x) =>
     F x (prj1 G _ _ _ Hx)[+]F' x (prj2 G _ _ _ Hx))
    part_function_plus_strext.

End Part_Function_Plus.

Implicit Arguments Fplus [G].
Infix "{+}" := Fplus (at level 50, left associativity).

(** **Subsemigroups
%\begin{convention}%
Let [csg] a semi-group and [P] a non-empty
predicate on the semi-group which is preserved by [[+]].
%\end{convention}%
*)
Section SubCSemiGroups.
Variable csg : CSemiGroup.
Variable P : csg -> CProp.
Variable op_pres_P : bin_op_pres_pred _ P csg_op.

Let subcrr : CSetoid := Build_SubCSetoid _ P.
Definition Build_SubCSemiGroup : CSemiGroup :=
  Build_CSemiGroup subcrr (Build_SubCSetoid_bin_op _ _ _ op_pres_P)
    (restr_f_assoc _ _ _ op_pres_P (CSemiGroups.plus_assoc csg)).
End SubCSemiGroups.
