(* $Id: IntervalFunct.v,v 1.5 2004/04/08 15:28:06 lcf Exp $ *)

Require Export PartFunEquality.

Section Operations.

(** * Functions with compact domain

In this section we concern ourselves with defining operations on the
set of functions from an arbitrary interval [[a,b]] to [IR].
Although these are a particular kind of partial function, they have
the advantage that, given [a] and [b], they have type [Set] and can
thus be quantified over and extracted from existential hypothesis.
This will be important when we want to define concepts like
differentiability, which involve the existence of an object satisfying
some given properties.

Throughout this section we will focus on a compact interval and define
operators analogous to those we already have for arbitrary partial
functions.

%\begin{convention}% Let [a,b] be real numbers and denote by [I] the
compact interval [[a,b]].  Let [f, g] be setoid functions of
type [I -> IR].
%\end{convention}%
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variables f g : CSetoid_fun (subset I) IR.

Section Const.

(**
Constant and identity functions are defined.

%\begin{convention}% Let [c:IR].
%\end{convention}%
*)

Variable c : IR.

Lemma IConst_strext : forall x y : subset I, c [#] c -> x [#] y.
intros x y H.
elim (ap_irreflexive_unfolded _ c H).
Qed.

Definition IConst := Build_CSetoid_fun _ _ (fun x => c) IConst_strext.

End Const.

Lemma IId_strext : forall x y : subset I, scs_elem _ _ x [#] scs_elem _ _ y -> x [#] y.
intros x y; case x; case y; intros; algebra.
Qed.

Definition IId := Build_CSetoid_fun _ _ _ IId_strext.

(**
Next, we define addition, algebraic inverse, subtraction and product of functions.
*)

Lemma IPlus_strext : forall x y : subset I, f x[+]g x [#] f y[+]g y -> x [#] y.
intros x y H.
elim (bin_op_strext_unfolded _ _ _ _ _ _ H); intro H0;
 exact (csf_strext_unfolded _ _ _ _ _ H0).
Qed.

Definition IPlus := Build_CSetoid_fun _ _ (fun x => f x[+]g x) IPlus_strext.

Lemma IInv_strext : forall x y : subset I, [--] (f x) [#] [--] (f y) -> x [#] y.
intros x y H.
generalize (un_op_strext_unfolded _ _ _ _ H); intro H0.
exact (csf_strext_unfolded _ _ _ _ _ H0).
Qed.

Definition IInv := Build_CSetoid_fun _ _ (fun x => [--] (f x)) IInv_strext.

Lemma IMinus_strext : forall x y : subset I, f x[-]g x [#] f y[-]g y -> x [#] y.
intros x y H.
elim (cg_minus_strext _ _ _ _ _ H); intro H0;
 exact (csf_strext_unfolded _ _ _ _ _ H0).
Qed.

Definition IMinus := Build_CSetoid_fun _ _ (fun x => f x[-]g x) IMinus_strext.

Lemma IMult_strext : forall x y : subset I, f x[*]g x [#] f y[*]g y -> x [#] y.
intros x y H.
elim (bin_op_strext_unfolded _ _ _ _ _ _ H); intro H0;
 exact (csf_strext_unfolded _ _ _ _ _ H0).
Qed.

Definition IMult := Build_CSetoid_fun _ _ (fun x => f x[*]g x) IMult_strext.

Section Nth_Power.

(**
Exponentiation to a natural power [n] is also useful.
*)

Variable n : nat.

Lemma INth_strext : forall x y : subset I, f x[^]n [#] f y[^]n -> x [#] y.
intros.
apply csf_strext_unfolded with (IR:CSetoid) f.
apply nexp_strext with n; assumption.
Qed.

Definition INth := Build_CSetoid_fun _ _ (fun x => f x[^]n) INth_strext.

End Nth_Power.

(**
If a function is non-zero in all the interval then we can define its multiplicative inverse.
*)

Section Recip_Div.

(* begin show *)
Hypothesis Hg : forall x : subset I, g x [#] Zero.
(* end show *)

Lemma IRecip_strext : forall x y : subset I, (One[/] g x[//]Hg x) [#] (One[/] g y[//]Hg y) -> x [#] y.
intros x y H.
elim (div_strext _ _ _ _ _ _ _ H); intro H0.
elim (ap_irreflexive_unfolded _ _ H0).
exact (csf_strext_unfolded _ _ _ _ _ H0).
Qed.

Definition IRecip := Build_CSetoid_fun _ _ (fun x => One[/] g x[//]Hg x) IRecip_strext.

Lemma IDiv_strext : forall x y : subset I, (f x[/] g x[//]Hg x) [#] (f y[/] g y[//]Hg y) -> x [#] y.
intros x y H.
elim (div_strext _ _ _ _ _ _ _ H); intro H0;
 exact (csf_strext_unfolded _ _ _ _ _ H0).
Qed.

Definition IDiv := Build_CSetoid_fun _ _ (fun x => f x[/] g x[//]Hg x) IDiv_strext.

End Recip_Div.

(**
Absolute value will also be needed at some point.
*)

Lemma IAbs_strext : forall x y : subset I, AbsIR (f x) [#] AbsIR (f y) -> x [#] y.
intros x y H.
apply csf_strext_unfolded with (IR:CSetoid) f.
simpl in H; unfold ABSIR in H; elim (bin_op_strext_unfolded _ _ _ _ _ _ H).
auto.
intro; apply un_op_strext_unfolded with (cg_inv (c:=IR)); assumption.
Qed.

Definition IAbs := Build_CSetoid_fun _ _ (fun x => AbsIR (f x)) IAbs_strext.

End Operations.

(** 
The set of these functions form a ring with relation to the operations
of sum and multiplication.  As they actually form a set, this fact can
be proved in Coq for this class of functions; unfortunately, due to a
problem with the coercions, we are not able to use it (Coq will not
recognize the elements of that ring as functions which can be applied
to elements of [[a,b]]), so we merely state this fact here as a
curiosity.

Finally, we define composition; for this we need two functions with
different domains.

%\begin{convention}% [a',b'] be real numbers and denote by [I'] the
compact interval [[a',b']], and let [g] be a setoid function of type
[I' -> IR].
%\end{convention}%
*)
Section Composition.

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variables a' b' : IR.
Hypothesis Hab' : a' [<=] b'.
(* begin hide *)
Let I' := Compact Hab'.
(* end hide *)

Variable f : CSetoid_fun (subset I) IR.
Variable g : CSetoid_fun (subset I') IR.

Hypothesis Hfg : forall x : subset I, I' (f x).

Lemma IComp_strext : forall x y : subset I,
 g (Build_subcsetoid_crr _ _ _ (Hfg x)) [#] g (Build_subcsetoid_crr _ _ _ (Hfg y)) ->
 x [#] y.
intros x y H.
apply csf_strext_unfolded with (IR:CSetoid) f.
exact (csf_strext_unfolded _ _ _ _ _ H).
Qed.

Definition IComp := Build_CSetoid_fun _ _
 (fun x => g (Build_subcsetoid_crr _ _ _ (Hfg x))) IComp_strext.

End Composition.

Implicit Arguments IConst [a b Hab].
Implicit Arguments IId [a b Hab].
Implicit Arguments IPlus [a b Hab].
Implicit Arguments IInv [a b Hab].
Implicit Arguments IMinus [a b Hab].
Implicit Arguments IMult [a b Hab].
Implicit Arguments INth [a b Hab].
Implicit Arguments IRecip [a b Hab].
Implicit Arguments IDiv [a b Hab].
Implicit Arguments IAbs [a b Hab].
Implicit Arguments IComp [a b Hab a' b' Hab'].
