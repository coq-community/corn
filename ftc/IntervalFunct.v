(* $Id$ *)

Require Export PartFunEquality.

Section Operations.

(** * Functions with compact domain

In this section we concern ourselves with defining operations on the set of functions from an arbitrary interval $[a,b]$#[a,b]# to [IR].  Although these are a particular kind of partial function, they have the advantage that, given [a] and [b], they have type [Set] and can thus be quantified over and extracted from existential hypothesis.  This will be important when we want to define concepts like differentiability, which involve the existence of an object satisfying some given properties.

Throughout this section we will focus on a compact interval and define operators analogous to those we already have for arbitrary partial functions.

%\begin{convention}% Let [a,b] be real numbers and denote by [I] the compact interval $[a,b]$#[a,b]#.  Let [f,g] be setoid functions of type [I->IR].
%\end{convention}%
*)

Variables a b : IR.
Hypothesis Hab : a[<=]b.
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

Lemma ifunct_const_strext : forall x y : subset I, c[#]c -> x[#]y.
intros x y H.
elim (ap_irreflexive_unfolded _ c H).
Qed.

Definition ifunct_const :=
  Build_CSetoid_fun _ _ (fun x : subset I => c) ifunct_const_strext.

End Const.

Section Id.

Lemma ifunct_id_strext :
 forall x y : subset I, scs_elem _ _ x[#]scs_elem _ _ y -> x[#]y.
intros x y; case x; case y; intros; Algebra.
Qed.

Definition ifunct_id :=
  Build_CSetoid_fun _ _ (fun x : subset I => scs_elem _ _ x) ifunct_id_strext.

End Id.

(**
Next, we define addition, algebraic inverse, subtraction and product of functions.
*)

Section Sum.

Lemma ifunct_plus_strext :
 forall x y : subset I, f x[+]g x[#]f y[+]g y -> x[#]y.
intros x y H.
elim (bin_op_strext_unfolded _ _ _ _ _ _ H); intro H0;
 exact (csetoid_fun_strext_unfolded _ _ _ _ _ H0).
Qed.

Definition ifunct_plus :=
  Build_CSetoid_fun _ _ (fun x : subset I => f x[+]g x) ifunct_plus_strext.

End Sum.

Section Inv.

Lemma ifunct_inv_strext :
 forall x y : subset I, [--](f x)[#][--](f y) -> x[#]y.
intros x y H.
generalize (un_op_strext_unfolded _ _ _ _ H); intro H0.
exact (csetoid_fun_strext_unfolded _ _ _ _ _ H0).
Qed.

Definition ifunct_inv :=
  Build_CSetoid_fun _ _ (fun x : subset I => [--](f x)) ifunct_inv_strext.

End Inv.

Section Minus.

Lemma ifunct_minus_strext :
 forall x y : subset I, f x[-]g x[#]f y[-]g y -> x[#]y.
intros x y H.
elim (cg_minus_strext _ _ _ _ _ H); intro H0;
 exact (csetoid_fun_strext_unfolded _ _ _ _ _ H0).
Qed.

Definition ifunct_minus :=
  Build_CSetoid_fun _ _ (fun x : subset I => f x[-]g x) ifunct_minus_strext.

End Minus.

Section Mult.

Lemma ifunct_mult_strext :
 forall x y : subset I, f x[*]g x[#]f y[*]g y -> x[#]y.
intros x y H.
elim (bin_op_strext_unfolded _ _ _ _ _ _ H); intro H0;
 exact (csetoid_fun_strext_unfolded _ _ _ _ _ H0).
Qed.

Definition ifunct_mult :=
  Build_CSetoid_fun _ _ (fun x : subset I => f x[*]g x) ifunct_mult_strext.

End Mult.

Section Nth_Power.

(**
Exponentiation to a natural power [n] is also useful.
*)

Variable n : nat.

Lemma ifunct_nth_strext : forall x y : subset I, f x[^]n[#]f y[^]n -> x[#]y.
intros.
apply csetoid_fun_strext_unfolded with (IR:CSetoid) f.
apply nexp_strext with n; assumption.
Qed.

Definition ifunct_nth :=
  Build_CSetoid_fun _ _ (fun x : subset I => f x[^]n) ifunct_nth_strext.

End Nth_Power.

(**
If a function is non-zero in all the interval then we can define its multiplicative inverse.
*)

Section Recip.

(* begin show *)
Hypothesis Hg : forall x : subset I, g x[#]Zero.
(* end show *)

Lemma ifunct_recip_strext :
 forall x y : subset I, (One[/] g x[//]Hg x)[#](One[/] g y[//]Hg y) -> x[#]y.
intros x y H.
elim (div_strong_ext _ _ _ _ _ _ _ H); intro H0.
elim (ap_irreflexive_unfolded _ _ H0).
exact (csetoid_fun_strext_unfolded _ _ _ _ _ H0).
Qed.

Definition ifunct_recip :=
  Build_CSetoid_fun _ _ (fun x : subset I => One[/] g x[//]Hg x)
    ifunct_recip_strext.

End Recip.

Section Div.

Hypothesis Hg : forall x : subset I, g x[#]Zero.

Lemma ifunct_div_strext :
 forall x y : subset I, (f x[/] g x[//]Hg x)[#](f y[/] g y[//]Hg y) -> x[#]y.
intros x y H.
elim (div_strong_ext _ _ _ _ _ _ _ H); intro H0;
 exact (csetoid_fun_strext_unfolded _ _ _ _ _ H0).
Qed.

Definition ifunct_div :=
  Build_CSetoid_fun _ _ (fun x : subset I => f x[/] g x[//]Hg x)
    ifunct_div_strext.

End Div.

Section Absolute_Value.

(**
Absolute value will also be needed at some point.
*)

Lemma ifunct_AbsIR_strext :
 forall x y : subset I, AbsIR (f x)[#]AbsIR (f y) -> x[#]y.
intros x y H.
apply csetoid_fun_strext_unfolded with (IR:CSetoid) f.
simpl in H; unfold ABSIR in H; elim (bin_op_strext_unfolded _ _ _ _ _ _ H).
auto.
intro; apply un_op_strext_unfolded with (cg_inv (c:=IR)); assumption.
Qed.

Definition ifunct_abs :=
  Build_CSetoid_fun _ _ (fun x : subset I => AbsIR (f x)) ifunct_AbsIR_strext.

End Absolute_Value.

End Operations.

(** 
The set of these functions form a ring with relation to the operations of sum and multiplication.  As they actually
form a set, this fact can be proved in Coq for this class of functions; unfortunately, due to a problem with the
coercions, we are not able to use it (Coq will not recognize the elements of that ring as functions which can be
applied to elements of $[a,b]$#[a,b]#), so we merely state this fact here as a curiosity.

Finally, we define composition; for this we need two functions with different domains.

%\begin{convention}% [a',b'] be real numbers and denote by [I'] the compact interval $[a',b']$#[a',b']#, and let [g] be a setoid function of type [I'->IR].
%\end{convention}%
*)
Section IFunct_Composition.

Variables a b : IR.
Hypothesis Hab : a[<=]b.
(* begin hide *)
Let I := Compact Hab.
(* end hide *)

Variables a' b' : IR.
Hypothesis Hab' : a'[<=]b'.
(* begin hide *)
Let I' := Compact Hab'.
(* end hide *)

Variable f : CSetoid_fun (subset I) IR.
Variable g : CSetoid_fun (subset I') IR.

Hypothesis Hfg : forall x : subset I, I' (f x).

Lemma ifunct_comp_strext :
 forall x y : subset I,
 g (Build_subcsetoid_crr _ _ _ (Hfg x))[#]
 g (Build_subcsetoid_crr _ _ _ (Hfg y)) -> x[#]y.
intros x y H.
apply csetoid_fun_strext_unfolded with (IR:CSetoid) f.
exact (csetoid_fun_strext_unfolded _ _ _ _ _ H).
Qed.

Definition ifunct_comp :=
  Build_CSetoid_fun _ _
    (fun x : subset I => g (Build_subcsetoid_crr _ _ _ (Hfg x)))
    ifunct_comp_strext.

End IFunct_Composition.

Notation IConst := (ifunct_const _ _ _).
Notation IId := (ifunct_id _ _ _).
Notation IPlus := (ifunct_plus _ _ _).
Notation IInv := (ifunct_inv _ _ _).
Notation IMinus := (ifunct_minus _ _ _).
Notation IMult := (ifunct_mult _ _ _).
Notation INth := (ifunct_nth _ _ _).
Notation IRecip := (ifunct_recip _ _ _).
Notation IDiv := (ifunct_div _ _ _).
Notation IAbs := (ifunct_abs _ _ _).
Notation IComp := (ifunct_comp _ _ _ _ _ _).