(* $Id$ *)

Require Export CSetoids.

Section unary_function_composition.

(**
Let [S1],  [S2] and [S3] be setoids, [f] a
setoid function from [S1] to [S2], and [g] from [S2]
to [S3] in the following definition of composition.  *)

Variables S1 S2 S3 : CSetoid.
Variable f : CSetoid_fun S1 S2.
Variable g : CSetoid_fun S2 S3.

Definition compose_CSetoid_fun : CSetoid_fun S1 S3.
apply (Build_CSetoid_fun _ _ (fun x : S1 => g (f x))).
(* str_ext *)
unfold fun_strong_ext in |- *; intros x y H.
apply (csf_strext _ _ f). apply (csf_strext _ _ g). assumption.
Defined.

End unary_function_composition.

Section unary_and_binary_function_composition.

Definition compose_CSetoid_bin_un_fun (A B C : CSetoid)
  (f : CSetoid_bin_fun B B C) (g : CSetoid_fun A B) : 
  CSetoid_bin_fun A A C.
intros A B C f g.
apply (Build_CSetoid_bin_fun A A C (fun a0 a1 : A => f (g a0) (g a1))).
unfold bin_fun_strong_ext in |- *.
intros x1 x2 y1 y2 H0.
set (H1 := csbf_strext B B C f) in *.
generalize H1.
unfold bin_fun_strong_ext in |- *.
intro H10.
set (H2 := H10 (g x1) (g x2) (g y1) (g y2) H0) in *.
elim H2.
intro H3.
set (H4 := csf_strext A B g) in *.
generalize H4.
unfold fun_strong_ext in |- *.
intro H40.
left.
apply H40.
exact H3.

intro H3.
set (H4 := csf_strext A B g) in *.
generalize H4.
unfold fun_strong_ext in |- *.
intro H40.
right.
apply H40.
exact H3.
Defined.

End unary_and_binary_function_composition.

Section function_projection.

Lemma proj_bin_fun :
 forall (A B C : CSetoid) (f : CSetoid_bin_fun A B C) (a : A),
 fun_strong_ext (f a).
intros A B C f a.
red in |- *.
elim f.
intro fo.
unfold bin_fun_strong_ext in |- *.
intro csbf_strext0.
simpl in |- *.
intros x y.
intro H.
cut (a[#]a or x[#]y).
intro H0.
elim H0.
cut (Not (a[#]a)).
intros nH1 H1.
elim nH1.
exact H1.

apply ap_irreflexive_unfolded.

intuition.

apply csbf_strext0.
exact H.
Qed.

Definition projected_bin_fun A B C (f : CSetoid_bin_fun A B C) 
  (a : A) := Build_CSetoid_fun B C (f a) (proj_bin_fun A B C f a).

Definition compose_CSetoid_bin_fun A B C (f g : CSetoid_fun A B)
  (h : CSetoid_bin_fun B B C) : CSetoid_fun A C.
intros A B C f g h.
apply (Build_CSetoid_fun A C (fun a : A => h (f a) (g a))).
unfold fun_strong_ext in |- *.
intros x y H.
cut (f x[#]f y or g x[#]g y).
intro H1.
elim H1.
intro H2.
apply (csf_strext A B f).
exact H2.

intro H2.
apply (csf_strext A B g).
exact H2.

apply (csbf_strext B B C h).
exact H.

Defined.

Definition compose_CSetoid_un_bin_fun (A B C : CSetoid)
  (f : CSetoid_bin_fun B B C) (g : CSetoid_fun C A) : 
  CSetoid_bin_fun B B A.
intros A0 B0 C f g.
apply Build_CSetoid_bin_fun with (fun x y : B0 => g (f x y)).
unfold bin_fun_strong_ext in |- *.
intros x1 x2 y1 y2.
case f.
simpl in |- *.
unfold bin_fun_strong_ext in |- *.
case g.
simpl in |- *.
unfold fun_strong_ext in |- *.
intros gu gstrext fu fstrext H.
apply fstrext.
apply gstrext.
exact H.
Defined.

End function_projection.

Section BinProj.

Variable S : CSetoid.

Definition binproj1 (x y:S) := x.

Lemma binproj1_strext : bin_fun_strong_ext _ _ _ binproj1.
red in |- *; auto.
Qed.

Definition cs_binproj1 : CSetoid_bin_op S.
red in |- *; apply Build_CSetoid_bin_op with binproj1.
apply binproj1_strext.
Defined.

End BinProj.

(** **Combining operations
%\begin{convention}%
Let [S1], [S2] and [S3] be setoids.
%\end{convention}%
*)

Section CombiningOperations.
Variables S1 S2 S3 : CSetoid.

(**
In the following definition, we assume [f] is a setoid function from
[S1] to [S2], and [op] is an unary operation on [S2].
Then [opOnFun] is the composition [op] after [f].
*)
Section CombiningUnaryOperations.
Variable f : CSetoid_fun S1 S2.
Variable op : CSetoid_un_op S2.

Definition opOnFun : CSetoid_fun S1 S2.
apply (Build_CSetoid_fun S1 S2 (fun x : S1 => op (f x))).
(* str_ext *)
unfold fun_strong_ext in |- *; intros x y H.
apply (csf_strext _ _ f x y).
apply (csf_strext _ _ op _ _ H).
Defined.

End CombiningUnaryOperations.

End CombiningOperations.

(** **Partial Functions

In this section we define a concept of partial function for an arbitrary setoid.  Essentially, a partial function is what would be expected---a predicate on the setoid in question and a total function from the set of points satisfying that predicate to the setoid.  There is one important limitations to this approach: first, the record we obtain has type [Type], meaning that we can't use, for instance, elimination of existential quantifiers.

Furthermore, for reasons we will explain ahead, partial functions will not be defined via the [CSetoid_fun] record, but the whole structure will be incorporated in a new record.

Finally, notice that to be completely general the domains of the functions have to be characterized by a [CProp]-valued predicate; otherwise, the use you can make of a function will be #\emph{#a priori#}# restricted at the moment it is defined.

Before we state our definitions we need to do some work on domains.
*)

Section SubSets_of_G.

(** ***Subsets of Setoids

Subsets of a setoid will be identified with predicates from the carrier set of the setoid into [CProp].  At this stage, we do not make any assumptions about these predicates.

We will begin by defining elementary operations on predicates, along with their basic properties.  In particular, we will work with well defined predicates, so we will prove that these operations preserve welldefinedness.

%\begin{convention}%
Let [S:CSetoid] and [P,Q:S->CProp].
%\end{convention}%
*)

Variable S : CSetoid.

Section Conjunction.

Variables P Q : S -> CProp.

Definition conjP (x : S) : CProp := P x and Q x.

Lemma prj1 : forall x : S, conjP x -> P x.
intros x H; inversion_clear H; assumption.
Qed.

Lemma prj2 : forall x : S, conjP x -> Q x.
intros x H; inversion_clear H; assumption.
Qed.

Lemma conj_wd :
 pred_well_def _ P -> pred_well_def _ Q -> pred_well_def _ conjP.
intros H H0.
red in |- *; intros x y H1 H2.
inversion_clear H1; split.

apply H with x; assumption.

apply H0 with x; assumption.
Qed.

End Conjunction.

Section Disjunction.

Variables P Q : S -> CProp.

(**
Although at this stage we never use it, for completeness's sake we also treat disjunction (corresponding to union of subsets).
*)

Definition disj (x : S) : CProp := P x or Q x.

Lemma inj1 : forall x : S, P x -> disj x.
intros; left; assumption.
Qed.

Lemma inj2 : forall x : S, Q x -> disj x.
intros; right; assumption.
Qed.

Lemma disj_wd :
 pred_well_def _ P -> pred_well_def _ Q -> pred_well_def _ disj.
intros H H0.
red in |- *; intros x y H1 H2.
inversion_clear H1.

left; apply H with x; assumption.

right; apply H0 with x; assumption.
Qed.

End Disjunction.

Section Extension.

(**
The next definition is a bit tricky, and is useful for choosing among the elements that satisfy a predicate [P] those that also satisfy [R] in the case where [R] is only defined for elements satisfying [P]---consider [R] to be a condition on the image of an object via a function with domain [P].  We chose to call this operation [extension].
*)

Variable P : S -> CProp.
Variable R : forall x : S, P x -> CProp.

Definition extend (x : S) : CProp := P x and (forall H : P x, R x H).

Lemma ext1 : forall x : S, extend x -> P x.
intros x H; inversion_clear H; assumption.
Qed.

Lemma ext2_a : forall x : S, extend x -> {H : P x | R x H}.
intros x H; inversion_clear H.
exists X; auto.
Qed.

Lemma ext2 : forall (x : S) (Hx : extend x), R x (ProjT1 (ext2_a x Hx)).
intros; apply projT2.
Qed.

Lemma extension_wd :
 pred_well_def _ P ->
 (forall (x y : S) Hx Hy, x[=]y -> R x Hx -> R y Hy) ->
 pred_well_def _ extend.
intros H H0.
red in |- *; intros x y H1 H2.
elim H1; intros H3 H4; split.

apply H with x; assumption.

intro H5; apply H0 with x H3; [ apply H2 | apply H4 ].
Qed.

End Extension.

End SubSets_of_G.

Notation Conj := (conjP _).
Implicit Arguments disj [S].

Implicit Arguments extend [S].
Implicit Arguments ext1 [S P R x].
Implicit Arguments ext2 [S P R x].

(** ***Operations

We are now ready to define the concept of partial function between arbitrary setoids.
*)

Record BinPartFunct (S1 S2 : CSetoid) : Type := 
  {bpfdom : S1 -> CProp;
   bdom_wd : pred_well_def S1 bpfdom;
   bpfpfun :> forall x : S1, bpfdom x -> S2;
   bpfstrx :
    forall (x y : S1) (Hx : bpfdom x) (Hy : bpfdom y),
    bpfpfun x Hx[#]bpfpfun y Hy -> x[#]y}.


Notation BDom := (bpfdom _ _).
Implicit Arguments bpfpfun [S1 S2].

(**
The next lemma states that every partial function is well defined.
*)

Lemma bpfwdef :
 forall (S1 S2 : CSetoid) (F : BinPartFunct S1 S2) x y Hx Hy,
 x[=]y -> F x Hx[=]F y Hy.
intros.
apply not_ap_imp_eq; intro H0.
generalize (bpfstrx _ _ _ _ _ _ _ H0).
exact (eq_imp_not_ap _ _ _ H).
Qed.

(** Similar for automorphisms. *)

Record PartFunct (S : CSetoid) : Type := 
  {pfdom : S -> CProp;
   dom_wd : pred_well_def S pfdom;
   pfpfun :> forall x : S, pfdom x -> S;
   pfstrx :
    forall (x y : S) (Hx : pfdom x) (Hy : pfdom y),
    pfpfun x Hx[#]pfpfun y Hy -> x[#]y}.

Notation Dom := (pfdom _).
Notation Part := (pfpfun _).
Implicit Arguments pfpfun [S].

(**
The next lemma states that every partial function is well defined.
*)

Lemma pfwdef :
 forall (S : CSetoid) (F : PartFunct S) x y Hx Hy, x[=]y -> F x Hx[=]F y Hy.
intros.
apply not_ap_imp_eq; intro H0.
generalize (pfstrx _ _ _ _ _ _ H0).
exact (eq_imp_not_ap _ _ _ H).
Qed.

(**
A few characteristics of this definition should be explained:
- The domain of the partial function is characterized by a predicate that is required to be well defined but not strongly extensional.  The motivation for this choice comes from two facts: first, one very important subset of real numbers is the compact interval [[a,b]]---characterized by the predicate [ [x:IR](a[<=]x)*(x[<=]b)], which is not strongly extensional; on the other hand, if we can apply a function to an element [s] of a setoid [S] it seems reasonable (and at some point we do have to do it) to apply that same function to any element [s'] which is equal to [s] from the point of view of the setoid equality.
- The last two conditions state that [pfpfun] is really a subsetoid function.  The reason why we do not write it that way is the following: when applying a partial function [f] to an element [s] of [S] we also need a proof object [H]; with this definition the object we get is [f(s,H)], where the proof is kept separate from the object.  Using subsetoid notation, we would get $f(\langle s,H\rangle)$#f(&lt;s,H&gt;)#; from this we need to apply two projections to get either the original object or the proof, and we need to apply an extra constructor to get $f(\langle s,H\rangle)$#f(&lt;s,H&gt;)# from [s] and [H].  This amounts to spending more resources when actually working with these objects.
- This record has type [Type], which is very unfortunate, because it means in particular that we cannot use the well behaved set existential quantification over partial functions; however, later on we will manage to avoid this problem in a way that also justifies that we don't really need to use that kind of quantification.
Another approach to this definition that completely avoid this complication would be to make [PartFunct] a dependent type, receiving the predicate as an argument.  This does work in that it allows us to give [PartFunct] type [Set] and do some useful stuff with it; however, we are not able to define something as simple as an operator that gets a function and returns its domain (because of the restrictions in the type elimination rules).  This sounds very unnatural, and soon gets us into strange problems that yield very unlikely definitions, which is why we chose to altogether do away with this approach.

%\begin{convention}% All partial functions will henceforth be denoted by capital letters.
%\end{convention}%

We now present some methods for defining partial functions.
*)

Hint Resolve CI: core.

Section CSetoid_Ops.

Variable S : CSetoid.

(**
To begin with, we want to be able to ``see'' each total function as a partial function.
*)

Definition total_eq_part : CSetoid_un_op S -> PartFunct S.
intros f.
apply
 Build_PartFunct with (fun x : S => CTrue) (fun (x : S) (H : CTrue) => f x).
red in |- *; intros; auto.
intros x y Hx Hy H.
exact (csetoid_fun_strext_unfolded _ _ f _ _ H).
Defined.

Section Part_Function_Const.

(**
In any setoid we can also define constant functions (one for each element of the setoid) and an identity function:

%\begin{convention}% Let [c:S].
%\end{convention}%
*)

Variable c : S.

Definition Fconst := total_eq_part (Const_CSetoid_fun _ _ c).

End Part_Function_Const.

Section Part_Function_Id.

Definition Fid := total_eq_part (id_un_op S).

End Part_Function_Id.

(**
(These happen to be always total functions, but that is more or less obvious, as we have no information on the setoid; however, we will be able to define partial functions just applying other operators to these ones.)

If we have two setoid functions [F] and [G] we can always compose them.  The domain of our new function will be the set of points [s] in the domain of [F] for which [F(s)] is in the domain of [G]#. #%\footnote{%Notice that the use of extension here is essential.%}.%  The inversion in the order of the variables is done to maintain uniformity with the usual mathematical notation.

%\begin{convention}% Let [G,F:(PartFunct S)] and denote by [Q] and [P], respectively, the predicates characterizing their domains.
%\end{convention}%
*)

Section Part_Function_Composition.

Variables G F : PartFunct S.

(* begin hide *)
Let P := Dom F.
Let Q := Dom G.
(* end hide *)
Let R (x : S) := {Hx : P x | Q (F x Hx)}.

Lemma part_function_comp_strext :
 forall (x y : S) (Hx : R x) (Hy : R y),
 G (F x (ProjT1 Hx)) (ProjT2 Hx)[#]G (F y (ProjT1 Hy)) (ProjT2 Hy) -> x[#]y.
intros x y Hx Hy H.
exact (pfstrx _ _ _ _ _ _ (pfstrx _ _ _ _ _ _ H)).
Qed.

Lemma part_function_comp_dom_wd : pred_well_def S R.
red in |- *; intros x y H H0.
unfold R in |- *; inversion_clear H.
exists (dom_wd _ F x y x0 H0).
apply (dom_wd _ G) with (F x x0).
assumption.
apply pfwdef; assumption.
Qed.

Definition Fcomp :=
  Build_PartFunct _ R part_function_comp_dom_wd
    (fun (x : S) (Hx : R x) => G (F x (ProjT1 Hx)) (ProjT2 Hx))
    part_function_comp_strext.

End Part_Function_Composition.

End CSetoid_Ops.

(**
%\begin{convention}% Let [F:(BinPartFunct S1 S2)] and [G:(PartFunct S2 S3)], and denote by [Q] and [P], respectively, the predicates characterizing their domains.
%\end{convention}%
*)

Section BinPart_Function_Composition.

Variables S1 S2 S3 : CSetoid.

Variable G : BinPartFunct S2 S3.
Variable F : BinPartFunct S1 S2.

(* begin hide *)
Let P := BDom F.
Let Q := BDom G.
(* end hide *)
Let R (x : S1) := {Hx : P x | Q (F x Hx)}.

Lemma bin_part_function_comp_strext :
 forall (x y : S1) (Hx : R x) (Hy : R y),
 G (F x (ProjT1 Hx)) (ProjT2 Hx)[#]G (F y (ProjT1 Hy)) (ProjT2 Hy) -> x[#]y.
intros x y Hx Hy H.
exact (bpfstrx _ _ _ _ _ _ _ (bpfstrx _ _ _ _ _ _ _ H)).
Qed.

Lemma bin_part_function_comp_dom_wd : pred_well_def S1 R.
red in |- *; intros x y H H0.
unfold R in |- *; inversion_clear H.
exists (bdom_wd _ _ F x y x0 H0).
apply (bdom_wd _ _ G) with (F x x0).
assumption.
apply bpfwdef; assumption.
Qed.

Definition BinFcomp :=
  Build_BinPartFunct _ _ R bin_part_function_comp_dom_wd
    (fun (x : S1) (Hx : R x) => G (F x (ProjT1 Hx)) (ProjT2 Hx))
    bin_part_function_comp_strext.

End BinPart_Function_Composition.

(* Different tokens for compatibility with coqdoc *)

Implicit Arguments Fconst [S].
Notation "[-C-] x" := (Fconst x) (at level 2, right associativity).

Notation FId := (Fid _).

Implicit Arguments Fcomp [S].
Infix "[o]" := Fcomp (at level 65, no associativity).

Hint Resolve pfwdef bpfwdef: algebra.

Section bijections.
(** **Bijections *)

Definition injective A B (f : CSetoid_fun A B) :=
  forall a0 a1 : A, a0[#]a1 -> f a0[#]f a1.

Definition injective_weak A B (f : CSetoid_fun A B) :=
  forall a0 a1 : A, f a0[=]f a1 -> a0[=]a1.

Definition surjective A B (f : CSetoid_fun A B) :=
  forall b : B, {a : A | f a[=]b}.

Implicit Arguments injective [A B].
Implicit Arguments injective_weak [A B].
Implicit Arguments surjective [A B].

Lemma injective_imp_injective_weak :
 forall A B (f : CSetoid_fun A B), injective f -> injective_weak f.
intros A B f.
unfold injective in |- *.
intro H.
unfold injective_weak in |- *.
intros a0 a1 H0.
apply not_ap_imp_eq.
red in |- *.
intro H1.
set (H2 := H a0 a1 H1) in *.
set (H3 := ap_imp_neq B (f a0) (f a1) H2) in *.
set (H4 := eq_imp_not_neq B (f a0) (f a1) H0) in *.
apply H4.
exact H3.
Qed.

Definition bijective A B (f : CSetoid_fun A B) :=
  injective f and surjective f.

Implicit Arguments bijective [A B].

Lemma id_is_bij : forall A : CSetoid, bijective (id_un_op A).
intro A.
unfold bijective in |- *.
split.
unfold injective in |- *.
intros a0 a1.
unfold id_un_op in |- *.
simpl in |- *.
intro H.
exact H.

unfold surjective in |- *.
intro b.
unfold id_un_op in |- *.
simpl in |- *.
exists b.
apply eq_reflexive.
Qed.

Lemma comp_resp_bij :
 forall A B C (f : CSetoid_fun A B) (g : CSetoid_fun B C),
 bijective f -> bijective g -> bijective (compose_CSetoid_fun A B C f g).
intros A B C f g.
unfold bijective in |- *.
intros H0 H1.
elim H0.
intros H00 H01.
elim H1.
intros H10 H11.
split.
unfold injective in |- *.
intros a0 a1.
unfold compose_CSetoid_fun in |- *.
simpl in |- *.
intro H2.
unfold injective in H00.
unfold injective in H10.
apply H10.
apply H00.
exact H2.

unfold surjective in |- *.
intro c.
unfold compose_CSetoid_fun in |- *.
simpl in |- *.
unfold surjective in H11.
unfold surjective in H01.
set (H2 := H11 c) in *.
elim H2.
intros b H20.
set (H3 := H01 b) in *.
elim H3.
intros a H30.
exists a.
AStepl (g b).
AStepl c.
apply eq_reflexive.
Qed.

Definition inv A B (f : CSetoid_fun A B) (H : bijective f) :
  forall b : B, {a : A | f a[=]b}.
unfold bijective in |- *.
unfold surjective in |- *.
intuition.
Defined.

Implicit Arguments inv [A B].

Definition invfun A B (f : CSetoid_fun A B) (H : bijective f) : B -> A.
intros A B f H H0.
set (H1 := inv f H) in *.
elim (H1 H0).
intros a H2.
exact a.
Defined.

Implicit Arguments invfun [A B].

Lemma inv1 :
 forall A B (f : CSetoid_fun A B) (H : bijective f) (b : B),
 f (invfun f H b)[=]b.
intros A B f H b.
unfold invfun in |- *.
unfold sig_rec in |- *.
unfold sig_rect in |- *.
case inv.
intuition.
Qed.

Lemma inv2 :
 forall A B (f : CSetoid_fun A B) (H : bijective f) (a : A),
 invfun f H (f a)[=]a.
intros.
unfold invfun in |- *.
case inv.
unfold sigT_rec in |- *.
unfold sigT_rect in |- *.
unfold bijective in H.
unfold injective in H.
elim H.
intros H0 H1.
intro x.
apply injective_imp_injective_weak.
unfold injective in |- *.
apply H0.
Qed.

Lemma inv_strext :
 forall A B (f : CSetoid_fun A B) (H : bijective f),
 fun_strong_ext (invfun f H).
intros A B f H.
unfold fun_strong_ext in |- *.
intros x y.
unfold bijective in H.
unfold injective in H.
intro H1.
unfold surjective in H.
elim H.
intros H00 H01.
elim (H01 x).
intros a0 H2.
elim (H01 y).
intros a1 H3.
AStepl (f a0).
AStepr (f a1).
apply H00.
AStepl (invfun f H x).
AStepr (invfun f H y).
exact H1.
AStepl (invfun f H (f a1)).
apply inv2.
set (H4 := injective_imp_injective_weak) in *.
generalize H4.
unfold injective in |- *.
unfold injective_weak in |- *.
intros.
apply H0 with (f := f).
apply H00.
AStepl (f a1).
AStepr y.
exact H3.
apply eq_symmetric.
apply inv1.
apply eq_symmetric.
apply inv1.
AStepl (invfun f H (f a0)).
apply inv2.
set (H4 := injective_imp_injective_weak) in *.
generalize H4.
unfold injective in |- *.
unfold injective_weak in |- *.
intros.
apply H0 with (f := f).
apply H00.
AStepl (f a0).
AStepr x.
exact H2.
apply eq_symmetric.
apply inv1.
apply eq_symmetric.
apply inv1.
Qed.

Definition Inv A B f (H : bijective f) :=
  Build_CSetoid_fun B A (invfun f H) (inv_strext A B f H).

Implicit Arguments Inv [A B].

Definition Inv_bij :
  forall A B (f : CSetoid_fun A B) (H : bijective f), bijective (Inv f H).
intros A B f H.
unfold bijective in |- *.
split.
unfold injective in |- *.
unfold bijective in H.
unfold surjective in H.
elim H.
intros H0 H1.
intros b0 b1 H2.
elim (H1 b0).
intros a0 H3.
elim (H1 b1).
intros a1 H4.
AStepl (Inv f (CAnd_intro _ _ H0 H1) (f a0)).
AStepr (Inv f (CAnd_intro _ _ H0 H1) (f a1)).
cut (fun_strong_ext f).
unfold fun_strong_ext in |- *.
intros H5.
apply H5.
AStepl (f a0).
AStepr (f a1).
AStepl b0.
AStepr b1.
exact H2.
apply eq_symmetric.
unfold Inv in |- *.
simpl in |- *.
apply inv1.
apply eq_symmetric.
unfold Inv in |- *.
simpl in |- *.
apply inv1.
elim f.
intuition.

unfold surjective in |- *.
intro a.
exists (f a).
unfold Inv in |- *.
simpl in |- *.
apply inv2.
Qed.


End bijections.
Implicit Arguments bijective [A B].
Implicit Arguments injective [A B].
Implicit Arguments injective_weak [A B].
Implicit Arguments surjective [A B].
Implicit Arguments inv [A B].
Implicit Arguments invfun [A B].
Implicit Arguments Inv [A B].
