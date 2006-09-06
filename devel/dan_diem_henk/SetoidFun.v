
Require Export Setoids.
Require Export build_setoid_fun.

Set Implicit Arguments.

(** ** The Setoid of Setoid functions

The setoid functions form again a setoid. *)

Section setoid_of_setoid_functions.

Variables A B : Setoid.

Definition eq_fun (f g : Setoid_fun A B) :=
  forall x : A, f x[=]g x.

Lemma eq_fun_reflexive : Creflexive _ eq_fun.
Proof.
red.
unfold eq_fun.
triv.
Qed.

Lemma eq_fun_transitive : Ctransitive _ eq_fun.
Proof.
red.
unfold eq_fun.
intros f g h H1 H2 x.
trans (g x).
Qed.

Lemma eq_fun_symmetric : Csymmetric _ eq_fun.
Proof.
red.
unfold eq_fun.
intros f g H x.
symm.
Qed.

Lemma eq_fun_equiv : Cequivalence _ eq_fun.
Proof.
exact (Build_Cequivalence _ eq_fun eq_fun_reflexive eq_fun_symmetric  eq_fun_transitive).
Qed.

Definition setoid_of_setoid_functions :=
  Build_Setoid (Setoid_fun A B) eq_fun eq_fun_equiv.

End setoid_of_setoid_functions.


Infix "[->]" := setoid_of_setoid_functions (at level 85, right associativity).

(** **Nullary and n-ary operations
*)

Definition is_nullary_operation (S:Setoid) (s:S):Prop := True.

Fixpoint n_ary_operation (n:nat)(V:Setoid){struct n} : Setoid:=
match n with
| O    => V
|(S m) => V [->] (n_ary_operation m V)
end.

Section synek_herbelin.

Variables A B : Setoid.

Variable f : A[->]B.

Variable a : A.

(* fails :
Check (f a).
*)

(* but these work: *)

Check ((f : Setoid_fun A B) a).

Check (sf_fun A B f a).

End synek_herbelin.

(** ** Composition of Setoid functions
*)

Section compositions.

Variables A B C D E : Setoid.

Variable f1 : Setoid_fun A C.
Variable f2 : Setoid_bin_fun A B C.
Variable g1 : Setoid_fun C E.
Variable g2 : Setoid_bin_fun C D E.
Variable h1 : Setoid_fun B D.
Variable h2 : Setoid_bin_fun A B D.

Let uu x := g1 (f1 x).

Definition compose_uu : Setoid_fun A E.
build_setoid_fun uu.
Defined.

Let ub x y := g1 (f2 x y).

Definition compose_ub : Setoid_bin_fun A B E.
build_setoid_fun ub.
Defined.

Let bu x y := g2 (f1 x) (h1 y).

Definition compose_bu : Setoid_bin_fun A B E.
build_setoid_fun bu.
Defined.

Let bb x y := g2 (f2 x y) (h2 x y).

Definition compose_bb : Setoid_bin_fun A B E.
build_setoid_fun bb.
Defined.

End compositions.

Notation "f [o] g" := (*"f [ouu] g"*)
  (compose_uu f g) (at level 20, left associativity).

Notation "f [oub] g" := 
  (compose_ub f g) (at level 20, left associativity).

Notation "f [obu] ( g , h )" := 
  (compose_bu f g h) (at level 20).

Notation "f [obb] ( g , h )" := 
  (compose_bb f g h) (at level 20).

(** ***Composition (of unary functions) as operation
*)

(** [compose_uu'] is just [compose_uu], except that the types 
of the argument functions are lifted to [FS_as_Setoid]s *)

Definition compose_uu' A B C : A [->] B -> B [->] C -> A [->] C :=
  fun f g => f[o]g.

Definition comp_as_bin_op : 
  forall A : Setoid,
  Setoid_bin_op (A [->] A).
Proof.
intro A.
apply (Build_Setoid_bin_op (A[->]A) (fun f g => compose_uu' f g)).
intros f1 f2 g1 g2 Hf Hg x.
simpl in *|-*.
apply eq_transitive with (g1 (f2 x)).
apply sf_wd.
apply Hf.
apply Hg.
Defined.

Lemma assoc_comp : forall A : Setoid, associative (comp_as_bin_op A).
Proof.
intros A f g h x.
simpl.
apply eq_reflexive.
Qed.

(** ***Projections
*)

Section function_projection.

Definition projected_bin_fun 
  (A B C : Setoid) (f : Setoid_bin_fun A B C) (x : A) : (Setoid_fun B C).
intros A B C f x.
build_setoid_fun (f x).
Defined.

End function_projection.

Section combinators_as_setoid_operations.

Definition id := id_un_op.

Variables A B : Setoid.

Definition first : (Setoid_bin_fun A B A).
build_setoid_fun (fun (x : A) (_ : B) => x).
Defined.

Definition second : (Setoid_bin_fun A B B).
build_setoid_fun (fun (_ : A) (y : B) => y).
Defined.

End combinators_as_setoid_operations.

Section p66E2b4.

(** **The Free Setoid
%\begin{convention}% Let [A:CSetoid].
%\end{convention}%
*)

Variable A : Setoid.

Definition Astar := list A.

Definition empty_word : Astar := nil A.

Fixpoint eq_fm (m k : list A) {struct m} : CProp :=
  match m,k with
  | nil       , nil       => CTrue
  | cons a m' , cons b k' =>  a[=]b and (eq_fm m' k')
  | _         , _         => CFalse
  end.

Lemma eq_fm_reflexive : Creflexive _ eq_fm.
Proof.
red.
induction x as [ | a x IHx ]; simpl.
constructor.
split.
apply eq_reflexive.
exact IHx.
Qed.

Lemma eq_fm_symmetric : Csymmetric _ eq_fm.
Proof.
red.
induction x as [ | a x IHx ]; destruct y; simpl; trivial.
intros [ H H0 ].
split.
apply eq_symmetric with (1:=H).
apply IHx with (1:=H0).
Qed.

Lemma eq_fm_transitive : Ctransitive _ eq_fm.
Proof.
red.
induction x as [ | a x IHx ]; destruct y; destruct z; simpl; trivial.
intro H; elim H.
intros [ H H0] [ H1 H2 ].
split.
apply eq_transitive with (1:=H) (2:=H1).
apply IHx with (1:=H0) (2:=H2).
Qed.

Lemma eq_fm_equiv : Cequivalence Astar eq_fm.
Proof.
exact (Build_Cequivalence Astar eq_fm eq_fm_reflexive eq_fm_symmetric eq_fm_transitive).
Qed.

Definition free_setoid_as_setoid : Setoid:=
  Build_Setoid Astar eq_fm eq_fm_equiv.

Definition app_as_bin_op : Setoid_bin_op free_setoid_as_setoid.
apply (Build_Setoid_bin_op free_setoid_as_setoid (app A)).
red.
induction x1 as [ | a1 x1 IHx1 ]; destruct x2 as [ | a2 x2 ]; 
  simpl; intros y1 y2 Hx Hy.
exact Hy.
elim Hx.
elim Hx.
elim Hx; intros H1 H2.
split.
exact H1.
apply IHx1 with (1:=H2) (2:=Hy).
Qed.

End p66E2b4.

Unset Implicit Arguments.

(** **Partial Functions

In this section we define a concept of partial function for an
arbitrary setoid.  Essentially, a partial function is what would be
expected---a predicate on the setoid in question and a total function
from the set of points satisfying that predicate to the setoid.  There
are som important limitations to this approach: first, the record we
obtain has type [Type], meaning that we can't use, for instance,
elimination of existential quantifiers.

Furthermore, for reasons we will explain ahead, partial functions will
not be defined via the [Setoid_fun] record, but the whole structure
will be incorporated in a new record.

Finally, notice that to be completely general the domains of the
functions have to be characterized by a [CProp]-valued predicate;
otherwise, the use you can make of a function will be %\emph{%#<i>#a
priori#</i>#%}% restricted at the moment it is defined.

Before we state our definitions we need to do some work on domains.
*)

Section SubSets_of_G.

(** ***Subsets of Setoids

Subsets of a setoid will be identified with predicates from the
carrier set of the setoid into [CProp].  At this stage, we do not make
any assumptions about these predicates.

We will begin by defining elementary operations on predicates, along
with their basic properties.  In particular, we will work with well
defined predicates, so we will prove that these operations preserve
welldefinedness.

%\begin{convention}% Let [S:Setoid] and [P,Q:S->CProp].
%\end{convention}%
*)

Variable S : Setoid.

Section Conjunction.

Variables P Q : S -> Prop.

Definition conjP (x : S) : Prop := P x /\ Q x.

Lemma prj1 : forall x : S, conjP x -> P x.
Proof.
intros x [ H _ ]; exact H.
Qed.

Lemma prj2 : forall x : S, conjP x -> Q x.
intros x [ _ H ]; exact H.
Qed.

Lemma conj_wd : pred_wd S P -> pred_wd S Q -> pred_wd S conjP.
Proof.
intros H H0 x y [ H1 H2 ] H3.
split.
apply H with (1:=H1) (2:=H3).
apply H0 with (1:=H2) (2:=H3).
Qed.

End Conjunction.

Section Disjunction.

Variables P Q : S -> Prop.

(**
Although at this stage we never use it, for completeness's sake 
we also treat disjunction (corresponding to union of subsets).
*)

Definition disjP (x : S) : Prop := P x \/ Q x.

Lemma inj1 : forall x : S, P x -> disjP x.
Proof.
intros x H; left; exact H.
Qed.

Lemma inj2 : forall x : S, Q x -> disjP x.
Proof.
intros x H; right; exact H.
Qed.

Lemma disj_wd : pred_wd S P -> pred_wd S Q -> pred_wd S disjP.
Proof.
intros H H0 x y H1 H2.
elim H1; intro H3.
left; apply H with (1:=H3) (2:=H2).
right; apply H0 with (1:=H3) (2:=H2).
Qed.

End Disjunction.

Section Extension.

(**
The next definition is a bit tricky, and is useful for choosing among 
the elements that satisfy a predicate [P] those that also satisfy [R] 
in the case where [R] is only defined for elements satisfying [P]---
consider [R] to be a condition on the image of an object via a function 
with domain [P].  We chose to call this operation [extension].
*)

Variable P : S -> Prop.
Variable R : forall x : S, P x -> Prop.

Definition extend (x : S) : Prop := P x /\ (forall Hx : P x, R x Hx).

Lemma ext1 : forall x : S, extend x -> P x.
Proof.
intros x [ H _ ]; exact H.
Qed.

Lemma ext2_a : forall x : S, extend x -> {Hx : P x | R x Hx}.
Proof.
intros x [ H H0 ].
exists H.
apply H0.
Qed.

Lemma ext2 : forall (x : S) (Hx : extend x), R x (ProjT1 (ext2_a x Hx)).
Proof.
intros; apply projT2.
Qed.

Lemma extension_wd : 
  pred_wd S P ->
  (forall (x y : S) Hx Hy, x [=] y -> R x Hx -> R y Hy) -> 
  pred_wd S extend.
Proof.
intros H H0 x y [ H1 H2 ] H3.
split.
apply H with (1:=H1) (2:=H3).
intro H4.
apply H0 with (1:=H3) (2:=(H2 H1)).
Qed.

End Extension.

End SubSets_of_G.

Notation Conj := (conjP _).
Implicit Arguments disjP [S].

Implicit Arguments conj_wd [S P Q].

Notation Prj1 := (prj1 _ _ _ _).
Notation Prj2 := (prj2 _ _ _ _).

Implicit Arguments extend [S].
Implicit Arguments ext1 [S P R x].
Implicit Arguments ext2 [S P R x].

(** ***Operations

We are now ready to define the concept of partial function 
between arbitrary setoids.
*)

Record PartFunct (S1 S2 : Setoid) : Type := 
  {pf_dom :  S1 -> CProp;
   pf_dom_wd : pred_wd S1 pf_dom;
   pf_fun :> forall x : S1, pf_dom x -> S2;
   pf_wd  :  forall x y Hx Hy, x[=]y -> pf_fun x Hx [=] pf_fun y Hy}.

Implicit Arguments pf_dom [S1 S2].
Implicit Arguments pf_fun [S1 S2].

(**
A few characteristics of this definition should be explained:
 - The domain of the partial function is characterized by a predicate
that is required to be well defined but not strongly extensional.  The
motivation for this choice comes from two facts: first, one very
important subset of real numbers is the compact interval
[[a,b]]---characterized by the predicate [ fun x : IR => a [<=] x /\ x
[<=] b], which is not strongly extensional; on the other hand, if we
can apply a function to an element [s] of a setoid [S] it seems
reasonable (and at some point we do have to do it) to apply that same
function to any element [s'] which is equal to [s] from the point of
view of the setoid equality.
 - The last two conditions state that [pfpfun] is really a subsetoid
function.  The reason why we do not write it that way is the
following: when applying a partial function [f] to an element [s] of
[S] we also need a proof object [H]; with this definition the object
we get is [f(s,H)], where the proof is kept separate from the object.
Using subsetoid notation, we would get $f(\langle
s,H\rangle)$#f(&lang;s,H&rang;)#; from this we need to apply two
projections to get either the original object or the proof, and we
need to apply an extra constructor to get $f(\langle
s,H\rangle)$#f(&lang;s,H&rang;)# from [s] and [H].  This amounts
to spending more resources when actually working with these objects.
 - This record has type [Type], which is very unfortunate, because it
means in particular that we cannot use the well behaved set
existential quantification over partial functions; however, later on
we will manage to avoid this problem in a way that also justifies that
we don't really need to use that kind of quantification.  Another
approach to this definition that completely avoid this complication
would be to make [PartFunct] a dependent type, receiving the predicate
as an argument.  This does work in that it allows us to give
[PartFunct] type [Set] and do some useful stuff with it; however, we
are not able to define something as simple as an operator that gets a
function and returns its domain (because of the restrictions in the
type elimination rules).  This sounds very unnatural, and soon gets us
into strange problems that yield very unlikely definitions, which is
why we chose to altogether do away with this approach.

%\begin{convention}% All partial functions will henceforth be denoted 
by capital letters.
%\end{convention}%

We now present some methods for defining partial functions.
*)

(**
To begin with, we want to be able to ``see'' each total function as a 
partial function.
*)

Definition total_eq_part A B : Setoid_fun A B -> PartFunct A B :=
  fun f =>
  Build_PartFunct A B (fun _ => True) (fun _ _ _ _ => I) 
  (fun x _ =>  f x)  (fun x y _ _ H => (sf_wd A B f x y H)).

(**
In any setoid we can also define constant functions (one for each element 
of the setoid) and an identity function:

%\begin{convention}% Let [c:A].
%\end{convention}%
*)

Definition Fconst A B b := total_eq_part A B (Const_Setoid_fun A B b).


Definition Fid A := total_eq_part A A (id_un_op A).

(**
(These happen to be always total functions, but that is more or less obvious, 
as we have no information on the setoid; however, we will be able to define 
partial functions just applying other operators to these ones.)

If we have two setoid functions [F] and [G] we can always compose them.  
The domain of our new function will be the set of points [s] in 
the domain of [F] for which [F(s)] is in the domain of [G]#. 
#%\footnote{%Notice that the use of extension here is essential.%}.%  
The inversion in the order of the variables is done to maintain uniformity 
with the usual mathematical notation.

%\begin{convention}% Let [G,F:(PartFunct S)] and denote by [Q] and [P], 
respectively, the predicates characterizing their domains.
%\end{convention}%
*)

Section Part_Function_Composition.

Variables A B C : Setoid.
Variable G : PartFunct B C.
Variable F : PartFunct A B.

Let P := pf_dom F.
Let Q := pf_dom G.
Let R x := {Hx : P x | Q (F x Hx)}.

Lemma part_function_comp_dom_wd : pred_wd A R.
Proof.
intros x y [ Hx H ] H0.
unfold R.
exists (pf_dom_wd A B F x y Hx H0).
apply (pf_dom_wd B C G) with (F x Hx).
exact H.
apply pf_wd with (1:=H0).
Qed.

Let comp := (fun (x : A) (Hx : R x) => G (F x (ProjT1 Hx)) (ProjT2 Hx)).

Lemma part_function_comp_wd :
  forall (x y : A) (Hx : R x) (Hy : R y),
  x[=]y -> comp x Hx [=] comp y Hy.
Proof.
intros x y [ px qx ] [ py qy ] H.
unfold comp; simpl.
apply pf_wd.
apply pf_wd with (1:=H).
Qed.

Definition Fcomp : (PartFunct A C):=
  Build_PartFunct A C R part_function_comp_dom_wd comp part_function_comp_wd.

End Part_Function_Composition.

(* Different tokens for compatibility with coqdoc *)

Implicit Arguments Fconst [A B].
Notation "[-C-] x" := (Fconst x) (at level 2, right associativity).

Notation FId := (Fid _).

Implicit Arguments Fcomp [A B].
(*
Infix "[o]" := Fcomp (at level 65, no associativity).
*)

Hint Resolve pf_wd : algebra.

Set Implicit Arguments.

Section bijections.

(** **Bijections *)

Variables A B : Setoid.

Implicit Types f : (Setoid_fun A B).

Definition injective f := 
  forall x1 x2 : A, f x1 [=] f x2 -> x1 [=] x2.

Definition surjective f := 
  forall y : B, {x : A | f x [=] y}.

Definition bijective f := 
  injective f and surjective f.

Let bij2inj f (Bf : bijective f) : injective f := (CAnd_proj1 _ _ Bf).
Let bij2surj f (Bf : bijective f) : surjective f := (CAnd_proj2 _ _ Bf).

Definition inv_fun f (Bf : bijective f) : B -> A :=
  fun y => projT1 (bij2surj Bf y).

Definition inv_prf f (Bf : bijective f) : 
  forall y : B, f (inv_fun Bf y) [=] y :=
  fun y => projT2 (bij2surj Bf y).

(* use setoid_rewrite instead ! *)
Remark eq_wd : 
  forall (X : Setoid) (x x' y y' : X),
  x[=]x' -> y[=]y' -> x[=]y -> x'[=]y'.
Proof.
intros X x x' y y' xx' yy' xy.
trans x.
symm.
trans y.
Qed.

Lemma inv_fun_wd :
  forall f (Bf : bijective f),
  fun_wd (inv_fun Bf).
Proof.
intros f Bf y1 y2 H.
apply (bij2inj Bf).
apply eq_wd with (x:=y1) (y:=y2).
symm.
apply inv_prf.
symm.
apply inv_prf.
exact H.
Qed.

Definition Inv f (Bf : bijective f) :=
  Build_Setoid_fun B A (inv_fun Bf) (inv_fun_wd Bf).

End bijections.

Section inverses.

(** **Inverses *)

Definition left_inverse A B (f : Setoid_fun A B) (g : Setoid_fun B A) :=
  forall x : A, g (f x) [=] x.

Variables A B : Setoid.

Implicit Types f : (Setoid_fun A B).
Implicit Types g : (Setoid_fun B A).

Definition right_inverse f g :=
  left_inverse g f. (* forall y : B, f (g y) [=] y *)

Definition inverse f g :=
  left_inverse f g and right_inverse f g.

Lemma left_inverse_injective :
  forall f g, 
  left_inverse f g ->
  injective f.
Proof.
intros f g H x1 x2 H0.
apply eq_wd with (1:=(H x1)) (2:=(H x2)).
apply sf_wd with (1:=H0).
Qed.

Lemma right_inverse_surjective :
  forall f g,
  right_inverse f g ->
  surjective f.
Proof.
intros f g H y.
exists (g y).
exact (H y).
Qed.

Lemma inverse_bijective :
  forall f g,
  inverse f g ->
  bijective f.
Proof.
intros f g [ Hl Hr ].
split.
apply left_inverse_injective with (1:=Hl).
apply right_inverse_surjective with (1:=Hr).
Qed.

Lemma Inv_right_inverse :
  forall f (Bf : bijective f),
  right_inverse f (Inv Bf).
Proof.
intros f Bf y.
exact (inv_prf Bf y).
Qed.

Lemma Inv_left_inverse :
  forall f (Bf : bijective f),
  left_inverse f (Inv Bf).
Proof.
intros f [ Hi Hs ] x.
apply Hi.
apply Inv_right_inverse.
Qed.

Lemma Inv_inverse : 
  forall f (Bf : bijective f),
  inverse f (Inv Bf).
Proof.
intros f Bf.
split.
exact (Inv_left_inverse Bf).
exact (Inv_right_inverse Bf).
Qed.

End inverses.

Section Inv_bijection.

Variables A B : Setoid.

Implicit Types f : Setoid_fun A B.
Implicit Types g : Setoid_fun B A.

Lemma inverse_symmetric :
  forall f g,
  inverse f g -> 
  inverse g f.
Proof.
intros f g [ Hl Hr ].
split; [ exact Hr | exact Hl ].
Qed.

Lemma Inv_bijective : 
  forall f (Bf : bijective f),
  bijective (Inv Bf).
Proof.
intros f Bf.
apply inverse_bijective with (g:=f).
apply inverse_symmetric.
apply Inv_inverse.
Qed.

End Inv_bijection.

Section composition_inverse.

Variables A B C : Setoid.
Variable f : Setoid_fun A B.
Variable f' : Setoid_fun B A.
Variable h : Setoid_fun B C.
Variable h' : Setoid_fun C B.

Lemma composition_preserves_inverse :
  inverse f f' ->
  inverse h h' ->
  inverse (f[o]h) (h'[o]f').
Proof.
intros [ lif rif ] [ lih rih ].
split; red; intro x; simpl.
trans (f' (f x)).
apply sf_wd.
red in lih.
apply lih.
trans (h (h' x)).
apply sf_wd.
apply rif.
Qed.

End composition_inverse.

Section combinators_and_bijections.

Variables A B C : Setoid.

Lemma id_is_bij : 
  bijective (id_un_op A).
Proof.
split; red; simpl.
intros x1 x2 H; exact H.
intro y; exists y; apply eq_reflexive.
Qed.

Implicit Types f : (Setoid_fun A B).
Implicit Types g : (Setoid_fun B C).

Lemma composition_respects_bijection: 
  forall f g, 
  bijective f -> 
  bijective g ->
  bijective (f[o]g).
Proof.
intros f g [Injf Surf ] [ Injg Surg ].
split; red; simpl.
intros a1 a2 H.
apply Injf; apply Injg; exact H.
intro c.
elim (Surg c); intros b H.
elim (Surf b); intros a H0.
exists a.
trans (g b).
apply sf_wd with (1:=H0).
Qed.

End combinators_and_bijections.
