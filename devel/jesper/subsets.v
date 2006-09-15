(* Copyright © 1998-2006
 * Henk Barendregt
 * Luís Cruz-Filipe
 * Herman Geuvers
 * Mariusz Giero
 * Rik van Ginneken
 * Dimitri Hendriks
 * Sébastien Hinderer
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
(** Subsets are defined as propositional functions and a number of
lemmas are proved about them. Also equivalence relations on subsets
are defined. In particular, finite subsets are considered and finite
choice is proved. In this file we avoid packing things in
records. There is also a file [subsetspacked.v] which provides
additional results about records.

The ideas behind this file can be found in [[
@InProceedings{carlstromsubsets,
  author    = {Jesper Carlstr{\"o}m},
  title     = {Subsets, Quotients and Partial Functions 
               in {M}artin-{L}{\"o}f's Type Theory},
  editor    = {Herman Geuvers and Freek Wiedijk},
  booktitle = {Types for Proofs and Programs, Second International Workshop,
               {TYPES} 2002, {B}erg en {D}al, {T}he {N}etherlands, 
               {A}pril 24--28, 2002, Selected Papers},
  publisher = {Springer},
  series    = {Lecture Notes in Computer Science},
  volume    = {2646},
  pages     = {78-94},
  year      = {2003},
  isbn      = {3-540-14031-X},
  bibsource = {DBLP, http://dblp.uni-trier.de},
  note      = {\url{http://www.springerlink.com/openurl.asp?genre=article&issn=0302-9743&volume=2646&spage=78}},
}
]]  

Some definitions have been altered for practical reasons. For
instance, reflexivity as defined in the paper have been divided in the
conjunction of two principles: reflexivity and proof-irrelevance. That
made it easier to apply reflexivity.

We rely very much on implicit arguments in the following way. Partial
functions take two arguments, so applications should look like [f x p],
where [p] is a proof that [x] is in the domain of the function. The
implicit arguments mechanism of Coq could not hide [p], but [x] can be
hidden. Therefore I preferred to write [f x' x] rather than [f x p],
because we can then hide [x'] and write simply [f x], which is easier
to read. It is suggested to think of [x] as representing the object in
the domain, even though it is in fact a proof that such an object is
indeed in the domain. Notice that this leads to non-standard notation:
to say [y=f x] we say [y:f x in codomain], because [y] should be a
proof that [f x] is in the codomain.

This file was written by J. Carlstrom, Spring 2004, University of
Nijmegen. Financed by Calculemus.

*)

Require Export CLogic.

(** We use the lemma [eq_proofs_unicity] which is in the following module.
It will prove that partial functions from [nat] do not depend on
proofs *)

Require Coq.Logic.Eqdep_dec.

(** The following tactic replaces all [b] with [a] and tries to solve the
result using [auto]. It introduces the assumption [a=b]. *)

Ltac equal a b :=
  cut (a=b); [destruct 1;auto|idtac].

(** The following is exists-elimination on a hypothesis H in the
context. It introduces variables x p. *)

Ltac existse H x p := elim H; clear H; intros x p.

(* begin hide *)
Set Implicit Arguments.
Unset Strict Implicit.
(* end hide *)

(** [bin] is the the type of binary relations on a type *)

Definition bin (X:Type) := (X->X->CProp).


(** ** Preliminary stuff about equivalence relations *)
Section setoids.

Variable carrier:Type.

Definition refl (R:bin carrier) :=
   forall x:carrier, R x x.

Definition sym (R:bin carrier) :=
   forall x y:carrier, R x y -> R y x.

Definition trans (R:bin carrier) :=
   forall x y z:carrier, R x y -> R y z -> R x z.

End setoids.


(** ** Definition of subsets and common algebraic operations on them *)
Section subsets.

Variable (carrier:Type).

Definition subset (X:Type) : Type := X->CProp.

Definition insubset (x:carrier) (U:subset carrier) := U x.
Infix "in" := insubset (at level 60).

Definition intersection (U V:subset carrier) x := x in U and x in V.
Definition union (U V:subset carrier) x := x in U or x in V.
Definition complement (U:subset carrier) x := Not (x in U).

Definition intersection_family (I:Type) (U:I->(subset carrier)) x :=
  forall i:I, x in U i.

Definition union_family (I:Type) (U:I->(subset carrier)) x :=
  {i:I | x in U i}.

Definition includedin (U V:subset carrier):= forall x:carrier, 
    x in U -> x in V.

Infix "<=" := includedin (at level 70).

Definition extequal (U V:subset carrier) := (U <= V) and (V <= U).

Infix "=_ext" := extequal (at level 70).

Lemma extequal_refl: refl (extequal).
Proof.
intros U.
split; intro p; trivial.
Qed.

Lemma extequal_sym: sym extequal.
Proof.
intros U V [p q].
split; auto.
Qed.

Lemma extequal_trans: trans extequal.
Proof.
intros U V W [p q] [r s].
split; intros a t; auto.
Qed.

Let binaryfam (A:Type) (U1 U2:subset A) : bool -> subset A :=
   fun b => match b with
              | true => U1
              | false => U2
            end.

Lemma intersection_bool_family: forall (U V:subset carrier), 
   (intersection_family (binaryfam U V)) =_ext intersection U V.
Proof.
intros U V.
split; intros x' x.
  split.
    apply (x true).
  apply (x false).
elim x; intros t f.
intro b; elim b; assumption.
Qed.

End subsets.


Infix "in" := insubset (at level 60).
Infix "/\" := intersection.
Infix "\/" := union.
Notation "~ U" := (complement U).
Notation "'for' x 'in' U , P" :=
    (forall (x':_) (x:x' in U), P)
    (at level 200, x ident).
Notation "'exists' x 'in' U , P" :=
    {x':_ |{ x:(x' in U) | P}}
    (at level 200, x ident).
Infix "<=" := includedin.
Infix "=_ext" := extequal (at level 70).




(** ** Extensionality of the operations on subsets *)
Section subsetalgebra.

Variable carrier:Type.
Variables U V U' V':subset carrier.

Lemma intersection_ext:
   (U =_ext U') -> (V =_ext V') -> ((U /\ V) =_ext (U' /\ V')).
Proof.
intros [p q] [r s].
split; intros a [u v]; split; auto.
Qed.

Lemma union_ext:
   (U =_ext U') -> (V =_ext V') -> ((U \/ V) =_ext (U' \/ V')).
Proof.
intros [p q] [r s].
split; (intros a [u | v]; [left | right]; auto).
Qed.

Lemma complement_ext: (U =_ext V) -> ((~ U) =_ext (~ V)).
Proof.
intros [p q].
split; intros a r s; auto.
Qed.

Lemma deMorgan: (~ (U \/ V)) =_ext (~ U /\ ~V).
Proof.
split.
intros a p.
split; intro q; apply p; [left|right]; assumption.
intros a [p q] [r|s]; auto.
Qed.

End subsetalgebra.




(** * Quotients 

We now define equivalence relations on subsets *)
Section quotients.

Variables carrier:Type.
Variable domain:subset carrier.

Definition bin_on := (for x in domain, for y in domain, CProp).

Variable R:bin_on.

Infix "~" := R (at level 70). 

Definition underlying (x':carrier) (_:x' in domain) := x'.

Definition refl_part := for x in domain, x~x.

Definition sym_part := for x in domain, for y in domain, x~y -> y~x.

Definition trans_part := 
   for x in domain,
   for y in domain,
   for z in domain,   x~y -> y~z -> x~z.

Definition proofirr :=
   for x in domain,
   for y in domain,
   forall z:(underlying x) in domain,
   forall w:(underlying y) in domain,
   z~w -> x~y.


(** 
The finest of all reflexive and proof-irrelevant relations is the
relation [same] *)

Definition same:bin_on := fun
   (x':_) (x:x' in domain)
   (y':_) (y:y' in domain) =>
    x'=y'.

Lemma strongrefl: proofirr ->
                  refl_part -> 
                  forall a:carrier,
                  forall (x y:a in domain),
                  x~y.
Proof.
intros Hpirr Hrefl a x y.
apply Hpirr with x x.
apply Hrefl.
Qed.

Lemma same_finest: proofirr ->
                   refl_part ->
                   for x in domain,
                   for y in domain,
                   same x y -> x ~ y.
Proof.
intros Hpirr Hrefl x' x y' y; compute.
destruct 1; apply strongrefl; assumption.
Qed.

(**

Every relation on a subset can be extended by reflexive closure to a
total relation. If the first relation is an equivalence relation on
the subset, the reflexive closure is an equivalence relation. 

*)

Definition reflexive_closure : bin carrier := 
    fun x' y':carrier => 
   (x'=y') or {x:(x' in domain) | {y:(y' in domain) | x~y}}.

(** reflexive relations on subsets extend to reflexive relations *)

Lemma reflexive_closure_refl: refl reflexive_closure.
Proof.
intros x'.
left; auto.
Qed.

(** symmetric relations on subsets extend to symmetric relations *)

Lemma reflexive_closure_of_sym_sym: sym_part -> sym reflexive_closure.
Proof.
intros s x' y' [eq|H].
 left; symmetry; assumption.
existse H x H.
existse H y H.
right; exists y; exists x; auto.
Qed.


(** Interestingly, we don't have the analogous lemma for transitivity,
since it might happen that we have 

   - [R x' x y' y]
   - [R y' u z' z]

and so the reflexive closure will identify x' with y' and y' with z',
but not necessarily x' with z' (because y need not be the same as
u). We need also proofirr to prove transitivity. *)

Lemma reflexive_closure_of_pirr_trans_trans: 
   proofirr -> trans_part -> trans reflexive_closure.
Proof.
intros Hpirr Htr x' y' z' [id| p].
  destruct id.
  intros [id| p].
    destruct id.
    left; reflexivity.
  existse p x H.
  existse H z e.
  right; exists x; exists z; assumption.
existse p x H.
existse H y e.
intros [id| p].
  destruct id.
  right; exists x; exists y; assumption.
existse p y2 H.
existse H z e2.
right; exists x; exists z.
apply Htr with y' y; auto.
apply Hpirr with y2 z; auto.
Qed.

End quotients.

(* begin hide *)
Implicit Arguments same [carrier x' x'0].
(* end hide *)


(** * Partial Functions *)
Section partialfunctions.

(* A partial function is: *)
Notation "U ~> B" := (for x in U, B) (at level 0).

Variables carrier cocarrier:Type.
Variable domain:subset carrier.
Variable codomain:subset cocarrier.
Variable R:bin_on domain.
Variable R_co:bin_on codomain.
Variable f:domain ~> cocarrier.

Infix "~" := R (at level 70).
Infix "~~" := R_co (at level 70).


Definition into := for x in domain, f x in codomain.

(** We do not consider a partial function to be f *together* with its
into-proof. Rather, f itself is a partial function. This will be
useful because we can then vary the codomain. Being into a codomain is
a predicate on partial functions.

Think of the identity function on a type as an example of a partial
function. We define things so that extensionality and injectivity of
it are both equivalent to proofirr of the relation. For surjectivity,
see below. *)

Definition extensional :=
   for x in domain, 
   for x' in domain, 
   forall y:f x in codomain,
   forall y':f x' in codomain,
   x~x' -> y~~y'.   

(** The following definition will sometimes be useful, namely as a
substitute for f_i and extensionality when one knows that f x is in a
subset and that x~x' *)

Definition into_extensional :=
   for x in domain,
   for x' in domain,
   x~x' -> f x' in codomain -> f x in codomain.

Definition injective :=
   for x in domain, 
   for x' in domain,
   forall y:f x in codomain,
   forall y':f x' in codomain,
   y ~~ y' -> x ~ x'.

(** We do as Bishop and consider a partial function to be surjective
to a subset if it has a (possible non-extensional) right inverse. *)

Variable g:codomain ~> carrier.

Definition isinv : CProp :=
                 for y in codomain,
                 forall x:(g y in domain),
                 forall y':(f x in codomain), y' ~~ y.

End partialfunctions.

Notation "U ~> B" := (for x in U, B) (at level 0).






(** ** Bijections *)
Section bijections.

Variables carrier cocarrier:Type.
Variable domain:subset carrier.
Variable codomain:subset cocarrier.
Variable R:bin_on domain.
Variable R_co:bin_on codomain.
Variable f:domain ~> cocarrier.
Hypothesis Hpirr_domain:proofirr R.
Hypothesis Hpirr_codomain:proofirr R_co.
Hypothesis Hsym_codomain:sym_part R_co.
Hypothesis Htr_codomain:trans_part R_co.

(** Assume f is surjective: *)

Hypothesis f_i:into codomain f.
Variable finv:codomain ~> carrier.
Hypothesis finv_i:into domain finv.
Hypothesis isid:isinv R_co f finv.


Infix "~" := R (at level 70).
Infix "~~" := R_co (at level 70).


Lemma inv_ext:
   injective R R_co f -> 
   extensional R_co R finv.
Proof.
intros Hinj y1' y1 y2' y2 x1 x2 H.
apply Hinj with (f_i x1) (f_i x2).
apply Htr_codomain with y1' y1; trivial.
apply Htr_codomain with y2' y2; auto.
Qed.

Lemma inv_leftinv:
   injective R R_co f ->
   isinv R finv f.
Proof.
intros Hinj x' x1 y x2.
apply Hinj with (f_i x2) y; auto.
Qed.
   
Lemma inv_injective:
   extensional R R_co f ->
   injective R_co R finv.
Proof.
intros Hext b y b' y' x x' eq.
apply Htr_codomain with (f x) (f_i x); auto.
apply Htr_codomain with (f x') (f_i x'); auto.
Qed.

End bijections.


(** ** Compositions *)
Section compositions.

(** We will introduce a lot of hypotheses stating that all relations
are equivalence relations. However, we will use only a few of
them. When this section is closed, lemmas will depend only on the
relevant assumptions. This is an advantage compared to the setoid
approach, where all lemmas depend on all equivalence relation
properties. *)

Variables A B C:Type.
Variable X:subset A.
Variable Y:subset B.
Variable Z:subset C.

Variable RX:bin_on X.
Variable RY:bin_on Y.
Variable RZ:bin_on Z.

Hypothesis Xpirr:proofirr RX.
Hypothesis Ypirr:proofirr RY.
Hypothesis Zpirr:proofirr RZ.

Hypothesis Xrefl:refl_part RX.
Hypothesis Yrefl:refl_part RY.
Hypothesis Zrefl:refl_part RZ.

Hypothesis Xsym:sym_part RX.
Hypothesis Ysym:sym_part RY.
Hypothesis Zsym:sym_part RZ.

Hypothesis Xtr:trans_part RX.
Hypothesis Ytr:trans_part RY.
Hypothesis Ztr:trans_part RZ.

Variable f:X ~> B.
Variable g:Y ~> C.

Hypothesis f_i:into Y f.

Definition composition (a:A) (x:a in X) := g (f_i x).

Infix "~X" := RX (at level 70).
Infix "~Y" := RY (at level 70).
Infix "~Z" := RZ (at level 70).

Lemma composition_extensional:
   extensional RX RY f ->
   extensional RY RZ g ->
   extensional RX RZ composition. 
Proof.
compute; auto.
Qed.

(** We don't need to assume that f is extensional. *)

Hypothesis Hextg:extensional RY RZ g.


Lemma composition_injective:  
   injective RX RY f ->
   injective RY RZ g ->
   injective RX RZ composition. 
Proof.
intros Hinjf Hinjg.
intros a x a' x' b y H.
apply Hinjf with (f_i x) (f_i x').
apply Hinjg with b y; auto.
Qed.

(** We now prove that a composition of two surjections is again a
surjection. So suppose f and g are surjections: *)

Hypothesis finv:Y ~> A.
Hypothesis finv_i:into X finv.
Hypothesis fisid:isinv RY f finv.

Hypothesis g_i:into Z g.
Hypothesis ginv:Z ~> B.
Hypothesis ginv_i:into Y ginv.
Hypothesis gisid:isinv RZ g ginv.

Lemma gf_i : (*for x in X, composition x in Z.*)
into Z composition.
Proof.
intros x' x; unfold composition.
apply g_i.
Qed.

(** The composition is: *)

Definition gfinv := 
   fun (c:C) (z:c in Z) => finv (ginv_i z).

(** That it is surjective means that it has the following properties: *)

Lemma gfinv_i : into X gfinv.
intros c z.
compute in *|-*; auto.
Qed.

Lemma gfisid:isinv RZ composition gfinv.
Proof.
intros c z x z'.
apply Ztr with (g (ginv_i z)) (g_i (ginv_i z)); trivial.
compute; auto.
Qed.


End compositions.





(** * Finite subsets *)
Section finiteness.

Variables carrier:Type.
Variables domain:subset carrier.
Variables R:bin_on domain.

Definition fin n : subset nat := fun k => {l:nat | k + S l = n}.



Definition decidable (P:CProp) :CProp := P or Not P.

Lemma nat_discrete: forall m n:nat, decidable (m=n).
Proof.
intros m n.
compare m n.
intro H; left; assumption.
intro H; right; auto.
Qed.

(** We assume we are dealing with a finite subset. However, we
simultaneously prove properties of subfinite subsets, as the
injectivity will be rarely used. When this section is closed, all
lemmas that do not depend on the injectivity will be applicable also
to subfinite subsets. *)

Hypothesis Hpirr: proofirr R.
Hypothesis Hrefl: refl_part R.
Hypothesis Hsym: sym_part R.
Hypothesis Htr: trans_part R.
Variable n:nat.

Definition fineq := same (fin n).
Infix "=_fin" := fineq (at level 70).
Infix "~" := R (at level 70).

(** Finitely enumerable means there is a surjection [enum] from [fin n]
into the subset, that is, it has a right inverse [label]. According to
the definition of surjection, we shall assume the following: *)

Variable enum:(fin n) ~> carrier.
Hypothesis enum_i: into domain enum.
Hypothesis label:domain ~> nat.
Hypothesis label_i:into (fin n) label.

(** We must also assume that [enum] and [label] connects *)

Hypothesis enumisid: isinv R enum label.

(** Finiteness is the assumption of injectivity also. Notice that
lemmas that do not use this assumption can be applied to finitely
enumerable subsets *)

Hypothesis enum_inj: injective fineq R enum.

(** Now to some technical details. The following lemma is due to
M. Hofmann, but the proof is due to M. Hedberg. *)

Lemma Hofmann: forall (k l:nat)(p q:k=l), p=q.
Proof.
intros.
apply Coq.Logic.Eqdep_dec.eq_proofs_unicity.
intros x y; compare x y; auto.
Qed.

Lemma fin_unique_proofs : for k in fin n,
                          forall l:(underlying k) in fin n,
                          k=l.
Proof.
unfold underlying; intros uk k l.
existse k x p; existse l y q.
equal x y.
  equal p q; apply Hofmann.
auto with zarith.
Qed.
                          
(** This previous lemma will be used to prove that [enum] is
extensional in a very strong sense: *)

Lemma enum_super_ext: extensional fineq (same domain) enum.
Proof.
intros a k b l x y.
compute; destruct 1.
equal k l; apply fin_unique_proofs.
Qed.

Lemma enum_ext: extensional fineq R enum.
Proof.
intros a k b l x x' H.
equal (enum k) (enum l).
  apply Hpirr with x x; auto.
apply enum_super_ext; auto.
Qed.

(** The following is a consequence of injectivity by lemma inv_ext *)

Lemma label_ext : extensional R fineq label.
Proof.
apply inv_ext with enum; auto.
Qed.

(** We shall now prove that finite subsets are discrete *)

Definition discrete :=
   for x in domain,
   for y in domain, 
   decidable (x ~ y).

Lemma finite_discrete: discrete.
Proof.
intros a x b y.
compare (label x) (label y); intro H.
  left.
  apply Htr with (enum (label_i x)) (enum_i (label_i x)); auto.
  apply Htr with (enum (label_i y)) (enum_i (label_i y)); auto.
  apply enum_ext; assumption.
right.
intro Heq; elim H.
apply label_ext; auto.
Qed.

(** We will now prove finite choice. To this end, we assume we have a
surjective map f to our finite subset. In fact, we do not assume full surjectivity, because we need only that the image covers our domain (rather than equals the domain). *)

Variable B:Type.
Variable Y:subset B.
Variable RY:bin_on Y.
Hypothesis Ypirr:proofirr RY.
Hypothesis Yrefl:refl_part RY.
Variable f:Y ~> carrier.
Hypothesis finv:domain ~> B.
Hypothesis finv_i:into Y finv.
Hypothesis fisid:isinv R f finv.

Infix "~Y" := RY (at level 70).
  
Definition finite_choice_function : domain ~> B :=
    composition (composition finv enum_i) label_i.

Lemma finite_choice_function_i: into Y finite_choice_function.
Proof.
compute in *|-*; auto.
Qed.

(** This finite choice function is VERY extensional, namely from R to
the equality [same] which is the finest reflexive and proof-irrelevant
relation. *)

Lemma finite_choice_super_ext: extensional R (same Y) finite_choice_function.
Proof.
  unfold finite_choice_function. 
  apply composition_extensional with fineq.
    apply label_ext; auto.
  intros x k x' k' y y'.
  compute; destruct 1.
  equal k k'; apply fin_unique_proofs.
Qed.

(** The weaker extensionality follows as a corollary: *)

Lemma finite_choice_ext: extensional R RY finite_choice_function.
Proof.
  intros x k x' k' y y' eq.
  apply same_finest; auto.
  apply finite_choice_super_ext; auto.
Qed.

Lemma finite_choice: isinv R f finite_choice_function.
Proof.
intros a x y x2; compute.
apply Htr with (enum (label_i x)) (enum_i (label_i x)); auto.
Qed.

End finiteness.

