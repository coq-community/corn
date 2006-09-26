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
Require Export mytactics.

(* Now PERs *)

Definition Rel (A:Set):= A ->A->Prop.
Definition Trans (A: Set)(R:Rel A):=forall a b c, (R a b)->(R b c)->(R a c).
Definition Sym (A:Set)(R:Rel A):= forall a b, (R a b)->(R b a).

Implicit Arguments Trans [A].
Implicit Arguments Sym [A].

Record Per :Type:=
{car:Set;
 rel:>(Rel car);
 trans:(Trans rel);
 sym:(Sym rel)}.

Definition isin (A:Per)(a:car A):Prop.
intros.
destruct A as [cA rA trA srA].
simpl in a.
exact (rA a a).
Defined.

Notation "a <- A" := (isin A a) (at level 60).

Record bar (A:Per):Type:=
{el:>car A;
 elin:rel A el el}.

Implicit Arguments el [A].
Implicit Arguments elin [A].

Coercion bar : Per>->Sortclass.




(**** R [x] S in Per ******)

Inductive prod (A B:Set): Set:=
               pair:A->B->(prod A B).

Implicit Arguments pair [A B].

Infix "[x1]" := prod (at level 80).

Definition prodp_car (A B:Per):Set.
intros P Q.
exact ((car P)[x1](car Q)).
Defined.

Definition prodp_rel (A B:Per):(Rel (prodp_car A B)).
intros A B.
unfold Rel.
unfold prodp_car.
intros [a b] [a' b'].
exact ((rel A a a')/\(rel B b b')).
Defined.

Lemma prodp_t: forall (A B:Per),(Trans (prodp_rel A B)).
intros.
unfold Trans.
intros [a1 b1] [a2 b2] [a3 b3].
simpl.
intros. spl.
intuition.
apply (trans A) with a2; aa.
intuition.
apply (trans B) with b2;
aa.
Save.

Lemma prodp_s: forall (A B:Per),(Sym (prodp_rel A B)).
intros A B.
unfold Sym.
intros [a1 b1][a2 b2] [P Q].
simpl.

spl.

ap (sym A).
ap (sym B).
Qed.

Definition prodp (A B:Per):Per.
intros A B.
exact 
(Build_Per(prodp_car A B)(prodp_rel A B)(prodp_t A B)(prodp_s A B)).
Defined.

Definition pairp (A B:Per):A->B->(prodp A B).
intros A B a b.
simpl.
Check pair.
apply (Build_bar _ (pair (el a)(el b))).
Defined.

Infix "[x]":= prodp (at level 80).

Lemma L6:forall A B,forall (c:(A[x]B)),
exists a:A, exists b:B, c=(pairp A B a b).
intros.
destruct c as [a b].
exists a.
exists b.
reflexivity.
Save.

Lemma L7 :forall A B:Per,forall (a1 a2:A) (b1 b2:B),
(pairp A B a1 b1)=(pairp A B a2 b2) <->
((a1=a2)/\(b1=b2)).
intros A B a1 a2 b1 b2.
split.
unfold pairp.
intro.
inversion H.
intuition.
intro.
get H PP QQ.
rr PP.
rr QQ.
reflexivity.
Save.

(********** R[=>]S ***************)

Definition Perf (A B:Per)(f:A->B):Prop.
intros.
destruct A as [A rA trA srA].
destruct B as [B rB trB srB].
exact (forall a a':A,(rA a a')->(rB (f a)(f a'))).
Defined.

Ltac desP A B C D:= destruct A as [A B C D].

Definition Pfeq (A B:Per)(f g:A->B):Prop.
intros.
simpl in f.
simpl in g.
destruct A as [cA rA tA sA].
destruct B as [cB rB tB sB].

set (A:=Build_Per cA rA tA sA).
set (B:=Build_Per cB rB tB sB).

exact ((Perf A B f)/\(Perf A B g)/\forall a:A,((rA a a)->(rB (f a)(g a)))).
Defined.


Notation "f '[=pf]' g" := (Pfeq _ _ f g) (at level 68).

Lemma tPfeq : forall A B :Per,(Trans (A->B) (Pfeq A B)).
Proof.
intros A B.
unfold Trans.
intros f g h.
desP A rA trA srA.
desP B rB trB srB.
simpl_all.
intros [ H [ H0 H1 ] ] [ H2 [ H3 H4 ] ].
spl.
ap H.
spl.
ap H3.
apply trB with (g a).
ap H1.
ap H4.
Qed.

Lemma sPfeq : forall A B :Per,(Sym (A->B) (Pfeq A B)).
intros A B.
desP A rA trA srA.
desP B rB trB srB.
unfold Sym.
simpl.
intros f g X.
spl.
get X XX YY.
get YY Z ZZ.
ap (Z a a').
spl.
get X XX Y.
get Y YY Z.
ap XX.
ap srB.
get X XX Y.
get Y YY Z.
ap Z.
Qed.


Definition PerFS (A B:Per):Per.
intros A B.
exact (Build_Per (A->B)(Pfeq A B)(tPfeq A B)(sPfeq A B)).
Defined.

Infix "[=>]" := PerFS (at level 66).

Definition sur (A B:Per)(f:A[=>]B):Prop.
intros.
destruct B as [cB rB tB sB].
exact (forall b, (rB b b)->exists a, (rB b (f a))).
Defined.

(********* R/S *******)

Definition PRel (A B:Per):= (A->B->Prop).

Record okPRel (A:Per):Type:=
{rR:>A->A->Prop(*PRel A A*);
tR:(Trans A rR);
sR:(Sym A rR);
iR:forall a b:A,(rel A a b)->(rR a b)}.

Definition quot (A:Per)(R:okPRel A):Per.
intros A R.
destruct A as [cA rA tA sA].
destruct R as [rRel tRel sRel].
simpl in rRel.
simpl in tRel.
simpl in sRel.
exact (Build_Per cA rRel tRel sRel).
Defined.

Infix "[/]" := quot (at level 70).

Definition can (A:Per)(R:okPRel A):(A[=>](A [/] R)).
intros A.
destruct A as [cA rA tA sA].
intro R.
destruct R as [rRR tRR sRR]. 
simpl.
exact (fun a=>a).
Defined.


Lemma main : forall (A:Per)(R:okPRel A),(can A R)<-(A[=>](A [/] R)).
intros A R.
simpl.
destruct A as [cA rA tA sA].
destruct R as [rRR tRR sRR iRR].
unfold Pfeq.
simpl.
spl.
apply iRR.
simpl. aa.
spl.
ap iRR.
ap iRR.
Defined.

Lemma main2 :forall (A:Per)(R:okPRel A),(sur _ _ (can A R)).
intros A R.
destruct A as [cA rA tA sA].
destruct R as [rRR tRR sRR iRR].
simpl.
intro.
exists b.
aa.
Qed.


(*Notation "'[' a ']_' A '[/]' R" := 
  (can A R a) (at level 80, format "'[' [ a ]_ A [/] R ']'").*)

Notation "'[' a ']_' R" := 
  (can _ R a) (at level 80, format "'[' [ a ]_ R ']'").

Notation "x [=] y" := (rel _ x y) (at level 81).

Lemma main3 : 
  forall (A : Per) (R : okPRel A) (a b : A),
  (R a b)<->([a]_R[=][b]_R).
Proof.
intros.
spl.
destruct R.
destruct A.
unfold can.
simpl in H.
simpl in a.
simpl in b.
simpl.
aa.
destruct A.
destruct R.
simpl.
ap H.
Defined.

(**************** Subsets ********************)
Definition compatible (A:Per)(P:A->Prop):Prop.
intros.

exact (forall a,(a<-A)->(P a)).
Defined.


Definition cRestr (A:Per)(P:A->Prop):(Rel A).
intros.
unfold Rel.
intros a b.
destruct A as [cA rA tA sA].
simpl in a.
simpl in b.
exact ((rA a b)/\(P a)/\(P b)).
Defined.

Lemma L38 : forall (A:Per)(P:A->Prop),(Trans A (cRestr A P)).
intro A.
destruct A as [cA rA tA sA].
unfold cRestr; unfold Trans.
simpl. intros.
spl.
intuition.
apply tA with b; aa.
spl.
intuition.
intuition.
Qed.

Lemma L39 : forall (A:Per)(P:A->Prop),(Sym A (cRestr A P)).
intro A.
destruct A as [cA rA tA sA].
unfold cRestr; unfold Trans; simpl.
intros.
unfold Sym.
intros.
spl.
ap sA.
aa.
intuition.
intuition.
Qed.

Definition restr (A:Per)(P:A->Prop):Per.
intros A P.
set (R:= (cRestr A P)).
assert (Trans A R).
ap (L38 A P).
assert (Sym A R).
ap (L39 A P).
exact (Build_Per A R H H0).
Defined.


Infix "[|]" := restr (at level 69).

Lemma L100 :forall (A:Per)(P Q:A->Prop)(a b:A),
(rel ((A[|]P)[|]Q)a b)<->(rel ((A[|]Q)[|]P)a b).
intros [cA rA tA sA].
intros.
simpl_all.
intuition.
Qed.

Lemma L101:forall (A:Per)(P Q R:A->Prop)(a b:A),
(rel ((A[|]P)[|]Q)a b)<->(rel ((A[|]Q)[|]P)a b).
intros.
unfold restr.
destruct A as [Ac Ar At As].
simpl.
intuition.
Qed.


Notation "{ x : A | P }" := (restr A (fun x => P))
  (at level 0, x at level 99) : type_scope.

Lemma L30 : 
  forall (A:Per) (a:A) (P:A->Prop), 
  a<-{ x : A | P x } 
  <->
  a<-A/\(P a).
Proof.
intros [ A R t s ] a P.
simpl.
intuition.
Qed.

(********************** Universe ********************)

Inductive unv:Type:=
          InU: forall A:Set, forall a:A, unv.


Definition URel:=(unv->unv->Prop).
Definition UTrans (R:URel):=(forall a b c,(R a b)->(R b c)->(R a c)).
Definition USym (R:URel):=(forall a b, (R a b)->(R b a)).

Record UPer:Type:=
{urel:>URel;
utrans:(UTrans urel);
usym:(USym urel)}.

Definition uin (a:unv)(A:UPer):Prop.
intros.
destruct A as [rA tA sA].
exact (rA a a).
Defined.

Infix "<~" := uin (at level 70).

Definition Ucompatible (A:UPer)(P:unv->Prop):Prop.
intros.
exact (forall a,(a<~A)->(P a)).
Defined.


Definition ucRestr (A:UPer)(P:unv->Prop):(unv->unv->Prop).
intros A P.
intros a b.
exact ((urel A a b)/\(P a)/\(P b)).
Defined.

Lemma L385 : forall (A:UPer)(P:unv->Prop),(UTrans (ucRestr A P)).
intro A.
destruct A as [rA tA sA].
unfold ucRestr; unfold Trans.
simpl. intros.
unfold UTrans.
intros.
intuition.
apply tA with b; aa.
Qed.

Lemma L395 : forall (A:UPer)(P:unv->Prop),(USym (ucRestr A P)).
intro A.
destruct A as [rA tA sA].
unfold ucRestr; unfold UTrans; simpl.
intros.
unfold USym.
intros.
spl.
ap sA.
intuition.
intuition.
Qed.

Definition urestr (A:UPer)(P:unv->Prop):UPer.
intros A P.
set (R:= (ucRestr A P)).
assert (UTrans R).
ap (L385 A P).
assert (USym R).
ap (L395 A P).
exact (Build_UPer R H H0).
Defined.

Infix "@" := urestr (at level 69).

Lemma L31 : forall A a (P:unv->Prop),a<~(A@P) <-> (a<~A/\(P a)).
intros.
unfold urestr.
unfold ucRestr.
unfold uin.
destruct A as [rA tA sA]; destruct a.
simpl.
split.
intuition.
intuition.
Qed.

(************************* A sub B ****************************)

Definition restr_f1 (A B:Per)(P:A->Prop)(f:A[=>]B):{ x:A | P x}[=>]B.
intros A B P f.
exact f.
Defined.

Definition restr_f2 (A B:Per)(Q:B->Prop)(f:A[=>]B):A[=>]{b:B|Q b}.
intros A B Q f.
exact f.
Defined.

Definition restr_f (A B:Per)(P:A->Prop)(Q:B->Prop)(f:A[=>]{y:B|Q y}):
{ x:A | P x}[=>]B.
intros A B P Q f.
exact f.
Defined.

Lemma L1000: forall (A B : Per)(f : A[=>]B)(x : A),
(f<-(A[=>]B))->(rel A x x) ->(rel B (f x) (f x)).
intros A B f a p.
unfold isin in p.
unfold PerFS in f.
simpl_all.
intro q.
unfold Pfeq in p.
simpl_all.
destruct A as [Ac Ar At As].
destruct B as [Bc Br Bt Bs].
simpl_all.
intuition.
Qed.


Lemma L1001:forall (A B:Per)(P:A->Prop)(Q:B->Prop)
(f:A[=>]{y:B|Q y}),(f<-(A[=>]{y:B|Q y}))->
(restr_f A B P Q f) <- ({ x:A | P x}[=>]B).
intros A B P Q f.
unfold isin.
destruct A as [AC AR AT AS].
destruct B as [BC BR BT BS].
simpl_all.
unfold restr_f.
intuition.
el (H0 a a') p.
intro r. aa.
el (H a a') p.
intro; aa.
el (H a a) p; intro; aa.
Qed.

(************************* The END ****************************)
