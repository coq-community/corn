Require Export mytactics.

(* Now PERs *)

Definition Rel (A:Type):= A ->A->Prop.
Definition Trans (A: Type)(R:Rel A):=forall a b c, (R a b)->(R b c)->(R a c).
Definition Sym (A:Type)(R:Rel A):= forall a b, (R a b)->(R b a).

Implicit Arguments Trans [A].
Implicit Arguments Sym [A].

Record Per :Type:=
{car:Type;
 rel:(Rel car);
 trans:(Trans rel);
 sym:(Sym rel)}.

Definition Peq (A :Per)(a b:car A):Prop.
intros A a b.
exact (rel A a b).
Defined.

Implicit Arguments Peq [A].

Infix "[=]":= Peq (at level 80).

Definition isin (A:Per)(a:car A):=(rel A a a).

Notation "a <- A" := (isin A a) (at level 60).

Record bar (A:Per):Type:=
{el:>car A;
 elin:rel A el el}.


Implicit Arguments el [A].
Implicit Arguments elin [A].
Coercion bar : Per>->Sortclass.

Definition Bar (A:Per):Type.
intro.
set (AA:= bar A).
set (rA:=fun (a b:AA)=>(rel A (el a)(el b))).
assert (Trans rA).
unfold Trans.
unfold rA.
intros a b c P Q.
destruct A as [cA1 rA1 tA1 sA1].
simpl_all.
unfold Trans in tA1.
ap (tA1 (el a)(el b)(el c)).
assert (Sym rA).
unfold Sym.
unfold rA.
intros.
destruct A as [cA1 rA1 tA1 sA1].
simpl_all.
ap (sA1 (el a)(el b)).
exact (Build_Per AA rA H H0).
Defined.

Lemma treq:forall (A:Type)(a b c:A),(a=b)->(b=c)->(a=c).
Proof.
intros A a b c P Q.
rr P.
Qed.

Lemma symeq:forall (A:Type)(a b:A), (a=b)->(b=a).
Proof.
intros A a b P.
rr P.
reflexivity.
Qed.

(*Implicit Arguments treq [A].
Implicit Arguments symeq [A].*)

Definition Type_to_Per (A:Type):Per.
intro A.
set (eqa:=fun a b:A=>(a=b)).
exact (Build_Per A eqa (treq A) (symeq A)).
Defined.

(********** R[=>]S ***************)

Definition Perf (A B:Per)(f:A->B):Prop.
intros.
exact (forall a a':A,(rel A a a')->(rel B (f a)(f a'))).
Defined.

Ltac desP A B C D:= destruct A as [A B C D].

Definition apperf (A B:Per)(f:A->B)(a:A):B.
intros A B f a.
Check (f a).
exact (f a).
Defined.

Implicit Arguments apperf [A B].
Implicit Arguments Perf [A B].

Definition Pfeq (A B : Per) := 
  fun f g : A -> B => 
  Perf f /\ Perf g /\ forall a:A, rel B (f a) (g a).  

Notation "f '[=pf]' g" := (Pfeq _ _ f g) (at level 68).

Lemma tPfeq : forall A B :Per,(Trans (Pfeq A B)).
Proof.
intros A B.
unfold Trans.
intros f g h.
unfold Pfeq.
intuition.
assert (Trans (rel B)).
ap (trans B).
unfold Trans in H6.
assert (rel B (apperf f a) (apperf g a)).
apply (H4 a).
aa.
assert (rel B (apperf g a)(apperf h a)).
apply (H5 a).
aa.

clear H4 H5 H1 H H0 H2.
destruct a as [aa pa].
simpl in H3.
clear H3.
apply (H6 (f (Build_bar A aa pa)) 
(g (Build_bar A aa pa)) (h (Build_bar A aa pa))).
aa.
aa.
Qed.

Lemma sPfeq : forall A B :Per,(Sym (Pfeq A B)).
Proof.
intros A B.
desP A rA trA srA.
desP B rB trB srB.
unfold Sym.
simpl.
intros f g X.
spl.
get X XX YY.
get YY Z ZZ.
spl.
unfold Pfeq in X. intuition.
simpl.
unfold Pfeq in X.
intuition.
unfold Sym in srB.
ap srB.
ap H3.
Qed.


Definition PerFS (A B:Per):Per.
intros A B.
Check (bar A).
Check (tPfeq).
destruct A as [cA rA tA sA].
destruct B as [cB rB tB sB].
Check Pfeq.
Check (Build_Per (cA -> cB)).
set (A:= Build_Per cA rA tA sA).
Check (Pfeq A).
set (B:= Build_Per cB rB tB sB).
Check Pfeq. Check (bar A). 
Check (Build_Per (A -> B) (Pfeq A B)(tPfeq A B)).
exact (Build_Per (A -> B)(Pfeq A B)(tPfeq A B)(sPfeq A B)).
Defined.

Infix "[=>]" := PerFS (at level 66).

Definition pfap (A B:Per)(f:A[=>]B)(a:A):B.
intros A B f a.
destruct f as [ff pf].
destruct a as [aa pa].
unfold PerFS in ff.
destruct A as [cA rA tA sA].
simpl_all.
destruct B as [cB rB tB sB].
simpl_all.
Check ff.
Check el.
set (A:=Build_Per cA rA tA sA).

set (B:=Build_Per cB rB tB sB).
simpl.
unfold Pfeq in pf.
set (a:=Build_bar A aa pa).
set (bb:=(apperf ff a)).
exact bb.
Defined.

Implicit Arguments pfap [A B].

Infix "[ ]" := pfap (at level 80).

Lemma pfapok: forall (A B:Per)(f:A[=>]B) (a:A),(a<-A)->((f[ ]a)<-B).
intros.
destruct a as [aa pa].
destruct A as [cA rA tA sA].
destruct B as [cB rB tB sB].
destruct f as [ff pf].
unfold pfap.
simpl  in aa.
unfold apperf.
unfold isin.
unfold PerFS in pf.
simpl_all.
unfold Pfeq in pf.
intuition.
set (A:=Build_Per cA rA tA sA).
simpl in H3.
unfold apperf in H3.
simpl.
set (a:= (Build_bar A aa pa)).

ap (H3 a).
Defined.

Definition id (A:Per):A[=>]A.
intros A.
set (idA:=fun (a:A)=>a).
assert (idA[=pf]idA).
unfold Pfeq.
unfold Perf.
intuition.
Check (Build_bar (A->A) idA H).
unfold PerFS.
destruct A.



(**** R [x] S in Per ******)

Inductive prod (A B:Type): Type:=
               pair:A->B->(prod A B).

Implicit Arguments pair [A B].

Infix "[x1]" := prod (at level 80).

Definition prodp_car (A B:Per):Type.
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
Defined.

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
apply (Build_bar (prodp A B)(pair (el a)(el b))).
simpl.
intuition.
destruct a.
simpl.
aa.
destruct b.
intuition.
Defined.

Print pairp.
Implicit Arguments pairp [A B].

Infix "[x]":= prodp (at level 80).

Lemma L6:forall A B,forall (c:(A[x]B)),
exists a:A, exists b:B, c[=](pairp a b).
Proof.
intros A B.
intros [[a b] p].
unfold prodp in p.
unfold prodp_car in p.
unfold prodp_rel in p.
destruct A as [cA rA tA sA].
destruct B as [cB rB tB sB].
simpl_all.

unfold pairp.
unfold prodp.
elim p.
intros pa pb.
set (A:= Build_Per cA rA tA sA).
set (a0:= Build_bar A a pa).
set (B:=Build_Per cB rB tB sB).
set (b0:=Build_bar B b pb).
exists a0; exists b0.
simpl.
intuition.
Qed.

Lemma L7 :forall A B:Per,forall (a1 a2:A) (b1 b2:B),
(pairp a1 b1)[=](pairp a2 b2) <->
((a1[=]a2)/\(b1[=]b2)).
intros A B a1 a2 b1 b2.
split.
intro P.
spl.
unfold pairp in P.
destruct A.
destruct B.
simpl_all.

intuition.
unfold pairp in P.
destruct A;
destruct B.
simpl_all.
intuition.
intro.
get H PP QQ.
Save.


(********* R/S *******)

Definition PRel (A B:Per):= (A->B->Prop).
Definition PPred (A:Per):= (A->Prop).

Definition okpred (A:Per)(P:PPred A):Prop.
intros A P.
exact (forall (a b:A),(rel A a b)->(P a)->(P b)).
Defined.

Definition okrel (A B:Per)(R:PRel A B):Prop.
intros A B R.
exact (forall (a a' : A)(b:B), (rel A a a')->(R a b)->(R a' b)).
Defined.


Record okPRel (A:Per):Type:=
{rR:A->A->Prop(*PRel A A*);
tR:(Trans rR);
sR:(Sym rR);
iR:forall a b:A,(rel A a b)->(rR a b)}.

Definition quot (A:Per)(R:okPRel A):Per.
intros A R.
Check (rR A R).
set (RR:=fun a b:A=>(rR A R (a)(b))).
assert (Trans RR).
unfold Trans.
unfold RR.
intros a b c P Q.
ap (tR A R a b c).

assert (Sym RR).
unfold Sym; unfold RR.
intros a b P.
ap (sR A R).
exact (Build_Per (A) RR H H0).
Defined.

Infix "[/]" := quot (at level 70).

Definition can (A:Per)(R:okPRel A):(A[=>](A [/] R)).
intros A.
intro R.

set (idA:=fun a:A=>a).
Check idA.
unfold quot.
destruct A.
unfold PerFS.
simpl.
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
