Require Export mytactics.

(* Now PERs *)

Inductive unv:Type:=
          InU: forall A:Set, forall a:A, unv.

Check (unv->Prop).

Definition Pw := (unv->Prop).
Definition set:Type :=Pw.

Definition isin (a:unv)(A:set): Prop.
intros a A.
exact (A a).
Defined.

Infix "<~" := isin (at level 70).

(*******)

Definition Rel := unv ->unv->Prop.

Definition trans (R:Rel):= forall a b c, (R a b)->(R b c)->(R a c).
Definition sym   (R:Rel):= forall a b, (R a b)->(R b a).

Record Per :Type:=
{rel_p:>Rel;
 per_t:(trans rel_p);
 per_s:(sym rel_p)}.

Definition restr (A:Per)(P:Pw):Per.
intros A P.
destruct A as [rA tA sA].
set (rAP:=fun(a b:unv)=>(P a)/\(P b)/\(rA a b)).
assert (trans (fun(a b:unv)=>(P a)/\(P b)/\(rA a b))). (*??*)
unfold trans.
intros.
intuition.
apply tA with b.
aa. aa.
assert (sym (fun(a b:unv)=>(P a)/\(P b)/\(rA a b))).
unfold sym.
intros.
intuition.
exact (Build_Per (fun(a b:unv)=>(P a)/\(P b)/\(rA a b)) H H0).
Defined.

Print restr.
Print isin.

Infix "|":= restr (at level 69).

Definition isinP (a:unv)(A:Per):=(rel_p A a a).

Infix "<-":= isinP (at level 70).

Lemma L0 : forall a A P, (a<-A|P)->(a<-A).
intros.
destruct A as [rA tA sA].
unfold restr in H.
simpl in H.
intuition.
Qed.

Lemma L1 : forall a A P,(a<-A|P)<->((a<-A)/\(P a)).
intros a A P.
spl.  spl.
destruct A as [rA tA sA];
unfold restr in H;
simpl in H;
intuition.
destruct A as [rA tA sA].
unfold restr in H.
simpl in H.
intuition.

unfold isinP in H.
unfold isinP.
intuition.
destruct A as [rA tA sA].
unfold restr.
simpl.
intuition.
Defined.


(*******************)

Definition tt :unv->Set.
intro.
destruct X.
exact A.
Defined.

Definition InUS (A:Set):Per.
intro.
set (AA:=fun a b:unv=>(tt a)=(tt b)/\a=b).
assert (trans AA).
unfold AA;unfold trans.
intros.
spl.
intuition.
rr H1.
intuition.
rr H2.
assert (sym AA).
unfold AA; unfold sym.
intros.
intuition.
exact (Build_Per AA H H0).
Defined.

Definition Hom (R S:Per)(f:unv):Prop.
intros R S.
intro f.
exact (exists A B:Set,forall (a b:unv), (rel_p (InUS A) a b)->
(rel_p (InUS A) (f (InU (tt A) a)) (f (InU (tt B) b)))).


Definition compatible (A B:Per):Prop.
intros.
destruct A as [rA tA sA].
destruct B as [rB tB sB].
exact (forall a b,(rA a b)->(rB a b)).
Defined.

Definition restrP (A R:Per):Per.
intros A R.
destruct A as [rA trA srA].
exact R.
Defined.

Infix "|P" := restrP (at level 66).


Definition Perf (A B:Per)(f:unv->unv):Prop.
intros.
destruct A as [rA tA sA].
destruct B as [rB tB sB].
exact (forall a a',(rA a a')->(rB (f a)(f a'))).
Defined.

Ltac desP A B C D:= destruct A as [A B C D].

Definition rPerf (A B:Per)(f g:unv->unv):Prop.
intros.
destruct A as [rA tA sA].
destruct B as [rB tB sB].

(* Trying to destruct A, while keeping it prevents me to use the coercion? 
Check (forall a:A, rA a a).*)
set (A:=Build_Per rA tA sA).
set (B:=Build_Per rB tB sB).
exact ((Perf A B f)/\(Perf A B g)/\forall a,((rA a a)->(rB (f a)(g a)))).
Defined.

Print rPerf.

(* Infix "[=pf]" := rPerf (at level 68).*)

Notation "f '[=pf]' g" := (rPerf _ _ f g) (at level 68).

Check rPerf.
Print Rel.

Lemma trPerf : (trans (rPerf)).
intros.
unfold trans.
intros f g h.
intros.
desP A rA trA srA.
desP B rB trB srB.

simpl in *|- * .
spl.
apply trB with (g a).
intuition. 
ap H5.
apply trA with a'.
ap H0.
ap srA.
ap srA.

apply trB with (g a').
get H0 X Y.
ap X.
ap srB.
get H X Y.
get Y YY ZZ.
ap (ZZ a').
apply trA with a.
apply srA.
aa. aa.
intuition.
apply trB with (g a).
ap H4.
ap H5.
Qed.

Lemma srPerf : forall A B :Per,(sym (A->B) (rPerf A B)).
intros A B.
desP A rA trA srA.
desP B rB trB srB.
unfold sym.
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
exact (Build_Per (A->B)(rPerf A B)(trPerf A B)(srPerf A B)).
Defined.

Infix "[=>]" := PerFS (at level 66).

Definition canonical : forall (A:Per) (R:Rel3 A A),forall (p:trans A
R)(q:sym A R), (A[=>]((A|R) p q)).
intros A.
destruct A as [cA rA tA sA].
set (A:=(Build_Per cA rA tA sA)).
intros R p q.

simpl.

intro a.
exact a.
Qed.

Definition sur (A B:Per)(f:A[=>]B):Prop.
intros.
destruct B as [cB rB tB sB].
exact (forall b, (rB b b)->exists a, (rB b (f a))).
Defined.

Record Rel4 (A:Per):Type:=
{rR:>Rel3 A A;
tR:(trans A rR);
sR:(sym A rR);
iR:forall a b:A,(rel_p A a b)->(rR a b)}.

Definition restr2 (A:Per)(R:Rel4 A):Per.
intros A R.
destruct A as [cA rA tA sA].
destruct R as [rRel tRel sRel].
simpl in rRel.
simpl in tRel.
simpl in sRel.
exact (Build_Per cA rRel tRel sRel).
Defined.

Infix "|2" := restr2 (at level 70).

Definition canonical2 (A:Per)(R:Rel4 A):(A[=>](A|2 R)).
intros A.
destruct A as [cA rA tA sA].
intro R.
destruct R as [rRR tRR sRR]. (* rR tR sR not possible!*)
simpl.
exact (fun a=>a).
Defined.

Lemma main : forall (A:Per)(R:Rel4 A),
(canonical2 A R)<-(A[=>](A|2 R)).
intros A R.
simpl.
destruct A as [cA rA tA sA].
destruct R as [rRR tRR sRR iRR].
unfold rPerf.
simpl.
spl.
apply iRR.
simpl. aa.
spl.
ap iRR.
ap iRR.
Defined.

Lemma main2 :forall (A:Per)(R:Rel4 A),(sur _ _ (canonical2 A R)).
intros A R.
destruct A as [cA rA tA sA].
destruct R as [rRR tRR sRR iRR].
simpl.
intro.
exists b.
aa.
Qed.

Notation "A a '[=]' a'" := (rel_p A a a') (at level 70).

Lemma main3 : forall (A:Per)(R:Rel4 A)(a b:A),
(rR A R a b)<->(rel_p (A|2 R) (canonical2 A R a) (canonical2 _ R b)).
intros.
spl.
destruct R.
destruct A.
unfold canonical2.
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












