Require Export Arith.
Require Export mytactics.

(*The next uni (universe) is the disjoint union of all Sets*)

Inductive uni:Type:=
          InU: forall A:Set, forall a:A, uni.

Definition Pw (A:Set): Type:=(A -> Prop).

Record Sub : Type :=
   {S_carr:>Set; S_prop:>(Pw S_carr)}.



Definition ins (A:Sub)(a:A):=(S_prop A a).
Infix "[e]" := ins (at level 80).

Notation "x <- y":= (y[e]x) (at level 80).


Definition InS : Set -> Sub.
intro A.
exact (Build_Sub A (fun x:A=>True)).
Defined.


Definition tt (a:uni):Sub.
intro a.
destruct a.
exact (InS A).
Defined.

Check ins.


Inductive uniS:Type:=
          InUS: forall A:Sub, forall a:A, uniS.

Definition ttS (a:uniS):Sub.
intro a.
destruct a.
exact (InS A).
Defined.


Definition esti (a:uniS)(A:Sub):Prop:= ((ttS a)=(A)).
Definition esti2 (a:uniS)(A:Sub):Prop:= ((ttS a)=(InS A)).

(*Lemma L1 : forall (a:uniS)(A:Sub), (esti a A)<->(esti2 a A).
intros.
spl.
intro.
unfold esti2.
unfold esti in H.
rr H.
destruct A.
simpl.
unfold InS.

unfold InS.

unfold ttS.
simpl.

intuition.
unfold ttS.*)


Definition InF (A B:Set)(f:A->B):(InS A)[=>](InS B).
intros. simpl. assumption. 
Defined.

Definition restr (A:Sub)(P:Pw A):Sub.
intros A P.
exact (Build_Sub A (fun a:A=>(P a)/\(a<-A))).
Defined.

Definition S_fun (A B:Sub):= (Build_Sub (A->B) (fun f:(A->B)
=>forall a:A,(a<-A)->((f a)<-B))).

Infix "[=>]" := S_fun (at level 80).

Infix "|" := restr (at level 80).

Lemma aussonderung : 
forall (A:Sub) (P:(Pw A)) a, (a<-(A|P))<->(a<-A)/\(P a).
intros.
spl.
intro.
unfold ins in H.
unfold restr in H.
destruct H.
unfold ins.
spl.

intro.
destruct H.
unfold restr.
simpl.
spl.
Qed.

Section bij.

Variables A B C:Sub.

Definition inj (f:A[=>]B):Prop:= ((f<-(A[=>]B))/\(forall a
b,(a<-A)->(b<-A)->(f a)=(f b)-> a=b)).  

Definition sur (f:A[=>]B):Prop:= ((f<-(A[=>]B)/\
(forall b,(b<-B)->exists a,(a<-A)/\(f a)=b))).

Definition bij (f:A[=>]B):=(inj f)/\(sur f).

Definition iso :=(exists f:A[=>]B,(bij f)).
End bij.

Infix "=1" := iso (at level 80).

Ltac des x y z:=
       destruct x as [y z].

Section comp.
Variable A B C :Sub.

Definition comp (g:B[=>]C)(f:A[=>]B):= (fun a:A=>(g(f a))).
(*End comp.*)

Infix "[o]" := comp (at level 80).

(*Section iso.
Variables A B C:Sub.*)

Lemma ap_t : forall f a, a<-A->f<-(A[=>]B)->(f a)<-B.
intros f a P Q.
unfold ins in Q.
simpl in Q.
ap (Q a).
Qed.

End comp.

Section comp2.
Variables A B C:Sub.

Check comp.


Lemma comp_t : 
forall f g, f<-(A[=>]B)->g<-(B[=>]C)->((comp A B C g f)<-(A[=>]C)).
intros f g P Q.
intros a R.
unfold comp.
ap (ap_t B C g (f a)).
ap (ap_t A B f a).
Qed.

Lemma iso_trans : ((A =1 B)->(B=1 C)->(A=1 C)).
unfold iso.
intros P Q.
des P f bij_f.
des Q g bij_g.
exists (comp A B C g f).
des bij_f inj_f sur_f.
des bij_g inj_g sur_g.
des inj_f inj_f_t inj_f_p.
des sur_f sur_f_t sur_f_p.
des inj_g inj_g_t inj_g_p.
des sur_g sur_g_t sur_g_p.

spl.
spl.
ap (comp_t f g).
intros a b P Q R.
unfold comp in R.
assert ((f a)=(f b)).
ap inj_g_p.
ap (ap_t A B f).
ap (ap_t A B f).
ap (inj_f_p).

spl.
ap (comp_t f g).
intros c P.
assert (exists b,(b<-B)/\(g b)=c).
elim (sur_g_p c P). intros b Q. (*!*)
exists b.
aa.
get H b Q.
des Q Q1 Q2.
elim (sur_f_p b Q1). 
intros a R.
exists a.
unfold comp.
get R R1 R2.
rr R2.
rr Q2.
intuition.
Qed.

End comp2.

Axiom iso_sym: forall A B:Sub, (A =1 B)->(B=1A).

Definition N := (InS nat).
Definition N_ n := Build_Sub nat (fun i => (i < n)).

Definition Finite (A:Sub):Prop :=
   exists n,  A=1 (N_ n).


Definition Singleton (A:Sub) (a:A):= A|(fun x:A=>(x=a)).

Section decidable.
Variable A B:Sub.


Definition Emptyset := Build_Sub A (fun a=> False).

Definition isempty (A:Sub):=~(exists a,a<-A).

Lemma Empty_isempty : (isempty Emptyset).
unfold isempty; unfold Emptyset.
simpl.
intro.
elim H.
intuition.
Qed.

Lemma isempty_N0 : (forall A,(isempty A)<->(A=1 (N_ 0))).
intro C.
spl.
intro P.
unfold isempty in P.
exists (fun b:C=>0).
unfold bij.
split.
unfold inj.
spl.

simpl.
intros b Q.
assert (exists b, b<-C).
exists b. aa.
elim (P H).

intros a b Q R S.
assert (exists b, b<- C).
exists b. aa.
elim (P H).

unfold sur.
simpl.
spl.
intros b Q.
assert (exists b,b<-C).
exists b; aa.
elim (P H).
intros b Q.
elim (le_Sn_O b Q).

intro P.
unfold isempty. 
intro Q.
des Q a R.
get P f S.
intro Q.
assert ((f a)<O).
ap (ap_t C (N_ O) f a).
des Q inj_g sur_g.
des inj_g inj_g_t inj_g_p.
aa.
ap (le_Sn_O (f a)).
Qed.

Lemma isempty_finite :forall A,(isempty A)->(Finite A).

intros BB P.
exists O.
assert ((isempty BB)->(BB=1 (N_ O))).

get (isempty_N0 BB ) T U.
intuition.
Qed.


Lemma empty_finite : (Finite Emptyset).
apply (isempty_finite).
ap Empty_isempty.
Qed.

Definition decidable (P:Pw A):=
forall a,{(P a)}+{~(P a)}.

Check decidable.

Lemma subset_empty_empty : forall P, (isempty A)->(isempty(A|P)).
unfold isempty.
intros P Q R.
unfold ins in R.
unfold restr in R.
simpl in R.
get R a RR.
assert (exists a,a<-A).
exists a.
get RR SS TT.
ap (Q H).
Qed.

Lemma eqset_finite :
  forall A B, A =1 B -> Finite A -> Finite B.
intros C D P.
unfold Finite.
intro Q.
get Q n R.
exists n.
assert (D=1 C).
ap iso_sym.
apply (iso_trans D C (N_ n)).
aa.
aa.
Qed.

Lemma eqset_isempty:
forall A B, A=1B -> (isempty A)->(isempty B).
intros C D P Q.
assert (D=1 N_ 0).
assert (C=1 N_ 0).
el (isempty_N0 C) R.
intro T.
ap R.
assert (D=1C).
ap iso_sym.
ap (iso_trans D C (N_ 0)).
el (isempty_N0 D) R.
intro T.
ap T.
Qed.

Definition extend (P:Pw A)(a:A):= fun x:A=>(P x)\/(x=a).
Infix "U":= extend (at level 70).

Definition eqprop (P Q:Pw A):Prop:=
forall a,(P a)<->(Q a).
Infix "=p":=eqprop(at level 70).

Lemma eqprop_sym:forall P Q,(P=p Q)->(Q=p P).
intros P Q.
unfold eqprop.
intros.
elim (H a).
intuition.
Qed.


Definition I (A:Sub):=fun a:A=>a.
Lemma typeI: (I A<-(A[=>]A)).
unfold ins; unfold S_fun.
simpl.
intros a P.
unfold I.
aa.
Qed.

Lemma eqprop_iso : (forall P Q, (P=pQ)->(A|P)=1(A|Q)).
intros P Q R.
exists (I A).
unfold bij.
unfold I.
spl.
unfold inj.
spl.
unfold ins.
unfold S_fun.
simpl.
intros a Z.
unfold eqprop in R.
intuition.
el (R a) T.
intro.
ap (T H).

intros. aa.
unfold sur.
simpl.
spl.
intros; intuition.
elim (R a).
intros X1 X2; ap (X1 H0).
intros.
exists b. spl. intuition.
elim (R b); intros.
ap (H2 H0).
reflexivity.
Qed.

Lemma 
add_one_preserves_finiteness :
   forall P a,(decidable P)-> Finite (A|P) -> Finite (A|(P U a)).
Proof.
intros P a Q R.
elim (Q a); intro X.
assert ((A|P)=1(A|P U a)).
ap (eqprop_iso).
unfold eqprop.
intros x.
spl.
unfold extend.
intuition.
intro T.
unfold extend in T.
elim T; intros.
aa.
rr H.
ap (eqset_finite (A|P)).

get R k Y.
exists (S k).
ap iso_sym.
assert (N_ k=1 (A|P)).
ap iso_sym.
clear Y.
get H f Z.
des Z inj_f sur_f.
exists (fun n=> if n=k then a else (f n)).
spl.

des inj_f inj_f_t inj_f_p.
unfold  ins in inj_f_t.
unfold S_fun in inj_f_t.
simpl in inj_f_t.
simpl in f.

assert ((P U a)=p P).
unfold eqprop.
intros x.
spl.
unfold extend.
intuition.
rr H0.
intro R.
unfold extend.
left. aa.
ap (eqset_finite (A|P) (A|(P U a))).

ap eqprop_sym.


assert (Finite (A|P)).
exists k.
aa.
ap (eqprop_iso P (P U a)).





Lemma dec_subset_finite_finite : forall P:(Pw A),
(Finite A)->(decidable P)->(Finite (A|P)).
intros P fin_A dec_P.
des fin_A k bij_k.
induction k.

assert (isempty (A|P)).
ap subset_empty_empty.

getc (isempty_N0 A) Q R.
ap R.
ap (isempty_finite).

(* Now the induction step *)
assert (N_ (S k)=1 A).
ap iso_sym.

des H f bij_f.
des bij_f inj_f sur_f.
Check (dec_P (f k)).
elim (dec_P (f k)); intro.

Abort.
