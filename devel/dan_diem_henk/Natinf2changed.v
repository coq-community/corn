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
Require Export Arith.
Require Export Bool.
Require Export Le.
Require Export Omega.
(* Henks stuff *)

Require Export Arith.
Require Export BoolToProp.

Ltac sympl f H :=
  unfold f;
  let T := type of H in
  let H0 := fresh "H" in 
  match constr:T with
  | (bp ?b)
      =>rewrite H
  | (not (bp ?b))
      =>cut (b = b); 
         [ pattern b at -1; case b; 
           [ intro H0; elim (H H0) | intro H0 ] 
           | reflexivity ]
  | _ =>fail "Sorry, I can't do the things you want me to!"
  end; try assumption.


Ltac btriv := 
        try (intro H);
        try (inversion H);
        unfold bp;
        try reflexivity.

Ltac rr x :=
     rewrite x; try assumption.

Ltac rl x:=
     rewrite<- x; try assumption.

Ltac spl :=
     split; try assumption.

Ltac get x y z:=
   elim x; intros  y; try intro z; try assumption; try assumption; clear x.

Ltac getc x y z:=
         elim x; intros  y z.

Ltac aa := try assumption.

Ltac ap x:= apply x; aa; aa.

Ltac el x y:=
     elim x; try intro y; try assumption.

Lemma btnd : forall b:bool, b\/~b.
intro b.
elim b.
left.
btriv.
right.
btriv.
Qed.

Ltac bcase x y:=
     elim (btnd x); try intro y.


(*Implicit Type n m k :nat.*)

Lemma a1 : forall n, ~(n<<n).
intro n.
boolToProp.
auto with arith.
Qed.



Lemma b1: forall n, n-<n.
intro.
boolToProp.
auto with arith.
Qed.

Lemma a2 : forall n, (n<< (S n)).
intro.
boolToProp.
auto with arith.
Qed.

Lemma a3 : forall n, ~(n<<O).
intro.
boolToProp.
auto with arith.
Qed.

Lemma b2 : forall n m, m<<(S n)->m-<n.
intros m n.

boolToProp.
auto with arith.
Qed.


Lemma b3 : forall n, O-<n.
intro.
boolToProp.
auto with arith.
Qed.


Lemma trans : forall n m k:nat, (n-<m)->(m-<k)->(n-<k).
intros n m k.
boolToProp.
omega.
Qed.

Lemma b4: forall n, n-<(S n).
intro.
boolToProp.
auto with arith.
Qed.

Lemma b5: forall n m, n<<m-> n-<m.
intros n m.
boolToProp.
auto with arith.
Qed.

Lemma a4 : forall n m, m <<(S n)-> ~m = n -> (m << n).
intros n m.
boolToProp.
omega.
Qed.

Lemma a5 : forall n m, n<<m ->~n=m.
intros n m.
boolToProp.
omega.
Qed.

Lemma a6 : forall n m, n-<m -> m-<n -> m = n.
intros n m.
boolToProp.
omega.
Qed.

Lemma a7 : forall n m, m <<(S n) -> ~(m << n)-> m = n.
intros n m.
boolToProp.
omega.
Qed.

Lemma a9 : forall n m:nat, (n<<m)->(n<<(S m)).
intros n m.
boolToProp.
omega.
Qed.

Axiom a10: forall n m:nat, (n<<(S m))->(n<<m)\/(n=m).

Lemma a11: forall n m:nat, (n<<(S m))->(n-<m).
intros n m.
boolToProp.
omega.
Qed.

Lemma a12: forall n m:nat, (m-<n)\/(n<<m).
intros n m.
boolToProp.
preBoolToPropSolve H.
omega.
Qed.

Lemma a13: forall n m :nat, (0<<n)->(0<<m)->((pred n)=(pred m))->(n=m).
intros n m.
boolToProp.
omega.
Qed.

Lemma a14: forall n m:nat, (n<<m)->(0<<m).
intros n m.
boolToProp.
omega.
Qed.

Lemma a15: forall n m:nat, (n-<m)->(n-<(S m)).
intros n m.
boolToProp.
omega.
Qed.

Lemma not_Sm_leq_m : forall m, ~(S m)-<m.
intro.
boolToProp.
omega.
Qed.

Lemma a16: forall n m:nat, (n-<m)->~((S m)-<n).
intros n m.
boolToProp.
omega.
Qed.

Lemma a17: forall n m:nat, (n<<m)->(n-<m).
intros n m.
boolToProp.
omega.
Qed.

Lemma a18: forall k n m:nat, (k-<n)->(n<<m)->(k=(pred m))-> k=n.
intros k n m.
boolToProp.
omega.
Qed.

(*Use nat as universe for now. *)

Definition universe := nat.
Definition set := nat -> Prop.

Definition isSubset s1 s2  := forall m:universe, (s2 m) -> (s1 m).
Definition protofun := universe -> universe.

Section ProtofunProperties.

Variable f g:protofun.
Variable A B:set.

Definition isfun f
:= forall m:universe, 
(A m) -> (B (f m)).


Definition IsInjective f := (isfun f)/\
              forall m k:universe, (A m)->(A k)->(f m) = (f k) ->  m = k.

Definition IsSurjective f  :=(isfun f)/\
           forall m:universe, (B m)->(exists n:universe, (A n) /\ (f n) = m).

Definition IsBijective := ((IsInjective f)/\ (IsSurjective f)).

Definition comp (f g: protofun) :protofun := fun x=>(f(g x)).
Infix "o":= comp (at level 4).
Check comp.

Check IsInjective.
Check isfun.

Axiom comp_pres_IsInj : 
forall f g:protofun, (IsInjective f)-> (IsInjective g)->(IsInjective (f o g)).
(* ??
clear f g.
unfold IsInjective.

intros f g P Q.
split.
unfold isfun.
*)



End ProtofunProperties.

Definition iso (A B:set):=(exists f:protofun,(IsBijective f A B)).

Infix "=1" := iso (at level 8).


Axiom sym_iso: forall A B:set, (A=1 B)->(B=1 A).


Definition N_ n := fun i => (i << n).

Definition Finite (A:set):Prop :=
   exists n:universe, exists f:protofun, IsBijective f A (N_ n).

Definition Emptyset := fun n:nat => false.

Axiom trans_iso: forall A B C:set, (A=1 B)->(B=1 C)->(A=1 C).
(*intros A B C P Q.
get P f P2.
get P2 P3 P4.
get Q g Q2.
get Q2 Q3 Q4.
*)



Implicit Types m n i : nat.






Implicit Types s : set.


Lemma empty_finite : (Finite Emptyset).
unfold Finite.
unfold Emptyset.
exists O.
exists (fun n => n).
unfold IsBijective.
split.

unfold IsInjective.
split.
unfold isfun.
intros m. 
btriv.

intros.
assumption.

split.
unfold isfun.
intros m. 
btriv.


intros m p.
unfold N_ in p.
assert False.
apply (a3 m p).
elim H.
Defined.

Definition Singleton n := fun m => n=m.
Notation "[ n ]":= (Singleton n).

Definition Union A B:set:= fun n => (A n)\/(B n).
Infix "[U]" := Union (at level 40, left associativity).


Definition eqset := fun A B:set => forall n:universe, (A n)<->(B n).
Infix "=s" := eqset (at level 70).

Lemma eqsetssame : forall A B:set, A=sB->Finite A->Finite B.
intros.
elim H0.
intros.

unfold Finite.
unfold Finite in H0.
elim H0; intros.
exists x0.
elim H2; intros.
exists x1.
elim H3.
intros.
split.
split.
elim H4; intros.
unfold isfun; intros.
apply H6.
elim (H m); intros.

apply (H10).
assumption.

intros.
elim (H4).
intros.
apply H10.
elim (H m).
intros.
auto.

elim (H k); intros.
intuition.
assumption.
split.
elim H5.
intros.
unfold isfun.
intros.
apply (H6 ).
elim (H m); intros; try assumption.
intuition.

intros.

elim H5; intros.
assert (exists n:universe, (A n)/\(x1 n)=m).
apply (H8 m).
assumption.
elim H9; intros.
exists x2.
elim H10; intros.
split.
elim (H x2); intros.
apply H13.
assumption.
assumption.
Defined.

Definition Decidable : set -> Set:=
   fun A:set => forall n:universe, {(A n)} + {~(A n)}.

Print set.

Definition dset := universe -> bool.


Lemma eqset_sym : forall A B:set, A=s B->B=s A.
Proof. 
intros.
unfold eqset.
unfold eqset in H.
intro; split.
elim (H n); intros P Q.
assumption.
elim (H n); intros P Q.
assumption.
Qed.


Lemma addonepresfinite : 
   forall A:dset, (Finite A)->forall n:universe,
      Finite (A[U][n]).                 (* One cannot state (A[U]{n})! *)
Proof.
intros A P n.
getc P k Q.
get Q f R.
get R XX YY.
get XX ZZ WW.
(* There are two cases: (A n) and ~(A n) *)
bcase (A n) Q.
(* In this case AU{n}=A *)
assert (A[U][n]=s A).
unfold eqset.
spl.
intro T.
el T PP.
rl PP.

intro U.
unfold Union.
left; assumption.

ap (eqsetssame A (A[U][n])).
ap (eqset_sym ((fun y : nat => A y)[U][n]) A H).

(* Case ~(A n) *)

exists (S k).
pose (ff := fun x=>if (A x) then (f x) else k).
exists ff.

assert (isfun ((fun y : nat => A y)[U][n]) (fun i => i << (S k)) ff).

unfold isfun.
intros m V.
elim V; intro Z.
sympl ff Z.
ap (a9 (f m) k).
ap (ZZ m).
rewrite<- Z.
sympl ff Q.
ap (a2 k).

spl.
spl.
intros m1 m2 X Y.
el X C; el Y D.
sympl ff C; sympl ff D.
ap (WW m1 m2 C D).

sympl ff C. 
rewrite D in Q.
sympl ff Q.

intro Q1.
assert (bp(f m1)<<k).
ap (ZZ m1).
rewrite Q1 in H1.
elim (a1 k H1).

el Y Q1.
rewrite<- C.
 sympl ff Q; sympl ff Q1.

intro K.
assert (bp(f m2)<<k).
ap ZZ.
rewrite<- K in H1.
elim (a1 k H1). 
 
rewrite<- Q1 in D.
elim (Q D).

rl C.
rl D.
trivial.

(* He he *)

unfold IsSurjective.
spl. 

intros m X.
bcase (m<<k) Y.
get YY C D.
elim (D m). intros mm Z. (* together not doable! *)
exists mm.
spl.
left.
get Z ZW WW.
trivial.
get Z ZW WW.
sympl ff ZW.
trivial.
assumption.

(* Other case ~(m<<k) *)
exists n.
spl.

right.
unfold Singleton.
reflexivity.

sympl ff Q.
assert (m=k).
apply (a7 k m X Y).
rewrite H1.
reflexivity.
Qed.











Implicit Types b : bool.

Definition eqb b1 b2: bool :=
                 match b1, b2 with
              true, true  => true
             |false, false => true
             | _, _ => false end.

Infix "[=]" := eqb (at level 70).

Definition notb : bool -> bool := fun b => (b [=] false).

Notation "[~]" := notb (at level 72).

Definition andb b1 b2 : bool :=
           match b1, b2 with
           true, true => true
          | _, _ => false end.

Definition orb b1 b2 : bool :=
           match b1, b2 with
           false, false => false
          | _, _ => true end.

Definition impb b1 b2 : bool :=
           match b1, b2 with
           true, false => false
          | _, _ => true end.

Infix "[/\]" := andb (at level 80, right associativity).

Infix "[\/]" := orb  (at level 85, right associativity).

Infix "[~>]" := impb  (at level 8, right associativity).




Fixpoint
 even n : bool:=
  match n with
    O => true
  | S x => odd x
  end
with
 odd n : bool :=
  match n with
    O => false
  | S x => even x
  end.

Lemma test: forall n, even n \/ odd n.
Proof.
induction n as [ | n IHn ]; simpl.
left; constructor.
elim IHn; intro H; [ right | left ]; exact H.
Qed.



Lemma bleqcor : forall n m:nat, (n-<m)\/~(n-<m).
unfold bp.
intros n m.
elim (n -< m).
left.
unfold bp.
trivial.

right.
unfold not.
intro.
discriminate H.
Save.

Print bleqcor.

Definition myf n m:nat:=
if (n -< m) then n else (pred n).


Lemma refl : forall n: nat, n-<n.
intro n.
induction n.
simpl.
unfold bp.
reflexivity.
simpl.
unfold bp.
trivial.
Qed.

Lemma c1 : (forall n m: nat, ((myf n m)-<n)).
intros n m.
elim (bleqcor n m); intro H;
sympl myf H.
apply (refl n).

induction n.
simpl.
unfold bp.
reflexivity.

unfold pred.
clear IHn.
clear m H H0.
induction n as [ | n ihn]. 
unfold bp.
reflexivity.
induction n.
simpl.
unfold bp; reflexivity.


simpl.
unfold bleq.
exact ihn.
Qed.

Definition All : set := (fun n=>true).


Lemma a78 : forall n m: nat, ~(m-<n)->(n<<m).
intros n m.
elim (a12 n m).
intros.
unfold not in H0.
elim (H0 H).

intros.
assumption.
Qed.

Definition compl: universe -> set:= 
fun x y:nat=> x<>y.

Lemma compl_iso : forall n:universe, ((compl n) =1 All).
intros n.
unfold iso.
pose (myg := (fun n x:universe=>(if x-<n then x else pred x))).
exists (myg n). 

assert (isfun (compl n) All (myg n) ).
unfold isfun.
intros.
unfold All.
btriv.

split.
split.
assumption.

intros m k.
intros p q.

elim (bleqcor m n);
elim (bleqcor k n).
intros P Q. 

sympl myg P.
sympl myg Q.
trivial.

intros P Q.
sympl myg P.
sympl myg Q.
intros R.
assert (bp(n<<k)).
apply (a78 n k P).
assert (m=n).
apply  (a18 m n k ).
assumption. assumption.
assumption.
rewrite H2 in p.
unfold compl in p.
elim p.
split.
intros PP QQ.
sympl myg PP.
sympl myg QQ.
intro RR.

(* apply (a8 n).
apply (a8 n).


intros P Q.

sympl myg P.
sympl myg Q.
intro R.
*)
assert (bp(n<<m)).
apply  (a78 n m QQ).
assert (k=n).
Check a18.
apply  (a18 k n m ).
assumption. assumption.
apply sym_eq. assumption.
rewrite H2 in q.
unfold compl in q.
elim q.
split.

intros PP QQ.

(* apply (a8 n).
apply (a8 n).

intros.

generalize H2.*)

sympl myg PP.
sympl myg QQ.

intro R.
apply a13.
Focus 3.
assumption.

apply (a14 n ).
apply (a78 n m QQ).
apply (a14 n k).
apply (a78 n k PP).

unfold IsSurjective.
split.
assumption.
intros m P.
elim (bleqcor n m); intro R.
exists (S m).
assert (~(bp((S m)-<n))).
elim (bleqcor (S m) n); intro.
simpl.
simpl.
apply (a16 n m R).
assumption.
split.



unfold compl.
assert (bp(n-<(S m))).
apply (a15 n m R).
sympl andb H0.

intro.
rewrite<- H3 in H1.
apply H0.
rr H3.
ap refl.

sympl myg H0.
simpl.
reflexivity.

(* sympl andb H1. 
btriv.
intro.
elim H3; intros.
inversion H5.
sympl myg H0.
simpl.
reflexivity.*)

assert (bp(m-<n)).

apply (a17 m n).
apply (a78 m n).
assumption.

exists m.
split.
Focus 2.

sympl myg H0.
reflexivity.
(* ????? *)

unfold compl.
unfold bp.
unfold bp in H0.
intro PP.
rewrite PP in R.
ap R.
ap refl.
Qed.

Lemma hulp: forall k, ((N_ (S k))=1 All) -> 
exists m, (N_ k)=1 (compl m).
Proof.
intros k P.
unfold iso in P.
get P f Q.
elim Q.
intro R.
intro S. (* get Q R S did not work! *)
get S X Y.
exists (f k).

get R PP QQ.

unfold iso.
exists f.
spl.
spl.
unfold isfun; intros.
intro.
ap (a5 (f k)(f m)).
assert (k=m).
ap (QQ  k m).
ap a2.
ap a9.
rewrite H1 in H.
elim (a1 m H).

intros m1 m2 P1 P2.
ap QQ.
ap a9.
ap a9.

spl.
intros m RR.
unfold compl; intro SS.
ap (a5 m k).
ap QQ.
ap a9.
ap a2.
elim SS; intros.
ap a6.
ap refl.
ap refl.

intros m RR.
get Q TT UU.
get UU VV WW.
el (WW m) l.
intro xx.

exists l.
spl.

Focus 2.
get xx YY ZZ.
get xx YY ZZ.

ap a4.
intro.
rewrite H in ZZ.
ap RR.
spl.
Qed.

Lemma nat_not_finite : ~(Finite All).
Proof.

unfold not; intro H.
unfold Finite in H.
elim H; intro k.
induction k.

intro P.
elim P; intros g Q.
assert (bp(N_ O(g O))).
unfold IsBijective in Q.
elim Q; intros.
unfold IsInjective in H0.
unfold isfun in H0.
elim H0; intros.

apply (H2 O).
unfold All.
btriv.

unfold N_ in H0.
ap (a3(g O)).
intro P.

assert ((N_ (S k))=1 All).
ap sym_iso.

assert (exists m,(N_ k)=1 (compl m)).
ap hulp.
get H1 m QQ.
ap IHk.
assert (compl m)=1 All.
ap compl_iso.
assert (N_ k)=1 All.
apply trans_iso with (compl m).
assumption.
assumption.
ap sym_iso.
Qed.




Definition myh (n:nat):nat->nat:=
fun k:nat=>if beq k n then O else k.

Lemma aap : (myh O 1)= 1.
simpl.
assert (~(bp(beq O 1))).
simpl.
btriv.
sympl myh H.
simpl.
trivial.
Qed.

Definition Inf (A:set):= ~(Finite A).
Definition DInf A:= exists a:universe,
                exists f:protofun,(A a)/\ (isfun A A f)
               /\(IsInjective A (compl a) f).

Lemma DedInf_Inf: forall A:set, (DInf A)->(Inf A).
intros A P.
get P a Q.
get Q f R.
get R R1 R2.
get R2 R R3.

unfold Inf; unfold Finite.
intro S.
get S n S1.
get S1 g S. (*?*)
intro S.

get S PP QQ.
clear QQ.
assert (exists g, IsInjective A (fun i => i << n) g).
exists g.
aa.
clear PP; clear g.

induction n.

get H g P.
get P P1 P2.

assert (bp(g a)<<O).
ap P1.
ap (a3 (g a) H).
ap IHn.
clear IHn.

get H g T.
get T T1 T2.
bcase ((g a)=b n) UU.
Check (comp f g). (* (f o g) does not work *)

exists (comp g f).

unfold IsInjective.
split.

unfold isfun.
intros m P.
unfold comp.
unfold isfun in T1.
assert (~((g(f m))=n)).
intro Q.
rewrite<- Q in UU.
get R3 R4 R5.
Abort.



