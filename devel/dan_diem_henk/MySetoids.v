
(* Two requests, a small one and a less small one.*)
(*The next uni (universe) is the disjoint union of all Sets*)

Inductive uni:Type:=
          InU: forall A:Set, forall a:A, uni.

Variable A:Set.

Definition InA := (InU A).
Coercion InA : A >-> uni.

(* This works. But
Coercion (InU A) : A>-> uni.
does not. Possible to repair?*)

(* I would like that 
Coercion InU (B:Set) : B >-> uni.
works. Possible?*)

(* No need to read on, unless you want to see what I want to experiment with *)

(* Changing a:A, a judgement, into (InU a[:]A), an assertion *)

Definition isel : uni->Set->Prop.
intros c C.
destruct c.
exact (C=A0).
Defined.

Infix "[:]" := isel (at level 80).

Variable B:Set.
Variable a:A.

Axiom a0 : (A=B). 


Lemma a1 : (a[:]A).
simpl.
reflexivity.
Qed.

Lemma a2 : (a[:]B).
simpl.
rewrite (a0).
reflexivity.
Qed.

Require Export Arith.

Inductive uni2 :Type:=
  InUE: forall A:Set, forall a:A, uni2.

Definition isel2 : uni2->Set->Prop.
intros a A.
destruct a.
exact (A=A0).
Defined.

Infix "[:]" := isel (at level 80).

Print isel.

Variable A B:Set.
Variable a b: A.
Axiom a12 : (A=B).

Check (InUE nat).

Definition Innat := (InUE nat).

Coercion Innat : nat >-> uni2.

(* Coercion (InUE nat):nat>-> uni2.*)

Axiom a20 : (nat=B).

pwd
Lemma a21 : 1[:]nat.
simpl.
reflexivity.
Qed.


(* Coercion InUE (C:Set):C >-> uni2. *)

Lemma a14 : (InUE A a)[:]A.
simpl.
reflexivity.
Qed.

Lemma a15 : (InUE A a)[:]B.
(* exact a14 does not work *)
simpl.
assert (A=B).
exact a12.
rewrite H.
reflexivity.
Qed.


Lemma A16 : forall z:uni2,exists C:Set, z[:]C.
intros.
destruct z.
exists A0.
simpl.
reflexivity.
Save.

Print A16.

(*******************************************************)



Inductive uni : Type :=
   InU : forall A:Set, uni.


Inductive uni3 :Type:=
  InUe: forall A:Set, forall a:A, uni3
  | InUs : Set-> uni3.

Definition undo : uni -> Set:=
fun A : uni => match A with
                      | InU A0 => A0
                      end.


Definition shift :uni2->uni.
intro A.
destruct A.
exact (InU A).
Save.

Print shift.



Lemma s1:forall A:uni,((InU(undo A))=A).
intro A.
unfold undo.
destruct A.
reflexivity.
Save.

Lemma s2:forall A:Set, ((undo(InU A))=A).
intro A.
simpl.
reflexivity.
Save.

Definition Nat:uni:= InU nat.

Inductive Prod (A B :Set): Set:=
       pair : A->B->(Prod A B).

Definition UProd (A B:uni): uni:=
InU(Prod (undo A)(undo B)).

Variable A B:uni.







Definition UDProd (A:uni)(f:(undo A)->uni):uni.
intros A f.
exact (InU(forall x:(undo A), ((undo(f x))))).
Qed.

Set Implicit Arguments.

Definition set:=uni->Prop.
Definition p_pred:=uni->Prop.
Definition pred(A:set) (P:p_pred):=forall x,(P x)->(A x).
Definition p_rel:=uni->uni->Prop.
Definition rel(A B:set)(R:p_rel):=forall x y,(R x y)->(A x)/\(B y).

Definition intersection (A B:set):=fun x=>(A x)/\(B x).
Infix "[^]" := intersection (at level 60, left associativity).
Definition union (A B:set):=fun x=>(A x)\/(B x).
Infix "[v]" := union (at level 60, left associativity).
Definition C (A: set):=fun x=>~(A x).

Definition reflexive (A:set)(R:p_rel):=forall x:uni,(A x)->(R x x).
Definition transitive (A:set)(R:p_rel):=forall x y z, (A x)->(A y)->(A z)->(R x y)->(R y z)->(R x z).
Definition symmetric (A:set)(R:p_rel):=forall x y, (A x)->(A y)->(R x y)->(R y x).
Definition equivalence (A:set)(R:p_rel):= (rel A A R)/\(transitive A R)/\
                                          (reflexive A R)/\(symmetric A R).

Record psetoid : Type := 
  {s_crr   :> set;
   s_rel   :  p_rel}. 

Definition Setoid (S:psetoid):=(equivalence (s_crr S) (s_rel S)).

Definition set2psetoid (A:set): psetoid :=
Build_psetoid A (fun x y:uni=>(A x)/\(x=y)). 

Lemma d1 : forall A, Setoid (set2psetoid A).
intros.
unfold Setoid.
split.
simpl.
unfold rel.
intros.
elim H; intros.
split.
assumption.
rewrite<- H1; assumption.

split.
simpl.
unfold transitive.
intros.
intuition.
rewrite H5.
intuition.

intuition.
unfold reflexive.
unfold set2psetoid.
simpl.
intros.
intuition.

unfold symmetric.
simpl.
intros.
intuition.
Save.

Definition func (A B:set):=fun f:(uni->uni)=>forall x,(A x)->(B(f x)).

Definition Setoidfunc (S T:psetoid)(f:uni->uni):= (func S T).

Definition subsetoid (S:psetoid) (P:p_pred):=(pred S P)/\
forall s t,(P s)->(s_rel S s t)->(P t).

Definition relon (A:set)(R:p_rel):=(rel A A R).

Definition s_restr (A:set)(P:p_pred) (x:uni):=((A[^]P) x).
Definition r_restr (A:set)(R:p_rel)(P:p_pred):=
fun x y:uni=>(P x)/\(P y)/\(R x y).

Infix "[|]" := s_restr (at level 60).
Notation "A R [||] P":= (r_restr A R P) (at level 60). 

Definition subset (A B:set):=forall x,(A x)->(B x).
Infix "[C]" :=subset (at level 60).

Lemma d3: forall (A P:set)(R:p_rel),(P[C]A)->(relon A R)->
(relon (A[|] P)(r_restr A R P)).
intros.
unfold relon.
unfold rel.
intros.
unfold s_restr.
unfold intersection.
unfold r_restr in H1.
intuition.
Save.

Definition ps_restr (S:psetoid)(P:p_pred):=
(Build_psetoid (S[|] P) (*(S (s_rel S)[||] P)).*)
(r_restr S (s_rel S) P)). 
(* Bug? [||] cannot be used*)

Infix "|" := ps_restr (at level 80).


Record RSetoid :Type:=
{rs_crr :>psetoid;
pr:(Setoid rs_crr)}.

Record RsubSetoid (S:RSetoid):Type:=
{RsubS : >p_pred;
prRsub:(subsetoid S RsubS)}.



Lemma d2:forall (S:RSetoid)(P:RsubSetoid S),(Setoid (S | P)).
Proof.
intros.
unfold Setoid.
split.
simpl.
unfold rel.
intros.
unfold intersection.
unfold Setoid in H.
destruct P.
unfold subsetoid in prRsub0.
unfold s_restr.
split.
unfold intersection.
split.
unfold r_restr in H.
intuition.
unfold s_rel in H2.



split.
unfold transitive.
unfold rel. 
intros.

intros.
intuition.
unfold Setoid in H.
unfold equivalence in H.
intuition. simpl.
simpl in H2.
simpl in H3.
unfold r_restr.
unfold r_restr in H2.
unfold r_restr in H3.
intuition.
simpl in H1.
unfold s_restr in H1.
unfold intersection in H1.
intuition.
unfold s_restr in H3.
unfold intersection in H3.
intuition.
unfold transitive in H.

apply (H x y z).

simpl in H1.
unfold s_restr in H1.
unfold intersection in H1.
intuition.
unfold s_restr in H2.
unfold intersection in H2.
intuition.
unfold s_restr in H3.
unfold intersection in H3.
intuition.
unfold s_rel in H4.
unfold r_restr in H4.
elim H4; intros.elim H10; intros.
apply H12.

unfold s_rel in H5.
unfold r_restr in H5.
elim H5; intros. elim H10; intros.
apply H12.

split.
simpl.
unfold reflexive.
split.
unfold s_restr in H1.
unfold intersection in H1.
intuition.
split.
unfold s_restr in H1.
unfold intersection in H1.
intuition.
unfold Setoid in H.
unfold equivalence in H.
intuition.
unfold reflexive in H3.
apply H3.
unfold s_restr in H1.
unfold intersection in H1.
intuition.

unfold symmetric.
simpl. 
intros.
unfold Setoid in H.
unfold equivalence in H.
unfold symmetric in H.
intuition.

unfold subsetoid in H0.
unfold r_restr.
unfold r_restr in H3.
intuition.
Save.

(**)











Definition Relation := A->A->Prop.
Definition Reflexive := Treflexive.
Definition Symmetric := Tsymmetric.
Definition Transitive := Ttransitive.
Definition Equiv := Tequiv.

End preliminaries.


(* use global def of implicits within prelim file *) 
Implicit Arguments Reflexive [A].
Implicit Arguments Symmetric [A].
Implicit Arguments Transitive [A].
Implicit Arguments Equiv [A].

Record is_Setoid (A : Type) (eq : Relation A) : CProp := 
  {ax_eq_reflexive  : Reflexive eq;
   ax_eq_symmetric  : Symmetric eq;
   ax_eq_transitive : Transitive eq}.

Record Setoid : Type := 
  {s_crr   :> Type;
   s_eq    :  Relation s_crr;
   s_proof :  is_Setoid s_crr s_eq}.

Implicit Types S  : Setoid.

Notation "x [=] y" := 
  (s_eq _ x y) (at level 70, no associativity).

Definition s_neq S : Relation S := 
  fun x y : S => ~ x [=] y.

Notation "x [~=] y" := 
  (s_neq _ x y) (at level 70, no associativity).

(** ** Setoid axioms
We want concrete lemmas that state the axiomatic properties of a setoid.
%\begin{convention}%
Let [S] be a setoid.
%\end{convention}%
*)

Section Setoid_axioms. 

Variable S : Setoid.

Lemma Setoid_is_Setoid : is_Setoid S (s_eq S).
Proof.
exact (s_proof S).
Qed.

Lemma eq_reflexive : Reflexive (s_eq S).
Proof.
exact (ax_eq_reflexive S (s_eq S) (s_proof S)).
Qed.

Lemma eq_symmetric : Symmetric (s_eq S).
Proof.
exact (ax_eq_symmetric S (s_eq S) (s_proof S)).
Qed.

Lemma eq_transitive : Transitive (s_eq S).
Proof.
exact (ax_eq_transitive S (s_eq S) (s_proof S)).
Qed.

End Setoid_axioms.

(** [Type2Setoid T] builds a setoid out of an arbitrary type [T] 
where the equivalence is taken to be Coq's Leibniz equality ([eq]).
*)

Definition Type2Setoid (T : Type) : Setoid :=
  Build_Setoid T (eq (A:=T)) 
    (Build_is_Setoid T (eq (A:=T))  
      (refl_equal (A:=T)) 
      (sym_equal (A:=T))
      (trans_equal (A:=T))).

(** **Setoid basics%\label{section:setoid-basics}%
%\begin{convention}% Let [S] be a setoid.
%\end{convention}%
*)

Section Setoid_basics.

Variable S : Setoid.

(**
In `there exists a unique [a:S] such that %\ldots%#...#', 
we now mean unique with respect to the setoid equality. 
We use [ex_unq] to denote unique existence.
*)

Definition ex_unq (P : S -> CProp) := 
  {x : S | forall y : S, P y -> x [=] y | P x}.

Lemma eq_wdl : forall x y z : S, x [=] y -> x [=] z -> z [=] y.
intros x y z H H0.
apply eq_transitive with (2:=H).
apply eq_symmetric with (1:=H0).
Qed.

Lemma eq_imp_not_neq : forall x y : S, x [=] y -> ~ x [~=] y.
Proof.
intros x y H H0.
exact (H0 H).
Qed.

End Setoid_basics.

Section product_setoid.
(** **The product of setoids *)

Definition prod_eq (A B : Setoid) : (Relation (prodT A B)) :=
  fun p q => fstT p [=] fstT q /\ sndT p [=] sndT q.

Lemma prod_setoid_is_Setoid : 
  forall A B : Setoid,
  is_Setoid (prodT A B) (prod_eq A B).
Proof.
intros A B.
split; do 2 red.
destruct x; simpl.
split; apply eq_reflexive.
destruct x; destruct y; simpl.
intros [ H H0 ]; split; apply eq_symmetric; [ exact H | exact H0 ].
destruct x; destruct y; destruct z; simpl.
intros [ H H0 ] [ H1 H2 ]; split.
apply eq_transitive with (1:=H) (2:=H1).
apply eq_transitive with (1:=H0) (2:=H2).
Qed.

Definition ProdSetoid (A B : Setoid) : Setoid := 
  Build_Setoid (prodT A B) (prod_eq A B) (prod_setoid_is_Setoid A B).

End product_setoid.

Infix "[*]" := ProdSetoid (at level 60, left associativity).

Section union_setoid.
(** The union of setoids *)

(* This should be moved, perhaps to CLogic.v *)

Inductive TSum (A B : Type) : Type :=
  | Tinleft : A -> TSum A B
  | Tinright : B -> TSum A B.

Definition union_eq (A B:Setoid): (Relation (TSum A B)):=
   fun x y : (TSum A B) => 
     match x, y with 
       Tinleft a, Tinleft b => a [=] b
     | Tinright a, Tinright b => a [=] b
     | _, _ => False
     end.

Lemma unionsetoid_is_Setoid : 
   forall A B:Setoid, (is_Setoid (TSum A B) (union_eq A B)).
intros A B.
apply (Build_is_Setoid _ (union_eq A B)).
intro x.
destruct x; simpl; apply eq_reflexive.
intros x y.
destruct x; destruct y; simpl; trivial.
apply eq_symmetric.
apply eq_symmetric.
intros x y z.
destruct x; destruct y; destruct z; simpl; trivial.
intros.
apply (eq_transitive _ _ _ _ H H0).
intro H; elim H.
intro H; elim H.
intros H H0.
apply (eq_transitive _ _ _ _ H H0).
Qed.

Definition UnionSetoid (A B:Setoid) : Setoid :=
  (Build_Setoid (TSum A B) (union_eq A B)  (unionsetoid_is_Setoid A B)).

End union_setoid.

Infix "[+]" := UnionSetoid (at level 60, left associativity).

Variables A B : Setoid.

Check A [+] B.

Implicit Arguments ex_unq [S].

Hint Resolve eq_reflexive: algebra_r.
Hint Resolve eq_symmetric : algebra_s.

Declare Left Step eq_wdl.
Declare Right Step eq_transitive.

(** **Relations and predicates
Here we define the notions of well-definedness 
on predicates and relations.

%\begin{convention}% Let [S] be a setoid.
%\end{convention}%

%\begin{nameconvention}%
- ``well-defined'' is abbreviated to [well_def] (or [wd]).
%\end{nameconvention}%
*)

Section Setoid_relations_and_predicates.

Variable S : Setoid.

(** ***Predicates

At this stage, we consider [CProp]- and [Prop]-valued predicates on setoids.

%\begin{convention}% Let [P] be a predicate on (the carrier of) [S].
%\end{convention}%
*)

Section SetoidPredicates.

Variable P : S -> Prop.

Definition pred_wd (P : S -> Prop) : Prop := 
  forall x y : S, P x -> x [=] y -> P y.

Definition cpred_wd (P : S -> CProp) : CProp :=
  forall x y : S, P x -> x [=] y -> P y.

End SetoidPredicates.

Record wd_pred : Type :=
  {wdp_pred     :> S -> Prop;
   wdp_well_def :  pred_wd wdp_pred}.

Record Setoid_predicate : Type := 
 {sp_pred :> S -> Prop;
  sp_wd   :  pred_wd sp_pred}.

(** ***Relations
%\begin{convention}%
Let [R] be a relation on (the carrier of) [S].
%\end{convention}% *)

Section SetoidRelations.

Variable R : S -> S -> Prop.

Definition rel_wdr : Prop := 
  forall x y z : S, R x y -> y [=] z -> R x z.

Definition rel_wdl : Prop := 
  forall x y z : S, R x y -> x [=] z -> R z y.

End SetoidRelations.

(** ***Definition of a setoid relation
The type of relations over a setoid.  *)

Record Setoid_relation : Type := 
  {sr_rel    :> S -> S -> Prop;
   sr_wdr    :  rel_wdr sr_rel;
   sr_wdl    :  rel_wdl sr_rel}.

End Setoid_relations_and_predicates.

(** **Functions between setoids
Such functions must preserve the setoid equality, 
i.e.%\% be well-defined.
For every arity this has to be defined separately.
%\begin{convention}%
Let [S1], [S2] and [S3] be setoids.
%\end{convention}%

First we consider unary functions.  *)

Section Setoid_functions.

Variables S1 S2 S3 : Setoid.

Section unary_functions.

(**
In the following two definitions,
[f] is a function from (the carrier of) [S1] to
(the carrier of) [S2].  *)

Variable f : S1 -> S2.

Definition fun_wd : Prop := 
  forall x y : S1, x [=] y -> f x [=] f y.

End unary_functions.

Record Setoid_fun : Type := 
  {sf_fun :> S1 -> S2;
   sf_wd  :  fun_wd sf_fun}.

Definition Const_Setoid_fun : S2 -> Setoid_fun.
intro c.
apply (Build_Setoid_fun (fun _ => c)).
intros x y H.
apply eq_reflexive.
Defined.

Section binary_functions.

(**
Now we consider binary functions.
In the following two definitions,
[f] is a function from [S1] and [S2] to [S3].
*)

Variable f : S1 -> S2 -> S3.

Definition bin_fun_wd : Prop := 
  forall x1 x2 y1 y2,
  x1 [=] x2 -> y1 [=] y2 -> f x1 y1 [=] f x2 y2.

End binary_functions.

Record Setoid_bin_fun : Type := 
 {sbf_fun :> S1 -> S2 -> S3;
  sbf_wd  : bin_fun_wd sbf_fun}.

End Setoid_functions.

Hint Resolve sf_wd : algebra_c.

Implicit Arguments fun_wd [S1 S2].

(** **The unary and binary (inner) operations on a setoid
An operation is a function with domain(s) and co-domain equal.

%\begin{nameconvention}%
The word ``unary operation'' is abbreviated to [un_op];
``binary operation'' is abbreviated to [bin_op].
%\end{nameconvention}%

%\begin{convention}%
Let [S] be a setoid.
%\end{convention}%
*)

Section setoid_inner_ops.

Variable S : Setoid.

(** Properties of binary operations *)

Definition commutes (f : S -> S -> S) : Prop := 
  forall x y : S, f x y [=] f y x.

Definition associative (f : S -> S -> S) : Prop := 
  forall x y z : S, f x (f y z) [=] f (f x y) z.

(** Well-defined unary operations on a setoid.  *)

Definition un_op_wd := fun_wd (S1:=S) (S2:=S).

Definition Setoid_un_op : Type := Setoid_fun S S.

Definition Build_Setoid_un_op := Build_Setoid_fun S S.

Definition s_un_op_wd := sf_wd S S.

Lemma id_wd : un_op_wd (fun x : S => x).
Proof.
exact (fun x y H => H).
Qed.

Definition id_un_op := 
  Build_Setoid_un_op (fun x : S => x) id_wd.

(* begin hide *)
Identity Coercion un_op_fun : Setoid_un_op >-> Setoid_fun.
(* end hide *)

(** Well-defined binary operations on a setoid.  *)

Definition bin_op_wd := bin_fun_wd S S S.

Definition Setoid_bin_op : Type := Setoid_bin_fun S S S.

Definition Build_Setoid_bin_op := Build_Setoid_bin_fun S S S.

Definition s_bin_op_wd := sbf_wd S S S.

(* begin hide *)
Identity Coercion bin_op_bin_fun : Setoid_bin_op >-> Setoid_bin_fun.
(* end hide *)

Variable op : Setoid_bin_op.
Variable c : S.

Lemma bin_op_is_wd_un_op_lft : un_op_wd (fun x => op x c).
Proof.
intros x y H.
apply s_bin_op_wd.
exact H.
apply eq_reflexive.
Qed.

Lemma bin_op_is_wd_un_op_rht : un_op_wd (fun x => op c x).
Proof.
intros x y H. 
apply s_bin_op_wd. 
apply eq_reflexive. 
exact H.
Qed.

Definition bin_op2un_op_rht : Setoid_un_op :=
  Build_Setoid_un_op (fun x => op c x) bin_op_is_wd_un_op_rht.

Definition bin_op2un_op_lft : Setoid_un_op :=
  Build_Setoid_un_op (fun x => op x c) bin_op_is_wd_un_op_lft.

End setoid_inner_ops.

Implicit Arguments commutes [S].
Implicit Arguments associative [S].

Hint Resolve s_bin_op_wd s_un_op_wd : algebra_c.

(** **The binary outer operations on a setoid
%\begin{convention}%
Let [S1] and [S2] be setoids.
%\end{convention}%
*)

Section setoid_outer_ops.

Variables S1 S2 : Setoid.

(**
Well-defined outer operations on a setoid.
*)

Definition outer_op_well_def := bin_fun_wd S1 S2 S2.

Definition Setoid_outer_op : Type := Setoid_bin_fun S1 S2 S2.
Definition Build_Setoid_outer_op := Build_Setoid_bin_fun S1 S2 S2.
Definition soo_wd := sbf_wd S1 S2 S2.

(* begin hide *)
Identity Coercion outer_op_bin_fun : Setoid_outer_op >-> Setoid_bin_fun.
(* end hide *)

End setoid_outer_ops.

Hint Resolve soo_wd : algebra_c.

(** **Subsetoids
%\begin{convention}%
Let [S] be a setoid, and [P] a predicate on the carrier of [S].
%\end{convention}%
*)

Section SubSetoids.

Variable S : Setoid.
Variable P : S -> Prop.

Record subsetoid_crr : Type := 
 {ss_elt :> S;
  ss_prf  :  P ss_elt}.

(** Though [ss_elt] is declared as a coercion, it does not satisfy the
uniform inheritance condition and will not be inserted.  However it will
also not be printed, which is handy.
*)

Definition restrict_relation (R : Relation S) : Relation subsetoid_crr :=
  fun a b =>
  match a, b with
  | Build_subsetoid_crr x _, Build_subsetoid_crr y _ => R x y
  end.

Definition subsetoid_eq : Relation subsetoid_crr :=
  restrict_relation (s_eq S).

Lemma subsetoid_is_Setoid : is_Setoid subsetoid_crr subsetoid_eq.
Proof.
split; do 2 red.
destruct x; simpl.
apply eq_reflexive.
destruct x; destruct y; simpl.
intro H; apply eq_symmetric with (1:=H).
destruct x; destruct y; destruct z; simpl.
intros H1 H2; apply eq_transitive with (1:=H1) (2:=H2).
Qed.

Definition Build_SubSetoid : Setoid := 
  Build_Setoid subsetoid_crr subsetoid_eq subsetoid_is_Setoid.

Lemma ss_elt_wd :
  forall (e1 e2 : subsetoid_crr),
  (s_eq Build_SubSetoid e1 e2) -> (* if we put e1 [=] e2, it gets (ofcourse?) coerced to (ss_elt e1) [=] (ss_elt e2) *)  
  ss_elt e1 [=] ss_elt e2.
Proof.
intros e1 e2 H.
destruct e1 as [ e1_e e1_p ].
destruct e2 as [ e2_e e2_p ].
simpl in *|-* .
exact H.
Qed.

Lemma ss_elt_inj :
  forall (e1 e2 : subsetoid_crr),
  ss_elt e1 [=] ss_elt e2 ->
  s_eq Build_SubSetoid e1 e2. 
Proof.
intros e1 e2 H.
Set Printing Coercions.
destruct e1 as [ e1_e e1_p ].
destruct e2 as [ e2_e e2_p ].
simpl in *|-* .
exact H.
Qed.

(** ***Subsetoid unary operations
%\begin{convention}%
Let [f] be a unary setoid operation on [S].
%\end{convention}%
*)

Section SubSetoid_unary_operations.

Variable f : Setoid_un_op S.

Definition un_op_pres_pred : CProp := 
  forall x : S, P x -> P (f x).

(**
%\begin{convention}%
Assume [pr:un_op_pres_pred].
%\end{convention}% *)

Variable pr : un_op_pres_pred.

Definition restr_un_op (a : subsetoid_crr) : subsetoid_crr :=
  match a with
  | Build_subsetoid_crr x p => Build_subsetoid_crr (f x) (pr x p)
  end.

Lemma restr_un_op_wd : un_op_wd Build_SubSetoid restr_un_op.
Proof.
red.
red.
destruct x; destruct y; simpl; intro H.
apply s_un_op_wd with (1:=H).
Qed.

Definition Build_SubSetoid_un_op : Setoid_un_op Build_SubSetoid :=
  Build_Setoid_un_op Build_SubSetoid restr_un_op restr_un_op_wd.

End SubSetoid_unary_operations.

(** ***Subsetoid binary operations
%\begin{convention}%
Let [f] be a binary setoid operation on [S].
%\end{convention}%
*)

Section SubSetoid_binary_operations.

Variable f : Setoid_bin_op S.

Definition bin_op_pres_pred : CProp := 
  forall x y : S, P x -> P y -> P (f x y).

(**
%\begin{convention}%
Assume [bin_op_pres_pred].
%\end{convention}%
*)

Variable pr : bin_op_pres_pred.

Definition restr_bin_op (a b : subsetoid_crr) : subsetoid_crr :=
  match a, b with
  | Build_subsetoid_crr x p, Build_subsetoid_crr y q =>
      Build_subsetoid_crr (f x y) (pr x y p q)
  end.

Lemma restr_bin_op_wd : bin_op_wd Build_SubSetoid restr_bin_op.
Proof.
red.
red.
destruct x1; destruct x2; destruct y1; destruct y2; simpl; intros H H0.
apply s_bin_op_wd with (1:=H) (2:=H0).
Qed.

Definition Build_SubSetoid_bin_op : Setoid_bin_op Build_SubSetoid :=
  Build_Setoid_bin_op Build_SubSetoid restr_bin_op restr_bin_op_wd.

Lemma restr_f_assoc : 
  associative f -> associative Build_SubSetoid_bin_op.
Proof.
intro H.
red.
intros.
simpl.
destruct x; destruct y; destruct z; simpl.
apply H.
Qed.

End SubSetoid_binary_operations.

End SubSetoids.

Implicit Arguments ss_elt [S P].
Implicit Arguments ss_prf [S P].

(* begin hide *)
Ltac Step_final x := apply eq_transitive with x; Algebra.
(* end hide *)

Tactic Notation "Step_final" constr(c) :=  Step_final c.
