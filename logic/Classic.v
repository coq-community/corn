(*
Copyright © 2007-2008 Russell O’Connor

Permission is hereby granted, free of charge, to any person obtaining a copy of
this proof and associated documentation files (the "Proof"), to deal in
the Proof without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Proof, and to permit persons to whom the Proof is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Proof.

THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
*)

Require Import List.

(**
* Classical Logic
This section introduces the classical logic connectives, "classical or"
and "classical exists" through their double negation translation.
Induction principles are given that allow you to destruct these formulas
as you would their constructive counter parts, so long as the conclusion
is double negataion stable. 

No classical axioms are assumed.
*)

(**
** Classical or
*)

Section ClassicOr.

Definition orC (P Q:Prop) := ~((~P)/\(~Q)).

Lemma orWeaken : forall P Q, ({P}+{Q}) -> orC P Q.
Proof.
unfold orC.
tauto.
Qed.

Lemma orC_ind : forall (P Q G:Prop),
 (~~G -> G) -> (P -> G) -> (Q -> G) -> (orC P Q) -> G.
Proof.
unfold orC.
tauto.
Qed.

Lemma orC_stable : forall P Q, ~~(orC P Q) -> orC P Q.
Proof.
unfold orC.
auto.
Qed.

End ClassicOr.

(**
** Classical Existential
*)
Section ClassicExists.

Variable A : Type.
Variable P : A->Prop.

Definition existsC : Prop :=
 ~forall x:A, ~P x.

Lemma existsWeaken : (exists x:A, P x) -> existsC.
Proof.
intros [x Hx] H.
apply (H x).
assumption.
Qed.

Lemma existsC_ind : forall (Q:Prop),
 (~~Q -> Q) -> (forall x:A, P x -> Q) -> existsC -> Q.
Proof.
intros Q HQ H ex.
apply HQ.
intros Z.
apply ex.
intros x Hx.
apply Z.
apply H with x.
assumption.
Qed.

Lemma existsC_stable : ~~existsC -> existsC.
Proof.
unfold existsC.
auto.
Qed.

End ClassicExists.

(**
** Pidgeon Hole Principle
Here we show the classical result of the pigenon hole principle using the
classical quantifiers.

Given a finite list of elements and a relation P(n,x) saying when items from
the list are selected, there classically exists an item that is selected a
classically infinite number of times.
*)

Lemma infinitePidgeonHolePrinicple : 
 forall (X:Type) (l:list X) (P:nat -> X -> Prop),
 (forall n, existsC X (fun x => ~~In x l /\ P n x)) ->
 existsC X (fun x => In x l /\ forall n, existsC nat (fun m => (n <= m)%nat /\ (P m x))).
Proof.
intros X l.
induction l;
 intros P HP G.
 apply (HP O).
 intros x [Hx _].
 auto with *.
apply (G a).
split; auto with *.
intros n Hn.
set (P':= fun m => P (m+n)%nat).
assert (HP' : forall m : nat, existsC X (fun x => ~~In x l /\ P' m x)).
 intros m.
 unfold P'.
 destruct (HP (m + n)%nat) as [HG | y [Hy0 Hy1]] using existsC_ind.
  apply existsC_stable; auto.
 apply existsWeaken.
 exists y.
 split; auto.
 revert Hy0.
 cut (In y (a  :: l) -> In y l);[tauto|].
 intros Hy0.
 destruct Hy0; auto.
 elim (Hn (m + n)%nat).
 rewrite H.
 auto with *.
destruct (IHl P' HP') as [HG | x [Hx0 Hx1]] using existsC_ind.
 tauto.
apply (G x).
split; auto with *.
unfold P' in Hx1.
intros n0.
destruct (Hx1 n0) as [HG | m [Hm0 Hm1]] using existsC_ind.
 apply existsC_stable; auto.
apply existsWeaken.
exists (m + n)%nat.
split; auto.
auto with *.
Qed.

(**
This weaker version of the pidgen hole principle uses a function to select
elements from a list instead of a releation.  It may be more convienent to
use at times.
*)
Lemma infinitePidgeonHolePrinicpleB : 
 forall (X:Type) (l:list X) (f:nat -> X),
 (forall n, In (f n) l) ->
 existsC X (fun x => In x l /\ forall n, existsC nat (fun m => (n <= m)%nat /\ (f m)=x)).
Proof.
intros X l f H.
apply infinitePidgeonHolePrinicple.
intros n.
apply existsWeaken.
exists (f n).
auto with *.
Qed.

