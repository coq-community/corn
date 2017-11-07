(*
Copyright © 2006-2008 Russell O’Connor

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
Set Firstorder Depth 5.

Require Export CoRN.order.PartialOrder.

Local Open Scope po_scope.

(**
* SemiLattice
A (meet) semi lattice augments a partial order with a greatest lower bound
operator.
*)

(*Should I take a PartialOrder parameter, or just a type and an inequality relation? *)
Record is_SemiLattice (po : PartialOrder) (meet : po -> po -> po) : Prop :=
{ sl_meet_lb_l : forall x y, meet x y <= x (*left lower bound*)
; sl_meet_lb_r : forall x y, meet x y <= y (*right lower bound*)
; sl_meet_glb : forall x y z, z <= x -> z <= y -> z <= meet x y (*greatest lower bound *)
}.

Record SemiLattice : Type :=
{ po :> PartialOrder
; meet : po -> po -> po
; sl_proof : is_SemiLattice po meet
}.

(* begin hide *)
Implicit Arguments meet [s].

Add Parametric Morphism (X:SemiLattice) : (@meet X) with signature (@st_eq X) ==> (@st_eq X) ==> (@st_eq X)  as meet_compat.
Proof.
 assert (forall x1 x2 : X, x1 == x2 -> forall x3 x4 : X, x3 == x4 -> meet x1 x3 <= meet x2 x4).
  intros.
  revert H H0; do 2 rewrite -> equiv_le_def; intros.
  pose (le_trans X).
  destruct (sl_proof X).
  apply sl_meet_glb0; firstorder.
 intros.
 pose (Seq_sym X _ (po_st (po_proof X))).
 apply le_antisym; firstorder.
Qed.
(* end hide *)

Section Meet.

Variable X : SemiLattice.

Definition makeSemiLattice po meet p1 p2 p3 :=
@Build_SemiLattice po meet
(@Build_is_SemiLattice po meet p1 p2 p3).

(** The axioms and basic properties of a semi lattice *)
Lemma meet_lb_l : forall x y : X, meet x y <= x.
Proof (sl_meet_lb_l _ _ (sl_proof X)).

Lemma meet_lb_r : forall x y : X, meet x y <= y.
Proof (sl_meet_lb_r _ _ (sl_proof X)).

Lemma meet_glb : forall x y z : X, z <= x -> z <= y -> z <= meet x y.
Proof (sl_meet_glb _ _ (sl_proof X)).

(** commutativity of meet *)
Lemma meet_comm : forall x y:X, meet x y == meet y x.
Proof.
 assert (forall x y : X, meet x y <= meet y x).
  intros.
  destruct X.
  simpl in *.
  firstorder.
 intros; apply le_antisym; firstorder.
Qed.

(** associativity of meet *)
Lemma meet_assoc : forall x y z:X, meet x (meet y z) == meet (meet x y) z.
Proof.
 assert (forall x y z : X, meet x (meet y z) <= meet (meet x y) z).
  intros.
  apply meet_glb; [apply meet_glb|]; firstorder using meet_lb_l meet_lb_r le_trans.
 intros.
 apply le_antisym.
  apply H.
 rewrite -> meet_comm.
 rewrite -> (meet_comm x (meet y z)).
 rewrite -> (meet_comm x y).
 rewrite -> (meet_comm y z).
 apply H.
Qed.

(** idempotency of meet *)
Lemma meet_idem : forall x:X, meet x x == x.
Proof.
 intros.
 apply le_antisym; firstorder using meet_lb_l meet_glb le_refl.
Qed.

Lemma le_meet_l : forall x y : X, x <= y <-> meet x y == x.
Proof.
 intros.
 split; intros.
  apply le_antisym.
   apply meet_lb_l.
  apply meet_glb.
   apply le_refl.
  assumption.
 rewrite <- H.
 apply meet_lb_r.
Qed.

Lemma le_meet_r : forall x y : X, y <= x <-> meet x y == y.
Proof.
 intros.
 rewrite -> meet_comm.
 apply le_meet_l.
Qed.

(** monotonicity of meet *)
Lemma meet_monotone_r : forall a : X, monotone X (meet a).
Proof.
 intros.
 rewrite -> monotone_def.
 intros.
 revert H;rewrite -> le_meet_l, meet_comm; intro.
 rewrite <- H.
 rewrite -> meet_assoc.
 apply meet_lb_l.
Qed.

Lemma meet_monotone_l : forall a : X, monotone X (fun x => meet x a).
Proof.
 intros.
 assert (A:=meet_monotone_r a).
 revert A; do 2 rewrite -> monotone_def;intros.
 rewrite -> (meet_comm x), (meet_comm y);auto.
Qed.

Lemma meet_le_compat : forall w x y z : X, w<=y -> x<=z -> meet w x <= meet y z.
Proof.
 intros.
 apply le_trans with (y:=meet y x).
  firstorder using meet_monotone_l monotone_def.
 firstorder using meet_monotone_r monotone_def.
Qed.

End Meet.
