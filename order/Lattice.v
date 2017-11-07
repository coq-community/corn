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

Require Import Coq.Setoids.Setoid.
Require Export CoRN.order.SemiLattice.

Local Open Scope po_scope.

(**
* Lattice
A lattice is a semilattice with a join operation such that it forms
a semilattice with in the dual partial order.
*)
Record Lattice : Type :=
{ sl :> SemiLattice
; join : sl -> sl -> sl
; l_proof : is_SemiLattice (Dual sl) join
}.
(* begin hide *)
Implicit Arguments join [l].
(* end hide*)
Section Join.

Variable X : Lattice.

Definition makeLattice (po:PartialOrder) (meet join :  po -> po -> po) p1 p2 p3 p4 p5 p6 :=
@Build_Lattice (@makeSemiLattice po meet p1 p2 p3) join
(@Build_is_SemiLattice (Dual po) join p4 p5 p6).

(** The axioms of a join lattice. *)
Lemma join_ub_l : forall x y : X, x <= join x y.
Proof (sl_meet_lb_l _ _ (l_proof X)).

Lemma join_ub_r : forall x y : X, y <= join x y.
Proof (sl_meet_lb_r _ _ (l_proof X)).

Lemma join_lub : forall x y z : X, x <= z -> y <= z -> join x y <= z.
Proof (sl_meet_glb _ _ (l_proof X)).

(**
** Dual Latice
The dual of a lattice is a lattice. *)
Definition Dual : Lattice :=
@makeLattice (Dual X) (@join X) (@meet X)
 join_ub_l
 join_ub_r
 join_lub
 (@meet_lb_l X)
 (@meet_lb_r X)
 (@meet_glb X).

(** All the lemmas about meet semilattices hold for join. *)
Lemma join_comm :  forall x y:X, join x y == join y x.
Proof meet_comm Dual.

Lemma join_assoc : forall x y z:X, join x (join y z) == join (join x y) z.
Proof meet_assoc Dual.

Lemma join_idem : forall x:X, join x x == x.
Proof meet_idem Dual.

Lemma le_join_l : forall x y : X, y <= x <-> join x y == x.
Proof le_meet_l Dual.

Lemma le_join_r : forall x y : X, x <= y <-> join x y == y.
Proof le_meet_r Dual.

Lemma join_monotone_r : forall a : X, monotone X (join a).
Proof meet_monotone_r Dual.

Lemma join_monotone_l : forall a : X, monotone X (fun x => join x a).
Proof meet_monotone_l Dual.

Lemma join_le_compat : forall w x y z : X, w<=y -> x<=z -> join w x <= join y z.
Proof fun w x y z => meet_le_compat Dual y z w x.

End Join.
(* begin hide *)
Add Parametric Morphism X : (@join X) with signature (@st_eq (sl X)) ==> (@st_eq X) ==> (@st_eq X) as join_compat.
Proof.
 exact (meet_compat (Dual X)).
Qed.
(* end hide *)
Section MeetJoin.

Variable X : Lattice.
(** Lemma about how meet and join interact. *)
Lemma meet_join_absorb_l_l : forall x y:X, meet x (join x y) == x.
Proof.
 intros.
 apply le_antisym.
  apply meet_lb_l.
 apply meet_glb.
  apply le_refl.
 apply join_ub_l.
Qed.

Lemma meet_join_absorb_l_r : forall x y:X, meet x (join y x) == x.
Proof.
 intros.
 rewrite -> (join_comm X).
 apply meet_join_absorb_l_l.
Qed.

Lemma meet_join_absorb_r_l : forall x y:X, meet (join x y) x == x.
Proof.
 intros.
 rewrite -> (meet_comm X).
 apply meet_join_absorb_l_l.
Qed.

Lemma meet_join_absorb_r_r : forall x y:X, meet (join y x) x == x.
Proof.
 intros.
 rewrite -> (join_comm X).
 apply meet_join_absorb_r_l.
Qed.

Lemma meet_join_eq : forall x y : X, meet x y == join x y -> x == y.
Proof.
 intros.
 rewrite <- (meet_join_absorb_l_l y x).
 rewrite -> (join_comm X y x).
 rewrite <- H.
 rewrite -> (meet_comm X x y).
 rewrite -> (meet_assoc X).
 rewrite -> (meet_idem X).
 set (RHS := meet y x).
 rewrite <- (meet_join_absorb_l_l x y).
 rewrite <- H.
 rewrite -> (meet_assoc X).
 rewrite -> (meet_idem X).
 rewrite -> (meet_comm X).
 reflexivity.
Qed.

End MeetJoin.

Section JoinMeet.

Variable X : Lattice.
(** The dual of the previous laws holds. *)
Lemma join_meet_absorb_l_l : forall x y:X, join x (meet x y) == x.
Proof meet_join_absorb_l_l (Dual X).

Lemma join_meet_absorb_l_r : forall x y:X, join x (meet y x) == x.
Proof meet_join_absorb_l_r (Dual X).

Lemma join_meet_absorb_r_l : forall x y:X, join (meet x y) x == x.
Proof meet_join_absorb_r_l (Dual X).

Lemma join_meet_absorb_r_r : forall x y:X, join (meet y x) x == x.
Proof meet_join_absorb_r_r (Dual X).

End JoinMeet.
