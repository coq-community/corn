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

Require Export BinPos.

(**
* Lazy Nat
This s a lazified version of the natural number that allow one to delay
computation until demanded.  This is useful for large natural numbers
(often upper bounds) where only a small number of terms are actually need
for compuation.
*)
Inductive LazyNat : Set :=
| LazyO : LazyNat
| LazyS : (unit -> LazyNat) -> LazyNat.

(**
** Successor
*)
Definition lazyS (n:LazyNat) : LazyNat := LazyS (fun _ => n).

(** Convert a nat to a lazy nat *)
Fixpoint LazifyNat (n : nat) {struct n} : LazyNat :=
  match n with
  | O => LazyO
  | S p => LazyS (fun _ => (LazifyNat p))
  end.

(**
** Predecessor
*)
Definition LazyPred (n:LazyNat) : LazyNat :=
match n with
| LazyO => LazyO
| LazyS n' => (n' tt)
end.

Lemma LazifyPred : forall n, LazifyNat (pred n) = LazyPred (LazifyNat n).
Proof.
 induction n; reflexivity.
Qed.

(**
** Addition
*)
Fixpoint LazyPlus (n m : LazyNat) {struct n} : LazyNat :=
  match n with
  | LazyO => m
  | LazyS p => LazyS (fun _ => LazyPlus (p tt) m)
  end.

Lemma LazifyPlus : forall n m, (LazifyNat (n + m) = LazyPlus (LazifyNat n) (LazifyNat m))%nat.
Proof.
 induction n.
  reflexivity.
 simpl.
 intros m.
 rewrite IHn.
 reflexivity.
Qed.

(**
** Multiplication
*)
Fixpoint Pmult_LazyNat (x:positive) (pow2:LazyNat) {struct x} : LazyNat :=
  match x with
    | xI x' => (LazyPlus pow2 (Pmult_LazyNat x' (LazyPlus pow2 pow2)))%nat
    | xO x' => Pmult_LazyNat x' (LazyPlus pow2 pow2)%nat
    | xH => pow2
  end.

Lemma LazifyPmult_LazyNat : forall x pow2, LazifyNat (Pmult_nat x pow2) = Pmult_LazyNat x (LazifyNat pow2).
Proof.
 induction x; simpl; intros pow2; repeat (rewrite LazifyPlus||rewrite IHx); reflexivity.
Qed.

(** Convert a positive to a lazy nat.  This is the most common way of
generating lazy nats. *)
Definition LazyNat_of_P (x:positive) := Pmult_LazyNat x (LazyS (fun _ => LazyO)).

Lemma LazifyNat_of_P : forall x, LazifyNat (nat_of_P x) = LazyNat_of_P x.
Proof.
 intros x.
 refine (LazifyPmult_LazyNat _ _).
Qed.
(* begin hide *)
Hint Rewrite <- LazifyNat_of_P LazifyPmult_LazyNat LazifyPlus LazifyPred : UnLazyNat.
(* end hide *)

Fixpoint Pplus_LazyNat (p:positive)(n:LazyNat) {struct n} : positive :=
match n with
| LazyO => p
| (LazyS n') => (Pplus_LazyNat (Psucc p) (n' tt))
end.
