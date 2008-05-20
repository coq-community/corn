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

Require Export Complete.
Require Export Prelength.
Require Import Qmetric.
Require Import CornTac.

Set Implicit Arguments.

Open Local Scope uc_scope.

(**
* Complete Metric Space: Computable Reals (CR)
*)

Definition CR := Complete Q_as_MetricSpace.

Delimit Scope CR_scope with CR.
Bind Scope CR_scope with CR.

Definition inject_Q : Q -> CR := (@Cunit Q_as_MetricSpace).

(* begin hide *)
Add Morphism (inject_Q) with signature Qeq ==> (@ms_eq _) as inject_Q_wd.
exact (uc_wd (@Cunit Q_as_MetricSpace)).
Qed.
(* end hide *)

Notation "' x" := (inject_Q x) : CR_scope.

Notation "x == y" := (@ms_eq CR x y) (at level 70, no associativity) : CR_scope.
