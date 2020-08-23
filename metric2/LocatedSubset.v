(*
Copyright © 2020 Vincent Semeria

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

(**
* Located subsets

A subset Y : X -> Prop of a metric space X is located when its distance
function, fun x:X => d(x,Y), constructively exists. It is the generalization
to continuous spaces of the computable subsets of the natural numbers.
We cannot use the characteristic functions instead, because they are discontinuous.

When X has dimension 2, a located subset of X can be drawn on a raster,
ie a pixel grid. For each pixel, compute whether the distance of Y to
the center of the pixel is less than the size of the pixel. If so,
switch the pixel on otherwise leave it off.

With our ball-based definition of metric space, this translates as a
decidable sumbool.
*)

Require Import CoRN.model.totalorder.QposMinMax.
Require Import CoRN.metric2.Compact.

Definition LocatedSubset (X : MetricSpace) (Y : X -> Prop) : Type
:= forall (d e : Q) (x:X),
    d < e
    -> { forall y:X, Y y -> ~ball d x y } + { exists y:X, Y y /\ ball e x y }.

Lemma LocatedSubset_wd
  : forall (X : MetricSpace) (Y Z : X -> Prop),
    (forall x:X, Y x <-> Z x)
    -> LocatedSubset X Y
    -> LocatedSubset X Z.
Proof.
  intros X Y Z YeqZ Yloc d e x dlte. 
  destruct (Yloc d e x dlte) as [far|close].
  - left. intros y H.
    apply far, YeqZ, H.
  - right. destruct close as [y [yin close]].
    exists y. split. apply YeqZ, yin. exact close.
Qed.

(* A finite subset is located when the metric itself is located. *)
Fixpoint LocatedFinite (X : MetricSpace) (loc : locatedMetric X) (l : list X)
         {struct l} : LocatedSubset X (fun x => In x l).
Proof.
  destruct l as [|a l].
  - intros d e x ltde. left.
    intros y H. contradiction H.
  - intros d e x ltde.
    destruct (loc d e x a ltde).
    right. exists a. split. left; reflexivity. exact b.
    destruct (LocatedFinite X loc l d e x ltde) as [far|close].
    + left. intros y H. destruct H.
      rewrite <- H. exact n.
      apply far, H.
    + right. destruct close as [y [H H0]].
      exists y. split. right. exact H. exact H0.
Defined.

(* Slighlty more general than finite is totally bounded. *)
Lemma TotallyBoundedIsLocated
  : forall (X : MetricSpace) (Y : X -> Prop),
    TotallyBoundedSubset X Y
    -> locatedMetric X
    -> LocatedSubset X Y.
Proof.
  intros X Y totalBound loc d e x ltde.
  pose ((1#2)*(e-d)) as approxLen.
  pose (d+approxLen) as demid.
  assert (0 < approxLen) as approxLenPos.
  { unfold approxLen.
    rewrite <- (Qmult_0_r (1#2)).
    apply Qmult_lt_l. reflexivity.
    unfold Qminus. rewrite <- Qlt_minus_iff.
    exact ltde. }
  assert (demid < e).
  { unfold demid, approxLen.
    apply (Qplus_lt_l _ _ (-(1#2)*e)).
    ring_simplify.
    apply Qmult_lt_l. reflexivity. exact ltde. }
  (* The approximation of Y at precision (e-d)/2 is a finite subset of Y,
     such as any point of Y in close to a point in the finite subset
     within (e-d)/2. *)
  specialize (totalBound (exist _ _ approxLenPos)) as [l H0].
  unfold proj1_sig in e0.
  destruct (LocatedFinite X loc l demid e x H)
    as [far|close].
  + left. intros y H2 abs. 
    (* The distance between x and any point of the finite approximation
       of Y is above oneThird. *)
    specialize (e0 y H2) as [t [H3 H4]].
    specialize (far t H3).
    specialize (H0 t H3).
    contradict far. 
    apply (ball_triangle X d approxLen _ _ _ abs) in H4.
    exact H4.
  + right.
    destruct close as [y [yin close]].
    exists y. split. exact (H0 y yin).
    exact close.
Qed.

Lemma CompactIsLocated
  : forall (X : MetricSpace) (Y : Compact X),
    locatedMetric X
    -> LocatedSubset (Complete X) (fun z => inCompact z Y).
Proof.
  intros X Y loc d e x ltde. 
  (* TODO faster to avoid Bishop compact subsets and work directly on approximations. *)
  apply (TotallyBoundedIsLocated
           (Complete X)
           (fun z => inCompact z Y)
           (totallyBoundedSubset (CompactAsBishopCompact loc Y))
           (Complete_located loc) _ _ _ ltde).
Qed.
