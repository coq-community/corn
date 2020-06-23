(*
Copyright © 2008 Russell O’Connor

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
Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Export CoRN.raster.Raster.
Require Import CoRN.reals.fast.Interval.
Require Export CoRN.metric2.FinEnum.
Require Export CoRN.metric2.ProductMetric.
Require Import CoRN.logic.Classic.
Require Import CoRN.tactics.CornTac.

Set Implicit Arguments.
(**
** Rasters on Planes
By attaching coordinates to the top-left and bottom-right corners of
a raster, it can be interpreted as a finite set in [Q]^2. *)
Definition Q2 := (ProductMS Q_as_MetricSpace Q_as_MetricSpace).

Lemma stableQ2 : stableMetric Q2.
Proof.
 apply ProductMS_stable; apply stableQ.
Qed.

(** For [Q2], classical membership in a finite enumeration is the
same as a constructive membership. *)
Lemma InStrengthen : forall x (l:FinEnum stableQ2),
InFinEnumC x l -> exists y : ProductMS _ _, In y l /\ st_eq x y.
Proof.
 induction l.
  contradiction.
 intros H.
 assert (L:st_eq x a \/ ~st_eq x a).
  destruct (Qeq_dec (fst x) (fst a)).
   destruct (Qeq_dec (snd x) (snd a)).
    left.
    split; auto.
   right; intros [_ B]; auto.
  right; intros [B _]; auto.
 destruct L.
  exists a.
  split; auto with *.
 destruct (IHl) as [y [Hy0 Hy1]].
  destruct H as [G | H | H] using orC_ind.
    auto using InFinEnumC_stable.
   elim H0; auto.
  auto.
 exists y.
 split; auto with *.
Qed.

Definition InterpRow (up : list Q) n (v:Vector.t bool n) : FinEnum stableQ:=
 map (@fst _ _ ) (filter (@snd _ _) (combine up v)).

Definition InterpRaster n m (bitmap : raster n m) (tl br:(ProductMS Q_as_MetricSpace Q_as_MetricSpace)) : FinEnum stableQ2 :=
 let (l,t) := tl in
 let (r,b) := br in
 let up := (UniformPartition l r n) in
 flat_map (fun (p:Q*Vector.t bool _) => let (y,r):=p in map (fun x => (x,y)) (InterpRow up r)) (combine (UniformPartition t b m) bitmap).

(** Notation for the interpretation of a raster. *)
Notation "a ⇱ b ⇲ c" := (InterpRaster b a c) (at level 1,
 format "a ⇱ '[v' '/' b ']' '[v' '/' ⇲ c ']'") : raster.

(*
Local Open Scope raster.
Local Open Scope raster_parsing.

Example ex5 :=
(0, 1)⇱
         ⎥█░█⎢
         ⎥░█░⎢
         ⎥░░█⎢
             ⇲(1, 0).

Eval compute in (ex5).
*)

Fixpoint iterateN (A:Type) (f:A -> A) (z:A) (n:nat) : list A :=
match n with
 O => nil
|S m => z :: (iterateN f (f z) m)
end.

Lemma iterateN_f : forall A f (z:A) n, iterateN f (f z) n = map f (iterateN f z n).
Proof.
 intros A f z n.
 revert f z.
 induction n.
  reflexivity.
 simpl.
 intros f z.
 rewrite <- IHn.
 reflexivity.
Qed.

(** Correctness properties of our interpretation. *)
Section InterpRasterCorrect.

Let f := fun l r (n:nat) (i:Z) => l + (r - l) * (2 * i + 1 # 1) / (2 * Z.of_nat n # 1).

Lemma InterpRaster_correct1 : forall n m (t l b r:Q) (bitmap: raster n m) i j,
    Is_true (RasterIndex bitmap i j)
    -> In (f l r n (Z.of_nat j),f t b m (Z.of_nat i)) (InterpRaster bitmap (l,t) (r,b)).
Proof.
 intros n m t l b r bitmap.
 unfold InterpRaster, InterpRow, UniformPartition.
 fold (f l r n).
 fold (f t b m).
 generalize (f l r n) (f t b m).
 induction bitmap as [ | a]; intros f0 f1 i j H.
  unfold RasterIndex in H.
  destruct (nth_in_or_default i (map (@Vector.to_list _ _) (@Vector.nil (@Vector.t bool n))) nil) as [A | A].
   contradiction.
  rewrite A in H; clear A.
  destruct (nth_in_or_default j nil false) as [A | A].
   contradiction.
  rewrite A in H; clear A.
  contradiction.
 destruct i as [|i].
  simpl.
  apply in_or_app.
  left.
  unfold RasterIndex in H.
  simpl in H.
  clear bitmap IHbitmap.
  revert f0 j H.
  induction a as [|a]; intros f0 j H.
   destruct (nth_in_or_default j (@Vector.nil bool) false) as [A | A].
    contradiction.
   rewrite A in H; clear A.
   contradiction.
  destruct j as [|j].
   simpl in H.
   destruct a; try contradiction.
   simpl.
   left; reflexivity.
  rewrite inj_S.
  cut (In ((f0 (Z.succ (Z.of_nat j))), (f1 0%Z)) (map (fun x : Q => (x, (f1 0%Z)))
    (map (@fst _ _) (filter (@snd _ _) (combine (map f0 (iterateN Z.succ 1%Z n)) a0))))).
   intros L.
   destruct a; try right; auto.
  change (1%Z) with (Z.succ 0).
  rewrite iterateN_f.
  rewrite (map_map Z.succ f0).
  apply (IHa (fun x:Z => f0 (Z.succ x))).
  apply H.
 rewrite inj_S.
 set (f1':= fun (x:Z) =>(f1 (Z.succ x))).
 fold (f1' (Z.of_nat i)).
 simpl.
 apply in_or_app.
 right.
 change (1%Z) with (Z.succ 0).
 rewrite iterateN_f.
 rewrite map_map.
 fold f1'.
 apply IHbitmap.
 apply H.
Qed.

Lemma InterpRaster_correct2 : forall n m (t l b r:Q) x y (bitmap: raster n m),
In (x,y) (InterpRaster bitmap (l,t) (r,b)) ->
exists p, Is_true (RasterIndex bitmap (fst p) (snd p)) /\ x=f l r n (Z.of_nat (snd p))
     /\ y=f t b m (Z.of_nat (fst p)).
Proof.
 intros n m t l b r x y bitmap.
 unfold InterpRaster, InterpRow, UniformPartition.
 fold (f l r n).
 fold (f t b m).
 generalize (f l r n) (f t b m).
 induction bitmap as [|a]; intros f0 f1 H.
  contradiction.
 simpl in H.
 destruct (in_app_or _ _ _ H) as [H0 | H0]; clear H.
  cut (exists p : nat, Is_true (nth p a false) /\ x = f0 (Z.of_nat p) /\ y = f1 0%Z).
   intros [z Z].
   clear -Z.
   exists (0%nat,z).
   auto.
  clear bitmap IHbitmap.
  revert f0 H0.
  induction a as [|a]; intros f0 H0.
   contradiction.
  destruct a.
   simpl in H0.
   destruct H0 as [H0 | H0].
    exists 0%nat.
    split.
     constructor.
    simpl in H0.
    inversion_clear H0.
    auto.
   edestruct IHa as [z Hz].
    change 1%Z with (Z.succ 0) in H0.
    rewrite iterateN_f in H0.
    rewrite (map_map Z.succ f0) in H0.
    apply H0.
   exists (S z).
   rewrite inj_S; auto.
  edestruct IHa as [z Hz].
   simpl in H0.
   change 1%Z with (Z.succ 0) in H0.
   rewrite iterateN_f in H0.
   rewrite (map_map Z.succ f0) in H0.
   apply H0.
  exists (S z).
  rewrite inj_S; auto.
 change 1%Z with (Z.succ 0) in H0.
 rewrite iterateN_f in H0.
 rewrite (map_map) in H0.
 edestruct IHbitmap as [z Hz].
  apply H0.
 exists (S (fst z),snd z).
 simpl (fst ((S (fst z)), (snd z))).
 rewrite inj_S.
 auto.
Qed.

End InterpRasterCorrect.
(* begin hide *)
Add Parametric Morphism n m bm : (@InterpRaster n m bm) with signature (@st_eq _) ==> (@st_eq _) ==> (@st_eq _) as InterpRaster_wd.
Proof.
 cut (forall (x1 x2 : Q2), prod_st_eq Q_as_MetricSpace Q_as_MetricSpace x1 x2 -> forall x3 x4 : Q2,
   prod_st_eq Q_as_MetricSpace Q_as_MetricSpace x3 x4 -> forall y,
     InFinEnumC (X:=ProductMS Q_as_MetricSpace Q_as_MetricSpace) y (InterpRaster bm x1 x3) ->
       InFinEnumC (X:=ProductMS Q_as_MetricSpace Q_as_MetricSpace) y (InterpRaster bm x2 x4)).
  intros L.
  split.
   apply L; auto.
  apply L.
   symmetry; auto.
  symmetry; auto.
 intros [x1l x1r] x2 Hx [y1l y1r] y2 Hy z Hz.
 destruct (InStrengthen _ _ Hz) as [[ax ay] [Ha0 Ha1]].
 destruct (InterpRaster_correct2 _ _ _ _ _ _ _ Ha0) as [[bx by'] [Hb0 [Hb1 Hb2]]].
 rewrite Hb1 in Ha1.
 rewrite Hb2 in Ha1.
 unfold snd, fst in Ha1.
 destruct x2 as [x2l x2r].
 destruct y2 as [y2l y2r].
 assert (L0:st_eq z ((x2l + (y2l - x2l) * (2 * Z.of_nat by' + 1 # 1) / (2 * Z.of_nat n # 1)),
   (x2r + (y2r - x2r) * (2 * Z.of_nat bx + 1 # 1) / (2 * Z.of_nat m # 1)))).
  transitivity ((x1l + (y1l - x1l) * (2 * Z.of_nat by' + 1 # 1) / (2 * Z.of_nat n # 1)),
    (x1r + (y1r - x1r) * (2 * Z.of_nat bx + 1 # 1) / (2 * Z.of_nat m # 1))).
   auto.
  clear - Hx Hy.
  destruct Hx as [Hx1 Hx2].
  destruct Hy as [Hy1 Hy2].
  split; unfold fst,snd in *.
   rewrite -> Hx1, Hy1.
   reflexivity.
  rewrite -> Hx2, Hy2.
  reflexivity.
 rewrite -> (InFinEnumC_wd1 _ _ _ (InterpRaster bm (x2l, x2r) (y2l, y2r)) L0).
 apply InFinEnumC_weaken.
 auto using InterpRaster_correct1.
Qed.
(* end hide *)
