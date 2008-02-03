Require Export Raster.
Require Import Interval.
Require Export FinEnum.
Require Export ProductMetric.
Require Import Classic.

Set Implicit Arguments.

Lemma stableQ2 : stableMetric (ProductMS Q_as_MetricSpace Q_as_MetricSpace).
Proof.
apply ProductMS_stable; apply stableQ.
Qed.

Lemma InStrengthen : forall x (l:FinEnum stableQ2),
InFinEnumC x l -> exists y : ProductMS _ _, In y l /\ ms_eq x y.
Proof.
induction l.
 contradiction.
intros H.
assert (L:ms_eq x a \/ ~ms_eq x a).
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

Definition InterpRow (up : list Q) n (v:Bvector n) : FinEnum stableQ:=
 map (@fst _ _ ) (filter (@snd _ _) (combine up v)).

Definition InterpRaster (tl br:Q*Q) n m (bitmap : raster n m) : FinEnum stableQ2 :=
 let (l,t) := tl in
 let (r,b) := br in
 let up := (UniformPartition l r n) in
 flat_map (fun (p:Q*Bvector _) => let (y,r):=p in map (fun x => (x,y)) (InterpRow up r)) (combine (UniformPartition t b m) bitmap).

Notation "a ⇱ b ⇲ c" := (InterpRaster a c b) (at level 1,
 format "a ⇱ '[v' '/' b ']' '[v' '/' ⇲ c ']'") : raster.

(*
Open Local Scope raster.
Open Local Scope raster_parsing.

Example ex5 := 
(0, 1)⇱
         ⎥█░█⎢
         ⎥░█░⎢
         ⎥░░█⎢
             ⇲(1, 0).

Eval compute in (ex5).
*)

Section InterpRasterCorrect.

Let f := fun l r (n:nat) (i:Z) => l + (r - l) * (2 * i + 1 # 1) / (2 * n # 1).

Lemma InterpRaster_correct1 : forall n m (t l b r:Q) (bitmap: raster n m) i j,
Is_true (RasterIndex bitmap i j) -> In (f l r n j,f t b m i) (InterpRaster (l,t) (r,b) bitmap).
Proof.
intros n m t l b r bitmap.
unfold InterpRaster, InterpRow, UniformPartition.
fold (f l r n).
fold (f t b m).
generalize (f l r n) (f t b m).
induction bitmap;
 intros f0 f1 i j H.
 unfold RasterIndex in H.
 destruct (nth_in_or_default i (map (@vectorAsList _ _) (Vnil (vector bool n))) nil) as [A | A].
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
 induction a; intros f0 j H.
  destruct (nth_in_or_default j (Vnil bool) false) as [A | A].
   contradiction.
  rewrite A in H; clear A.
  contradiction.
 destruct j as [|j].
  simpl in H.
  destruct a; try contradiction.
  simpl.
  left; reflexivity.
 rewrite inj_S.
 cut (In (Pair (f0 (Zsucc j)) (f1 0%Z))
  (map (fun x : Q => Pair x (f1 0%Z))
     (map (@fst _ _) (filter (@snd _ _) (combine (map f0 (iterateN Zsucc 1%Z n)) a0))))).
  intros L.
  destruct a; try right; auto.
 change (1%Z) with (Zsucc 0).
 rewrite iterateN_f.
 rewrite (map_map Zsucc f0).
 apply (IHa (fun x:Z => f0 (Zsucc x))).
 apply H.
rewrite inj_S.
set (f1':= fun (x:Z) =>(f1 (Zsucc x))).
fold (f1' i).
simpl.
apply in_or_app.
right.
change (1%Z) with (Zsucc 0).
rewrite iterateN_f.
rewrite map_map.
fold f1'.
apply IHbitmap.
apply H.
Qed.

Lemma InterpRaster_correct2 : forall n m (t l b r:Q) x y (bitmap: raster n m),
In (x,y) (InterpRaster (l,t) (r,b) bitmap) -> 
 exists p, Is_true (RasterIndex bitmap (fst p) (snd p)) /\ x=f l r n (snd p) /\ y=f t b m (fst p).
Proof.
intros n m t l b r x y bitmap.
unfold InterpRaster, InterpRow, UniformPartition.
fold (f l r n).
fold (f t b m).
generalize (f l r n) (f t b m).
induction bitmap;
 intros f0 f1 H.
 contradiction.
simpl in H.
destruct (in_app_or _ _ _ H) as [H0 | H0]; clear H.
 cut (exists p : nat,
  Is_true (nth p a false) /\
  x = f0 p /\ y = f1 0%Z).
  intros [z Z].
  clear -Z.
  exists (0%nat,z).
  auto.
 clear bitmap IHbitmap.
 revert f0 H0.
 induction a; intros f0 H0.
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
   change 1%Z with (Zsucc 0) in H0.
   rewrite iterateN_f in H0.
   rewrite (map_map Zsucc f0) in H0.
   apply H0.
  exists (S z).
  rewrite inj_S; auto.
 edestruct IHa as [z Hz].
  simpl in H0.
  change 1%Z with (Zsucc 0) in H0.
  rewrite iterateN_f in H0.
  rewrite (map_map Zsucc f0) in H0.
  apply H0.
 exists (S z).
 rewrite inj_S; auto.
change 1%Z with (Zsucc 0) in H0.
rewrite iterateN_f in H0.
rewrite (map_map) in H0.
edestruct IHbitmap as [z Hz].
 apply H0.
exists (S (fst z),snd z).
simpl (fst (Pair (S (fst z)) (snd z))).
rewrite inj_S.
auto.
Qed.

End InterpRasterCorrect.