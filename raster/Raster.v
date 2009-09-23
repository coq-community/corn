Require Export Bvector.
Require Export List.
Require Import Arith.

Set Implicit Arguments.

(**
* Rasters
A n by m raster is a vector of vector of booleans.
*)
Definition raster n m := vector (vector bool n) m.

(** A series of notation allows rasters to be rendered (and to a certain
extent parsed) in Coq *)
Notation "'⎥' a b" := (Vcons (vector bool _) a _ b)
  (format "'[v' '⎥' a '/' b ']'", at level 0, a, b at level 0) : raster.
Notation "'⎥' a" := (Vcons (vector bool _) a _ (Vnil _))
  (format "'⎥' a", at level 0, a, b at level 0) : raster.
(*
Notation "☙" := (Vnil (vector bool _)) (at level 0, right associativity) : raster.
*)
Notation "█ a" := (Vcons bool true _ a) (at level 0, right associativity) : raster.
Notation "⎢" := (@Vnil bool) (at level 0, right associativity) : raster.
Notation "' ' a" := (Vcons bool false _ a) (at level 0, right associativity) : raster.
Notation "░ a" := (Vcons bool false _ a) (at level 0, right associativity, only parsing) : raster_parsing.

(** Standard rasters. *)
Definition emptyRaster n m : raster n m :=
Vconst _ (Vconst _ false _) _.

Definition fullRaster n m : raster n m :=
Vconst _ (Vconst _ false _) _.

Definition vectorAsList A n (v:vector A n) : list A :=
vector_rect A (fun (n0 : nat) (_ : vector A n0) => list A) nil
  (fun (a : A) (n0 : nat) (_ : vector A n0) (IHv : list A) => a :: IHv) n v.

Coercion vectorAsList : vector>->list.

Lemma length_vectorAsList : forall A n (v:vector A n), (length v) = n.
Proof.
 induction v.
  reflexivity.
 simpl.
 auto with *.
Qed.

(** Indexing into a raster *)
Definition RasterIndex n m (r:raster n m) i j :=
 nth j (nth i (map (@vectorAsList _ _) r) nil) false.

(** Indexing into an empty raster is alway empty *)
Lemma emptyRasterEmpty : forall n m i j,
RasterIndex (emptyRaster n m) i j = false.
Proof.
 intros n m.
 induction m.
  intros [|i] [|j]; constructor.
 intros i j.
 simpl.
 destruct i.
  unfold RasterIndex.
  simpl.
  clear IHm.
  revert j.
  induction n.
   destruct j; auto.
  destruct j; auto.
  simpl.
  apply IHn.
 unfold RasterIndex in *.
 simpl.
 apply IHm.
Qed.

(** [setRaster] transforms a raster by setting (or reseting) the (i,j)th
pixel. *)
Definition updateVector A n (v:vector A n) (f:A->A) : nat -> vector A n :=
vector_rect A (fun (n0 : nat) (_ : vector A n0) => nat -> vector A n0)
  (fun (_ : nat) => Vnil A)
  (fun (a : A) (n0 : nat) (v0 : vector A n0) (IHv : nat -> vector A n0)
     (i : nat) =>
   match i with
   | 0 => Vcons A (f a) n0 v0
   | S i0 => Vcons A a n0 (IHv i0)
   end) n v.

Definition setRaster n m (r:raster n m) (x:bool) (i j:nat) :=
updateVector r (fun row => updateVector row (fun _ => x) j) i.

Lemma updateVector_correct1 : forall A n (v:vector A n) f i d1 d2,
i < n -> nth i (updateVector v f i) d1 = f (nth i v d2).
Proof.
 induction v.
  intros.
  absurd (i < 0); auto with *.
 intros f [|i] d1 d2 H.
  reflexivity.
 simpl.
 apply IHv.
 auto with *.
Qed.

Lemma updateVector_correct2 : forall A n (v:vector A n) f d1 i j,
i <> j ->
nth i (updateVector v f j) d1 = nth i v d1.
Proof.
 induction v.
  reflexivity.
 intros f d1 i [|j] H; destruct i as [|i]; try reflexivity.
  elim H; auto.
 simpl.
 apply IHv.
 auto.
Qed.

Lemma setRaster_correct1 : forall n m (r:raster n m) x i j,
 (i < m) -> (j < n) ->
 RasterIndex (setRaster r x i j) i j = x.
Proof.
 intros n m r x i j Hi Hj.
 unfold RasterIndex.
 replace (nth i (map (@vectorAsList _ _) (setRaster r x i j)) nil)
   with (nth i (map (@vectorAsList _ _) (setRaster r x i j)) (Vconst bool false n)).
  rewrite map_nth.
  unfold setRaster.
  rewrite (updateVector_correct1 r (fun row  => updateVector row (fun _ : bool => x) j) (Vconst bool false n) (Vconst bool false n) Hi).
  rewrite updateVector_correct1; auto.
 apply nth_indep.
 rewrite map_length.
 rewrite length_vectorAsList.
 auto.
Qed.

Lemma setRaster_overflow : forall n m (r:raster n m) x i j,
 (m <= i) \/ (n <= j) ->
 (setRaster r x i j) = r.
Proof.
 intros n m r x i j [Hi | Hj].
  revert i Hi.
  induction r.
   reflexivity.
  intros [|i] Hi.
   absurd (S n0 <= 0); auto with *.
  simpl.
  rewrite IHr; auto with *.
 revert i j Hj.
 induction r.
  reflexivity.
 intros [|i] j Hj.
  simpl.
  replace (updateVector a (fun _ : bool => x) j) with a.
   auto.
  clear n0 IHr r.
  revert j Hj.
  induction a.
   reflexivity.
  intros [|j] Hj.
   absurd (S n <= 0); auto with *.
  simpl.
  rewrite <- IHa; auto with *.
 simpl.
 rewrite IHr; auto with *.
Qed.

Lemma setRaster_correct2 : forall n m (r:raster n m) x i j i0 j0,
 (i <> i0) \/ (j <> j0) ->
 RasterIndex (setRaster r x i0 j0) i j = RasterIndex r i j.
Proof.
 intros n m r x i j i0 j0 H.
 destruct (le_lt_dec m i0) as [Hm | Hm].
  rewrite setRaster_overflow; auto with *.
 destruct (le_lt_dec n j0) as [Hn | Hn].
  rewrite setRaster_overflow; auto with *.
 unfold RasterIndex.
 assert (L:forall v : vector (Bvector n) m, nth j (nth i (map (@vectorAsList _ _) v) nil) false =
   nth j (nth i (map (@vectorAsList _ _) v) (Vconst bool false n)) false).
  intros v.
  destruct (le_lt_dec m i) as [Hi | Hi].
   transitivity false.
    rewrite (nth_overflow (map (@vectorAsList _ _) v)).
     destruct j; reflexivity.
    rewrite map_length.
    rewrite length_vectorAsList.
    auto.
   rewrite map_nth.
   rewrite (nth_overflow v).
    clear - j.
    revert j.
    induction n.
     destruct j; reflexivity.
    intros [|j].
     reflexivity.
    simpl.
    apply IHn.
   rewrite length_vectorAsList.
   auto.
  f_equal.
  apply nth_indep.
  rewrite map_length, length_vectorAsList.
  auto.
 transitivity (nth j (nth i (map (@vectorAsList _ _) (setRaster r x i0 j0)) (Vconst bool false n)) false).
  apply L.
 transitivity (nth j (nth i (map (@vectorAsList _ _) r) (Vconst bool false n)) false);[|symmetry;apply L].
 do 2 rewrite map_nth.
 destruct (eq_nat_dec i i0).
  destruct H as [Hi | Hj].
   elim Hi; auto.
  rewrite <- e in *; clear e.
  unfold setRaster.
  rewrite (updateVector_correct1 r (fun row => updateVector row (fun _ : bool => x) j0) (Vconst bool false n) (Vconst bool false n) Hm).
  rewrite updateVector_correct2; auto.
 unfold setRaster.
 rewrite updateVector_correct2; auto.
Qed.
