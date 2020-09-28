Require Coq.Vectors.Vector.
Export Vector.VectorNotations.
Require Export CoRN.stdlib_omissions.List.
Require Import Coq.Arith.Arith Coq.PArith.BinPos.

Set Implicit Arguments.

(**
* Rasters
A n by m raster is a vector of vector of booleans.
*)
Definition raster n m := Vector.t (Vector.t bool n) m.

(** A series of notation allows rasters to be rendered (and to a certain
extent parsed) in Coq *)
Notation "'⎥' a b" := (Vector.cons _ a _ b)
  (format "'[v' '⎥' a '/' b ']'", at level 0, a, b at level 0) : raster.
Notation "'⎥' a" := (Vector.cons _ a _ Vector.nil)
  (format "'⎥' a", at level 0, a at level 0) : raster.
(*
Notation "☙" := (Vnil (vector bool _)) (at level 0, right associativity) : raster.
*)
Notation "█ a" := (Vector.cons bool true _ a) (at level 0, right associativity) : raster.
Notation "⎢" := (@Vector.nil bool) (at level 0, right associativity) : raster.
Notation "' ' a" := (Vector.cons bool false _ a) (at level 0, right associativity) : raster.
Notation "░ a" := (Vector.cons bool false _ a) (at level 0, right associativity, only parsing) : raster_parsing.

(** Standard rasters. *)
Definition emptyRaster n m : raster n m := Vector.const (Vector.const false _) _.

Coercion Vector.to_list : Vector.t>->list.

Lemma length_vectorAsList : forall A n (v: Vector.t A n), (length v) = n.
Proof.
 induction v.
  reflexivity.
 simpl.
 auto with *.
Qed.

(** Indexing into a raster *)
Definition RasterIndex n m (r:raster n m) i j :=
 nth j (nth i (map (@Vector.to_list _ _) r) nil) false.

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
Fixpoint updateVector A n (v : Vector.t A n) (f : A->A) : nat -> Vector.t A n := 
  match v with
  | Vector.nil _ => fun _ => Vector.nil A
  | Vector.cons _ a' n' v' => fun i =>
    match i with
    | 0 => Vector.cons A (f a') n' v'
    | S i' => Vector.cons A a' n' (updateVector v' f i')
    end
  end.

Definition setRaster n m (r:raster n m) (x:bool) (i j:nat) :=
updateVector r (fun row => updateVector row (fun _ => x) j) i.

Lemma updateVector_correct1 : forall A n (v: Vector.t A n) f i d1 d2,
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

Lemma updateVector_correct2 : forall A n (v: Vector.t A n) f d1 i j,
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

Lemma setRaster_correct1
  : forall (n m : positive) (r:raster (Pos.to_nat n) (Pos.to_nat m)) x i j,
 (i < Pos.to_nat m) -> (j < Pos.to_nat n) ->
 RasterIndex (setRaster r x i j) i j = x.
Proof.
 intros n m r x i j Hi Hj.
 unfold RasterIndex.
 replace (nth i (map (@Vector.to_list _ _) (setRaster r x i j)) nil)
   with (nth i (map (@Vector.to_list _ _) (setRaster r x i j)) (Vector.const false (Pos.to_nat n))).
  rewrite map_nth.
  unfold setRaster.
  rewrite (updateVector_correct1 r (fun row  => updateVector row (fun _ : bool => x) j) (Vector.const false (Pos.to_nat n)) (Vector.const false (Pos.to_nat n)) Hi).
  rewrite updateVector_correct1; auto.
 apply nth_indep.
 rewrite map_length.
 rewrite length_vectorAsList.
 auto.
Qed.

Lemma updateVector_overflow : forall A n (v : Vector.t A n) f i, n <= i -> updateVector v f i = v.
Proof with try reflexivity; auto with arith.
 induction v...
 intros f [|i] E.
  inversion E.
 simpl. rewrite IHv...
Qed.

Lemma setRaster_overflow : forall n m (r:raster n m) x i j,
 (m <= i) \/ (n <= j) ->
 (setRaster r x i j) = r.
Proof with try reflexivity; auto.
 unfold setRaster.
 intros n m r x i j [Hi | Hj].
  apply updateVector_overflow...
 revert i j Hj. induction r...
 intros [|i] j Hj; simpl; f_equal...
 apply updateVector_overflow...
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
 assert (L:forall v : Vector.t (Vector.t bool n) m, nth j (nth i (map (@Vector.to_list _ _) v) nil) false =
   nth j (nth i (map (@Vector.to_list _ _) v) (Vector.const false n)) false).
  intros v.
  destruct (le_lt_dec m i) as [Hi | Hi].
   transitivity false.
    rewrite (nth_overflow (map (@Vector.to_list _ _) v)).
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
 transitivity (nth j (nth i (map (@Vector.to_list _ _) (setRaster r x i0 j0)) (Vector.const false n)) false).
  apply L.
 transitivity (nth j (nth i (map (@Vector.to_list _ _) r) (Vector.const false n)) false);[|symmetry;apply L].
 do 2 rewrite map_nth.
 destruct (eq_nat_dec i i0).
  destruct H as [Hi | Hj].
   elim Hi; auto.
  rewrite <- e in *; clear e.
  unfold setRaster.
  rewrite (updateVector_correct1 r (fun row => updateVector row (fun _ : bool => x) j0) (Vector.const false n) (Vector.const false n) Hm).
  rewrite updateVector_correct2; auto.
 unfold setRaster.
 rewrite updateVector_correct2; auto.
Qed.
