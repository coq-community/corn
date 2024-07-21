Require Coq.Vectors.Vector.
Export Vector.VectorNotations.
Require Export CoRN.stdlib_omissions.List.
From Coq Require Import Arith BinPos.

Set Implicit Arguments.

(**
* Rasters
An n by m raster is a matrix of booleans. Do not use Vector, which stores
a slow nat on each cons.
*)
Variant raster (columns lines : positive) : Set :=
| raster_data : list (list bool) -> raster columns lines.

(* TODO directly list (list bool), length of first line then
   all lines same length. *)
Definition raster_well_formed {columns lines : positive} (r : raster columns lines) : Prop
  := match r with raster_data _ _ d =>
     length d = Pos.to_nat lines
     /\ Forall (fun line : list bool => length line = Pos.to_nat columns) d
     end.

(** A series of notation allows rasters to be rendered (and to a certain
extent parsed) in Coq *)
Notation "'⎥' a b" := (List.cons a b)
  (format "'[v' '⎥' a '/' b ']'", at level 0, a, b at level 0) : raster.
Notation "'⎥' a" := (List.cons a List.nil)
  (format "'⎥' a", at level 0, a at level 0) : raster.
(*
Notation "☙" := (Vnil (vector bool _)) (at level 0, right associativity) : raster.
*)
Notation "█ a" := (List.cons true a) (at level 0, right associativity) : raster.
Notation "⎢" := (@List.nil bool) (at level 0, right associativity) : raster.
Notation "' ' a" := (List.cons false a) (at level 0, right associativity) : raster.
Notation "░ a" := (List.cons false a) (at level 0, right associativity, only parsing) : raster_parsing.

(** Standard rasters. *)
Definition emptyRaster n m : raster n m
  := raster_data n m (List.repeat (List.repeat false (Pos.to_nat n)) (Pos.to_nat m)).

Lemma emptyRaster_wf : forall n m, raster_well_formed (emptyRaster n m).
Proof.
  split.
  - apply repeat_length.
  - apply Forall_forall. intros.
    apply repeat_spec in H. subst x.
    apply repeat_length.
Qed.

(** Indexing into a raster *)
Definition RasterIndex {n m} (r:raster n m) i j : bool
  := let (d) := r in nth j (nth i d nil) false.

Lemma nth_repeat : forall A n (x:A) k d,
    nth n (List.repeat x k) d
    = if le_lt_dec k n then d else x.
Proof.
  intros. destruct (le_lt_dec k n).
  - apply nth_overflow. rewrite repeat_length. exact l.
  - apply (repeat_spec k x).
    apply nth_In.
    rewrite repeat_length.
    exact l.
Qed.
    
(** Indexing into an empty raster is alway empty *)
Lemma emptyRasterEmpty : forall n m i j,
    RasterIndex (emptyRaster n m) i j = false.
Proof.
 intros n m i j.
 simpl.
 rewrite (nth_repeat i (repeat false (Pos.to_nat n)) (Pos.to_nat m) nil).
 destruct (le_lt_dec (Pos.to_nat m) i).
 - destruct j; reflexivity.
 - rewrite (nth_repeat j false (Pos.to_nat n) false).
   destruct (le_lt_dec (Pos.to_nat n) j); reflexivity.
Qed.

(** [setRaster] transforms a raster by setting (or reseting) the (i,j)th
pixel. *)
Fixpoint updateList A (v : list A) (f : A->A) : nat -> list A := 
  match v with
  | nil => fun _ => nil
  | cons a' v' => fun i =>
    match i with
    | 0 => cons (f a') v'
    | S i' => cons a' (updateList v' f i')
    end
  end.

Lemma updateList_length : forall A (v:list A) f i,
    length (updateList v f i) = length v.
Proof.
  induction v.
  - reflexivity.
  - intros. simpl. destruct i.
    reflexivity. simpl. rewrite IHv. reflexivity.
Qed. 

Lemma updateList_correct1 : forall A (v: list A) f i d1 d2,
i < length v -> nth i (updateList v f i) d1 = f (nth i v d2).
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

Lemma updateList_correct2 : forall A (v: list A) f d1 i j,
i <> j ->
nth i (updateList v f j) d1 = nth i v d1.
Proof.
 induction v.
  reflexivity.
 intros f d1 i [|j] H; destruct i as [|i]; try reflexivity.
  elim H; auto.
 simpl.
 apply IHv.
 auto.
Qed.

Lemma updateList_overflow : forall A (v : list A) f i,
    length v <= i -> updateList v f i = v.
Proof.
 induction v.
 - reflexivity.
 - intros. simpl. destruct i.
   exfalso; inversion H.
   apply f_equal. rewrite IHv. reflexivity.
   apply le_S_n, H. 
Qed. 

Definition setRaster {n m} (r:raster n m) (x:bool) (i j:nat) : raster n m
  := let (d) := r in
     raster_data n m (updateList d (fun row => updateList row (fun _ => x) j) i).

Lemma setRaster_wf : forall n m (r:raster n m) x i j,
    raster_well_formed r -> raster_well_formed (setRaster r x i j).
Proof.
  intros. destruct r. destruct H. split.
  - rewrite updateList_length. exact H.
  - apply Forall_forall. intros. 
    apply In_nth with (d:=nil) in H1.
    destruct H1 as [k [H1 H2]]. subst x0.
    rewrite Forall_forall in H0. 
    rewrite updateList_length in H1.
    destruct (Nat.eq_dec k i).
    + subst i. rewrite updateList_correct1 with (d2:=nil).
      rewrite updateList_length.
      apply H0. apply nth_In, H1. exact H1.
    + rewrite (updateList_correct2 l). 2: exact n0.
      apply H0. apply nth_In, H1.
Qed. 

Lemma setRaster_correct1
  : forall {n m : positive} (r:raster n m) x i j,
    raster_well_formed r -> 
 (i < Pos.to_nat m) -> (j < Pos.to_nat n) ->
 RasterIndex (setRaster r x i j) i j = x.
Proof.
 intros n m r x i j rWf Hi Hj.
 destruct r. simpl. destruct rWf.
 rewrite updateList_correct1 with (d2:=nil).
 2: rewrite H; exact Hi.
 rewrite updateList_correct1. reflexivity.
 trivial.
 rewrite Forall_forall in H0.
 rewrite (H0 (nth i l nil)). exact Hj.
 apply nth_In.
 rewrite H. exact Hi.
Qed.

Lemma setRaster_overflow : forall {n m} (r:raster n m) x i j,
    raster_well_formed r ->
    (Pos.to_nat m <= i) \/ (Pos.to_nat n <= j) ->
    (setRaster r x i j) = r.
Proof.
  intros. destruct r.
  unfold setRaster. apply f_equal.
  destruct H.
  destruct H0.
  - apply updateList_overflow.
    rewrite H. exact H0.
  - clear H m.
    rewrite Forall_forall in H1.
    revert i. induction l.
    + reflexivity.
    + intro i. simpl. destruct i.
      f_equal. apply updateList_overflow.
      rewrite (H1 a). exact H0. left. reflexivity.
      f_equal. apply IHl.
      intros. apply H1. right. exact H.
Qed.

Lemma setRaster_correct2 : forall n m (r:raster n m) x i j i0 j0,
    raster_well_formed r ->
 (i <> i0) \/ (j <> j0) ->
 RasterIndex (setRaster r x i0 j0) i j = RasterIndex r i j.
Proof.
 intros n m r x i j i0 j0 rWf H.
 destruct (le_lt_dec (Pos.to_nat m) i0) as [Hm | Hm].
  rewrite setRaster_overflow; auto with *.
 destruct (le_lt_dec (Pos.to_nat n) j0) as [Hn | Hn].
  rewrite setRaster_overflow; auto with *.
 destruct r as [l]. simpl.
 destruct H.
 + f_equal.
   rewrite updateList_correct2.
   reflexivity. exact H.
 + destruct rWf. destruct (Nat.eq_dec i i0).
   subst i0. 
   rewrite updateList_correct1 with (d2:=nil).
   2: rewrite H0; exact Hm.
   rewrite updateList_correct2.
   reflexivity. exact H.
   f_equal.
   rewrite updateList_correct2.
   reflexivity. exact n0.
Qed.
