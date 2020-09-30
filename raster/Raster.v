Require Coq.Vectors.Vector.
Export Vector.VectorNotations.
Require Export CoRN.stdlib_omissions.List.
Require Import Coq.Arith.Arith Coq.PArith.BinPos Coq.PArith.PArith.

Set Implicit Arguments.

(**
* Rasters
An n by m raster is a matrix of booleans. Do not use Vector, which stores
a slow nat on each cons.
*)
Definition raster : Set := list (list bool).

Definition RasterLineLength (r : raster) : nat := length (nth O r nil).

Definition raster_well_formed (r : raster) : Prop
  := forall h k : list bool,
    In h r
    -> In k r
    -> length h = length k.

Definition raster_well_formed_nm (n m : positive) (r : raster) : Prop
  := length r = Pos.to_nat m
     /\ forall h : list bool,
      In h r
      -> length h = Pos.to_nat n.

Lemma raster_well_formed_weaken : forall n m r,
    raster_well_formed_nm n m r -> raster_well_formed r.
Proof.
  intros. intros h k ih ik.
  destruct H.
  transitivity (Pos.to_nat n).
  - apply H0, ih.
  - symmetry. apply H0, ik.
Qed.

Lemma raster_well_formed_strengthen : forall n m r,
    raster_well_formed r
    -> length r = Pos.to_nat m
    -> length (nth 0 r nil) = Pos.to_nat n
    -> raster_well_formed_nm n m r.
Proof.
  split.
  - exact H0.
  - intros h ih. 
    rewrite (H h (nth 0 r nil) ih).
    exact H1. apply nth_In.
    rewrite H0. apply Pos2Nat.is_pos.
Qed.

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
Definition emptyRaster n m : raster
  := List.repeat (List.repeat false (Pos.to_nat n)) (Pos.to_nat m).

Lemma emptyRaster_wf : forall n m, raster_well_formed_nm n m (emptyRaster n m).
Proof.
  intros n m. unfold emptyRaster.
  split.
  - apply repeat_length.
  - intros h ih. apply repeat_spec in ih.
    subst h. apply repeat_length.
Qed.

Lemma raster_well_formed_tl
  : forall r:raster, raster_well_formed r -> raster_well_formed (tl r).
Proof.
  intros r H h k ih ik.
  apply In_nth with (d:=nil) in ih.
  destruct ih as [n [nin ih]]. subst h.
  apply In_nth with (d:=nil) in ik.
  destruct ik as [m [min ik]]. subst k.
  destruct r.
  - exfalso. inversion nin. 
  - simpl.
    apply H; right; apply nth_In; assumption.
Qed.

(** Indexing into a raster *)
Definition RasterIndex (r : raster) (line col : nat) : bool
  := nth col (nth line r nil) false.

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
 unfold RasterIndex, emptyRaster. 
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

Definition setRaster (r:raster) (x:bool) (i j:nat) : raster
  := updateList r (fun row => updateList row (fun _ => x) j) i.

Lemma setRaster_wf : forall n m (r:raster) x i j,
    raster_well_formed_nm n m r
    -> raster_well_formed_nm n m (setRaster r x i j).
Proof.
  intros. destruct H. split.
  - unfold setRaster. rewrite updateList_length. exact H.
  - intros. 
    apply In_nth with (d:=nil) in H1.
    destruct H1 as [k [H1 H2]]. subst h.
    unfold setRaster in H1.
    unfold setRaster.
    rewrite updateList_length in H1.
    destruct (Nat.eq_dec k i).
    + subst i.
      rewrite updateList_correct1 with (d2:=nil).
      rewrite updateList_length.
      apply H0. apply nth_In, H1. exact H1.
    + rewrite (updateList_correct2 r). 2: exact n0.
      apply H0. apply nth_In, H1.
Qed. 

Lemma setRaster_correct1
  : forall (r:raster) x i j,
    raster_well_formed r -> 
    (i < length r) -> (j < RasterLineLength r) ->
    RasterIndex (setRaster r x i j) i j = x.
Proof.
  intros r x i j rWf Hi Hj.
  unfold RasterIndex, setRaster.
  unfold RasterLineLength in Hj.
  rewrite updateList_correct1 with (d2:=nil).
  2: exact Hi.
  rewrite updateList_correct1. reflexivity.
  trivial.
  rewrite (rWf (nth i r nil) (nth O r nil)).
  exact Hj.
  apply nth_In, Hi.
  apply nth_In.
  apply (le_lt_trans _ i).
  apply le_0_n. exact Hi.
Qed.

Lemma setRaster_overflow : forall (r:raster) x i j,
    raster_well_formed r ->
    (length r <= i) \/ (RasterLineLength r <= j) ->
    (setRaster r x i j) = r.
Proof.
  intros.
  unfold setRaster. 
  destruct H0.
  - apply updateList_overflow, H0.
  - revert i. induction r.
    + reflexivity.
    + intro i. simpl.
      unfold RasterLineLength in H0. simpl in H0.
      destruct i.
      * f_equal. apply updateList_overflow.
        exact H0.
      * f_equal. apply IHr.
        apply (raster_well_formed_tl H).
        unfold RasterLineLength.
        destruct r. apply le_0_n.
        rewrite (H _ a).
        exact H0. right. left. reflexivity.
        left. reflexivity.
Qed.

Lemma setRaster_correct2 : forall (r:raster) x i j i0 j0,
    raster_well_formed r ->
    (i <> i0) \/ (j <> j0) ->
    RasterIndex (setRaster r x i0 j0) i j = RasterIndex r i j.
Proof.
 intros r x i j i0 j0 rWf H.
 destruct (le_lt_dec (length r) i0) as [Hm | Hm].
  rewrite setRaster_overflow; auto with *.
 destruct (le_lt_dec (RasterLineLength r) j0) as [Hn | Hn].
  rewrite setRaster_overflow; auto with *.
 unfold RasterIndex, setRaster.
 destruct H.
 - f_equal.
   rewrite updateList_correct2.
   reflexivity. exact H.
 - destruct (Nat.eq_dec i i0).
   + subst i0. 
     rewrite updateList_correct1 with (d2:=nil).
     2: exact Hm.
     rewrite updateList_correct2.
     reflexivity. exact H.
   + f_equal.
     rewrite updateList_correct2.
     reflexivity. exact n.
Qed.
