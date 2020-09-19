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

Require Import CoRN.algebra.RSetoid.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import CoRN.model.metric2.Qmetric. 
Require Import CoRN.metric2.Limit.
Require Import Coq.QArith.Qabs. 
Require Import Coq.Arith.Arith.
Require Import Coq.QArith.Qpower.
Require Import CoRN.reals.fast.LazyNat. 
Require Import Coq.setoid_ring.Ring MathClasses.interfaces.abstract_algebra MathClasses.theory.streams.
Require Export MathClasses.theory.series.
Require Import MathClasses.interfaces.abstract_algebra MathClasses.theory.streams.

Opaque Qabs.
Local Open Scope Q_scope.

(**
** Specific results for streams on [Q]
*)

(** [everyOther] preserves limits. *)
Lemma everyOther_nbz : forall (s : Stream Q) (e : QposInf),
    (NearBy 0 e s) -> NearBy 0 e (everyOther s).
Proof.
 cofix everyOther_nbz.
 intros [s [b r]] x [H [_ Hs]].
 constructor;[|apply everyOther_nbz];assumption.
Qed.

Instance everyOther_zl `{Hx : !Limit s 0} : Limit (everyOther s) 0.
Proof.
 intros e.
 assert (H:=Hx e). clear Hx.
 revert s H.
 fix everyOther_zl 2.
 intros x [H|H].
  left.
  apply everyOther_nbz.
  assumption.
 case (H tt);[intros X |intros X].
  right; left.
  clear - x X.
  abstract ( destruct x as [a [b x]]; destruct X; apply everyOther_nbz; assumption).
 right; intros _.
 apply everyOther_zl.
 apply X.
 constructor.
Defined.

(** [mult_Streams] preserves convergeing to 0. *)
Lemma mult_Streams_nbz : forall {s1 s2 : Stream Q} {x : QposInf},
    (NearBy 0 x s1)
    -> forall {y : QposInf}, NearBy 0 y s2
             -> NearBy 0 (x*y) (mult_Streams s1 s2).
Proof.
 unfold NearBy.
 cofix mult_Streams_nbz.
 intros s1 s2 x [Ha0 Hs1] y [Hb0 Hs2].
 constructor.
 2: apply (mult_Streams_nbz (CoqStreams.tl s1) (CoqStreams.tl s2)); assumption.
 destruct x as [x|];[|constructor].
 destruct y as [y|];[|constructor].
 simpl.
 unfold Qball.
 unfold QAbsSmall.
 setoid_replace ((CoqStreams.hd s1 * CoqStreams.hd s2)%mc - 0)%Q
   with ((CoqStreams.hd s1 - 0) * (CoqStreams.hd s2 - 0)). 
 apply Qmult_AbsSmall; assumption.
 ring_simplify. reflexivity.
Qed.

(* The multiplication of a bounded stream b by a stream a
   converging to 0 converges to 0. *)
Lemma mult_Streams_zl : forall (a b : Stream Q),
    (Limit a 0) -> forall (x:Qpos), NearBy 0 x b ->
                              Limit (mult_Streams a b) 0.
Proof.
 intros a b Ha x Hb e.
 assert (H:=Ha (e * (Qpos_inv x))%QposInf).
 generalize b Hb.
 clear b Hb.
 induction H; intros b Hb.
  left.
  abstract ( destruct e as [e|];[|apply ForAll_True];
             assert (Heq:proj1_sig e== proj1_sig ((e*Qpos_inv x)*x)%Qpos);[
    simpl; field; apply Qpos_nonzero
             |rewrite -> (NearBy_comp _ _ (ball_refl _ 0 (Qle_refl 0)) _ _ Heq );
              apply (mult_Streams_nbz H Hb)] ).
 right.
 simpl.
 rename H0 into IHExists.
 intros.
 apply (IHExists tt).
  apply Limit_tl; assumption.
 destruct Hb; assumption.
Defined.

(**
*** [StreamBounds]
[StreamBounds] says that one stream pointwise bounds the absolute value
of the other. *)
Definition StreamBounds (a b : Stream Q)
  := ForAll (fun (x:Stream (Q*Q)) => let (a,b):=(CoqStreams.hd x) in QAbsSmall a b)
            (zipWith pair a b).

(** If the bounding stream goes to 0, so does the bounded stream. *)
Lemma Stream_Bound_nbz : forall a b e, (StreamBounds a b) -> NearBy 0 e a -> NearBy 0 e b.
Proof.
 cofix Stream_Bound_nbz.
 intros a b e Hb Ha.
 constructor.
  destruct Hb as [[Hb1 Hb2] _].
  destruct e as [e|];[|constructor].
  destruct Ha as [[Ha1 Ha2] _].
  simpl in *.
  split.
   apply Qle_trans with (-(CoqStreams.hd a -0)).
    apply Qopp_le_compat.
    assumption.
   ring_simplify.
   assumption.
  apply Qle_trans with (CoqStreams.hd a - 0).
   ring_simplify.
   assumption.
  assumption.
 eapply Stream_Bound_nbz.
  destruct Hb as [_ Hb].
  change (StreamBounds (CoqStreams.tl a) (CoqStreams.tl b)) in Hb.
  apply Hb.
 destruct Ha as [_ Ha].
 assumption.
Qed.

Lemma Stream_Bound_zl : forall a b, (StreamBounds a b) -> Limit a 0 -> Limit b 0.
Proof.
 intros a b H Ha e.
 assert (Ha':=(Ha e)); clear Ha.
 generalize b H; clear b H.
 induction Ha'; intros b Hb.
  left.
  apply Stream_Bound_nbz with x; assumption.
 right.
 rename H0 into IHHa'.
 intros _.
 apply (IHHa' tt).
 destruct Hb; assumption.
Defined.

Section Qpowers.
Variable a : Q.

Hypothesis Ha : 0 <= a <= 1.

(** It is decreasing and nonnegative when a is between 0 and 1. *)
Lemma powers_help_dnn : forall x, (0 <= x) -> DecreasingNonNegative (powers_help a x).
Proof.
 intros x Hx.
 destruct Ha as [Ha0 Ha1].
 generalize x Hx; clear x Hx.
 cofix powers_help_dnn.
 intros b Hb.
 constructor.
  simpl.
  split.
  rewrite <- (Qmult_0_l a). apply Qmult_le_compat_r; assumption.
  rewrite Qmult_comm.
  rewrite <- (Qmult_1_l b) at 2.
  apply Qmult_le_compat_r. exact Ha1. exact Hb.
 apply powers_help_dnn.
 rewrite <- (Qmult_0_l a). apply Qmult_le_compat_r; assumption.
Qed.

Lemma powers_dnn : DecreasingNonNegative (powers a).
Proof.
 apply powers_help_dnn.
 discriminate.
Qed.

Lemma powers_help_nbz : forall x,
    0 <= x <= 1 -> NearBy 0 (Qpos2QposInf (1#1)) (powers_help a x).
Proof.
 cofix powers_help_nbz.
 intros b [Hb0 Hb1].
 destruct Ha as [Ha0 Ha1].
 constructor.
  simpl.
  unfold Qball.
  unfold QAbsSmall. setoid_replace (b-0)%Q with b.
  2: unfold Qminus; apply Qplus_0_r.
  split;simpl.
   apply Qle_trans with 0;[discriminate|assumption].
  assumption.
 simpl.
 apply powers_help_nbz.
 split.
 rewrite <- (Qmult_0_l a). apply Qmult_le_compat_r; assumption.
 apply (Qle_trans _ (1*a)).
 apply Qmult_le_compat_r; assumption.
 rewrite Qmult_1_l. exact Ha1.
Qed.

Lemma powers_nbz : NearBy 0 (Qpos2QposInf (1#1)) (powers a).
Proof.
 apply powers_help_nbz.
 split; discriminate.
Qed.
End Qpowers.

(**
*** [ppositives]
The stream of postive numbers (as positive).

We do not use [positives] because [positive] does not form a semiring.
*)
CoFixpoint ppositives_help (n:positive) : Stream positive :=
Cons n (ppositives_help (Pos.succ n)).

Definition ppositives := ppositives_help 1.

Lemma Str_nth_ppositives : forall n, Str_nth n ppositives ≡ P_of_succ_nat n.
Proof.
 intros n.
 unfold ppositives.
 apply nat_of_P_inj.
 rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
 change (S n) with ((nat_of_P 1) + n)%nat.
 generalize 1%positive.
 induction n.
  intros c.
  rewrite plus_comm.
  reflexivity.
 intros c.
 unfold Str_nth in *.
 simpl.
 rewrite IHn.
 rewrite nat_of_P_succ_morphism.
 apply plus_n_Sm.
Qed.

Lemma Str_nth_ppositives' n
  : inject_Z (Zpos (Str_nth n ppositives)) = Str_nth n positives.
Proof.
  rewrite Str_nth_ppositives, Str_nth_positives.
  rewrite Z.P_of_succ_nat_Zplus.
  rewrite <-(naturals.to_semiring_unique (Basics.compose inject_Z Z_of_nat)).
  unfold Basics.compose.
  rewrite <-(rings.preserves_1 (f:=inject_Z)).
  rewrite <-rings.preserves_plus.
  now rewrite commutativity.
Qed.

(**
*** [Qrecip_positives]
The stream of 1/n.
*)
Definition Qrecip_positives := CoqStreams.map (fun x => 1#x) ppositives.

Lemma Str_nth_Qrecip_positives : forall n, Str_nth n Qrecip_positives = 1#(P_of_succ_nat n).
Proof.
 intros n.
 unfold Qrecip_positives.
 rewrite Str_nth_map.
 rewrite Str_nth_ppositives.
 reflexivity.
Qed.

Lemma Str_nth_Qrecip_positives' n : Str_nth n Qrecip_positives = / Str_nth n positives.
Proof.
  unfold Qrecip_positives.
  rewrite Str_nth_map.
  rewrite Qmake_Qdiv.
  rewrite Str_nth_ppositives'.
  apply (left_identity (/ Str_nth n positives)).
Qed.

(** The limit of [recip_positives] is 0. *)
Lemma Qrecip_positives_help_nbz : forall (x: Qpos) (q:positive),
    (Zpos (Qden (proj1_sig x)) <= Zpos q)%Z
    -> NearBy 0 (Qpos2QposInf x) (CoqStreams.map (fun x => 1#x) (ppositives_help q)).
Proof.
  assert (∀ (q n d : positive),
    (Zpos d <= Zpos q)%Z
    → NearBy 0 (Qpos2QposInf (n # d)) (CoqStreams.map (λ x : positive, 1 # x) (ppositives_help q))).
 { cofix Qrecip_positives_help_nbz.
 intros q n d Hpq.
 constructor.
 - simpl.
   unfold Qball, QAbsSmall, Qminus.
   rewrite Qplus_0_r.
  split. discriminate.
  change (1*Zpos d <= Zpos n*Zpos q)%Z.
  apply Zmult_le_compat.
  apply Pos.le_1_l. exact Hpq.
  discriminate. discriminate.
 - apply Qrecip_positives_help_nbz.
 clear Qrecip_positives_help_nbz.
 rewrite Zpos_succ_morphism.
 apply (Z.le_trans _ _ _ Hpq).
 apply Z.le_succ_diag_r. }
 intros. destruct x as [[n d] xpos].
 destruct n as [|n|n]. inversion xpos. 2: inversion xpos.
 apply H. exact H0.
Qed.

Lemma Qrecip_positives_help_Exists : forall P n p, 
    LazyExists P (CoqStreams.map (fun x => (1#x)) (ppositives_help (Pplus_LazyNat p n)))
    -> LazyExists P (CoqStreams.map (fun x => (1#x)) (ppositives_help p)).
Proof.
 induction n; intros p H0.
  exact H0.
 right.
 intros _.
 apply (H tt).
 apply H0.
Defined.

Instance Qrecip_positives_zl : Limit Qrecip_positives 0.
 intros [[[n d] U] | ]; [| left; apply ForAll_True].
 unfold Qrecip_positives.
 unfold ppositives.
 apply Qrecip_positives_help_Exists with (LazyPred (LazyNat_of_P d)).
 left.
 abstract ( apply Qrecip_positives_help_nbz; induction d using Pind;[simpl;auto with *|];
   autorewrite with UnLazyNat in *; rewrite nat_of_P_succ_morphism; assert (H:=lt_O_nat_of_P d);
     destruct (nat_of_P d);[elimtype False;auto with *|]; simpl in *;
       replace (Pplus_LazyNat 2 (LazifyNat n0)) with (Pos.succ (Pplus_LazyNat 1 (LazifyNat n0)));[
         repeat rewrite Zpos_succ_morphism; auto with * |]; clear -n0;
           change 2%positive with (Pos.succ 1); generalize 1%positive;
             induction n0;intros p;[reflexivity|]; simpl in *; rewrite IHn0; reflexivity ).
Defined.

(** [recip_positives] is [DecreasingNonNegative]. *)
Instance Qrecip_positives_dnn : DecreasingNonNegative Qrecip_positives.
Proof.
 unfold Qrecip_positives.
 unfold ppositives.
 generalize (1%positive) at 2.
 cofix Qrecip_positives_dnn.
 intros p.
 constructor.
  simpl.
  split.
   discriminate.
  change (Zpos p <= Zpos (Pos.succ p))%Z.
  repeat rewrite Zpos_succ_morphism.
  auto with *.
 simpl.
 apply Qrecip_positives_dnn.
Qed.

(**
*** [pfactorials]
The stream of factorials as positives.

Again, we do not use [factorials] because [positive] does not form a semiring.
*)
CoFixpoint pfactorials_help (n c:positive) : Stream positive :=
Cons c (pfactorials_help (Pos.succ n) (n*c)).

Definition pfactorials := pfactorials_help 1 1.

Lemma Str_nth_pfactorials : forall n, nat_of_P (Str_nth n pfactorials) ≡ fact n.
Proof.
 unfold pfactorials.
 intros n.
 pose (ONE:=1%positive).
 replace (fact n) with ((nat_of_P 1)*fact (pred (nat_of_P ONE) + n))%nat by (simpl;auto).
 replace (nat_of_P (Str_nth n (pfactorials_help 1 1)))
   with ((fact (pred (nat_of_P ONE)))*(nat_of_P (Str_nth n (pfactorials_help ONE 1))))%nat by (simpl; auto with * ).
 change (pfactorials_help 1 1) with (pfactorials_help ONE 1).
 generalize ONE.
 generalize 1%positive.
 unfold ONE; clear ONE.
 induction n.
  intros a b.
  unfold Str_nth.
  simpl.
  rewrite plus_comm.
  now rewrite mult_comm.
 intros a b.
 unfold Str_nth in *.
 simpl.
 assert (X:=IHn (b*a)%positive (Pos.succ b)).
 clear IHn.
 rewrite nat_of_P_succ_morphism in X.
 rewrite <- plus_n_Sm.
 assert (forall (n m:nat), eq (Z_of_nat n) (Z_of_nat m) -> eq n m).
 { intros i j H. intuition. }
 apply H. clear H.
 apply Zmult_reg_l with (Z.of_nat (nat_of_P b));
   [rewrite positive_nat_Z; auto with *|].
 do 2 rewrite <- (inj_mult (nat_of_P b)).
 apply inj_eq.
 rewrite (Nat.mul_assoc (nat_of_P b) (nat_of_P a)).
 rewrite <- Pos2Nat.inj_mul.
 rewrite <- pred_Sn in X.
 change (S (pred (nat_of_P b) + n))%nat with (S (pred (nat_of_P b)) + n)%nat.
 assert (Z:S (pred (nat_of_P b)) = nat_of_P b).
 { apply (Nat.lt_succ_pred 0). apply Pos2Nat.is_pos. }
 rewrite Z.
 rewrite <- X.
 replace (fact (nat_of_P b)) with (fact (S (pred (nat_of_P b)))) by congruence.
 change (fact (S (pred (nat_of_P b)))) with ((S (pred (nat_of_P b)))*(fact (pred (nat_of_P b))))%nat.
 rewrite Z.
 ring.
Qed.

Lemma Str_nth_pfactorials' n
  : inject_Z (Zpos (Str_nth n pfactorials)) = Str_nth n factorials.
Proof.
  rewrite Str_nth_factorials.
  rewrite <-Str_nth_pfactorials.
  rewrite <-(naturals.to_semiring_unique (Basics.compose inject_Z Z_of_nat)).
  unfold Basics.compose.
  rewrite positive_nat_Z. reflexivity.
Qed.

(**
*** [Qrecip_factorials]
The stream of 1/n!.
**)
Definition Qrecip_factorials := CoqStreams.map (fun x => 1#x) pfactorials.

Lemma Str_nth_Qrecip_factorials : forall n, (Str_nth n Qrecip_factorials) = 1#(P_of_succ_nat (pred (fact n))).
Proof.
 intros n.
 unfold Qrecip_factorials.
 rewrite Str_nth_map.
 rewrite <- Str_nth_pfactorials.
 unfold equiv, stdlib_rationals.Q_eq, Qeq. simpl.
 apply f_equal.
 transitivity (Pos.of_nat (Pos.to_nat (Str_nth n pfactorials))).
 2: apply Pos2Nat.id. 
 destruct (Pos.to_nat (Str_nth n pfactorials)) eqn:des.
 2: apply Pos.of_nat_succ.
 exfalso. pose proof (Pos2Nat.is_pos (Str_nth n pfactorials)).
 rewrite des in H. inversion H.
Qed.

Lemma Str_nth_Qrecip_factorials' n : Str_nth n Qrecip_factorials = / Str_nth n factorials.
Proof.
  unfold Qrecip_factorials.
  rewrite Str_nth_map.
  rewrite Qmake_Qdiv.
  rewrite Str_nth_pfactorials'.
  now apply (left_identity (/ Str_nth n factorials)).
Qed.

(** [Qrecip_factorials] is [DecreasingNonNegative]. *)
Instance Qrecip_factorials_dnn : DecreasingNonNegative Qrecip_factorials.
Proof.
 unfold Qrecip_factorials.
 unfold pfactorials.
 generalize (1%positive) at 3. generalize (1%positive) at 2.
 cofix Qrecip_factorials_dnn.
 intros a b.
 constructor.
  simpl.
  split.
   discriminate.
  apply (Z.mul_le_mono_nonneg_r 1 (Zpos a) (Zpos b)).
  discriminate. apply Pos.le_1_l.
 simpl.
 apply Qrecip_factorials_dnn.
Qed.

(** The limit of [Qrecip_factorial] is 0. *)
Lemma Qrecip_factorial_bounded
  : StreamBounds Qrecip_positives (CoqStreams.tl Qrecip_factorials).
Proof.
 unfold Qrecip_positives, Qrecip_factorials, ppositives, pfactorials.
 cut (forall (p q:positive), StreamBounds (CoqStreams.map (fun x : positive => 1 # x) (ppositives_help p))
   (CoqStreams.tl (CoqStreams.map (fun x : positive => 1 # x) (pfactorials_help p q)))).
  intros H.
  apply (H 1%positive 1%positive).
 auto with *.
 cofix Qrecip_factorial_bounded.
 constructor.
  simpl.
  split.
   discriminate.
  change (Zpos p <= Zpos p * Zpos q)%Z.
  rewrite Z.mul_comm.
  apply (Z.mul_le_mono_nonneg_r 1 (Zpos q) (Zpos p)).
  discriminate. apply Pos.le_1_l.
 simpl in *.
 apply Qrecip_factorial_bounded.
Qed.

Instance Qrecip_factorials_zl : Limit Qrecip_factorials 0.
Proof.
 intros e.
 right.
 intros _.
 refine (Stream_Bound_zl _ _ _ _ _).
 apply Qrecip_factorial_bounded.
Defined.
