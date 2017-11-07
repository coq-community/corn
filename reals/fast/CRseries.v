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

Require Import Coq.Program.Program.
Require Import CoRN.reals.fast.CRAlternatingSum.
Require Import CoRN.reals.fast.CRGeometricSum.
Require Import CoRN.metric2.Limit.
Require Import Coq.QArith.Qabs. 
Require Import CoRN.tactics.CornTac.
Require Import Coq.Arith.Arith.
Require Import CoRN.model.ordfields.Qordfield.
Require Import Coq.QArith.Qpower.
Require Import CoRN.reals.fast.LazyNat. 
Require Import Coq.setoid_ring.Ring MathClasses.interfaces.abstract_algebra MathClasses.theory.streams.
Require Export MathClasses.theory.series.

Opaque Qabs.
Local Open Scope Q_scope.

(**
** Specific results for series on [Q]
*)

(** [everyOther] preserves limits. *)
Lemma everyOther_nbz : forall (s : Stream Q) x, (NearBy 0 x s) -> NearBy 0 x (everyOther s).
Proof.
 cofix.
 intros [s [b r]] x [H [_ Hs]].
 constructor;[|apply: everyOther_nbz];assumption.
Qed.

Instance everyOther_zl `{Hx : !Limit s 0} : Limit (everyOther s) 0.
Proof.
 intros e.
 assert (H:=Hx e). clear Hx.
 revert s H.
 fix 2.
 intros x [H|H].
  left.
  apply everyOther_nbz.
  assumption.
 case (H tt);[intros X |intros X].
  right; left.
  clear - x X.
  abstract ( destruct x as [a [b x]]; destruct X; apply: everyOther_nbz; assumption).
 right; intros _.
 apply: everyOther_zl.
 apply X.
 constructor.
Defined.

(** [mult_Streams] preserves convergeing to 0. *)
Lemma mult_Streams_nbz : forall {s1 s2 : Stream Q} {x}, (NearBy 0 x s1) -> forall {y}, NearBy 0 y s2 ->
 NearBy 0 (x*y) (mult_Streams s1 s2).
Proof.
 unfold NearBy.
 cofix.
 intros s1 s2 x [Ha0 Hs1] y [Hb0 Hs2].
 constructor;[|apply (mult_Streams_nbz (tl s1) (tl s2)); assumption].
 destruct x as [x|];[|constructor].
 destruct y as [y|];[|constructor].
 simpl.
 unfold Qball.
 stepr ((hd s1 - 0) * (hd s2 - 0)); [| now (simpl;ring_simplify; reflexivity)].
 autorewrite with QposElim.
 apply mult_AbsSmall; assumption.
Qed.

Lemma mult_Streams_zl : forall (a b : Stream Q), (Limit a 0) -> forall (x:Qpos), NearBy 0 x b ->
 Limit (mult_Streams a b) 0.
Proof.
 intros a b Ha x Hb e.
 assert (H:=Ha (e * (Qpos_inv x))%QposInf).
 generalize b Hb.
 clear b Hb.
 induction H; intros b Hb.
  left.
  abstract ( destruct e as [e|];[|apply ForAll_True]; assert (Heq:e==((e*Qpos_inv x)*x)%Qpos);[
    autorewrite with QposElim; field; apply Qpos_nonzero
      |rewrite -> (NearBy_comp _ _ (Qeq_refl 0) _ _ Heq ); apply (mult_Streams_nbz H Hb)] ).
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
Definition StreamBounds (a b : Stream Q) := ForAll (fun (x:Stream (Q*Q)) => let (a,b):=(hd x) in AbsSmall a b) (zipWith (@pair _ _) a b).

(** If the bounding stream goes to 0, so does the bounded stream. *)
Lemma Stream_Bound_nbz : forall a b e, (StreamBounds a b) -> NearBy 0 e a -> NearBy 0 e b.
Proof.
 cofix.
 intros a b e Hb Ha.
 constructor.
  destruct Hb as [[Hb1 Hb2] _].
  destruct e as [e|];[|constructor].
  destruct Ha as [[Ha1 Ha2] _].
  simpl in *.
  split.
   apply Qle_trans with (-(hd a -0)).
    apply Qopp_le_compat.
    assumption.
   ring_simplify.
   assumption.
  apply Qle_trans with (hd a - 0).
   ring_simplify.
   assumption.
  assumption.
 eapply Stream_Bound_nbz.
  destruct Hb as [_ Hb].
  change (StreamBounds (tl a) (tl b)) in Hb.
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

(** If one stream is [DecreasingNonNegative] and the other is
a [GeometricSeries], then the result is a [GeometricSeries]. *)
Lemma mult_Streams_Gs : forall a (x y  : Stream Q),
 (DecreasingNonNegative x) ->
 (GeometricSeries a y) ->
 (GeometricSeries a (mult_Streams x y)).
Proof.
 cofix.
 intros a x y Hx Hy.
 constructor.
  destruct Hy as [Hy _].
  apply dnn_alt in Hx.
  destruct Hx as [[[Hx2 _] [[Hx0 Hx1] _]] _].
  simpl.
  rewrite -> Qabs_Qmult.
  apply Qle_trans with (Qabs (hd x) * Qabs (hd (tl y))).
   apply Qmult_le_compat_r.
    do 2 (rewrite -> Qabs_pos; try assumption).
   apply Qabs_nonneg.
  rewrite -> Qabs_Qmult.
  replace LHS with (Qabs (hd (tl y))*Qabs (hd x)) by simpl; ring.
  replace RHS with (a * (Qabs (hd y)) * Qabs (hd x)) by simpl; ring.
  apply Qmult_le_compat_r; try assumption.
  apply Qabs_nonneg.
 apply: mult_Streams_Gs.
 now destruct Hy.
Qed.

Section Qpowers.
Variable a : Q.

(** [powers] is a [GeometricSeries]. *)
Lemma powers_help_Gs : (0 <= a) -> forall c,
 (GeometricSeries a (powers_help a c)).
Proof.
 intros Ha.
 cofix.
 intros c.
 constructor.
  simpl.
  rewrite -> Qmult_comm.
  rewrite -> Qabs_Qmult.
  rewrite -> (Qabs_pos a); try assumption.
  apply Qle_refl.
 apply: powers_help_Gs.
Qed.

Lemma powers_Gs : (0 <= a) -> (GeometricSeries a (powers a)).
Proof.
 intros Ha.
 apply (powers_help_Gs Ha).
Qed.

Hypothesis Ha : 0 <= a <= 1.

(** It is decreasing an nonnegative when a is between 0 and 1. *)
Lemma powers_help_dnn : forall x, (0 <= x) -> DecreasingNonNegative (powers_help a x).
Proof.
 intros x Hx.
 destruct Ha as [Ha0 Ha1].
 generalize x Hx; clear x Hx.
 cofix.
 intros b Hb.
 constructor.
  simpl.
  split.
   apply: mult_resp_nonneg; assumption.
  replace RHS with (b*1) by simpl; ring.
  apply: mult_resp_leEq_lft; assumption.
 simpl.
 apply powers_help_dnn.
 apply: mult_resp_nonneg; assumption.
Qed.

Lemma powers_dnn : DecreasingNonNegative (powers a).
Proof.
 apply powers_help_dnn.
 discriminate.
Qed.

Lemma powers_help_nbz : forall x, 0 <= x <= 1 -> NearBy 0 (1#1)%Qpos (powers_help a x).
Proof.
 cofix.
 intros b [Hb0 Hb1].
 destruct Ha as [Ha0 Ha1].
 constructor.
  simpl.
  unfold Qball.
  stepr b; [| now (simpl;ring)].
  split;simpl.
   apply Qle_trans with 0;[discriminate|assumption].
  assumption.
 simpl.
 apply powers_help_nbz.
 split.
  apply: mult_resp_nonneg; assumption.
 replace RHS with (1*1) by simpl; ring.
 apply: mult_resp_leEq_both; assumption.
Qed.

Lemma powers_nbz : NearBy 0 (1#1)%Qpos (powers a).
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
Cons n (ppositives_help (Psucc n)).

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

Lemma Str_nth_ppositives' n : (Str_nth n ppositives : Q) = Str_nth n positives.
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
Definition Qrecip_positives := map (fun x => 1#x) ppositives.

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
 (Qden x <= q)%Z -> NearBy 0 x (map (fun x => 1#x) (ppositives_help q)).
Proof.
 intro x.
 destruct (Qpos_as_positive_ratio x) as [[n d] U].
 subst.
 simpl.
 cofix.
 intros q Hpq.
 constructor.
  simpl.
  unfold Qball.
  stepr (1#q); [| now (simpl;ring)].
  apply (AbsSmall_leEq_trans _ (1#q)).
   change (1*d <= n*q)%Z.
   apply Zmult_le_compat; auto with *.
  apply AbsSmall_reflexive.
  discriminate.
 apply: Qrecip_positives_help_nbz.
 clear Qrecip_positives_help_nbz.
 rewrite Zpos_succ_morphism.
 auto with *.
Qed.

Lemma Qrecip_positives_help_Exists : forall P n p, 
  LazyExists P (map (fun x => (1#x)) (ppositives_help (Pplus_LazyNat p n))) -> LazyExists P (map (fun x => (1#x)) (ppositives_help p)).
Proof.
 induction n; intros p H0.
  exact H0.
 right.
 intros _.
 apply: (H tt).
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
       replace (Pplus_LazyNat 2 (LazifyNat n0)) with (Psucc (Pplus_LazyNat 1 (LazifyNat n0)));[
         repeat rewrite Zpos_succ_morphism; auto with * |]; clear -n0;
           change 2%positive with (Psucc 1); generalize 1%positive;
             induction n0;intros p;[reflexivity|]; simpl in *; rewrite IHn0; reflexivity ).
Defined.

(** [recip_positives] is [DecreasingNonNegative]. *)
Instance Qrecip_positives_dnn : DecreasingNonNegative Qrecip_positives.
Proof.
 unfold Qrecip_positives.
 unfold ppositives.
 generalize (1%positive) at 2.
 cofix.
 intros p.
 constructor.
  simpl.
  split.
   discriminate.
  change (p <= Psucc p)%Z.
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
Cons c (pfactorials_help (Psucc n) (n*c)).

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
 assert (X:=IHn (b*a)%positive (Psucc b)).
 clear IHn.
 rewrite nat_of_P_succ_morphism in X.
 rewrite <- plus_n_Sm.
 apply surj_eq.
 apply Zmult_reg_l with (nat_of_P b:Z); [rewrite inject_nat_convert; auto with *|].
 do 2 rewrite <- (inj_mult (nat_of_P b)).
 apply inj_eq.
 rewrite (mult_assoc (nat_of_P b) (nat_of_P a)).
 rewrite <- nat_of_P_mult_morphism.
 rewrite <- pred_Sn in X.
 change (S (pred (nat_of_P b) + n))%nat with (S (pred (nat_of_P b)) + n)%nat.
 assert (Z:S (pred (nat_of_P b)) = nat_of_P b).
  apply S_predn.
  intros H.
  symmetry in H.
  apply (lt_not_le _ _ (lt_O_nat_of_P b)).
  auto with *.
 rewrite Z.
 rewrite <- X.
 replace (fact (nat_of_P b)) with (fact (S (pred (nat_of_P b)))) by congruence.
 change (fact (S (pred (nat_of_P b)))) with ((S (pred (nat_of_P b)))*(fact (pred (nat_of_P b))))%nat.
 rewrite Z.
 ring.
Qed.

Lemma Str_nth_pfactorials' n : (Str_nth n pfactorials : Q) = Str_nth n factorials.
Proof.
  rewrite Str_nth_factorials.
  rewrite <-Str_nth_pfactorials.
  rewrite <-(naturals.to_semiring_unique (Basics.compose inject_Z Z_of_nat)).
  unfold Basics.compose.
  now rewrite inject_nat_convert.
Qed.

(**
*** [Qrecip_factorials]
The stream of 1/n!.
**)
Definition Qrecip_factorials := map (fun x => 1#x) pfactorials.

Lemma Str_nth_Qrecip_factorials : forall n, (Str_nth n Qrecip_factorials) = 1#(P_of_succ_nat (pred (fact n))).
Proof.
 intros n.
 unfold Qrecip_factorials.
 rewrite Str_nth_map.
 rewrite <- Str_nth_pfactorials.
 now rewrite <- anti_convert_pred_convert.
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
 cofix.
 intros a b.
 constructor.
  simpl.
  split.
   discriminate.
  change (b <= a*b)%Z.
  auto with *.
 simpl.
 apply Qrecip_factorials_dnn.
Qed.

(** The limit of [Qrecip_factorial] is 0. *)
Lemma Qrecip_factorial_bounded : StreamBounds Qrecip_positives (tl Qrecip_factorials).
Proof.
 unfold Qrecip_positives, Qrecip_factorials, ppositives, pfactorials.
 cut (forall (p q:positive), StreamBounds (map (fun x : positive => 1 # x) (ppositives_help p))
   (tl (map (fun x : positive => 1 # x) (pfactorials_help p q)))).
  intros H.
  apply (H 1%positive 1%positive).
 auto with *.
 cofix.
 constructor.
  simpl.
  split.
   discriminate.
  change (p <= p * q)%Z.
  auto with *.
 simpl in *.
 apply Qrecip_factorial_bounded.
Qed.

Instance Qrecip_factorials_zl : Limit Qrecip_factorials 0.
Proof.
 intros e.
 right.
 intros _.
 apply: Stream_Bound_zl.
 apply Qrecip_factorial_bounded.
Defined.
