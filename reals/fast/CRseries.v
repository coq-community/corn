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

Require Import CRAlternatingSum.
Require Import CRGeometricSum.
Require Import Limit.
Require Import Qabs.
Require Import CornTac.
Require Import Arith.
Require Import Qordfield.
Require Import Qpower.
Require Import LazyNat.

Set Implicit Arguments.

Opaque Qabs.

(**
** Operations on Sequences
These are common operations on sequences that we will be using.
*** [everyOther]
*)

(** [everyOther] drops ever other term. *)
CoFixpoint everyOther (A:Type) (s:Stream A) : Stream A :=
Cons (hd s) (everyOther (tl (tl s))).

(** It preserves [DecreasingNonNegative]. *)
Lemma everyOther_dnn : forall (a : Stream Q),
 (DecreasingNonNegative a) ->  
 (DecreasingNonNegative (everyOther a)).
Proof.
intros a Ha.
rewrite <- dnn_alt_iff_dnn.
generalize a Ha; clear a Ha.
cofix.
intros [a [b [c [d x]]]] [[_ [_ [H0 _]]] [_ Ha]].
constructor;[assumption|].
rapply everyOther_dnn.
apply Ha.
Qed.

(** It preserves limits. *)
Lemma everyOther_nbz : forall (a : Stream Q) x, (NearBy 0 x a) ->
 NearBy 0 x (everyOther a).
cofix.
intros [a [b r]] x [H [_ Ha]].
constructor;[|rapply everyOther_nbz];assumption.
Qed.

Lemma everyOther_zl : forall (a : Stream Q), (Limit a 0) ->
 Limit (everyOther a) 0.
Proof.
intros x Hx e.
assert (H:=Hx e).
generalize x H; clear x Hx H.
fix 2.
intros x [H|H].
 left.
 apply everyOther_nbz.
 assumption.
case (H tt);[intros X |intros X].
 right; left.
 clear - x X.
 abstract (
 destruct x as [a [b x]];
 destruct X;
 rapply everyOther_nbz;
 assumption).
right; intros _.
rapply everyOther_zl.
apply X.
constructor.
Defined.

(** Its characterization. *)
Lemma Str_nth_tl_everyOther : forall n A (a:Stream A), Str_nth_tl n (everyOther a) = everyOther (Str_nth_tl (2*n) a).
Proof.
induction n.
 reflexivity.
intros A [a0 [a1 a]].
simpl.
rewrite IHn.
replace (n + S (n + 0))%nat with (S (2*n))%nat.
 reflexivity.
ring.
Qed.

Lemma Str_nth_everyOther : forall n A (a:Stream A), Str_nth n (everyOther a) = (Str_nth (2*n) a).
Proof.
intros n A a.
unfold Str_nth.
rewrite Str_nth_tl_everyOther.
destruct (Str_nth_tl (2 * n) a).
reflexivity.
Qed.

(**
*** [mult_Streams]
The point wise product of two streams.
*)
Definition mult_Streams := zipWith (Qmult).

(** It preserves convergeing to 0. *)
Lemma mult_Streams_nbz : forall (a b : Stream Q) x, (NearBy 0 x a) -> forall y, NearBy 0 y b ->
 NearBy 0 (x*y) (mult_Streams a b).
Proof.
unfold NearBy.
cofix.
intros a b x [Ha0 Ha] y [Hb0 Hb].
constructor;[|apply (mult_Streams_nbz (tl a) (tl b)); assumption].
destruct x as [x|];[|constructor].
destruct y as [y|];[|constructor].
simpl.
unfold Qball.
stepr ((hd a-0)*(hd b-0)) by (simpl;ring).
autorewrite with QposElim.
rapply mult_AbsSmall; assumption.
Qed.

Lemma ForAll_True : forall X (S:Stream X), ForAll (fun x => True) S.
Proof.
cofix.
intros.
constructor.
constructor.
auto.
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
abstract (
destruct e as [e|];[|rapply ForAll_True];
assert (Heq:e==((e*Qpos_inv x)*x)%Qpos);[
 autorewrite with QposElim;
 field;
 apply Qpos_nonzero
|rewrite (NearBy_comp _ 0 0 (Qeq_refl 0) Heq );
 apply (mult_Streams_nbz H Hb)]
).

right.
simpl.
rename H0 into IHExists.
intros.
apply (IHExists tt).
apply Limit_tl; assumption.
destruct Hb; assumption.
Defined.

(** It preserves [DecreasingNonNegative]. *)
Lemma mult_Streams_dnn : forall (a b : Stream Q),
 (DecreasingNonNegative a) ->  
 (DecreasingNonNegative b) ->
 (DecreasingNonNegative (mult_Streams a b)).
Proof.
intros a b.
repeat rewrite <- dnn_alt_iff_dnn.
generalize a b; clear a b.
cofix.
intros a b [[Ha1 Ha2] Ha'] [[Hb1 Hb2] Hb'].
constructor.
simpl.
split.
rsapply mult_resp_nonneg; assumption.
rsapply mult_resp_leEq_both; assumption.
simpl.
apply mult_Streams_dnn; assumption.
Qed.

(** 
*** [StreamBounds] 
[StreamBounds] says that one stream pointwise bounds the absolute value
of the other. *)
Definition StreamBounds (a b : Stream Q) := ForAll (fun (x:Stream (Q*Q)) => let (a,b):=(hd x) in AbsSmall a b) (zipWith Pair a b).

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
rapply Stream_Bound_nbz.
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
cofix.
intros a x y Hx Hy.
constructor.
 destruct Hy as [Hy _].
 destruct Hx as [[[Hx2 _] [[Hx0 Hx1] _]] _].
 simpl.
 rewrite Qabs_Qmult.
 apply Qle_trans with (Qabs (hd x) * Qabs (hd (tl y))).
  apply Qmult_le_compat_r.
   do 2 (rewrite Qabs_pos; try assumption).
  apply Qabs_nonneg.
 rewrite Qabs_Qmult.
 replace LHS with (Qabs (hd (tl y))*Qabs (hd x)) by ring.
 replace RHS with (a * (Qabs (hd y)) * Qabs (hd x)) by ring.
 apply Qmult_le_compat_r; try assumption.
 apply Qabs_nonneg.
rapply mult_Streams_Gs.
 destruct Hx; assumption.
destruct Hy; assumption.
Qed.

Section Powers.

Variable a : Q.
(**
*** [powers]
The stream of powers of a.
*)
CoFixpoint powers_help (c:Q) : Stream Q :=
Cons c (powers_help (c*a)).

Definition powers := powers_help 1.

Lemma Str_nth_powers_help : forall n x, Str_nth n (powers_help x) == x*a^n.
Proof.
induction n.

intros c.
unfold Str_nth.
simpl.
ring.

intros c.
unfold Str_nth in *.
rewrite inj_S.
simpl.

rewrite IHn.
unfold Zsucc.
destruct (Qeq_dec a 0).
rewrite q.
rewrite (Qpower_0 (n+1)).
auto with *.
ring.
rewrite Qpower_plus;[assumption|].
ring.
Qed.

Lemma Str_nth_powers : forall n, Str_nth n powers == a^n.
Proof.
intros n.
unfold powers.
rewrite Str_nth_powers_help.
ring.
Qed.

(** [powers] is a [GeometricSeries]. *)
Lemma powers_help_Gs : (0 <= a) -> forall c,
 (GeometricSeries a (powers_help c)).
intros Ha.
cofix.
intros c.
constructor.
 simpl.
 rewrite Qmult_comm.
 rewrite Qabs_Qmult.
 rewrite Qabs_pos; try assumption.
 apply Qle_refl.
rapply powers_help_Gs.
Qed.
 
Lemma powers_Gs : (0 <= a) -> (GeometricSeries a powers).
Proof.
intros Ha.
rapply (powers_help_Gs Ha).
Qed.

Hypothesis Ha : 0 <= a <= 1.

(** It is decreasing an nonnegative when a is between 0 and 1. *)
Lemma powers_help_dnn : forall x, (0 <= x) -> DecreasingNonNegative (powers_help x).
Proof.
intros x Hx.
destruct Ha as [Ha0 Ha1].
apply dnn_alt_dnn.
generalize x Hx; clear x Hx.
cofix.
intros b Hb.
constructor.
simpl.
split.
rsapply mult_resp_nonneg; assumption.
replace RHS with (b*1) by ring.
rsapply mult_resp_leEq_lft; assumption.

simpl.
apply powers_help_dnn.
rsapply mult_resp_nonneg; assumption.
Qed.

Lemma powers_dnn : DecreasingNonNegative powers.
Proof.
rapply powers_help_dnn.
discriminate.
Qed.

Lemma powers_help_nbz : forall x, 0 <= x <= 1 -> NearBy 0 (1#1)%Qpos (powers_help x).
Proof.
cofix.
intros b [Hb0 Hb1].
destruct Ha as [Ha0 Ha1].
constructor.
simpl.
unfold Qball.
stepr b by (simpl;ring).
split;simpl.
apply Qle_trans with 0;[discriminate|assumption].
assumption.

simpl.
apply powers_help_nbz.
split.
rsapply mult_resp_nonneg; assumption.
replace RHS with (1*1) by ring.
rsapply mult_resp_leEq_both; assumption.
Qed.

Lemma powers_nbz : NearBy 0 (1#1)%Qpos powers.
Proof.
rapply powers_help_nbz.
split; discriminate.
Qed.

End Powers.

(**
*** [positives]
The stream of postive numbers.
*)
CoFixpoint positives_help (n:positive) : Stream positive :=
Cons n (positives_help (Psucc n)).

Definition positives := positives_help 1.

Lemma Str_nth_positives : forall n, Str_nth n positives = P_of_succ_nat n.
Proof.
intros n.
unfold positives.
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
rapply plus_n_Sm.
Qed.

(**
*** [recip_positives]
The stream of 1/n.
*)
Definition recip_positives := map (fun x => 1#x) positives.

Lemma Str_nth_recip_positives : forall n, Str_nth n recip_positives = 1#(P_of_succ_nat n).
Proof.
intros n.
unfold recip_positives.
rewrite Str_nth_map.
rewrite Str_nth_positives.
reflexivity.
Qed.

(** The limit of [recip_positives] is 0. *)
Lemma recip_positives_help_nbz : forall (n d q:positive), (d <= q)%Z -> NearBy 0 (n#d)%Qpos (map (fun x => 1#x) (positives_help q)).
cofix.
intros n d q Hpq.
constructor.
simpl.
unfold Qball.
stepr (1#q) by (simpl;ring).
rapply (AbsSmall_leEq_trans _ (1#q)).
change (1*d <= n*q)%Z.
apply Zmult_le_compat; auto with *.
apply AbsSmall_reflexive.
discriminate.
rapply recip_positives_help_nbz.
rewrite Zpos_succ_morphism.
auto with *.
Qed.

Lemma recip_positives_help_Exists : forall P n p, LazyExists P (map (fun x => (1#x)) (positives_help (Pplus_LazyNat p n))) -> LazyExists P (map (fun x => (1#x)) (positives_help p)).
Proof.
induction n; intros p H0.
exact H0.

right.
intros _.
rapply (H tt).
apply H0.
Defined.

Lemma recip_positives_zl : Limit recip_positives 0.
Proof.
intros [[n d]|];[|left;rapply ForAll_True].
unfold recip_positives.
unfold positives.
apply recip_positives_help_Exists with (LazyPred (LazyNat_of_P d)).
left.

abstract (
apply recip_positives_help_nbz;
induction d using Pind;[simpl;auto with *|];
autorewrite with UnLazyNat in *;
rewrite nat_of_P_succ_morphism;
assert (H:=lt_O_nat_of_P d);
destruct (nat_of_P d);[elimtype False;auto with *|];
simpl in *;
replace (Pplus_LazyNat 2 (LazifyNat n0)) with (Psucc (Pplus_LazyNat 1 (LazifyNat n0)));[
 repeat rewrite Zpos_succ_morphism;
 auto with *
|];
clear -n0;
change 2%positive with (Psucc 1);
generalize 1%positive;
induction n0;intros p;[reflexivity|];
simpl in *;
rewrite IHn0;
reflexivity
).
Defined.

(** [recip_positives] is [DecreasingNonNegative]. *)
Lemma recip_positives_dnn : DecreasingNonNegative recip_positives.
Proof.
apply dnn_alt_dnn.
unfold recip_positives.
unfold positives.
cut (forall p, DecreasingNonNegative_alt
  (map (fun x : positive => 1 # x) (positives_help p))).
auto.
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
apply recip_positives_dnn.
Qed.

(**
*** [factorials]
The stream of factorials.
*)
CoFixpoint factorials_help (n c:positive) : Stream positive :=
Cons c (factorials_help (Psucc n) (n*c)).

Definition factorials := factorials_help 1 1.

Lemma Str_nth_factorials : forall n, nat_of_P (Str_nth n factorials) = fac n.
Proof.
unfold factorials.
intros n.
pose (ONE:=1%positive).
replace (fac n) with ((nat_of_P 1)*fac (pred (nat_of_P ONE) + n))%nat by (simpl;auto).
replace (nat_of_P (Str_nth n (factorials_help 1 1)))
 with ((fac (pred (nat_of_P ONE)))*(nat_of_P (Str_nth n (factorials_help ONE 1))))%nat by (simpl; auto with *).
change (factorials_help 1 1) with (factorials_help ONE 1).
generalize ONE.
generalize 1%positive.
unfold ONE; clear ONE.

induction n.
intros a b.
unfold Str_nth.
simpl.
rewrite plus_comm.
auto with *.

intros a b.
unfold Str_nth in *.
simpl.
assert (X:=IHn (b*a)%positive (Psucc b)).
clear IHn.
rewrite nat_of_P_succ_morphism in X.
rewrite <- plus_n_Sm.
apply surj_eq.
apply Zmult_reg_l with (nat_of_P b:Z);
 [rewrite inject_nat_convert; auto with *|].
do 2 rewrite <- (inj_mult (nat_of_P b)).
apply inj_eq.
rewrite (mult_assoc (nat_of_P b) (nat_of_P a)).
rewrite  <- nat_of_P_mult_morphism.
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
replace (fac (nat_of_P b)) with (fac (S (pred (nat_of_P b)))) by congruence.
change (fac (S (pred (nat_of_P b)))) with ((S (pred (nat_of_P b)))*(fac (pred (nat_of_P b))))%nat.
rewrite Z.
ring.
Qed.
(**
*** [recip_factorials]
The stream of 1/n!.
*)
Definition recip_factorials := map (fun x => 1#x) factorials.

Lemma Str_nth_recip_factorials : forall n, (Str_nth n recip_factorials) = 1#(P_of_succ_nat (pred (fac n))).
Proof.
intros n.
unfold recip_factorials.
rewrite Str_nth_map.
rewrite <- Str_nth_factorials.
rewrite <- anti_convert_pred_convert.
reflexivity.
Qed.

(** [recip_factorials] is [DecreasingNonNegative]. *)
Lemma recip_factorials_dnn : DecreasingNonNegative recip_factorials.
Proof.
unfold recip_factorials.
unfold factorials.
apply dnn_alt_dnn.
cut (forall a b, DecreasingNonNegative_alt
  (map (fun x : positive => 1 # x) (factorials_help a b))).
auto.
cofix.
intros a b.
constructor.
simpl.
split.
discriminate.
change (b <= a*b)%Z.
auto with *.

simpl.
apply recip_factorials_dnn.
Qed.

(** The limit of [recip_factorial] is 0. *)
Lemma recip_factorial_bounded : StreamBounds recip_positives (tl recip_factorials).
Proof.
unfold recip_positives, recip_factorials, positives, factorials.
cut (forall (p q:positive), StreamBounds (map (fun x : positive => 1 # x) (positives_help p))
  (tl (map (fun x : positive => 1 # x) (factorials_help p q)))).
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
apply recip_factorial_bounded.
Qed.

Lemma recip_factorials_zl : Limit recip_factorials 0.
Proof.
intros e.
right.
intros _.
rapply Stream_Bound_zl.
apply recip_factorial_bounded.
apply recip_positives_zl.
Defined.