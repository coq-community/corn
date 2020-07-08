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
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.reals.fast.CRAlternatingSum.
Require Import CoRN.reals.fast.CRstreams.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import CoRN.model.totalorder.QMinMax.
Require Import Coq.QArith.Qpower.
Require Import Coq.QArith.Qabs.
Require Import Coq.ZArith.Zdiv.

Set Implicit Arguments.

Opaque CR Qabs.

Local Open Scope Q_scope.

Import MathClasses.theory.CoqStreams.

(**
** Geometric Series
A geometric series is simple to sum.  However we do something slightly
more general.  We sum a series that satifies the ratio test. *)

Section GeometricSeries.
Variable a : Q.

Hypothesis Ha0 : 0 <= a.
Hypothesis Ha1 : a < 1.

(** The definition of what we are calling a [GeometricSeries]: a series
that satifies the ratio test. *)
Definition GeometricSeries := ForAll (fun s => Qabs ((hd (tl s))) <= a*(Qabs(hd s))).

(** [err_bound] majorates the distance between
    the head of the series and its limit. *)
Let err_bound (s:Stream Q) : Q := Qabs (hd s)/(1-a).

(** [err_prop]: is err a bound on the series s? *)
Let err_prop (err:Q) (s:Stream Q) : bool :=
match ((err_bound s) ?= err) with
 Gt => false
|_ => true
end.

(* begin hide *)
Local Coercion Is_true : bool >-> Sortclass.
(* end hide *)

Lemma err_prop_prop : forall e s, err_prop e s <-> err_bound s <= e.
Proof.
 intros e s.
 unfold err_prop, err_bound, Qcompare, Qle, Z.le.
 destruct (Qnum (Qabs (hd s) / (1 - a))%Q * Zpos (Qden e) ?= Qnum e * Zpos (Qden (Qabs (hd s) / (1 - a))%Q))%Z;
   split; auto with *.
Qed.

(** The key lemma bout error bounds. *)
Lemma err_prop_key : forall (e:Q) (s: Stream Q) (x:Q),
 err_prop e s -> Qabs x <= a*e -> Qabs (Qplus' (hd s) x) <= e.
Proof.
 intros e s x Hs Hx.
 rewrite -> Qplus'_correct.
 eapply Qle_trans.
  apply Qabs_triangle.
  setoid_replace e with (e*(1-a) + a*e)
    by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
 assert (X:0 < 1 - a).
  change (0 < 1 + - a).
  rewrite <- Qlt_minus_iff.
  assumption.
 apply Qplus_le_compat; try assumption.
 rewrite -> err_prop_prop in Hs.
 unfold err_bound in Hs.
 apply Qmult_lt_0_le_reg_r with (/(1-a)).
  apply Qinv_lt_0_compat; assumption.
  rewrite <- Qmult_assoc, Qmult_inv_r, Qmult_1_r.
  assumption.
 auto with *.
Qed.

Lemma err_prop_key' : forall (e:Q) (s: Stream Q),
 GeometricSeries s -> err_prop e s -> err_prop (a*e) (tl s).
Proof.
 intros e s [H _] Hs.
 rewrite -> err_prop_prop in *.
 unfold err_bound in *.
 rewrite -> Qle_minus_iff in H, Hs |- *.
 rewrite -> Qlt_minus_iff in Ha1.
 setoid_replace (a * e + - (Qabs (hd (tl s)) / (1 - a)))
   with (a * (e + - (Qabs (hd s)/(1-a)))+ (a * Qabs (hd s) + - Qabs (hd (tl s)))/(1+-a))
   by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; field).
 rewrite <- Qplus_0_r.
 apply Qplus_le_compat.
 apply Qmult_le_0_compat. exact Ha0. exact Hs.
 apply Qmult_le_0_compat. exact H.
 apply Qlt_le_weak, Qinv_lt_0_compat, Ha1.
 intro abs. rewrite abs in Ha1. exact (Qlt_irrefl 0 Ha1).
Qed.

Lemma err_prop_monotone : forall (e0 e1:Q) (s: Stream Q), (e0 <= e1) -> err_prop e0 s -> err_prop e1 s.
Proof.
 intros e0 e1 s He H.
 rewrite ->  err_prop_prop in *.
 apply Qle_trans with e0; assumption.
Qed.

Lemma err_prop_monotone' : forall (e:Q) (s: Stream Q), GeometricSeries s -> err_prop e s -> err_prop e (tl s).
Proof.
 intros e s Hs H.
 rewrite -> err_prop_prop in *.
 eapply Qle_trans;[|apply H].
 unfold err_bound.
 apply Qmult_le_r.
 - apply Qinv_lt_0_compat. unfold Qminus.
   rewrite <- Qlt_minus_iff. exact Ha1.
 - destruct Hs as [H0 _].
   eapply Qle_trans;[apply H0|].
   rewrite <- (Qmult_1_l (Qabs(hd s))) at 2.
   apply Qmult_le_compat_r.
   apply Qlt_le_weak, Ha1. apply Qabs_nonneg.
Qed.

(** [InfiniteSum] is sums the series s.

[InfiniteSum_raw_F] is the body of the fixpoint.  It tests the error of
the partial sum and bails out early if the error becomes small enough.
*)
Definition InfiniteSum_raw_F rec (err_prop:Stream Q -> bool) (s:Stream Q) : Q :=
if (err_prop s) then 0 else (Qplus' (hd s) (rec err_prop (tl s))).

(** By carefully using continuations, we can efficently compute n
iterations of [InfiniteSum_raw_F] with call-by-value. *)
Fixpoint InfiniteSum_raw_N (n:positive) (cont: (Stream Q -> bool) -> Stream Q -> Q) {struct n} : (Stream Q -> bool) -> Stream Q -> Q :=
match n with
| xH => InfiniteSum_raw_F cont
| xO n' => InfiniteSum_raw_N n' (fun err s => InfiniteSum_raw_N n' cont err s)
| xI n' => InfiniteSum_raw_F (fun err s =>
 (InfiniteSum_raw_N n' (fun err s => InfiniteSum_raw_N n' cont err s)) err s)
end.

(*
Remark : the eta expension here is important, else the virtual machine will
compute the value of (InfiniteGeometricSum_raw_N n') before
reducing the call of InfiniteGeometricSum_raw_F.*)

(** Lemmas for reasoning about InfiniteSum_raw_N. *)
Lemma InfiniteSum_raw_N_F : forall p c,
 InfiniteSum_raw_N p (fun err s => InfiniteSum_raw_F c err s) =
 InfiniteSum_raw_F (fun err s => InfiniteSum_raw_N p c err s).
Proof.
 induction p; intro c; try reflexivity; simpl; repeat rewrite IHp; reflexivity.
Qed.

Lemma InfiniteSum_raw_N_Psucc : forall p c,
 InfiniteSum_raw_N (Pos.succ p) c =
 InfiniteSum_raw_F (fun err s => InfiniteSum_raw_N p c err s).
Proof.
 intros p.
 induction p; intros c; try reflexivity.
 simpl in *.
 do 2 rewrite IHp.
 rewrite InfiniteSum_raw_N_F.
 reflexivity.
Qed.


Lemma InfiniteSum_raw_N_extend' : forall (p q:positive) s (err : Stream Q -> bool),
 (err (Str_nth_tl (nat_of_P p) s)) -> (Zpos p <= Zpos q)%Z ->
 InfiniteSum_raw_N p (fun _ _ => 0) err s = InfiniteSum_raw_N q (fun _ _ => 0) err s.
Proof.
 induction p using Pind.
  simpl.
  intros q s err H H0.
  destruct q using Pind.
   reflexivity.
  rewrite InfiniteSum_raw_N_Psucc.
  unfold InfiniteSum_raw_F.
  destruct (err s); try reflexivity.
  destruct q using Pind;[simpl|rewrite InfiniteSum_raw_N_Psucc]; (unfold InfiniteSum_raw_F;
    destruct (err (tl s));[reflexivity|contradiction]).
 intros q s err H H0.
 destruct q using Pind.
  elim (Pos.succ_discr p).
  apply Zpos_eq_rev.
  apply Zle_antisym.
   rewrite Pplus_one_succ_r.
   rewrite Zpos_plus_distr.
   auto with *.
  eapply Z.le_trans.
   apply H0.
  auto with *.
 do 2 rewrite InfiniteSum_raw_N_Psucc.
 unfold InfiniteSum_raw_F.
 destruct (err s); try reflexivity.
 do 2 rewrite Zpos_succ_morphism in H0.
 rewrite (IHp q); auto with *.
 rewrite nat_of_P_succ_morphism in H.
 assumption.
Qed.

Lemma InfiniteSum_raw_N_extend : forall (p:positive) s (err : Stream Q -> bool),
 (err (Str_nth_tl (nat_of_P p) s)) ->
 InfiniteSum_raw_N p (fun _ _ => 0) err s = InfiniteSum_raw_N (Pos.succ p) (fun _ _ => 0) err s.
Proof.
 intros.
 apply InfiniteSum_raw_N_extend'. assumption.
 rewrite Zpos_succ_morphism.
 auto with *.
Qed.

Lemma InfiniteSum_raw_N_ind : forall (err:Stream Q -> bool) (P:Stream Q -> Q -> Prop),
 (forall s, (err s) -> P s 0) ->
 (forall s rec, ~(err s) -> P (tl s) rec -> P s (Qplus' (hd s) rec)) ->
 forall (p:positive) s, (err (Str_nth_tl (nat_of_P p) s)) -> P s (InfiniteSum_raw_N p (fun err s => 0) err s).
Proof.
 intros err P H0 H1 p.
 induction p using Pind; intros s X.
  simpl.
  unfold InfiniteSum_raw_F.
  case_eq (err s); auto with *.
  intros C; apply H1; auto with *.
  destruct (err s); auto with *.
 rewrite InfiniteSum_raw_N_Psucc.
 unfold InfiniteSum_raw_F.
 case_eq (err s); auto with *.
 rewrite nat_of_P_succ_morphism in X.
 intros C; apply H1; auto with *.
 destruct (err s); auto with *.
Qed.

(** If a geometric sum s is bounded by e,
    summing s to any index p is within bound e. *)
Lemma err_prop_correct : forall (e:Qpos) (s : Stream Q) (p:positive) (e':Stream Q -> bool),
    GeometricSeries s
    -> (err_prop (proj1_sig e) s)
    -> (e' (Str_nth_tl (Pos.to_nat p) s))
    -> Qabs (InfiniteSum_raw_N p (fun err s => 0) e' s) <= proj1_sig e.
Proof.
 intros e s p e' gs H Z.
 assert (X:0<=proj1_sig e) by apply Qpos_nonneg.
 generalize (proj1_sig e) X H gs.
 clear e X H gs.
 set (P:=fun s q => forall e, 0 <= e -> err_prop e s -> GeometricSeries s -> Qabs q <= e).
 change (P s (InfiniteSum_raw_N p (fun (_ : Stream Q -> bool) (_ : Stream Q) => 0) e' s)).
 apply InfiniteSum_raw_N_ind; auto with *.
  intros s0 H0 e He ep gs0.
  assumption.
 unfold P in *.
 intros s0 rec _ Hrec e He H0 gs0.
 apply err_prop_key.
  assumption.
 apply Hrec.
   apply Qmult_le_0_compat; assumption.
  apply err_prop_key'; assumption.
 destruct gs0.
 assumption.
Qed.

(** This lemma tells us how to compute an upper bound on the number of
terms we will need to compute.  It is okay for this error to be loose
because the partial sums will bail out early when it sees that its
estimate of the error is small enough. *)
Lemma GeometricCovergenceLemma : forall (n:positive) (e:Qpos),
 /(proj1_sig e*(1 - a)) <= inject_Z (Zpos n) -> a^Zpos n <= proj1_sig e.
Proof.
 destruct (Qle_lt_or_eq _ _ Ha0) as [Ha0'|Ha0'].
 - intros n e H.
  assert (0 < a^Zpos n).
  { assert (X:0 < proj1_sig (Qpos_power (exist _ _ Ha0') (Zpos n))%Qpos)
      by auto with *.
   exact X. }
  apply Qmult_lt_0_le_reg_r with ((/proj1_sig e)*/(a^Zpos n)).
  apply (Qle_lt_trans _ (0 * (/a^Zpos n))).
  rewrite Qmult_0_l. apply Qle_refl.
  apply Qmult_lt_r.
    apply Qinv_lt_0_compat; exact H0.
   apply Qinv_lt_0_compat, Qpos_ispos.
  assert (0 < proj1_sig e) by (apply Qpos_ispos).
  rewrite (Qmult_assoc (proj1_sig e)), Qmult_inv_r, Qmult_1_l.
  2: apply Qpos_nonzero.
  setoid_replace (a ^ Zpos n * (/ proj1_sig e * / a ^ Zpos n))
    with (/proj1_sig e)
    by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; field).
  2: split. 2: apply Qpos_nonzero. 2: auto with *.
  rewrite -> Qlt_minus_iff in Ha1.
  change (0<1-a) in Ha1.
  rewrite -> Qle_minus_iff in H.
  apply Qle_trans with (1 + inject_Z (Zpos n) * (/a -1)).
   + rewrite -> Qle_minus_iff.
     setoid_replace (1 + inject_Z (Zpos n) * (/ a - 1) + - / proj1_sig e)
       with (1+(1 - a)*((inject_Z (Zpos n)*(1-a)*/a + (inject_Z (Zpos n) +-(/(proj1_sig e*(1 - a)))))))
       by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; field).
     2: split; auto with *.
     apply (Qle_trans _ (1+0)).
   discriminate. apply Qplus_le_r.
   repeat apply Qmult_le_0_compat; simpl; auto with *.
   assert (0 <= 1-a) by auto with *.
   apply (Qle_trans _ (0+0)). discriminate.
   apply Qplus_le_compat. 2: exact H.
   apply Qmult_le_0_compat.
   apply Qmult_le_0_compat. discriminate.
   exact H2. apply Qlt_le_weak, Qinv_lt_0_compat, Ha0'.
   + clear -n Ha0'.
     induction n using Pind.
     simpl.
     setoid_replace (1 + inject_Z 1 * (/ a - 1)) with (/a)
       by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
     apply Qle_refl.
     rewrite Zpos_succ_morphism.
     unfold Z.succ.
     rewrite -> Qpower_plus;[|auto with *].
     rewrite -> Qinv_mult_distr.
     rewrite -> Q.Zplus_Qplus.
     apply Qle_trans with ((1 + inject_Z (Zpos n) * (/ a - 1))*/a).
     rewrite -> Qle_minus_iff.
     setoid_replace ( (1 + inject_Z (Z.pos n) * (/ a - 1)) * / a +
  - (1 + (inject_Z (Z.pos n) + inject_Z 1) * (/ a - 1)))
       with (inject_Z (Zpos n)*(/a -1)^2)
       by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
     apply Qmult_le_0_compat. discriminate.
     unfold Qle. rewrite Z.mul_0_l. simpl.
     rewrite Z.mul_1_r. apply Z.square_nonneg.
     apply Qmult_le_compat_r.
     assumption.
     apply Qinv_le_0_compat; auto with *.
 - intros n e _.
   rewrite <- Ha0'.
   rewrite -> Qpower_0; auto with *.
Qed.

Definition InfiniteGeometricSum_maxIter series (err:Qpos) : positive :=
let x := (1-a) in
let (n,d) := (Qabs (hd series))/(proj1_sig err*x*x) in
match Z.succ (Z.div n (Zpos d)) with
| Zpos p => p
| _ => 1%positive
end.

Lemma InfiniteGeometricSum_maxIter_monotone : forall series (err:Qpos),
 GeometricSeries series ->
 (Zpos (InfiniteGeometricSum_maxIter (tl series) err)
  <= Zpos (InfiniteGeometricSum_maxIter series err))%Z.
Proof.
 intros series err Gs.
 unfold InfiniteGeometricSum_maxIter.
 cut ((Qabs (hd (tl series)) / (proj1_sig err * (1 - a) * (1 - a))) <=
   (Qabs (hd series) / (proj1_sig err * (1 - a) * (1 - a)))).
  generalize (Qabs (hd (tl series)) / (proj1_sig err * (1 - a) * (1 - a)))
    (Qabs (hd series) / (proj1_sig err * (1 - a) * (1 - a))).
  intros [na da] [nb db] H.
  cut (Z.succ (na/Zpos da) <= Z.succ (nb/Zpos db))%Z.
   generalize (Z.succ (na / Zpos da)) (Z.succ (nb/Zpos db)).
   intros [|x|x] [|y|y] Hxy; try solve [apply Hxy | apply Qle_refl | elim Hxy; constructor
     | unfold Qle; simpl; repeat rewrite Pmult_1_r; auto with *].
  apply Zsucc_le_compat.
  unfold Qle in H.
  simpl in H.
  rewrite <- (Zdiv_mult_cancel_r na (Zpos da) (Zpos db)); auto with *.
  rewrite <- (Zdiv_mult_cancel_r nb (Zpos db) (Zpos da)); auto with *.
  rewrite (Zmult_comm (Zpos db) (Zpos da)).
  apply Z_div_le; auto with *.
 assert (X:0 < 1 - a).
  change (0 < 1 + - a).
  rewrite <- Qlt_minus_iff.
  assumption.
 apply Qle_shift_div_l.
 apply (Qpos_ispos (err * (exist _ _ X) * (exist _ _ X))). 
  unfold Qdiv. rewrite <- Qmult_assoc.
  rewrite <- (Qmult_comm (proj1_sig err * (1 - a) * (1 - a))).
  rewrite Qmult_inv_r, Qmult_1_r. 
 destruct Gs as [H _].
 eapply Qle_trans.
  apply H.
 rewrite <- (Qmult_1_l (Qabs (hd series))) at 2.
 apply Qmult_le_compat_r.
 apply Qlt_le_weak, Ha1. apply Qabs_nonneg.
 apply (Qpos_nonzero (err * (exist _ _ X) * (exist _ _ X))).
Qed.

Lemma InfiniteGeometricSum_maxIter_correct : forall series (err:Qpos), GeometricSeries series ->
 err_prop (proj1_sig err) (Str_nth_tl (nat_of_P (InfiniteGeometricSum_maxIter series err)) series).
Proof.
 intros series err H.
 rewrite -> err_prop_prop.
 unfold err_bound.
 assert (X:0 < 1 - a).
  change (0 < 1 + - a).
  rewrite <- Qlt_minus_iff.
  assumption.
 apply Qle_shift_div_r; try assumption.
 assert (Y:(Qabs (hd series) * a ^ Zpos (InfiniteGeometricSum_maxIter series err)
            <= proj1_sig err * (1 - a))).
 { destruct (Qlt_le_dec 0 (Qabs (hd series))).
   apply Qmult_lt_0_le_reg_r with (/Qabs (hd series)).
    apply Qinv_lt_0_compat; assumption.
    rewrite (Qmult_comm (Qabs (hd series))), <- Qmult_assoc.
    rewrite Qmult_inv_r, Qmult_1_r.
    2: auto with *.
   cut (a ^ Zpos (InfiniteGeometricSum_maxIter series err)
        <= proj1_sig (err * exist _ _ X * Qpos_inv (exist _ _ q))%Qpos).
    autorewrite with QposElim; auto.
   apply GeometricCovergenceLemma.
   autorewrite with QposElim.
   unfold InfiniteGeometricSum_maxIter.
   simpl (/ (proj1_sig
     (err * exist (Qlt 0) (1 - a) X * Qpos_inv (exist (Qlt 0) (Qabs (hd series)) q))%Qpos * (1 - a))).
   setoid_replace (/ (proj1_sig err * (1 - a) * / Qabs (hd series) * (1 - a)))
     with (Qabs (hd series) / (proj1_sig err * (1 - a) * (1 - a)))
     by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; field).
   2: repeat split;auto with *;apply Qpos_nonzero.
   cut (0 < (Qabs (hd series) / (proj1_sig err * (1 - a) * (1 - a)))).
    generalize (Qabs (hd series) / (proj1_sig err * (1 - a) * (1 - a))).
    intros [n d] Hnd.
    apply Qle_trans with (inject_Z (Z.succ (n/Zpos d))).
     unfold Qle.
     simpl.
     unfold Z.succ.
     apply Zle_0_minus_le.
     replace ((n / Zpos d + 1) * Zpos d - n * 1)%Z
       with (Zpos d*(n/Zpos d) + n mod (Zpos d) - n mod (Zpos d) - n + Zpos d)%Z
       by ring.
     rewrite <- Z_div_mod_eq; auto with *.
     replace (n - n mod (Zpos d) - n + Zpos d)%Z
       with (Zpos d - n mod (Zpos d))%Z by ring.
     apply Zle_minus_le_0.
     destruct (Z_mod_lt n (Zpos d)); auto with *.
    generalize (Z.succ (n/Zpos d)).
    intros [|z|z].
      discriminate.
     apply Qle_refl.
    discriminate.
   cut (0 < proj1_sig ((exist _ _ q) * Qpos_inv(err * (exist _ _ X)*(exist _ _ X)))%Qpos).
    simpl; auto. 
   apply Q.Qmult_lt_0_compat; auto with *.
  setoid_replace (Qabs (hd series)) with 0.
   rewrite Qmult_0_l.
   apply (Qpos_nonneg (err * (exist _ _ X))).
  apply Qle_antisym; try assumption.
  apply Qabs_nonneg. }
 apply Qle_trans with (Qabs (hd series)*a^Zpos (InfiniteGeometricSum_maxIter series err)); try assumption.
 clear Y.
 generalize (InfiniteGeometricSum_maxIter series err).
 intros p.
 revert series H.
 induction p using Pind; intros series H.
  simpl.
  destruct H.
  rewrite -> Qmult_comm.
  assumption.
 rewrite nat_of_P_succ_morphism.
 rewrite Zpos_succ_morphism.
 unfold Z.succ.
 rewrite -> Qpower_plus';[|discriminate].
 rewrite Qmult_assoc.
 apply Qle_trans with (Qabs (hd (Str_nth_tl (nat_of_P p) series))*a).
  change (S (nat_of_P p)) with (1+(nat_of_P p))%nat.
  rewrite <- Str_nth_tl_plus.
  cut (GeometricSeries (Str_nth_tl (nat_of_P p) series)).
   generalize (Str_nth_tl (nat_of_P p) series).
   intros s [H0 _].
   rewrite -> Qmult_comm.
   assumption.
  clear -H.
  induction (nat_of_P p).
   auto.
  change (S n) with (1+n)%nat.
  rewrite <- Str_nth_tl_plus.
  simpl.
  destruct IHn; assumption.
 apply Qmult_le_compat_r; try assumption.
 apply IHp; assumption.
Qed.

(** The implemenation of [InfiniteGeometricSum]. *)
Definition InfiniteGeometricSum_raw series (e:QposInf) : Q :=
match e with
| QposInfinity => 0
| Qpos2QposInf err => InfiniteSum_raw_N (InfiniteGeometricSum_maxIter series err)
  (fun err s => 0) (err_prop (proj1_sig err)) series
end.

(* Now we prove that bounds are correct when applied to tails
   of a geometric series at indexes p and p0. *)
Lemma err_prop_correct_tail : 
  forall (series : Stream Q) (e0 e1:Qpos) (p p0 : positive),
    GeometricSeries series
    -> (proj1_sig e1 <= proj1_sig e0)
    -> err_prop (proj1_sig e0) (Str_nth_tl (nat_of_P p) series)
    -> err_prop (proj1_sig e1) (Str_nth_tl (nat_of_P p0) series)
    -> Qball (proj1_sig e0)
            (InfiniteSum_raw_N p (fun (_ : Stream Q -> bool) (_ : Stream Q) => 0)
                               (err_prop (proj1_sig e0)) series)
            (InfiniteSum_raw_N p0 (fun (_ : Stream Q -> bool) (_ : Stream Q) => 0)
                               (err_prop (proj1_sig e1)) series).
Proof.
  intros series e0 e1 p0 p1 H He H0.
  revert H.
  set (P0:=fun s q => GeometricSeries s ->
                   err_prop (proj1_sig e1) (Str_nth_tl (nat_of_P p1) s) -> Qball (proj1_sig e0) q (InfiniteSum_raw_N p1 (fun (_ : Stream Q -> bool) (_ : Stream Q) => 0)
                                                                                                                    (err_prop (proj1_sig e1)) s)).
  change (P0 series (InfiniteSum_raw_N p0 (fun (_ : Stream Q -> bool) (_ : Stream Q) => 0)
                                       (err_prop (proj1_sig e0)) series)).
  apply InfiniteSum_raw_N_ind; try assumption; unfold P0.
  - intros s Hs Gs H1.
    apply ball_sym;simpl.
    unfold Qball.
    rewrite <- AbsSmall_Qabs.
    unfold Qminus.
    rewrite -> Qplus_0_r.
    apply err_prop_correct; assumption.
  - intros s rec Hs Ind Gs H1.
    clear P0.
    rewrite InfiniteSum_raw_N_extend; try assumption.
    rewrite InfiniteSum_raw_N_Psucc.
    unfold InfiniteSum_raw_F.
    case_eq (err_prop (proj1_sig e1) s).
    intros H.
    elim Hs.
    apply err_prop_monotone with (proj1_sig e1); try assumption.
    destruct (err_prop (proj1_sig e1) s);[constructor | discriminate H].
    intros H.
    unfold Qball.
    rewrite <- AbsSmall_Qabs.
    repeat rewrite -> Qplus'_correct.
    set (x:=InfiniteSum_raw_N p1 (fun (_ : Stream Q -> bool) (_ : Stream Q) => 0) (err_prop (proj1_sig e1)) (tl s)) in *.
    set (Qplus' (hd s) rec - Qplus' (hd s) x).
    setoid_replace (hd s + rec - (hd s + x)) with (rec - x)
      by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
    rewrite -> AbsSmall_Qabs.
    apply Ind.
    destruct Gs; assumption.
    rewrite <- tl_nth_tl.
    apply err_prop_monotone'; try assumption.
    clear - Gs.
    induction p1 using Pind.
    destruct Gs; assumption.
    rewrite nat_of_P_succ_morphism.
    simpl.
    rewrite <- tl_nth_tl.
    destruct IHp1; assumption.
Qed.

Lemma InfiniteGeometricSum_raw_prf : forall series, GeometricSeries series ->
is_RegularFunction (InfiniteGeometricSum_raw series).
Proof.
 intros series H e0 e1.
 pose (InfiniteGeometricSum_maxIter series e0) as p0.
 pose (InfiniteGeometricSum_maxIter series e1) as p1.
 destruct (Qle_total (proj1_sig e1) (proj1_sig e0)).
 - apply ball_weak. apply Qpos_nonneg.
   apply (err_prop_correct_tail
            e0 e1 p0 p1 H q
            (InfiniteGeometricSum_maxIter_correct e0 H)
            (InfiniteGeometricSum_maxIter_correct e1 H)).
 - assert (QposEq (e0 + e1) (e1+e0)) by (unfold QposEq; simpl; ring).
   apply (ball_wd _ H0 _ _ (reflexivity _) _ _ (reflexivity _)). clear H0.
   apply ball_weak. apply Qpos_nonneg.
   apply ball_sym.
   apply (err_prop_correct_tail
            e1 e0 p1 p0 H q
            (InfiniteGeometricSum_maxIter_correct e1 H)
            (InfiniteGeometricSum_maxIter_correct e0 H)).
Qed.

Definition InfiniteGeometricSum series (Gs:GeometricSeries series) : CR :=
Build_RegularFunction (InfiniteGeometricSum_raw_prf Gs).

(** The [InfiniteGeometricSum] is correct. *)
Lemma InfiniteGeometricSum_step : forall series (Gs:GeometricSeries series),
 (InfiniteGeometricSum Gs ==
  ('(hd series))+(InfiniteGeometricSum (ForAll_Str_nth_tl 1%nat Gs)))%CR.
Proof.
 intros series Gs.
 rewrite -> CRplus_translate.
 apply regFunEq_e.
 intros e.
 simpl.
 rewrite InfiniteSum_raw_N_extend; [|apply InfiniteGeometricSum_maxIter_correct; assumption].
 rewrite InfiniteSum_raw_N_Psucc.
 unfold InfiniteSum_raw_F.
 case_eq (err_prop (proj1_sig e) series); intros He.
 - assert (He':err_prop (proj1_sig e) series).
  { destruct (err_prop (proj1_sig e) series);try discriminate He; constructor. }
  clear He.
  apply ball_sym.
  simpl.
  unfold Qball.
  rewrite <- AbsSmall_Qabs.
  ring_simplify (hd series + InfiniteSum_raw_N (InfiniteGeometricSum_maxIter (tl series) e)
    (fun (_ : Stream Q -> bool) (_ : Stream Q) => 0) (err_prop (proj1_sig e)) (tl series) - 0).
  eapply Qle_trans.
   apply Qabs_triangle.
  apply Qplus_le_compat; simpl.
   rewrite ->  err_prop_prop in He'.
   unfold err_bound in He'.
   assert (X:0 < 1 - a).
    change (0 < 1 + - a).
    rewrite <- Qlt_minus_iff.
    assumption.
   clear - He' Ha0 X.
   setoid_replace (Qabs (hd series))
     with ((Qabs (hd series)/(1-a))*(1-a))
     by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; field).
   2: auto with *.
   apply (Qle_trans _ ((proj1_sig e) * (1-a))).
   apply Qmult_le_compat_r. exact He'.
   apply Qlt_le_weak, X.
   rewrite <- (Qmult_1_r (proj1_sig e)) at 2.
   apply Qmult_le_l. apply Qpos_ispos.
   rewrite <- (Qplus_0_r 1) at 2. apply Qplus_le_r.
   apply (Qopp_le_compat 0), Ha0.
  apply err_prop_correct.
    destruct Gs; assumption.
   apply err_prop_monotone'; assumption.
  change (Is_true (err_prop (proj1_sig e)
    (Str_nth_tl (S (nat_of_P (InfiniteGeometricSum_maxIter (tl series) e))) series))).
  induction (S (nat_of_P (InfiniteGeometricSum_maxIter (tl series) e))).
   assumption.
  simpl.
  rewrite <- tl_nth_tl.
  apply err_prop_monotone'; try assumption.
  apply ForAll_Str_nth_tl.
  assumption.
 - rewrite -> Qplus'_correct.
 rewrite (@InfiniteSum_raw_N_extend' (InfiniteGeometricSum_maxIter (tl series) e)
   (InfiniteGeometricSum_maxIter series e)).
   apply ball_refl. apply (Qpos_nonneg (e+e)).
  apply InfiniteGeometricSum_maxIter_correct.
  destruct Gs; assumption.
 apply (@InfiniteGeometricSum_maxIter_monotone series e).
 assumption.
Qed.

Lemma InfiniteGeometricSum_bound : forall series
 (Gs:GeometricSeries series),
    (-'(err_bound series) <= InfiniteGeometricSum Gs
     /\ InfiniteGeometricSum Gs <= '(err_bound series))%CR.
Proof.
 intros series Gs.
 assert (Y:0 < 1 - a).
 { change (0 < 1 + - a).
  rewrite <- Qlt_minus_iff.
  assumption. }
 destruct (Qeq_dec (err_bound series) 0) as [Hq|Hq].
 - setoid_replace (InfiniteGeometricSum Gs) with 0%CR.
   split; simpl; rewrite -> Hq; try apply CRle_refl.
   rewrite CRopp_0. apply CRle_refl.
  apply regFunEq_e.
  intros e.
  apply ball_sym.
  simpl.
  unfold Qball.
  unfold QAbsSmall.
  setoid_replace (0 - InfiniteSum_raw_N (InfiniteGeometricSum_maxIter series e)
                                    (fun (_ : Stream Q -> bool) (_ : Stream Q) => 0) (err_prop (proj1_sig e)) series)
    with 0.
  split. apply (Qopp_le_compat 0), (Qpos_nonneg (e+e)).
  apply (Qpos_nonneg (e+e)).
  unfold Qminus. rewrite Qplus_0_l.
  assert (X:err_prop (proj1_sig e) series).
   rewrite -> err_prop_prop.
   rewrite -> Hq.
   apply Qpos_nonneg.
  destruct  (InfiniteGeometricSum_maxIter series e) using Pind.
   simpl.
   unfold InfiniteSum_raw_F.
   destruct (err_prop (proj1_sig e) series); try contradiction; reflexivity.
  rewrite InfiniteSum_raw_N_Psucc.
  unfold InfiniteSum_raw_F.
  destruct (err_prop (proj1_sig e) series); try contradiction; reflexivity.
 - assert (Herr:0 < err_bound series).
   { unfold err_bound.
     apply Qlt_shift_div_l.
     assumption.
     rewrite Qmult_0_l.
     destruct (Qle_lt_or_eq 0 (Qabs (hd series))).
     apply Qabs_nonneg.
     assumption.
     elim Hq.
     unfold err_bound.
     rewrite <- H.
     unfold Qdiv. apply Qmult_0_l. }
   set (e:=exist _ _ Herr).
   cut (-(' proj1_sig e) <= InfiniteGeometricSum Gs
        /\ InfiniteGeometricSum Gs <= 'proj1_sig e)%CR.
   + intros [H0 H1].
     unfold e in *.
     split; assumption.
   + setoid_replace (InfiniteGeometricSum Gs)
       with (InfiniteGeometricSum Gs - 0)%CR
       by (unfold canonical_names.equiv; ring).
     apply CRAbsSmall_ball.
     apply regFunBall_e.
     intros d.
     simpl.
     set (p:=(InfiniteGeometricSum_maxIter series d)).
     set (e':=(err_prop (proj1_sig d))).
     unfold Qball.
     rewrite <- AbsSmall_Qabs.
     setoid_replace (InfiniteSum_raw_N p (fun (_ : Stream Q -> bool) (_ : Stream Q) => 0) e'
                                       series - 0)
       with (InfiniteSum_raw_N p (fun (_ : Stream Q -> bool) (_ : Stream Q) => 0) e' series)
       by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; ring).
     apply (err_prop_correct (d+e+d)%Qpos); try assumption.
     apply err_prop_monotone with (proj1_sig e).
     simpl.
     apply (Qle_trans _ (0 + err_bound series + 0)).
     rewrite Qplus_0_l, Qplus_0_r. apply Qle_refl.
     apply Qplus_le_compat. apply Qplus_le_compat.
     apply Qpos_nonneg. apply Qle_refl. apply Qpos_nonneg.
     rewrite -> err_prop_prop.
     unfold e.
     apply Qle_refl.
     unfold e'.
     apply InfiniteGeometricSum_maxIter_correct.
     assumption.
Qed.

Lemma InfiniteGeometricSum_small_tail : forall series (e : Qpos),
GeometricSeries series ->
{n : nat & forall Gs : GeometricSeries (Str_nth_tl n series),
     (- ' proj1_sig e <= InfiniteGeometricSum Gs
      /\ InfiniteGeometricSum Gs <= 'proj1_sig e)%CR }.
Proof.
 intros series e.
 exists (nat_of_P (InfiniteGeometricSum_maxIter series e)).
 intros Gs.
 pose proof (InfiniteGeometricSum_bound Gs) as [H0 H1].
 split.
 refine (CRle_trans _ H0). apply CRopp_le_compat.
 rewrite ->  CRle_Qle.
 rewrite <- err_prop_prop.
 apply InfiniteGeometricSum_maxIter_correct.
 assumption.
 apply (CRle_trans H1).
 rewrite ->  CRle_Qle.
 rewrite <- err_prop_prop.
 apply InfiniteGeometricSum_maxIter_correct.
 assumption.
Qed.

End GeometricSeries.

(** If one stream is [DecreasingNonNegative] and the other is
a [GeometricSeries], then the result is a [GeometricSeries]. *)
Lemma mult_Streams_Gs : forall a (x y  : Stream Q),
 (DecreasingNonNegative x) ->
 (GeometricSeries a y) ->
 (GeometricSeries a (mult_Streams x y)).
Proof.
 cofix mult_Streams_Gs.
 intros a x y Hx Hy.
 constructor.
  destruct Hy as [Hy _].
  apply dnn_alt in Hx.
  destruct Hx as [[[Hx2 _] [[Hx0 Hx1] _]] _].
  simpl.
  rewrite -> Qabs_Qmult.
  apply Qle_trans
    with (Qabs (CoqStreams.hd x) * Qabs (CoqStreams.hd (CoqStreams.tl y))).
   apply Qmult_le_compat_r.
    do 2 (rewrite -> Qabs_pos; try assumption).
   apply Qabs_nonneg.
  rewrite -> Qabs_Qmult.
  rewrite Qmult_comm.
  rewrite (Qmult_comm (Qabs (CoqStreams.hd x))), Qmult_assoc.
  apply Qmult_le_compat_r; try assumption.
  apply Qabs_nonneg.
 destruct Hy.
 apply mult_Streams_Gs. 2: exact Hy.
 apply Hx.
Qed.

(** [powers] is a [GeometricSeries]. *)
Lemma powers_help_Gs (a : Q) : (0 <= a) -> forall c,
 (GeometricSeries a (powers_help a c)).
Proof.
 intros Ha.
 cofix powers_help_Gs.
 intros c.
 constructor.
  simpl.
  rewrite -> Qmult_comm.
  rewrite -> Qabs_Qmult.
  rewrite -> (Qabs_pos a); try assumption.
  apply Qle_refl.
 apply powers_help_Gs.
Qed.

Lemma powers_Gs (a : Q) : (0 <= a) -> (GeometricSeries a (powers a)).
Proof.
 intros Ha.
 apply (powers_help_Gs Ha).
Qed.

Definition InfiniteGeometricSum_shift_raw
           (s : Stream Q) (n : nat) {a : Q}
           (Gs : GeometricSeries a (Str_nth_tl n s))
           (e : QposInf) : Q
  := take s n Qplus' 0
     + InfiniteGeometricSum_raw a (Str_nth_tl n s) e.

Lemma InfiniteGeometricSum_raw_shift_prf
  : forall (s : Stream Q) (n : nat) {a : Q}
      (Gs : GeometricSeries a (Str_nth_tl n s)),
    0 <= a -> a < 1 ->
    is_RegularFunction (InfiniteGeometricSum_shift_raw s n Gs).
Proof.
  intros. intros e1 e2.
  apply AbsSmall_Qabs.
  unfold InfiniteGeometricSum_shift_raw.
  setoid_replace (take s n Qplus' 0 + InfiniteGeometricSum_raw a (Str_nth_tl n s) e1 -
              (take s n Qplus' 0 + InfiniteGeometricSum_raw a (Str_nth_tl n s) e2))
    with (InfiniteGeometricSum_raw a (Str_nth_tl n s) e1
          - InfiniteGeometricSum_raw a (Str_nth_tl n s) e2)
    by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; ring).
  apply AbsSmall_Qabs.
  apply (InfiniteGeometricSum_raw_prf H H0 Gs).
Qed.

Definition InfiniteGeometricSum_shift (s : Stream Q) (n : nat) (a : Q)
      (Gs : GeometricSeries a (Str_nth_tl n s))
      (apos : 0 <= a) (aone : a < 1) : CR
  := Build_RegularFunction (InfiniteGeometricSum_raw_shift_prf s n Gs apos aone).

(* Proof of correctness : the limit of the geometric series does not depend
   on the geometric ratio. *)
Lemma InfiniteGeometricSum_wd : forall (s : Stream Q) (a b : Q)
      (Gsa : GeometricSeries a s)
      (Gsb : GeometricSeries b s)
      (apos : 0 <= a) (aone : a < 1)
      (bpos : 0 <= b) (bone : b < 1),
    st_eq (InfiniteGeometricSum apos aone Gsa)
          (InfiniteGeometricSum bpos bone Gsb).
Proof.
Admitted.
