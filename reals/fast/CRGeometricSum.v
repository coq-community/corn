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
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.reals.fast.CRAlternatingSum.
Require Import CoRN.reals.fast.CRstreams.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import CoRN.model.totalorder.QMinMax.
From Coq Require Import Qpower.
From Coq Require Import Qabs.
From Coq Require Import Zdiv.

Set Implicit Arguments.

Opaque Qabs.

Local Open Scope Q_scope.

Import MathClasses.theory.CoqStreams.

(** [InfiniteSum] approximates the limit of the series s within err_prop. *)
(* This Fixpoint is fat because the fuel is a unary nat,
   which can waste a lot of memory in normal form inside vm_compute. *)
Fixpoint InfiniteSum_fat (filter:Stream Q -> bool) (s:Stream Q) (q : Q) (fuel:nat) : Q
  := if filter s
     then q
     else match fuel with
          | O => q
          | S p => InfiniteSum_fat filter (tl s) (Qplus' q (hd s)) p
          end.

Definition InfiniteSum_raw_F (cont: Stream Q -> Q -> Q)
           (err_prop:Stream Q -> bool) (s:Stream Q) (q : Q) : Q :=
  if (err_prop s)
  then q (* the error is small enough, stop the sum *)
  else cont (tl s) (Qplus' q (hd s)). (* continue the calculations *)

(** Sum a rational stream up to the first index at which the filter
    Stream Q -> bool equals true, or 2^n.
    n is intended as a termination proof (fuel). It is otherwise useless
    for the calculations and we want it as small as possible in memory,
    because vm_compute will start by computing its normal form.
    By choosing 2^n we make the fuel logarithmic in the actual number of iterations.
    cont is a continuation that holds the rest of the computations
    to do in the recursion, it starts with fun _ q => q.
    This has the same calculation speed as InfiniteSum_fat, and
    should take less memory. *)
Fixpoint InfiniteSum_raw_N (n:nat) (filter: Stream Q -> bool)
         (cont: Stream Q -> Q -> Q) {struct n}
  : Stream Q -> Q -> Q :=
match n with
| O => InfiniteSum_raw_F cont filter
| S p => InfiniteSum_raw_N p filter (fun s => InfiniteSum_raw_N p filter cont s)
end.

(*
Remark : the eta expension here is important, else the virtual machine will
compute the value of (InfiniteGeometricSum_raw_N n') before
reducing the call of InfiniteGeometricSum_raw_F.*)

(* Get an idea of how the recursion goes. The continuation will
   unfold n layers deep, before being folded by additions. *)
Lemma InfiniteSum_raw_N_unfold : forall n cont (filter : Stream Q -> bool) s,
    InfiniteSum_raw_N (S (S n)) filter cont s
    = InfiniteSum_raw_N
        n filter (fun s0 => InfiniteSum_raw_N
                           n filter (fun s1 => InfiniteSum_raw_N
                                              (S n) filter cont s1) s0) s.
Proof.
  reflexivity.
Qed.

Lemma InfiniteSum_fat_plus
  : forall (fuel:nat) (filter:Stream Q -> bool) (s:Stream Q) (q : Q),
    InfiniteSum_fat filter s q fuel == q + InfiniteSum_fat filter s 0 fuel.
Proof.
  induction fuel.
  - intros. simpl. destruct (filter s); rewrite Qplus_0_r; reflexivity.
  - intros. simpl. destruct (filter s). symmetry. apply Qplus_0_r.
    rewrite IHfuel.
    rewrite (IHfuel filter (tl s) (Qplus' 0 (hd s))).
    rewrite Qplus_assoc. apply Qplus_comp. 2: reflexivity.
    rewrite Qplus'_correct, Qplus'_correct, Qplus_0_l. reflexivity.
Qed. 

Lemma InfiniteSum_fat_remove_filter
  : forall (fuel:nat) (filter:Stream Q -> bool) (s:Stream Q) (q : Q),
    filter (Str_nth_tl fuel s) = true
    -> exists n:nat, 
      InfiniteSum_fat filter s q fuel
      = InfiniteSum_fat (fun _ => false) s q n
      /\ (forall p:nat, lt p n -> filter (Str_nth_tl p s) = false)
      /\ filter (Str_nth_tl n s) = true.
Proof.
  induction fuel.
  - intros. exists O.
    split. 2: split. simpl. destruct (filter s); reflexivity.
    intros. exfalso; inversion H0. exact H.
  - intros. destruct (filter s) eqn:des.
    + exists O. split. 2: split. simpl. rewrite des. reflexivity.
      intros. exfalso; inversion H0. exact des.
    + specialize (IHfuel filter (tl s) (Qplus' q (hd s)) H) as [n [H1 H2]].
      exists (S n). split. 2: split.
      simpl. rewrite des. rewrite H1. reflexivity.
      intros. destruct p. exact des.
      simpl. apply H2. apply le_S_n in H0. exact H0.
      apply H2.
Qed.

Lemma InfiniteSum_fat_add_stop
  : forall (p n : nat) (s : Stream Q) (filter : Stream Q -> bool) (q : Q),
    le n p
    -> filter (Str_nth_tl n s) = true
    -> InfiniteSum_fat filter s q p
      = InfiniteSum_fat filter s q n.
Proof.
  induction p.
  - intros n s filter q H H0.
    inversion H. reflexivity.
  - intros n s filter q H H0.
    destruct n.
    + simpl in H0. simpl. rewrite H0. reflexivity.
    + specialize (IHp n (tl s) filter).
      simpl.
      destruct (filter s) eqn:des. reflexivity.
      rewrite IHp. reflexivity. apply le_S_n, H. exact H0.
Qed.

Lemma InfiniteSum_fat_extend
  : forall (n : nat) (s : Stream Q) (filter : Stream Q -> bool) (q : Q),
    filter (Str_nth_tl n s) = true
    -> InfiniteSum_fat filter s q n
      = InfiniteSum_fat filter s q (S n).
Proof.
  intros. symmetry. apply InfiniteSum_fat_add_stop.
  apply le_S, Nat.le_refl. exact H.
Qed. 

Lemma InfiniteSum_fat_add_pass
  : forall (n p : nat) (s : Stream Q) (filter : Stream Q -> bool) (q : Q),
    (forall k:nat, lt k n -> filter (Str_nth_tl k s) = false)
    -> InfiniteSum_fat filter s q (n+p)
      = InfiniteSum_fat
          filter (Str_nth_tl n s) (InfiniteSum_fat filter s q n) p.
Proof.
  induction n.
  - intros. simpl. 
    destruct (filter s); reflexivity.
  - intros.
    pose proof (H O (le_n_S 0 n (Nat.le_0_l _))) as zeroFalse.
    simpl in zeroFalse.
    simpl. rewrite zeroFalse.
    rewrite IHn. reflexivity.
    intros k H0. destruct n. exfalso; inversion H0. 
    apply Nat.le_succ_r in H0. destruct H0.
    apply (H (S k)), le_n_S, le_S, H0.
    inversion H0. subst k.
    apply (H (S n) (Nat.le_refl _)).
Qed. 

Lemma decide_filter_before_n
  : forall (n : nat) (filter : Stream Q -> bool) (s : Stream Q),
    (exists p:nat, lt p n /\ filter (Str_nth_tl p s) = true)
    \/ (forall p:nat, lt p n -> filter (Str_nth_tl p s) = false).
Proof.
  induction n.
  - intros. right.
    intros. exfalso. inversion H.
  - intros. destruct (filter (Str_nth_tl n s)) eqn:des.
    left. exists n. split. apply Nat.le_refl. exact des.
    destruct (IHn filter s).
    + left. destruct H as [p [H H0]]. exists p.
      split. apply le_S, H. exact H0.
    + right. intros.
      apply Nat.le_succ_r in H0. destruct H0. 
      apply H, H0. inversion H0. subst p. exact des.
Qed.

Lemma InfiniteSum_raw_N_step
  : forall (fuel : nat) c (filter : Stream Q -> bool) (s : Stream Q) (q : Q),
    (forall p:nat, p < 2 ^ fuel -> filter (Str_nth_tl p s) = false)%nat
    -> InfiniteSum_raw_N fuel filter c s q
      = c (Str_nth_tl (2^fuel) s)
          (InfiniteSum_raw_N fuel filter (fun _ r => r) s q).
Proof.
  induction fuel.
  - intros. simpl. unfold InfiniteSum_raw_F.
    destruct (filter s) eqn:des. 2: reflexivity.
    exfalso. specialize (H O (Nat.le_refl _)). simpl in H.
    rewrite H in des. discriminate.
  - intros. simpl.
    assert (forall p : nat, (p < 2 ^ fuel)%nat -> filter (Str_nth_tl p s) = false) as firstHalf.
    { intros. apply (H p).
      simpl. rewrite Nat.add_0_r.
      apply (Nat.lt_le_trans _ (0+2^fuel)).
      exact H0. apply Nat.add_le_mono_r, Nat.le_0_l. }
    rewrite IHfuel, IHfuel.
    3: exact firstHalf.
    rewrite Nat.add_0_r, Str_nth_tl_plus.
    apply f_equal. symmetry. apply IHfuel.
    exact firstHalf.
    intros. rewrite Str_nth_tl_plus. apply H.
    simpl. rewrite Nat.add_0_r.
    apply Nat.add_lt_mono_r, H0.
Qed.

(* The initial continuation is not reached when
   the filter is triggered before. *)
Lemma InfiniteSum_raw_N_cont_invariant
  : forall (fuel p : nat) c d (filter : Stream Q -> bool) (s : Stream Q) (q : Q),
    (p < 2 ^ fuel)%nat
    -> filter (Str_nth_tl p s) = true
    -> InfiniteSum_raw_N fuel filter c s q
      = InfiniteSum_raw_N fuel filter d s q.
Proof.
  induction fuel.
  - intros. simpl in H. simpl.
    unfold InfiniteSum_raw_F.
    destruct (filter s) eqn:des. reflexivity.
    apply le_S_n in H. inversion H.
    exfalso. subst p. simpl in H0.
    rewrite H0 in des. discriminate.
  - intros. simpl. simpl in H. rewrite Nat.add_0_r in H.
    destruct (decide_filter_before_n (2^fuel) filter s).
    destruct H1 as [k [H1 H2]]. apply (IHfuel k).
    exact H1. exact H2.
    (* Now 2^fuel <= p *)
    destruct (Nat.lt_ge_cases p (2^fuel)).
    exfalso. specialize (H1 p H2). rewrite H0 in H1. discriminate.
    apply Nat.le_exists_sub in H2.
    destruct H2 as [k [H2 _]]. subst p.
    rewrite <- Str_nth_tl_plus in H0. 
    rewrite (InfiniteSum_raw_N_step
               fuel (fun s0 : Stream Q => InfiniteSum_raw_N fuel filter c s0)).
    2: exact H1.
    rewrite (InfiniteSum_raw_N_step
               fuel (fun s0 : Stream Q => InfiniteSum_raw_N fuel filter d s0)).
    2: exact H1.
    apply (IHfuel k).
    apply Nat.add_lt_mono_r in H. exact H. exact H0.
Qed.

Lemma InfiniteSum_raw_N_correct
  : forall (fuel : nat) (s : Stream Q) (filter : Stream Q -> bool) (q : Q),
    InfiniteSum_raw_N fuel filter (fun _ r => r) s q
    = InfiniteSum_fat filter s q (2 ^ fuel)%nat.
Proof.
  induction fuel.
  - intros. simpl. unfold InfiniteSum_raw_F.
    destruct (filter s). reflexivity. simpl.
    destruct (filter (tl s)); reflexivity.
  - intros s filter q. simpl. rewrite Nat.add_0_r.
    destruct (decide_filter_before_n (2^fuel)%nat filter s).
    + destruct H as [p [H H0]].
      rewrite (@InfiniteSum_fat_add_stop _ p).
      3: exact H0.
      rewrite <- (@InfiniteSum_fat_add_stop (2^fuel)).
      2: apply (Nat.le_trans _ (S p) _ (le_S _ _ (Nat.le_refl p)) H).
      2: exact H0.
      rewrite <- IHfuel.
      apply (@InfiniteSum_raw_N_cont_invariant fuel p).
      exact H. exact H0.
      apply (Nat.le_trans _ (2^fuel + 0)).
      rewrite Nat.add_0_r.
      apply (Nat.le_trans _ (S p) _ (le_S _ _ (Nat.le_refl p)) H).
      apply Nat.add_le_mono_l, Nat.le_0_l.
    + rewrite InfiniteSum_fat_add_pass. 2: exact H.
      rewrite <- IHfuel. rewrite <- IHfuel.
      rewrite InfiniteSum_raw_N_step. reflexivity. exact H.
Qed.

Lemma InfiniteSum_raw_N_extend : forall (p q:nat) s (err : Stream Q -> bool) (r:Q),
 (Is_true (err (Str_nth_tl (2^p) s))) -> (p <= q)%nat ->
 InfiniteSum_raw_N p err (fun _ r => r) s r
 = InfiniteSum_raw_N q err (fun _ r => r) s r.
Proof.
  intros.
  rewrite InfiniteSum_raw_N_correct, InfiniteSum_raw_N_correct.
  symmetry. apply InfiniteSum_fat_add_stop.
  apply Nat.pow_le_mono_r. discriminate. exact H0.
  unfold Is_true in H.
  destruct (err (Str_nth_tl (2 ^ p) s)).
  reflexivity. contradiction.
Qed.

Lemma InfiniteSum_fat_minus
  : forall (i p : nat) (s : Stream Q) (q : Q),
    InfiniteSum_fat (fun _ => false) s q (p + i) -
    InfiniteSum_fat (fun _ => false) s q i
    == InfiniteSum_fat (fun _ => false) (Str_nth_tl i s) 0 p.
Proof.
  induction i.
  - intros. simpl. rewrite Nat.add_0_r.
    unfold Qminus. rewrite InfiniteSum_fat_plus.
    ring.
  - intros. rewrite Nat.add_succ_r. simpl.
    rewrite IHi. reflexivity.
Qed.

Lemma InfiniteSum_fat_wd
  : forall (fuel:nat) (filter:Stream Q -> bool) (s:Stream Q) (q r : Q),
    q == r
    -> InfiniteSum_fat filter s q fuel
      == InfiniteSum_fat filter s r fuel.
Proof.
  induction fuel.
  - intros. simpl. destruct (filter s); exact H.
  - intros. simpl. destruct (filter s). exact H.
    apply IHfuel. rewrite Qplus'_correct, Qplus'_correct.
    apply Qplus_comp. exact H. reflexivity.
Qed.

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

Lemma err_prop_prop : forall e s, err_prop e s = true <-> err_bound s <= e.
Proof.
 intros e s.
 unfold err_prop, err_bound, Qcompare, Qle, Z.le.
 destruct (Qnum (Qabs (hd s) / (1 - a))%Q * Zpos (Qden e) ?= Qnum e * Zpos (Qden (Qabs (hd s) / (1 - a))%Q))%Z;
   split; auto with *.
Qed.

Lemma err_prop_nonneg : forall e s, err_prop e s = true -> 0 <= e.
Proof.
  intros. apply err_prop_prop in H.
  refine (Qle_trans _ _ _ _ H).
  apply Qmult_le_0_compat. apply Qabs_nonneg.
  apply Qlt_le_weak, Qinv_lt_0_compat.
  unfold Qminus. rewrite <- Qlt_minus_iff. exact Ha1.
Qed.

(** The key lemma about error bounds. *)
Lemma err_prop_key : forall (e:Q) (s: Stream Q) (x:Q),
 err_prop e s = true -> Qabs x <= a*e -> Qabs (Qplus' (hd s) x) <= e.
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
 GeometricSeries s -> err_prop e s = true -> err_prop (a*e) (tl s) = true.
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

Lemma err_prop_monotone : forall (e0 e1:Q) (s: Stream Q),
    (e0 <= e1) -> err_prop e0 s = true -> err_prop e1 s = true.
Proof.
 intros e0 e1 s He H.
 rewrite ->  err_prop_prop in *.
 apply Qle_trans with e0; assumption.
Qed.

Lemma err_prop_monotone' : forall (e:Q) (s: Stream Q),
    GeometricSeries s -> err_prop e s = true -> err_prop e (tl s) = true.
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

(** If a geometric sum s is bounded by e,
    summing s to any index p is within bound e. *)
Lemma err_prop_correct : forall (p:nat) (e:Q) (s : Stream Q) (e':Stream Q -> bool),
    GeometricSeries s
    -> err_prop e s = true
    -> Qabs (InfiniteSum_fat e' s 0%Q p) <= e.
Proof.
  induction p.
  - intros. simpl. apply err_prop_nonneg in H0.
    destruct (e' s); exact H0.
  - intros. simpl.
    destruct (e' s). apply err_prop_nonneg in H0. exact H0.
    rewrite InfiniteSum_fat_plus.
    rewrite Qplus'_correct, Qplus_0_l.
    rewrite <-  Qplus'_correct.
    apply err_prop_key. exact H0.
    apply (IHp (a*e)). apply H.
    apply err_prop_key'; assumption.
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
 (InfiniteGeometricSum_maxIter (tl series) err
  <= InfiniteGeometricSum_maxIter series err)%positive.
Proof.
 intros series err Gs.
 unfold InfiniteGeometricSum_maxIter.
 cut ((Qabs (hd (tl series)) / (proj1_sig err * (1 - a) * (1 - a))) <=
      (Qabs (hd series) / (proj1_sig err * (1 - a) * (1 - a)))).
 - generalize (Qabs (hd (tl series)) / (proj1_sig err * (1 - a) * (1 - a)))
              (Qabs (hd series) / (proj1_sig err * (1 - a) * (1 - a))).
   intros [na da] [nb db] H.
   cut (Z.succ (na/Zpos da) <= Z.succ (nb/Zpos db))%Z.
   generalize (Z.succ (na / Zpos da)) (Z.succ (nb/Zpos db)).
   intros [|x|x] [|y|y] Hxy;
     try solve [apply Hxy | apply Qle_refl | elim Hxy; constructor
                | unfold Qle; simpl; repeat rewrite Pmult_1_r].
   apply Pos.le_1_l. discriminate.
   apply Pos.le_1_l. discriminate.
   apply Zsucc_le_compat.
   unfold Qle in H.
   simpl in H.
   rewrite <- (Zdiv_mult_cancel_r na (Zpos da) (Zpos db)).
   2: discriminate.
   rewrite <- (Zdiv_mult_cancel_r nb (Zpos db) (Zpos da)).
   2: discriminate.
   rewrite (Zmult_comm (Zpos db) (Zpos da)).
   apply Z_div_le. reflexivity. exact H.
 - assert (X:0 < 1 - a).
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

Lemma InfiniteGeometricSum_maxIter_correct
  : forall series (err:Qpos),
    GeometricSeries series ->
    err_prop (proj1_sig err) (Str_nth_tl (nat_of_P (InfiniteGeometricSum_maxIter series err)) series) = true.
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
     rewrite <- Z_div_mod_eq_full.
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
Definition InfiniteGeometricSum_fat series (e:QposInf) : Q :=
  match e with
  | QposInfinity => 0
  | Qpos2QposInf err => InfiniteSum_fat
                         (err_prop (proj1_sig err))
                         series 0%Q
                         (Pos.to_nat (InfiniteGeometricSum_maxIter series err))
  end.

Definition InfiniteGeometricSum_raw series (e:QposInf) : Q :=
  match e with
  | QposInfinity => 0
  | Qpos2QposInf err => InfiniteSum_raw_N
                         (Pos.to_nat (Pos.size (InfiniteGeometricSum_maxIter series err)))
                         (err_prop (proj1_sig err))
                         (fun _ r => r) series 0%Q 
  end.

Lemma InfiniteGeometricSum_raw_correct
  : forall (series : Stream Q) (e : QposInf),
    GeometricSeries series
    -> InfiniteGeometricSum_raw series e = InfiniteGeometricSum_fat series e.
Proof.
  assert (forall n:nat,
             lt 0 n -> Pos.of_nat (2 ^ n) = (2 ^ Pos.of_nat n)%positive) as inj_pow.
  { induction n.
    - intros. exfalso; inversion H.
    - intros _. destruct n. reflexivity.
      rewrite Nat2Pos.inj_succ. 2: discriminate.
      rewrite Pos.pow_succ_r.
      rewrite <- IHn. 2: apply le_n_S, Nat.le_0_l. clear IHn.
      generalize (S n). intro k.
      change (2 ^ S k)%nat with (2 * 2 ^ k)%nat.
      rewrite Nat2Pos.inj_mul. reflexivity. discriminate.
      apply Nat.pow_nonzero. discriminate. }
  intros. destruct e. 2: reflexivity.
  simpl. rewrite InfiniteSum_raw_N_correct.
  apply InfiniteSum_fat_add_stop.
  2: apply InfiniteGeometricSum_maxIter_correct, H.
  specialize (inj_pow (Pos.to_nat (Pos.size (InfiniteGeometricSum_maxIter series q)))
                      (Pos2Nat.is_pos _)).
  rewrite Pos2Nat.id in inj_pow. 
  rewrite <- Nat2Pos.id. rewrite inj_pow.
  apply Pos2Nat.inj_le.
  apply Pos.lt_le_incl, Pos.size_gt.
  apply Nat.pow_nonzero. discriminate.
Qed. 

(* Now we prove that bounds are correct when applied to tails
   of a geometric series at indexes p and p0. *)
Lemma err_prop_tail_correct : 
  forall (series : Stream Q) (e0 e1:Q) (p p0 : nat),
    GeometricSeries series
    -> e1 <= e0
    -> err_prop e0 (Str_nth_tl p series) = true
    -> err_prop e1 (Str_nth_tl p0 series) = true
    -> Qball e0
            (InfiniteSum_fat (err_prop e0) series 0%Q p)
            (InfiniteSum_fat (err_prop e1) series 0%Q p0).
Proof.
  intros series e0 e1 p0 p1 H He H0 H1.
  (* err_prop e1 implies err_prop e0 so the e1 sum is longer.
     Replace by the first indexes where the filters are triggered,
     the one of e1 being higher.
     The subtraction is a tail sum of e0 after the convergence index,
     so it is below e0. *)
  pose proof (@InfiniteSum_fat_remove_filter p0 (err_prop e0) series 0%Q)
    as [i [H2 H3]].
  exact H0. rewrite H2.
  pose proof (@InfiniteSum_fat_remove_filter p1 (err_prop e1) series 0%Q)
    as [j [H4 H5]].
  exact H1. rewrite H4.
  clear H4 H2 H1 H0 p0 p1. destruct H3. destruct H5.
  destruct (Nat.lt_ge_cases j i).
  - exfalso.
    specialize (H0 j H4).
    pose proof (err_prop_monotone (Str_nth_tl j series) He H3) as mon.
    rewrite mon in H0. discriminate.
  - unfold Qball.
    rewrite <- AbsSmall_Qabs, Qabs_Qminus.
    apply Nat.le_exists_sub in H4. destruct H4 as [p [H4 _]].
    subst j. clear H3 H2 He e1.
    rewrite InfiniteSum_fat_minus.
    apply err_prop_correct.
    2: exact H1.
    apply ForAll_Str_nth_tl, H.
Qed.

Lemma InfiniteGeometricSum_raw_prf : forall series,
    GeometricSeries series ->
    is_RegularFunction Qball (InfiniteGeometricSum_raw series).
Proof.
 intros series H e0 e1.
 rewrite InfiniteGeometricSum_raw_correct.
 rewrite InfiniteGeometricSum_raw_correct.
 2: exact H. 2: exact H. 
 pose proof (InfiniteGeometricSum_maxIter_correct e0 H) as H0.
 pose proof (InfiniteGeometricSum_maxIter_correct e1 H) as H1.
 destruct (Qle_total (proj1_sig e1) (proj1_sig e0)).
 - apply ball_weak. apply Qpos_nonneg.
   apply (err_prop_tail_correct _ _ H q H0 H1).
 - rewrite Qplus_comm.
   apply ball_weak. apply Qpos_nonneg.
   apply ball_sym.
   apply (err_prop_tail_correct _ _ H q H1 H0).
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
 apply regFunEq_equiv, regFunEq_e.
 intros e.
 change (approximate (InfiniteGeometricSum Gs) e)
   with (InfiniteGeometricSum_raw series e).
 rewrite InfiniteGeometricSum_raw_correct. 2: exact Gs. 
 simpl (InfiniteGeometricSum (ForAll_Str_nth_tl 1 Gs)).
 change (approximate
       (translate (hd series) (InfiniteGeometricSum (ForAll_Str_nth_tl 1 Gs))) e)
   with (hd series
         + (InfiniteGeometricSum_raw (tl series) e)).
 rewrite InfiniteGeometricSum_raw_correct. 2: apply Gs. 
 simpl.
 rewrite InfiniteSum_fat_extend.
 2: apply InfiniteGeometricSum_maxIter_correct, Gs.
 simpl.
 case_eq (err_prop (proj1_sig e) series); intros He.
 - apply ball_sym.
  simpl.
  unfold Qball.
  rewrite <- AbsSmall_Qabs.
  unfold Qminus. rewrite Qplus_0_r.
  eapply Qle_trans.
   apply Qabs_triangle.
  apply Qplus_le_compat; simpl.
   rewrite ->  err_prop_prop in He.
   unfold err_bound in He.
   assert (X:0 < 1 - a).
    change (0 < 1 + - a).
    rewrite <- Qlt_minus_iff.
    assumption.
   clear - He Ha0 X.
   setoid_replace (Qabs (hd series))
     with ((Qabs (hd series)/(1-a))*(1-a))
     by (unfold canonical_names.equiv, stdlib_rationals.Q_eq; simpl; field).
   2: auto with *.
   apply (Qle_trans _ ((proj1_sig e) * (1-a))).
   apply Qmult_le_compat_r. exact He.
   apply Qlt_le_weak, X.
   rewrite <- (Qmult_1_r (proj1_sig e)) at 2.
   apply Qmult_le_l. apply Qpos_ispos.
   rewrite <- (Qplus_0_r 1) at 2. apply Qplus_le_r.
   apply (Qopp_le_compat 0), Ha0.
  apply err_prop_correct.
    destruct Gs; assumption.
   apply err_prop_monotone'; assumption.
 - assert (Qplus' 0 (hd series) == hd series).
   { rewrite Qplus'_correct. apply Qplus_0_l. }
   rewrite (InfiniteSum_fat_wd _ _ _ H).
   rewrite InfiniteSum_fat_plus.
   rewrite (@InfiniteSum_fat_add_stop
              (Pos.to_nat (InfiniteGeometricSum_maxIter series e))
              (Pos.to_nat (InfiniteGeometricSum_maxIter (tl series) e))). 
   apply Qball_Reflexive.
   apply (Qpos_nonneg (e+e)). 
   apply Pos2Nat.inj_le.
   apply (@InfiniteGeometricSum_maxIter_monotone series e), Gs.
   apply InfiniteGeometricSum_maxIter_correct, Gs.
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
  apply regFunEq_equiv, regFunEq_e.
  intros e.
  apply ball_sym.
  change (approximate (InfiniteGeometricSum Gs) e)
    with (InfiniteGeometricSum_raw series e).
  rewrite InfiniteGeometricSum_raw_correct. 2: exact Gs. 
  simpl.
  unfold Qball.
  unfold QAbsSmall.
  setoid_replace (0 - InfiniteSum_fat (err_prop (proj1_sig e)) series 0
                                      (Pos.to_nat (InfiniteGeometricSum_maxIter series e)))%Q
    with 0.
  split. apply (Qopp_le_compat 0), (Qpos_nonneg (e+e)).
  apply (Qpos_nonneg (e+e)).
   unfold canonical_names.equiv, stdlib_rationals.Q_eq.
  unfold Qminus. rewrite Qplus_0_l.
  assert (X:err_prop (proj1_sig e) series = true).
   rewrite -> err_prop_prop.
   rewrite -> Hq.
   apply Qpos_nonneg.
  destruct  (InfiniteGeometricSum_maxIter series e) using Pind.
   simpl.
   destruct (err_prop (proj1_sig e) series).
   reflexivity. discriminate. 
   rewrite Pos2Nat.inj_succ.
   simpl.
   destruct (err_prop (proj1_sig e) series).
   reflexivity. discriminate.
 - cut (-(' err_bound series) <= InfiniteGeometricSum Gs
        /\ InfiniteGeometricSum Gs <= 'err_bound series)%CR.
   + intros [H0 H1].
     split; assumption.
   + setoid_replace (InfiniteGeometricSum Gs)
       with (InfiniteGeometricSum Gs - 0)%CR
       by (unfold canonical_names.equiv, msp_Equiv; ring).
     apply CRAbsSmall_ball.
     apply regFunBall_e.
     intros d.
     change (approximate (InfiniteGeometricSum Gs) d)
       with (InfiniteGeometricSum_raw series d).
     rewrite InfiniteGeometricSum_raw_correct. 2: exact Gs.
     simpl. 
     set (p:=(InfiniteGeometricSum_maxIter series d)).
     unfold Qball.
     rewrite <- AbsSmall_Qabs.
     unfold Qminus. rewrite Qplus_0_r.
     apply (err_prop_correct _ (proj1_sig d+err_bound series+proj1_sig d));
       try assumption.
     apply err_prop_monotone with (err_bound series).
     simpl.
     apply (Qle_trans _ (0 + err_bound series + 0)).
     rewrite Qplus_0_l, Qplus_0_r. apply Qle_refl.
     apply Qplus_le_compat. apply Qplus_le_compat.
     apply Qpos_nonneg. apply Qle_refl. apply Qpos_nonneg.
     rewrite -> err_prop_prop.
     apply Qle_refl.
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
    is_RegularFunction Qball (InfiniteGeometricSum_shift_raw s n Gs).
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
    msp_eq (InfiniteGeometricSum apos aone Gsa)
          (InfiniteGeometricSum bpos bone Gsb).
Proof.
  assert (forall (s : Stream Q) (a b : Q)
      (Gsa : GeometricSeries a s)
      (Gsb : GeometricSeries b s)
      (apos : 0 <= a) (aone : a < 1)
      (bpos : 0 <= b) (bone : b < 1),
    a <= b ->
    msp_eq (InfiniteGeometricSum apos aone Gsa)
          (InfiniteGeometricSum bpos bone Gsb)).
  { intros. 
    (* The same series is summed up to 2 different indexes,
       the distance is the sum between the lower and upper index.
       The upper index is associated to b, which corresponds to a
       slower geometric series. *)
    intros e1 e2.
    change (approximate (InfiniteGeometricSum apos aone Gsa) e1)
      with (InfiniteGeometricSum_raw a s e1).
    rewrite (InfiniteGeometricSum_raw_correct apos aone _ Gsa).
    change (approximate (InfiniteGeometricSum bpos bone Gsb) e2)
      with (InfiniteGeometricSum_raw b s e2).
    rewrite (InfiniteGeometricSum_raw_correct bpos bone _ Gsb).
    simpl.
    pose proof (@InfiniteSum_fat_remove_filter
                  (Pos.to_nat (InfiniteGeometricSum_maxIter a s e1))
                  (fun s0 : Stream Q =>
                     match Qabs (hd s0) / (1 - a) ?= proj1_sig e1 with
                     | Gt => false
                     | _ => true
                     end)
                  s 0%Q)
      as [i [H2 H3]].
    apply (InfiniteGeometricSum_maxIter_correct apos aone _ Gsa).
    rewrite H2.
    pose proof (@InfiniteSum_fat_remove_filter
                  (Pos.to_nat (InfiniteGeometricSum_maxIter b s e2))
                  (fun s0 : Stream Q =>
                     match Qabs (hd s0) / (1 - b) ?= proj1_sig e2 with
                     | Gt => false
                     | _ => true
                     end)
                  s 0%Q)
      as [j [H4 H5]].
    apply (InfiniteGeometricSum_maxIter_correct bpos bone _ Gsb).
    rewrite H4.
    destruct (Nat.lt_ge_cases i j) as [H0|H0].
    - rewrite Qplus_0_r.
      apply Nat.le_exists_sub in H0.
      destruct H0 as [k [H0 _]]. subst j.
      unfold Qball. clear H5.
      rewrite <- AbsSmall_Qabs, Qabs_Qminus.
      replace (k + S i)%nat with (S k + i)%nat
        by (rewrite Nat.add_succ_r; reflexivity).
      rewrite InfiniteSum_fat_minus.
      apply (Qle_trans _ (proj1_sig e1 + 0)).
      rewrite Qplus_0_r.
      apply (err_prop_correct apos aone).
      apply ForAll_Str_nth_tl, Gsa. apply H3.
      apply Qplus_le_r, Qpos_nonneg.
    - rewrite Qplus_0_r.
      apply Nat.le_exists_sub in H0.
      destruct H0 as [k [H0 _]]. subst i.
      unfold Qball. clear H3.
      rewrite <- AbsSmall_Qabs, Qabs_Qminus.
      rewrite Qabs_Qminus.
      rewrite InfiniteSum_fat_minus.
      apply (Qle_trans _ (0 + proj1_sig e2)).
      rewrite Qplus_0_l.
      apply (err_prop_correct bpos bone).
      apply ForAll_Str_nth_tl, Gsb. apply H5.
      apply Qplus_le_l, Qpos_nonneg. }
  intros. destruct (Qle_total a b).
  apply H, q. symmetry. apply H, q.
Qed.

