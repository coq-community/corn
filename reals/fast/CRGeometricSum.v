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
Require Import Qordfield.
Require Import QMinMax.
Require Import Qpossec.
Require Import Qpower.
Require Import Qauto.
Require Import Qabs.
Require Import CRcorrect.
Require Import CRIR.
Require Import iso_CReals.
Require Import Q_in_CReals.
Require Import Series.
Require Import Zdiv.
Require Import CornTac.

Set Implicit Arguments.

Opaque CR Qabs.

Open Local Scope Q_scope.

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

(** [err_bound] is a bound on how the series could be in terms of its
head elemement. *)
Let err_bound (s:Stream Q) : Q := Qabs (hd s)/(1-a).

(** [err_prop]: is err an bound on the series s? *)
Let err_prop (err:Q) (s:Stream Q) : bool :=
match ((err_bound s) ?= err) with
 Gt => false
|_ => true
end.

(* begin hide *)
Coercion Local Is_true : bool >-> Sortclass.
(* end hide *)

Lemma err_prop_prop : forall e s, err_prop e s <-> err_bound s <= e.
Proof.
 intros e s.
 unfold err_prop, err_bound, Qcompare, Qle, Zle.
 destruct (Qnum (Qabs (hd s) / (1 - a))%Q * Qden e ?= Qnum e * Qden (Qabs (hd s) / (1 - a))%Q)%Z;
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
 stepr (e*(1-a) + a*e); [| simpl; ring].
 assert (X:0 < 1 - a).
  change (0 < 1 + - a).
  rewrite <- Qlt_minus_iff.
  assumption.
 apply: plus_resp_leEq_both; try assumption.
 rewrite -> err_prop_prop in Hs.
 unfold err_bound in Hs.
 apply Qmult_lt_0_le_reg_r with (/(1-a)).
  apply Qinv_lt_0_compat; assumption.
 replace RHS with (e:Q).
  assumption.
 simpl.
 field.
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
 replace RHS with (a * (e + - (Qabs (hd s)/(1-a)))+ (a * Qabs (hd s) + - Qabs (hd (tl s)))/(1+-a)).
  Qauto_nonneg.
 simpl.
 field.
 auto with *.
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
 apply: mult_resp_leEq_rht.
  destruct Hs as [H0 _].
  eapply Qle_trans;[apply H0|].
  stepr (1*Qabs(hd s)); [| simpl; ring].
  apply: mult_resp_leEq_rht; auto with *.
  apply Qabs_nonneg.
 apply Qinv_le_0_compat.
 unfold Qminus.
 rewrite <- Qle_minus_iff.
 auto with *.
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
 InfiniteSum_raw_N p (fun err s => InfiniteSum_raw_F c err s)=
 InfiniteSum_raw_F (fun err s => InfiniteSum_raw_N p c err s).
Proof.
 induction p; intro c; try reflexivity; simpl; repeat rewrite IHp; reflexivity.
Qed.

Lemma InfiniteSum_raw_N_Psucc : forall p c,
 InfiniteSum_raw_N (Psucc p) c =
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
 (err (Str_nth_tl (nat_of_P p) s)) -> (p <= q)%Z ->
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
  elim (Psucc_discr p).
  apply Zpos_eq_rev.
  apply Zle_antisym.
   rewrite Pplus_one_succ_r.
   rewrite Zpos_plus_distr.
   auto with *.
  eapply Zle_trans.
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
 InfiniteSum_raw_N p (fun _ _ => 0) err s = InfiniteSum_raw_N (Psucc p) (fun _ _ => 0) err s.
Proof.
 intros.
 apply InfiniteSum_raw_N_extend'; auto with *.
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

(** The infinite sum is indeed bounded by an error bound. *)
Lemma err_prop_correct : forall (e:Qpos) s, (GeometricSeries s) -> (err_prop e s) ->
 forall (p:positive) (e':Stream Q -> bool),
  (e' (Str_nth_tl (nat_of_P p) s)) -> Qabs (InfiniteSum_raw_N p (fun err s => 0) e' s) <= e.
Proof.
 intros e s gs H p e' Z.
 assert (X:0<=e) by apply Qpos_nonneg.
 generalize (QposAsQ e) X H gs.
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
   apply: mult_resp_nonneg; assumption.
  apply err_prop_key'; assumption.
 destruct gs0.
 assumption.
Qed.

(** This lemma tells us how to compute an upper bound on the number of
terms we will need to compute.  It is okay for this error to be loose
because the partial sums will bail out early when it sees that its
estimate of the error is small enough. *)
Lemma GeometricCovergenceLemma : forall (n:positive) (e:Qpos),
 /(e*(1 - a)) <= n -> a^n <= e.
Proof.
 destruct (Qle_lt_or_eq _ _ Ha0) as [Ha0'|Ha0'].
  intros n e H.
  assert (0 < a^n).
   assert (X:0 < ((mkQpos Ha0')^n)%Qpos) by auto with *.
   autorewrite with QposElim in X.
   assumption.
  apply Qmult_lt_0_le_reg_r with ((/e)*/(a^n)).
   apply: mult_resp_pos.
    apply Qinv_lt_0_compat; auto with *.
   apply Qinv_lt_0_compat.
   assumption.
  assert (0 <e) by auto with *.
  stepr (/a^n); [| simpl; field; split; auto with *].
  stepl (/e); [| simpl; field; split; auto with *].
  rewrite -> Qlt_minus_iff in Ha1.
  change (0<1-a) in Ha1.
  rewrite -> Qle_minus_iff in H.
  apply Qle_trans with (1 + n*(/a -1)).
   rewrite -> Qle_minus_iff.
   stepr (1+(1 - a)*((n*(1-a)*/a + (n +-(/(e*(1 - a))))))); [| simpl; field; split; auto with *].
   apply: plus_resp_nonneg; try discriminate.
   repeat apply: mult_resp_nonneg; simpl; auto with *.
   assert (0 <= 1-a) by auto with *.
   Qauto_nonneg.
  clear -n Ha0'.
  induction n using Pind.
   simpl.
   stepl (/a); [| simpl; ring].
   apply Qle_refl.
  rewrite Zpos_succ_morphism.
  unfold Zsucc.
  rewrite -> Qpower_plus;[|auto with *].
  rewrite -> Qinv_mult_distr.
  rewrite -> injz_plus.
  apply Qle_trans with ((1 + n * (/ a - 1))*/a).
   rewrite -> Qle_minus_iff.
   stepr (n*(/a -1)^2); [| simpl; ring].
   Qauto_nonneg.
  apply: mult_resp_leEq_rht.
   assumption.
  apply Qinv_le_0_compat; auto with *.
 intros n e _.
 rewrite <- Ha0'.
 rewrite -> Qpower_0; auto with *.
Qed.

Definition InfiniteGeometricSum_maxIter series (err:Qpos) : positive :=
let x := (1-a) in
let (n,d) := (Qabs (hd series))/(err*x*x) in
match Zsucc (Zdiv n d) with
| Zpos p => p
| _ => 1%positive
end.

Lemma InfiniteGeometricSum_maxIter_monotone : forall series (err:Qpos),
 GeometricSeries series ->
 (InfiniteGeometricSum_maxIter (tl series) err <= InfiniteGeometricSum_maxIter series err)%Z.
Proof.
 intros series err Gs.
 unfold InfiniteGeometricSum_maxIter.
 cut ((Qabs (hd (tl series)) / (err * (1 - a) * (1 - a))) <=
   (Qabs (hd series) / (err * (1 - a) * (1 - a)))).
  generalize (Qabs (hd (tl series)) / (err * (1 - a) * (1 - a)))
    (Qabs (hd series) / (err * (1 - a) * (1 - a))).
  intros [na da] [nb db] H.
  cut (Zsucc (na/da) <= Zsucc (nb/db))%Z.
   generalize (Zsucc (na / da)) (Zsucc (nb/db)).
   intros [|x|x] [|y|y] Hxy; try solve [apply Hxy | apply Qle_refl | elim Hxy; constructor
     | unfold Qle; simpl; repeat rewrite Pmult_1_r; auto with *].
  apply Zsucc_le_compat.
  unfold Qle in H.
  simpl in H.
  rewrite <- (Zdiv_mult_cancel_r na da db); auto with *.
  rewrite <- (Zdiv_mult_cancel_r nb db da); auto with *.
  rewrite (Zmult_comm db da).
  apply Z_div_le; auto with *.
 assert (X:0 < 1 - a).
  change (0 < 1 + - a).
  rewrite <- Qlt_minus_iff.
  assumption.
 apply Qle_shift_div_l.
  Qauto_pos.
 stepl (Qabs (hd (tl series))); [| simpl; field;split; auto with *; apply Qpos_nonzero].
 destruct Gs as [H _].
 eapply Qle_trans.
  apply H.
 stepr (1*Qabs (hd series)); [| simpl; ring].
 apply: mult_resp_leEq_rht;simpl; auto with *.
Qed.

Lemma InfiniteGeometricSum_maxIter_correct : forall series (err:Qpos), GeometricSeries series ->
 err_prop err (Str_nth_tl (nat_of_P (InfiniteGeometricSum_maxIter series err)) series).
Proof.
 intros series err H.
 rewrite -> err_prop_prop.
 unfold err_bound.
 assert (X:0 < 1 - a).
  change (0 < 1 + - a).
  rewrite <- Qlt_minus_iff.
  assumption.
 apply Qle_shift_div_r; try assumption.
 assert (Y:(Qabs (hd series) * a ^ InfiniteGeometricSum_maxIter series err <= err * (1 - a))).
  destruct (Qlt_le_dec 0 (Qabs (hd series))).
   apply Qmult_lt_0_le_reg_r with (/Qabs (hd series)).
    apply Qinv_lt_0_compat; assumption.
   stepl (a ^ InfiniteGeometricSum_maxIter series err); [| simpl; field; auto with *].
   cut (a ^ InfiniteGeometricSum_maxIter series err <= (err * mkQpos X / mkQpos q)%Qpos).
    autorewrite with QposElim; auto.
   apply GeometricCovergenceLemma.
   autorewrite with QposElim.
   unfold InfiniteGeometricSum_maxIter.
   stepl (Qabs (hd series) / (err * (1 - a) * (1 - a))); [| simpl;
     (field;repeat split;auto with *;apply Qpos_nonzero)].
   cut (0 < (Qabs (hd series) / (err * (1 - a) * (1 - a)))).
    generalize (Qabs (hd series) / (err * (1 - a) * (1 - a))).
    intros [n d] Hnd.
    apply Qle_trans with (Zsucc (n/d)).
     unfold Qle.
     simpl.
     unfold Zsucc.
     apply Zle_0_minus_le.
     replace RHS with (d*(n/d) + n mod d - n mod d - n + d)%Z by ring.
     rewrite <- Z_div_mod_eq; auto with *.
     replace RHS with (d - n mod d)%Z by ring.
     apply Zle_minus_le_0.
     destruct (Z_mod_lt n d); auto with *.
    generalize (Zsucc (n/d)).
    intros [|z|z].
      discriminate.
     apply Qle_refl.
    discriminate.
   cut (0 < (mkQpos q)/(err * (mkQpos X)*(mkQpos X)))%Qpos.
    autorewrite with QposElim; auto.
   apply Q.Qmult_lt_0_compat; auto with *.
   apply Qinv_lt_0_compat; auto with *.
  setoid_replace (Qabs (hd series)) with 0.
   stepl 0; [| simpl; ring].
   apply Qlt_le_weak; Qauto_pos.
  apply Qle_antisym; try assumption.
  apply Qabs_nonneg.
 apply Qle_trans with (Qabs (hd series)*a^(InfiniteGeometricSum_maxIter series err)); try assumption.
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
 unfold Zsucc.
 rewrite -> Qpower_plus';[|discriminate].
 stepr ((Qabs (hd series) * a ^ p)*a); [| simpl; ring].
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
 apply: mult_resp_leEq_rht; try assumption.
 apply IHp; assumption.
Qed.

(** The implemenation of [InfiniteGeometricSum]. *)
Definition InfiniteGeometricSum_raw series (e:QposInf) : Q :=
match e with
| QposInfinity => 0
| Qpos2QposInf err => InfiniteSum_raw_N (InfiniteGeometricSum_maxIter series err)
  (fun err s => 0) (err_prop err) series
end.

Lemma InfiniteGeometricSum_raw_prf : forall series, GeometricSeries series ->
is_RegularFunction (InfiniteGeometricSum_raw series).
Proof.
 intros series H e0 e1.
 assert (A0:=InfiniteGeometricSum_maxIter_correct e0 H).
 assert (A1:=InfiniteGeometricSum_maxIter_correct e1 H).
 revert A0 A1.
 simpl.
 generalize (InfiniteGeometricSum_maxIter series e0) (InfiniteGeometricSum_maxIter series e1).
 revert e0 e1.
 cut (forall (e0 e1:Qpos), (e1 <= e0) -> forall (p p0 : positive),
   err_prop e0 (Str_nth_tl (nat_of_P p) series) -> err_prop e1 (Str_nth_tl (nat_of_P p0) series) ->
     Qball (e0) (InfiniteSum_raw_N p (fun (_ : Stream Q -> bool) (_ : Stream Q) => 0)
       (err_prop e0) series) (InfiniteSum_raw_N p0 (fun (_ : Stream Q -> bool) (_ : Stream Q) => 0)
         (err_prop e1) series)).
  intros X e0 e1 p0 p1.
  destruct (Qle_total e1 e0).
   intros H0 H1.
   apply: ball_weak;simpl;auto.
  intros H0 H1.
  setoid_replace (e0 + e1)%Qpos with (e1+e0)%Qpos by QposRing.
  apply: ball_weak.
  apply ball_sym.
  apply X; auto with *.
 intros e0 e1 He p0 p1 H0.
 revert H.
 set (P0:=fun s q => GeometricSeries s ->
   err_prop e1 (Str_nth_tl (nat_of_P p1) s) -> Qball e0 q (InfiniteSum_raw_N p1 (fun (_ : Stream Q -> bool) (_ : Stream Q) => 0)
     (err_prop e1) s)).
 change (P0 series (InfiniteSum_raw_N p0 (fun (_ : Stream Q -> bool) (_ : Stream Q) => 0)
   (err_prop e0) series)).
 apply InfiniteSum_raw_N_ind; try assumption; unfold P0.
  intros s Hs Gs H1.
  apply: ball_sym;simpl.
  unfold Qball.
  rewrite <- AbsSmall_Qabs.
  unfold Qminus.
  rewrite -> Qplus_0_r.
  apply err_prop_correct; assumption.
 intros s rec Hs Ind Gs H1.
 clear P0.
 rewrite InfiniteSum_raw_N_extend; try assumption.
 rewrite InfiniteSum_raw_N_Psucc.
 unfold InfiniteSum_raw_F.
 case_eq (err_prop e1 s).
  intros H.
  elim Hs.
  apply err_prop_monotone with e1; try assumption.
  destruct (err_prop e1 s);[constructor | discriminate H].
 intros H.
 unfold Qball.
 rewrite <- AbsSmall_Qabs.
 repeat rewrite -> Qplus'_correct.
 set (x:=InfiniteSum_raw_N p1 (fun (_ : Stream Q -> bool) (_ : Stream Q) => 0) (err_prop e1) (tl s)) in *.
 set (Qplus' (hd s) rec - Qplus' (hd s) x).
 setoid_replace (hd s + rec - (hd s + x)) with (rec - x) by (simpl; ring).
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

Definition InfiniteGeometricSum series (Gs:GeometricSeries series) : CR :=
Build_RegularFunction (InfiniteGeometricSum_raw_prf Gs).

(** The [InfiniteGeometricSum] is correct. *)
Lemma InfiniteGeometricSum_step : forall series (Gs:GeometricSeries series),
 (InfiniteGeometricSum Gs ==
  ('(hd series))+(InfiniteGeometricSum (ForAll_Str_nth_tl 1%nat Gs)))%CR.
Proof.
 intros series Gs.
 rewrite -> CRplus_translate.
 apply: regFunEq_e.
 intros e.
 simpl.
 rewrite InfiniteSum_raw_N_extend; [|apply InfiniteGeometricSum_maxIter_correct; assumption].
 rewrite InfiniteSum_raw_N_Psucc.
 unfold InfiniteSum_raw_F.
 case_eq (err_prop e series); intros He.
  assert (He':err_prop e series).
   destruct (err_prop e series);try discriminate He; constructor.
  clear He.
  apply: ball_sym.
  simpl.
  unfold Qball.
  rewrite <- AbsSmall_Qabs.
  ring_simplify (hd series + InfiniteSum_raw_N (InfiniteGeometricSum_maxIter (tl series) e)
    (fun (_ : Stream Q -> bool) (_ : Stream Q) => 0) (err_prop e) (tl series) - 0).
  eapply Qle_trans.
   apply Qabs_triangle.
  autorewrite with QposElim.
  apply: plus_resp_leEq_both;simpl.
   rewrite ->  err_prop_prop in He'.
   unfold err_bound in He'.
   assert (X:0 < 1 - a).
    change (0 < 1 + - a).
    rewrite <- Qlt_minus_iff.
    assumption.
   clear - He' Ha0 X.
   stepl ((Qabs (hd series)/(1-a))*(1-a)); [| simpl; field; auto with *].
   stepr (e*1); [| simpl; ring].
   apply: mult_resp_leEq_both; simpl; try solve[Qauto_nonneg]; auto with *.
   rewrite -> Qle_minus_iff.
   ring_simplify.
   assumption.
  apply err_prop_correct.
    destruct Gs; assumption.
   apply err_prop_monotone'; assumption.
  change (Is_true (err_prop e
    (Str_nth_tl (S (nat_of_P (InfiniteGeometricSum_maxIter (tl series) e))) series))).
  induction (S (nat_of_P (InfiniteGeometricSum_maxIter (tl series) e))).
   assumption.
  simpl.
  rewrite <- tl_nth_tl.
  apply err_prop_monotone'; try assumption.
  apply ForAll_Str_nth_tl.
  assumption.
 rewrite -> Qplus'_correct.
 rewrite (@InfiniteSum_raw_N_extend' (InfiniteGeometricSum_maxIter (tl series) e)
   (InfiniteGeometricSum_maxIter series e)).
   apply: ball_refl.
  apply InfiniteGeometricSum_maxIter_correct.
  destruct Gs; assumption.
 apply (@InfiniteGeometricSum_maxIter_monotone series e).
 assumption.
Qed.

Lemma InfiniteGeometricSum_bound : forall series
 (Gs:GeometricSeries series),
 AbsSmall (R:=CRasCOrdField) ('(err_bound series))%CR (InfiniteGeometricSum Gs).
Proof.
 intros series Gs.
 assert (Y:0 < 1 - a).
  change (0 < 1 + - a).
  rewrite <- Qlt_minus_iff.
  assumption.
 destruct (Qeq_dec (err_bound series) 0) as [Hq|Hq].
  stepr 0%CR.
   split; simpl; rewrite -> Hq; try apply CRle_refl.
   setoid_replace (-0)%CR with 0%CR by (simpl; ring).
   apply CRle_refl.
  apply: regFunEq_e.
  intros e.
  apply ball_sym.
  simpl.
  unfold Qball.
  stepr 0.
   apply zero_AbsSmall.
   apply Qpos_nonneg.
  simpl.
  ring_simplify.
  assert (X:err_prop e series).
   rewrite -> err_prop_prop.
   rewrite -> Hq.
   apply Qpos_nonneg.
  destruct  (InfiniteGeometricSum_maxIter series e) using Pind.
   simpl.
   unfold InfiniteSum_raw_F.
   destruct (err_prop e series); try contradiction; reflexivity.
  rewrite InfiniteSum_raw_N_Psucc.
  unfold InfiniteSum_raw_F.
  destruct (err_prop e series); try contradiction; reflexivity.
 assert (Herr:0 < err_bound series).
  unfold err_bound.
  apply Qlt_shift_div_l.
   assumption.
  ring_simplify.
  destruct (Qle_lt_or_eq 0 (Qabs (hd series))).
    apply Qabs_nonneg.
   assumption.
  elim Hq.
  unfold err_bound.
  rewrite <- H.
  field; auto with *.
 set (e:=mkQpos Herr).
 cut (AbsSmall (R:=CRasCOrdField) (' e)%CR (InfiniteGeometricSum Gs)).
  intros [H0 H1].
  unfold e in *.
  autorewrite with QposElim in *.
  split; assumption.
 stepr (InfiniteGeometricSum Gs[-]0)%CR; [| now (unfold cg_minus; simpl; ring)].
 rewrite -> CRAbsSmall_ball.
 apply: regFunBall_e.
 intros d.
 simpl.
 set (p:=(InfiniteGeometricSum_maxIter series d)).
 set (e':=(err_prop d)).
 unfold Qball.
 rewrite <- AbsSmall_Qabs.
 setoid_replace (InfiniteSum_raw_N p (fun (_ : Stream Q -> bool) (_ : Stream Q) => 0) e'
   series - 0) with (InfiniteSum_raw_N p (fun (_ : Stream Q -> bool) (_ : Stream Q) => 0) e'
     series) by (simpl; ring).
 apply err_prop_correct; try assumption.
  apply err_prop_monotone with e.
   autorewrite with QposElim.
   Qauto_le.
  rewrite -> err_prop_prop.
  unfold e.
  autorewrite with QposElim.
  apply Qle_refl.
 unfold e'.
 apply InfiniteGeometricSum_maxIter_correct.
 assumption.
Qed.

Lemma InfiniteGeometricSum_small_tail : forall series (e : Qpos),
GeometricSeries series ->
{n : nat & forall Gs : GeometricSeries (Str_nth_tl n series),
AbsSmall (R:=CRasCOrdField) (' e)%CR (InfiniteGeometricSum Gs)}.
Proof.
 intros series e.
 exists (nat_of_P (InfiniteGeometricSum_maxIter series e)).
 intros Gs.
 eapply AbsSmall_leEq_trans; [|apply InfiniteGeometricSum_bound].
 rewrite ->  CRle_Qle.
 rewrite <- err_prop_prop.
 apply InfiniteGeometricSum_maxIter_correct.
 assumption.
Qed.

Lemma GeometricSeries_convergent : forall (series:Stream Q),
 GeometricSeries series ->
 convergent (fun n => inj_Q IR (Str_nth n series)).
Proof.
 intros series H.
 apply ratio_test_conv.
 exists 0%nat.
 exists (inj_Q IR a).
  rstepr (nring 1:IR).
  stepr (inj_Q IR (nring 1)); [| now apply (inj_Q_nring IR 1)].
  apply inj_Q_less.
  assumption.
 assert (Ha0':[0][<=]inj_Q IR a).
  rstepl (nring 0:IR).
  stepl (inj_Q IR (nring 0)); [| now apply (inj_Q_nring IR 0)].
  apply inj_Q_leEq.
  assumption.
 split.
  assumption.
 intros n _.
 destruct (ForAll_Str_nth_tl n H) as [H0 _].
 stepr (inj_Q IR a[*](inj_Q IR (Qabs (Str_nth n series)))); [| now
   apply mult_wdr; apply eq_symmetric; apply AbsIR_Qabs].
 stepl (inj_Q IR (Qabs (Str_nth (S n) series))); [| now apply eq_symmetric; apply AbsIR_Qabs].
 stepr (inj_Q IR (a[*]Qabs (Str_nth n series))); [| now apply inj_Q_mult].
 apply inj_Q_leEq.
 replace (S n) with (1+n)%nat by auto with *.
 rewrite <- Str_nth_plus.
 assumption.
Qed.

(* This is a horrendous proof.  I'm sure half of it isn't needed, but I don't care to make it better
 all proofs of this are extensionally equivalent anyway *)
Lemma InfiniteGeometricSum_correct : forall (series:Stream Q) (x:nat -> IR),
 (forall n:nat, inj_Q IR (Str_nth n series)%Q[=]x n) ->
 forall (Gs:GeometricSeries series) H,
 (InfiniteGeometricSum Gs==IRasCR (series_sum x H))%CR.
Proof.
 intros seq x Hx Gs H.
 unfold series_sum.
 rewrite -> IR_Lim_as_CR.
 apply: SeqLimit_unique.
 intros e He.
 generalize (IR_Cauchy_prop_as_CR (Build_CauchySeq IR (seq_part_sum x) H)).
 intros C.
 destruct (C _ (pos_div_two _ _ He)) as [n Hn].
 exists n.
 intros m Hm.
 unfold CS_seq in *.
 clear C.
 unfold seq_part_sum in *.
 rstepr (((IRasCR (Sum0 (G:=IR) m x)[-](IRasCR (Sum0 (G:=IR) n x)))[+]
   ((IRasCR (Sum0 (G:=IR) n x)[-]InfiniteGeometricSum Gs)))).
 apply AbsSmall_eps_div_two;[apply Hn; assumption|].
 clear m Hm.
 stepr (('(Sum0 n (fun n => (Str_nth n seq))%Q))%CR[-]InfiniteGeometricSum Gs).
  revert seq x H Hx Gs Hn.
  induction n.
   intros seq x H Hx Gs Hn.
   stepr ([0][-]InfiniteGeometricSum Gs);
     [|apply csbf_wd_unfolded; try apply eq_reflexive; apply eq_symmetric; apply IR_Zero_as_CR].
   apply AbsSmall_minus.
   rstepr (InfiniteGeometricSum Gs).
   assert (Hn' : forall m : nat, (0 <= m)%nat -> AbsSmall (R:=CRasCOrdField) (e [/]TwoNZ)
     (IRasCR (Sum0 (G:=IR) m x))).
    intros m Hm.
    stepr (IRasCR (Sum0 (G:=IR) m x)[-]IRasCR (Sum0 (G:=IR) 0 x)).
     apply Hn; assumption.
    unfold cg_minus.
    simpl.
    rewrite -> IR_Zero_as_CR.
    ring.
   stepl (IRasCR (CRasIR (e[/]TwoNZ)))%CR; [| now apply CRasIRasCR_id].
   stepr (IRasCR (CRasIR (InfiniteGeometricSum Gs)))%CR; [| now apply CRasIRasCR_id].
   rewrite <- IR_AbsSmall_as_CR.
   apply AbsSmall_approach.
   intros d Hd.
   rewrite -> IR_AbsSmall_as_CR.
   stepr (InfiniteGeometricSum Gs); [| now apply eq_symmetric; apply CRasIRasCR_id].
   destruct (Q_dense_in_CReals IR d) as [q Hq0 Hq].
    assumption.
   assert (Hq0': 0 < q).
    apply (less_inj_Q IR).
    stepl ([0]:IR).
     assumption.
    apply eq_symmetric; apply (inj_Q_nring IR 0).
   destruct (InfiniteGeometricSum_small_tail (mkQpos Hq0') Gs) as [m Hm].
   rstepr ((IRasCR (Sum0 (G:=IR) m x))[+]((InfiniteGeometricSum Gs)[-](IRasCR (Sum0 (G:=IR) m x)))).
   stepl (IRasCR (CRasIR (e [/]TwoNZ))[+](IRasCR d)); [| now apply eq_symmetric; apply IR_plus_as_CR].
   apply AbsSmall_plus.
    stepl (e [/]TwoNZ); [| now apply eq_symmetric; apply CRasIRasCR_id].
    apply Hn'; auto with *.
   apply AbsSmall_leEq_trans with ('q)%CR.
    stepl (IRasCR (inj_Q IR q)); [| now apply IR_inj_Q_as_CR].
    rewrite <- IR_leEq_as_CR.
    apply less_leEq.
    assumption.
   rewrite QposAsmkQpos in Hm.
   clear - Hm Hx.
   revert seq x Hx Gs Hm.
   induction m.
    intros seq x Hx Gs Hm.
    stepr (InfiniteGeometricSum Gs).
     apply Hm.
    unfold cg_minus.
    simpl.
    rewrite -> IR_Zero_as_CR.
    ring.
   intros seq x Hx Gs Hm.
   stepr ((InfiniteGeometricSum (ForAll_Str_nth_tl 1 Gs)[-]IRasCR (Sum0 (G:=IR) m (fun n => (x (S n)))))).
    apply IHm.
     intros n.
     stepl ((inj_Q IR (Str_nth (S n) seq)%Q)).
      apply Hx.
     apply eq_reflexive.
    intros.
    apply Hm.
   change (InfiniteGeometricSum (ForAll_Str_nth_tl 1 Gs)-
     IRasCR (Sum0 (G:=IR) m (fun n : nat => (x (S n)))) ==
       InfiniteGeometricSum Gs-IRasCR (Sum0 (G:=IR) (S m) x))%CR.
   symmetry.
   rewrite -> InfiniteGeometricSum_step.
   setoid_replace (IRasCR (Sum0 (G:=IR) (S m) x))
     with (IRasCR (inj_Q _ (hd seq) [+](Sum0 (G:=IR) m (fun n0 : nat => (x (S n0)))%Q))).
    rewrite -> (IR_plus_as_CR).
    rewrite -> IR_inj_Q_as_CR.
    ring.
   apply IRasCR_wd.
   apply eq_symmetric.
   stepl (x O[+]Sum0 (G:=IR) m (fun n0 : nat => (x (S n0)))).
    apply Sum0_shift.
    intros i.
    apply eq_reflexive.
   apply bin_op_wd_unfolded.
    apply eq_symmetric.
    apply (Hx O).
   apply eq_reflexive.
  intros seq x H Hx Gs Hn.
  set (y:=(fun n => (x (n + 1)%nat))).
  stepr (('(((Sum0 (G:=Q_as_CAbGroup) n (fun n0 : nat =>  Str_nth n0 (tl seq))%Q)))%CR)[-]
    InfiniteGeometricSum (ForAll_Str_nth_tl 1 Gs))%CR; [apply (IHn (tl seq) y )|].
     apply tail_series with x.
      assumption.
     exists 1%nat.
     exists 0%nat.
     intros; apply eq_reflexive.
    intros m.
    unfold y.
    stepr ((inj_Q IR (Str_nth (m+1) seq))); [| now apply (Hx (m + 1)%nat)].
    rewrite <- Str_nth_plus.
    apply eq_reflexive.
   intros m Hm.
   stepr (IRasCR (Sum0 (G:=IR) (S m) x)[-]IRasCR (Sum0 (G:=IR) (S n) x)).
    apply Hn.
    auto with *.
   change ((IRasCR (Sum0 (G:=IR) (S m) x) - IRasCR (Sum0 (G:=IR) (S n) x) ==
     IRasCR (Sum0 (G:=IR) m y) - IRasCR (Sum0 (G:=IR) n y))%CR).
   do 2 rewrite <- IR_minus_as_CR.
   apply IRasCR_wd.
   stepr ((x O[+]Sum0 (G:=IR) m y[-](x O[+]Sum0 (G:=IR) n y))).
    apply bin_op_wd_unfolded;[|apply un_op_wd_unfolded]; apply eq_symmetric; apply Sum0_shift;
      intros; unfold y;rewrite plus_comm; apply eq_reflexive.
   rational.
  change ((' Sum0 (G:=Q_as_CAbGroup) n (fun n0 : nat => (Str_nth n0 (tl seq))%Q) -
    InfiniteGeometricSum (ForAll_Str_nth_tl 1 Gs) == ' (Sum0 (G:=Q_as_CAbGroup) (S n)
      (fun n0 : nat => (Str_nth n0 seq)%Q)) - InfiniteGeometricSum Gs))%CR.
  symmetry.
  rewrite -> InfiniteGeometricSum_step.
  set (z:=(fun n0 : nat => (Str_nth n0 seq)%Q)).
  setoid_replace ((Sum0 (G:=Q_as_CAbGroup) (S n) z):Q) with ((z O + (Sum0 (G:=Q_as_CAbGroup) n
    (fun n0 : nat => (Str_nth n0 (tl seq))%Q)))).
   rewrite <- (CRplus_Qplus (z O)).
   unfold z, Str_nth.
   simpl.
   ring.
  symmetry.
  apply: Sum0_shift.
  intros i.
  reflexivity.
 apply cg_minus_wd;[rewrite -> IR_Sum0_as_CR|reflexivity].
 clear - Hx.
 induction n.
  reflexivity.
 change ((' (Sum0 (G:=Q_as_CAbGroup) n (fun n0 : nat => (Str_nth n0 seq)) + (Str_nth n seq))%Q ==
   (Sum0 (G:=CRasCAbGroup) n (fun n0 : nat => IRasCR (x n0)):CR) + IRasCR (x n))%CR).
 rewrite <- CRplus_Qplus.
 apply ucFun2_wd;[apply IHn|].
 transitivity (IRasCR (inj_Q IR (Str_nth n seq)%Q)); [symmetry;apply IR_inj_Q_as_CR|].
 apply IRasCR_wd.
 apply Hx.
Qed.

Lemma InfiniteGeometricSum_correct' : forall (series:Stream Q),
 forall (Gs:GeometricSeries series),
 (InfiniteGeometricSum Gs == IRasCR (series_sum _ (GeometricSeries_convergent Gs)))%CR.
Proof.
 intros series Gs.
 apply InfiniteGeometricSum_correct.
 intros; apply eq_reflexive.
Qed.

End GeometricSeries.
