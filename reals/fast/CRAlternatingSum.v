(*
Copyright © 2006 Russell O’Connor

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

Require Import iso_CReals.
Require Import Q_in_CReals.
Require Import ArithRing.
Require Export CRArith.
Require Import CRIR.
Require Import Bool.
Require Import COrdAbs.
Require Import Qordfield.
Require Export Qmetric.
Require Import LazyNat.
Require Export Limit.
Require Import QposMinMax.
Require Import Qpower.
Require Export Streams.
Require Import PowerSeries.
Require Import CornTac.

Set Implicit Arguments.

Opaque CR.

Open Local Scope Q_scope.

Definition DecreasingNonNegative := ForAll (fun (s:Stream Q) => ForAll (fun (t:Stream Q) => 0 <= (hd t) <= (hd s)) s).

Definition DecreasingNonNegative_alt := ForAll (fun (s:Stream Q) => 0 <= (hd (tl s)) <= (hd s)).

Lemma dnn_alt_dnn : forall s, DecreasingNonNegative_alt s -> DecreasingNonNegative s.
Proof.
cofix r1.
intros s H.
constructor.

cut (hd s <= hd s);[|apply Qle_refl].
set (x:=hd s).
unfold x at 1.
generalize s H x.
clear s H x.
cofix r2.
intros s H x Hx.
constructor.
destruct H.
split.
apply Qle_trans with (hd (tl s)); firstorder.
assumption.
destruct H.
apply r2.
apply H0.
apply Qle_trans with (hd s); firstorder.

destruct H.
apply r1.
apply H0.
Qed.

Lemma dnn_dnn_alt : forall s, DecreasingNonNegative s -> DecreasingNonNegative_alt s.
Proof.
cofix.
intros s H.
constructor.
destruct H.
destruct H.
destruct H1.
assumption.
apply dnn_dnn_alt.
destruct H; assumption.
Qed.

Lemma dnn_alt_iff_dnn : forall s, DecreasingNonNegative_alt s <-> DecreasingNonNegative s.
Proof.
firstorder using dnn_alt_dnn dnn_dnn_alt.
Qed.

Lemma dnn_tl : forall s, DecreasingNonNegative s -> DecreasingNonNegative (tl s).
Proof.
intros s [_ H].
assumption.
Qed.

Coercion Local Is_true : bool >-> Sortclass.

Fixpoint takeUntil (A B:Type) (P : Stream A -> bool)(s:Stream A) (ex:LazyExists P s) (cons: A -> B -> B) (nil : B) {struct ex} : B :=
(if P s as b return ((P s -> b) -> B)
then fun _ => nil
else fun (n : P s -> False) => cons (hd s)
     (@takeUntil A B P (tl s)
      match ex with
      | LazyHere H => (False_ind _ (n H))
      | LazyFurther ex0 => ex0 tt
      end cons nil))
(fun x => x).

Lemma takeUntil_wd : forall (A B:Type) (P : Stream A -> bool)(s:Stream A)(ex1 ex2:LazyExists P s) (cons: A -> B -> B) (nil:B),
  takeUntil P ex1 cons nil = takeUntil P ex2 cons nil.
Proof.
intros A B P s ex1 ex2 cons nil.
assert (H:=ex1).
induction H;
case ex1; clear ex1; case ex2; clear ex2;
simpl;
destruct (P x); try contradiction; auto.
intros ex2 ex1.
rewrite (H0 tt (ex1 tt) (ex2 tt)).
reflexivity.
Qed.

Lemma takeUntil_end : forall (A B:Type) (P:Stream A -> bool) seq (ex:LazyExists P seq) (cons:A -> B -> B) (nil : B),
 P seq -> takeUntil P ex cons nil = nil.
Proof.
intros A B P seq ex cons nil H.
rewrite <- (takeUntil_wd (B:=B) P (LazyHere P _ H)).
unfold takeUntil.
destruct (P seq);[|contradiction].
reflexivity.
Qed.

Lemma takeUntil_step : forall (A B:Type) (P:Stream A -> bool) seq (ex:LazyExists P seq) (cons: A -> B -> B) (nil: B),
 ~P seq -> exists ex':(LazyExists P (tl seq)), takeUntil P ex cons nil = cons (hd seq) (takeUntil P ex' cons nil).
Proof.
intros A B P seq ex cons nil H.
assert (ex':=ex).
destruct ex' as [H0|ex'].
elim H; assumption.
exists (ex' tt).
rewrite <- (takeUntil_wd (B:=B) P (LazyFurther seq ex')).
simpl.
destruct (P seq).
elim H; constructor.
reflexivity.
Qed.

(* Deforested
Fixpoint AlternatingSum (l:list Q) : Q :=
match l with 
| nil => 0
| cons x xs => (x - (AlternatingSum xs))
end.
*)

Definition PartialAlternatingSumUntil (P:Stream Q -> bool)(seq:Stream Q)(ex:LazyExists P seq) : Q :=
(takeUntil P ex Qminus' 0).

Lemma PartialAlternatingSumUntil_small : forall (P:Stream Q -> bool)(seq:Stream Q)(dnn:DecreasingNonNegative seq)(ex:LazyExists P seq), 0 <= (PartialAlternatingSumUntil P ex) <= (hd seq).
Proof.
intros P seq dnn ex.
assert (H:=ex).
unfold PartialAlternatingSumUntil.
induction H;
destruct dnn as [[[Za Zb] Z1] dnn];
case ex; clear ex; simpl; destruct (P x); try contradiction; pose Qle_refl; auto.
intros ex.
rename H0 into IH.
destruct (IH tt dnn (ex tt)) as [H0 H1].
destruct Z1 as [[_ Zd] _].
split.
     rewrite Qminus'_correct.
rsapply shift_zero_leEq_minus.
apply Qle_trans with (hd (tl x)); auto.
rewrite Qle_minus_iff.
     rewrite Qminus'_correct.
ring_simplify.
assumption.
Qed.

Definition Qball_ex_bool e a b : bool :=
 if ball_ex_dec _ Qball_dec e a b then true else false.

Lemma sumbool_eq_true : forall P (dec:{P}+{~P}), (if dec then true else false) = true <-> P.
Proof.
intros.
destruct dec;
simpl;split;auto.
discriminate 1.
Qed.

Lemma Limit_near : forall (seq:Stream Q) (l:Q), Limit seq l -> forall e, LazyExists (fun s => Qball_ex_bool e (hd s) l) seq.
Proof.
intros seq l H e.
assert (H' := (H e)).

induction H'.
left.
destruct H0 as [H0 _].
unfold Qball_ex_bool.
destruct (ball_ex_dec Q_as_MetricSpace Qball_dec e (hd x) l).
constructor.
apply n; clear n.
apply H0.

right.
rename H1 into IHH'.
intro.
apply (IHH' tt).
apply Limit_tl.
assumption.
Defined.

Definition InfiniteAlternatingSum_raw (seq:Stream Q)(dnn:DecreasingNonNegative seq)(zl:Limit seq 0)(e:QposInf) :=
PartialAlternatingSumUntil _ (Limit_near zl e).

Lemma InfiniteAlternatingSum_prf : forall seq (dnn:DecreasingNonNegative seq) (zl:Limit seq 0), is_RegularFunction (InfiniteAlternatingSum_raw dnn zl).
Proof.
Opaque Qball_dec.
intros seq dnn zl.
unfold is_RegularFunction, ball, Qball.
simpl.

(*WLOG e2 <= e1*)
cut (forall e1 e2 : Qpos, e2 <= e1 ->
Qball (e1 + e2) (InfiniteAlternatingSum_raw dnn zl e1)
  (InfiniteAlternatingSum_raw dnn zl e2)).
intros H e1 e2.
destruct (Qpos_le_total e1 e2).
setoid_replace (e1+e2)%Qpos with (e2+e1)%Qpos by QposRing.
rsapply ball_sym.
auto.
auto.

intros e1 e2 He.
rsapply ball_weak.
unfold Qball.
unfold InfiniteAlternatingSum_raw.
unfold PartialAlternatingSumUntil.
generalize (Limit_near zl e1) (Limit_near zl e2).
clear zl.
intros ex1 ex2.
simpl in *.
pose (F:= fun e => (fun s : Stream Q => Qball_ex_bool e (hd s) 0)).

assert(case1: forall seq (dnn:DecreasingNonNegative seq) (ex2: LazyExists _ seq), (Qball e1 (hd seq) 0) ->
       AbsSmall (R:=Q_as_COrdField) (e1:Q) (0 - (takeUntil (F e2) ex2 Qminus' 0))).
clear seq dnn ex1 ex2.
intros seq dnn ex2 [Hseq1 Hseq2].
rsapply AbsSmall_minus.
change (AbsSmall (e1:Q) ((PartialAlternatingSumUntil _ (ex2))-0)).
stepr (PartialAlternatingSumUntil _ (ex2)) by (simpl; ring).
destruct (PartialAlternatingSumUntil_small _ dnn (ex2)) as [Hl1 Hl2].
apply AbsSmall_leEq_trans with (hd seq).
stepl (hd seq - 0);[assumption|simpl;ring].
split;[|assumption].
apply Qle_trans with 0;[|assumption].
simpl.
rewrite Qle_minus_iff; ring_simplify.
destruct dnn as [[[X _] _] _]; assumption.

assert(H:=ex1).
induction H;
case (ex1); unfold Qball_ex_bool in *; simpl in *; destruct (Qball_dec e1 (hd x) 0); try contradiction; auto.
intros ex3.

assert (case2:~(Qball e2 (hd x) 0)).
intros q.
apply n.
unfold Qball.
apply AbsSmall_leEq_trans with (e2:Q); assumption.

Opaque Qred.
case (ex2); unfold Qball_ex_bool in *; simpl; destruct (Qball_dec e2 (hd x) 0); try contradiction;
try solve[intros; elim case2].
intros ex4.
simpl.
set (a :=
     (takeUntil
        (fun s : Stream Q => if Qball_dec e1 (hd s) 0 then true else false)
        (ex3 tt)) Qminus' 0).
set (b:=(takeUntil
         (fun s : Stream Q => if Qball_dec e2 (hd s) 0 then true else false)
         (ex4 tt)) Qminus' 0).
stepr (b-a) by (simpl;
     repeat rewrite Qminus'_correct;
 ring).
rsapply AbsSmall_minus.
rename H0 into IHExists.
rapply (IHExists tt).
clear - dnn.
destruct dnn.
assumption.
Transparent Qball_dec.
Qed.

Definition InfiniteAlternatingSum (seq:Stream Q)(dnn:DecreasingNonNegative seq)(zl:Limit seq 0) : CR :=
Build_RegularFunction (InfiniteAlternatingSum_prf dnn zl).

Lemma InfiniteAlternatingSum_step : forall seq (dnn:DecreasingNonNegative seq) (zl:Limit seq 0),
 (InfiniteAlternatingSum dnn zl ==
  ('(hd seq))-(InfiniteAlternatingSum (dnn_tl dnn) (Limit_tl zl)))%CR.
Proof.
intros [hd seq] [dnn_hd dnn] zl.
rewrite CRplus_translate.
rapply regFunEq_e.
intros e.
simpl.
unfold Cap_raw; simpl.
unfold InfiniteAlternatingSum_raw.
unfold PartialAlternatingSumUntil.
simpl.
set (P:=(fun s : Stream Q =>
         Qball_ex_bool e (Streams.hd s) 0)).
case_eq (P (Cons hd seq)); intros H.

rewrite takeUntil_end;[|apply Is_true_eq_left;assumption].
case_eq (P seq); intros H0.

rewrite takeUntil_end;[|apply Is_true_eq_left;assumption].
simpl.
ring_simplify.
unfold P in H.
rsapply ball_weak.
rsapply ball_sym.
unfold Qball_ex_bool in H.
destruct (ball_ex_dec Q_as_MetricSpace Qball_dec e (Streams.hd (Cons hd seq))) as [X|X];
 [apply X|discriminate H].

unfold P in *.
unfold Qball_ex_bool in *.
destruct (ball_ex_dec Q_as_MetricSpace Qball_dec e (Streams.hd (Cons hd seq))) as [X|X];
 [|discriminate H].
destruct (ball_ex_dec Q_as_MetricSpace Qball_dec e (Streams.hd seq)) as [Y|Y];
 [discriminate H0|].
elim Y.
simpl in dnn_hd.
destruct dnn_hd as [_ [[Z0 Z1] dnn_hd0]].
split;simpl.
apply Qle_trans with 0.
rewrite Qle_minus_iff; ring_simplify; apply Qpos_nonneg.
ring_simplify.
apply Z0.
ring_simplify.
eapply Qle_trans.
apply Z1.
destruct X as [_ X].
replace LHS with (hd - 0) by ring.
apply X.

destruct (takeUntil_step P (Limit_near zl e) Qminus' 0) as [ex' rw];
 [rewrite H;auto|].
rewrite rw; clear rw.
simpl.
rewrite (@takeUntil_wd Q Q P _ ex' (Limit_near (Limit_tl zl) e)).
     rewrite Qminus'_correct.
rapply ball_refl.
Qed.

Lemma InfiniteAlternatingSum_nonneg : forall seq (dnn:DecreasingNonNegative seq) (zl:Limit seq 0),
 (inject_Q 0%Q <= InfiniteAlternatingSum dnn zl)%CR.
Proof.
intros seq dnn zl e.
apply Qle_trans with 0.
rewrite Qle_minus_iff; ring_simplify; apply Qpos_nonneg.
unfold InfiniteAlternatingSum.
simpl.
unfold Cap_raw.
simpl.
ring_simplify.
unfold InfiniteAlternatingSum_raw.
simpl.
destruct (PartialAlternatingSumUntil_small _ dnn (Limit_near zl ((1 # 2) * e)%Qpos)).
assumption.
Qed.

Lemma InfiniteAlternatingSum_bound : forall seq (dnn:DecreasingNonNegative seq) (zl:Limit seq 0),
 (InfiniteAlternatingSum dnn zl <= inject_Q (hd seq))%CR.
Proof.
intros seq dnn zl.
rewrite InfiniteAlternatingSum_step.
change (inject_Q (hd seq) - InfiniteAlternatingSum (dnn_tl dnn) (Limit_tl zl)[<=]inject_Q (hd seq))%CR.
stepr (inject_Q (hd seq) - inject_Q 0%Q)%CR.
rsapply minus_resp_leEq_rht.
apply InfiniteAlternatingSum_nonneg.
simpl.
ring.
Qed.

Section Series.

Definition mult_Streams := zipWith (Qmult).

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

Definition StreamBounds (a b : Stream Q) := ForAll (fun (x:Stream (Q*Q)) => let (a,b):=(hd x) in AbsSmall a b) (zipWith Pair a b).

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

Section Powers.

Variable a : Q.

CoFixpoint powers_help (c:Q) : Stream Q :=
Cons c (powers_help (c*a)).

Definition powers := powers_help 1.

Lemma Str_nth_powers : forall n, Str_nth n powers == a^n.
Proof.
unfold powers.
intros n.
setoid_replace (a^n) with (1*a^n) by ring.
generalize 1.
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

Hypothesis Ha : 0 <= a <= 1.

Lemma powers_dnn : DecreasingNonNegative powers.
Proof.
destruct Ha as [Ha0 Ha1].
apply dnn_alt_dnn.
unfold powers.
cut (0 <= 1);[|discriminate].
generalize 1.
cofix.
intros b Hb.
constructor.
simpl.
split.
rsapply mult_resp_nonneg; assumption.
replace RHS with (b*1) by ring.
rsapply mult_resp_leEq_lft; assumption.

simpl.
apply powers_dnn.
rsapply mult_resp_nonneg; assumption.
Qed.

Lemma powers_nbz : NearBy 0 (1#1)%Qpos powers.
Proof.
unfold powers.
pose (one:=1).
cut (0 <= 1 <=one);[|split;discriminate].
generalize 1.
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
apply powers_nbz.
split.
rsapply mult_resp_nonneg; assumption.
unfold one in *; clear one.
replace RHS with (1*1) by ring.
rsapply mult_resp_leEq_both; assumption.
Qed.

End Powers.

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

Definition recip_positives := map (fun x => 1#x) positives.

Lemma Str_nth_recip_positives : forall n, Str_nth n recip_positives = 1#(P_of_succ_nat n).
Proof.
intros n.
unfold recip_positives.
rewrite Str_nth_map.
rewrite Str_nth_positives.
reflexivity.
Qed.

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

Fixpoint Pplus_LazyNat (p:positive)(n:LazyNat) {struct n} : positive :=
match n with
| LazyO => p
| (LazyS n') => (Pplus_LazyNat (Psucc p) (n' tt))
end.

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

End Series.

Lemma InfiniteAlternatingSum_correct : forall (seq:Stream Q) (x:nat -> IR),
 (forall n:nat, inj_Q IR (((-(1))^n)*Str_nth n seq)%Q[=]x n) ->
 forall (dnn:DecreasingNonNegative seq) zl H,
 (InfiniteAlternatingSum dnn zl==IRasCR (series_sum x H))%CR.
Proof.
intros seq x Hx dnn zl H.
unfold series_sum.
rewrite IR_Lim_as_CR.
rapply SeqLimit_unique.
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
       ((IRasCR (Sum0 (G:=IR) n x)[-]InfiniteAlternatingSum dnn zl)))).
rapply AbsSmall_eps_div_two;[apply Hn; assumption|].

assert (X:AbsSmall (R:=CRasCReals) (e [/]TwoNZ) (('(((-(1))^n)*(Str_nth n seq)))%CR)).
stepr (IRasCR (x n)).
stepr (Sum n n (fun n => IRasCR (x n))) by rapply Sum_one.
unfold Sum, Sum1.
stepr (IRasCR (Sum0 (S n) x)[-]IRasCR (Sum0 n x )) by
 (rapply cg_minus_wd; apply IR_Sum0_as_CR).
apply Hn.
auto.
simpl.
symmetry.
rewrite <- IR_inj_Q_as_CR.
apply IRasCR_wd.
apply Hx.

stepr (('(Sum0 n (fun n => ((-(1))^n)*(Str_nth n seq))%Q))%CR[-]InfiniteAlternatingSum dnn zl).
clear - X.
generalize seq dnn zl X.
clear seq dnn zl X.
generalize (e[/]TwoNZ).
clear e.
induction n; intros e seq dnn zl X.
simpl in *.
rapply AbsSmall_minus.
stepr (InfiniteAlternatingSum dnn zl) by (unfold cg_minus;simpl;ring).
rsapply leEq_imp_AbsSmall;[apply InfiniteAlternatingSum_nonneg|].
rsapply leEq_transitive.
apply InfiniteAlternatingSum_bound.
setoid_replace (hd seq) with (1*hd seq)%Q by ring.
destruct X; assumption.

rapply AbsSmall_minus.
stepr (('(((Sum0 (G:=Q_as_CAbGroup) n (fun n0 : nat =>  ((- (1)) ^ n0 * Str_nth n0 (tl seq))%Q)))%CR)[-]
   InfiniteAlternatingSum (dnn_tl dnn) (Limit_tl zl)))%CR;
 [apply IHn|].
rewrite inj_S in X.
rstepr ([--][--]('(((- (1)) ^ n * Str_nth n (tl seq))%Q))%CR).
rapply inv_resp_AbsSmall.
stepr (' ((- (1)) ^ Zsucc n * Str_nth (S n) seq))%CR;[assumption|].
simpl.
change ((' ( (- (1)) ^ (n+1) * Str_nth n (tl seq)) ==
 - ' ((- (1)) ^ n * Str_nth n (tl seq)))%CR).
rewrite Qpower_plus;[discriminate|].
simpl.
ring.

stepl (InfiniteAlternatingSum dnn zl[-](('(((- (1)) ^ 0 * Str_nth 0 seq)%Q[+]
((Sum0 (G:=Q_as_CAbGroup) n
  (fun n0 : nat => ((- (1)) ^ (S n0) * Str_nth n0 (tl seq))%Q))):Q))%CR));[
rsapply cg_minus_wd;[reflexivity|
 rewrite CReq_Qeq;
 rapply Sum0_shift;
 intros i; simpl; reflexivity]|].
unfold cg_minus; simpl.
rewrite InfiniteAlternatingSum_step.
generalize (InfiniteAlternatingSum (dnn_tl dnn) (Limit_tl zl)).
intros x.
change (Str_nth 0 seq) with (hd seq).
setoid_replace ((Sum0 (G:=Q_as_CAbGroup) n
    (fun n0 : nat => Qpower_positive (- (1)) (P_of_succ_nat n0)  * Str_nth n0 (tl seq)))%Q:Q)
 with (-(Sum0 (G:=Q_as_CAbGroup) n
   (fun n0 : nat => ((- (1)) ^ n0 * Str_nth n0 (tl seq)))))%Q;[ring|].
rapply eq_transitive;[|apply (inv_Sum0 Q_as_CAbGroup)].
rapply Sum0_wd.
intros i; simpl.
change (Qpower_positive (- (1)) (P_of_succ_nat i)) with ((-(1))^ S i).
rewrite inj_S.
unfold Zsucc.
rewrite Qpower_plus;[discriminate|].
ring.

rsapply cg_minus_wd;[rewrite IR_Sum0_as_CR|reflexivity].
clear - Hx.
induction n.
reflexivity.
change ((' (Sum0 (G:=Q_as_CAbGroup) n
      (fun n0 : nat => ((- (1)) ^ n0 * Str_nth n0 seq)%Q) +
    (- (1)) ^ n * Str_nth n seq) ==
 (Sum0 (G:=CRasCAbGroup) n (fun n0 : nat => IRasCR (x n0)):CR) + IRasCR (x n))%CR).
rewrite <- CRplus_Qplus.
apply ucFun2_wd;[apply IHn|].
transitivity (IRasCR (inj_Q IR ((- (1)) ^ n * Str_nth n seq)%Q));
 [symmetry;apply IR_inj_Q_as_CR|].
apply IRasCR_wd.
apply Hx.
Qed.
