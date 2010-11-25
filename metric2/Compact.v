(*
Copyright © 2008 Russell O’Connor

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
Require Import Limit.
Require Export FinEnum.
Require Import Zpow_facts.
Require Export Complete.
Require Import Classic.
Require Import COrdFields2.
Require Import Qordfield.
Require Import Qpower.
Require Import Qauto.
Require Import CornTac.

Set Implicit Arguments.
Set Automatic Introduction.

Open Local Scope Q_scope.

(**
* Compact sets
This module formalizes compact sets as the completion of a finitely
enumerables sets.
*)
Section BishopCompact.

(**
** Bishop Compactness
This section formalizes Bishops definition of compactness to serve as a
reference specification for our definition of compactness.
*)

Variable X : MetricSpace.

Variable P : X -> Prop.

Definition CompleteSubset :=
 forall (f:Complete X), (forall e, P (approximate f e)) ->
 {y:X | P y & st_eq (Cunit y) f}.

Definition ExtSubset :=
 forall x y, (st_eq x y) -> (P x <-> P y).

Definition TotallyBoundedSubset :=
 forall e, {l : list X | forall y, In y l -> P y & forall x, P x -> exists y, In y l /\ ball e x y }.

(** A Bishop compact set is an (extensional) predicate that is complete
 and totally bounded. *)
Record CompactSubset :=
 {completeSubset : CompleteSubset
 ;totallyBoundedSubset : TotallyBoundedSubset
 ;extSubset : ExtSubset
 }.

End BishopCompact.

Section AlmostIn.

Variable X : MetricSpace.
Hypothesis stableX : stableMetric X.

(** [almostIn] is a useful predicate that says when a point is within e
of (classically) some member of a finite enumeration. We won't know which
point it is close to. *)
Fixpoint almostIn (e:Qpos) (x:X) (l:FinEnum stableX) : Prop :=
match l with
| nil => False
| y::ys => orC (ball e x y) (almostIn e x ys)
end.

Lemma almostIn_stable : forall e x l, ~~almostIn e x l -> almostIn e x l.
Proof.
 intros e x l.
 induction l.
  tauto.
 intros H.
 simpl in *.
 unfold orC in *.
 tauto.
Qed.

Lemma almostIn_weak_le : forall (e1 e2:Qpos) x l, (e1 <= e2) -> almostIn e1 x l -> almostIn e2 x l.
Proof.
 induction l; intros He H.
  apply H.
 destruct H as [G | H | H] using orC_ind.
   auto using almostIn_stable.
  apply orWeaken.
  left.
  eapply ball_weak_le.
   apply He.
  assumption.
 apply orWeaken.
 right.
 apply IHl; assumption.
Qed.

(** If you are almost in for every e, then you are infact in the finite
enumeration *)
Lemma InAlmostIn : forall x l, (forall e, almostIn e x l)<->(InFinEnumC x l).
Proof.
 induction l.
  split.
   intros H.
   apply (H (1#1)%Qpos).
  contradiction.
 split.
  intros H [A B].
  assert (existsC Qpos (fun e => ~ball e x a)).
   intros C.
   apply A.
   apply ball_eq.
   intros d.
   apply stableX.
   apply C.
  destruct H0 as [ G | z Hz] using existsC_ind.
   tauto.
  apply B.
  apply -> IHl.
  intros e.
  apply almostIn_stable.
  intros C.
  destruct (Qlt_le_dec e z).
   apply (H e).
   split; try assumption.
   intros D.
   apply Hz.
   eapply ball_weak_le.
    apply Qlt_le_weak.
    apply q.
   assumption.
  apply (H z).
  split; try assumption.
  intros D.
  apply C.
  eapply almostIn_weak_le.
   apply q.
  assumption.
 intros H e.
 move H after e.
 destruct H as [ G | H | H] using orC_ind.
   auto using almostIn_stable.
  apply orWeaken.
  left.
  rewrite -> H.
  apply ball_refl.
 rewrite <- IHl in H.
 apply orWeaken.
 right.
 apply H.
Qed.

Lemma almostIn_closed : forall e x l, (forall d, almostIn (e+d) x l) -> almostIn e x l.
Proof.
 induction l.
  intros H.
  apply (H (1#1)%Qpos).
 intros H.
 intros [A B].
 apply B.
 clear B.
 apply IHl.
 intros d.
 assert (existsC Qpos (fun d => ~ball (e+d) x a)).
  intros Y.
  apply A.
  apply ball_closed.
  intros d0.
  apply stableX.
  apply Y.
 destruct H0 as [G | d0 Hd0] using existsC_ind.
  auto using almostIn_stable.
 apply almostIn_stable.
 intros Z.
 destruct (Qlt_le_dec d0 d).
  apply Z.
  apply (@almostIn_weak_le (e + d0)%Qpos).
   autorewrite with QposElim.
   apply Qlt_le_weak.
   rewrite -> Qlt_minus_iff in *.
   replace RHS with (d + - d0) by simpl; ring.
   assumption.
  apply almostIn_stable.
  intros Y.
  apply (H d0).
  split; try assumption.
 apply (H d).
 split.
  intros Y.
  apply Hd0.
  apply (@ball_weak_le X (e + d)%Qpos).
   autorewrite with QposElim.
   rewrite -> Qle_minus_iff in *.
   replace RHS with (d0 + - d) by simpl; ring.
   assumption.
  assumption.
 assumption.
Qed.

(** Left and right triangle laws for balls and [almostIn]. *)
Lemma almostIn_triangle_l : forall e1 e2 x1 x2 l, (ball e1 x1 x2) -> almostIn e2 x2 l -> almostIn (e1 + e2) x1 l.
Proof.
 induction l; intros H1 H2.
  apply H2.
 destruct H2 as [G | H2 | H2] using orC_ind.
   auto using almostIn_stable.
  apply orWeaken.
  left.
  eapply ball_triangle.
   apply H1.
  apply H2.
 apply orWeaken.
 right.
 apply IHl; assumption.
Qed.

Lemma almostIn_triangle_r : forall e1 e2 x l1 l2, almostIn e1 x l1 -> (ball e2 l1 l2) -> almostIn (e1 + e2) x l2.
Proof.
 intros e1 e2 x l1 l2 H1 [H2 _].
 revert l2 H1 H2.
 induction l1; intros l2 H1 H2.
  contradiction.
 unfold hemiMetric in *.
 destruct H1 as [G | H1 | H1] using orC_ind.
   auto using almostIn_stable.
  assert (Z:InFinEnumC a (a :: l1)).
   apply orWeaken.
   left; reflexivity.
  destruct (H2 a Z) as [ G | z [Hz0 Hz1]] using existsC_ind.
   auto using almostIn_stable.
  clear - H1 Hz0 Hz1.
  apply almostIn_closed.
  intros d.
  rewrite <- InAlmostIn in Hz0.
  apply almostIn_triangle_l with z.
   apply ball_triangle with a; assumption.
  apply Hz0.
 apply IHl1.
  assumption.
 intros y Hy.
 apply H2.
 apply orWeaken.
 right; assumption.
Qed.

(** If you are almost in a finite enumeration then you are close to
(classically) some point that is in the enumeration. *)
Lemma almostInExistsC : forall e x s, almostIn e x s <-> existsC X (fun y => ball e x y /\ InFinEnumC y s).
Proof.
 intros e x s.
 induction s.
  split; try contradiction.
  intros H.
  apply H.
  intros y [_ Hy].
  apply Hy.
 split.
  intros H.
  destruct H as [G | H | H] using orC_ind.
    auto using existsC_stable.
   apply existsWeaken.
   exists a.
   split; auto.
   apply orWeaken.
   left; reflexivity.
  rewrite -> IHs in H.
  destruct H as [G | y [Hy0 Hy1]] using existsC_ind.
   auto using existsC_stable.
  apply existsWeaken.
  exists y.
  split; auto.
  apply orWeaken.
  right; auto.
 intros H.
 destruct H as [G | y [Hy0 Hy1]] using existsC_ind.
  auto using almostIn_stable.
 destruct Hy1 as [G | Hy1 | Hy1] using orC_ind.
   auto using almostIn_stable.
  apply orWeaken.
  left.
  rewrite <- Hy1.
  auto.
 apply orWeaken.
 right.
 change (almostIn e x s).
 rewrite -> IHs.
 apply existsWeaken.
 exists y.
 auto.
Qed.

End AlmostIn.
(* begin hide *)
Add Parametric Morphism X stableX : (@almostIn X stableX) with signature QposEq ==> (@st_eq _) ==> (@st_eq _) ==> iff as almostIn_wd.
Proof.
 unfold FinEnum_eq.
 assert (Y:forall x1 x2 : Qpos, QposEq x1 x2 -> forall y1 y2 : X,
   st_eq y1 y2 ->forall z : FinEnum stableX, (almostIn x1 y1 z -> almostIn x2 y2 z)).
  intros x1 x2 Hx y1 y2 Hy.
  induction z.
   auto.
  intros H.
  destruct H as [G | H | H] using orC_ind.
    auto using almostIn_stable.
   apply orWeaken.
   left.
   rewrite <- Hx, <- Hy.
   assumption.
  apply orWeaken.
  right.
  apply IHz; assumption.
 intros x1 x2 Hx y1 y2 Hy.
 cut (forall z1 x3 : FinEnum stableX, (forall x : X, InFinEnumC x z1 -> InFinEnumC x x3) ->
   (almostIn x1 y1 z1 -> almostIn x2 y2 x3)).
  intros Z z1 z2 Hz.
  split.
   apply Z.
   intros x H.
   simpl in Hz.
   unfold FinEnum_eq in Hz.
   apply -> Hz.
   assumption.
  intros H.
  eapply Y.
    unfold QposEq.
    simpl; symmetry.
    apply Hx.
   symmetry.
   apply Hy.
  eapply Z.
   intros a Ha.
   simpl in Hz; unfold FinEnum_eq in Hz.
   apply <- Hz.
   apply Ha.
  eapply Y.
    unfold QposEq.
    simpl; symmetry.
    apply Hx.
   symmetry.
   apply Hy.
  assumption.
 induction z1; intros z2 Hz.
  contradiction.
 intros H.
 destruct H as [G | H | H] using orC_ind.
   auto using almostIn_stable.
  assert (Z:InFinEnumC a z2).
   apply Hz.
   apply orWeaken.
   left; reflexivity.
  rewrite -> Hx, Hy in H.
  clear - H Z.
  induction z2.
   apply Z.
  destruct Z as [G | Z | Z] using orC_ind.
    auto using almostIn_stable.
   rewrite -> Z in H.
   apply orWeaken.
   left; assumption.
  apply orWeaken.
  right; apply IHz2; auto.
 apply IHz1.
  intros b Hb.
  apply Hz.
  apply orWeaken.
  right; assumption.
 assumption.
Qed.
(* end hide *)
(**
** Definition of Compact
A compact set is defined as the completion of finite enumerations as
a metric space *)
Definition Compact X (stableX : stableMetric X) := Complete (FinEnum stableX).

(** A point is in a compact set if all the approximations are almost in
the approximations of the compact set. *)
Definition inCompact X stableX (x:Complete X) (s:Compact stableX) :=
 forall e1 e2, almostIn (e1 + e2) (approximate x e1) (approximate s e2).
(* begin hide *)
Add Parametric Morphism X stableX : (@inCompact X stableX) with signature (@st_eq _) ==> (@st_eq _) ==> iff as inCompact_wd.
Proof.
 cut (forall x1 x2 : Complete X, st_eq x1 x2 -> forall x3 x4 : Complete (FinEnum stableX),
   st_eq x3 x4 -> (inCompact x1 x3 -> inCompact x2 x4)).
  intros Z x1 x2 Hx y1 y2 Hy.
  split.
   apply Z; assumption.
  apply Z; symmetry; assumption.
 intros x1 x2 Hx y1 y2 Hy H e1 e2.
 apply almostIn_closed.
 intros d.
 set (d':=((1 # 4) * d)%Qpos).
 setoid_replace (e1 + e2 + d)%Qpos
   with ((e1 + d') + (d' + d') +  (d' + e2))%Qpos; [| unfold d';QposRing].
 apply almostIn_triangle_r with (approximate y1 d');[|apply Hy].
 symmetry in Hx.
 apply almostIn_triangle_l with (approximate x1 d');[apply Hx|].
 apply H.
Qed.
(* end hide *)
Section Compact.

Variable X : MetricSpace.
Hypothesis stableX : stableMetric X.

Let Compact := Compact stableX.
Let inCompact := @inCompact X stableX.

Lemma inCompact_stable : forall x s, ~~inCompact x s -> inCompact x s.
Proof.
 intros x s H e1 e2.
 apply almostIn_stable.
 intros H0.
 apply H.
 intros H1.
 apply H0.
 apply H1.
Qed.

(**
** Compact is Bishop Compact.
Here we show that our definiton of compactness satifies Bishop's compactness.

First we show that our compact sets are complete.
*)

Lemma CompactCompleteSubset : forall x, CompleteSubset _ (fun z => inCompact z x).
Proof.
 intros x a H.
 exists (Cjoin a).
  abstract ( intros e1 e2; unfold inCompact in H; eapply almostIn_weak_le;
    [|apply (H ((1#2)*e1) ((1#2)*e1) e2)%Qpos]; autorewrite with QposElim; rewrite -> Qle_minus_iff;
      ring_simplify; auto with *; apply Qmult_le_0_compat; auto with * ).
 apply CunitCjoin.
Defined.

Section CompactTotallyBounded.

(** In order to show that compact sets are totally bounded we need to assume
that the underlying metric space is located.  According to Bishop's
definition, every metric space is located.  Therefore this is a fair
assumption to make. *)
Hypothesis locatedX : locatedMetric X.

(** If a point is almost in an enumeration, then there it is close to
a point in the enumeration in a constructive sense. *)
Lemma AlmostInExists: forall (e d:Qpos) x (s:FinEnum stableX), e < d -> almostIn e x s -> {y | In y s /\ ball d x y}.
Proof.
 intros e d x s Hed.
 induction s.
  contradiction.
 intros H.
 destruct (locatedX _ _ x a Hed).
  exists a.
  abstract (auto with * ).
 destruct IHs as [y Hy].
  abstract ( apply almostIn_stable; intros H0; apply H; split; auto).
 exists y.
 abstract (destruct Hy; auto with * ).
Defined.

(** The limit of this stream is going to be used to construct a point
inside the compact set close to a suitable starting point. *)
CoFixpoint CompactTotallyBoundedStream (s:Compact) (k d1 d2:Qpos) (pt:X) Hpt : Stream X :=
Cons pt
 (let (f,_) := HausdorffBallHausdorffBallStrong locatedX
               (regFun_prf s d1 (k*d1)%Qpos) in
  let (pt',HptX) := f pt Hpt d2 in
  let (Hpt',_) := HptX in
  (CompactTotallyBoundedStream s k (k*d1) (k*d2) pt' Hpt')).

(*
Lemma CompactTotallyBoundedStream_PI : forall n (s:Compact) (k d1 d2:Qpos) (pt:X) Hpt1 Hpt2,
(Str_nth n (CompactTotallyBoundedStream s k d1 d2 pt Hpt1))=(Str_nth n (CompactTotallyBoundedStream s k d1 d2 pt Hpt2)).
Proof.
induction n.
 reflexivity.
intros.
unfold Str_nth.
simpl.
unfold HausdorffBallHausdorffBallStrong.
case (@regFun_prf (FinEnum X stableX) s d1 (Qpos_mult k d1)).
intros H _.
set (A:=HemiMetricHemiMetricStrong X locatedX (d1 + k * d1)
            (fun x : X => InFinEnumC X x (approximate s d1))
            (approximate s (k * d1)%Qpos) H pt Hpt1 d2).
set (B:=HemiMetricHemiMetricStrong X locatedX (d1 + k * d1)
            (fun x : X => InFinEnumC X x (approximate s d1))
            (approximate s (k * d1)%Qpos) H pt Hpt2 d2).
assert ((let (y,_) := A in y) = (let (y,_):= B in y)).
 clear - A B.
 unfold A, B.
 clear A B.
 unfold HemiMetricHemiMetricStrong.
 generalize (H pt Hpt1) (H pt Hpt2).
 clear H.
 induction ((approximate s (k * d1)%Qpos)).
  intros e.
  elim e.
  intros x [Y _].
  apply Y.
 intros C0 C1.
 simpl.
 destruct (locatedX pt a (HemiMetricHemiMetricStrong_subproof0 (d1 + k * d1) d2));
  simpl.
  reflexivity.
 simpl in *.
 apply IHm.
revert H0.
destruct A as [a Ha].
destruct B as [b Hb].
intros H0.
revert Ha Hb.
rewrite H0.
intros [Ha _] [Hb _].
rapply IHn.
Qed.
*)

(** This stream is Cauchy *)
Lemma CompactTotallyBoundedStreamCauchyLemma : forall n (k d:Qpos),
k < 1 ->
0 < (d*(1-k^(S n))/(1-k)).
Proof.
 intros n k d Hk.
 repeat (apply: mult_resp_pos; simpl); auto with *.
  unfold Qminus.
  rewrite <- Qlt_minus_iff.
  induction n.
   assumption.
  simpl.
  rewrite Pplus_one_succ_l.
  rewrite -> Qpower_plus_positive.
  apply Qlt_trans with (k*1).
   apply: mult_resp_less_lft;simpl; auto with *.
  ring_simplify.
  assumption.
 apply Qlt_shift_inv_l.
  unfold Qminus.
  rewrite <- Qlt_minus_iff.
  assumption.
 ring_simplify.
 constructor.
Qed.

Lemma CompactTotallyBoundedStreamCauchy1 : forall n s (k d1 d2:Qpos) pt Hpt
 (Hd:0 < ((((1#1)+k)*d1+d2)%Qpos*(1-k^(S n))/(1-k))), k < 1 ->
 ball (mkQpos Hd) pt (Str_nth n (CompactTotallyBoundedStream s k d1 d2 pt Hpt)).
Proof.
 induction n; intros s k d1 d2 pt Hpt Hd Hk.
  apply ball_refl.
 unfold Str_nth.
 set (e:=(((1#1) + k) * d1 + d2)%Qpos * (1 - k ^ S (S n)) / (1 - k)) in *.
 set (e':=(mkQpos Hd)).
 set (e0:=((d1 + k * d1 + d2) + mkQpos
   (CompactTotallyBoundedStreamCauchyLemma n _ (((1#1)+k)*(k*d1) + (k*d2)) Hk))%Qpos).
 setoid_replace e' with e0.
  simpl.
  destruct (HausdorffBallHausdorffBallStrong locatedX (regFun_prf s d1 (k * d1)%Qpos)) as [f _].
  destruct (f pt Hpt d2) as [pt' [Hpt' Hpt'']].
  unfold e0.
  apply ball_triangle with pt'.
   assumption.
  apply IHn; assumption.
 unfold e', e0, e.
 unfold QposEq.
 autorewrite with QposElim.
 change (S (S n)) with (1+(S n))%nat.
 change (S n) with (1 + n)%nat.
 repeat rewrite inj_plus.
 assert (~k==0).
  apply Qpos_nonzero.
 repeat rewrite -> Qpower_plus; auto.
 simpl; field.
 intros H0.
 apply (Qlt_not_le _ _ Hk).
 rewrite -> Qle_minus_iff.
 replace RHS with (-(1-k)) by simpl; ring.
 rewrite -> H0.
 discriminate.
Qed.

Lemma CompactTotallyBoundedStreamCauchy2 : forall (m n:nat) s (k d1 d2:Qpos) pt Hpt
 (Hd:0 < ((((1#1)+k)*d1+d2)%Qpos*(1-k^(S n))/(1-k))), k < 1 ->
 ball (k^m*(mkQpos Hd))
  (Str_nth m (CompactTotallyBoundedStream s k d1 d2 pt Hpt))
  (Str_nth (m + n) (CompactTotallyBoundedStream s k d1 d2 pt Hpt)).
Proof.
 induction m; intros n s k d1 d2 pt Hpt Hd Hk.
  setoid_replace (k^0 * (mkQpos Hd))%Qpos with (mkQpos Hd); [| QposRing].
  apply CompactTotallyBoundedStreamCauchy1; assumption.
 pose (e':=(CompactTotallyBoundedStreamCauchyLemma n _ (((1#1)+k)*(k*d1) + (k*d2)) Hk)%Qpos).
 setoid_replace (k^S m*mkQpos Hd)%Qpos with (k^m*mkQpos e')%Qpos.
  replace (S m + n)%nat with (S (m + n))%nat by omega.
  unfold Str_nth.
  simpl.
  destruct (HausdorffBallHausdorffBallStrong locatedX (regFun_prf s d1 (k * d1)%Qpos)) as [f _].
  destruct (f pt Hpt d2) as [pt' [Hpt' _]].
  simpl.
  apply (IHm n s k (k*d1)%Qpos (k*d2)%Qpos pt' Hpt' e'); assumption.
 unfold QposEq.
 autorewrite with QposElim.
 change (S n) with (1 + n)%nat.
 change (S m) with (1 + m)%nat.
 repeat rewrite inj_plus.
 assert (~k==0).
  apply Qpos_nonzero.
 repeat rewrite -> Qpower_plus; auto.
 simpl; field.
 intros H0.
 apply (Qlt_not_le _ _ Hk).
 rewrite -> Qle_minus_iff.
 replace RHS with (-(1-k)) by simpl; ring.
 rewrite -> H0.
 discriminate.
Qed.

Lemma StreamInCompactApprox : forall n s k d1 d2 pt Hpt,
  {q:Qpos | InFinEnumC (Str_nth n (CompactTotallyBoundedStream s k d1 d2 pt Hpt)) (approximate s q) & q==k^n*d1}.
Proof.
 induction n.
  intros.
  exists d1.
   assumption.
  simpl; ring.
 intros.
 unfold Str_nth.
 simpl.
 destruct (HausdorffBallHausdorffBallStrong locatedX (regFun_prf s d1 (k * d1)%Qpos)) as [f _].
 destruct (f pt Hpt d2) as [pt' [Hpt' _]].
 destruct (IHn s k (k*d1) (k*d2) pt' Hpt')%Qpos as [q Hq Hq0].
 exists q.
  apply Hq.
 change (q==k^(P_of_succ_nat n)*d1).
 rewrite Zpos_P_of_succ_nat.
 unfold Zsucc.
 rewrite -> Qpower_plus;[|apply Qpos_nonzero].
 autorewrite with QposElim in Hq0.
 ring [Hq0].
Qed.

Definition CompactTotallyBoundedIndex (e d1 d2:Qpos) : nat :=
let (n,d):=((1+(1#4))*d1 + d2)/e/(1-(1#4)) in
 match Zsucc (Zdiv n d) with
| Zpos p => div2 (S (Z_to_nat (log_sup_correct1 p)))
| _ => O
end.

Hint Resolve Qinv_lt_0_compat. (* todo: move, and put in appropriate hint db *)

Lemma CompactTotallyBoundedIndexLemma : forall (e d1 d2:Qpos),
((1+(1#4))*d1 + d2)*(1#4)^(CompactTotallyBoundedIndex e d1 d2)/(1-(1#4)) <= e.
Proof.
 intros e d1 d2.
 unfold CompactTotallyBoundedIndex.
 set (a:=((1 + (1 # 4)) * d1 + d2)).
 set (b:=(1 - (1 # 4))).
 rewrite -> Qmake_Qdiv.
 rewrite -> Qdiv_power.
 rewrite -> Qpower_1.
 unfold Qdiv.
 ring_simplify.
 rewrite <- Qmult_assoc.
 rewrite -> Qmult_comm.
 rewrite <- Qmult_assoc.
 rewrite -> Qmult_comm.
 apply Qle_shift_div_r.
  induction (let (n, d) := a * / e * / b in match Zsucc (n / d) with | Z0 => 0%nat
    | Zpos p => div2 (S (Z_to_nat (z:=log_sup p) (log_sup_correct1 p))) | Zneg _ => 0%nat end).
   constructor.
  change (S n) with (1+n)%nat.
  rewrite inj_plus.
  rewrite -> Qpower_plus;[|discriminate].
  change 0 with (4*0).
  apply: mult_resp_less_lft; auto.
  constructor.
 assert (He:~e==0).
  apply Qpos_nonzero.
 set (z:=a * / e * / b).
 rewrite <- (Qinv_involutive e).
 rewrite -> (Qmult_comm (/ /e)).
 apply Qle_shift_div_l.
  auto with *.
 replace LHS with z by (unfold z;simpl; ring).
 assert (Hz:0 < z).
  unfold z.
  subst a.
  apply Q.Qmult_lt_0_compat; auto with *.
  apply Q.Qmult_lt_0_compat; auto with *.
  apply Q.Qplus_lt_le_0_compat; auto with *.
    (* todo: this is ugly ^ *)
 destruct z as [[|n|n] d].
   elim (Qlt_not_le _ _ Hz).
   discriminate.
  apply Qle_trans with (Zsucc (n/d)).
   rewrite -> Qmake_Qdiv.
   apply Qle_shift_div_r; auto with *.
   unfold Zsucc, Qle.
   simpl.
   rewrite Zpos_mult_morphism.
   ring_simplify.
   rewrite Zmult_comm.
   replace LHS with (d * (n / d) + n mod d)%Z by (apply Z_div_mod_eq; auto with * ).
   apply Zplus_le_compat_l.
   destruct (Z_mod_lt n d); auto with *.
  generalize (Zsucc (n/d)).
  intros z.
  clear -z.
  destruct z.
    discriminate.
   change (4%positive:Z) with (2^2)%Z.
   rewrite -> Zpower_Qpower;[|discriminate].
   rewrite <- Qpower_mult.
   apply Qle_trans with (two_p (log_sup p)).
    unfold Qle; simpl.
    rewrite Pmult_comm;simpl.
    ring_simplify.
    destruct (log_sup_correct2 p).
    auto.
   generalize  (log_sup p) (log_sup_correct1 p).
   intros z Hz.
   clear p.
   cut (z <=  (2 * div2 (S (Z_to_nat (z:=z) Hz))))%Z.
    generalize ((2 * div2 (S (Z_to_nat (z:=z) Hz))))%Z.
    intros y Hy.
    rewrite <- Zpower_Qpower; auto with *.
    unfold Qle.
    simpl.
    ring_simplify.
    replace y with (z + (y-z))%Z by ring.
    rewrite Zpower_exp; auto with *.
    replace  (two_p z) with (2^z)%Z.
     replace LHS with ((2^z)*1)%Z by ring.
     apply Zmult_le_compat_l.
      assert (H:(0 <= y - z)%Z) by auto with *.
      destruct (y -z)%Z; try discriminate.
       simpl.
       change 1%Z with (Zsucc 0)%Z.
       apply Zlt_le_succ.
       apply Zpower_pos_pos; constructor.
      elim H; reflexivity.
     destruct z as [|z|z].
       discriminate.
      simpl.
      apply Zlt_le_weak.
      apply Zpower_pos_pos; constructor.
     elim Hz; constructor.
    destruct z as [|z|z].
      reflexivity.
     simpl.
     clear - z.
     induction z using Pind; simpl.
      reflexivity.
     rewrite Pplus_one_succ_l.
     rewrite Zpower_pos_is_exp.
     rewrite two_power_pos_is_exp.
     rewrite IHz.
     reflexivity.
    elim Hz; constructor.
   replace LHS with (Z_to_nat Hz:Z) by (apply Z_to_nat_correct).
   generalize (Z_to_nat (z:=z) Hz).
   intros n.
   clear - n.
   change 2%Z with (2%nat:Z).
   rewrite <- inj_mult.
   apply inj_le.
   replace RHS with (double (div2 (S n))) by (unfold double; omega).
   destruct (even_or_odd n).
    apply le_S_n.
    rewrite <- odd_double; auto with *.
   rewrite <- even_double; auto with *.
  discriminate.
 discriminate Hz.
Qed.

Definition CompactTotallyBounded_raw  (s:Compact) (d1 d2:Qpos) (pt:X) Hpt (e:QposInf) : X :=
match e with
|QposInfinity => pt
|Qpos2QposInf e' => (Str_nth (CompactTotallyBoundedIndex e' d1 d2)
  (CompactTotallyBoundedStream s (1#4) d1 d2 pt Hpt))
end.

(*
Lemma CompactTotallyBounded_raw_PI : forall s d1 d2 pt Hpt1 Hpt2 e,
 (CompactTotallyBounded_raw s d1 d2 pt Hpt1 e) = (CompactTotallyBounded_raw s d1 d2 pt Hpt2 e).
Proof.
intros.
destruct e; try reflexivity.
unfold CompactTotallyBounded_raw.
apply CompactTotallyBoundedStream_PI.
Qed.
*)

(** This stream forms a regular function *)
Lemma CompactTotallyBounded_prf : forall (s:Compact) (d1 d2:Qpos) (pt:X) Hpt,
 is_RegularFunction (CompactTotallyBounded_raw s d1 d2 pt Hpt).
Proof.
 unfold CompactTotallyBounded_raw, is_RegularFunction.
 cut (forall (s : Compact) (d1 d2 : Qpos) (pt : X)
   (Hpt : InFinEnumC pt (approximate s d1)) (e1 e2 : Qpos),
     ((CompactTotallyBoundedIndex e1 d1 d2) <= (CompactTotallyBoundedIndex e2 d1 d2))%nat ->
       ball (m:=X) (e1 + e2) (Str_nth (CompactTotallyBoundedIndex e1 d1 d2)
         (CompactTotallyBoundedStream s (1 # 4) d1 d2 pt Hpt))
           (Str_nth (CompactTotallyBoundedIndex e2 d1 d2)
             (CompactTotallyBoundedStream s (1 # 4) d1 d2 pt Hpt))).
  intros Z s d1 d2 pt Hpt e1 e2.
  destruct (le_lt_dec (CompactTotallyBoundedIndex e1 d1 d2) (CompactTotallyBoundedIndex e2 d1 d2)).
   apply Z; auto.
  setoid_replace (e1 + e2)%Qpos with (e2 + e1)%Qpos; [| QposRing].
  apply ball_sym.
  apply Z; auto with *.
 intros s d1 d2 pt Hpt e1 e2 H.
 set (A:=CompactTotallyBoundedIndex e1 d1 d2) in *.
 set (B:=CompactTotallyBoundedIndex e2 d1 d2) in *.
 rewrite (le_plus_minus _ _ H).
 assert (Y:(1#4)%Qpos < 1).
  constructor.
 assert (Y0:= (CompactTotallyBoundedStreamCauchyLemma (B-A) _ (((1#1)+(1#4))*d1 + d2) Y)%Qpos).
 eapply ball_weak_le; [|apply (CompactTotallyBoundedStreamCauchy2 A _ s pt Hpt Y0);constructor].
 autorewrite with QposElim.
 unfold Qdiv.
 set (C:=(((1 + (1 # 4)) * d1 + d2) * (1 # 4) ^ A * / (1 - (1 # 4)))).
 replace LHS with ((1 - (1 # 4) ^ S (B - A)) * C) by (unfold C; simpl; ring).
 apply Qle_trans with (1*C).
  apply: mult_resp_leEq_rht;simpl.
   rewrite -> Qle_minus_iff.
   ring_simplify.
   apply Qpower_pos_positive.
   discriminate.
  unfold C.
  change (1-(1#4)) with (3#4).
  Qauto_nonneg.
  apply Qpower_pos.
  discriminate.
 ring_simplify.
 apply Qle_trans with e1.
  apply CompactTotallyBoundedIndexLemma.
 Qauto_le.
Qed.

Definition CompactTotallyBounded_fun  (s:Compact) (d1 d2:Qpos) (pt:X) Hpt : Complete X :=
 Build_RegularFunction (CompactTotallyBounded_prf s d1 d2 pt Hpt).

(** The limit is inside the compact set *)
Lemma CompactTotallyBoundedInCompact : forall (s:Compact) (d1 d2:Qpos) (pt:X) Hpt,
 inCompact (CompactTotallyBounded_fun s d1 d2 pt Hpt) s.
Proof.
 intros s d1 d2 pt Hpt e1 e2.
 simpl.
 destruct (StreamInCompactApprox (CompactTotallyBoundedIndex e1 d1 d2) s (1#4) d1 d2 pt Hpt)
   as [q Hq Hq0].
 apply almostIn_closed.
 intros d.
 apply almostIn_weak_le with (d + (q + e2))%Qpos.
  autorewrite with QposElim.
  rewrite -> Qle_minus_iff.
  replace RHS with (e1 + - q) by simpl; ring.
  rewrite <- Qle_minus_iff.
  rewrite -> Hq0.
  eapply Qle_trans;[|apply (CompactTotallyBoundedIndexLemma e1 d1 d2)].
  autorewrite with QposElim.
  cut (0 <= (1 # 4) ^ CompactTotallyBoundedIndex e1 d1 d2).
   generalize ( (1 # 4) ^ CompactTotallyBoundedIndex e1 d1 d2).
   intros z Hz.
   clear - Hz.
   rewrite -> Qle_minus_iff.
   replace  RHS with (z*((d1 + 2*d2)/(3#2))) by simpl; field.
   Qauto_nonneg.
  apply Qpower_pos.
  discriminate.
 eapply almostIn_triangle_r;[|apply regFun_prf].
 apply <- InAlmostIn.
 assumption.
Qed.

(** The limit is close to the initial starting point *)
Lemma CompactTotallyBoundedNotFar : forall (s:Compact) (d1 d2:Qpos) (pt:X) Hpt,
 ball ((5#3)*d1 + (4#3)*d2) (Cunit pt) (CompactTotallyBounded_fun s d1 d2 pt Hpt).
Proof.
 intros s d1 d2 pt Hpt e1 e2.
 simpl.
 assert (Z:(1#4)%Qpos < 1) by constructor.
 assert (Z0:=(CompactTotallyBoundedStreamCauchyLemma (CompactTotallyBoundedIndex e2 d1 d2) _ (((1#1)+(1#4))*(d1) + (d2)) Z)%Qpos).
 eapply ball_weak_le;
   [|apply (CompactTotallyBoundedStreamCauchy1 (CompactTotallyBoundedIndex e2 d1 d2) s pt Hpt Z0);constructor].
 autorewrite with QposElim.
 apply Qle_trans with (((1 + (1 # 4)) * d1 + d2) / (1 - (1 # 4))).
  apply: mult_resp_leEq_rht; try discriminate.
  replace RHS with (((1 + (1 # 4)) * d1 + d2)*1) by simpl; ring.
  apply mult_resp_leEq_lft.
   simpl.
   rewrite -> Qle_minus_iff.
   ring_simplify.
   apply (Qpower_pos (1#4) (P_of_succ_nat (CompactTotallyBoundedIndex e2 d1 d2))).
   discriminate.
  simpl.
  apply Qlt_le_weak.
  apply Q.Qplus_lt_le_0_compat; auto with *.
 rewrite -> Qle_minus_iff.
 unfold Qdiv.
 change (/(1-(1#4))) with (4#3).
 ring_simplify.
 apply Qlt_le_weak.
 apply Q.Qplus_lt_le_0_compat; auto with *.
Qed.

(** Using CompactTotallyBounded_fun we can map the approximation of
a compact set to a new enumeration that contains only points inside
the compact sets, without moving the points too much *)
Definition CompactTotalBound (s:Compact) (e:Qpos) : list (Complete X).
Proof.
 generalize (CompactTotallyBounded_fun s ((1#5)*e) ((1#5)*e)).
 induction (approximate s ((1 # 5) * e)%Qpos).
  intros _.
  exact nil.
 intros H.
 apply cons.
  apply H with a.
  apply InFinEnumC_weaken; auto with *.
 apply IHs0.
 intros pt Hpt.
 apply H with pt.
 apply orWeaken;right;assumption.
Defined.

Lemma CompactTotalBoundNotFar : forall SCX (s:Compact) (e:Qpos),
 ball ((3#5)*e) (map Cunit (approximate s ((1#5)*e)%Qpos):FinEnum SCX) (CompactTotalBound s e).
Proof.
 intros SCX s e.
 unfold CompactTotalBound.
 generalize (CompactTotallyBoundedNotFar s ((1#5)*e) ((1#5)*e)).
 generalize (CompactTotallyBounded_fun s ((1 # 5) * e) ((1 # 5) * e)).
 induction (approximate s ((1 # 5) * e)%Qpos); intros H L.
  apply ball_refl.
 split; intros x Hx.
  destruct Hx as [G | Hx | Hx] using orC_ind.
    auto using existsC_stable.
   apply existsWeaken.
   exists (H a (InFinEnumC_weaken X a (a :: s0) (in_eq a s0))).
   split.
    apply: orWeaken.
    left.
    reflexivity.
   rewrite -> Hx.
   setoid_replace ((3 # 5) * e)%Qpos with ((5 # 3) * ((1 # 5) * e) + (4 # 3) * ((1 # 5) * e))%Qpos; [| QposRing].
   apply L.
  set (H':=(fun pt (Hpt : InFinEnumC pt s0) => H pt (orWeaken _ _ (right Hpt)))).
  assert (L':forall (pt : X) (Hpt : InFinEnumC pt s0),
    ball (m:=Complete X) ((5 # 3) * ((1 # 5) * e) + (4 # 3) * ((1 # 5) * e)) (Cunit pt) (H' pt Hpt)).
   intros pt Hpt.
   apply L.
  destruct (IHs0 H' L') as [A _].
  destruct (A x Hx) as [G | y [Hy0 Hy1]] using existsC_ind.
   auto using existsC_stable.
  apply existsWeaken.
  exists y.
  split; auto.
  apply: orWeaken.
  right; assumption.
 destruct Hx as [G | Hx | Hx] using orC_ind.
   auto using existsC_stable.
  apply existsWeaken.
  exists (Cunit a).
  split.
   apply: orWeaken.
   left.
   reflexivity.
  rewrite -> Hx.
  setoid_replace ((3 # 5) * e)%Qpos with ((5 # 3) * ((1 # 5) * e) + (4 # 3) * ((1 # 5) * e))%Qpos; [| QposRing].
  apply ball_sym.
  apply L.
 set (H':=(fun pt (Hpt : InFinEnumC pt s0) => H pt (orWeaken _ _ (right Hpt)))).
 assert (L':forall (pt : X) (Hpt : InFinEnumC pt s0),
   ball (m:=Complete X) ((5 # 3) * ((1 # 5) * e) + (4 # 3) * ((1 # 5) * e)) (Cunit pt) (H' pt Hpt)).
  intros pt Hpt.
  apply L.
 destruct (IHs0 H' L') as [_ A].
 destruct (A x Hx) as [G | y [Hy0 Hy1]] using existsC_ind.
  auto using existsC_stable.
 apply existsWeaken.
 exists y.
 split; auto.
 apply: orWeaken.
 right; assumption.
Qed.

(** This means that our compact sets are totally bounded. *)
Lemma CompactTotallyBoundedA : forall s e y, In y (CompactTotalBound s e) -> inCompact y s.
Proof.
 intros s e y.
 unfold CompactTotalBound.
 generalize (CompactTotallyBoundedInCompact s ((1#5)*e) ((1#5)*e)).
 generalize (CompactTotallyBounded_fun s ((1#5)*e) ((1#5)*e)).
 generalize (approximate s ((1 # 5) * e)%Qpos).
 intros l.
 induction l.
  contradiction.
 intros F L [H|H].
  rewrite <- H.
  apply L.
 eapply (IHl);[|apply H].
 intros pt Hpt.
 apply L.
Qed.

Lemma CompactTotallyBoundedB : forall s e x, (inCompact x s) -> exists y, In y (CompactTotalBound s e) /\ ball e x y.
Proof.
 intros s e x Hx.
 assert (Z:((1 # 20) * e + (1 # 5) * e)%Qpos < ((7 # 20) * e)%Qpos).
  rewrite -> Qlt_minus_iff.
  autorewrite with QposElim.
  ring_simplify.
  Qauto_pos.
 destruct (AlmostInExists _ _ (approximate x ((1#20)*e)%Qpos) (approximate s ((1#5)*e)%Qpos) Z (Hx _ _))
   as [y [Hy0 Hy1]].
 clear Z.
 unfold CompactTotalBound.
 revert Hy0.
 cut (forall pt Hpt, ball ((3#5)*e) (Cunit pt) (CompactTotallyBounded_fun s ((1#5)*e) ((1#5)*e) pt Hpt)).
  generalize (CompactTotallyBounded_fun s ((1#5)*e) ((1#5)*e)).
  generalize (approximate s ((1 # 5) * e)%Qpos).
  intros l.
  induction l.
   contradiction.
  intros F HF [H|H].
   econstructor.
   split.
    left.
    reflexivity.
   rewrite <- H in Hy1.
   clear - Hy1 HF.
   setoid_replace e with ((1#20)*e + (7#20)*e + (3#5)*e)%Qpos; [| QposRing].
   apply ball_triangle with (Cunit a);[|apply HF].
   apply ball_triangle with (Cunit (approximate x ((1#20)*e)%Qpos)).
    apply ball_approx_r.
   rewrite -> ball_Cunit.
   assumption.
  edestruct (fun F HF => IHl F HF H) as [y' [Hy'0 Hy'1]];
    [|exists y';split;[right;apply Hy'0|assumption]].
  intros pt Hpt.
  apply: HF.
 intros pt Hpt.
 setoid_replace ((3#5)*e)%Qpos with ((5#3)*((1#5)*e) + (4#3)*((1#5)*e))%Qpos; [| QposRing].
 apply CompactTotallyBoundedNotFar.
Qed.

Lemma CompactTotallyBounded : forall s, TotallyBoundedSubset _ (fun z => inCompact z s).
Proof.
 intros s e.
 exists (CompactTotalBound s e).
  apply CompactTotallyBoundedA.
 apply CompactTotallyBoundedB.
Defined.



(** And hence our compact sets are Bishop compact. *)
Lemma CompactAsBishopCompact : forall s, CompactSubset _ (fun z => inCompact z s).
Proof.
 intros s.
 split.
   apply CompactCompleteSubset.
  apply CompactTotallyBounded.
 abstract ( intros a b Hab; unfold inCompact; rewrite -> Hab; reflexivity).
Defined.

End CompactTotallyBounded.

(**
** Bishop Compact is Compact.
Next we must show that Bishop compact sets are compact according to our
definition.

Given a Bishop compact set we construct finite enumerations that approximate
that set. *)
Definition BishopCompactAsCompact_raw
 (P:Complete X->Prop) (HP:CompactSubset _ P) (e:QposInf) : (FinEnum stableX) :=
match e with
|QposInfinity => nil
|Qpos2QposInf e' =>
  (let (l,_,_) := (totallyBoundedSubset HP ((1#2)*e')) in
   map (fun x => approximate x ((1#2)*e')) l)%Qpos
end.

(** These approximations are coherent *)
Lemma BishopCompactAsCompact_prf :
 forall P (HP:CompactSubset _ P), is_RegularFunction (BishopCompactAsCompact_raw HP).
Proof.
 cut (forall (P : RegularFunction X -> Prop) (HP : CompactSubset (Complete X) P) (e1 e2 : Qpos),
   hemiMetric X (e1 + e2) (fun a : X => InFinEnumC a
     (let (l, _, _) := totallyBoundedSubset HP ((1 # 2) * e1)%Qpos in
       map (fun x : RegularFunction X => approximate x ((1 # 2) * e1)%Qpos) l)) (fun a : X =>
         InFinEnumC a (let (l, _, _) := totallyBoundedSubset HP ((1 # 2) * e2)%Qpos in
           map (fun x : RegularFunction X => approximate x ((1 # 2) * e2)%Qpos) l))).
  intros Z P [HP0 HP HP1] e1 e2.
  split.
   apply Z.
  apply (hemiMetric_wd1 X (e2+e1)%Qpos).
   QposRing.
  apply Z.
 intros P [HP0 HP HP1] e1 e2 x Hx.
 simpl in *.
 destruct (HP ((1 # 2) * e1)%Qpos) as [l Hl0 Hl1].
 destruct (HP ((1 # 2) * e2)%Qpos) as [r Hr0 Hr1].
 simpl in *.
 assert (Z0:existsC (Complete X) (fun x' => In x' l /\ ball ((1#2)*e1) (Cunit x) x')).
  clear - Hx HP1.
  induction l.
   elim Hx.
  destruct Hx as [ G | Hx | Hx] using orC_ind.
    auto using existsC_stable.
   apply existsWeaken.
   exists a.
   split; auto with *.
   rewrite -> Hx.
   apply ball_approx_l.
  destruct (IHl Hx) as [G | z [Hz0 Hz1]] using existsC_ind.
   auto using existsC_stable.
  apply existsWeaken.
  exists z.
  auto with *.
 destruct Z0 as [ G | z [Hz0 Hz1] ] using existsC_ind.
  auto using existsC_stable.
 destruct (Hr1 _ (Hl0 _ Hz0)) as [ y [Hy0 Hy1]].
 apply existsWeaken.
 exists (approximate y ((1#2)%Qpos*e2)).
 split.
  clear - Hy0.
  induction r.
   elim Hy0.
  destruct Hy0 as [Hy0 | Hy0].
   rewrite Hy0.
   apply: orWeaken.
   left.
   reflexivity.
  apply: orWeaken.
  right.
  apply IHr; auto.
 setoid_replace (e1+e2)%Qpos with ((1#2)*e1 + (1#2)*e2 + (1#2)*e2 + (1#2)*e1)%Qpos; [| QposRing].
 apply ball_weak.
 rewrite <- ball_Cunit.
 repeat eapply ball_triangle.
   apply Hz1.
  change (ball ((1 # 2) * e2) z y) in Hy1.
  apply Hy1.
 apply ball_approx_r.
Qed.

(** Hence Bishop compact sets are compact in our sense. *)
Definition BishopCompactAsCompact
 (P:Complete X->Prop) (HP:CompactSubset _ P) : Compact :=
Build_RegularFunction (BishopCompactAsCompact_prf HP).

Section Isomorphism.

(**
** Isomorphism
We claim that Bishop compact sets correspond to our compact sets, but
to be sure we need to show that the definitions are isomoprhic.  We
need to show that the conversions back and forth are equivalent to the
identity. *)
Hypothesis locatedX : locatedMetric X.

Lemma BishopCompact_Compact_BishopCompact1 :
 forall (P:Complete X->Prop) (HP:CompactSubset _ P) x,
  P x -> inCompact x (BishopCompactAsCompact HP).
Proof.
 intros P [HP1 HP2 HP3] x Hx e1 e2.
 simpl.
 destruct (HP2 ((1 # 2) * e2)%Qpos) as [l Hl0 Hl1].
 destruct (Hl1 x Hx) as [y [Hy0 Hy1]].
 clear - Hy0 Hy1.
 induction l.
  contradiction.
 destruct Hy0 as [Hy0|Hy0].
  rewrite Hy0.
  apply: orWeaken.
  left.
  rewrite <- ball_Cunit.
  setoid_replace (e1+e2)%Qpos with (e1 + ((1 # 2) * e2 + (1 # 2) * e2))%Qpos; [| QposRing].
  apply ball_triangle with x.
   apply ball_approx_l.
  apply ball_triangle with y.
   assumption.
  apply ball_approx_r.
 apply: orWeaken.
 right.
 apply IHl.
 auto with *.
Qed.

Lemma BishopCompact_Compact_BishopCompact2 :
 forall (P:Complete X->Prop) (HP:CompactSubset _ P) x,
  inCompact x (BishopCompactAsCompact HP) -> P x.
Proof.
 intros P [HP1 HP2 HP3] x Hx.
 assert (Y:forall e:Qpos, ((7#8)*e)%Qpos < e).
  intros.
  rewrite -> Qlt_minus_iff.
  autorewrite with QposElim.
  ring_simplify.
  Qauto_pos.
 assert (A:forall e, {y | P y /\ ball (m:=Complete X) e x y}).
  intros e.
  assert (Hx':=Hx ((1#16)*e)%Qpos ((1#2)*e)%Qpos).
  simpl in Hx'.
  clear - Hx' locatedX Y.
  destruct (HP2 ((1 # 2) * ((1 # 2) * e))%Qpos) as [l Hl0 Hl1].
  clear Hl1.
  induction l.
   contradiction.
  destruct (Complete_located locatedX _ _ x a (Y e)) as [A|A].
   exists a.
   split; auto.
  apply IHl.
   intros y Hy.
   apply Hl0; auto with *.
  destruct Hx' as [G | Hx' | Hx'] using orC_ind.
    auto using almostIn_stable.
   elim A.
   clear - Hx'.
   rewrite <- ball_Cunit in Hx'.
   setoid_replace ((7 # 8) * e)%Qpos with ((1#16)*e + ((1 # 16) * e + (1 # 2) * e) + (((1 # 2) * ((1 # 2) * e))))%Qpos
     ; [| QposRing].
   eapply ball_triangle.
    eapply ball_triangle.
     apply ball_approx_r.
    apply Hx'.
   apply ball_approx_l.
  assumption.
 set (f:=fun e => (let (y,_):= (A e) in y)).
 assert (Hf0:forall e, ball (m:=Complete X) (e) (f e) x).
  intros e.
  unfold f.
  destruct (A e) as [y [_ Hy]].
  apply ball_sym.
  assumption.
 assert (Hf:is_RegularFunction (fun e => match e with QposInfinity => f (1#1)%Qpos | Qpos2QposInf e' => f e' end)).
  intros e1 e2.
  apply ball_triangle with x.
   apply Hf0.
  apply ball_sym.
  apply Hf0.
 set (f':=(Build_RegularFunction Hf)).
 assert (Hf1 : forall (e:Qpos), P (approximate f' e)).
  intros e.
  simpl; unfold f.
  destruct (A e).
  tauto.
 destruct (HP1 f') as [y Hy].
  intros [e|]; apply: Hf1.
 unfold ExtSubset in HP3.
 rewrite -> (HP3 x y); auto.
 rewrite <- Cunit_eq.
 rewrite -> s.
 intros e1 e2.
 apply ball_sym.
 setoid_replace (e1+e2)%Qpos with (e2+e1)%Qpos; [| QposRing].
 apply ball_weak.
 apply Hf0.
Qed.

Lemma BishopCompact_Compact_BishopCompact :
 forall (P:Complete X->Prop) (HP:CompactSubset _ P) x,
  P x <-> inCompact x (BishopCompactAsCompact HP).
Proof.
 intros P HP x.
 split.
  apply BishopCompact_Compact_BishopCompact1.
 apply BishopCompact_Compact_BishopCompact2.
Qed.

Lemma Compact_BishopCompact_Compact : forall s,
 st_eq s (BishopCompactAsCompact (CompactAsBishopCompact locatedX s)).
Proof.
 intros s e1 e2.
 setoid_replace (e1 + e2)%Qpos with (e1 + (1#5)*((1#2)*e2) + ((3#5)*((1#2)*e2) + (1#2)*e2) + (1#10)*e2)%Qpos; [| QposRing].
 apply ball_weak.
 apply ball_triangle with (approximate s ((1#5)*((1#2)*e2))%Qpos).
  apply regFun_prf.
 clear e1.
 rewrite -> (@FinEnum_map_Cunit _ stableX (Complete_stable stableX)).
 apply ball_triangle with (CompactTotalBound locatedX s ((1 # 2) * e2)).
  apply CompactTotalBoundNotFar.
 simpl.
 change (FinEnum_ball (Complete X)) with (@ball (FinEnum (Complete_stable stableX))).
 induction (CompactTotalBound locatedX s ((1 # 2) * e2)).
  apply ball_refl.
 destruct IHl as [IHlA IHlB].
 split; intros x Hx; (destruct Hx as [G | Hx | Hx] using orC_ind; [auto using existsC_stable
   |apply existsWeaken |]).
    exists (Cunit (approximate a ((1 # 2) * e2)%Qpos)).
    split.
     apply: orWeaken.
     left; reflexivity.
    rewrite -> Hx.
    apply ball_approx_r.
   destruct (IHlA x Hx) as [ G | y [Hy0 Hy1]] using existsC_ind.
    auto using existsC_stable.
   apply existsWeaken.
   exists y.
   split; auto.
   apply: orWeaken.
   right.
   assumption.
  exists a.
  split.
   apply orWeaken.
   left; reflexivity.
  rewrite -> Hx.
  apply: ball_approx_l.
 destruct (IHlB x Hx) as [ G | y [Hy0 Hy1]] using existsC_ind.
  auto using existsC_stable.
 apply existsWeaken.
 exists y.
 split; auto.
 apply orWeaken.
 right.
 assumption.
Qed.

End Isomorphism.

End Compact.

Require Import Prelength.

Section CompactDistr.

Variable X : MetricSpace.
Hypothesis stableX : stableMetric X.
Hypothesis stableCX : stableMetric (Complete X).

(**
** FinEnum distributes over Complete
The FiniteEnumeration monad distributes over the Completion monad.
This corresponds to a function from FinEnum (Complete X) to
Complete (FinEnum X).
*)
Definition FinCompact_raw (x: FinEnum stableCX) (e:QposInf) : FinEnum stableX :=
map (fun x => approximate x e) x.

Lemma FinCompact_prf : forall x, is_RegularFunction (FinCompact_raw x).
Proof.
 intros x.
 cut (forall e1 e2, hemiMetric X (e1 + e2) (fun a : X => InFinEnumC a (FinCompact_raw x e1))
   (fun a : X => InFinEnumC a (FinCompact_raw x e2))).
  intros L e1 e2.
  split; auto.
  eapply hemiMetric_wd1;[|apply L].
  QposRing.
 intros e1 e2.
 induction x.
  apply hemiMetric_refl.
 intros b Hb.
 destruct Hb as [G | Hb | Hb] using orC_ind.
   auto using existsC_stable.
  apply existsWeaken.
  exists (approximate a e2).
  split.
   apply: orWeaken.
   left; reflexivity.
  rewrite -> Hb.
  apply regFun_prf.
 destruct (IHx b Hb) as [G | y [Hy0 Hy1]] using existsC_ind.
  auto using existsC_stable.
 apply existsWeaken.
 exists y.
 split; auto.
 apply: orWeaken.
 right; auto.
Qed.

Definition FinCompact_fun (x: FinEnum stableCX) : Compact stableX :=
 Build_RegularFunction (FinCompact_prf x).

Lemma FinCompact_uc : is_UniformlyContinuousFunction FinCompact_fun Qpos2QposInf.
Proof.
 cut (forall e d1 d2 (a b : FinEnum stableCX), (hemiMetric (Complete X) e
   (fun a0 : Complete X => InFinEnumC a0 a) (fun a : Complete X => InFinEnumC a b)) ->
     (hemiMetric X (d1 + e + d2) (fun a0 : X => InFinEnumC a0 (approximate (FinCompact_fun a) d1))
       (fun a0 : X => InFinEnumC a0 (approximate (FinCompact_fun b) d2)))).
  intros L e a b [Hab0 Hab1] d1 d2.
  split; auto.
  eapply hemiMetric_wd1;[|apply L;apply Hab1].
  QposRing.
 intros e d1 d2 a b Hab c Hc.
 simpl in Hc.
 unfold FinCompact_raw in Hc.
 assert (existsC (Complete X) (fun d => InFinEnumC d a /\ st_eq c (approximate d d1))).
  clear - Hc.
  induction a.
   contradiction.
  destruct Hc as [ G | Hc | Hc] using orC_ind.
    auto using existsC_stable.
   apply existsWeaken.
   exists a.
   split; auto.
   apply orWeaken; left; reflexivity.
  destruct (IHa Hc) as [G | y [Hy0 Hy1]] using existsC_ind.
   auto using existsC_stable.
  apply existsWeaken.
  exists y.
  split; auto.
  apply orWeaken; right; auto.
 destruct H as [ G | d [Hd0 Hd1]] using existsC_ind.
  auto using existsC_stable.
 destruct (Hab d Hd0) as [ G | z [Hz0 Hz1]] using existsC_ind.
  auto using existsC_stable.
 clear - Hd1 Hz0 Hz1.
 induction b.
  contradiction.
 destruct Hz0  as [ G | Hz0 | Hz0] using orC_ind.
   auto using existsC_stable.
  apply existsWeaken.
  exists (approximate a d2).
  split.
   apply: orWeaken.
   left; reflexivity.
  rewrite -> Hz0 in Hz1.
  rewrite -> Hd1.
  apply Hz1.
 destruct (IHb Hz0) as [G | y [Hy0 Hy1]] using existsC_ind.
  auto using existsC_stable.
 apply existsWeaken.
 exists y.
 split; auto.
 apply: orWeaken; right; auto.
Qed.

Open Local Scope uc_scope.

Definition FinCompact : FinEnum stableCX --> Compact stableX :=
 Build_UniformlyContinuousFunction FinCompact_uc.

Lemma FinCompact_correct : forall x (s:FinEnum stableCX),
 InFinEnumC x s <-> inCompact x (FinCompact s).
Proof.
 intros x s.
 split.
  intros H e1 e2.
  simpl.
  induction s.
   contradiction.
  move H after IHs.
  destruct H as [G | H | H] using orC_ind.
    auto using almostIn_stable.
   apply: orWeaken.
   left; auto.
  apply: orWeaken.
  right.
  apply IHs; auto.
 intros H.
 induction s.
  apply (H (1#1) (1#1))%Qpos.
 unfold inCompact in H.
 simpl in H.
 set (P:= fun n (b:bool) => if b
   then (let e1 := (1#P_of_succ_nat n)%Qpos in let e2 := e1 in (ball (m:=X) (e1 + e2) (approximate x e1) (approximate a e2)))
     else (let e1 := (1#P_of_succ_nat n)%Qpos in let e2 := e1 in (almostIn (e1 + e2) (approximate x e1) (FinCompact_raw s e2)))).
 assert (L: (forall n : nat, existsC bool (fun x => ~ ~ In x (true :: false :: nil) /\ P n x))).
  intros n.
  destruct (H  (1#P_of_succ_nat n)%Qpos (1#P_of_succ_nat n)%Qpos) as [ G | L | L] using orC_ind.
    auto using existsC_stable.
   apply existsWeaken.
   exists true.
   split; auto with *.
  apply existsWeaken.
  exists false.
  split; auto with *.
 destruct (infinitePidgeonHolePrinicple _ _ _ L) as [G | c [_ Hc]] using existsC_ind.
  auto using InFinEnumC_stable.
 destruct c.
  apply orWeaken.
  left.
  unfold P in Hc.
  apply ball_eq.
  intros e.
  destruct (Qpos_as_positive_ratio ((1#4)*e)%Qpos) as [[en ed] He].
  simpl in He.
  destruct (Hc (pred (nat_of_P ed))) as [G | m [Hm0 Hm1]] using existsC_ind.
   auto using stableCX.
  set (m' := (1#P_of_succ_nat m)%Qpos).
  apply ball_weak_le with (m' + (m' + m') + m')%Qpos.
   unfold m'.
   autorewrite with QposElim.
   replace LHS with ((1#P_of_succ_nat m)/(1#4)) by simpl; field.
   apply Qle_shift_div_r.
    constructor.
   rewrite -> Qmult_comm.
   change ((1#4)*e) with (((1#4)*e)%Qpos:Q).
   rewrite He.
   unfold Qle; simpl.
   rewrite Zpos_mult_morphism.
   apply Zle_trans with (en * ed)%Z; auto with *.
   apply Zmult_le_compat_l; auto with *.
   rewrite (anti_convert_pred_convert ed).
   do 2 rewrite <- POS_anti_convert.
   do 2 rewrite inj_S.
   rewrite -> inj_le_iff in Hm0.
   auto with *.
  eapply ball_triangle;[|apply ball_approx_l].
  eapply ball_triangle;[apply ball_approx_r|].
  rewrite -> ball_Cunit.
  apply Hm1.
 apply orWeaken.
 right.
 apply IHs.
 unfold P in Hc.
 intros e1 e2.
 apply almostIn_closed.
 intros d.
 destruct (Qpos_as_positive_ratio ((1#4)*d)%Qpos) as [[dn dd] Hd].
 simpl in Hd.
 destruct (Hc (pred (nat_of_P dd))) as [G | m [Hm0 Hm1]] using existsC_ind.
  auto using almostIn_stable.
 set (m' := (1#P_of_succ_nat m)%Qpos).
 apply almostIn_weak_le with ((e1 + m') + (m' + m') + (m' + e2))%Qpos.
  autorewrite with QposElim.
  rewrite -> Qle_minus_iff.
  replace RHS with (d + - (m' + (m' + m') + m')) by simpl; ring.
  rewrite <- Qle_minus_iff.
  unfold m'.
  autorewrite with QposElim.
  replace LHS with ((1#P_of_succ_nat m)/(1#4)) by simpl; field.
  apply Qle_shift_div_r.
   constructor.
  rewrite -> Qmult_comm.
  change ((1#4)*d) with (((1#4)*d)%Qpos:Q).
  rewrite Hd.
  unfold Qle; simpl.
  rewrite Zpos_mult_morphism.
  apply Zle_trans with (dn * dd)%Z; auto with *.
  apply Zmult_le_compat_l; auto with *.
  rewrite (anti_convert_pred_convert dd).
  do 2 rewrite <- POS_anti_convert.
  do 2 rewrite inj_S.
  rewrite -> inj_le_iff in Hm0.
  auto with *.
 eapply almostIn_triangle_r;[|apply regFun_prf].
 eapply almostIn_triangle_l;[apply regFun_prf|].
 apply Hm1.
Qed.

Lemma CompactCompleteCompact_prf : forall x,
 is_RegularFunction (Cmap_raw FinCompact x).
Proof.
 intros x e1 e2.
 unfold Cmap_raw.
 simpl.
 apply FinCompact_uc.
 unfold ball_ex.
 apply regFun_prf.
Qed.

Definition CompactCompleteCompact_fun x : Complete (Compact stableX) :=
 Build_RegularFunction (CompactCompleteCompact_prf x).

Lemma CompactCompleteCompact_uc :
 is_UniformlyContinuousFunction CompactCompleteCompact_fun Qpos2QposInf.
Proof.
 intros e a b H d1 d2.
 simpl in *.
 apply FinCompact_uc.
 apply H.
Qed.

Definition CompactCompleteCompact : Compact stableCX --> Compact stableX :=
 uc_compose Cjoin (Build_UniformlyContinuousFunction CompactCompleteCompact_uc).

Lemma CompactCompleteCompact_correct : forall x s,
 inCompact x s <-> inCompact (Cjoin x) (CompactCompleteCompact s).
Proof.
 intros x s.
 split.
  intros H e1 e2.
  simpl.
  unfold Cjoin_raw.
  simpl.
  assert (Z:=(H ((1#2)*e1) ((1#2)*e2))%Qpos).
  rewrite -> almostInExistsC in Z.
  destruct Z as [G | z [Hz0 Hz1]] using existsC_ind.
   auto using almostIn_stable.
  rewrite -> FinCompact_correct in Hz1.
  apply almostIn_closed.
  intros d.
  assert (Z0:=(Hz0  ((1#2)*e1) ((1#2)*d))%Qpos).
  assert (Z1:=(Hz1 ((1#2)*d) ((1#2)*e2))%Qpos).
  simpl in Z1.
  set (w0:=((1 # 2) * e1 + ((1 # 2) * e1 + (1 # 2) * e2) + (1 # 2) * d)%Qpos) in *.
  set (w1:= ((1 # 2) * d + (1 # 2) * e2)%Qpos) in *.
  setoid_replace (e1 + e2 + d)%Qpos with (w0 + w1)%Qpos; [| unfold w0, w1; QposRing].
  eapply almostIn_triangle_l.
   apply Z0.
  apply Z1.
 intros H e1 e2.
 apply almostIn_closed.
 intros d.
 set (d':=((1#4)*d)%Qpos).
 setoid_replace (e1 + e2 + d)%Qpos with ((e1 + (1#2)*d' + (1#2)*d') + (((d' + d') + (1#2)*d') + ((1#2)*d' + e2)))%Qpos; [| unfold d'; QposRing].
 eapply almostIn_triangle_l.
  eapply ball_triangle.
   apply regFun_prf.
  apply ball_approx_r.
 eapply almostIn_triangle_r;[|apply regFun_prf].
 assert (Z:= (H d' d')).
 simpl in Z.
 unfold Cjoin_raw in Z.
 rewrite -> almostInExistsC in Z.
 simpl in Z.
 destruct Z as [G | z [Hz0 Hz1]] using existsC_ind.
  auto using almostIn_stable.
 change (InFinEnumC (X:=X) z (approximate (FinCompact (approximate s ((1 # 2) * d')%Qpos))
   ((1 # 2) * d')%Qpos)) in Hz1.
 apply almostIn_triangle_l with (Cunit z).
  rewrite -> ball_Cunit.
  assumption.
 clear - Hz1.
 induction ((approximate s ((1 # 2) * d')%Qpos)).
  auto.
 destruct Hz1 as [G | Hz1 | Hz1] using orC_ind.
   auto using almostIn_stable.
  apply orWeaken.
  left.
  rewrite -> Hz1.
  apply ball_approx_l.
 apply orWeaken.
 right.
 apply IHs0; auto.
Qed.

End CompactDistr.

Section CompactImage.

(**
** Compact Image
If x is in a compact set S, then f x is in the compact image of S under f.
(My definiton of compact image is really the closure of the image under f.)
*)
Variable z : Qpos.
Variable X Y : MetricSpace.
Hypothesis stableX : stableMetric X.
Hypothesis stableY : stableMetric Y.
Hypothesis plX : PrelengthSpace X.
Hypothesis plFEX : PrelengthSpace (FinEnum stableX).

Open Local Scope uc_scope.

Variable f : X --> Y.

Lemma almostIn_map : forall (e d:Qpos) a (b:FinEnum stableX), (QposInf_le d (mu f e)) -> almostIn d a b ->
 almostIn e (f a) (FinEnum_map z stableX stableY f b).
Proof.
 intros e d a b Hd Hab.
 induction b.
  contradiction.
 destruct Hab as [G | Hab | Hab] using orC_ind.
   auto using almostIn_stable.
  apply: orWeaken.
  left.
  apply uc_prf.
  eapply ball_ex_weak_le.
   apply Hd.
  assumption.
 apply: orWeaken.
 right.
 apply IHb.
 auto.
Qed.

Lemma almostIn_map2 : forall (e1 e2 d:Qpos) a (b:FinEnum stableX), (QposInf_le d ((mu f e1) + (mu f e2))) -> almostIn d a b ->
 almostIn (e1 + e2) (f a) (FinEnum_map z stableX stableY f b).
Proof.
 intros e1 e2 d a b Hd Hab.
 induction b.
  contradiction.
 destruct Hab as [G | Hab | Hab] using orC_ind.
   auto using almostIn_stable.
  apply: orWeaken.
  left.
  apply (mu_sum plX e2 (e1::nil) f).
  eapply ball_ex_weak_le.
   apply Hd.
  assumption.
 apply: orWeaken.
 right.
 apply IHb.
 auto.
Qed.

Definition CompactImage : Compact stableX --> Compact stableY :=
 Cmap plFEX (FinEnum_map z stableX stableY f).

Lemma CompactImage_correct1 : forall x s,
 (inCompact x s) -> (inCompact (Cmap plX f x) (CompactImage s)).
Proof.
 intros x s H e1 e2.
 apply almostIn_closed.
 intros d1.
 setoid_replace (e1 + e2 + d1)%Qpos
   with ((e1 + (1#4)*d1) + ((1#4)*d1 + ((1#4)*d1)) + ((1#4)*d1 + e2))%Qpos; [| QposRing].
 apply almostIn_triangle_r with (approximate (CompactImage s) ((1#4)*d1)%Qpos); [|apply regFun_prf].
 apply almostIn_triangle_l with (approximate (Cmap plX f x) ((1#4)*d1)%Qpos); [apply regFun_prf|].
 simpl.
 unfold FinEnum_map_modulus.
 case_eq (mu f ((1#4)*d1)).
  intros d Hd.
  apply: almostIn_map2;[|apply H].
  rewrite Hd.
  apply: Qle_refl.
 intros H0.
 assert (Z:=H z z).
 destruct (approximate s z).
  contradiction.
 apply: orWeaken.
 left.
 set (d:=((1 # 4) * d1)%Qpos).
 apply (mu_sum plX d (d::nil) f).
 simpl.
 unfold d.
 rewrite H0.
 constructor.
Qed.

(*
Lemma CompactImage_correctC : forall y s, (inCompact y (CompactImage s)) ->
existsC _ (fun x => ms_eq (Cmap plX f x) y /\ inCompact x s).
Proof.
Complicated.  Probably best to prove compact -> Sequnetially compact
(where the sequnetially compact uses the classical existential)
I don't seem to need this proof at the momment.
*)

End CompactImage.

Section CompactImageBind.

Variable z : Qpos.
Variable X Y : MetricSpace.
Hypothesis stableX : stableMetric X.
Hypothesis stableY : stableMetric Y.
Hypothesis plX : PrelengthSpace X.
Hypothesis plFEX : PrelengthSpace (FinEnum stableX).

Open Local Scope uc_scope.

Variable f : X --> Complete Y.

Definition CompactImage_b : Compact stableX --> Compact stableY :=
 uc_compose (CompactCompleteCompact _ _) (CompactImage z (Complete_stable stableY) plFEX f).

Lemma CompactImage_b_correct1 : forall x s,
 (inCompact x s) -> (inCompact (Cbind plX f x) (CompactImage_b s)).
Proof.
 intros x s H.
 change (inCompact (Cjoin (Cmap_fun plX f x))
   (CompactCompleteCompact stableY _ (CompactImage z (Complete_stable stableY) plFEX f s))).
 rewrite <- CompactCompleteCompact_correct.
 apply: CompactImage_correct1;assumption.
Qed.

(*
Lemma CompactImage_b_correctC
*)

End CompactImageBind.
