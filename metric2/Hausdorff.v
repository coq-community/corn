Require Import ZBasics.
Require Export Metric.
Require Import Classification.
Require Import List.
Require Import ZArith.
Require Import QposMinMax.
Require Import Qauto.

Require Import CornTac.

(* I'll probably need to add the reverse implication at some point*)
Definition FinitelyEnumerable X (p:X -> Prop) :=
{l:list X | forall x:X, p x <-> In x l}.

Section ClassicExists.

Variable A : Type.
Variable P : A->Prop.

Definition existsC : Prop :=
 ~forall x:A, ~P x.

Lemma existsWeaken : (exists x:A, P x) -> existsC.
Proof.
intros [x Hx] H.
apply (H x).
assumption.
Qed.

Lemma existsC_ind : forall (Q:Prop),
 (~~Q -> Q) -> (forall x:A, P x -> Q) -> existsC -> Q.
Proof.
intros Q HQ H ex.
apply HQ.
intros Z.
apply ex.
intros x Hx.
apply Z.
apply H with x.
assumption.
Qed.

Lemma existsC_stable : ~~existsC -> existsC.
Proof.
unfold existsC.
auto.
Qed.

End ClassicExists.

Lemma infinitePidgeonHolePrinicple : 
 forall (X:Type) (l:list X) (P:nat -> X -> Prop),
 (forall n, existsC X (fun x => In x l /\ P n x)) ->
 existsC X (fun x => In x l /\ forall n, existsC nat (fun m => (n <= m)%nat /\ (P m x))).
Proof.
intros X l.
induction l;
 intros P HP G.
 apply (HP O).
 intros x [Hx _].
 auto with *.
apply (G a).
split; auto with *.
intros n Hn.
set (P':= fun m => P (m+n)%nat).
assert (HP' : forall m : nat, existsC X (fun x => In x l /\ P' m x)).
 intros m.
 unfold P'.
 destruct (HP (m + n)%nat) as [HG | y [Hy0 Hy1]] using existsC_ind.
  apply existsC_stable; auto.
 apply existsWeaken.
 exists y.
 split; auto.
 destruct Hy0; auto.
 elim (Hn (m + n)%nat).
 rewrite H.
 auto with *.
destruct (IHl P' HP') as [HG | x [Hx0 Hx1]] using existsC_ind.
 tauto.
apply (G x).
split; auto with *.
unfold P' in Hx1.
intros n0.
destruct (Hx1 n0) as [HG | m [Hm0 Hm1]] using existsC_ind.
 apply existsC_stable; auto.
apply existsWeaken.
exists (m + n)%nat.
split; auto.
auto with *.
Qed.

Lemma infinitePidgeonHolePrinicpleB : 
 forall (X:Type) (l:list X) (f:nat -> X),
 (forall n, In (f n) l) ->
 existsC X (fun x => In x l /\ forall n, existsC nat (fun m => (n <= m)%nat /\ (f m)=x)).
Proof.
intros X l f H.
apply infinitePidgeonHolePrinicple.
intros n.
apply existsWeaken.
exists (f n).
auto with *.
Qed.

Section HausdorffMetric.

Variable X : MetricSpace.

Variable XP_eq : (X -> Prop) -> (X -> Prop) -> Prop.
Hypothesis XP_eq_ST : Setoid_Theory (X -> Prop) XP_eq.

Add Setoid (X -> Prop) XP_eq XP_eq_ST as XP_Setoid.

Definition hemiMetric (e:Qpos) (A B: X -> Prop) := 
 forall x:X, A x -> 
 existsC X (fun y => B y /\ ball e x y).

Definition hausdorffBall (e:Qpos) (A B: X -> Prop) :=
 hemiMetric e A B /\ hemiMetric e B A.

(*
Add Morphism hemiMetric with signature QposEq ==> XP_eq ==> XP_eq ==> iff as hemiMetric_wd.
Proof.
cut (forall x1 x2 : Qpos,
QposEq x1 x2 ->
forall x3 x4 : X -> Prop,
XP_eq x3 x4 ->
forall x5 x6 : X -> Prop,
XP_eq x5 x6 -> (hemiMetric x1 x3 x5 -> hemiMetric x2 x4 x6)).
 intros Z e0 e1 He a0 a1 Ha b0 b1 Hb.
 split; apply Z; try assumption; try (unfold QposEq; symmetry; assumption).
intros e0 e1 He a0 a1 Ha b0 b1 Hb H x Hx.
apply (existC_destruct _ _ (H x Hx)).
 apply existC_stable.
intros a Ha.
apply existsWeaken.
exists a.
rewrite He in Ha.
assumption.
Qed.
*)

Lemma hemiMetric_wd1 : forall (e0 e1:Qpos) A B,
 (QposEq e0 e1) -> hemiMetric e0 A B -> hemiMetric e1 A B.
Proof.
intros e0 e1 A B He H x Hx.
destruct (H x Hx) as [HG | y [Hy Hxy]] using existsC_ind.
 apply existsC_stable; assumption.
apply existsWeaken.
exists y.
rewrite He in Hxy.
auto.
Qed.

Lemma hausdorffBall_wd1 : forall (e0 e1:Qpos) A B,
 (QposEq e0 e1) -> hausdorffBall e0 A B -> hausdorffBall e1 A B.
Proof.
intros e0 e1 A B He [H0 H1].
split; apply hemiMetric_wd1 with e0; assumption.
Qed.

Lemma hemiMetric_refl : forall e A, hemiMetric e A A.
Proof.
intros e A x Hx.
apply existsWeaken.
exists x.
split; try assumption.
apply ball_refl.
Qed.

Lemma hausdorffBall_refl : forall e A, hausdorffBall e A A.
Proof.
intros e A.
split; apply hemiMetric_refl.
Qed.

Lemma hausdorffBall_sym : forall e A B, 
 hausdorffBall e A B -> hausdorffBall e B A.
Proof.
intros e A B [H0 H1].
split; assumption.
Qed.

Lemma hemiMetric_triangle : forall e0 e1 A B C,
 hemiMetric e0 A B -> hemiMetric e1 B C -> hemiMetric (e0 + e1) A C.
Proof.
intros e0 e1 A B C H0 H1 x Hx.
destruct (H0 x Hx) as [HG | y [Hy Hxy]] using existsC_ind.
 apply existsC_stable; assumption.
destruct (H1 y Hy) as [HG | z [Hz Hyz]] using existsC_ind.
 apply existsC_stable; assumption.
apply existsWeaken.
exists z.
split; try assumption.
apply ball_triangle with y; assumption.
Qed.

Lemma hausdorffBall_triangle : forall e0 e1 A B C,
 hausdorffBall e0 A B -> hausdorffBall e1 B C -> hausdorffBall (e0 + e1) A C.
Proof.
intros e0 e1 A B C [H0A H0B] [H1A H1B].
split.
 apply hemiMetric_triangle with B; assumption.
apply hemiMetric_wd1 with (e1 + e0)%Qpos.
 QposRing.
apply hemiMetric_triangle with B; assumption.
Qed.

Hypothesis stableX : stableMetric X.

Lemma hemiMetric_closed : forall e A B,
 FinitelyEnumerable X B ->
 (forall d, hemiMetric (e+d) A B) ->
 hemiMetric e A B.
Proof.
intros e A B [l Hl] H x Hx.
set (P:=fun n y => B y /\ ball (e+(1#(P_of_succ_nat n)))%Qpos x y).
assert (HP:(forall n, existsC X (fun x => In x l /\ P n x))).
 intros n.
 unfold P.
 destruct (H (1#(P_of_succ_nat n))%Qpos x Hx) as [HG | y Hy] using existsC_ind.
  apply existsC_stable; auto.
 apply existsWeaken.
 exists y.
 split; auto.
 destruct Hy; destruct (Hl y); auto.
destruct 
 (infinitePidgeonHolePrinicple _ _ P HP) as [HG | y [Hy0 Hy1]] using existsC_ind.
 apply existsC_stable; auto.
destruct (Hy1 O) as [HG | m [_ [Hy _]]] using existsC_ind.
 apply existsC_stable; auto.
clear m.
apply existsWeaken.
exists y.
split; auto.
apply ball_closed.
intros [n d].
destruct (Hy1 (nat_of_P d)) as [HG | m [Hmd [_ Hm]]] using existsC_ind.
 apply stableX; assumption.
eapply ball_weak_le;[|apply Hm].
autorewrite with QposElim.
rewrite Qle_minus_iff.
ring_simplify.
rewrite <- Qle_minus_iff.
unfold Qle.
simpl.
assert (Z:=inj_le _ _ Hmd).
rewrite inject_nat_convert in Z.
change (d <= n * P_of_succ_nat m)%Z.
rewrite succ_nat.
eapply Zle_trans;[apply Z|].
ring_simplify.
replace LHS with (m*1)%Z by ring.
apply Zle_trans with (m*n + 0)%Z; auto with *.
ring_simplify (m*n + 0)%Z; auto with *.
Qed.

Lemma hausdorffBall_closed : forall e A B,
 FinitelyEnumerable X A -> FinitelyEnumerable X B ->
 (forall d, hausdorffBall (e+d) A B) ->
 hausdorffBall e A B.
Proof.
intros e A B HA HB H.
split; 
 apply hemiMetric_closed; 
 try assumption;
 intros d;
 destruct (H d);
 assumption.
Qed.

End HausdorffMetric.

Section HausdorffMetricStrong.

Variable X : MetricSpace.

Definition hemiMetricStrong (e:Qpos) (A B: X -> Prop) := 
 forall x:X, A x -> 
 forall d:Qpos, exists y:X, B y /\ ball (e+d) x y.

Definition hausdorffBallStrong (e:Qpos) (A B: X -> Prop) :=
 (hemiMetricStrong e A B * hemiMetricStrong e B A)%type.

Lemma hemiMetricStrong_wd1 : forall (e0 e1:Qpos) A B,
 (QposEq e0 e1) -> hemiMetricStrong e0 A B -> hemiMetricStrong e1 A B.
Proof.
intros e0 e1 A B He H x Hx d.
destruct (H x Hx d) as [y [Hy Hxy]].
exists y.
rewrite He in Hxy.
auto.
Qed.

Lemma hausdorffBallStrong_wd1 : forall (e0 e1:Qpos) A B,
 (QposEq e0 e1) -> hausdorffBallStrong e0 A B -> hausdorffBallStrong e1 A B.
Proof.
intros e0 e1 A B He [H0 H1].
split; apply hemiMetricStrong_wd1 with e0; assumption.
Qed.

Lemma hemiMetricStrong_refl : forall e A, hemiMetricStrong e A A.
Proof.
intros e A x Hx d.
exists x.
split; try assumption.
apply ball_refl.
Qed.

Lemma hausdorffBallStrong_refl : forall e A, hausdorffBallStrong e A A.
Proof.
intros e A.
split; apply hemiMetricStrong_refl.
Qed.

Lemma hausdorffBallStrong_sym : forall e A B, 
 hausdorffBallStrong e A B -> hausdorffBallStrong e B A.
Proof.
intros e A B [H0 H1].
split; assumption.
Qed.

Lemma hemiMetricStrong_triangle : forall e0 e1 A B C,
 hemiMetricStrong e0 A B -> hemiMetricStrong e1 B C -> hemiMetricStrong (e0 + e1) A C.
Proof.
intros e0 e1 A B C H0 H1 x Hx d.
destruct (H0 x Hx ((1#2)*d)%Qpos) as [y [Hy Hxy]].
destruct (H1 y Hy ((1#2)*d)%Qpos) as [z [Hz Hyz]].
exists z.
split; try assumption.
setoid_replace (e0 + e1 + d)%Qpos with ((e0 + (1 # 2) * d) +(e1 + (1 # 2) * d))%Qpos by QposRing.
apply ball_triangle with y; assumption.
Qed.

Lemma hausdorffBallStrong_triangle : forall e0 e1 A B C,
 hausdorffBallStrong e0 A B -> hausdorffBallStrong e1 B C -> hausdorffBallStrong (e0 + e1) A C.
Proof.
intros e0 e1 A B C [H0A H0B] [H1A H1B].
split.
 apply hemiMetricStrong_triangle with B; assumption.
apply hemiMetricStrong_wd1 with (e1 + e0)%Qpos.
 QposRing.
apply hemiMetricStrong_triangle with B; assumption.
Qed.

Lemma hemiMetricStrong_closed : forall e A B,
 FinitelyEnumerable X B ->
 (forall d, hemiMetricStrong (e+d) A B) ->
 hemiMetricStrong e A B.
Proof.
intros e A B HB H x Hx d.
destruct (H ((1#2)*d)%Qpos x Hx ((1#2)*d)%Qpos) as [y [Hy Hxy]].
exists y.
split; try assumption.
setoid_replace (e + d)%Qpos with (e + (1 # 2) * d + (1 # 2) * d)%Qpos by QposRing.
assumption.
Qed.

Lemma hausdorffBallStrong_closed : forall e A B,
 FinitelyEnumerable X A -> FinitelyEnumerable X B ->
 (forall d, hausdorffBallStrong (e+d) A B) ->
 hausdorffBallStrong e A B.
Proof.
intros e A B HA HB H.
split; 
 apply hemiMetricStrong_closed; 
 try assumption;
 intros d;
 destruct (H d);
 assumption.
Qed.

Hypothesis almostDecideX : locatedMetric X.

Definition HemiMetricStrongAlmostDecidable : 
 forall (e d:Qpos) A B,
 FinitelyEnumerable X A -> FinitelyEnumerable X B ->
 e < d -> hemiMetricStrong d A B + (hemiMetricStrong e A B->False).
Proof.
assert (P1:forall (e d : Qpos) (a:X) (B : X -> Prop),
FinitelyEnumerable X B ->
e < d -> hemiMetricStrong d (fun x=>a=x) B + (hemiMetricStrong e (fun x=>a=x) B -> False)).
 intros e d a B [lB HB].
 revert B HB.
 induction lB.
  intros B HB Hed.
  right.
  intros H.
  destruct (H a (refl_equal a) d) as [y [Hy _]].
  destruct (HB y) as [Y _].
  elim Y; assumption.
 intros B HB Hed.
 destruct (IHlB (fun x => In x lB)) as [H|H].
    tauto.
   assumption.
  left.
  intros x Hx d0.
  destruct (H x Hx d0) as [y [Hy0 Hy1]].
  exists y.
  split; try assumption.
  destruct (HB y); auto with *.
 destruct (almostDecideX ((1#2)*(e+d))%Qpos d a a0).
   autorewrite with QposElim.
   rewrite Qlt_minus_iff.
   replace RHS with ((1#2)*(d + - e)) by ring.
   rewrite Qlt_minus_iff in Hed.
   Qauto_pos.
  left.
  intros x Hx d0.
  exists a0.
  destruct (HB a0).
  split; auto with *.
  apply ball_weak.
  rewrite <- Hx.
  assumption.
 right.
 intros H0.
 destruct (Qpos_lt_plus Hed) as [c Hc].
 apply H.
 intros x Hx d0.
 destruct (H0 a (refl_equal a) (Qpos_min d0 ((1#2)*c)%Qpos)) as [y [Hy0 Hy1]].
 destruct (HB y) as [Y _].
 exists y.
 destruct (Y Hy0) as [H1 | H1].
  elim n.
  rewrite H1.
  apply ball_weak_le with (e + Qpos_min d0 ((1 # 2) * c))%Qpos; auto.
  autorewrite with QposElim.
  rewrite Hc.
  rewrite Qle_minus_iff.
  replace RHS with ((1 # 2) * c + - (Qpos_min d0 ((1 # 2) * c))) by ring.
  rewrite <- Qle_minus_iff.
  rapply Qpos_min_lb_r.
 change (In y lB) in H1.
 split; auto with *.
 rewrite <- Hx.
 apply ball_weak_le with (e + Qpos_min d0 ((1 # 2) * c))%Qpos; auto.
 autorewrite with QposElim.
 rewrite Qle_minus_iff.
 replace RHS with (d0 + - (Qpos_min d0 ((1 # 2) * c))) by ring.
 rewrite <- Qle_minus_iff.
 rapply Qpos_min_lb_l.

intros e d A B [lA HA].
revert A HA.
induction lA.
 intros A HA HB _.
 left.
 intros x Hx.
 destruct (HA x) as [HAx _].
 elim (HAx Hx).
intros A Ha HB Hed.
pose (A':=fun x => In x lA).
destruct (IHlA A') as [I|I]; try assumption.
  tauto.
 destruct (P1 e d a B HB Hed) as [J|J].
  left.
  intros x Hx d0.
  rewrite Ha in Hx.
  destruct Hx.
   destruct (J x H d0) as [y Hy].
   exists y; assumption.
  change (In x lA) in H.
  destruct (I x H d0) as [y Hy].
  exists y; assumption.
 right.
 intros H.
 apply J.
 intros x Hx d0.
 apply H.
 rewrite Ha.
 rewrite Hx.
 auto with *. 
right.
intros H.
apply I.
intros x Hx d0.
apply H.
rewrite Ha.
auto with *.
Qed.

Definition HausdorffBallStrongAlmostDecidable : 
 forall (e d:Qpos) A B,
 FinitelyEnumerable X A -> FinitelyEnumerable X B ->
 e < d -> hausdorffBallStrong d A B + (hausdorffBallStrong e A B->False).
Proof.
intros e d A B HA HB Hed.
destruct (HemiMetricStrongAlmostDecidable e d A B HA HB Hed).
 destruct (HemiMetricStrongAlmostDecidable e d B A HB HA Hed).
  left.
  split; assumption.
 right.
 intros [_ H]; auto.
right.
intros [H _]; auto.
Qed.

End HausdorffMetricStrong.
