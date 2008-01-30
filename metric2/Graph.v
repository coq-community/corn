Require Export UniformContinuity.
Require Export Compact.
Require Export CompleteProduct.
Require Import QposMinMax.
Require Import QMinMax.
Require Import Classic.
Require Import Qauto.
Require Import CornTac.

Set Implicit Arguments.

Section Graph.

Variable X Y:MetricSpace.
Let XY := ProductMS X Y.

Definition graphPoint_raw (f:X -> Y) (x:X) : XY := (x,f x).

Open Local Scope uc_scope.

Variable f : X --> Y.

Definition graphPoint_modulus (e:Qpos) : Qpos := 
match (mu f e) with
| QposInfinity => e
| Qpos2QposInf d => Qpos_min e d
end.

Lemma graphPoint_uc : is_UniformlyContinuousFunction (graphPoint_raw f) graphPoint_modulus.
Proof.
intros e a b H.
split.
 change (ball_ex e a b).
 eapply ball_ex_weak_le;[|apply H].
 destruct (mu f e) as [d|].
  rapply Qpos_min_lb_l.
 rapply Qle_refl.
rapply uc_prf.
eapply ball_ex_weak_le;[|apply H].
destruct (mu f e) as [d|].
 rapply Qpos_min_lb_r.
constructor.
Qed.

Definition graphPoint : X --> XY :=
Build_UniformlyContinuousFunction graphPoint_uc.

Hypothesis stableX : stableMetric X.
Hypothesis stableXY : stableMetric XY.

Definition CompactGraph (plFEX:PrelengthSpace (FinEnum stableX)) : Compact stableX --> Compact stableXY :=
CompactImage (1#1) _ plFEX graphPoint.

Lemma CompactGraph_correct1 : forall plX plFEX x s, (inCompact x s) ->
inCompact (Strength (x,(Cmap plX f x))) (CompactGraph plFEX s).
intros plX plFEX x s Hs.
unfold CompactGraph.
setoid_replace (Strength (X:=X) (Y:=Y) (Basics.Pair x (Cmap plX f x))) with (Cmap plX graphPoint x) using relation ms_eq.
 auto using CompactImage_correct1.
intros e1 e2.
split;simpl.
 eapply ball_weak_le;[|apply regFun_prf].
 destruct (mu f e2);
  autorewrite with QposElim.
  assert (Qmin e2 q <= e2) by auto with *.
  rewrite Qle_minus_iff in *.
  Qauto_le.
 apply Qle_refl.
apply (mu_sum plX e2 (e1::nil) f).
simpl.
 eapply ball_ex_weak_le;[|apply regFun_prf_ex].
destruct (mu f e1) as [d0|]; try constructor.
destruct (mu f e2) as [d|]; try constructor.
simpl.
autorewrite with QposElim.
assert (Qmin e2 d <= d) by auto with *.
rewrite Qle_minus_iff in *.
Qauto_le.
Qed.

Lemma CompactGraph_correct2 : forall plFEX p s, inCompact p (CompactGraph plFEX s) ->
inCompact (Cfst p) s.
Proof.
intros plFEX p s H e1 e2.
simpl.
unfold Cfst_raw.
apply almostIn_closed.
intros d.
set (d':=((1#2)*d)%Qpos).
setoid_replace (e1 + e2 + d)%Qpos with ((e1 + d') + (d'+ e2))%Qpos by (unfold d';QposRing).
assert (H':=H e1 d').
clear H.
unfold XY in *.
destruct (approximate p e1) as [a b].
simpl in *.
set (d2:=match mu f d' with
             | Qpos2QposInf d => Qpos_min d' d
             | QposInfinity => d'
             end) in *.
eapply almostIn_triangle_r with (approximate s d2).
 clear - H'.
 induction (approximate s d2).
  contradiction.
 destruct H' as [G | [H' _] | H'] using orC_ind.
   auto using almostIn_stable.
  rapply orWeaken.
  left.
  assumption.
 rapply orWeaken.
 right.
 apply IHm.
 assumption.
eapply ball_weak_le;[|apply regFun_prf].
unfold d2.
destruct (mu f d') as [d0|]; auto with *.
autorewrite with QposElim.
assert (Qmin d' d0 <= d') by auto with *.
rewrite Qle_minus_iff in *.
Qauto_le.
Qed.

Lemma CompactGraph_correct3 : forall plX plFEX p s, inCompact p (CompactGraph plFEX s) ->
ms_eq (Cmap plX f (Cfst p)) (Csnd p).
Proof.
intros plX plFEX p s H.
apply ball_eq.
intros e1.
apply regFunBall_e.
intros e2.
set (e':=((1#6)*e1)%Qpos).
setoid_replace (e2 + e1 + e2)%Qpos with ((e2 + e') + ((e' + e') + (e' + e')) + (e2 + e'))%Qpos by (unfold e';QposRing).
set (d' := graphPoint_modulus e').
assert (Hd'1 : d' <= e').
 unfold d', graphPoint_modulus.
 destruct (mu f e'); auto with *.
 apply Qpos_min_lb_l.
assert (Hd'2 : QposInf_le d' (mu f e')).
 unfold d', graphPoint_modulus.
 destruct (mu f e').
  rapply Qpos_min_lb_r.
 constructor.
assert (H':= H d' d').
apply ball_triangle with (approximate (Csnd p) d').
 apply ball_triangle with (f (Cfst_raw p d')).
  rapply (mu_sum plX e' (e2::nil) f).
  simpl.
  apply ball_ex_weak_le with (mu f e2 + d')%QposInf.
   destruct (mu f e2); try constructor.
   destruct (mu f e'); try constructor.
   clear - Hd'2.
   simpl in *.
   autorewrite with QposElim.
   rewrite Qle_minus_iff in *.
   Qauto_le.
  unfold Cfst_raw.
  simpl.
  assert (Z:=regFun_prf_ex p (mu f e2) d').
  destruct (mu f e2); try constructor.
  destruct Z; auto.
 assert (L:existsC X (fun x => ball (d' + d') (approximate p d') (Pair x (f x)))).
  clear -H'.
  simpl in H'.
  induction (@approximate (@FinEnum X stableX) s
             (Qpos2QposInf
                match @mu X Y f d' return Qpos with
                | Qpos2QposInf d => Qpos_min d' d
                | QposInfinity => d'
                end)).
   contradiction.
  destruct H' as [G | H | H] using orC_ind.
    auto using existsC_stable.
   apply existsWeaken.
   exists a.
   apply H.
  auto.
 clear - L Hd'1 Hd'2 plX stableXY.
 destruct L as [G | a [Hl Hr]] using existsC_ind.
  rapply (@ProductMS_stableY X).
    apply (approximate (Cfst p) (1#1)%Qpos).
   apply stableXY.
  auto.
 apply ball_triangle with (f a).
  simpl.
  apply (mu_sum plX e' (e'::nil) f).
  simpl.
  unfold graphPoint_modulus in d'.
  apply ball_ex_weak_le with (d' + d')%Qpos.
   clear - Hd'2.
   destruct (mu f e'); try constructor.
   simpl in *.
   autorewrite with QposElim.
   rewrite Qle_minus_iff in *.
   replace RHS with ((q + - d') + (q + - d')) by ring.
   Qauto_nonneg.
  apply Hl.
 apply ball_sym.
 eapply ball_weak_le;[|apply Hr].
 autorewrite with QposElim.
 clear - Hd'1.
 rewrite Qle_minus_iff in *.
 replace RHS with ((e' + - d') + (e' + - d')) by ring.
 Qauto_nonneg.
eapply ball_weak_le;[|apply regFun_prf].
autorewrite with QposElim.
rewrite Qle_minus_iff in *.
Qauto_le.
Qed.

Lemma CompactGraph_graph : forall (plX : PrelengthSpace X) plFEX p q1 q2 s, 
 inCompact (Strength (p,q1)) (CompactGraph plFEX s) ->
 inCompact (Strength (p,q2)) (CompactGraph plFEX s) ->
 ms_eq q1 q2.
Proof.
intros plX plFEX p q1 q2 s Hq1 Hq2.
transitivity (Cmap plX f p).
 symmetry.
 rewrite <- (StrengthCorrect2 p q1).
 rapply CompactGraph_correct3.
 apply Hq1.
rewrite <- (StrengthCorrect2 p q2).
rapply CompactGraph_correct3.
apply Hq2.
Qed.

End Graph.