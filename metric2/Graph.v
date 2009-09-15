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
Require Export UniformContinuity.
Require Export Compact.
Require Export Prelength.
Require Export CompleteProduct.
Require Import QposMinMax.
Require Import QMinMax.
Require Import Classic.
Require Import Qauto.
Require Import CornTac.

Set Implicit Arguments.

Open Local Scope Q_scope.

Section Graph.
(**
* Graphing
Uniformly continuous functions over compact sets can be graph.  A graph of a
funciton f : X --> Y is the the subset of X*Y {(x,f x) | x in S} where S is
the domain under consideration.  This graph is compact when S is a compact
subset of X.
*)
Variable X Y:MetricSpace.
Let XY := ProductMS X Y.

(** [graphPoint] is the fundamental function of graphing.  It will be lifted in
various ways to produce a graph *)
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
unfold graphPoint_modulus in *.
split.
 change (ball_ex e a b).
 eapply ball_ex_weak_le;[|apply H].
 destruct (mu f e) as [d|].
  apply Qpos_min_lb_l.
 apply Qle_refl.
apply: uc_prf.
eapply ball_ex_weak_le;[|apply H].
destruct (mu f e) as [d|].
 apply Qpos_min_lb_r.
constructor.
Qed.

Definition graphPoint : X --> XY :=
Build_UniformlyContinuousFunction graphPoint_uc.

Hypothesis stableX : stableMetric X.
Hypothesis stableXY : stableMetric XY.

(** The compact image of graphFunction is the graph of [Cmap f] over any
compact set S *)
Definition CompactGraph (plFEX:PrelengthSpace (FinEnum stableX)) : Compact stableX --> Compact stableXY :=
CompactImage (1#1) _ plFEX graphPoint.

Lemma CompactGraph_correct1 : forall plX plFEX x s, (inCompact x s) ->
inCompact (Couple (x,(Cmap plX f x))) (CompactGraph plFEX s).
intros plX plFEX x s Hs.
unfold CompactGraph.
setoid_replace (Couple (X:=X) (Y:=Y) (x, (Cmap plX f x))) with (Cmap plX graphPoint x).
 auto using CompactImage_correct1.
intros e1 e2.
split;simpl.
 unfold graphPoint_modulus.
 eapply ball_weak_le;[|apply regFun_prf].
 destruct (mu f e2);
  autorewrite with QposElim.
  assert (Qmin e2 q <= e2) by auto with *.
  rewrite -> Qle_minus_iff in *.
  Qauto_le.
 apply Qle_refl.
apply (mu_sum plX e2 (e1::nil) f).
simpl.
unfold graphPoint_modulus.
eapply ball_ex_weak_le;[|apply regFun_prf_ex].
destruct (mu f e1) as [d0|]; try constructor.
destruct (mu f e2) as [d|]; try constructor.
simpl.
autorewrite with QposElim.
assert (Qmin e2 d <= d) by auto with *.
rewrite -> Qle_minus_iff in *.
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
unfold FinEnum_map_modulus, graphPoint_modulus in H'.
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
  apply orWeaken.
  left.
  assumption.
 apply orWeaken.
 right.
 apply IHs0.
 assumption.
eapply ball_weak_le;[|apply regFun_prf].
unfold d2.
destruct (mu f d') as [d0|]; auto with *.
autorewrite with QposElim.
assert (Qmin d' d0 <= d') by auto with *.
rewrite -> Qle_minus_iff in *.
Qauto_le.
Qed.

Lemma CompactGraph_correct3 : forall plX plFEX p s, inCompact p (CompactGraph plFEX s) ->
st_eq (Cmap plX f (Cfst p)) (Csnd p).
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
  apply Qpos_min_lb_r.
 constructor.
assert (H':= H d' d').
apply ball_triangle with (approximate (Csnd p) d').
 apply ball_triangle with (f (Cfst_raw p d')).
  apply: (mu_sum plX e' (e2::nil) f).
  simpl.
  apply ball_ex_weak_le with (mu f e2 + d')%QposInf.
   destruct (mu f e2); try constructor.
   destruct (mu f e'); try constructor.
   clear - Hd'2.
   simpl in *.
   autorewrite with QposElim.
   rewrite -> Qle_minus_iff in *.
   Qauto_le.
  unfold Cfst_raw.
  simpl.
  assert (Z:=regFun_prf_ex p (mu f e2) d').
  destruct (mu f e2); try constructor.
  destruct Z; auto.
 assert (L:existsC X (fun x => ball (d' + d') (approximate p d') (x, (f x)))).
  clear -H'.
  simpl in H'.
  unfold FinEnum_map_modulus, graphPoint_modulus in H'.
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
  apply (@ProductMS_stableY X).
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
   rewrite -> Qle_minus_iff in *.
   replace RHS with ((q + - d') + (q + - d')) by ring.
   Qauto_nonneg.
  apply Hl.
 apply ball_sym.
 eapply ball_weak_le;[|apply Hr].
 autorewrite with QposElim.
 clear - Hd'1.
 rewrite -> Qle_minus_iff in *.
 replace RHS with ((e' + - d') + (e' + - d')) by ring.
 Qauto_nonneg.
eapply ball_weak_le;[|apply regFun_prf].
autorewrite with QposElim.
rewrite -> Qle_minus_iff in *.
Qauto_le.
Qed.

Lemma CompactGraph_graph : forall (plX : PrelengthSpace X) plFEX p q1 q2 s, 
 inCompact (Couple (p,q1)) (CompactGraph plFEX s) ->
 inCompact (Couple (p,q2)) (CompactGraph plFEX s) ->
 st_eq q1 q2.
Proof.
intros plX plFEX p q1 q2 s Hq1 Hq2.
transitivity (Cmap plX f p).
 symmetry.
 rewrite <- (CoupleCorrect2 p q1).
 apply: CompactGraph_correct3.
 apply Hq1.
rewrite <- (CoupleCorrect2 p q2).
apply: CompactGraph_correct3.
apply Hq2.
Qed.

Lemma CompactGraph_correct : forall plX plFEX x y s, 
inCompact (Couple (x,y)) (CompactGraph plFEX s) <->
(inCompact x s /\ st_eq y (Cmap plX f x)).
Proof.
intros plX plFEX x y s.
split; intros H.
 split;
  rewrite <- (CoupleCorrect2 x y).
  apply (@CompactGraph_correct2 plFEX).
  exact H.
 symmetry.
 transitivity (Csnd (Couple (x,y))).
  apply: CompactGraph_correct3.
  apply H.
 apply CoupleCorrect3.
destruct H as [H0 H1].
change (x, y) with (PairMS x y).
rewrite H1.
apply: CompactGraph_correct1.
auto.
Qed.

End Graph.

Section GraphBind.

(**
** Graph and Bind
The previous section used [graphPoint] to produce the graph of [Cmap f] over
any compact set S.  In this section we use [graphPoint_b] to produce the
graph of [Cbind f] over any compact set S.  It proceeds in largely the same
way. *)


(*This section ought to be defined in terms of Graph,
 but I'm too tired to figure out how to do it properly.
 Instead I just brainlessly cut and paste and modify the above
 section. *)

Variable X Y:MetricSpace.
Let XY := ProductMS X Y.

Definition graphPoint_b_raw (f:X -> Complete Y) (x:X) : Complete XY := Couple (Cunit x,f x).

Open Local Scope uc_scope.

Variable f : X --> Complete Y.

Lemma graphPoint_b_uc : is_UniformlyContinuousFunction (graphPoint_b_raw f) (graphPoint_modulus f).
Proof.
intros e a b H d1 d2.
split.
 change (ball_ex (d1 + e + d2) a b).
 eapply ball_ex_weak_le;[|apply H].
 unfold graphPoint_modulus.
 destruct (mu f e) as [d|].
  simpl.
  apply Qle_trans with e.
   apply: Qpos_min_lb_l.
  autorewrite with QposElim.
  Qauto_le.
 simpl.
 autorewrite with QposElim.
 Qauto_le.
simpl.
revert d1 d2.
change (ball e (f a) (f b)).
apply: uc_prf.
eapply ball_ex_weak_le;[|apply H].
unfold graphPoint_modulus.
destruct (mu f e) as [d|].
 apply: Qpos_min_lb_r.
constructor.
Qed.

Definition graphPoint_b : X --> Complete XY :=
Build_UniformlyContinuousFunction graphPoint_b_uc.

Hypothesis stableX : stableMetric X.
Hypothesis stableXY : stableMetric XY.

Definition CompactGraph_b (plFEX:PrelengthSpace (FinEnum stableX)) : Compact stableX --> Compact stableXY :=
CompactImage_b (1#1) _ plFEX graphPoint_b.

Require Import Qordfield.
Lemma CompactGraph_b_correct1 : forall plX plFEX x s, (inCompact x s) ->
inCompact (Couple (x,(Cbind plX f x))) (CompactGraph_b plFEX s).
intros plX plFEX x s Hs.
unfold CompactGraph_b.
setoid_replace (Couple (X:=X) (Y:=Y) (x, (Cbind plX f x))) with (Cbind plX graphPoint_b x).
 auto using CompactImage_b_correct1.
intros e1 e2.
split;simpl.
 eapply ball_weak_le;[|apply regFun_prf].
 unfold graphPoint_modulus.
 destruct (mu f ((1#2)*e2));
  autorewrite with QposElim.
  assert (Qmin ((1#2)*e2) q <= ((1#2)*e2)) by auto with *.
  rewrite -> Qle_minus_iff in *.
  replace RHS with ((1 # 2) * e2 + ((1 # 2) * e2 + - Qmin ((1 # 2) * e2) q)) by ring.
  Qauto_nonneg.
 Qauto_le.
unfold Cjoin_raw.
rewrite <- ball_Cunit.
setoid_replace (e1 + e2)%Qpos with ((1#2)*e1 + ((1#2)*e1 + (1#2)*e2) + (1#2)*e2)%Qpos by QposRing.
eapply ball_triangle;[|apply ball_approx_r].
eapply ball_triangle.
 apply (ball_approx_l (approximate (Cmap_fun plX f x) ((1 # 2)%Qpos * e1)) ((1#2)*e1)).
set (e1':=((1 # 2) * e1)%Qpos).
set (e2':=((1 # 2) * e2)%Qpos).
simpl.
apply (mu_sum plX e2' (e1'::nil) f).
simpl.
 eapply ball_ex_weak_le;[|apply regFun_prf_ex].
unfold e1'.
unfold graphPoint_modulus.
destruct (mu f ((1#2)*e1)) as [d0|]; try constructor.
destruct (mu f e2') as [d|]; try constructor.
simpl.
autorewrite with QposElim.
assert (Qmin e2' d <= d) by auto with *.
rewrite -> Qle_minus_iff in *. Qauto_le.
Qed.

Lemma CompactGraph_b_correct2 : forall plFEX p s, inCompact p (CompactGraph_b plFEX s) ->
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
unfold Cjoin_raw in H'.
simpl in *.
unfold FinEnum_map_modulus, graphPoint_modulus in H'.
set (d2:=match mu f ((1#2)*d') with
             | Qpos2QposInf d => Qpos_min ((1#2)*d') d
             | QposInfinity => ((1#2)*d')%Qpos
             end) in *.
eapply almostIn_triangle_r with (approximate s d2).
 clear - H'.
 induction (approximate s d2).
  contradiction.
 destruct H' as [G | [H' _] | H'] using orC_ind.
   auto using almostIn_stable.
  apply orWeaken.
  left.
  assumption.
 apply orWeaken.
 right.
 apply IHs0.
 assumption.
eapply ball_weak_le;[|apply regFun_prf].
unfold d2.
destruct (mu f ((1#2)*d')) as [d0|].
 autorewrite with QposElim.
 assert (Qmin ((1#2)*d') d0 <= ((1#2)*d')) by auto with *.
 rewrite -> Qle_minus_iff in *.
 replace RHS with ((1 # 2) * d' + - Qmin ((1 # 2) * d') d0 + (1#2)*d') by ring.
 Qauto_nonneg.
autorewrite with QposElim.
replace RHS with ((1 # 2) * d' + e2 + (1#2)*d') by ring.
Qauto_le.
Qed.

Lemma CompactGraph_b_correct3 : forall plX plFEX p s, inCompact p (CompactGraph_b plFEX s) ->
st_eq (Cbind plX f (Cfst p)) (Csnd p).
Proof.
intros plX plFEX p s H.
apply ball_eq.
intros e1.
apply regFunBall_e.
intros e2.
set (e':=((1#6)*e1)%Qpos).
setoid_replace (e2 + e1 + e2)%Qpos with ((e2 + e') + ((e' + e') + (e' + e')) + (e2 + e'))%Qpos by (unfold e';QposRing).
set (d' := graphPoint_modulus f ((1#2)*e')).
assert (Hd'1 : d' <= e').
 unfold d', graphPoint_modulus.
 destruct (mu f ((1#2)*e'));
  autorewrite with QposElim.
  apply Qle_trans with ((1#2)*e'); auto with *.
  rewrite Qle_minus_iff.
  ring_simplify.
  Qauto_nonneg.
 rewrite Qle_minus_iff.
 ring_simplify.
 Qauto_nonneg. 
assert (Hd'2 : QposInf_le (d') (mu f ((1#2)*e'))).
 unfold d', graphPoint_modulus.
 destruct (mu f ((1#2)*e')).
  apply Qpos_min_lb_r.
 constructor.
assert (H':= H ((1#2)*d')%Qpos d').
apply ball_triangle with (approximate (Csnd p) ((1#2)%Qpos*d')).
 simpl (approximate (Cbind plX f (Cfst (X:=X) (Y:=Y) p)) e2).
 apply ball_triangle with (approximate (f (Cfst_raw p ((1#2)*d'))) ((1#2)*d'))%Qpos.
  unfold Cjoin_raw.
  simpl.
  apply ball_weak_le with ((1#2)*e2 + ((1#2)*e2 + (1#2)*e') + (1#2)*d')%Qpos.
   autorewrite with QposElim.
   clear - Hd'1.
   rewrite -> Qle_minus_iff in *.
   replace RHS with ((1 # 2) * (e' + - d')) by ring.
   Qauto_nonneg.
  cut (ball ((1 # 2) * e2 + (1 # 2) * e')
    (f (Cfst_raw p (mu f ((1 # 2) * e2))))
    (f (Cfst_raw p ((1 # 2) * d')%Qpos))).
   intros L.
   apply L.
  apply (mu_sum plX ((1#2)*e') (((1#2)*e2)::nil) f)%Qpos.
  simpl.
  apply ball_ex_weak_le with (QposInf_plus (mu f ((1#2)*e2)) ((1#2)*d'))%Qpos.
   destruct (mu f ((1#2)*e2)); try constructor.
   destruct (mu f ((1#2)*e')); try constructor.
   clear - Hd'2.
   simpl in *.
   autorewrite with QposElim.
   rewrite -> Qle_minus_iff in *.
   replace RHS with (q0 + - d' + (1#2)*d') by ring.
   Qauto_nonneg.
  unfold Cfst_raw.
  simpl.
  assert (Z:=regFun_prf_ex p (mu f ((1#2)*e2)) ((1#2)%Qpos*d')).
  destruct (mu f ((1#2)*e2)); try constructor.
  destruct Z; auto.
 assert (L:existsC X (fun x => ball (((1#2)*d') + d') (approximate p ((1#2)%Qpos*d')) (Couple_raw ((Cunit x), (f x)) ((1#2)*d')%Qpos))).
  clear -H'.
  simpl in H'.
  unfold Cjoin_raw in H'.
  simpl in H'.
  unfold FinEnum_map_modulus, graphPoint_modulus in H'.
  induction (@approximate (@FinEnum X stableX) s
             (Qpos2QposInf
                match @mu X _ f ((1#2)*d') return Qpos with
                | Qpos2QposInf d => Qpos_min ((1#2)*d') d
                | QposInfinity => ((1#2)*d')%Qpos
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
  apply (@ProductMS_stableY X).
    apply (approximate (Cfst p) (1#1)%Qpos).
   apply stableXY.
  auto.
 apply ball_triangle with (approximate (f a) ((1#2)%Qpos*d')).
  apply ball_weak_le with ((1#2)*d' + ((1#2)*e' + (1#2)*e') + (1#2)*d')%Qpos.
   clear - Hd'1.
   autorewrite with QposElim.
   rewrite -> Qle_minus_iff in *.
   replace RHS with (e' + - d') by ring.
   auto.   
  simpl.
  rewrite <- ball_Cunit.
  eapply ball_triangle;[|apply ball_approx_r].
  eapply ball_triangle;[apply ball_approx_l|].
  apply (mu_sum plX ((1#2)*e') (((1#2)*e')::nil) f)%Qpos.
  simpl.
  unfold graphPoint_modulus in d'.
  apply ball_ex_weak_le with (d' + d')%Qpos.
   clear - Hd'2.
   destruct (mu f ((1#2)*e')); try constructor.
   simpl in *.
   autorewrite with QposElim.
   rewrite -> Qle_minus_iff in *.
   replace RHS with ((q + - d') + (q + - d')) by ring.
   Qauto_nonneg.
  simpl.
  eapply ball_weak_le;[|apply Hl].
  autorewrite with QposElim.
  Qauto_le.  
 apply ball_sym.
 eapply ball_weak_le;[|apply Hr].
 autorewrite with QposElim.
 clear - Hd'1.
 rewrite -> Qle_minus_iff in *.
 replace RHS with ((e' + - d') + (e' + - d') + (1#2)*d') by ring.
 Qauto_nonneg.
eapply ball_weak_le;[|apply (regFun_prf (Csnd p) ((1#2)*d')%Qpos)].
autorewrite with QposElim.
rewrite -> Qle_minus_iff in *.
replace RHS with ((e' + - d') + (1#2)*d') by ring.
Qauto_nonneg.
Qed.

Lemma CompactGraph_b_graph : forall (plX : PrelengthSpace X) plFEX p q1 q2 s, 
 inCompact (Couple (p,q1)) (CompactGraph_b plFEX s) ->
 inCompact (Couple (p,q2)) (CompactGraph_b plFEX s) ->
 st_eq q1 q2.
Proof.
intros plX plFEX p q1 q2 s Hq1 Hq2.
transitivity (Cbind plX f p).
 symmetry.
 rewrite <- (CoupleCorrect2 p q1).
 apply: CompactGraph_b_correct3.
 apply Hq1.
rewrite <- (CoupleCorrect2 p q2).
apply: CompactGraph_b_correct3.
apply Hq2.
Qed.

Lemma CompactGraph_b_correct : forall plX plFEX x y s, 
inCompact (Couple (x,y)) (CompactGraph_b plFEX s) <->
(inCompact x s /\ st_eq y (Cbind plX f x)).
Proof.
intros plX plFEX x y s.
split; intros H.
 split;
  rewrite <- (CoupleCorrect2 x y).
  apply (@CompactGraph_b_correct2 plFEX).
  exact H.
 symmetry.
 transitivity (Csnd (Couple (x,y))).
  apply: CompactGraph_b_correct3.
  apply H.
 apply CoupleCorrect3.
destruct H as [H0 H1].
change (x, y) with (PairMS x y).
rewrite H1.
apply CompactGraph_b_correct1.
auto.
Qed.

End GraphBind.
