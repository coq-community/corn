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
Require Import CoRN.algebra.RSetoid.
Require Export CoRN.metric2.UniformContinuity.
Require Export CoRN.metric2.Compact.
Require Export CoRN.metric2.Prelength.
Require Export CoRN.metric2.CompleteProduct.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import CoRN.model.totalorder.QMinMax.
Require Import CoRN.logic.Classic.

Set Implicit Arguments.

Local Open Scope Q_scope.

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

Local Open Scope uc_scope.

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
 apply uc_prf.
 eapply ball_ex_weak_le;[|apply H].
 destruct (mu f e) as [d|].
  apply Qpos_min_lb_r.
 constructor.
Qed.

Definition graphPoint : X --> XY :=
Build_UniformlyContinuousFunction graphPoint_uc.

(** The compact image of graphFunction is the graph of [Cmap f] over any
compact set S *)
Definition CompactGraph (plFEX:PrelengthSpace (FinEnum X)) : Compact X --> Compact XY :=
CompactImage (1#1) plFEX graphPoint.

Lemma CompactGraph_correct1 : forall plX plFEX x s, (inCompact x s) ->
inCompact (Couple (x,(Cmap plX f x))) (CompactGraph plFEX s).
Proof.
 intros plX plFEX x s Hs.
 unfold CompactGraph.
 setoid_replace (Couple (X:=X) (Y:=Y) (x, (Cmap plX f x))) with (Cmap plX graphPoint x).
  auto using CompactImage_correct1.
 intros e1 e2.
 split;simpl.
  unfold graphPoint_modulus.
  eapply ball_weak_le;[|apply regFun_prf].
  destruct (mu f e2); simpl.
   assert (Qmin (proj1_sig e2) (proj1_sig q) <= proj1_sig e2) by auto with *.
   rewrite -> Qle_minus_iff in *.
   rewrite Q_Qpos_min.
   rewrite <- Qle_minus_iff.
   apply Qplus_le_r.
   rewrite <- Qle_minus_iff in H.
   exact H.
  apply Qle_refl.
 apply (mu_sum plX e2 (e1::nil) f).
 simpl.
 unfold graphPoint_modulus.
 eapply ball_ex_weak_le;[|apply regFun_prf_ex].
 destruct (mu f e1) as [d0|]; try constructor.
 destruct (mu f e2) as [d|]; try constructor.
 simpl. rewrite Q_Qpos_min.
 assert (Qmin (proj1_sig e2) (proj1_sig d) <= proj1_sig d) by auto with *.
 apply Qplus_le_r.
 exact H.
Qed.

Lemma CompactGraph_correct2 : forall plFEX p s, inCompact p (CompactGraph plFEX s) ->
inCompact (Cfst p) s.
Proof.
 intros plFEX p s H e1 e2.
 simpl.
 unfold Cfst_raw.
 apply FinSubset_ball_closed.
 intros d dpos.
 set (d':=((1#2)*exist _ _ dpos)%Qpos).
 assert (Qeq (proj1_sig e1 + proj1_sig e2 + d)
             (proj1_sig ((e1 + d') + (d'+ e2))%Qpos))
   by (simpl; ring).
 apply (@FinSubset_ball_wd_full _ _ _
           H0 _ _ (reflexivity _) _ _ (reflexivity _)).
 clear H0. 
 pose proof (H e1 d') as H'.
 clear H.
 unfold XY in *.
 destruct (approximate p e1) as [a b].
 simpl in *.
 unfold FinEnum_map_modulus, graphPoint_modulus in H'.
 set (d2:=match mu f d' with | Qpos2QposInf d => Qpos_min d' d | QposInfinity => d' end) in *.
 eapply FinSubset_ball_triangle_r with (approximate s d2).
  clear - H'.
  induction (approximate s d2).
  exfalso; exact (FinSubset_ball_nil H').
  apply FinSubset_ball_orC in H'.
  destruct H' as [G | [H' _] | H'] using orC_ind.
 intro abs; contradict G; intro G; contradiction.
 intro abs; contradict abs. exists a0.
 split. left. reflexivity.
   assumption.
   apply FinSubset_ball_cons.
  apply IHl.
  assumption.
 eapply ball_weak_le;[|apply regFun_prf].
 unfold d2.
 destruct (mu f d') as [d0|]; auto with *.
 simpl. rewrite Q_Qpos_min.
 assert (Qmin (proj1_sig d') (proj1_sig d0) <= proj1_sig d') by auto with *.
 apply Qplus_le_l.
 exact H.
Qed.

Lemma CompactGraph_correct3 : forall plX plFEX p s, inCompact p (CompactGraph plFEX s) ->
st_eq (Cmap plX f (Cfst p)) (Csnd p).
Proof.
 intros plX plFEX p s H.
 apply ball_eq.
 intros e1 epos.
 apply regFunBall_e.
 intros e2.
 set (e':=((1#6)*exist _ _ epos)%Qpos).
 setoid_replace (proj1_sig e2 + e1 + proj1_sig e2)
   with (proj1_sig ((e2 + e') + ((e' + e') + (e' + e')) + (e2 + e'))%Qpos)
   by (unfold e'; simpl; ring).
 set (d' := graphPoint_modulus e').
 assert (Hd'1 : proj1_sig d' <= proj1_sig e').
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
   apply (mu_sum plX e' (e2::nil) f).
   simpl.
   apply ball_ex_weak_le with (mu f e2 + d')%QposInf.
    destruct (mu f e2); try constructor.
    destruct (mu f e'); try constructor.
    clear - Hd'2.
    simpl in *.
    apply Qplus_le_r.
    exact Hd'2.
   unfold Cfst_raw.
   simpl.
   assert (Z:=regFun_prf_ex p (mu f e2) d').
   destruct (mu f e2); try constructor.
   destruct Z; auto.
  assert (L:existsC X (fun x => ball (proj1_sig d' + proj1_sig d') (approximate p d') (x, (f x)))).
   clear -H'.
   simpl in H'.
   unfold FinEnum_map_modulus, graphPoint_modulus in H'.
   induction (@approximate _ (FinEnum_ball X) s (Qpos2QposInf match @mu X Y f d' return Qpos with
     | Qpos2QposInf d => Qpos_min d' d | QposInfinity => d' end)).
   exfalso; exact (FinSubset_ball_nil H').
   apply FinSubset_ball_orC in H'.
   destruct H' as [G | H | H] using orC_ind.
 intro abs; contradict G; intro G; contradiction.
    apply existsWeaken.
    exists a.
    apply H.
   auto.
  clear - L Hd'1 Hd'2 plX.
  destruct L as [G | a [Hl Hr]] using existsC_ind.
  apply (msp_stable (msp _)), G.
  apply ball_triangle with (f a).
   simpl.
   apply (mu_sum plX e' (e'::nil) f).
   simpl.
   unfold graphPoint_modulus in d'.
   apply ball_ex_weak_le with (d' + d')%Qpos.
    clear - Hd'2.
    destruct (mu f e'); try constructor.
    simpl in *.
    apply Qplus_le_compat; exact Hd'2.
   apply Hl.
  apply ball_sym.
  eapply ball_weak_le;[|apply Hr].
  simpl.
  clear - Hd'1.
  apply Qplus_le_compat; exact Hd'1.
 eapply ball_weak_le;[|apply regFun_prf].
 simpl.
 rewrite Qplus_comm.
 apply Qplus_le_r.
 exact Hd'1.
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
  refine (CompactGraph_correct3 _ _).
  apply Hq1.
 rewrite <- (CoupleCorrect2 p q2).
 refine (CompactGraph_correct3 _ _).
 apply Hq2.
Qed.

Lemma CompactGraph_correct : forall plX plFEX x y s,
inCompact (Couple (x,y)) (CompactGraph plFEX s) <->
(inCompact x s /\ st_eq y (Cmap plX f x)).
Proof.
 intros plX plFEX x y s.
 split; intros H.
  split; rewrite <- (CoupleCorrect2 x y).
   apply (@CompactGraph_correct2 plFEX).
   exact H.
  symmetry.
  transitivity (Csnd (Couple (x,y))).
   refine (CompactGraph_correct3 _ _).
   apply H.
  apply CoupleCorrect3.
 destruct H as [H0 H1].
 change (x, y) with (PairMS x y).
 rewrite -> H1.
 apply CompactGraph_correct1.
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

Local Open Scope uc_scope.

Variable f : X --> Complete Y.

Lemma graphPoint_b_uc : is_UniformlyContinuousFunction (graphPoint_b_raw f) (graphPoint_modulus f).
Proof.
 intros e a b H d1 d2.
 split.
  change (ball_ex (Qpos2QposInf d1 + e + Qpos2QposInf d2) a b).
  eapply ball_ex_weak_le;[|apply H].
  unfold graphPoint_modulus.
  destruct (mu f e) as [d|].
 - simpl.
   apply Qle_trans with (proj1_sig e + 0).
   rewrite Qplus_0_r.
    apply Qpos_min_lb_l.
    rewrite <- (Qplus_comm (proj1_sig e)), <- Qplus_assoc.
    apply Qplus_le_r.
    apply (Qpos_nonneg (d1+d2)).
 - simpl.
   apply Qle_trans with (proj1_sig e + 0).
   rewrite Qplus_0_r.
    apply Qle_refl.
    rewrite <- (Qplus_comm (proj1_sig e)), <- Qplus_assoc.
    apply Qplus_le_r.
    apply (Qpos_nonneg (d1+d2)).
 - simpl.
 revert d1 d2.
 change (ball (proj1_sig e) (f a) (f b)).
 apply uc_prf.
 eapply ball_ex_weak_le;[|apply H].
 unfold graphPoint_modulus.
 destruct (mu f e) as [d|].
  apply Qpos_min_lb_r.
 constructor.
Qed.

Definition graphPoint_b : X --> Complete XY :=
Build_UniformlyContinuousFunction graphPoint_b_uc.

Definition CompactGraph_b (plFEX:PrelengthSpace (FinEnum X)) : Compact X --> Compact XY :=
CompactImage_b (1#1) plFEX graphPoint_b.

Local Open Scope Q_scope.

Lemma CompactGraph_b_correct1 : forall plX plFEX x s, (inCompact x s) ->
inCompact (Couple (x,(Cbind plX f x))) (CompactGraph_b plFEX s).
Proof.
 intros plX plFEX x s Hs.
 unfold CompactGraph_b.
 setoid_replace (Couple (X:=X) (Y:=Y) (x, (Cbind plX f x))) with (Cbind plX graphPoint_b x).
  auto using CompactImage_b_correct1.
 intros e1 e2.
 split. 
 apply ball_weak_le with (proj1_sig (e1 + (graphPoint_modulus f ((1 # 2) * e2)))%Qpos)
 ;[|apply regFun_prf].
  unfold graphPoint_modulus.
  destruct (mu f ((1#2)*e2)). simpl. 
   rewrite Q_Qpos_min.
  assert (Qmin ((1#2)*proj1_sig e2) (proj1_sig q)
          <= ((1#2)*proj1_sig e2)) by auto with *.
  apply Qplus_le_r.
  apply (Qle_trans _ _ _ H).
  rewrite <- (Qmult_1_l (proj1_sig e2)) at 2.
  apply Qmult_le_r.
  apply Qpos_ispos.
  discriminate.
   simpl. 
   apply Qplus_le_r.
  rewrite <- (Qmult_1_l (proj1_sig e2)) at 2.
  apply Qmult_le_r.
  apply Qpos_ispos.
  discriminate. 
 simpl. unfold Cjoin_raw. 
 rewrite <- ball_Cunit.
 setoid_replace (proj1_sig e1 + proj1_sig e2)
   with (proj1_sig ((1#2)*e1 + ((1#2)*e1 + (1#2)*e2) + (1#2)*e2)%Qpos)
   by (simpl; ring).
 eapply ball_triangle;[|apply ball_approx_r].
 eapply ball_triangle.
 apply (ball_approx_l (approximate (Cmap_fun plX f x) (Qpos2QposInf ((1 # 2)%Qpos * e1)))
                      ((1#2)*e1)).
 set (e1':=((1 # 2) * e1)%Qpos).
 set (e2':=((1 # 2) * e2)%Qpos).
 simpl.
 apply (mu_sum plX e2' (e1'::nil) f).
 apply ball_ex_weak_le
   with (e:= (mu f e1' + graphPoint_modulus f ((1 # 2) * e2))%QposInf).
 2: apply regFun_prf_ex.
 unfold e1'.
 unfold graphPoint_modulus.
 replace (fold_right QposInf_plus (mu f e2') (map (mu f) (((1 # 2) * e1)%Qpos :: nil)))
   with (mu f ((1 # 2) * e1) + mu f e2')%QposInf by reflexivity.
 destruct (mu f ((1#2)*e1)) as [d0|]; try constructor.
 unfold e2'.
 destruct (mu f ((1 # 2) * e2)) as [d|]; try constructor.
 simpl. rewrite Q_Qpos_min.
 assert (Qmin (proj1_sig e2') (proj1_sig d) <= proj1_sig d) by auto with *.
 apply Qplus_le_r.
 exact H.
Qed.

Lemma CompactGraph_b_correct2 : forall plFEX p s, inCompact p (CompactGraph_b plFEX s) ->
 inCompact (Cfst p) s.
Proof.
 intros plFEX p s H e1 e2.
 simpl.
 unfold Cfst_raw.
 apply FinSubset_ball_closed.
 intros d dpos.
 set (d':=((1#2)*exist _ _ dpos)%Qpos).
 assert (Qeq (proj1_sig e1 + proj1_sig e2 + d)
             (proj1_sig ((e1 + d') + (d'+ e2))%Qpos))
   by (simpl; ring).
 apply (@FinSubset_ball_wd_full _ _ _
           H0 _ _ (reflexivity _) _ _ (reflexivity _)).
 clear H0. 
 assert (H':=H e1 d').
 clear H.
 unfold XY in *.
 destruct (approximate p e1) as [a b].
 simpl in *.
 unfold Cjoin_raw in H'.
 simpl in *.
 unfold FinEnum_map_modulus, graphPoint_modulus in H'.
 remember (match mu f ((1#2)*d') with
           | Qpos2QposInf d => Qpos_min ((1#2)*d') d
           | QposInfinity => ((1#2)*d')%Qpos end) as d2.
 simpl in Heqd2. rewrite <- Heqd2 in H'.
 eapply FinSubset_ball_triangle_r with (approximate s d2).
  clear - H'.
  induction (approximate s d2).
  exfalso; exact (FinSubset_ball_nil H').
  apply FinSubset_ball_orC in H'.
  destruct H' as [G | [H' _] | H'] using orC_ind.
 intro abs; contradict G; intro G; contradiction.
 intro abs; contradict abs. exists a0.
 split. left. reflexivity.
   assumption.
   apply FinSubset_ball_cons.
  apply IHl.
  assumption.
 eapply ball_weak_le;[|apply regFun_prf].
 rewrite Heqd2.
 destruct (@mu X (Complete Y) f
              (Qpos_mult
                 (@exist Q (Qlt {| Qnum := Z0; Qden := xH |})
                         {| Qnum := Z.pos xH; Qden := xO xH |} (@eq_refl comparison Lt)) d'))
   as [d0|].
 simpl.
 assert (Qmin ((1#2)* proj1_sig d') (proj1_sig d0) <= ((1#2)*proj1_sig d'))
   by auto with *.
 apply Qplus_le_l.
  rewrite Q_Qpos_min.
 apply (Qle_trans _ _ _ H).
 apply Qmult_le_l. reflexivity.
 simpl.
 rewrite <- (Qmult_1_l d) at 2.
 apply Qmult_le_r.
 apply dpos.
 discriminate. 
  simpl.
  apply Qplus_le_l.
 rewrite <- (Qmult_1_l ((1 # 2) * d)) at 2.
 apply Qmult_le_r.
 apply (Qpos_ispos d').
 discriminate. 
Qed.

Lemma CompactGraph_b_correct3 : forall plX plFEX p s, inCompact p (CompactGraph_b plFEX s) ->
st_eq (Cbind plX f (Cfst p)) (Csnd p).
Proof.
 intros plX plFEX p s H.
 apply ball_eq.
 intros e1 epos.
 apply regFunBall_e.
 intros e2.
 set (e':=((1#6)*exist _ _ epos)%Qpos).
 setoid_replace (proj1_sig e2 + e1 + proj1_sig e2)
   with (proj1_sig ((e2 + e') + ((e' + e') + (e' + e')) + (e2 + e'))%Qpos)
   by (unfold e'; simpl; ring).
 set (d' := graphPoint_modulus f ((1#2)*e')).
 assert (Hd'1 : proj1_sig d' <= proj1_sig e').
  unfold d', graphPoint_modulus.
  destruct (mu f ((1#2)*e')); autorewrite with QposElim.
   apply Qle_trans with ((1#2)*proj1_sig e'); auto with *.
  rewrite <- (Qmult_1_l (proj1_sig e')) at 2.
  apply Qmult_le_r.
  apply Qpos_ispos.
  discriminate. 
  rewrite <- (Qmult_1_l (proj1_sig e')).
  apply Qmult_le_r.
  apply Qpos_ispos.
  discriminate. 
 assert (Hd'2 : QposInf_le (d') (mu f ((1#2)*e'))).
  unfold d', graphPoint_modulus.
  destruct (mu f ((1#2)*e')).
   apply Qpos_min_lb_r.
  constructor.
 assert (H':= H ((1#2)*d')%Qpos d').
 apply ball_triangle with (approximate (Csnd p) (Qpos2QposInf ((1#2)%Qpos*d'))).
  simpl (approximate (Cbind plX f (Cfst (X:=X) (Y:=Y) p)) e2).
  apply ball_triangle
    with (approximate (f (Cfst_raw p (Qpos2QposInf (1#2)*d')))
                      (Qpos2QposInf (1#2)*d'))%Qpos.
   unfold Cjoin_raw.
   simpl.
   apply ball_weak_le with (proj1_sig ((1#2)*e2 + ((1#2)*e2 + (1#2)*e') + (1#2)*d')%Qpos).
   simpl.
    clear - Hd'1.
    rewrite -> Qle_minus_iff in *.
    setoid_replace (proj1_sig e2 + (1 # 6) * e1 +
  -
  ((1 # 2) * proj1_sig e2 + ((1 # 2) * proj1_sig e2 + (1 # 2) * ((1 # 6) * e1)) +
   (1 # 2) * proj1_sig d'))
      with ((1 # 2) * (proj1_sig e' + - proj1_sig d'))
      by (simpl; ring).
    apply Qmult_le_0_compat. discriminate.
    exact Hd'1.
   cut (ball ((1 # 2) * proj1_sig e2 + (1 # 2) * proj1_sig e') (f (Cfst_raw p (mu f ((1 # 2) * e2))))
     (f (Cfst_raw p ((1 # 2) * d')%Qpos))).
    intros L.
    apply L.
   apply (mu_sum plX ((1#2)*e') (((1#2)*e2)::nil) f)%Qpos.
   apply ball_ex_weak_le
     with (QposInf_plus (mu f ((1#2)*e2)) (Qpos2QposInf (1#2)*d'))%Qpos.
   simpl.
   destruct (@mu X (Complete Y) f
          (Qpos_mult
             (@exist Q (Qlt {| Qnum := Z0; Qden := xH |})
                     {| Qnum := Z.pos xH; Qden := xO xH |} (@eq_refl comparison Lt)) e2))
   ; try constructor.
   simpl in Hd'2.
   destruct (@mu X (Complete Y) f
          (Qpos_mult
             (@exist Q (Qlt {| Qnum := Z0; Qden := xH |})
                     {| Qnum := Z.pos xH; Qden := xO xH |} (@eq_refl comparison Lt)) e'))
   ; try constructor.
    clear - Hd'2.
    simpl in *.
    apply Qplus_le_r.
    refine (Qle_trans _ _ _ _ Hd'2).
    rewrite <- (Qmult_1_l (proj1_sig d')) at 2.
    apply Qmult_le_r.
    apply Qpos_ispos.
    discriminate. 
   unfold Cfst_raw.
   assert (Z:=regFun_prf_ex p (mu f ((1#2)*e2)) (Qpos2QposInf (1#2)%Qpos*d')).
   destruct (mu f ((1#2)*e2)); try constructor.
   destruct Z; auto.
   assert (L:existsC X (fun x => ball (proj1_sig (((1#2)*d') + d')%Qpos)
                                   (approximate p (Qpos2QposInf (1#2)%Qpos*d')) (Couple_raw ((Cunit x), (f x)) (Qpos2QposInf ((1#2)*d')%Qpos)))).
   clear -H'.
   simpl in H'.
   unfold Cjoin_raw in H'.
   simpl in H'.
   unfold FinEnum_map_modulus, graphPoint_modulus in H'.
   remember (match mu f ((1 # 2) * d') with
                  | Qpos2QposInf d => Qpos_min ((1 # 2) * d') d
                  | QposInfinity => ((1 # 2) * d')%Qpos
                  end) as mm.
   simpl in Heqmm. rewrite <- Heqmm in H'.
   induction (@approximate _ (FinEnum_ball X) s mm).
   exfalso; exact (FinSubset_ball_nil H').
   apply FinSubset_ball_orC in H'.
   destruct H' as [G | H | H] using orC_ind.
 intro abs; contradict G; intro G; contradiction.
    apply existsWeaken.
    exists a.
    apply H.
   auto.
  clear - L Hd'1 Hd'2 plX.
  destruct L as [G | a [Hl Hr]] using existsC_ind.
  apply (msp_stable (msp _)), G.
  apply ball_triangle with (approximate (f a) (Qpos2QposInf ((1#2)%Qpos*d'))).
   apply ball_weak_le with (proj1_sig ((1#2)*d' + ((1#2)*e' + (1#2)*e') + (1#2)*d')%Qpos).
    clear - Hd'1.
    simpl.
    rewrite -> Qle_minus_iff in *.
    setoid_replace ( (1 # 6) * e1 + (1 # 6) * e1 +
  -
  ((1 # 2) * proj1_sig d' + ((1 # 2) * ((1 # 6) * e1) + (1 # 2) * ((1 # 6) * e1)) +
   (1 # 2) * proj1_sig d'))
      with (proj1_sig e' + - proj1_sig d') by (simpl; ring).
    exact Hd'1.
   simpl.
   rewrite <- ball_Cunit.
   eapply ball_triangle;[|apply (ball_approx_r _ ((1#2)*d')%Qpos)].
   eapply ball_triangle;[apply (ball_approx_l _ ((1#2)*d'))|].
   apply (mu_sum plX ((1#2)*e') (((1#2)*e')::nil) f)%Qpos.
   simpl.
   unfold graphPoint_modulus in d'.
   apply ball_ex_weak_le with (d' + d')%Qpos.
    clear - Hd'2.
    simpl in Hd'2.
    destruct (@mu X (Complete Y) f
          (Qpos_mult
             (@exist Q (Qlt {| Qnum := Z0; Qden := xH |})
                     {| Qnum := Z.pos xH; Qden := xO xH |} (@eq_refl comparison Lt)) e'))
    ; try constructor.
    simpl in *.
    apply Qplus_le_compat; exact Hd'2.
   simpl.
   eapply ball_weak_le;[|apply Hl].
   simpl.
   apply Qplus_le_l.
   rewrite <- (Qmult_1_l (proj1_sig d')) at 2.
   apply Qmult_le_r.
   apply Qpos_ispos.
   discriminate. 
  apply ball_sym.
  eapply ball_weak_le;[|apply Hr].
  apply Qplus_le_compat.
  2: exact Hd'1.
  refine (Qle_trans _ _ _ _ Hd'1).
   rewrite <- (Qmult_1_l (proj1_sig d')).
   apply Qmult_le_r.
   apply Qpos_ispos.
   discriminate. 
 eapply ball_weak_le;[|apply (regFun_prf (Csnd p) ((1#2)*d')%Qpos)].
 rewrite Qplus_comm.
 apply Qplus_le_r.
  refine (Qle_trans _ _ _ _ Hd'1).
   rewrite <- (Qmult_1_l (proj1_sig d')).
   apply Qmult_le_r.
   apply Qpos_ispos.
   discriminate. 
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
  refine (CompactGraph_b_correct3 _ _).
  apply Hq1.
 rewrite <- (CoupleCorrect2 p q2).
 refine (CompactGraph_b_correct3 _ _).
 apply Hq2.
Qed.

Lemma CompactGraph_b_correct : forall plX plFEX x y s,
inCompact (Couple (x,y)) (CompactGraph_b plFEX s) <->
(inCompact x s /\ st_eq y (Cbind plX f x)).
Proof.
 intros plX plFEX x y s.
 split; intros H.
  split; rewrite <- (CoupleCorrect2 x y).
   apply (@CompactGraph_b_correct2 plFEX).
   exact H.
  symmetry.
  transitivity (Csnd (Couple (x,y))).
   refine (CompactGraph_b_correct3 _ _).
   apply H.
  apply CoupleCorrect3.
 destruct H as [H0 H1].
 change (x, y) with (PairMS x y).
 rewrite -> H1.
 apply CompactGraph_b_correct1.
 auto.
Qed.

End GraphBind.
