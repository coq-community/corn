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

Require Export CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.metric2.Complete.
Require Import CoRN.algebra.COrdFields2.
Require Import CoRN.model.ordfields.Qordfield.
Require Import CoRN.model.totalorder.QMinMax.
Require Import CoRN.model.totalorder.QposMinMax.
Require Import CoRN.stdlib_omissions.List.
Require Import CoRN.tactics.CornTac.
Require Import CoRN.tactics.Qauto.

Set Implicit Arguments.
Set Automatic Introduction.

Open Local Scope Q_scope.

Section Prelength_Space.
(**
** Prelength space
In a length space the "internal" metric of a metric space corresponds
to the given external metric.  The internal metric of a space measures
the distance between two point by the length of curves connecting them.

Because the notion of curves really only makes sense in a complete metric
space, here we use a weaker notion of a prelength space.  In this case
the internal metric says that two points are within e of each other if
you can get between the two points making arbitarily short hops while
covering a distance arbitrarily close to e.
*)
Variable X:MetricSpace.

(** The notion of a prelength space is neatly characterized by the
following simple definition. *)
Definition PrelengthSpace :=
forall (a b:X) (e d1 d2:Qpos), e < d1+d2 -> ball e a b ->
exists2 c:X, ball d1 a c & ball d2 c b.

(** There is some evidence that we should be using the classical
existential in the above definition.  For now we take the middle road
and use the [Prop] based existential.  This show that the exists
statement is not used in computations, but still every occurance is
constructive. *)

Hypothesis prelength : PrelengthSpace.

(** This proves that you can construct a trail of points between a and b
that is arbitarily close to e and with arbitrarily short hops. *)
Lemma trail : forall dl e (a b:X),
 ball e a b ->
 e < QposSum dl ->
 let n := length dl in
 (exists2 f : nat -> X, f 0 = a /\ f n = b
               & forall i z, i < n -> ball (nth i dl z) (f i) (f (S i)))%nat.
Proof.
 induction dl.
  intros e a b H H1.
  simpl in *.
  elim (less_antisymmetric_unfolded _ (e:Q) 0);solve[assumption|apply Qpos_prf].
 rename a into x.
 intros e a b B pe.
 simpl in pe.
 destruct dl.
  simpl in *.
  pose (f:= (fun n => match n with O => a | S _ => b end)).
  exists f; auto.
  intros [|i] z H;[|elimtype False; auto with *].
  clear z H.
  ring_simplify in pe.
  apply ball_weak_le with e.
   apply Qlt_le_weak; assumption.
  assumption.
 set (Sigma := QposSum (q::dl)).
 pose (g := ((Qmax 0 (e-x))+Sigma)/2).
 assert ((Qmax 0 (e-x))<Sigma).
  apply Qmax_case.
   intros.
   apply: less_leEq_trans.
    instantiate (1:=(q:Q)).
    apply Qpos_prf.
   unfold Sigma.
   simpl.
   stepl (q+0); [| simpl; ring].
   apply: plus_resp_leEq_lft.
   apply QposSumNonNeg.
  intros.
  apply: shift_minus_less;simpl.
  rewrite -> Qplus_comm.
  assumption.
 assert (Hg1:=Smallest_less_Average _ _ _ H).
 assert (0<g).
  apply: leEq_less_trans.
   apply Qmax_ub_l.
  apply Hg1.
 set (g' := (mkQpos H0):Qpos).
 assert (Hg:g'=g:>Q).
  apply QposAsmkQpos.
 assert (e<x+g').
  apply: shift_less_plus'.
  apply: leEq_less_trans.
   apply Qmax_ub_r.
  rewrite Hg.
  apply Hg1.
 assert (g'<Sigma).
  rewrite Hg.
  apply: Average_less_Greatest.
  assumption.
 destruct (prelength _ _ _ _ _ H1 B) as [c Hc1 Hc2].
 destruct (IHdl _ _ _ Hc2 H2) as [f' [Hf'1 Hf'2] Hf'3].
 exists (fun n => match n with O => a | S n' => f' n' end).
  auto.
 intros [|i] z Hi.
  simpl.
  congruence.
 apply Hf'3.
 auto with *.
Qed.

Variable Y:MetricSpace.

(** The major applicaiton of prelength spaces is that it allows one to
reduce the problem of [ball (e1 + e2) (f a) (f b)] to
[ball (mu f e1 + mu f e2) a b] instead of reduceing it to
[ball (mu f (e1 + e2)) a b].  This new reduction allows one to continue
reasoning by making use of the triangle law.

Below we show a more general lemma allowing for arbitarily many terms
in the sum. *)
Lemma mu_sum : forall e0 (es : list Qpos) (f:UniformlyContinuousFunction X Y) a b,
ball_ex (fold_right QposInf_plus (mu f e0) (map (mu f) es)) a b ->
ball (fold_right Qpos_plus e0 es) (f a) (f b).
Proof.
 intros e0 es f a b Hab.
 apply ball_closed.
 intros e'.
 setoid_replace (fold_right Qpos_plus e0 es + e')%Qpos with (fold_right Qpos_plus e0 (e'::es)); [| simpl;QposRing].
 set (ds := map (mu f) es) in *.
 set (d0 := (mu f e0)) in *.
 set (d' := (mu f e')) in *.
 assert (H:{ds' | (map Qpos2QposInf ds')=d0::d'::ds}+{In QposInfinity (d0::d'::ds)}).
  generalize (d0::d'::ds); clear.
  induction l as [|[d|] ds].
    left.
    exists (@nil Qpos).
    reflexivity.
   destruct IHds as [[ds' Hds']|Hds].
    left.
    exists (d::ds').
    rewrite <- Hds'.
    reflexivity.
   firstorder.
  firstorder.
 destruct H as [[ds' Hds']|Hds].
  destruct ds' as [|g0 [|g' gs]]; try discriminate Hds'.
  inversion Hds'.
  clear Hds'.
  unfold d0 in *; clear d0.
  unfold d' in *; clear d'.
  unfold ds in *; clear ds.
  replace (fold_right QposInf_plus (mu f e0) (map (mu f) es))
    with (Qpos2QposInf (fold_right Qpos_plus g0 gs)) in Hab.
   simpl in Hab.
   assert (H:(fold_right Qpos_plus g0 gs < QposSum ((g' :: gs)++(g0::nil)))).
    simpl.
    replace LHS with (QposSum (gs ++ g0::nil)).
     rewrite -> Qlt_minus_iff.
     ring_simplify.
     apply Qpos_prf.
    clear - g0.
    induction gs.
     simpl; ring.
    simpl.
    rewrite -> IHgs.
    reflexivity.
   case (trail _ _ _ _ Hab H).
   clear Hab H.
   cut (map Qpos2QposInf (g' :: gs) = map (mu f) (e' :: es)).
    clear H2 H1.
    generalize (e'::es) (g'::gs) a.
    clear gs g' es e' a.
    induction l as [|e es]; intros gs a Hes x [Ha Hb] H; destruct gs; try discriminate Hes.
     simpl in *.
     apply uc_prf.
     rewrite <- H0.
     rewrite <- Hb.
     rewrite <- Ha.
     simpl.
     apply (H 0%nat g0).
     auto with *.
    simpl.
    inversion Hes; clear Hes.
    eapply ball_triangle.
     apply uc_prf.
     rewrite <- H2.
     rewrite <- Ha.
     simpl; apply (H 0%nat g0).
     simpl; auto with *.
    apply (IHes _ (x 1%nat) H3 (fun i => x (S i))); try auto with *.
    intros.
    apply (H (S i) z).
    simpl; auto with *.
   simpl; congruence.
  rewrite <- H2.
  rewrite <- H0.
  clear - gs.
  induction gs.
   reflexivity.
  simpl.
  rewrite <- IHgs.
  reflexivity.
 assert (H:forall (e:Qpos) es, e < (fold_right Qpos_plus e0 es)%Qpos -> (mu f e)=QposInfinity -> ball (m:=Y) (fold_right Qpos_plus e0 es) (f a) (f b)).
  intros e esx He Hmu.
  apply ball_weak_le with e;[apply Qlt_le_weak; assumption|].
  apply uc_prf.
  rewrite Hmu.
  constructor.
 case (in_inv Hds).
  intros Hd0.
  apply H with e0.
   clear - es.
   induction es.
    simpl.
    rewrite -> Qlt_minus_iff.
    ring_simplify.
    apply Qpos_prf.
   simpl.
   replace RHS with (a+(fold_right Qpos_plus e0 (e'::es))) by (simpl;QposRing).
   eapply Qlt_trans.
    apply IHes.
   rewrite -> Qlt_minus_iff.
   ring_simplify.
   apply Qpos_prf.
  assumption.
 clear Hds.
 change (d'::ds) with (map (mu f) (e'::es)).
 induction (e'::es); intros Hds.
  elim Hds.
 simpl in Hds.
 destruct Hds as [Ha0|Hds].
  apply H with a0.
   simpl.
   rewrite -> Qlt_minus_iff.
   ring_simplify.
   apply Qpos_prf.
  assumption.
 simpl.
 eapply ball_weak_le with (fold_right Qpos_plus e0 l).
  rewrite Q_Qpos_plus.
  rewrite -> Qle_minus_iff; ring_simplify.
  auto with *.
 auto.
Qed.

End Prelength_Space.

Section Map.

Open Local Scope uc_scope.
Variable X Y : MetricSpace.
Hypothesis plX : PrelengthSpace X.
Variable f : X --> Y.

(**
*** A more effictient [Cmap] and [Cbind]
The main application of prelength spaces is to allow one to use a
more natural and more efficent map function for complete metric spaces.
Since this map function is more widely used in practice, it gets the
name [Cmap] while the original map function is stuck with the name
[Cmap_slow] as a reminder to try to use the function defined here if
possible. *)

Definition Cmap_raw (x:Complete X) (e:QposInf) :=
f (approximate x (QposInf_bind (mu f) e)).

Lemma Cmap_fun_prf (x:Complete X) : is_RegularFunction (fun e => f (approximate x (QposInf_bind (mu f) e))).
Proof.
 intros e1 e2.
 simpl.
 apply (@mu_sum X plX Y e2 (e1::nil)).
 simpl.
 destruct (mu f e1) as [d1|].
  destruct (mu f e2) as [d2|].
   apply: regFun_prf.
  constructor.
 constructor.
Qed.

Definition Cmap_fun (x:Complete X) : Complete Y :=
Build_RegularFunction (Cmap_fun_prf x).

Lemma Cmap_prf : is_UniformlyContinuousFunction Cmap_fun (mu f).
Proof.
 intros e0 x y Hxy e1 e2.
 simpl.
 setoid_replace (e1+e0+e2)%Qpos with (e1+(e0+e2))%Qpos; [| QposRing].
 apply (@mu_sum X plX Y e2 (e1::e0::nil)).
 simpl.
 destruct (mu f e1) as [d1|];[|constructor].
 destruct (mu f e0) as [d0|];[|constructor].
 destruct (mu f e2) as [d2|];[|constructor].
 simpl in *.
 setoid_replace (d1+(d0+d2))%Qpos with (d1+d0+d2)%Qpos; [| QposRing].
 apply Hxy.
Qed.

Definition Cmap : (Complete X) --> (Complete Y) :=
Build_UniformlyContinuousFunction Cmap_prf.

(** [Cmap] is equivalent to the original [Cmap_slow] *)
Lemma Cmap_correct : st_eq Cmap (Cmap_slow f).
Proof.
 intros x e1 e2.
 simpl.
 unfold Cmap_slow_raw.
 apply (@mu_sum X plX Y e2 (e1::nil)).
 simpl.
 destruct (mu f e1) as [d1|]; try constructor.
 destruct (mu f e2) as [d2|]; try constructor.
 simpl.
 eapply ball_weak_le;[|apply regFun_prf].
 autorewrite with QposElim.
 Qauto_le.
Qed.

Lemma Cmap_fun_correct : forall x, st_eq (Cmap_fun x) (Cmap_slow_fun f x).
Proof.
 apply Cmap_correct.
Qed.

End Map.

Section fast_Monad_Laws.
Open Local Scope uc_scope.

Variable X Y Z : MetricSpace.
Hypothesis plX : PrelengthSpace X.
Hypothesis plY : PrelengthSpace Y.

Notation "a =m b" := (st_eq a b)  (at level 70, no associativity).

Lemma fast_MonadLaw1 a : Cmap plX (uc_id X) a =m a.
Proof. rewrite Cmap_correct. apply MonadLaw1. Qed.

Lemma fast_MonadLaw2 (f:Y --> Z) (g:X --> Y) a : Cmap plX (uc_compose f g) a =m (Cmap plY f (Cmap plX g a)).
Proof. do 3 rewrite Cmap_correct. simpl. apply MonadLaw2. Qed.

Lemma fast_MonadLaw3 (f:X --> Y) a : Cmap plX f (Cunit a) =m Cunit (f a).
Proof. rewrite Cmap_correct. simpl. apply MonadLaw3. Qed.

(* State them all in such a shape some day... *)

End fast_Monad_Laws.

Open Local Scope uc_scope.

(** [Cmap] preserves extensional equality *)

Lemma map_eq_complete {X Y : MetricSpace} {plX : PrelengthSpace X} (f g : X --> Y) :
  (forall x : X, f x [=] g x) -> (forall x : Complete X, Cmap plX f x [=] Cmap plX g x).
Proof.
intros A x. apply lift_eq_complete. intro y. rewrite !fast_MonadLaw3, A. reflexivity.
Qed.

(** Similarly we define a new Cbind *)
Definition Cbind X Y plX (f:X-->Complete Y) := uc_compose Cjoin (Cmap plX f).

Lemma Cbind_correct : forall X Y plX (f:X-->Complete Y), st_eq (Cbind plX f) (Cbind_slow f).
Proof.
 unfold Cbind, Cbind_slow.
 intros X Y plX f.
 rewrite -> (Cmap_correct).
 reflexivity.
Qed.

Lemma Cbind_fun_correct : forall X Y plX (f:X-->Complete Y) x, st_eq (Cbind plX f x) (Cbind_slow f x).
Proof.
 apply Cbind_correct.
Qed.

(** Similarly we define a new Cmap_strong *)
Lemma Cmap_strong_prf : forall (X Y:MetricSpace) (plX:PrelengthSpace X),
 is_UniformlyContinuousFunction (@Cmap X Y plX) Qpos2QposInf.
Proof.
 intros X Y plX e a b Hab.
 do 2 rewrite -> Cmap_correct.
 apply Cmap_strong_slow_prf.
 auto.
Qed.

Definition Cmap_strong X Y plX : (X --> Y) --> (Complete X --> Complete Y) :=
Build_UniformlyContinuousFunction (@Cmap_strong_prf X Y plX).

Lemma Cmap_strong_correct : forall X Y plX, st_eq (@Cmap_strong X Y plX) (@Cmap_strong_slow X Y).
Proof.
 intros X Y plX.
 apply: Cmap_correct.
Qed.

(** Similarly we define a new Cap *)
Definition Cap_raw X Y plX (f:Complete (X --> Y)) (x:Complete X) (e:QposInf) :=
 approximate (Cmap plX (approximate f ((1#2)%Qpos*e)%QposInf) x) ((1#2)%Qpos*e)%QposInf.

Lemma Cap_fun_prf X Y plX (f:Complete (X --> Y)) (x:Complete X) : is_RegularFunction (Cap_raw plX f x).
Proof.
 intros e1 e2.
 unfold Cap_raw.
 unfold Cap_raw.
 unfold QposInf_mult, QposInf_bind.
 set (he1 := ((1 # 2) * e1)%Qpos).
 set (he2 := ((1 # 2) * e2)%Qpos).
 set (f1 := (approximate f he1)).
 set (f2 := (approximate f he2)).
 change (Cmap (Y:=Y) plX f1) with (Cmap_strong Y plX f1).
 change (Cmap (Y:=Y) plX f2) with (Cmap_strong Y plX f2).
 set (y1 :=(Cmap_strong Y plX f1 x)).
 set (y2 :=(Cmap_strong Y plX f2 x)).
 setoid_replace (e1 + e2)%Qpos with (he1 + (he1 + he2) + he2)%Qpos; [| unfold he1, he2; QposRing].
 rewrite <- ball_Cunit.
 apply ball_triangle with y2;[|apply ball_approx_r].
 apply ball_triangle with y1;[apply ball_approx_l|].
 apply (uc_prf (Cmap_strong Y plX)).
 apply: regFun_prf.
Qed.

Definition Cap_fun X Y plX (f:Complete (X --> Y)) (x:Complete X) : Complete Y :=
Build_RegularFunction (Cap_fun_prf plX f x).

Lemma Cap_fun_correct : forall X Y plX (f:Complete (X --> Y)) x, st_eq (Cap_fun plX f x) (Cap_slow_fun f x).
Proof.
 intros X Y plX f x e1 e2.
 simpl.
 unfold Cap_raw, Cap_slow_raw.
 set (e1':=((1 # 2)%Qpos * e1)%Qpos).
 set (e2':=((1 # 2)%Qpos * e2)%Qpos).
 change (ball (e1 + e2) (approximate (Cmap plX (approximate f ((1 # 2) * e1)%Qpos) x) e1')
   (approximate (Cmap_slow (approximate f ((1 # 2) * e2)%Qpos) x) e2')).
 setoid_replace (e1 + e2)%Qpos with (e1' + (((1 # 2) * e1)%Qpos + ((1 # 2) * e2)%Qpos) + e2')%Qpos; [| unfold e1', e2'; QposRing].
 generalize x e1' e2'.
 change (ball ((1 # 2) * e1 + (1 # 2) * e2) (Cmap plX (approximate f ((1 # 2) * e1)%Qpos))
   (Cmap_slow (approximate f ((1 # 2) * e2)%Qpos))).
 rewrite -> Cmap_correct.
 set (f1:=(approximate f ((1 # 2) * e1)%Qpos)).
 set (f2:=(approximate f ((1 # 2) * e2)%Qpos)).
 apply Cmap_strong_slow_prf.
 apply regFun_prf.
Qed.

Definition Cap_modulus X Y (f:Complete (X --> Y)) (e:Qpos) : QposInf := (mu (approximate f ((1#3)*e)%Qpos) ((1#3)*e)).

Lemma Cap_weak_prf X Y plX (f:Complete (X --> Y)) : is_UniformlyContinuousFunction (Cap_fun plX f) (Cap_modulus f).
Proof.
 intros e x y H.
 set (e' := ((1#3)*e)%Qpos).
 setoid_replace e with (e'+e'+e')%Qpos; [| unfold e';QposRing].
 apply ball_triangle with (Cmap plX (approximate f e') y).
  apply ball_triangle with (Cmap plX (approximate f e') x).
   rewrite -> Cap_fun_correct.
   simpl (Cmap plX (approximate f e') x).
   rewrite -> Cmap_fun_correct.
   apply Cap_slow_help.
  apply (uc_prf).
  apply H.
 apply ball_sym.
 rewrite -> Cap_fun_correct.
 simpl (Cmap plX (approximate f e') y).
 rewrite -> Cmap_fun_correct.
 apply Cap_slow_help.
Qed.

Definition Cap_weak X Y plX (f:Complete (X --> Y)) : Complete X --> Complete Y :=
Build_UniformlyContinuousFunction (Cap_weak_prf plX f).

Lemma Cap_weak_correct : forall X Y plX (f:Complete (X --> Y)), st_eq (Cap_weak plX f) (Cap_weak_slow f).
Proof.
 apply: Cap_fun_correct.
Qed.

Lemma Cap_prf X Y plX : is_UniformlyContinuousFunction (@Cap_weak X Y plX) Qpos2QposInf.
Proof.
 intros e a b Hab.
 do 2 rewrite -> Cap_weak_correct.
 apply Cap_slow_prf.
 auto.
Qed.

Definition Cap X Y plX : Complete (X --> Y) --> Complete X --> Complete Y :=
Build_UniformlyContinuousFunction (Cap_prf plX).

Lemma Cap_correct : forall X Y plX, st_eq (Cap Y plX) (Cap_slow X Y).
Proof.
 apply: Cap_fun_correct.
Qed.

(* begin hide *)
Add Parametric Morphism X Y plX : (@Cmap_fun X Y plX) with signature (@st_eq _) ==> (@st_eq _) ==> (@st_eq _) as Cmap_wd.
Proof.
 intros x1 x2 Hx y1 y2 Hy.
 change (st_eq (Cmap_fun plX x1 y1) (Cmap_fun plX x2 y2)).
 rewrite -> Cmap_fun_correct.
 set (a:=(Cmap_slow_fun x1 y1)).
 rewrite -> Cmap_fun_correct.
 apply Cmap_slow_wd; auto.
Qed.

Add Parametric Morphism X Y H : (@Cap_weak X Y H) with signature (@st_eq _) ==> (@st_eq _) as Cap_weak_wd.
Proof.
 intros x1 x2 Hx.
 apply: (@uc_wd _ _ (Cap Y H));assumption.
Qed.

Add Parametric Morphism X Y H : (@Cap_fun X Y H) with signature (@st_eq _) ==> (@st_eq _) ==> (@st_eq _) as Cap_wd.
Proof.
 intros x1 x2 Hx y1 y2 Hy.
 change (st_eq (Cap_fun H x1 y1) (Cap_fun H x2 y2)).
 transitivity (Cap_fun H x1 y2).
  apply (@uc_wd _ _ (Cap_weak H x1) _ _ Hy).
 generalize y2.
 apply: (@uc_wd _ _ (Cap Y H));assumption.
Qed.
(* end hide *)

(** Similarly we define a new [Cmap2]. *)
Definition Cmap2 (X Y Z:MetricSpace) (Xpl : PrelengthSpace X) (Ypl : PrelengthSpace Y) f := uc_compose (@Cap Y Z Ypl) (Cmap Xpl f).

(** Completion of a metric space preserves the prelength property.
In fact the completion of a prelenght space is a length space, but
we have not formalized the notion of a length space yet. *)
Lemma CompletePL : forall X, PrelengthSpace X -> PrelengthSpace (Complete X).
Proof.
 intros X Xpl x y e d1 d2 He Hxy.
 setoid_replace (d1+d2) with ((d1+d2)%Qpos:Q) in He; [| simpl; QposRing]. 
 destruct (Qpos_lt_plus He).
 pose (gA := ((1#5)*x0)%Qpos).
 pose (g := Qpos_min (Qpos_min ((1#2)*d1) ((1#2)*d2)) gA).
 unfold PrelengthSpace in Xpl.
 assert (Hd1:g < d1).
  unfold g.
  eapply Qle_lt_trans.
   apply Qpos_min_lb_l.
  eapply Qle_lt_trans.
   apply Qpos_min_lb_l.
  apply (half_3 _ (d1:Q)).
  apply Qpos_prf.
 assert (Hd2:g < d2).
  unfold g.
  eapply Qle_lt_trans.
   apply Qpos_min_lb_l.
  eapply Qle_lt_trans.
   apply Qpos_min_lb_r.
  apply (half_3 _ (d2:Q)).
  apply Qpos_prf.
 destruct (Qpos_lt_plus Hd1) as [d1' Hd1'].
 destruct (Qpos_lt_plus Hd2) as [d2' Hd2'].
 assert (He':(g + e + g)%Qpos < d1' + d2').
  apply: plus_cancel_less;simpl.
  instantiate (1:= (g+g)).
  assert (d1' + d2' + (g + g) == ((g+d1')%Qpos+(g+d2')%Qpos)).
   QposRing.
  rewrite -> H. clear H.
  unfold QposEq in *.
  rewrite <- Hd1'.
  rewrite <- Hd2'.
  clear d1' Hd1' d2' Hd2'.
  apply Qle_lt_trans with (e + 4*gA).
   stepl (e+4*g); [| unfold inject_Z; simpl; QposRing].
   apply: plus_resp_leEq_lft.
   apply: mult_resp_leEq_lft.
    apply Qpos_min_lb_r.
   compute; discriminate.
  assert (d1 + d2 == ((d1+d2)%Qpos:Q)). simpl; QposRing. rewrite -> H. clear H.
  rewrite -> q.
  assert (e + x0 == e+1*x0). QposRing. rewrite -> H. clear H.
  apply: plus_resp_less_lft;simpl.
  assert (4%positive * ((1 # 5) * x0) == (4#5)*x0). unfold inject_Z, gA. QposRing.
  rewrite -> H. clear H.
  apply: mult_resp_less.
   constructor.
  apply Qpos_prf.
 destruct (Xpl _ _ _ _ _ He' (Hxy g g)) as [c Hc1 Hc2].
 exists (Cunit c).
  rewrite <- Q_Qpos_plus in Hd1'.
  change (QposEq d1 (g + d1')) in Hd1'.
  rewrite -> Hd1'.
  eapply ball_triangle.
   apply ball_approx_r.
  rewrite -> ball_Cunit.
  assumption.
 rewrite <- Q_Qpos_plus in Hd2'.
 change (QposEq d2 (g + d2')) in Hd2'.
 rewrite -> Hd2'.
 setoid_replace (g + d2')%Qpos with (d2' + g)%Qpos; [| QposRing].
 eapply ball_triangle with (Cunit (approximate y g)).
  rewrite -> ball_Cunit.
  assumption.
 apply ball_approx_l.
Qed.
