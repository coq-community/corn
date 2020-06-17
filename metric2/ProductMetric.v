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
Require Import CoRN.model.totalorder.QposMinMax.
Require Export CoRN.metric2.Metric.
Require Import CoRN.metric2.Classification.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.metric2.Prelength.
Require Import CoRN.metric2.Complete.

Set Implicit Arguments.

(**
** Product Metric
The product of two metric spaces forms a metric space *)
Section ProductSetoid.

Variable X Y : RSetoid.

Definition prod_st_eq (a b:X*Y) :=
st_eq (fst a) (fst b) /\ st_eq (snd a) (snd b).

Lemma prodST : Setoid_Theory _ prod_st_eq.
Proof.
 split; unfold prod_st_eq.
   intros; split; reflexivity.
  intros x y [H1 H2]; split; symmetry; assumption.
 intros x y z [H1 H2] [H3 H4]; split.
  transitivity (fst y); assumption.
 transitivity (snd y); assumption.
Qed.

Definition prodS : RSetoid := Build_RSetoid prodST.
End ProductSetoid.

Section ProductMetric.
Variable X Y : MetricSpace.

Definition prod_ball e (a b:X*Y) :=
ball e (fst a) (fst b) /\ ball e (snd a) (snd b).

Lemma prod_ball_refl : forall (e:Q) a,
    0 <= e -> prod_ball e a a.
Proof.
 intros e a. split; apply ball_refl; exact H.
Qed.

Lemma prod_ball_sym : forall e a b, prod_ball e a b -> prod_ball e b a.
Proof.
 intros e a b [H1 H2].
 split; auto with *.
Qed.

Lemma prod_ball_triangle : forall e1 e2 a b c, prod_ball e1 a b -> prod_ball e2 b c -> prod_ball (e1 + e2) a c.
Proof.
 intros e1 e2 a b c [H1 H2] [H3 H4].
 split; eauto with metric.
Qed.

Lemma prod_ball_closed : forall e a b,
    (forall d, 0 < d -> prod_ball (e + d) a b) -> prod_ball e a b.
Proof.
 intros e a b H.
 unfold prod_ball in *.
 split; apply ball_closed; firstorder.
Qed.

Lemma prod_ball_eq : forall a b, (forall e, 0 < e -> prod_ball e a b) -> prod_st_eq _ _ a b.
Proof.
 intros a b H.
 unfold prod_ball in *.
 split; apply ball_eq; firstorder.
Qed.

Lemma prod_is_MetricSpace : is_MetricSpace (prodS X Y) prod_ball.
Proof.
 split.
 - intros. intros a. apply prod_ball_refl, H.
 - exact prod_ball_sym.
 - exact prod_ball_triangle.
 - exact prod_ball_closed.
 - exact prod_ball_eq.
 - intros. destruct H. apply (msp_nonneg (msp X)) in H. exact H.
Qed.

Definition ProductMS : MetricSpace.
Proof.
 exists (prodS X Y) prod_ball.
 2: apply prod_is_MetricSpace.
 intros e1 e2 He a1 a2 [Ha0 Ha1] b1 b2 [Hb0 Hb1]; unfold prod_ball.
 rewrite (ball_wd X He _ _ Ha0 _ _ Hb0).
 rewrite (ball_wd Y He _ _ Ha1 _ _ Hb1). reflexivity.
Defined.

(** Product metrics preserve properties of metric spaces such as
being a prelenght space, being stable, being located, and being deciable
*)
Lemma ProductMS_prelength : PrelengthSpace X -> PrelengthSpace Y -> PrelengthSpace ProductMS.
Proof.
 intros HX HY a b e d1 d2 Hed Hab.
 destruct (HX (fst a) (fst b) e d1 d2 Hed (proj1 Hab)) as [c1 Hc1].
 destruct (HY (snd a) (snd b) e d1 d2 Hed (proj2 Hab)) as [c2 Hc2].
 exists (c1,c2); split; assumption.
Defined.

Lemma ProductMS_stable : stableMetric X -> stableMetric Y -> stableMetric ProductMS.
Proof.
 unfold stableMetric.
 intros H0 H1 e [xl xr] [yl yr] H.
 simpl in H.
 unfold prod_ball in H.
 split.
  apply H0; tauto.
 apply H1; tauto.
Qed.

(** Furthermore, if a product space is stable, then the components are
stable (assuming the components are non-zero). *)
Lemma ProductMS_stableX : Y -> stableMetric ProductMS -> stableMetric X.
Proof.
 unfold stableMetric.
 intros a H0 e x y H.
 assert (Z:~ ~ ball (m:=ProductMS) e (x,a) (y,a)).
  revert H.
  cut (ball (m:=X) e x y -> ball (m:=ProductMS) e (x, a) (y, a)).
   tauto.
  intros H.
  split; auto.
  apply ball_refl. 
  apply (msp_nonneg (msp X) e x y H).
 destruct (H0 _ _ _ Z).
 assumption.
Qed.

Lemma ProductMS_stableY : X -> stableMetric ProductMS -> stableMetric Y.
Proof.
 unfold stableMetric.
 intros a H0 e x y H.
 assert (Z:~ ~ ball (m:=ProductMS) e (a,x) (a,y)).
  revert H.
  cut (ball (m:=Y) e x y -> ball (m:=ProductMS) e (a,x) (a, y)).
   tauto.
  intros H.
  split; auto. 
  apply ball_refl. 
  apply (msp_nonneg (msp Y) e x y H).
 destruct (H0 _ _ _ Z).
 assumption.
Qed.

Lemma ProductMS_located : locatedMetric X -> locatedMetric Y -> locatedMetric ProductMS.
Proof.
 unfold locatedMetric.
 intros H0 H1 e d x y Hed.
 destruct (H0 _ _ (fst x) (fst y) Hed) as [A | A].
  destruct (H1 _ _ (snd x) (snd y) Hed) as [B | B].
   left.
   split; assumption.
  right; intros [_ H].
  apply B; assumption.
 right; intros [H _].
 apply A; assumption.
Defined.

Lemma ProductMS_decidable : decidableMetric X -> decidableMetric Y -> decidableMetric ProductMS.
Proof.
 unfold decidableMetric.
 intros H0 H1 e x y.
 destruct (H0 e (fst x) (fst y)) as [A | A].
  destruct (H1 e (snd x) (snd y)) as [B | B].
   left.
   split; assumption.
  right; intros [_ H].
  apply B; assumption.
 right; intros [H _].
 apply A; assumption.
Defined.

(** This defines a pairing function with types of a metric space *)
Definition PairMS (x:X) (y:Y) : ProductMS := (x,y).

End ProductMetric.
(* begin hide *)
Arguments PairMS [X Y].

Add Parametric Morphism X Y : (@PairMS X Y) with signature (@st_eq _) ==> (@st_eq _) ==> (@st_eq _) as PairMS_wd.
Proof.
 intros.
 split; assumption.
Qed.
(* end hide *)
Local Open Scope uc_scope.

(** [together] forms the tensor of two functions operating between
metric spaces *)
Lemma together_uc : forall A B C D (f:A --> C) (g:B --> D),
 is_UniformlyContinuousFunction (fun (p:ProductMS A B) => (f (fst p), g (snd p)):ProductMS C D) (fun x => QposInf_min (mu f x) (mu g x)).
Proof.
 intros A B C D f g e a b H.
 split; simpl; apply uc_prf; apply ball_ex_weak_le with (QposInf_min (mu f e) (mu g e)).
    apply QposInf_min_lb_l.
   destruct (QposInf_min (mu f e) (mu g e)) as [q|]; auto.
   destruct H; auto.
  apply QposInf_min_lb_r.
 destruct (QposInf_min (mu f e) (mu g e)) as [q|]; auto.
 destruct H; auto.
Qed.

Definition together A B C D (f:A --> C) (g:B --> D) : (ProductMS A B --> ProductMS C D) :=
 Build_UniformlyContinuousFunction (together_uc f g).

(** Uniformly continuous functions on the product space can be curried: *)

Section uc_curry.

  Context {A B C: MetricSpace} (f: ProductMS A B --> C).

  Definition uc_curry_help_prf (a: A): is_UniformlyContinuousFunction (fun b => f (a, b)) (mu f).
  Proof with auto.
   repeat intro.
   destruct f. clear f. simpl in *.
   apply uc_prf.
   destruct (mu e)...
   split... apply ball_refl.
   apply Qpos_nonneg.
  Qed.

  Definition uc_curry_help (a: A): B --> C
    := Build_UniformlyContinuousFunction (uc_curry_help_prf a).

  Definition uc_curry_prf: is_UniformlyContinuousFunction uc_curry_help (mu f).
  Proof with auto.
   repeat intro. split. apply Qpos_nonneg. intro. simpl.
   destruct f. clear f. simpl in *.
   apply uc_prf.
   destruct (mu e)...
   split... apply ball_refl.
   apply Qpos_nonneg.
  Qed.

  Definition uc_curry: A --> B --> C
    := Build_UniformlyContinuousFunction uc_curry_prf.

End uc_curry.

(** Uncurry probably cannot be defined because because there is no way to construct a
 uniform modulus of continuity from the domain-indexed set of uni-formly continuous functions.

Hence, we can convert only one way, and so non-curried versions of binary functions are
strictly more valuable than their curried representations. Consequently, it can be argued
that binary functions should always be defined in non-curried form. *)

(** Completion distributes over products: *)

Section completion_distributes.

  Context {X Y: MetricSpace}.

  Definition distrib_Complete (xy: Complete (ProductMS X Y))
    : ProductMS (Complete X) (Complete Y).
  Proof.
    refine (@Build_RegularFunction _ (fun e => fst (approximate xy e)) _,
            @Build_RegularFunction _ (fun e => snd (approximate xy e)) _).
    intros e1 e2. apply xy.
    intros e1 e2. apply xy.
  Defined.

  Lemma distrib_Complete_uc_prf: is_UniformlyContinuousFunction distrib_Complete (fun e => e).
  Proof.
   unfold distrib_Complete.
   intros ??? H. split; repeat intro; simpl; apply H.
  Qed.

  Definition distrib_Complete_uc: Complete (ProductMS X Y) --> ProductMS (Complete X) (Complete Y) :=
    Build_UniformlyContinuousFunction distrib_Complete_uc_prf.

  Definition undistrib_Complete (xy: ProductMS (Complete X) (Complete Y))
    : Complete (ProductMS X Y).
  Proof.
    refine (@Build_RegularFunction
             (ProductMS X Y)
             (fun e => (approximate (fst xy) e, approximate (snd xy) e)) _).
    intros e1 e2.
    split. apply (regFun_prf (fst (xy))). apply (regFun_prf (snd (xy))).
  Defined. 

  Lemma undistrib_Complete_uc_prf: is_UniformlyContinuousFunction undistrib_Complete (fun e => e).
  Proof.
   unfold distrib_Complete.
   intros ??? H. split; repeat intro; simpl; apply H.
  Qed.

  Definition undistrib_Complete_uc: ProductMS (Complete X) (Complete Y) --> Complete (ProductMS X Y) :=
    Build_UniformlyContinuousFunction undistrib_Complete_uc_prf.

  Lemma distrib_after_undistrib_Complete xy: st_eq (distrib_Complete (undistrib_Complete xy)) xy.
  Proof.
   intros. unfold distrib_Complete, undistrib_Complete. simpl.
   unfold prod_st_eq. simpl.
   split; apply regFunEq_e; simpl; intros; apply ball_refl.
   apply (Qpos_nonneg (e+e)).
   apply (Qpos_nonneg (e+e)).
  Qed.

  Lemma undistrib_after_distrib_Complete xy: st_eq (undistrib_Complete (distrib_Complete xy)) xy.
  Proof.
   intros. unfold undistrib_Complete. simpl.
   apply regFunEq_e.
   split; simpl; apply ball_refl.
   apply (Qpos_nonneg (e+e)).
   apply (Qpos_nonneg (e+e)).
  Qed.

End completion_distributes.


(** The diagonal function [x ⟼ (x,x)] is a uniformly continuous function
  from a metric space X to the product space [X × X] *)
Section diag.
 Require Import Coq.Unicode.Utf8.
 Variable X:MetricSpace.

 Definition diag_raw : X → (ProductMS X X) := λ x, (x,x).

 Lemma diag_uc : (is_UniformlyContinuousFunction diag_raw (λ ε, ε)%Qpos).
 Proof.
  repeat try red; intuition.
 Qed.
 
 Definition diag: X --> (ProductMS X X) := Build_UniformlyContinuousFunction diag_uc.
End diag.

(* The curried and non-curried ways of lifting a function of 2 variables
   into the completed spaces are equal. *)
Lemma Cmap2_curry
  : forall (A B C: MetricSpace)
      (Apl : PrelengthSpace A) (Bpl : PrelengthSpace B)
      (f : ProductMS A B --> C) (a : Complete A) (b : Complete B),
    @st_eq (Complete C)
           (Cmap2 Apl Bpl (uc_curry f) a b)
           (uc_compose (Cmap (ProductMS_prelength Apl Bpl) f)
                       undistrib_Complete_uc (a,b)).
Proof.
  intros. intros e1 e2. 
  assert ((1#2)*proj1_sig e1 + proj1_sig e2 <= proj1_sig e1 + proj1_sig e2).
  { apply Qplus_le_l.
    rewrite <- (Qmult_1_l (proj1_sig e1)) at 2.
    apply Qmult_le_r. apply Qpos_ispos. discriminate. }
  apply (ball_weak_le _ _ _ H).
  apply (mu_sum (ProductMS_prelength Apl Bpl) e2 (((1#2)*e1)%Qpos :: nil) f).
  simpl. clear H.
  destruct (mu f (exist (Qlt 0) (1#2) (@eq_refl comparison Lt) * e1)).
  2: reflexivity.
  destruct (mu f e2). 2: reflexivity. split; apply regFun_prf.
Qed.

Definition uc_flip (X Y : MetricSpace) : ProductMS X Y --> ProductMS Y X.
Proof.
  apply (@Build_UniformlyContinuousFunction
            (ProductMS X Y) (ProductMS Y X)
            (fun xy => pair (snd xy) (fst xy)) (fun e => e)).
  intros e a b H. simpl. split; apply H.
Defined.

Definition uc_assoc (X Y Z : MetricSpace)
  : ProductMS (ProductMS X Y) Z --> ProductMS X (ProductMS Y Z).
Proof.
  apply (@Build_UniformlyContinuousFunction
            (ProductMS (ProductMS X Y) Z) (ProductMS X (ProductMS Y Z))
            (fun xyz => pair (fst (fst xyz)) (pair (snd (fst xyz)) (snd xyz)))
            (fun e => e)).
  intros e a b H. simpl. split.
  - simpl. destruct H, H. exact H.
  - simpl. destruct H, H. split; assumption.
Defined.

Lemma uc_pair_prf : 
  forall (A B C D : MetricSpace)
    (f : A --> B) (g : C --> D), 
    @is_UniformlyContinuousFunction
      (ProductMS A C) (ProductMS B D)
      (λ ac : ProductMS A C, (f (fst ac), g (snd ac)))
      (λ e : Qpos, QposInf_min (mu f e) (mu g e)).
Proof.
  intros. intros e x y H. split.
  - simpl. apply (uc_prf f).
    destruct (mu f e). 2: reflexivity. 
    apply (ball_ex_weak_le _ (QposInf_min q (mu g e))).
    simpl. destruct (mu g e). apply Qpos_min_lb_l.
    apply Qle_refl. simpl. destruct (mu g e).
    apply H. apply H.
  - simpl. apply (uc_prf g).
    destruct (mu g e). 2: reflexivity. 
    apply (ball_ex_weak_le _ (QposInf_min (mu f e) q)).
    destruct (mu f e). simpl. apply Qpos_min_lb_r.
    apply Qle_refl. destruct (mu f e).
    apply H. apply H.
Qed.

Definition uc_pair (A B C D : MetricSpace)
           (f : A --> B) (g : C --> D) : ProductMS A C --> ProductMS B D
  := Build_UniformlyContinuousFunction (uc_pair_prf f g).
  
Definition uc_complete_curry {X Y Z : MetricSpace}
           (f : Complete (ProductMS X Y) --> Z)
  : Complete X --> Complete Y --> Z
  := uc_curry (uc_compose f undistrib_Complete_uc).

Lemma Cmap2_comm
  : forall (X Y : MetricSpace) (Xpl : PrelengthSpace X)
      (f : ProductMS X X --> Y),
    (forall a b :X, st_eq (f (a,b)) (f (b,a)))
    -> forall (a b:Complete X),
      @st_eq (Complete Y)
             (uc_complete_curry (Cmap (ProductMS_prelength Xpl Xpl) f) a b)
             (uc_complete_curry (Cmap (ProductMS_prelength Xpl Xpl) f) b a).
Proof.
  intros.
  assert (ucEq (Cmap (ProductMS_prelength Xpl Xpl) f)
               (Cmap (ProductMS_prelength Xpl Xpl)
                     (uc_compose f (uc_flip X X)))).
  { intro x. apply Cmap_wd.
    intros xy. simpl. rewrite H. destruct xy. reflexivity. reflexivity. }
  specialize (H0 (undistrib_Complete (a,b))).
  simpl in H0. simpl. intros e1 e2. specialize (H0 e1 e2).
  simpl. simpl in H0.
  assert (forall x, eq (QposInf_bind (λ e : Qpos, e) x) x).
  { intro x. destruct x;reflexivity. }
  rewrite H1 in H0. apply H0.
Qed.

