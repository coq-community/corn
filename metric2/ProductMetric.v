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
Require Import CoRN.model.totalorder.QposMinMax.
Require Export CoRN.metric2.Metric.
Require Import CoRN.metric2.Classification.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.metric2.Prelength.
Require Import CoRN.metric2.Complete.
Require Import CoRN.metric2.LocatedSubset.

Set Implicit Arguments.

(**
** Product Metric
The product of two metric spaces forms a metric space *)
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

Lemma prod_is_MetricSpace : is_MetricSpace prod_ball.
Proof.
 split.
 - intros. intros a. apply prod_ball_refl, H.
 - exact prod_ball_sym.
 - exact prod_ball_triangle.
 - exact prod_ball_closed.
 - intros. destruct H. apply (msp_nonneg (msp X)) in H. exact H.
 - intros. split.
   + apply (msp_stable (msp X)).
     intro abs.
     contradict H; intros [H _].
     contradiction.
   + apply (msp_stable (msp Y)).
     intro abs.
     contradict H; intros [_ H].
     contradiction.
Qed.

Definition ProductMS : MetricSpace.
Proof.
 exists (prod X Y) prod_ball.
 2: apply prod_is_MetricSpace.
 intros e1 e2 a1 a2 He. split.
 - intros [H H0]. split; rewrite <- He; assumption.
 - intros [H H0]. split; rewrite He; assumption.
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

Add Parametric Morphism X Y : (@PairMS X Y)
    with signature (@msp_eq _) ==> (@msp_eq _) ==> (@msp_eq _) as PairMS_wd.
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
    refine (@Build_RegularFunction _ _ (fun e => fst (approximate xy e)) _,
            @Build_RegularFunction _ _ (fun e => snd (approximate xy e)) _).
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
             (ProductMS X Y) _
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

  Lemma distrib_after_undistrib_Complete xy
    : msp_eq (distrib_Complete (undistrib_Complete xy)) xy.
  Proof.
   intros. unfold distrib_Complete, undistrib_Complete. simpl.
   split; apply regFunEq_equiv, regFunEq_e; simpl; intros; apply ball_refl.
   apply (Qpos_nonneg (e+e)).
   apply (Qpos_nonneg (e+e)).
  Qed.

  Lemma undistrib_after_distrib_Complete xy
    : msp_eq (undistrib_Complete (distrib_Complete xy)) xy.
  Proof.
   intros. unfold undistrib_Complete. 
   apply regFunEq_equiv.
   apply (@regFunEq_e (ProductMS X Y)).
   split; simpl; apply ball_refl.
   apply (Qpos_nonneg (e+e)).
   apply (Qpos_nonneg (e+e)).
  Qed.

End completion_distributes.


(** The diagonal function [x ⟼ (x,x)] is a uniformly continuous function
  from a metric space X to the product space [X × X] *)

Require Import Coq.Unicode.Utf8.

Section diag.
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
    @msp_eq (Complete C)
           (Cmap2 Apl Bpl (uc_curry f) a b)
           (uc_compose (Cmap (ProductMS_prelength Apl Bpl) f)
                       undistrib_Complete_uc (a,b)).
Proof.
  intros. intros e1 e2. 
  rewrite Qplus_0_r.
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

Definition uc_complete_curry {X Y Z : MetricSpace}
           (f : Complete (ProductMS X Y) --> Z)
  : Complete X --> Complete Y --> Z
  := uc_curry (uc_compose f undistrib_Complete_uc).

Lemma Cmap2_comm
  : forall (X Y : MetricSpace) (Xpl : PrelengthSpace X)
      (f : ProductMS X X --> Y),
    (forall a b :X, msp_eq (f (a,b)) (f (b,a)))
    -> forall (a b:Complete X),
      @msp_eq (Complete Y)
             (uc_complete_curry (Cmap (ProductMS_prelength Xpl Xpl) f) a b)
             (uc_complete_curry (Cmap (ProductMS_prelength Xpl Xpl) f) b a).
Proof.
  intros.
  assert (ucEq (Cmap (ProductMS_prelength Xpl Xpl) f)
               (Cmap (ProductMS_prelength Xpl Xpl)
                     (uc_compose f (uc_flip X X)))).
  { intro x. apply Cmap_wd.
    apply ucEq_equiv.
    intros xy. simpl. rewrite H. destruct xy. reflexivity. reflexivity. }
  specialize (H0 (undistrib_Complete (a,b))).
  simpl in H0. simpl. intros e1 e2. specialize (H0 e1 e2).
  simpl. simpl in H0.
  assert (forall x, eq (QposInf_bind (λ e : Qpos, e) x) x).
  { intro x. destruct x;reflexivity. }
  rewrite H1 in H0. apply H0.
Qed.

Lemma undistrib_Located
  : forall (X Y : MetricSpace) (A : Complete (ProductMS X Y) -> Prop),
    LocatedSubset _ A
    -> LocatedSubset (ProductMS (Complete X) (Complete Y))
                    (fun xy => exists p, msp_eq p (undistrib_Complete xy) /\ A p).
Proof.
  intros X Y A loc d e p ltde.
  destruct (loc d e (undistrib_Complete p) ltde) as [far|close].
  - left. intros y H abs.
    destruct H as [q [H H0]].
    apply (far q H0).
    rewrite H.
    intros d1 d2; split; simpl; apply abs.
  - right. destruct close as [y [Ay close]].
    exists (distrib_Complete y). split.
    exists y. split. symmetry. apply undistrib_after_distrib_Complete.
    exact Ay.
    rewrite <- distrib_after_undistrib_Complete.
    split; intros d1 d2; apply close.
Defined.
