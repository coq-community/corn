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
Require Export CoRN.metric2.Metric.
Require Import CoRN.metric2.Classification.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.metric2.Prelength.
Require Import CoRN.metric2.Complete.
Require Import CoRN.tactics.CornTac.

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

Lemma prod_ball_refl : forall e a, prod_ball e a a.
Proof.
 intros e a.
 split; auto with *.
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

Lemma prod_ball_closed : forall e a b, (forall d, prod_ball (e + d) a b) -> prod_ball e a b.
Proof.
 intros e a b H.
 unfold prod_ball in *.
 split; apply ball_closed; firstorder.
Qed.

Lemma prod_ball_eq : forall a b, (forall e, prod_ball e a b) -> prod_st_eq _ _ a b.
Proof.
 intros a b H.
 unfold prod_ball in *.
 split; apply ball_eq; firstorder.
Qed.

Lemma prod_is_MetricSpace : is_MetricSpace (prodS X Y) prod_ball.
Proof.
 split.
     exact prod_ball_refl.
    exact prod_ball_sym.
   exact prod_ball_triangle.
  exact prod_ball_closed.
 exact prod_ball_eq.
Qed.

Definition ProductMS : MetricSpace.
Proof.
 exists (prodS X Y) prod_ball.
  abstract ( intros e1 e2 He a1 a2 [Ha0 Ha1] b1 b2 [Hb0 Hb1]; unfold prod_ball;
    change (QposEq e1 e2) in He; rewrite -> He, Ha0, Ha1, Hb0, Hb1; reflexivity) using prod_ball_wd.
 apply prod_is_MetricSpace.
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
Implicit Arguments PairMS [X Y].

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
  Qed.

  Definition uc_curry_help (a: A): B --> C := Build_UniformlyContinuousFunction (uc_curry_help_prf a).

  Definition uc_curry_prf: is_UniformlyContinuousFunction uc_curry_help (mu f).
  Proof with auto.
   repeat intro. simpl.
   destruct f. clear f. simpl in *.
   apply uc_prf.
   destruct (mu e)...
   split... apply ball_refl.
  Qed.

  Definition uc_curry: A --> B --> C := Build_UniformlyContinuousFunction uc_curry_prf.

End uc_curry.

(** Uncurry probably cannot be defined because because there is no way to construct a
 uniform modulus of continuity from the domain-indexed set of uni-formly continuous functions.

Hence, we can convert only one way, and so non-curried versions of binary functions are
strictly more valuable than their curried representations. Consequently, it can be argued
that binary functions should always be defined in non-curried form. *)

(** Completion distributes over products: *)

Section completion_distributes.

  Context {X Y: MetricSpace}.

  Program Definition distrib_Complete (xy: Complete (ProductMS X Y)): ProductMS (Complete X) (Complete Y) :=
   (@Build_RegularFunction _ (fun e => fst (approximate xy e)) _, @Build_RegularFunction _ (fun e => snd (approximate xy e)) _).

  Next Obligation. repeat intro. apply xy. Qed.
  Next Obligation. repeat intro. apply xy. Qed.

  Lemma distrib_Complete_uc_prf: is_UniformlyContinuousFunction distrib_Complete (fun e => e).
  Proof.
   unfold distrib_Complete.
   intros ??? H. split; repeat intro; simpl; apply H.
  Qed.

  Definition distrib_Complete_uc: Complete (ProductMS X Y) --> ProductMS (Complete X) (Complete Y) :=
    Build_UniformlyContinuousFunction distrib_Complete_uc_prf.

  Program Definition undistrib_Complete (xy: ProductMS (Complete X) (Complete Y)): Complete (ProductMS X Y) :=
   @Build_RegularFunction _ (fun e => (approximate (fst xy) e, approximate (snd xy) e)) _.

  Next Obligation. split. apply r. apply r0. Qed.

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
  Qed.

  Lemma undistrib_after_distrib_Complete xy: st_eq (undistrib_Complete (distrib_Complete xy)) xy.
  Proof.
   intros. unfold undistrib_Complete. simpl.
   apply regFunEq_e.
   split; simpl; apply ball_refl.
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