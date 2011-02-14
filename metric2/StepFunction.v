(*
Copyright © 2007-2008 Russell O’Connor

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
Require Import OpenUnit.
Require Import CornTac.
Require Import Qauto.
Require Import Qordfield.
Require Import COrdFields.

Set Implicit Arguments.

Open Local Scope Q_scope.

Section StepFunction.

Variable X:Type.

(**
* Step Functions
We represent step functions from [[0,1]] to [X] inductively as a tree
structure.  In the base case a costant function is a step function.
Given two step functions f and g, then they can be scaled and glued
together at a point o yeilding the step function which is f(x/o) for
x in [[0,o]], and g((x-o)/(1-o)) for x in [[o,1]].

Step functions are not functions.  They could be interpreted as
functions; however, we don't give any particular interpretation to how
the step functions ought to behave at the glue points in between step.
Because our primary purpose for introducing step functions is to
implement integration, this ambiguity is not a problem.
*)

Inductive StepF :Type:=
|constStepF:X-> StepF
|glue:OpenUnit-> StepF -> StepF -> StepF.

Fixpoint StepFfold (Y : Type) (f : X -> Y) (g : OpenUnit -> Y -> Y -> Y)
              (s : StepF) {struct s} : Y :=
  match s with
  | constStepF x => f x
  | glue b t1 t2 => g b (StepFfold f g t1) (StepFfold f g t2)
  end.

(** If f is a step function, so is f(1-x).  This symmetry operation
is useful reasoning about step functions because of the symetric nature
of the glue constructor. *)
Definition Mirror :StepF -> StepF :=
StepFfold constStepF (fun a l r => glue (OpenUnitDual a) r l).

(** [Split] decomposes (and scales) a step function at a point o.
It is essentially an inverse operation of glue *)
Definition Split : StepF -> OpenUnit -> StepF*StepF.
Proof.
 fix 1.
 intros s a.
 destruct s as [x | b t1 t2].
  exact (constStepF x , constStepF x).
 destruct (Q_dec a b) as [[H|H]|H].
   destruct (Split t1 (OpenUnitDiv a b H)) as [L R].
   exact (L, (glue (OpenUnitDualDiv b a H) R t2)).
  destruct (Split t2 (OpenUnitDualDiv a b H)) as [L R].
  refine ((glue (OpenUnitDiv b a H) t1 L), R).
 exact (t1,t2).
Defined.

Definition SplitL (s:StepF) (o:OpenUnit) : StepF :=
fst (Split s o).

Definition SplitR (s:StepF) (o:OpenUnit) : StepF :=
snd (Split s o).

(** Induction principles for reasoning about [Split], [SplitR],
and [SplitL] *)
Lemma Split_ind : forall s a (P:StepF*StepF -> Prop),
 (P (SplitL s a,SplitR s a)) -> P (Split s a).
Proof.
 intros s a P.
 unfold SplitL, SplitR.
 destruct (Split s a).
 auto with *.
Qed.

Lemma SplitLR_glue_ind : forall s1 s2 (a b:OpenUnit) (P:StepF -> StepF -> Prop),
 (forall (H:a < b), P (SplitL s1 (OpenUnitDiv a b H)) (glue (OpenUnitDualDiv b a H) (SplitR s1 (OpenUnitDiv a b H)) s2)) ->
 (forall (H:b < a), P (glue (OpenUnitDiv b a H) s1 (SplitL s2 (OpenUnitDualDiv a b H))) (SplitR s2 (OpenUnitDualDiv a b H))) ->
 (a == b -> P s1 s2) ->
 P (SplitL (glue b s1 s2) a) (SplitR (glue b s1 s2) a).
Proof.
 intros s1 s2 a b P Hl Hr Heq.
 unfold SplitL, SplitR.
 simpl.
 destruct (Q_dec a b) as [[Hab|Hab]|Hab]; try apply Split_ind; simpl; auto with *.
Qed.

Lemma SplitL_glue_ind : forall s1 s2 (a b:OpenUnit) (P:StepF -> Prop),
 (forall (H:a < b), P (SplitL s1 (OpenUnitDiv a b H))) ->
 (forall (H:b < a), P (glue (OpenUnitDiv b a H) s1 (SplitL s2 (OpenUnitDualDiv a b H)))) ->
 (a == b -> P (s1)) ->
 P (SplitL (glue b s1 s2) a).
Proof.
 intros.
 apply (SplitLR_glue_ind s1 s2 a b (fun a b => P a)); assumption.
Qed.

Lemma SplitR_glue_ind : forall s1 s2 (a b:OpenUnit) (P:StepF -> Prop),
 (forall (H:a < b), P (glue (OpenUnitDualDiv b a H) (SplitR s1 (OpenUnitDiv a b H)) s2)) ->
 (forall (H:b < a), P (SplitR s2 (OpenUnitDualDiv a b H))) ->
 (a == b -> P (s2)) ->
 P (SplitR (glue b s1 s2) a).
Proof.
 intros.
 apply (SplitLR_glue_ind s1 s2 a b (fun a b => P b)); assumption.
Qed.

Lemma SplitGlue : forall x y:StepF, forall o,
  (Split (glue o x y) o)=(x,  y).
Proof.
 intros. simpl.
 destruct (Q_dec o o) as [[H1|H1]|H1]; try (elim (Qlt_not_le _ _ H1); auto with * ); simpl; auto with *.
Qed.

Lemma SplitLGlue : forall x y:StepF, forall o,
  (SplitL (glue o x y) o)=x.
Proof.
 unfold SplitL.
 intros.
 rewrite SplitGlue.
 reflexivity.
Qed.

Lemma SplitRGlue : forall x y:StepF, forall o,
  (SplitR (glue o x y) o)=y.
Proof.
 unfold SplitR.
 intros.
 rewrite SplitGlue.
 reflexivity.
Qed.

(** As stepping point to a proper setoid equality on step functions,
[StepF_Qeq] specifies equality of step function upto [Qeq] on
rational glue points *)
Fixpoint StepF_Qeq (s1 s2: StepF) : Prop :=
match s1, s2 with
|constStepF x, constStepF y => x = y
|glue a x1 x2, glue b y1 y2 => a == b /\ (StepF_Qeq x1 y1) /\ (StepF_Qeq x2 y2)
|_, _ => False
end.

Lemma StepF_Qeq_refl : forall (s: StepF), StepF_Qeq s s.
Proof.
 induction s; simpl; auto with *.
Qed.

Lemma StepF_Qeq_sym : forall (s t: StepF), StepF_Qeq s t -> StepF_Qeq t s.
Proof.
 induction s; induction t; try contradiction; simpl; auto with *.
 intros [H0 [H1 H2]].
 repeat split; eauto with *.
Qed.

Lemma StepF_Qeq_trans : forall (s t u: StepF), StepF_Qeq s t -> StepF_Qeq t u -> StepF_Qeq s u.
Proof.
 induction s; induction t; induction u; try contradiction; simpl; auto with *.
  intros; transitivity x0; assumption.
 intros [H0 [H1 H2]] [H3 [H4 H5]].
 repeat split; eauto with *.
Qed.
(* begin hide *)
Hint Resolve StepF_Qeq_refl StepF_Qeq_sym StepF_Qeq_trans.
(* end hide *)
(** [Mirror] behaves well with respect to this equality *)
Lemma Mirror_resp_Qeq : forall (s t:StepF), StepF_Qeq s t -> StepF_Qeq (Mirror s) (Mirror t).
Proof.
 induction s; induction t; intros Hst; simpl in *; try assumption; try contradiction.
 destruct Hst as [Ho [Hst1 Hst2]].
 repeat split.
   rewrite -> Ho; reflexivity.
  apply IHs2; assumption.
 apply IHs1; assumption.
Qed.
(* begin hide *)
Hint Resolve Mirror_resp_Qeq.
(* end hide *)
Lemma MirrorMirror : forall (s:StepF), (StepF_Qeq (Mirror (Mirror s)) s).
Proof.
 induction s.
  simpl; reflexivity.
 repeat split; auto with *.
 simpl; ring.
Qed.
(* begin hide *)
Hint Resolve MirrorMirror.
(* end hide *)
(** Splits interacts with Mirror in the way you expect *)
Lemma SplitR_resp_Qeq : forall (s t:StepF) (a b:OpenUnit), a == b -> StepF_Qeq s t -> StepF_Qeq (SplitR s a) (SplitR t b).
Proof.
 induction s; induction t; intros a b Hab Hst; simpl in *; try assumption; try contradiction.
 destruct Hst as [Ho [Hst1 Hst2]].
 apply SplitR_glue_ind; intros Hao; apply SplitR_glue_ind; intros Hbo; repeat split; auto with *;
   try solve [elim (Qlt_not_le _ _ Hao); rewrite -> Hab; rewrite -> Ho; try rewrite -> Hbo; auto with *
     |elim (Qlt_not_le _ _ Hbo); rewrite <- Hab; rewrite <- Ho; try rewrite -> Hao; auto with *];
       try apply IHs1; try apply IHs2; auto with *; simpl; try (rewrite -> Hab; rewrite -> Ho; reflexivity).
Qed.
(* begin hide *)
Hint Resolve SplitR_resp_Qeq.
(* end hide *)
Lemma MirrorSplitL_Qeq : forall (s:StepF) (a b:OpenUnit), b == (OpenUnitDual a) -> (StepF_Qeq (Mirror (SplitL s a)) (SplitR (Mirror s) b)).
Proof.
 induction s.
  auto with *.
 intros a b Hab; simpl in Hab.
 simpl.
 apply SplitL_glue_ind; intros Hao; apply: SplitR_glue_ind; intros Hoa; simpl in Hoa;
   try (repeat split; auto with *; try apply IHs1; try apply IHs2; simpl; rewrite -> Hab; field; auto with * ).
       elim (Qlt_not_le _ _ Hao).
       rewrite -> Qlt_minus_iff in Hoa.
       rewrite -> Qle_minus_iff.
       replace RHS with (1 - o + - (1 - a)).
        rewrite <- Hab.
        auto with *.
       now simpl; ring.
      elim (Qlt_not_le _ _ Hao).
      rewrite -> Qle_minus_iff.
      replace RHS with (1 - o + - (1 - a)).
       rewrite <- Hab.
       rewrite <- Hoa.
       ring_simplify.
       auto with *.
      now simpl; ring.
     intros H; ring_simplify in H.
     revert H; change (~(a==0)); auto with *.
    elim (Qlt_not_le _ _ Hao).
    rewrite -> Qle_minus_iff.
    rewrite -> Qlt_minus_iff in Hoa.
    replace RHS with (1 - a + - (1 - o)).
     rewrite <- Hab.
     auto with *.
    now simpl; ring.
   elim (Qlt_not_le _ _ Hao).
   rewrite -> Qle_minus_iff.
   replace RHS with (1 - a + - (1 - o)).
    rewrite <- Hab.
    rewrite <- Hoa.
    ring_simplify.
    auto with *.
   now simpl; ring.
  elim (Qlt_not_le _ _ Hoa).
  rewrite -> Hab.
  rewrite -> Hao.
  auto with *.
 elim (Qlt_not_le _ _ Hoa).
 rewrite -> Hab.
 rewrite -> Hao.
 auto with *.
Qed.

Lemma MirrorSplitR_Qeq: forall (s:StepF) (a b:OpenUnit), b == (OpenUnitDual a) -> (StepF_Qeq (Mirror (SplitR s a)) (SplitL (Mirror s) b)).
Proof.
 intros s a b H.
 apply StepF_Qeq_trans with (Mirror (SplitR (Mirror (Mirror s)) a)); auto with *.
 apply StepF_Qeq_trans with (Mirror (Mirror (SplitL (Mirror s) b))); auto with *.
 apply Mirror_resp_Qeq.
 apply StepF_Qeq_sym.
 apply MirrorSplitL_Qeq.
 simpl in *.
 rewrite -> H.
 ring.
Qed.

Lemma SplitL_resp_Qeq : forall (s t:StepF) (a b:OpenUnit), a == b -> StepF_Qeq s t -> StepF_Qeq (SplitL s a) (SplitL t b).
Proof.
 intros s t a b H H0.
 apply StepF_Qeq_trans with (Mirror (Mirror (SplitL s a))); auto with *.
 apply StepF_Qeq_trans with (Mirror (SplitR (Mirror s) (OpenUnitDual a))).
  apply Mirror_resp_Qeq.
  apply MirrorSplitL_Qeq; auto with *.
 apply StepF_Qeq_trans with (Mirror (SplitR (Mirror t) (OpenUnitDual b))).
  apply Mirror_resp_Qeq.
  apply SplitR_resp_Qeq; auto with *.
  simpl; rewrite -> H; reflexivity.
 apply StepF_Qeq_trans with (Mirror (Mirror (SplitL t b))); auto with *.
 apply Mirror_resp_Qeq.
 apply StepF_Qeq_sym.
 apply MirrorSplitL_Qeq; auto with *.
Qed.
(* begin hide *)
Hint Resolve SplitL_resp_Qeq.
(* end hide *)
(** The following three lemmas are the key lemmas about Splits.  They
characterise how Splits distribute across each other. *)
Lemma SplitLSplitL : forall (s:StepF) (a b c:OpenUnit), (a*b==c) ->
 (StepF_Qeq (SplitL (SplitL s a) b) (SplitL s c)).
Proof.
 induction s.
  intros a b c _.
  apply StepF_Qeq_refl.
 intros a b c H.
 apply SplitL_glue_ind; intros Hao.
   apply SplitL_glue_ind; intros Hco.
     apply IHs1.
     simpl.
     rewrite <- H; field.
     auto with *.
    elim (Qlt_not_le a c).
     apply Qlt_trans with o; assumption.
    rewrite <- H.
    replace RHS with (1*a).
     replace LHS with (b*a).
      apply Qmult_le_compat_r; auto with *.
     now simpl; ring.
    now simpl; ring.
   elim (Qlt_not_le a c).
    rewrite -> Hco.
    apply Qlt_le_trans with o; auto with *.
   rewrite <- H.
   replace RHS with (1*a).
    replace LHS with (b*a).
     apply Qmult_le_compat_r; auto with *.
    now simpl; ring.
   now simpl; ring.
  apply SplitL_glue_ind; intros Hbd.
    apply SplitL_glue_ind; intros Hco.
      apply SplitL_resp_Qeq; auto with *.
      simpl.
      rewrite <- H.
      field; auto with *.
     elim (Qlt_not_le _ _ Hbd).
     simpl.
     apply Qle_shift_div_r; auto with *.
     rewrite -> Qmult_comm; rewrite -> H; auto with *.
    elim (Qlt_not_le _ _ Hbd).
    simpl.
    apply Qle_shift_div_r; auto with *.
    rewrite -> Qmult_comm; rewrite -> H; rewrite -> Hco; auto with *.
   apply SplitL_glue_ind; intros Hco.
     elim (Qlt_not_le _ _ Hbd).
     simpl.
     apply Qle_shift_div_l; auto with *.
     rewrite -> Qmult_comm; rewrite -> H; auto with *.
    repeat split; auto with *.
     simpl.
     rewrite <- H.
     field; auto with *.
    apply IHs2.
    simpl.
    rewrite <- H.
    field; repeat split; auto with *.
    clear - Hao; rewrite -> Qlt_minus_iff in Hao.
    auto with *.
   elim (Qlt_not_le _ _ Hbd).
   simpl.
   apply Qle_shift_div_l; auto with *.
   rewrite -> Qmult_comm; rewrite -> H; auto with *.
  assert (Y:o==c).
   rewrite <- H.
   rewrite -> Hbd.
   simpl.
   field.
   auto with *.
  apply SplitL_glue_ind; intros Hco; try (elim (Qlt_not_le _ _ Hco); rewrite -> Y; auto with * ).
  auto with *.
 apply SplitL_glue_ind; intros Hco.
   apply SplitL_resp_Qeq; auto with *.
   simpl.
   rewrite <- H.
   rewrite -> Hao.
   field; auto with *.
  elim (Qlt_not_le _ _ Hco).
  rewrite <- H.
  rewrite <- Hao.
  replace RHS with (1*a).
   replace LHS with (b*a).
    apply Qmult_le_compat_r; auto with *.
   now simpl; ring.
  now simpl; ring.
 elim (Qlt_not_le b 1).
  auto with *.
 rewrite <- Hao in Hco.
 rewrite -> Hco in H.
 apply Qmult_lt_0_le_reg_r with a.
  auto with *.
 ring_simplify.
 rewrite -> H.
 auto with *.
Qed.

Lemma SplitRSplitR : forall (s:StepF) (a b c:OpenUnit), (a+b-a*b==c) ->
 (StepF_Qeq (SplitR (SplitR s a) b) (SplitR s c)).
Proof.
 intros s a b c H.
 apply StepF_Qeq_trans with (Mirror (Mirror (SplitR (SplitR s a) b))); auto with *.
 apply StepF_Qeq_trans with (Mirror (Mirror (SplitR s c))); auto with *.
 apply Mirror_resp_Qeq.
 apply StepF_Qeq_trans with (SplitL (SplitL (Mirror s) (OpenUnitDual a)) (OpenUnitDual b)).
  apply StepF_Qeq_trans with (SplitL (Mirror (SplitR s a)) (OpenUnitDual b)).
   apply MirrorSplitR_Qeq; auto with *.
  apply SplitL_resp_Qeq; auto with *.
  apply MirrorSplitR_Qeq; auto with *.
 apply StepF_Qeq_trans with (SplitL (Mirror s) (OpenUnitDual c)).
  apply SplitLSplitL.
  simpl.
  rewrite <- H.
  ring.
 apply StepF_Qeq_sym.
 apply MirrorSplitR_Qeq; auto with *.
Qed.

Lemma SplitLSplitR : forall (s:StepF) (a b c d:OpenUnit), (a+b-a*b==c) -> (d*c==a) ->
 (StepF_Qeq (SplitL (SplitR s a) b) (SplitR (SplitL s c) d)).
Proof.
 induction s.
  intros a b c d _ _.
  apply StepF_Qeq_refl.
 intros a b c d H0 H1.
 apply SplitR_glue_ind; intros Hao.
   assert (Hao':~ o - a == 0).
    intros H.
    elim (Qlt_not_le _ _ Hao).
    rewrite -> Qle_minus_iff.
    replace RHS with (- (o- a)).
     rewrite -> H.
     auto with *.
    now simpl; ring.
   apply SplitL_glue_ind; intros Hbz; simpl in Hbz.
     apply SplitL_glue_ind; intros Hco.
       apply IHs1; simpl; [rewrite <- H0|rewrite <- H1]; field; auto with *.
      elim (Qlt_not_le _ _ Hbz).
      rewrite -> Qlt_minus_iff in Hco.
      rewrite -> Qle_minus_iff.
      replace RHS with ((a + b - a*b + -o)/(1 -a)).
       rewrite -> H0.
       apply Qle_shift_div_l; auto with *.
       replace LHS with 0.
        auto with *.
       now simpl; ring.
      now (simpl; field; auto with * ).
     elim (Qlt_not_le _ _ Hbz).
     rewrite -> Qle_minus_iff.
     replace RHS with ((a + b - a*b + -o)/(1 -a)).
      rewrite -> H0.
      rewrite -> Hco.
      replace RHS with 0.
       auto with *.
      now (simpl; field; auto with * ).
     now (simpl; field; auto with * ).
    apply SplitL_glue_ind; intros Hco.
      elim (Qlt_not_le _ _ Hbz).
      rewrite -> Qlt_minus_iff in Hco.
      rewrite -> Qle_minus_iff.
      replace RHS with ((o + -(a + b - a*b))/(1 -a)).
       rewrite -> H0.
       apply Qle_shift_div_l; auto with *.
       replace LHS with 0.
        auto with *.
       now simpl; ring.
      simpl; field. now auto with *.
     apply SplitR_glue_ind; intros Hdz; simpl in Hdz.
       repeat split; simpl.
         field_simplify; auto with *.
         apply Qmult_comp.
          rewrite <- H1; ring.
         apply Qinv_comp.
         replace LHS with (a + b - a*b - a).
          rewrite -> H0.
          replace RHS with (c - (d*c)).
           rewrite -> H1.
           reflexivity.
          now simpl; ring.
         now simpl; ring.
        apply SplitR_resp_Qeq; auto with *; simpl.
        rewrite <- H1; field; auto with *.
       apply SplitL_resp_Qeq; auto with *; simpl.
       rewrite <- H0; field; auto with *.
      elim (Qlt_not_le _ _ Hdz).
      apply Qle_shift_div_l; auto with *.
      rewrite -> H1; auto with *.
     elim (Qlt_not_le _ _ Hao).
     rewrite <- H1.
     rewrite -> Hdz.
     replace RHS with (o:Q).
      auto with *.
     simpl. field. now auto with *.
    elim (Qlt_not_le _ _ Hbz).
    rewrite <- Hco.
    rewrite <- H0.
    replace RHS with (b:Q); [ | simpl; field]; auto with *.
   apply SplitL_glue_ind; intros Hco.
     elim (Qlt_not_le _ _ Hco).
     rewrite <- H0.
     rewrite -> Hbz.
     replace RHS with (o:Q); [ | simpl; field]; auto with *.
    elim (Qlt_not_le _ _ Hco).
    rewrite <- H0.
    rewrite -> Hbz.
    replace LHS with (o:Q); [ | simpl; field]; auto with *.
   apply SplitR_resp_Qeq; simpl; auto with *.
   rewrite <- H1.
   rewrite -> Hco.
   field; auto with *.
  apply SplitL_glue_ind; intros Hco.
    elim (Qlt_not_le _ _ Hco).
    rewrite <- H0.
    apply Qlt_le_weak.
    rewrite -> Qlt_minus_iff in *.
    replace RHS with (a + - o + b*(1-a)).
     assert (Z:0 < (1-a)) by auto with *.
     Qauto_pos.
    now simpl; ring.
   assert (Hco':~ c - o == 0).
    intros H.
    elim (Qlt_not_le _ _ Hco).
    rewrite -> Qle_minus_iff.
    replace RHS with (c-o). rewrite -> H. auto with *.
     replace LHS with (-(c-o)). rewrite -> H. simpl; ring. now simpl; ring.
    apply SplitR_glue_ind; intros Hdz; simpl in Hdz.
     elim (Qlt_not_le _ _ Hdz).
     apply Qle_shift_div_r; auto with *.
     rewrite -> H1; auto with *.
    apply IHs2; simpl; [rewrite <- H0|rewrite <- H1]; field; auto with *.
   elim (Qlt_not_le _ _ Hao).
   rewrite <- H1.
   rewrite -> Hdz.
   replace LHS with (o:Q); [ | simpl; field]; auto with *.
  elim (Qlt_not_le _ _ Hao).
  rewrite <- H1.
  rewrite <- Hco.
  rewrite -> Qle_minus_iff.
  replace RHS with (c * (1-d)).
   apply Qlt_le_weak.
   assert (Z:0 < (1-d)) by auto with *.
   Qauto_pos.
  now simpl; ring.
 apply SplitL_glue_ind; intros Hco.
   elim (Qlt_not_le _ _ Hco).
   rewrite <- Hao.
   rewrite <- H1.
   rewrite -> Qle_minus_iff.
   replace RHS with (c * (1-d)).
    apply Qlt_le_weak.
    assert (Z:0 < (1-d)) by auto with *.
    Qauto_pos.
   now simpl; ring.
  apply SplitR_glue_ind; intros Hdz; simpl in Hdz.
    elim (Qlt_not_le _ _ Hdz).
    apply Qle_shift_div_r; auto with *.
    rewrite <- Hao.
    rewrite -> H1; auto with *.
   elim (Qlt_not_le _ _ Hdz).
   apply Qle_shift_div_l; auto with *.
   rewrite <- Hao.
   rewrite -> H1; auto with *.
  apply SplitL_resp_Qeq; simpl; auto with *.
  rewrite <- H0.
  rewrite <- Hao.
  field; auto with *.
 elim (Qlt_not_le (d*c) a).
  rewrite -> Hao.
  rewrite -> Hco.
  rewrite -> Qlt_minus_iff.
  replace RHS with (o * (1-d)).
   assert (Z:0 < (1-d)) by auto with *.
   Qauto_pos.
  now simpl; ring.
 rewrite -> H1.
 auto with *.
Qed.

End StepFunction.
(* begin hide *)
Add Parametric Relation X : (StepF X) (@StepF_Qeq X)
 reflexivity proved by (@StepF_Qeq_refl X)
 symmetry proved by (@StepF_Qeq_sym X)
 transitivity proved by (@StepF_Qeq_trans X)
 as StepF_Qeq_Setoid.
(* end hide *)
(** Step functions are a functor *)
Definition Map(X Y:Type):(X->Y)->(StepF X)->(StepF Y).
Proof.
 revert X Y.
 fix 4. intros X Y f [x| a t1 t2].
 exact (constStepF (f x)).
 exact (glue a (Map _ _ f t1) (Map _ _ f t2)).
Defined.

Notation "f ^@> x" := (Map f x) (at level 15, left associativity) : sfscope.

Open Local Scope sfscope.
(** Step functions are an applicative functor *)
Fixpoint Ap (X Y:Type) (f:StepF (X->Y)) (a:StepF X) : StepF Y :=
match f with
|constStepF f0 => f0 ^@> a
|glue o f0 f1 => let (l,r):=Split a o in (glue o (Ap f0 l) (Ap f1 r))
end.

Notation "f <@> x" := (Ap f x) (at level 15, left associativity) : sfscope.

Definition Map2 (X Y Z:Type) (f:(X->Y->Z)) a b :=
 f ^@> a <@> b.

Add Parametric Morphism X Y f : (@Map X Y f) with signature (@StepF_Qeq X) ==> (@StepF_Qeq Y) as Map_resp_Qeq.
Proof.
 induction x; induction y; try contradiction; intros Hs.
  simpl in *.
  rewrite Hs.
  reflexivity.
 destruct Hs as [Ho [Hl Hr]].
 repeat split; auto with *.
Qed.

(** These lemmas show how ap distributes over glue *)
Lemma ApGlue : forall X Y (fl fr:StepF (X -> Y)) o b, (glue o fl fr) <@> b = glue o (fl <@> (SplitL b o)) (fr <@> (SplitR b o)).
Proof.
 intros.
 simpl.
 apply Split_ind.
 reflexivity.
Qed.

Lemma ApGlueGlue : forall X Y (fl fr:StepF (X -> Y)) o l r, (glue o fl fr) <@> (glue o l r) = glue o (fl <@> l) (fr <@> r).
Proof.
 intros.
 rewrite ApGlue, SplitLGlue, SplitRGlue.
 reflexivity.
Qed.
(* begn hide *)
Add Parametric Morphism X Y : (@Ap X Y) with signature (@StepF_Qeq (X->Y)) ==> (@StepF_Qeq X) ==> (@StepF_Qeq Y) as Ap_resp_Qeq.
Proof.
 induction x; induction y; try contradiction; intros Hf s1 s2 Hs.
  simpl in *.
  rewrite Hf.
  apply Map_resp_Qeq.
  assumption.
 destruct Hf as [Ho [Hl Hr]].
 do 2 rewrite ApGlue.
 repeat split; auto.
  apply IHx1; auto with *.
  apply SplitL_resp_Qeq; auto with *.
 apply IHx2; auto with *.
 apply SplitR_resp_Qeq; auto with *.
Qed.
(* end hide *)
Section Ap.
(* begin hide *)
Hint Resolve StepF_Qeq_refl SplitL_resp_Qeq SplitR_resp_Qeq.
(* end hide *)
(** Splits commute with maps *)
Lemma SplitMap (X Y:Type):forall x:(StepF X), forall a, forall f:X->Y,
    (Split (Map f x) a) = let (l,r) := Split x a in (Map f l,Map f r).
Proof.
 intros s a f. revert a. induction s. simpl; auto.
 intros a.
 simpl.
 destruct (Q_dec a o) as [[H0|H0]|H0].
   rewrite IHs1. destruct (Split s1 (OpenUnitDiv a o H0)). auto with *.
   rewrite IHs2. destruct (Split s2 (OpenUnitDualDiv a o H0)). auto with *.
  auto.
Qed.

Lemma SplitLMap (X Y:Type): forall x:(StepF X), forall a, forall f:X->Y,
    SplitL (Map f x) a = Map f (SplitL x a).
Proof.
 intros. unfold SplitL. rewrite SplitMap. destruct (Split x a). simpl. auto.
Qed.

Lemma SplitRMap(X Y:Type): forall x:(StepF X), forall a, forall f:X->Y,
    SplitR (Map f x) a = Map f (SplitR x a).
Proof.
 intros. unfold SplitR. rewrite SplitMap. destruct (Split x a). simpl. auto.
Qed.

(** These lemmas show how ap distributes over split and uses mirror
properties to get the symetric cases *)
Lemma SplitLAp_Qeq (X Y:Type) : forall (f: StepF (X -> Y)) s o,
 StepF_Qeq (SplitL (f <@> s) o) ((SplitL f o) <@> (SplitL s o)).
Proof.
 induction f; intros.
  simpl.
  rewrite SplitLMap; auto with *.
 rewrite ApGlue.
 unfold SplitL at 1 3.
 simpl.
 destruct (Q_dec o0 o) as [[Ho|Ho]|Ho].
   do 2 apply Split_ind.
   simpl.
   eapply StepF_Qeq_trans; try assumption.
    apply IHf1.
   apply Ap_resp_Qeq; auto with *.
   apply SplitLSplitL.
   simpl.
   field; auto with *.
  do 2 apply Split_ind.
  simpl.
  apply Split_ind.
  repeat split; auto with *.
   apply Ap_resp_Qeq; auto with *.
   apply StepF_Qeq_sym.
   apply SplitLSplitL.
   simpl.
   field; auto with *.
  eapply StepF_Qeq_trans; try assumption.
   apply IHf2.
  apply Ap_resp_Qeq; auto with *.
  apply SplitLSplitR; simpl; field; auto with *.
 simpl.
 apply Ap_resp_Qeq; auto with *.
Qed.

Lemma MirrorMap (X Y:Type) : forall (f: X -> Y) s,
 (Mirror (Map f s)) = (Map f (Mirror s)).
Proof.
 intros f.
 induction s.
  reflexivity.
 change (Mirror (glue o (Map f s1) (Map f s2)) =
   glue (OpenUnitDual o) (Map f (Mirror s2)) (Map f (Mirror s1))).
 rewrite <- IHs1.
 rewrite <- IHs2.
 reflexivity.
Qed.

Lemma MirrorAp_Qeq (X Y: Type) : forall (f: StepF (X -> Y)) s,
 StepF_Qeq (Mirror (f <@> s)) ((Mirror f) <@> (Mirror s)).
Proof.
 induction f; intros s.
  simpl.
  rewrite MirrorMap.
  auto with *.
 rewrite ApGlue.
 change (StepF_Qeq
   (glue (OpenUnitDual o) (Mirror (f2 <@> (SplitR s o))) (Mirror (f1 <@> (SplitL s o))))
     ((glue (OpenUnitDual o) (Mirror f2) (Mirror f1)) <@> (Mirror s))).
 rewrite ApGlue.
 repeat split; auto with *.
  eapply StepF_Qeq_trans.
   apply IHf2.
  apply Ap_resp_Qeq; auto with *.
  apply MirrorSplitR_Qeq.
  reflexivity.
 eapply StepF_Qeq_trans.
  apply IHf1.
 apply Ap_resp_Qeq; auto with *.
 apply MirrorSplitL_Qeq.
 reflexivity.
Qed.

Lemma SplitRAp_Qeq (X Y:Type) : forall (f: StepF (X -> Y)) s o,
 StepF_Qeq (SplitR (f <@> s) o) ((SplitR f o) <@> (SplitR s o)).
Proof.
 intros f s o.
 eapply StepF_Qeq_trans.
  apply StepF_Qeq_sym.
  apply MirrorMirror.
 eapply StepF_Qeq_trans;[|apply MirrorMirror].
 apply Mirror_resp_Qeq.
 eapply StepF_Qeq_trans;[|apply StepF_Qeq_sym; apply MirrorAp_Qeq].
 eapply StepF_Qeq_trans.
  apply MirrorSplitR_Qeq.
  reflexivity.
 eapply StepF_Qeq_trans.
  apply SplitL_resp_Qeq.
   reflexivity.
  apply MirrorAp_Qeq.
 eapply StepF_Qeq_trans.
  apply SplitLAp_Qeq.
 apply StepF_Qeq_sym.
 apply Ap_resp_Qeq; apply MirrorSplitR_Qeq; reflexivity.
Qed.

End Ap.

Section ApplicativeFunctor.

(** These are the laws of an applicative functor *)
Lemma Ap_identity : forall X (a:StepF X), constStepF (fun x => x) <@> a = a.
Proof.
 induction a.
  reflexivity.
 simpl in *.
 rewrite IHa1.
 rewrite IHa2.
 reflexivity.
Qed.

Lemma Map_identity : forall X (a:StepF X), (fun x => x) ^@> a = a.
Proof.
 exact Ap_identity.
Qed.
(* begin hide *)
Hint Resolve Ap_resp_Qeq.
Hint Resolve SplitLAp_Qeq SplitRAp_Qeq.
Hint Resolve StepF_Qeq_refl StepF_Qeq_sym StepF_Qeq_trans SplitL_resp_Qeq SplitR_resp_Qeq.
(* end hide *)

Let compose X Y Z (x : Y ->Z) (y:X -> Y) z := x (y z).

Lemma Ap_composition_Qeq : forall X Y Z (a:StepF (Y->Z)) (b:StepF (X->Y)) (c:StepF X),
 StepF_Qeq (constStepF (@compose X Y Z) <@> a <@> b <@> c) (a <@> (b <@> c)).
Proof.
 induction a.
  simpl.
  induction b.
   simpl.
   induction c.
    auto.
   repeat split; auto.
  intros c.
  simpl in *.
  destruct (Split c o).
  repeat split; auto.
 intros b c.
 simpl in *.
 do 2 apply Split_ind.
 simpl.
 apply Split_ind.
 repeat split; eauto.
Qed.

Lemma Map_composition_Qeq : forall X Y Z (a:StepF (Y->Z)) (b:StepF (X->Y)) (c:StepF X),
 StepF_Qeq ((fun x y z => x (y z)) ^@> a <@> b <@> c) (a <@> (b <@> c)).
Proof.
 exact Ap_composition_Qeq.
Qed.

Lemma Ap_homomorphism : forall X Y (f:X->Y) (a:X),
 (constStepF f <@> constStepF a) = (constStepF (f a)).
Proof.
 reflexivity.
Qed.

Lemma Map_homomorphism : forall X Y (f:X->Y) (a:X),
 (f ^@> constStepF a) = (constStepF (f a)).
Proof.
 exact Ap_homomorphism.
Qed.

Lemma Ap_interchange : forall X Y (f:StepF (X->Y)) (a:X),
 (f <@> constStepF a) = (constStepF (fun g => g a)) <@> f.
Proof.
 induction f.
  reflexivity.
 intros a.
 simpl.
 rewrite IHf1.
 rewrite IHf2.
 reflexivity.
Qed.

Lemma Map_interchange : forall X Y (f:StepF (X->Y)) (a:X),
 (f <@> constStepF a) = (fun g => g a) ^@> f.
Proof.
 exact Ap_interchange.
Qed.

Lemma Map_compose_Map : forall X Y Z (f:Y->Z) (g:X -> Y) a,
 ((fun a => f (g a)) ^@> a) = (f ^@> (g ^@> a)).
Proof.
 induction a; simpl; congruence.
Qed.

End ApplicativeFunctor.
