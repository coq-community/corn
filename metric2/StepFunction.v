Require Export Metric.
Require Import OpenUnit.
Require Import CornTac.
Require Import Qauto.
Require Import Qordfield.
Require Import COrdFields.

Set Implicit Arguments.

Section StepFunction.

Variable X:Type.

Inductive StepF :Type:=
|leaf:X-> StepF
|glue:OpenUnit-> StepF -> StepF -> StepF.

Fixpoint StepFfold (Y : Type) (f : X -> Y) (g : OpenUnit -> Y -> Y -> Y)
              (s : StepF) {struct s} : Y :=
  match s with
  | leaf x => f x
  | glue b t1 t2 => g b (StepFfold f g t1) (StepFfold f g t2)
  end.

Definition Mirror :StepF -> StepF :=
StepFfold leaf (fun a l r => glue (OpenUnitDual a) r l).

Definition Split : StepF -> OpenUnit -> StepF*StepF.
fix 1.
intros s a.
destruct s as [x | b t1 t2].
 exact (leaf x , leaf x).

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
destruct (Q_dec a b) as [[Hab|Hab]|Hab]; 
 try apply Split_ind; simpl; auto with *.
Qed.

Lemma SplitL_glue_ind : forall s1 s2 (a b:OpenUnit) (P:StepF -> Prop),
 (forall (H:a < b), P (SplitL s1 (OpenUnitDiv a b H))) ->
 (forall (H:b < a), P (glue (OpenUnitDiv b a H) s1 (SplitL s2 (OpenUnitDualDiv a b H)))) ->
 (a == b -> P (s1)) ->
 P (SplitL (glue b s1 s2) a).
Proof.
intros.
apply (SplitLR_glue_ind s1 s2 a b (fun a b => P a));
assumption.
Qed.

Lemma SplitR_glue_ind : forall s1 s2 (a b:OpenUnit) (P:StepF -> Prop),
 (forall (H:a < b), P (glue (OpenUnitDualDiv b a H) (SplitR s1 (OpenUnitDiv a b H)) s2)) ->
 (forall (H:b < a), P (SplitR s2 (OpenUnitDualDiv a b H))) ->
 (a == b -> P (s2)) ->
 P (SplitR (glue b s1 s2) a).
Proof.
intros.
apply (SplitLR_glue_ind s1 s2 a b (fun a b => P b));
assumption.
Qed.

Lemma SplitGlue : forall x y:StepF, forall o,
  (Split (glue o x y) o)=(x,  y).
intros. simpl.
 destruct (Q_dec o o) as [[H1|H1]|H1]; try (elim (Qlt_not_le _ _ H1); auto with *); simpl; auto with *.
Qed.

Lemma SplitLGlue : forall x y:StepF, forall o,
  (SplitL (glue o x y) o)=x.
unfold SplitL.
intros.
rewrite SplitGlue.
reflexivity.
Qed.

Lemma SplitRGlue : forall x y:StepF, forall o,
  (SplitR (glue o x y) o)=y.
unfold SplitR.
intros.
rewrite SplitGlue.
reflexivity.
Qed.

Fixpoint StepF_Qeq (s1 s2: StepF) : Prop :=
match s1, s2 with
|leaf x, leaf y => x = y
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

Hint Resolve StepF_Qeq_refl StepF_Qeq_sym StepF_Qeq_trans.

Lemma Mirror_resp_Qeq : forall (s t:StepF), StepF_Qeq s t -> StepF_Qeq (Mirror s) (Mirror t).
Proof.
induction s; induction t; intros Hst; simpl in *; try assumption; try contradiction.
destruct Hst as [Ho [Hst1 Hst2]].
repeat split.
  rewrite Ho; reflexivity.
 apply IHs2; assumption.
apply IHs1; assumption.
Qed.

Hint Resolve Mirror_resp_Qeq.

Lemma MirrorMirror : forall (s:StepF), (StepF_Qeq (Mirror (Mirror s)) s).
Proof.
induction s.
 simpl; reflexivity.
repeat split; auto with *.
simpl; ring.
Qed.   

Hint Resolve MirrorMirror.

Lemma SplitR_resp_Qeq : forall (s t:StepF) (a b:OpenUnit), a == b -> StepF_Qeq s t -> StepF_Qeq (SplitR s a) (SplitR t b).
Proof.
induction s; induction t; intros a b Hab Hst; simpl in *; try assumption; try contradiction.
destruct Hst as [Ho [Hst1 Hst2]].
apply SplitR_glue_ind; intros Hao; apply SplitR_glue_ind; intros Hbo; repeat split; auto with *;
 try solve [elim (Qlt_not_le _ _ Hao); rewrite Hab; rewrite Ho; try rewrite Hbo; auto with *
           |elim (Qlt_not_le _ _ Hbo); rewrite <- Hab; rewrite <- Ho; try rewrite Hao; auto with *];
 try apply IHs1; try apply IHs2; auto with *; simpl; try (rewrite Hab; rewrite Ho; reflexivity).
Qed.

Hint Resolve SplitR_resp_Qeq.

Lemma MirrorSplitL_Qeq : forall (s:StepF) (a b:OpenUnit), b == (OpenUnitDual a) -> (StepF_Qeq (Mirror (SplitL s a)) (SplitR (Mirror s) b)).
Proof.
induction s.
 auto with *.
intros a b Hab; simpl in Hab.
simpl.
apply SplitL_glue_ind; intros Hao; rapply SplitR_glue_ind; intros Hoa; simpl in Hoa;
 try (repeat split; auto with *; try apply IHs1; try apply IHs2; simpl; rewrite Hab; field; auto with *).
      elim (Qlt_not_le _ _ Hao).
      rewrite Qlt_minus_iff in Hoa.
      rewrite Qle_minus_iff.
      replace RHS with (1 - o + - (1 - a)) by ring.
      rewrite <- Hab.
      auto with *.
     elim (Qlt_not_le _ _ Hao).
     rewrite Qle_minus_iff.
     replace RHS with (1 - o + - (1 - a)) by ring.
     rewrite <- Hab.
     rewrite <- Hoa.
     ring_simplify.
     auto with *.
    intros H; ring_simplify in H.
    revert H; change (~(a==0)); auto with *.
   elim (Qlt_not_le _ _ Hao).
   rewrite Qle_minus_iff.
   rewrite Qlt_minus_iff in Hoa.
   replace RHS with (1 - a + - (1 - o)) by ring.
   rewrite <- Hab.
   auto with *.
  elim (Qlt_not_le _ _ Hao).
  rewrite Qle_minus_iff.
  replace RHS with (1 - a + - (1 - o)) by ring.
  rewrite <- Hab.
  rewrite <- Hoa.
  ring_simplify.
  auto with *.
 elim (Qlt_not_le _ _ Hoa).
 rewrite Hab.
 rewrite Hao.
 auto with *.
elim (Qlt_not_le _ _ Hoa).
rewrite Hab.
rewrite Hao.
auto with *.
Qed.

Lemma MirrorSplitR_Qeq: forall (s:StepF) (a b:OpenUnit), b == (OpenUnitDual a) -> (StepF_Qeq (Mirror (SplitR s a)) (SplitL (Mirror s) b)).
Proof.
intros s a b H.
apply StepF_Qeq_trans with (Mirror (SplitR (Mirror (Mirror s)) a));
 auto with *.
apply StepF_Qeq_trans with (Mirror (Mirror (SplitL (Mirror s) b)));
 auto with *.
apply Mirror_resp_Qeq.
apply StepF_Qeq_sym.
apply MirrorSplitL_Qeq.
simpl in *.
rewrite H.
ring.
Qed.

Lemma SplitL_resp_Qeq : forall (s t:StepF) (a b:OpenUnit), a == b -> StepF_Qeq s t -> StepF_Qeq (SplitL s a) (SplitL t b).
Proof.
intros s t a b H H0.
apply StepF_Qeq_trans with (Mirror (Mirror (SplitL s a)));
 auto with *.
apply StepF_Qeq_trans with (Mirror (SplitR (Mirror s) (OpenUnitDual a))).
 apply Mirror_resp_Qeq.
 apply MirrorSplitL_Qeq; auto with *.
apply StepF_Qeq_trans with (Mirror (SplitR (Mirror t) (OpenUnitDual b))).
 apply Mirror_resp_Qeq.
 apply SplitR_resp_Qeq; auto with *.
 simpl; rewrite H; reflexivity.
apply StepF_Qeq_trans with (Mirror (Mirror (SplitL t b)));
 auto with *.
apply Mirror_resp_Qeq.
apply StepF_Qeq_sym.
apply MirrorSplitL_Qeq; auto with *.
Qed.

Hint Resolve SplitL_resp_Qeq.

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
   replace RHS with (1*a) by ring.
   replace LHS with (b*a) by ring.
   apply Qmult_le_compat_r; auto with *.
  elim (Qlt_not_le a c).
   rewrite Hco.
   apply Qlt_le_trans with o; auto with *.
  rewrite <- H.
  replace RHS with (1*a) by ring.
  replace LHS with (b*a) by ring.
  apply Qmult_le_compat_r; auto with *.
 apply SplitL_glue_ind; intros Hbd.
   apply SplitL_glue_ind; intros Hco.
     apply SplitL_resp_Qeq; auto with *.
     simpl.
     rewrite <- H.
     field; auto with *.
    elim (Qlt_not_le _ _ Hbd).
    simpl.
    apply Qle_shift_div_r; auto with *.
    rewrite Qmult_comm; rewrite  H; auto with *.
   elim (Qlt_not_le _ _ Hbd).
   simpl.
   apply Qle_shift_div_r; auto with *.
   rewrite Qmult_comm; rewrite H; rewrite Hco; auto with *.
  apply SplitL_glue_ind; intros Hco.
    elim (Qlt_not_le _ _ Hbd).
    simpl.
    apply Qle_shift_div_l; auto with *.
    rewrite Qmult_comm; rewrite  H; auto with *.
   repeat split; auto with *.
    simpl.
    rewrite <- H.
    field; auto with *.
   apply IHs2.
   simpl.
   rewrite <- H.
   field; repeat split; auto with *.
   clear - Hao; rewrite Qlt_minus_iff in Hao.
   auto with *.
  elim (Qlt_not_le _ _ Hbd).
  simpl.
  apply Qle_shift_div_l; auto with *.
  rewrite Qmult_comm; rewrite H; auto with *.
 assert (Y:o==c).
  rewrite <- H.
  rewrite Hbd.
  simpl.
  field.
  auto with *.
 apply SplitL_glue_ind; intros Hco;
  try (elim (Qlt_not_le _ _ Hco); rewrite Y; auto with *).
 auto with *.
apply SplitL_glue_ind; intros Hco.
  apply SplitL_resp_Qeq; auto with *.
  simpl.
  rewrite <- H.
  rewrite Hao.
  field; auto with *.
 elim (Qlt_not_le _ _ Hco).
 rewrite <- H.
 rewrite <- Hao.
 replace RHS with (1*a) by ring.
 replace LHS with (b*a) by ring.
 apply Qmult_le_compat_r; auto with *.
elim (Qlt_not_le b 1).
 auto with *.
rewrite <- Hao in Hco.
rewrite Hco in H.
apply Qmult_lt_0_le_reg_r with a.
 auto with *.
ring_simplify.
rewrite H.
auto with *.
Qed.

Lemma SplitRSplitR : forall (s:StepF) (a b c:OpenUnit), (a+b-a*b==c) -> 
 (StepF_Qeq (SplitR (SplitR s a) b) (SplitR s c)).
Proof.
intros s a b c H.
apply StepF_Qeq_trans with (Mirror (Mirror (SplitR (SplitR s a) b)));
 auto with *.
apply StepF_Qeq_trans with (Mirror (Mirror (SplitR s c)));
 auto with *.
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
   rewrite Qle_minus_iff.
   replace RHS with (- (o- a)) by ring.
   rewrite H.
   auto with *.
  apply SplitL_glue_ind; intros Hbz; simpl in Hbz.
    apply SplitL_glue_ind; intros Hco.
      apply IHs1; simpl; [rewrite <- H0|rewrite <- H1]; field; auto with *.
     elim (Qlt_not_le _ _ Hbz).
     rewrite Qlt_minus_iff in Hco.
     rewrite Qle_minus_iff.
     replace RHS with ((a + b - a*b + -o)/(1 -a)) by (field; auto with *).
     rewrite H0.
     apply Qle_shift_div_l; auto with *.
     replace LHS with 0 by ring.
     auto with *.
    elim (Qlt_not_le _ _ Hbz).
    rewrite Qle_minus_iff.
    replace RHS with ((a + b - a*b + -o)/(1 -a)) by (field; auto with *).
    rewrite H0.
    rewrite Hco.
    replace RHS with 0 by (field; auto with *).
    auto with *.
   apply SplitL_glue_ind; intros Hco.
     elim (Qlt_not_le _ _ Hbz).
     rewrite Qlt_minus_iff in Hco.
     rewrite Qle_minus_iff.
     replace RHS with ((o + -(a + b - a*b))/(1 -a)) by (field; auto with *).
     rewrite H0.
     apply Qle_shift_div_l; auto with *.
     replace LHS with 0 by ring.
     auto with *.
    apply SplitR_glue_ind; intros Hdz; simpl in Hdz.
      repeat split; simpl.
        field_simplify; auto with *.
        rapply Qmult_simpl.
         rewrite <- H1; ring.
        apply Qinv_comp.
        replace LHS with (a + b - a*b - a) by ring.
        rewrite H0.
        replace RHS with (c - (d*c)) by ring.
        rewrite H1.
        reflexivity.
       apply SplitR_resp_Qeq; auto with *; simpl.
       rewrite <- H1; field; auto with *.
      apply SplitL_resp_Qeq; auto with *; simpl.
      rewrite <- H0; field; auto with *.
     elim (Qlt_not_le _ _ Hdz).
     apply Qle_shift_div_l; auto with *.
     rewrite H1; auto with *.
    elim (Qlt_not_le _ _ Hao).
    rewrite <- H1.
    rewrite Hdz.
    replace RHS with (o:Q) by (field; auto with *).
    auto with *.
   elim (Qlt_not_le _ _ Hbz).
   rewrite <- Hco.
   rewrite <- H0.
   replace RHS with (b:Q) by (field; auto with *).
   auto with *.
  apply SplitL_glue_ind; intros Hco.
    elim (Qlt_not_le _ _ Hco).
    rewrite <- H0.
    rewrite Hbz.
    replace RHS with (o:Q) by (field; auto with *).
    auto with *.
   elim (Qlt_not_le _ _ Hco).
   rewrite <- H0.
   rewrite Hbz.
   replace LHS with (o:Q) by (field; auto with *).
   auto with *.
  apply SplitR_resp_Qeq; simpl; auto with *.
  rewrite <- H1.
  rewrite Hco.
  field; auto with *.
 apply SplitL_glue_ind; intros Hco.
   elim (Qlt_not_le _ _ Hco).
   rewrite <- H0.
   apply Qlt_le_weak.
   rewrite Qlt_minus_iff in *.
   replace RHS with (a + - o + b*(1-a)) by ring.
   assert (Z:0 < (1-a)) by auto with *.
   Qauto_pos.
  assert (Hco':~ c - o == 0).
   intros H.
   elim (Qlt_not_le _ _ Hco).
   rewrite Qle_minus_iff.
   replace RHS with (- (c- o)) by ring.
   rewrite H.
   auto with *.
  apply SplitR_glue_ind; intros Hdz; simpl in Hdz.
    elim (Qlt_not_le _ _ Hdz).
    apply Qle_shift_div_r; auto with *.
    rewrite H1; auto with *.
   apply IHs2; simpl; [rewrite <- H0|rewrite <- H1]; field; auto with *.
  elim (Qlt_not_le _ _ Hao).
  rewrite <- H1.
  rewrite Hdz.
  replace LHS with (o:Q) by (field; auto with *).
  auto with *.
 elim (Qlt_not_le _ _ Hao).
 rewrite <- H1.
 rewrite <- Hco.
 rewrite Qle_minus_iff.
 replace RHS with (c * (1-d)) by ring.
 apply Qlt_le_weak.
 assert (Z:0 < (1-d)) by auto with *.
 Qauto_pos.
apply SplitL_glue_ind; intros Hco.
  elim (Qlt_not_le _ _ Hco).
  rewrite <- Hao.
  rewrite <- H1.
  rewrite Qle_minus_iff.
  replace RHS with (c * (1-d)) by ring.
  apply Qlt_le_weak.
  assert (Z:0 < (1-d)) by auto with *.
  Qauto_pos.
 apply SplitR_glue_ind; intros Hdz; simpl in Hdz.
   elim (Qlt_not_le _ _ Hdz).
   apply Qle_shift_div_r; auto with *.
   rewrite <- Hao.
   rewrite H1; auto with *.
  elim (Qlt_not_le _ _ Hdz).
  apply Qle_shift_div_l; auto with *.
  rewrite <- Hao.
  rewrite H1; auto with *.
 apply SplitL_resp_Qeq; simpl; auto with *.
 rewrite <- H0.
 rewrite <- Hao.
 field; auto with *.
elim (Qlt_not_le (d*c) a).
 rewrite Hao.
 rewrite Hco.
 rewrite Qlt_minus_iff.
 replace RHS with (o * (1-d)) by ring.
 assert (Z:0 < (1-d)) by auto with *.
 Qauto_pos.
rewrite H1.
auto with *.
Qed.

End StepFunction.

Add Relation StepF StepF_Qeq 
 reflexivity proved by StepF_Qeq_refl
 symmetry proved by StepF_Qeq_sym
 transitivity proved by StepF_Qeq_trans
 as StepF_Qeq_Setoid.

Definition Map(X Y:Type):(X->Y)->(StepF X)->(StepF Y).
fix 4. intros X Y f [x| a t1 t2].
 exact (leaf (f x)).
exact (glue a (Map _ _ f t1) (Map _ _ f t2)).
Defined.

Notation "f ^@> x" := (Map f x) (at level 15, left associativity) : sfscope.

Open Local Scope sfscope.

Fixpoint Ap (X Y:Type) (f:StepF (X->Y)) (a:StepF X) : StepF Y :=
match f with
|leaf f0 => f0 ^@> a
|glue o f0 f1 => let (l,r):=Split a o in (glue o (Ap f0 l) (Ap f1 r))
end.

Notation "f <@> x" := (Ap f x) (at level 15, left associativity) : sfscope.

Definition Map2 (X Y Z:Type) (f:(X->Y->Z)) a b :=
 f ^@> a <@> b.

Add Morphism Map with signature StepF_Qeq ==> StepF_Qeq as Map_resp_Qeq.
Proof. 
intros X Y f.
induction x1; induction x2; try contradiction; intros Hs.
 simpl in *.
 rewrite Hs.
 reflexivity.
destruct Hs as [Ho [Hl Hr]].
repeat split; auto with *.
Qed.

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

Add Morphism Ap with signature StepF_Qeq ==> StepF_Qeq ==> StepF_Qeq as Ap_resp_Qeq.
Proof.
intros X Y.
induction x1; induction x2; try contradiction; intros Hf s1 s2 Hs.
 simpl in *.
 rewrite Hf.
 apply Map_resp_Qeq.
 assumption.
destruct Hf as [Ho [Hl Hr]].
do 2 rewrite ApGlue.
repeat split; auto.
 apply IHx1_1; auto with *.
 apply SplitL_resp_Qeq; auto with *.
apply IHx1_2; auto with *.
apply SplitR_resp_Qeq; auto with *.
Qed.

Section Ap.

Hint Resolve StepF_Qeq_refl SplitL_resp_Qeq SplitR_resp_Qeq.

Lemma SplitMap (X Y:Type):forall x:(StepF X), forall a, forall f:X->Y, 
    (Split (Map f x) a) = let (l,r) := Split x a in (Map f l,Map f r).
intros X Y s a f. revert a. induction s. simpl; auto.
intros a.
simpl.
destruct (Q_dec a o) as [[H0|H0]|H0].
rewrite IHs1. destruct (Split s1 (OpenUnitDiv a o H0)). auto with *. 
rewrite IHs2. destruct (Split s2 (OpenUnitDualDiv a o H0)). auto with *. 
auto.
Qed.

Lemma SplitLMap (X Y:Type): forall x:(StepF X), forall a, forall f:X->Y, 
    SplitL (Map f x) a = Map f (SplitL x a).
intros. unfold SplitL. rewrite SplitMap. destruct (Split x a). simpl. auto.
Qed.

Lemma SplitRMap(X Y:Type): forall x:(StepF X), forall a, forall f:X->Y, 
    SplitR (Map f x) a = Map f (SplitR x a).
intros. unfold SplitR. rewrite SplitMap. destruct (Split x a). simpl. auto.
Qed.

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
intros X Y f.
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
intros X Y.
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
intros X Y f s o.
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
apply Ap_resp_Qeq;
 apply MirrorSplitR_Qeq; reflexivity.
Qed.

End Ap.

Section ApplicativeFunctor.

Lemma Ap_identity : forall X (a:StepF X), leaf (fun x => x) <@> a = a.
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

Hint Resolve Ap_resp_Qeq.
Hint Resolve SplitLAp_Qeq SplitRAp_Qeq.
Hint Resolve StepF_Qeq_refl StepF_Qeq_sym StepF_Qeq_trans SplitL_resp_Qeq SplitR_resp_Qeq.

Definition compose X Y Z (x : Y ->Z) (y:X -> Y) z := x (y z).

Lemma Ap_composition_Qeq : forall X Y Z (a:StepF (Y->Z)) (b:StepF (X->Y)) (c:StepF X),
 StepF_Qeq (leaf (@compose X Y Z) <@> a <@> b <@> c) (a <@> (b <@> c)).
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
 (leaf f <@> leaf a) = (leaf (f a)).
Proof.
reflexivity.
Qed.

Lemma Map_homomorphism : forall X Y (f:X->Y) (a:X),
 (f ^@> leaf a) = (leaf (f a)).
Proof.
exact Ap_homomorphism.
Qed.

Lemma Ap_interchange : forall X Y (f:StepF (X->Y)) (a:X),
 (f <@> leaf a) = (leaf (fun g => g a)) <@> f.
Proof.
induction f.
 reflexivity.
intros a.
simpl.
rewrite IHf1.
rewrite IHf2.
reflexivity.
Qed.

End ApplicativeFunctor.

Lemma MapMap2 (X Y Z W:Type): forall (f:Z->W) (g:X->Y->Z) (x:StepF X) (y:StepF Y), 
  StepF_Qeq (f ^@> (g ^@> x <@> y)) ((fun x y => (f (g x y))) ^@> x <@> y).
Proof.
intros.
change ((fun (x0 : X) (y0 : Y) => f (g x0 y0)) ^@> x)
 with (leaf (compose (compose f) g) <@> x).
rewrite <- (Ap_homomorphism (compose (compose f)) g).
rewrite <- (Ap_homomorphism (@compose X _ _) (@compose Y _ _ f)).
(*Setoid rewrite bug *)
set (A:= (f ^@> (g ^@> x <@> y))).
rewrite Ap_composition_Qeq.
rewrite <- (Ap_homomorphism (@compose Y _ _) f).
rewrite Ap_composition_Qeq.
apply StepF_Qeq_refl.
Qed.

(*
Lemma Map2Map2Map2 (X Y Z W:Type): 
  forall (f:Z->Z->W) (g:X->Y->Z) (h:X->Y->Z) 
          (x:StepF X) (y:StepF Y), 
  (StepF_Qeq (f ^@> (g ^@> x <@> y) <@> (h ^@> x <@> y))
   ((fun x y => (f (g x y) (h x y))) ^@> x <@> y)).
Proof.
intros.
change ((fun (x0 : X) (y0 : Y) => f (g x0 y0) (h x0 y0)) ^@> x <@> y)
 with (

induction x. simpl. induction y.
  simpl; auto with *.
 Opaque Map2.
 simpl.
 Transparent Map2.
 rewrite <-IHy1. rewrite <-IHy2.
 rewrite Map2GlueGlue.
 reflexivity.
intro y. rewrite (Map2Glue (fun (x : X) (y0 : Y) => f (g x y0) (h x y0))).
rewrite <- IHx1. rewrite <- IHx2.
rewrite (Map2Glue g).
rewrite (Map2Glue h).
apply Map2GlueGlue.
Qed.
*)

Section EquivalenceA.
Variable X:Type.
Variable Xeq:X->X->Prop.
Hypothesis Xst:(Setoid_Theory X Xeq).

Add Setoid X Xeq Xst as Xsetoid.
Hint Resolve (Seq_trans X Xeq Xst) (Seq_sym X Xeq Xst) (Seq_refl X Xeq Xst):foo.

Definition StepFfoldProp:=StepFfold (fun x => x ) (fun _ a b => a /\ b ).

Definition StepF_eq (f g:StepF X):Prop:=
(StepFfoldProp (Map2 Xeq f g)).

Hint Unfold StepFfoldProp StepFfold StepF_eq.

Notation "x === y" := (StepF_eq x y) (at level 70).

Lemma glue_StepF_eq:forall s s1 s2, forall a, s1 === (SplitL s a) -> s2 === (SplitR s a) -> (glue a s1 s2) === s.
intros s s1 s2 a H0 H1.
unfold StepF_eq, Map2.
change (StepFfoldProp (glue a (Xeq ^@> s1) (Xeq ^@> s2) <@> s)).
rewrite ApGlue.
split; assumption.
Qed.

Lemma glue_eq_ind : forall s1 s2 s a (P:Prop), (s1 === (SplitL s a) -> s2 === (SplitR s a) -> P) -> (glue a s1 s2 === s) -> P.
Proof.
intros s1 s2 s a P H H0.
unfold SplitL, SplitR, StepF_eq, Map2 in *.
simpl in *.
destruct (Split s a).
destruct H0.
auto.
Qed.

Lemma StepF_eq_refl:forall x : StepF X, x === x.
intro s.
induction s.
compute. apply Seq_refl; auto.
apply glue_StepF_eq.
rewrite SplitLGlue; assumption.
rewrite SplitRGlue; assumption.
Qed.

Hint Resolve StepF_eq_refl.

Lemma glueSplit:forall s, forall a, (glue a (SplitL s a) (SplitR s a)) === s.
intros s a.
apply glue_StepF_eq; auto with *.
Qed.

Lemma StepF_Qeq_eq : forall s t, (StepF_Qeq s t) -> s === t.
Proof.
induction s; induction t; try contradiction; simpl.
 intros H.
 rewrite H.
 auto with *.
intros [H [H0 H1]].
apply glue_StepF_eq.
 apply IHs1.
 apply SplitL_glue_ind; intros H2;
  try (elim (Qlt_not_le _ _ H2); rewrite H); auto with *.
apply IHs2.
apply SplitR_glue_ind; intros H2;
 try (elim (Qlt_not_le _ _ H2); rewrite H); auto with *.
Qed.

End EquivalenceA.

Hint Resolve StepF_eq_refl StepF_Qeq_eq : sfarith.
Hint Unfold StepFfoldProp StepFfold StepF_eq : sfarith.

Section EquivalenceB.
Variable X:Type.
Variable Xeq:X->X->Prop.

Variable Y:Type.
Variable Yeq:Y->Y->Prop.
Hypothesis Yst:(Setoid_Theory Y Yeq).

Lemma Map_resp_StepF_eq: forall f:X->Y, 
    (forall x y, (Xeq x y)-> (Yeq (f x) (f y))) ->
    forall s t:(StepF X), (StepF_eq Xeq s t) -> (StepF_eq Yeq (Map f s) (Map f t)).
intros f H.
induction s. induction t.
  unfold StepF_eq, Map2;simpl;auto with *. 
 unfold StepF_eq, Map2. unfold StepFfoldProp. simpl;  intuition.
simpl. intros t H0.
unfold StepF_eq, Map2 in H0. simpl in H0.
unfold StepF_eq, Map2. simpl.
rewrite SplitMap. destruct ( Split t o) as [L R].
destruct H0 as [H1 H2]. split. fold StepFfoldProp. apply IHs1. apply H1.
apply IHs2. apply H2.
Qed.

End EquivalenceB.

Lemma StepFfoldPropglue:forall y o,
 StepFfoldProp (glue o (SplitL y o) (SplitR y o)) <-> StepFfoldProp y.
induction y.
  unfold StepF_eq, StepFfoldProp.
  simpl; tauto.
simpl.
intro o0.
apply SplitLR_glue_ind; intros H.
  generalize (IHy1 (OpenUnitDiv o0 o H)).
  unfold StepFfoldProp; simpl; tauto.
 generalize (IHy2 (OpenUnitDualDiv o0 o H)).
 unfold StepFfoldProp; simpl; tauto.
simpl.
reflexivity.
Qed.

Lemma StepFfoldProp_morphism:forall x y:(StepF Prop),
  (StepF_eq iff x y) ->
  ((StepFfoldProp x)<->(StepFfoldProp y)).
induction x. induction y.
   auto with *.
  unfold StepF_eq. simpl. unfold StepFfoldProp;simpl;intuition.
intros y H0.
unfold StepF_eq, Map2 in H0. simpl in H0.
destruct (Split y o) using (Split_ind y o).
destruct H0 as [H0l H0r].
change ((StepFfoldProp x1 /\ StepFfoldProp x2) <-> StepFfoldProp y).
rewrite (IHx1 (SplitL y o)); auto with *.
rewrite (IHx2 (SplitR y o)); auto with *.
rapply StepFfoldPropglue.
Qed.

Section EquivalenceC.
Variable X:Type.
Variable Xeq:X->X->Prop.
Hypothesis Xst:(Setoid_Theory X Xeq).
Add Setoid X Xeq Xst as Xth1.

Notation "x === y" := (StepF_eq Xeq x y) (at level 70).

Hint Resolve StepF_Qeq_refl SplitL_resp_Qeq SplitR_resp_Qeq.

Lemma StepF_eq_resp_Qeq : forall s t u v, (StepF_Qeq s t) -> (StepF_Qeq u v) -> s === u -> t === v.
Proof.
induction s; induction t; try contradiction.
 intros u v Hst Huv Hsu.
 simpl in Hst.
 unfold StepF_eq, Map2 in *.
 simpl in *.
 rewrite <- Hst.
 rewrite <- (StepFfoldProp_morphism (Map (Xeq x) u)); auto with *.
 apply (Map_resp_StepF_eq Xeq); auto with *.
  split;[apply iff_refl|apply iff_sym|apply iff_trans].
 intros a b Hab.
 rewrite Hab.
 reflexivity.
intros u v [H [Hst0 Hst1]] Huv Hsu.
destruct Hsu as [Hsu1 Hsu2] using (glue_eq_ind Xeq).
apply glue_StepF_eq.
 eapply IHs1.
   assumption.
  apply SplitL_resp_Qeq.
   apply H.
  apply Huv.
 assumption.
eapply IHs2.
  assumption.
 apply SplitR_resp_Qeq.
  apply H.
 apply Huv.
assumption.
Qed.

Lemma Mirror_eq_Mirror : forall s t, Mirror s === Mirror t <-> s === t.
Proof.
induction s.
 induction t; simpl.
  reflexivity.
 simpl in *.
 change (leaf x === (Mirror t2) /\ leaf x === (Mirror t1) <-> leaf x === t1 /\ leaf x === t2).
 tauto.
intros t.
unfold Mirror.
simpl.
fold (Mirror s1); fold (Mirror s2).
fold (Mirror t).
split; apply glue_eq_ind; intros H0 H1.
 apply glue_StepF_eq.
  rewrite <- IHs1.
  eapply StepF_eq_resp_Qeq;[| |apply H1]; auto with *.
  apply StepF_Qeq_sym.
  apply MirrorSplitL_Qeq; auto with *.
 rewrite <- IHs2.
 eapply StepF_eq_resp_Qeq;[| |apply H0]; auto with *.
 apply StepF_Qeq_sym.
 apply MirrorSplitR_Qeq; auto with *.
apply glue_StepF_eq.
 eapply StepF_eq_resp_Qeq;[apply StepF_Qeq_refl|apply MirrorSplitR_Qeq; apply Qeq_refl|].
 rewrite IHs2.
 assumption.
eapply StepF_eq_resp_Qeq;[apply StepF_Qeq_refl|apply MirrorSplitL_Qeq; apply Qeq_refl|].
rewrite IHs1.
assumption.
Qed.

Lemma StepFfoldPropSplitL : 
 forall (s : StepF Prop) a, StepFfoldProp s -> StepFfoldProp (SplitL s a).
Proof.
induction s; intros a H.
 assumption.
destruct H.
apply SplitL_glue_ind; intros Hao.
  apply IHs1; assumption.
 split.
  assumption.
 apply IHs2.
 assumption.
assumption.
Qed.

Lemma SplitL_resp_Xeq : forall s1 s2 a, s1 === s2 -> SplitL s1 a === SplitL s2 a.
Proof.
induction s1.
 intros s2 a H.
 unfold SplitL at 1.
 simpl.
 unfold StepF_eq, Map2 in *.
 simpl in *.
 rewrite <- SplitLMap.
 apply StepFfoldPropSplitL.
 assumption.
intros s2 a H.
destruct H using (glue_eq_ind Xeq).
apply SplitL_glue_ind; intros Hao.
  eapply StepF_eq_resp_Qeq;[| |apply IHs1_1;apply H].
   apply StepF_Qeq_refl.
  apply SplitLSplitL.
  simpl; field; auto with *.
 apply glue_StepF_eq.
  eapply StepF_eq_resp_Qeq;[| |apply H]; auto with *.
  apply StepF_Qeq_sym.
  apply SplitLSplitL.
  simpl; field; auto with *.
 eapply StepF_eq_resp_Qeq;[| |apply IHs1_2; apply H0]; auto with *.
 apply SplitLSplitR; simpl; field; auto with *.
eapply StepF_eq_resp_Qeq;[| |apply H]; auto with *.
Qed.

Lemma SplitR_resp_Xeq : forall s1 s2 a, s1 === s2 -> SplitR s1 a === SplitR s2 a.
Proof.
intros s1 s2 a H.
eapply StepF_eq_resp_Qeq; try (eapply StepF_Qeq_trans;[apply Mirror_resp_Qeq; apply StepF_Qeq_sym; apply MirrorSplitR_Qeq; reflexivity|apply MirrorMirror]).
rewrite  Mirror_eq_Mirror.
apply SplitL_resp_Xeq.
rewrite Mirror_eq_Mirror.
assumption.
Qed.

(*
Lemma Map2_morphism2:forall f, (forall x x' y y',
  (Xeq x x) -> (Yeq y y')-> (Zeq (f x y) (f x' y'))) ->
  forall s t t', (StepF_eq Yeq t t') ->
  (StepF_eq Zeq (Map2 f s t) (Map2 f s t')).
intros f H.
induction s.
 intros t t' H0.
 simpl.
 eapply Map_resp_StepF_eq;try apply Yst; auto with *.
 intros a b Hab.
 rewrite Hab.
intros t t' H0.
simpl.
apply Split_ind.
apply Split_ind.
simpl.
apply glue_StepF_eq.
 apply SplitL_glue_ind; intros H1; try (elim (Qlt_not_le _ _ H1); auto with * ).
 apply IHs1.
 apply SplitL_resp_Xeq; auto with *.
apply SplitR_glue_ind; intros H1; try (elim (Qlt_not_le _ _ H1); auto with * ).
apply IHs2.
apply SplitR_resp_Xeq; auto with *.
Qed.*)

Lemma StepF_eq_trans:forall x y z : StepF X, x === y -> y === z -> x === z.
induction x. intros.
 unfold StepF_eq, Map2;simpl;auto with *.
  cut (StepFfoldProp (Map (Xeq x) y)); try auto.
 intros H1.
 rewrite <- (StepFfoldProp_morphism (Map (Xeq x) y)); auto with *.
 eapply (Map_resp_StepF_eq Xeq); auto with *.
  split;[apply iff_refl|apply iff_sym|apply iff_trans].
 intros a b Hab.
 rewrite Hab.
 reflexivity.
intros.
destruct H using (glue_eq_ind Xeq).
apply glue_StepF_eq.
 eapply IHx1.
  apply H.
 apply SplitL_resp_Xeq.
 assumption.
eapply IHx2.
 apply H1.
apply SplitR_resp_Xeq.
assumption.
Qed.

Lemma glue_resp_StepF_eq:forall x x' y y' o,
  (x===x')->(y===y')->
  (glue o x y)===(glue o x' y').
intros.
unfold StepF_eq, Map2.
simpl (Xeq ^@> glue o x y).
rewrite ApGlueGlue.
split; assumption.
Qed.

Lemma StepF_eq_sym :forall y x: StepF X, StepF_eq Xeq x y -> StepF_eq Xeq y
x.
intros y. induction y.
 unfold StepF_eq. simpl. intro x0. induction x0.
  unfold StepFfoldProp. simpl. destruct Xst; auto with *.
 simpl. unfold StepFfoldProp; simpl; intuition; auto with *.
intros x H.
assert (H0:=(SplitL_resp_Xeq _ _ o H)).
unfold SplitL in H0.
rewrite SplitGlue in H0; simpl in H0.
assert (H1:=(SplitR_resp_Xeq _ _ o H)).
unfold SplitR in H1.
rewrite SplitGlue in H1; simpl in H1.
apply glue_StepF_eq;auto with *.
Qed.

Hint Resolve StepF_eq_sym StepF_eq_trans.

Lemma StepF_Sth : (Setoid_Theory (StepF X) (StepF_eq Xeq)).
split; intros; eauto with sfarith.
Qed.

Add Setoid (StepF X) (StepF_eq Xeq) StepF_Sth as StepF_Sth1.

Lemma glue_injl:forall o x y x1 y1,
(glue o x y)===(glue o x1 y1) -> (x===x1).
intros.
destruct H as [H _] using (glue_eq_ind Xeq).
rewrite SplitLGlue in H.
assumption.
Qed.

Lemma glue_injr:forall o x y x1 y1,
(glue o x y)===(glue o x1 y1) -> (y===y1).
intros.
destruct H as [_ H] using (glue_eq_ind Xeq).
rewrite SplitRGlue in H.
assumption.
Qed.

Lemma eq_glue_ind : forall (s1 s2 s : StepF X) (a : OpenUnit) (P : Prop),
       (StepF_eq Xeq (SplitL s a) s1 -> StepF_eq Xeq (SplitR s a) s2 -> P) ->
       StepF_eq Xeq s (glue a s1 s2) -> P.
Proof.
intros s1 s2 s a P H H0.
symmetry in H0.
destruct H0 as [H0l H0r] using (glue_eq_ind Xeq).
symmetry in H0l, H0r.
auto.
Qed.

Lemma MirrorSplitR: forall (s : StepF X) (a b : OpenUnit),
  b == OpenUnitDual a ->
  (Mirror (SplitR s a)) === (SplitL (Mirror s) b).
Proof.
intros.
apply StepF_Qeq_eq; auto with *.
apply MirrorSplitR_Qeq; auto with *.
Qed.

Lemma MirrorSplitL: forall  (s : StepF X) (a b : OpenUnit),
  b == OpenUnitDual a ->
  (Mirror (SplitL s a)) === (SplitR (Mirror s) b).
Proof.
intros.
apply StepF_Qeq_eq; auto with *.
apply MirrorSplitL_Qeq; auto with *.
Qed.

End EquivalenceC.

Hint Resolve StepF_eq_sym StepF_eq_trans :sfarith.
Hint Resolve SplitL_resp_Xeq SplitR_resp_Xeq:sfarith.

Section MapMorphism.
Variable X:Type.
Variable Xeq:X->X->Prop.
Variable Y:Type.
Variable Yeq:Y->Y->Prop.
Hypothesis Yst:(Setoid_Theory Y Yeq).
Add Setoid Y Yeq Yst as Yth2.

Lemma Map_morphism: forall (f g : X->Y),
    (forall x y, (Xeq x y)-> (Yeq (f x) (f y))) ->
    (forall x, (Yeq (f x) (g x))) ->
    forall s t:(StepF X), (StepF_eq Xeq s t) -> (StepF_eq Yeq (Map f s) (Map g t)).
Proof.
intros f g Hf Hfg s t Hst.
apply StepF_eq_trans with (Map f t); auto with *.
 apply (Map_resp_StepF_eq Xeq); auto with *.
clear - Hfg.
induction t.
 rapply Hfg.
rapply glue_resp_StepF_eq; assumption.
Qed.

End MapMorphism.

Section ApMorphism.
Variable X:Type.
Variable Xeq:X->X->Prop.
Hypothesis Xst:(Setoid_Theory X Xeq).

Variable Y:Type.
Variable Yeq:Y->Y->Prop.
Hypothesis Yst:(Setoid_Theory Y Yeq).
Add Setoid X Xeq Xst as Xth3.
Add Setoid Y Yeq Yst as Yth3.
Add Setoid (StepF Y) (StepF_eq Yeq) (StepF_Sth Yst) as StepF_Sth3.

Lemma Ap_morphism:forall (f g: StepF (X -> Y)),
  (StepFfoldProp ((fun f => forall x0 x1, (Xeq x0 x1) -> (Yeq (f x0) (f x1))) ^@> f)) ->
  (StepF_eq (fun a b => forall x, (Yeq (a x) (b x))) f g) ->
  forall s s', (StepF_eq Xeq s s') ->
  (StepF_eq Yeq (f <@> s) (g <@> s')).
Proof.
set (Qeq:=(fun a b : X -> Y => forall x : X, Yeq (a x) (b x))).
assert (Q:Setoid_Theory _ Qeq).
 unfold Qeq.
 split; intros.
   reflexivity.
  symmetry; auto with *.
 transitivity (y x0); auto with *.
induction f; intros g Hf Hfg.
 simpl.
 induction g; intros.
  simpl.
  apply (Map_morphism Xeq); auto with *.
 symmetry.
 rewrite ApGlue.
 destruct Hfg as [Hfg0 Hfg1] using (eq_glue_ind Q).
 apply glue_StepF_eq; symmetry.
  rewrite SplitLMap.
  auto with *.
 rewrite SplitRMap.
 auto with *.
intros s s' Hs.
destruct Hfg as [Hfg0 Hfg1] using (glue_eq_ind Qeq).
rewrite ApGlue.
destruct Hf.
apply glue_StepF_eq; auto with *.
 rewrite (StepF_Qeq_eq Yst _ _ (SplitLAp_Qeq g s' o)).
 apply IHf1; auto with *.
rewrite (StepF_Qeq_eq Yst _ _ (SplitRAp_Qeq g s' o)).
apply IHf2; auto with *.
Qed.

Variable W:Type.
Variable Weq:W->W->Prop.
Hypothesis Wst:(Setoid_Theory W Weq).
Add Setoid W Weq Wst as Wth2.

Lemma Map2_morphism: forall f g,
  (forall w w' x x', (Weq w w') -> (Xeq x x')-> (Yeq (f w x) (f w' x'))) ->
  (forall w x, (Yeq (f w x) (g w x))) ->
  forall s s' t t', (StepF_eq Weq s s') -> (StepF_eq Xeq t t') ->
  (StepF_eq Yeq (f ^@> s <@> t) (g ^@> s' <@> t')).
Proof.
intros f g Hf Hfg s s' t t' Hs Ht.
set (A:= f ^@> s).
set (B:= g ^@> s').
apply Ap_morphism; auto with *.
 unfold A.
 clear - Wst Hf.
 induction s.
  intros a b Hab.
  rapply Hf; auto with *; reflexivity.
 simpl.
 split; assumption.
unfold A, B.
apply (Map_morphism Weq); auto with *.
 split; intros.
   reflexivity.
  symmetry; auto with *.
 transitivity (y x0); auto with *.
intros.
apply Hf; auto with *.
reflexivity.
Qed.

End ApMorphism.
