Require Export Metric.
Require Import OpenUnit.
Require Import CornTac.
Require Import Qauto.
Require Import Qabs.
Require Import QMinMax.
Require Import Qordfield.
Require Import COrdFields.

Set Implicit Arguments.
 
Inductive StepF(X:Type):Type:=
|leaf:X->(StepF X)
|glue:OpenUnit->(StepF X)->(StepF X)->(StepF X).

Definition test1:=(leaf 1). 
Definition test2:=(glue (ou 1/2) (leaf 0) (leaf 1)).

Fixpoint Mirror (X:Type) (s:StepF X) : StepF X :=
match s with
| leaf x => leaf x
| glue a s1 s2 => glue (OpenUnitDual a) (Mirror s2) (Mirror s1)
end.

Definition Map(X Y:Type):(X->Y)->(StepF X)->(StepF Y).
fix 4. intros X Y f [x| a t1 t2].
 exact (leaf (f x)).
exact (glue a (Map _ _ f t1) (Map _ _ f t2)).
Defined.

Definition Split (X:Type): (StepF X)-> OpenUnit -> ((StepF X)*(StepF X)).
fix 2.
intros X s a.
destruct s as [x | b t1 t2].
 exact (leaf x , leaf x).

destruct (Q_dec a b) as [[H|H]|H].
   destruct (Split X t1 (OpenUnitDiv a b H)) as [L R].
  exact (L, (glue (OpenUnitDualDiv b a H) R t2)).
  destruct (Split X t2 (OpenUnitDualDiv a b H)) as [L R].
  refine ((glue (OpenUnitDiv b a H) t1 L), R).
  exact (t1,t2).
Defined.

Eval compute in (Split test2 (ou 1/4)).

Definition SplitL (X:Type) (s:StepF X) (o:OpenUnit) : (StepF X) :=
fst (Split s o).

Definition SplitR (X:Type) (s:StepF X) (o:OpenUnit) : (StepF X) :=
snd (Split s o).

Definition Map2 (X Y Z:Type):
  (X->Y->Z)->(StepF X)-> (StepF Y) -> (StepF Z).
fix 5. 
intros X Y Z f s t.
destruct s as [x | b t1 t2].
exact (Map (f x) t).
destruct (Split t b) as [L R].
exact (glue b (Map2 X Y Z f t1 L) (Map2 X Y Z f t2 R)).
Defined.

Definition StepFfold:=
(*
fix 5.
intros X Y f g s.
 destruct s as [x | b t1 t2].
 exact (f x).
 exact (g b (StepFfold X Y f g t1) (StepFfold X Y f g t2)).
Defined.*)
fix StepFfold (X Y : Type) (f : X -> Y) (g : OpenUnit -> Y -> Y -> Y)
              (s : StepF X) {struct s} : Y :=
  match s with
  | leaf x => f x
  | glue b t1 t2 => g b (StepFfold X Y f g t1) (StepFfold X Y f g t2)
  end.

Definition Supnorm:(StepF Q)->Q:=(StepFfold Qabs (fun _=> Qmax)).
Eval compute in (Supnorm test2):Q.
Definition IntegralQ:(StepF Q)->Q:=(StepFfold (fun x => x) (fun b x y => (b*x+(1-b)*y))).
Eval compute in (IntegralQ test2):Q.
Definition L1Norm(f:StepF Q):Q:=(IntegralQ (Map Qabs f)).
Eval compute in (L1Norm test2):Q.
Definition Distance(f g:StepF Q):Q:=(L1Norm (Map2 Qminus f g)).
Eval compute in (Distance test1 test2):Q.
Eval compute in (Distance test2 test1):Q.
Definition L1Ball (e:Qpos)(f g:StepF Q):Prop:=(Distance f g)<=e.
Eval compute in (L1Ball (1#1)%Qpos test2 test1).
Definition Mesh (X:Type):(StepF X)->Q:=(StepFfold (fun x => 1)(fun b x y => (Qmax (b*x) ((1-b)*y)))).
Eval compute in (Mesh test2).

Lemma Split_ind : forall X s a (P:StepF X*StepF X -> Prop),
 (P (SplitL s a,SplitR s a)) -> P (Split s a).
Proof.
intros X s a P.
unfold SplitL, SplitR.
destruct (Split s a).
auto with *.
Qed.

Lemma SplitLR_glue_ind : forall X s1 s2 (a b:OpenUnit) (P:(StepF X) -> (StepF X) -> Prop),
 (forall (H:a < b), P (SplitL s1 (OpenUnitDiv a b H)) (glue (OpenUnitDualDiv b a H) (SplitR s1 (OpenUnitDiv a b H)) s2)) ->
 (forall (H:b < a), P (glue (OpenUnitDiv b a H) s1 (SplitL s2 (OpenUnitDualDiv a b H))) (SplitR s2 (OpenUnitDualDiv a b H))) ->
 (a == b -> P s1 s2) ->
 P (SplitL (glue b s1 s2) a) (SplitR (glue b s1 s2) a).
Proof.
intros X s1 s2 a b P Hl Hr Heq.
unfold SplitL, SplitR.
simpl.
destruct (Q_dec a b) as [[Hab|Hab]|Hab]; 
 try apply Split_ind; simpl; auto with *.
Qed.

Lemma SplitL_glue_ind : forall X s1 s2 (a b:OpenUnit) (P:(StepF X) -> Prop),
 (forall (H:a < b), P (SplitL s1 (OpenUnitDiv a b H))) ->
 (forall (H:b < a), P (glue (OpenUnitDiv b a H) s1 (SplitL s2 (OpenUnitDualDiv a b H)))) ->
 (a == b -> P (s1)) ->
 P (SplitL (glue b s1 s2) a).
Proof.
intros.
apply (SplitLR_glue_ind s1 s2 a b (fun a b => P a));
assumption.
Qed.

Lemma SplitR_glue_ind : forall X s1 s2 (a b:OpenUnit) (P:(StepF X) -> Prop),
 (forall (H:a < b), P (glue (OpenUnitDualDiv b a H) (SplitR s1 (OpenUnitDiv a b H)) s2)) ->
 (forall (H:b < a), P (SplitR s2 (OpenUnitDualDiv a b H))) ->
 (a == b -> P (s2)) ->
 P (SplitR (glue b s1 s2) a).
Proof.
intros.
apply (SplitLR_glue_ind s1 s2 a b (fun a b => P b));
assumption.
Qed.

Fixpoint StepF_Qeq (X:Type) (s1 s2: StepF X) : Prop :=
match s1, s2 with
|leaf x, leaf y => x = y
|glue a x1 x2, glue b y1 y2 => a == b /\ (StepF_Qeq x1 y1) /\ (StepF_Qeq x2 y2)
|_, _ => False
end.

Lemma StepF_Qeq_refl : forall X (s: StepF X), StepF_Qeq s s.
Proof.
induction s; simpl; auto with *.
Qed.

Lemma StepF_Qeq_sym : forall X (s t: StepF X), StepF_Qeq s t -> StepF_Qeq t s.
Proof.
induction s; induction t; try contradiction; simpl; auto with *.
intros [H0 [H1 H2]].
repeat split; eauto with *.
Qed.

Lemma StepF_Qeq_trans : forall X (s t u: StepF X), StepF_Qeq s t -> StepF_Qeq t u -> StepF_Qeq s u.
Proof.
induction s; induction t; induction u; try contradiction; simpl; auto with *.
 intros; transitivity x0; assumption.
intros [H0 [H1 H2]] [H3 [H4 H5]].
repeat split; eauto with *.
Qed.

Hint Resolve StepF_Qeq_refl StepF_Qeq_sym StepF_Qeq_trans.

Lemma Mirror_resp_Qeq : forall X (s t:StepF X), StepF_Qeq s t -> StepF_Qeq (Mirror s) (Mirror t).
Proof.
induction s; induction t; intros Hst; simpl in *; try assumption; try contradiction.
destruct Hst as [Ho [Hst1 Hst2]].
repeat split.
  rewrite Ho; reflexivity.
 apply IHs2; assumption.
apply IHs1; assumption.
Qed.

Hint Resolve Mirror_resp_Qeq.

Lemma MirrorMirror : forall X (s:StepF X), (StepF_Qeq (Mirror (Mirror s)) s).
Proof.
induction s.
 simpl; reflexivity.
repeat split; auto with *.
simpl; ring.
Qed.   

Hint Resolve MirrorMirror.

Lemma SplitR_resp_Qeq : forall X (s t:StepF X) (a b:OpenUnit), a == b -> StepF_Qeq s t -> StepF_Qeq (SplitR s a) (SplitR t b).
Proof.
induction s; induction t; intros a b Hab Hst; simpl in *; try assumption; try contradiction.
destruct Hst as [Ho [Hst1 Hst2]].
apply SplitR_glue_ind; intros Hao; apply SplitR_glue_ind; intros Hbo; repeat split; auto with *;
 try solve [elim (Qlt_not_le _ _ Hao); rewrite Hab; rewrite Ho; try rewrite Hbo; auto with *
           |elim (Qlt_not_le _ _ Hbo); rewrite <- Hab; rewrite <- Ho; try rewrite Hao; auto with *];
 try apply IHs1; try apply IHs2; auto with *; simpl; try (rewrite Hab; rewrite Ho; reflexivity).
Qed.

Hint Resolve SplitR_resp_Qeq.

Lemma MirrorSplitL : forall X (s:StepF X) (a b:OpenUnit), b == (OpenUnitDual a) -> (StepF_Qeq (Mirror (SplitL s a)) (SplitR (Mirror s) b)).
Proof.
induction s.
 auto with *.
intros a b Hab; simpl in Hab.
simpl.
apply SplitL_glue_ind; intros Hao; apply SplitR_glue_ind; intros Hoa; simpl in Hoa;
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

Lemma MirrorSplitR : forall X (s:StepF X) (a b:OpenUnit), b == (OpenUnitDual a) -> (StepF_Qeq (Mirror (SplitR s a)) (SplitL (Mirror s) b)).
Proof.
intros X s a b H.
apply StepF_Qeq_trans with (Mirror (SplitR (Mirror (Mirror s)) a));
 auto with *.
apply StepF_Qeq_trans with (Mirror (Mirror (SplitL (Mirror s) b)));
 auto with *.
apply Mirror_resp_Qeq.
apply StepF_Qeq_sym.
apply MirrorSplitL.
simpl in *.
rewrite H.
ring.
Qed.

Lemma SplitL_resp_Qeq : forall X (s t:StepF X) (a b:OpenUnit), a == b -> StepF_Qeq s t -> StepF_Qeq (SplitL s a) (SplitL t b).
Proof.
intros X s t a b H H0.
apply StepF_Qeq_trans with (Mirror (Mirror (SplitL s a)));
 auto with *.
apply StepF_Qeq_trans with (Mirror (SplitR (Mirror s) (OpenUnitDual a))).
 apply Mirror_resp_Qeq.
 apply MirrorSplitL; auto with *.
apply StepF_Qeq_trans with (Mirror (SplitR (Mirror t) (OpenUnitDual b))).
 apply Mirror_resp_Qeq.
 apply SplitR_resp_Qeq; auto with *.
 simpl; rewrite H; reflexivity.
apply StepF_Qeq_trans with (Mirror (Mirror (SplitL t b)));
 auto with *.
apply Mirror_resp_Qeq.
apply StepF_Qeq_sym.
apply MirrorSplitL; auto with *.
Qed.

Hint Resolve SplitL_resp_Qeq.

Lemma SplitLSplitL : forall X (s:StepF X) (a b c:OpenUnit), (a*b==c) -> 
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

Lemma SplitRSplitR : forall X (s:StepF X) (a b c:OpenUnit), (a+b-a*b==c) -> 
 (StepF_Qeq (SplitR (SplitR s a) b) (SplitR s c)).
Proof.
intros X s a b c H.
apply StepF_Qeq_trans with (Mirror (Mirror (SplitR (SplitR s a) b)));
 auto with *.
apply StepF_Qeq_trans with (Mirror (Mirror (SplitR s c)));
 auto with *.
apply Mirror_resp_Qeq.
apply StepF_Qeq_trans with (SplitL (SplitL (Mirror s) (OpenUnitDual a)) (OpenUnitDual b)).
 apply StepF_Qeq_trans with (SplitL (Mirror (SplitR s a)) (OpenUnitDual b)).
  apply MirrorSplitR; auto with *.
 apply SplitL_resp_Qeq; auto with *.
 apply MirrorSplitR; auto with *.
apply StepF_Qeq_trans with (SplitL (Mirror s) (OpenUnitDual c)).
 apply SplitLSplitL.
 simpl.
 rewrite <- H.
 ring.
apply StepF_Qeq_sym.
apply MirrorSplitR; auto with *.
Qed.

Lemma SplitLSplitR : forall X (s:StepF X) (a b c d:OpenUnit), (a+b-a*b==c) -> (d*c==a) -> 
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

Require Import Setoid.
Section Equivalence.
Variable X:Type.
Variable Xeq:X->X->Prop.
Hypothesis Xst:(Setoid_Theory X Xeq).
Hint Resolve (Seq_trans X Xeq Xst) (Seq_sym X Xeq Xst) (Seq_refl X Xeq Xst):foo.

Definition StepFfoldProp:=StepFfold (fun x => x ) (fun _ a b => a /\ b ).

Definition StepF_eq (f g:StepF X):Prop:=
(StepFfoldProp (Map2 Xeq f g)).

Hint Unfold StepFfoldProp StepFfold StepF_eq.
Lemma Qdec_eq_ind: forall a b:Q, forall P:{a<b}+{b<a}+{a==b}->Type,
 a==b-> (forall H, (P (inright _ H)))->forall x, (P x).
intros a b P H H1 [[H2|H2]|H2].
  elim (Qlt_not_le _ _ H2); auto with*.
  (* Need to prove a==b -> b<=a*) 
  setoid_replace (a:Q) with (b:Q); auto with *.
 elim (Qlt_not_le _ _ H2); auto with*.
auto with *.
Qed.

Notation "x === y" := (StepF_eq x y) (at level 60).

Lemma StepF_eq_refl:forall x : StepF X, x === x.
intro s.
induction s.
compute. apply Seq_refl; auto.
unfold StepF_eq. simpl. elim (Q_dec o o) using Qdec_eq_ind; simpl; auto with *.
Qed.

Hint Resolve StepF_eq_refl:sfarith.

Lemma StepF_eq_aux:forall s s1 s2, forall a, s1 === (SplitL s a) -> s2 === (SplitR s a) -> (glue a s1 s2) === s.
intros s s1 s2 a. unfold SplitL, SplitR, StepF_eq. simpl. 
intros.
destruct (Split s a) as [s3 s4].
split; assumption.
Qed.

Lemma StepF_Qeq_eq : forall s t, (StepF_Qeq s t) -> s === t.
Proof.
induction s; induction t; try contradiction; simpl.
 intros H.
 rewrite H.
 auto with *.
intros [H [H0 H1]].
apply StepF_eq_aux.
 apply IHs1.
 apply SplitL_glue_ind; intros H2;
  try (elim (Qlt_not_le _ _ H2); rewrite H); auto with *.
apply IHs2.
apply SplitR_glue_ind; intros H2;
 try (elim (Qlt_not_le _ _ H2); rewrite H); auto with *.
Qed.

(*
Lemma glue_resp_Qeq:forall s t:StepF X, forall a b:OpenUnit, a==b -> (StepF_eq (glue a s t) (glue b s t)).
intros s t a b H.
unfold StepF_eq; simpl.
elim (Q_dec a b) using Qdec_eq_ind;auto with *.
intros H1.
change ((StepF_eq s s) /\ (StepF_eq t t)); auto with *.
Qed.
*)
Lemma glue_wd:forall (s1 s2 t1 t2:StepF X) (a b:OpenUnit), a==b -> s1 === s2 -> t1 === t2 -> ((glue a s1 t1) === (glue b s2 t2)).
Proof.
intros s1 s2 t1 t2 a b Hab Hs Ht.
unfold StepF_eq; simpl.
elim (Q_dec a b) using Qdec_eq_ind;auto with *.
Qed.

Lemma glue_eq_ind : forall s1 s2 s a (P:Prop), (s1 === (SplitL s a) -> s2 === (SplitR s a) -> P) -> (glue a s1 s2 === s) -> P.
Proof.
intros s1 s2 s a P H H0.
unfold SplitL, SplitR, StepF_eq in *.
simpl in *.
destruct (Split s a).
destruct H0.
apply H; assumption.
Qed.

Hint Resolve StepF_eq_aux glue_wd :starith.

Lemma glueSplit_eq:forall s:StepF X, forall a:OpenUnit, 
 (glue a (SplitL s a) (SplitR s a)) === s.
auto with *.
Qed.


Lemma Mapleaf(Y:Type): forall f:X->Y, 
  forall x, (Map f (leaf x))=(leaf (f x)).
 simpl;auto.
Qed.

Lemma Mapglue(Y:Type): forall f:X->Y, (forall o s1 s2, ((Map f (glue o s1 s2))=(glue o (Map f s1) (Map f s2)))).
 simpl;auto.
Qed.

 Hint Resolve Mapglue Mapleaf:foo.
Lemma splitmap(Y:Type):forall x:(StepF X), forall a, forall f:X->Y, 
    (Split (Map f x) a) = let (l,r) := Split x a in (Map f l,Map f r).
intros Y s. induction s. simpl; auto.
intros a f.
rewrite Mapglue. simpl. destruct (Q_dec a o) as [[H0|H0]|H0].
rewrite IHs1. destruct (Split s1 (OpenUnitDiv a o H0)). auto with *. 
rewrite IHs2. destruct (Split s2 (OpenUnitDualDiv a o H0)). auto with *. 
auto.
Qed.

Lemma SplitLMap(Y:Type): forall x:(StepF X), forall a, forall f:X->Y, 
    SplitL (Map f x) a = Map f (SplitL x a).
intros. unfold SplitL. rewrite splitmap. destruct (Split x a). simpl. auto.
Qed.

Lemma SplitRMap(Y:Type): forall x:(StepF X), forall a, forall f:X->Y, 
    snd (Split (Map f x) a) = Map f (snd (Split x a)).
intros. unfold SplitR. rewrite splitmap. destruct (Split x a). simpl. auto.
Qed.

End  Equivalence.

Hint Resolve StepF_eq_refl StepF_Qeq_eq splitmap SplitLMap SplitRMap:foo.
Section Equivalence1.
Variable X:Type.
Variable Xeq:X->X->Prop.
Hypothesis Xst:(Setoid_Theory X Xeq).
Variable Y:Type.
Variable Yeq:Y->Y->Prop.
Hypothesis Yst:(Setoid_Theory Y Yeq).

Hint Resolve (Seq_trans X Xeq Xst) (Seq_sym X Xeq Xst) (Seq_refl X Xeq Xst):foo.
Notation "x === y" := (StepF_eq Xeq x y) (at level 60).
Print StepF_eq.

Add Setoid X Xeq Xst as Xth.

Hint Unfold StepFfoldProp StepFfold StepF_eq.
Lemma Map_resp_StepF_eq: forall f:X->Y, 
    (forall x y, (Xeq x y)-> (Yeq (f x) (f y))) ->
    forall s t:(StepF X), (s === t) -> (StepF_eq Yeq (Map f s) (Map f t)).
intros f H.

induction s. induction t.
  unfold StepF_eq;simpl;auto with *. 
 rewrite Mapglue. rewrite Mapleaf. 
 unfold StepF_eq. unfold StepFfoldProp. simpl;  intuition.
simpl. intros t H0.
unfold StepF_eq in H0. simpl in H0.
unfold StepF_eq. simpl.
rewrite splitmap. destruct ( Split t o) as [L R].
destruct H0 as [H1 H2]. split. apply IHs1. apply H1.
apply IHs2. apply H2.

(*
assert ((glue o s1 s2) ===
  (glue o (fst (Split t o)) (snd (Split t o)))).
 generalize H0. unfold StepF_eq;simpl.
 elim (Q_dec o o) using Qdec_eq_ind;auto with *.
 destruct (Split t o). simpl. intuition. 

apply StepF_eq_aux. 
 rewrite fstsplitmap.
 apply IHs1.
 generalize H1. unfold StepF_eq;simpl.
 elim (Q_dec o o) using Qdec_eq_ind;auto with *;simpl; intuition.
rewrite sndsplitmap.
apply IHs2.
generalize H1. unfold StepF_eq;simpl.
elim (Q_dec o o) using Qdec_eq_ind;auto with *;simpl; intuition.
*)
Qed.
(*
Lemma leaf_eq:forall x y:X, (leaf x===leaf y) -> (Xeq x y).
auto with *.
Qed.

Lemma leaf_eq':forall x y:X, (Xeq x y) -> (leaf x===leaf y).
auto with *.
Qed.
*)
End Equivalence1.

Hint Resolve StepF_eq_refl.

Section Equivalence2.
Variable X:Type.
Variable Xeq:X->X->Prop.
Hypothesis Xst:(Setoid_Theory X Xeq).
Add Setoid X Xeq Xst as Xth1.

Hint Resolve (Seq_trans X Xeq Xst) (Seq_sym X Xeq Xst) (Seq_refl X Xeq Xst):foo.
Notation "x === y" := (StepF_eq Xeq x y) (at level 60).


(* Add Setoid X Xeq Xst as Xth.*)
Lemma StepFfoldPropglue:forall y o,
 StepFfoldProp (glue o (fst (Split y o)) (snd (Split y o))) <->
StepFfoldProp y.
induction y.
  unfold StepF_eq, StepFfoldProp.
  simpl; tauto.
simpl.
intro o0.
destruct (Q_dec o0 o) as [[H|H]|H].
   generalize (IHy1 (OpenUnitDiv o0 o H)).
   destruct (Split y1 (OpenUnitDiv o0 o H)) as [l r].
   simpl.
   change ((StepFfoldProp l /\StepFfoldProp r <-> StepFfoldProp y1) ->
(StepFfoldProp l /\ StepFfoldProp r /\ StepFfoldProp y2 <->
  StepFfoldProp y1 /\ StepFfoldProp y2)).
   tauto.
  generalize (IHy2 (OpenUnitDualDiv o0 o H)).
  destruct (Split y2 (OpenUnitDualDiv o0 o H)) as [l r].
  simpl.
  change ((StepFfoldProp l /\StepFfoldProp r <-> StepFfoldProp y2) ->
((StepFfoldProp y1 /\ StepFfoldProp l) /\ StepFfoldProp r <->
  StepFfoldProp y1 /\ StepFfoldProp y2)).
  tauto.
simpl.
reflexivity.
Qed.

Hint Resolve StepFfoldPropglue:foo.
Lemma StepFfoldProp_morphism:forall x y:(StepF Prop),
  (StepF_eq iff x y) ->
  ((StepFfoldProp x)<->(StepFfoldProp y)).
induction x. induction y.
   auto with *.
  unfold StepF_eq. simpl. unfold StepFfoldProp;simpl;intuition.
intros y H0.
unfold StepF_eq in H0. simpl in H0.
transitivity (StepFfoldProp ((glue o (fst (Split y o)) (snd (Split y 
o))))).
  change ((StepFfoldProp x1 /\ StepFfoldProp x2) <->
  ((StepFfoldProp (fst (Split y o)) /\ (StepFfoldProp (snd (Split y 
o)))))).
  destruct (Split y o) as [l r].
  destruct H0 as [H0l H0r].
  rewrite (IHx1 l); try assumption.
  rewrite (IHx2 r); try assumption.
  simpl.
  tauto.
auto with *.
Qed.

Lemma StepF_eq_resp_Qeq : forall s t u v, (StepF_Qeq s t) -> (StepF_Qeq u v) -> s === u -> t === v.
Proof.
induction s; induction t; try contradiction.
 intros u v Hst Huv Hsu.
 simpl in Hst.
 unfold StepF_eq in *.
 simpl in *.
 rewrite <- Hst.
 rewrite <- (StepFfoldProp_morphism (Map (Xeq x) u)); auto with *.
 apply (Map_resp_StepF_eq Xst); auto with *.
  split;[apply iff_refl|apply iff_sym|apply iff_trans].
 intros a b Hab; split; eauto with *.
intros u v [H [Hst0 Hst1]] Huv Hsu.
destruct Hsu as [Hsu1 Hsu2] using (glue_eq_ind Xeq).
apply StepF_eq_aux.
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
simpl.
split; apply glue_eq_ind; intros H0 H1.
 apply StepF_eq_aux.
  rewrite <- IHs1.
  eapply StepF_eq_resp_Qeq;[| |apply H1]; auto with *.
  apply StepF_Qeq_sym.
  apply MirrorSplitL; auto with *.
 rewrite <- IHs2.
 eapply StepF_eq_resp_Qeq;[| |apply H0]; auto with *.
 apply StepF_Qeq_sym.
 apply MirrorSplitR; auto with *.
apply StepF_eq_aux.
 eapply StepF_eq_resp_Qeq;[apply StepF_Qeq_refl|apply MirrorSplitR; apply Qeq_refl|].
 rewrite IHs2.
 assumption.
eapply StepF_eq_resp_Qeq;[apply StepF_Qeq_refl|apply MirrorSplitL; apply Qeq_refl|].
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
 unfold StepF_eq in *.
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
 apply StepF_eq_aux.
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
eapply StepF_eq_resp_Qeq; try (eapply StepF_Qeq_trans;[apply Mirror_resp_Qeq; apply StepF_Qeq_sym; apply MirrorSplitR; reflexivity|apply MirrorMirror]).
rewrite  Mirror_eq_Mirror.
apply SplitL_resp_Xeq.
rewrite Mirror_eq_Mirror.
assumption.
Qed.
End Equivalence2.

Section Equivalence3.
Variable X:Type.
Variable Xeq:X->X->Prop.
Hypothesis Xst:(Setoid_Theory X Xeq).
Variable Y:Type.
Variable Yeq:Y->Y->Prop.
Hypothesis Yst:(Setoid_Theory Y Yeq).
Variable Z:Type.
Variable Zeq:Z->Z->Prop.
Hypothesis Zst:(Setoid_Theory Z Zeq).
Hint Resolve (Seq_trans X Xeq Xst) (Seq_sym X Xeq Xst) (Seq_refl X Xeq Xst):foo.
Hint Resolve (Seq_trans Y Yeq Yst) (Seq_sym Y Yeq Yst) (Seq_refl Y Yeq Yst):foo.

Lemma Map2_morphism2:forall f, (forall x x' y y',
  (Xeq x x) -> (Yeq y y')-> (Zeq (f x y) (f x' y'))) ->
  forall s t t', (StepF_eq Yeq t t') ->
  (StepF_eq Zeq (Map2 f s t) (Map2 f s t')).
intros f H.
induction s.
 intros t t' H0.
 simpl.
 eapply Map_resp_StepF_eq;try apply Yst; auto with *.
intros t t' H0.
simpl.
apply Split_ind.
apply Split_ind.
simpl.
apply StepF_eq_aux.
 apply SplitL_glue_ind; intros H1; try (elim (Qlt_not_le _ _ H1); auto with *).
 apply IHs1.
 apply SplitL_resp_Xeq; auto with *.
apply SplitR_glue_ind; intros H1; try (elim (Qlt_not_le _ _ H1); auto with *).
apply IHs2.
apply SplitR_resp_Xeq; auto with *.
Qed.

Notation "x === y" := (StepF_eq Xeq x y) (at level 60).

Lemma StepF_eq_trans:forall x y z : StepF X, x === y -> y === z -> x === z.
induction x. intros.
 unfold StepF_eq;simpl;auto with *.
  cut (StepFfoldProp (Map (Xeq x) y)); try auto.
 intros H1.
 rewrite <- (StepFfoldProp_morphism Xst (Map (Xeq x) y)); auto with *.
 eapply Map_resp_StepF_eq; try apply Xst; auto with *.
  split;[apply iff_refl|apply iff_sym|apply iff_trans].
 intros a b Hab.
 split; eauto with *.
intros.
destruct H using (glue_eq_ind Xeq).
apply StepF_eq_aux.
 eapply IHx1.
  apply H.
 apply SplitL_resp_Xeq.
  apply Xst.
 assumption.
eapply IHx2.
 apply H1.
apply SplitR_resp_Xeq.
 apply Xst.
assumption.
Qed.

Lemma Map2_morphism1:forall f, (forall x x' y y',
  (Xeq x x) -> (Yeq y y')-> (Zeq (f x y) (f x' y'))) ->
  forall t t' s, (StepF_eq Xeq t t') ->
  (StepF_eq Zeq (Map2 f t s) (Map2 f t' s)).
intros f H.
induction t.
 induction t'.

Focus 3.
intros t' s H0.
destruct H0 as [H0a H0b] using (glue_eq_ind Xeq).
simpl.
apply Split_ind.
apply StepF_eq_trans.

induction s.
 intros t t' H0.
 simpl.
 eapply Map_resp_StepF_eq;try apply Yst; auto with *.
intros t t' H0.
simpl.
apply Split_ind.
apply Split_ind.
simpl.
apply StepF_eq_aux.
 apply SplitL_glue_ind; intros H1; try (elim (Qlt_not_le _ _ H1); auto with *).
 apply IHs1.
 apply SplitL_resp_Xeq; auto with *.
apply SplitR_glue_ind; intros H1; try (elim (Qlt_not_le _ _ H1); auto with *).
apply IHs2.
apply SplitR_resp_Xeq; auto with *.
Qed.


Lemma StepF_eq_symm:forall x y : StepF X, StepF_eq x y -> StepF_eq y x.
intro s. unfold StepF_eq. induction s. 
 intros t. simpl. induction t. 
  simpl. auto with *. 
 simpl. intuition.
simpl. intro t. destruct t as [y | b t1 t2].


 destruct y  simpl. intuition.
induction y. simpl; intuition.

unfold Map2. destruct (Split t b). simpl. auto with *.


 unfold Map2. unfold StepFfold. simpl. intuition. clear H1. simpl. apply H0. intros.
*)
destruct t as [y | b t1 t2].
destruct s as [x | a s1 s2].

Lemma StepF_eq_trans:forall x y z : StepF X, StepF_eq x y -> StepF_eq y z -> StepF_eq x z.


Lemma StepFst: Setoid_Theory (StepF X) StepF_eq.


(* TODO:
setoid eq 
Is a metric space
Continuity of integration
Continuity of Map, Map2
Continuous functions are in the completion, i.e. there is an injection 
from continuous functions to integrable ones.
Integration is correct. Needs mesh. 

Write a tactic Done (auto with *, etc)
Find out how simple works with fold.
*)
