
Require Import
        Coq.QArith.QArith CoRN.model.Zmod.ZGcd
        CoRN.model.totalorder.QposMinMax
        CoRN.stdlib_omissions.Q.
Set Automatic Introduction.

Open Scope Q_scope.

Definition Qgcd (a b: Q): Q :=
  Zgcd_nat (Qnum a * Qden b) (Qnum b * Qden a) # (Qden a * Qden b).

Lemma Qgcd_sym (a b: Q): Qgcd a b = Qgcd b a.
Proof.
 unfold Qgcd. intros. rewrite Zgcd_nat_sym. rewrite Pmult_comm. reflexivity.
Qed.

Lemma Qgcd_divides (a b: Q): exists c: Z, inject_Z c * Qgcd a b == a.
Proof.
 revert a b.
 intros [an ad] [bn bd].
 unfold Qgcd. simpl.
 destruct (Zgcd_nat_divides (an * bd) (bn * ad)) as [c E].
 exists c.
 unfold Qmult, Qeq. simpl.
 rewrite E, Zpos_mult_morphism.
 ring.
Qed.

Lemma Qgcd_nonneg a b: 0 <= Qgcd a b.
Proof.
 revert a b.
 intros [an ad] [bn bd]. simpl. unfold Qle. simpl. auto with *.
Qed.

#[global]
Hint Immediate Qgcd_nonneg.

Program Definition Qcd_pos: Qpos -> Qpos -> Qpos := Qgcd.

Next Obligation. Proof with auto.
 simpl.
 destruct (Qle_lt_or_eq 0 _ (Qgcd_nonneg (proj1_sig x) (proj1_sig x0))) as [| B]...
 exfalso.
 destruct x.
 destruct (Qgcd_divides x (proj1_sig x0)) as [? E]. simpl in *.
 revert q.
 rewrite <- E, <- B, Qmult_0_r.
 apply Qlt_irrefl.
Qed.

Lemma Qgcd_pos_divides (a b: Qpos):
  exists c: positive, inject_Z c * proj1_sig (Qcd_pos a b) == proj1_sig a.
Proof with auto with *.
 revert a b.
 intros [a ap] [b bp].
 simpl.
 destruct (Qgcd_divides a b) as [x E].
 destruct x.
   exfalso.
   ring_simplify in E.
   revert ap. rewrite E. apply Qlt_irrefl.
  exists p...
 exfalso.
 rewrite <- E in ap.
 apply (Qlt_irrefl 0).
 apply Qlt_le_trans with (inject_Z (Zneg p) * Qgcd a b)...
 rewrite Qmult_comm.
 apply Qmult_nonneg_nonpos...
Qed.

Lemma Qpos_gcd3 (a b c: Qpos):
  exists g: Qpos,
  exists i: positive, inject_Z i * proj1_sig g == proj1_sig a /\
  exists j: positive, inject_Z j * proj1_sig g == proj1_sig b /\
  exists k: positive, inject_Z k * proj1_sig g == proj1_sig c.
Proof with auto.
 intros.
 exists (Qcd_pos a (Qcd_pos b c)).
 destruct (Qgcd_pos_divides b c) as [x E].
 destruct (Qgcd_pos_divides c b) as [x0 F].
 simpl in F.
 rewrite Qgcd_sym in F.
 change (inject_Z x0 * proj1_sig (Qcd_pos b c) == proj1_sig c) in F.
 revert E F.
 generalize (Qcd_pos b c).
 intros.
 destruct (Qgcd_pos_divides a q) as [x1 G].
 destruct (Qgcd_pos_divides q a) as [x2 H].
 simpl in H.
 rewrite Qgcd_sym in H.
 change (inject_Z x2 * proj1_sig (Qcd_pos a q) == proj1_sig q) in H.
 exists x1.
 revert G H.
 generalize (Qcd_pos a q).
 split...
 exists (x * x2)%positive.
 split.
  rewrite Q.Pmult_Qmult.
  rewrite <- Qmult_assoc.
  rewrite H...
 exists (x0 * x2)%positive.
 rewrite Q.Pmult_Qmult.
 rewrite <- Qmult_assoc.
 rewrite H...
Qed.
