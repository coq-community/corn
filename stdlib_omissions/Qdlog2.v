(* Discrete logarithm with base 2 on [Q] *)
Require Import ZArith QArith Qround Qpower stdlib_omissions.Q.

Definition Qdlog2 (x : Q) : Z :=
  match Qlt_le_dec x 1 with
  | left _ => Zopp (Z.log2_up (Qround.Qceiling (/x)))
  | right _ => Z.log2 (Qround.Qfloor x)
  end.

Instance: Proper (Qeq ==> eq) Qdlog2.
Proof.
  intros ? ? E. unfold Qdlog2.
  do 2 case (Qlt_le_dec _ _); rewrite E; intros; try easy.
   now destruct (Qlt_not_le y 1).
  now destruct (Qlt_not_le y 1).
Qed.

Lemma Qdlog2_spec (x : Q) : 
  0 < x -> (2#1) ^ Qdlog2 x <= x /\ x < (2#1) ^ (Zsucc (Qdlog2 x)).
Proof.
  unfold Qdlog2.
  change (2 # 1) with (inject_Z 2).
  intros E1.
  case (Qlt_le_dec _ _); intros E2.
   assert (1 < Qceiling (/x))%Z.
    rewrite Zlt_Qlt.
    apply Qlt_le_trans with (/x).
     change (inject_Z 1) with (/1).
     now apply Qdiv_flip_lt.
    now apply Qle_ceiling.
   split.
    rewrite Qpower_opp. rewrite <-(Qinv_involutive x) at 2.
    apply Qdiv_flip_le.
     now apply Qinv_lt_0_compat.
    apply Qle_trans with (inject_Z (Qceiling (/x))).
     now apply Qle_ceiling.
    rewrite <-Zpower_Qpower, <-Zle_Qle.
     now apply Z.log2_up_spec.
    now apply Z.log2_up_nonneg.
   replace (Zsucc (-Z.log2_up (Qceiling (/x))))%Z with (-(Zpred (Z.log2_up (Qceiling (/x)))))%Z.
    rewrite Qpower_opp. rewrite <-(Qinv_involutive x) at 1.
    apply Qdiv_flip_lt.
     now apply Qpower_0_lt.
    apply Qle_lt_trans with (inject_Z (Zpred (Qceiling (/x)))).
     rewrite <-Zpower_Qpower, <-Zle_Qle.
      now apply Z.lt_le_pred, Z.log2_up_spec.
     now apply Z.lt_le_pred, Z.log2_up_pos.
    rewrite <-Z.sub_1_r. now apply Qceiling_lt.
   rewrite <-Z.add_1_l, <-Z.sub_1_r. ring.
  split.
   apply Qle_trans with (inject_Z (Qfloor x)).
    rewrite <-Zpower_Qpower, <-Zle_Qle.
     now apply Zlog2_spec, Qfloor_pos.
    now apply Z.log2_nonneg.
   now apply Qfloor_le.
  apply Qlt_le_trans with (inject_Z (Zsucc (Qfloor x))).
   rewrite <-Z.add_1_r.
   now apply Qlt_floor.
  rewrite <-Zpower_Qpower, <-Zle_Qle.
   now apply Zle_succ_l, Zlog2_spec, Qfloor_pos.
  now apply Zle_le_succ, Z.log2_nonneg.
Qed.

Lemma Qdlog2_nonneg (x : Q) : 
  1 <= x -> (0 <= Qdlog2 x)%Z.
Proof.
  intros E.
  unfold Qdlog2.
  case (Qlt_le_dec x 1); intros.
   now destruct (Qlt_not_le x 1).
  apply Z.log2_nonneg.
Qed.
