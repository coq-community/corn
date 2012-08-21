Require Import
  Program QArith Qdlog ZArith Qpossec Compress
  MetricMorphisms Qmetric ARArith
  theory.int_pow theory.nat_pow
  stdlib_rationals stdlib_binary_integers.

Instance Q_approx: AppApprox Q := λ x k, 
  match k with
  | Zneg p => approximateQ x (2 ^ p)
  | _ => x
  end.

Lemma Q_approx_correct (x : Q) (k : Z) : Qball (2 ^ k) (app_approx x k) x.
Proof.
  destruct k as [|p|]; try reflexivity.
  unfold app_approx, Q_approx.
  setoid_replace (2 ^ Zneg p)%Qpos with (1 # (2 ^ p))%Qpos.
   now apply ball_sym, approximateQ_correct.
  change (/ Qpower (2%Z) p == 1 # 2 ^ p).
  rewrite <-Qpower.Zpower_Qpower; auto with zarith.
  now rewrite <- Zpower_Ppow.
Qed.

Instance Q_approx_div: AppDiv Q := λ x y k, app_approx (x / y) k.

Instance inject_Q_Q: Cast Q Q_as_MetricSpace := Datatypes.id.
Instance inverse_Q_Q: AppInverse inject_Q_Q := λ x ε, app_approx x (Qdlog2 ε).

Instance: AppRationals Q.
Proof.
  split; try apply _.
     repeat (split; try apply _).
    split; try apply _. intros.
    apply ball_weak_le with (2 ^ Qdlog2 ε)%Qpos.
     now apply (Qpos_dlog2_spec ε).
    now apply Q_approx_correct.
   intros. now apply Q_approx_correct.
  intros. now apply Q_approx_correct.
Qed.

Notation ARQ := (AR (AQ:=Q)).
