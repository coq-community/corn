Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import Coq.ZArith.ZArith CoRN.reals.faster.ARArith.

Ltac AR_solve_pos_loop k :=
 (apply AR_epsilon_sign_dec_pos with k;
  vm_compute;
  match goal with
  | |- Gt ≡ Gt => reflexivity
  | |- Lt ≡ Gt => fail 2 "AR number is negative"
  end) || AR_solve_pos_loop (k - 8)%Z.

Tactic Notation "AR_solve_pos" constr(k) := AR_solve_pos_loop k.
Tactic Notation "AR_solve_pos" := AR_solve_pos 0%Z.

Tactic Notation "AR_solve_ltT" constr(k) := 
  match goal with
  | |- ARltT ?X ?Y => change (ARpos (Y - X)); AR_solve_pos_loop k
  end.
Tactic Notation "AR_solve_ltT" := AR_solve_ltT 0%Z.

Ltac AR_solve_apartT_loop k :=
  (apply AR_epsilon_sign_dec_apartT with k; vm_compute; discriminate) || AR_solve_apartT_loop (k - 8)%Z.

Tactic Notation "AR_solve_apartT" constr(k) := AR_solve_apartT_loop k.
Tactic Notation "AR_solve_apartT" := AR_solve_apartT 0%Z.
