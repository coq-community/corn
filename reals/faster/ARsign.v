Require Import ZArith Complete ARArith positive_semiring_elements.

Section sign.
Context `{AppRationals AQ}.

Definition AR_epsilon_sign_dec (k : Z) (x : AR) : comparison :=
  let ε : AQ₊ := Pos_shiftl 1 k in
  let z : AQ := approximate x ('ε : Qpos) in
  if decide_rel (≤) (2 * 'ε) z 
    then Gt 
    else if decide_rel (≤) z (-2 * 'ε) then Lt else Eq.

Program Definition AR_epsilon_sign_dec_pos (x : AR)
  (k : Z) (Pk : AR_epsilon_sign_dec k x ≡ Gt) : ARpos x := ARpos_char (Pos_shiftl 1 k) x _.
Next Obligation.
  revert Pk. unfold AR_epsilon_sign_dec.
  case (decide_rel (≤)); [ intros; assumption |].
  case (decide_rel (≤)); discriminate.
Qed.

Program Definition AR_epsilon_sign_dec_neg (x : AR)
  (k : Z) (Pk : AR_epsilon_sign_dec k x ≡ Lt) : ARpos (-x) := ARpos_char (Pos_shiftl 1 k) (-x) _.
Next Obligation.
  revert Pk. unfold AR_epsilon_sign_dec.
  case (decide_rel (≤)); [discriminate |].
  case (decide_rel (≤)); [| discriminate].
  intros. apply rings.flip_opp. 
  now rewrite rings.opp_involutive, rings.opp_mult_distr_l.
Qed.

Definition AR_epsilon_sign_dec_apart (x y : AR)
  (k : Z) (Pk : ¬AR_epsilon_sign_dec k (x - y) ≡ Eq) : x >< y.
Proof.
  revert Pk.
  case_eq (AR_epsilon_sign_dec k (x - y)); intros E ?.
    now destruct Pk.
   left. apply ARpos_wd with (-(x - y)).
    symmetry. now apply rings.opp_swap_r.
   now apply AR_epsilon_sign_dec_neg with k.
  right. now apply AR_epsilon_sign_dec_pos with k.
Defined.
End sign.

Ltac AR_solve_pos_loop k :=
 (apply AR_epsilon_sign_dec_pos with k;
  vm_compute;
  match goal with
  | |- Gt ≡ Gt => reflexivity
  | |- Lt ≡ Gt => fail 2 "AR number is negative"
  end) || AR_solve_pos_loop (k - 8)%Z.

Tactic Notation "AR_solve_pos" constr(k) := AR_solve_pos_loop k.
Tactic Notation "AR_solve_pos" := AR_solve_pos 0%Z.

Tactic Notation "AR_solve_lt" constr(k) := 
  match goal with
  | |- ?X ⋖ ?Y => change (ARpos (Y - X)); AR_solve_pos_loop k
  end.
Tactic Notation "AR_solve_lt" := AR_solve_lt 0%Z.

Ltac AR_solve_apart_loop k :=
  (apply AR_epsilon_sign_dec_apart with k; vm_compute; discriminate) || AR_solve_apart_loop (k - 8)%Z.

Tactic Notation "AR_solve_apart" constr(k) := AR_solve_apart_loop k.
Tactic Notation "AR_solve_apart" := AR_solve_apart 0%Z.
