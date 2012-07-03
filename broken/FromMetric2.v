Require Import Complete metric.
Require Import
  abstract_algebra stdlib_rationals
  orders.orders orders.semirings orders.rings theory.rings.

Instance Qinf_plus_proper : Proper ((=) ==> (=) ==> (=)) Qinf.plus.
Proof.
intros x1 x2 Ex y1 y2 Ey.
destruct x1 as [x1 |]; destruct x2 as [x2 |]; destruct y1 as [y1 |]; destruct y2 as [y2 |];
unfold equiv, Qinf.eq in *; try contradiction; trivial.
change (x1 = x2) in Ex; change (y1 = y2) in Ey; change (x1 + y1 = x2 + y2).
now rewrite Ex, Ey.
Qed.

Program Instance : ∀ x y : Q, Decision (x < y) := λ x y,
  match Qlt_le_dec x y with
  | left H => left H
  | right _ => right _
  end.
Next Obligation. now apply Qle_not_lt. Qed.

Section FromMetricSpace.

Variable X : MetricSpace.

Instance ms_msb : MetricSpaceBall X := λ (e : Qinf) (x y : X),
match e with
| Qinf.finite e' =>
  if (decide (e' = 0))
  then (forall d : Qpos, ball d x y)
  else
    match (decide (0 < e')) with
    | left e'_pos => ball (mkQpos e'_pos) x y
    | right _ => False
    end
| Qinf.infinite => True
end.

Instance : Proper ((=) ==> (≡) ==> (≡) ==> iff) mspc_ball.
Proof.
intros e1 e2 E1 x1 x2 E2 y1 y2 E3.
destruct e1 as [e1 |]; destruct e2 as [e2 |];
try (unfold equiv, Qinf.eq in *; contradiction); try reflexivity.
unfold mspc_ball, ms_msb.
change (e1 = e2) in E1.
destruct (decide (e1 = 0)) as [A1 | A1]; destruct (decide (e2 = 0)) as [A2 | A2];
[now rewrite E2, E3 | rewrite <- E1 in A2; now contradict A2 .. |].
destruct (decide (0 < e1)) as [B1 | B1]; destruct (decide (0 < e2)) as [B2 | B2];
[| exfalso; rewrite <- E1 in B2; now contradict B2 .. | easy].
apply ball_wd; [apply E1 | now rewrite E2 | now rewrite E3].
Qed.

Lemma msp_triangle' (e1 e2: Qpos) (y x z : X) (e : Qpos) :
  (e1 + e2)%Qpos == e -> ball e1 x y -> ball e2 y z -> ball e x z.
Proof.
intros E A1 A2. setoid_replace e with (e1 + e2)%Qpos by easy.
eapply (msp_triangle (msp X)); eauto.
Qed.

Lemma mspc_negative_help (e : Q) : e < 0 → ∀ x y, ~ mspc_ball e x y.
Proof.
intros e_neg x y A. unfold mspc_ball, ms_msb in A.
destruct (decide (e = 0)); [eapply lt_ne; eauto |].
destruct (decide (0 < e)); [eapply lt_flip; eauto | trivial].
Qed.

Lemma mspc_refl_help (e : Q) : 0 ≤ e → Reflexive (mspc_ball e).
Proof.
intros e_nonneg x. unfold mspc_ball, ms_msb.
destruct (decide (e = 0)); [intro d; apply (msp_refl (msp X)) |].
destruct (decide (0 < e)) as [A | A]; [apply (msp_refl (msp X)) |].
apply A, lt_iff_le_ne. now split; [| apply neq_symm].
Qed.

Lemma mspc_symm_help (e : Qinf) : Symmetric (mspc_ball e).
Proof.
intros x y A; unfold mspc_ball, ms_msb in *.
destruct e as [e |]; [| trivial].
destruct (decide (e = 0)); [intro d; now apply (msp_sym (msp X)) |].
now destruct (decide (0 < e)); [apply (msp_sym (msp X)) |].
Qed.

(*Lemma half_n_half (e : Q) : e / 2 + e / 2 = e.
Proof. field; discriminate. Qed.*)

Lemma mspc_triangle_0 (e : Q) (x y z : X) :
   mspc_ball 0 x y → mspc_ball e y z → mspc_ball e x z.
Proof.
intros A1 A2. unfold mspc_ball, ms_msb in *; simpl in A1.
destruct (decide (e = 0)).
(* intro d; setoid_replace d with (d * (1#2) + d * (1#2))%Qpos. *)
+ intros [d d_pos]. assert (hd_pos : (0 < d / 2)%Q) by (apply Q.Qmult_lt_0_compat; auto with qarith).
  apply (msp_triangle' (mkQpos hd_pos) (mkQpos hd_pos) y); [| apply A1 | apply A2].
  change (d / 2 + d / 2 = d); field; discriminate.
+ destruct (decide (0 < e)) as [E | E]; [| contradiction].
  apply (msp_closed (msp X)). intro d.
  apply (msp_triangle' d (mkQpos E) y); [apply plus_comm | apply A1 | apply A2].
Qed.

Lemma mspc_triangle_help (e1 e2 : Q) (x y z : X) :
   mspc_ball e1 x y → mspc_ball e2 y z → mspc_ball (e1 + e2) x z.
Proof.
intros A1 A2. generalize A1 A2; intros A1' A2'.
unfold mspc_ball, ms_msb in A1. destruct (decide (e1 = 0)) as [E1 | E1].
+ change ((e1 : Qinf) + (e2 : Qinf)) with (Qinf.finite (e1 + e2)%mc).
  rewrite E1, plus_0_l. rewrite E1 in A1'. now apply mspc_triangle_0 with (y := y).
+ unfold mspc_ball, ms_msb in A2. destruct (decide (e2 = 0)) as [E2 | E2].
  - change ((e1 : Qinf) + (e2 : Qinf)) with (Qinf.finite (e1 + e2)%mc).
    rewrite E2, plus_0_r. rewrite E2 in A2'. apply mspc_symm_help.
    now apply mspc_triangle_0 with (y := y); apply mspc_symm_help.
  - destruct (decide (0 < e1)) as [e1_pos | ?]; destruct (decide (0 < e2)) as [e2_pos | ?];
    [| contradiction ..].
    assert (0 < e1 + e2) by solve_propholds. assert (e1 + e2 ≠ 0) by solve_propholds.
    unfold mspc_ball, ms_msb; simpl.
    destruct (decide (e1 + e2 = 0)); [contradiction |].
    destruct (decide (0 < e1 + e2)) as [pos | nonpos]; [| contradiction].
    setoid_replace (mkQpos pos) with (Qpos_plus (mkQpos e1_pos) (mkQpos e2_pos)) by easy.
    now apply (msp_triangle (msp X)) with (b := y).
Qed.

Lemma mspc_ball_pos {e : Q} (e_pos : 0 < e) (x y : X) :
  mspc_ball e x y <-> ball (mkQpos e_pos) x y.
Proof.
unfold mspc_ball, ms_msb.
destruct (decide (e = 0)); [exfalso; now apply (lt_ne 0 e) |].
destruct (decide (0 < e)) as [e_pos' | ?]; [now apply (ball_wd X) | contradiction].
Qed.

Lemma mspc_closed_help (e : Q) (x y : X) :
   (∀ d : Q, 0 < d → mspc_ball (e + d) x y) → mspc_ball e x y.
Proof.
intro C. unfold mspc_ball, ms_msb.
destruct (decide (e = 0)) as [e_zero | e_nonzero].
+ intros [d d_pos]; specialize (C d d_pos). rewrite e_zero, plus_0_l in C.
  now apply (mspc_ball_pos d_pos) in C.
+ destruct (decide (0 < e)) as [e_pos | e_nonpos].
  - apply (msp_closed (msp X)). intros [d d_pos]; specialize (C d d_pos).
    assert (pos : 0 < e + d) by solve_propholds.
    apply (mspc_ball_pos pos) in C.
    now match goal with |- ball ?r x y => setoid_replace r with (mkQpos pos) by easy end.
  - assert (e / 2 < 0) by (apply neg_pos_mult; now destruct (lt_trichotomy e 0) as [? | [? | ?]]).
    assert (he_pos : 0 < -(e/2)) by now apply flip_neg_negate.
    eapply mspc_negative_help; [| apply (C _ he_pos)].
    now mc_setoid_replace (e - e / 2) with (e / 2) by (field; discriminate).
Qed.

Instance : ExtMetricSpaceClass X.
Proof.
constructor.
+ apply _.
+ intros; apply I.
+ apply mspc_negative_help.
+ apply mspc_refl_help.
+ apply mspc_symm_help.
+ apply mspc_triangle_help.
+ apply mspc_closed_help.
Qed.

End FromMetricSpace.


