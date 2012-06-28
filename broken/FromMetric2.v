Require Import Complete metric.
Require Import
  abstract_algebra stdlib_rationals
  orders.orders theory.rings.

Program Instance : ∀ x y : Q, Decision (x < y) := λ x y,
  match Qlt_le_dec x y with
  | left H => left H
  | right _ => right _
  end.
Next Obligation. now apply Qle_not_lt. Qed.

Section Conversion.

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

Lemma half_n_half (e : Q) : e / 2 + e / 2 = e.
Proof. field; (change (not (2 ≡ 0)%Z); discriminate). Qed.

Lemma mspc_triangle_0 (e : Q) (x y z : X) :
   mspc_ball 0 x y → mspc_ball e y z → mspc_ball e x z.
Proof.
intros A1 A2. unfold mspc_ball, ms_msb in *; simpl in A1.
destruct (decide (e = 0)).
(* intro d; setoid_replace d with (d * (1#2) + d * (1#2))%Qpos. *)
+ intros [d d_pos]. assert (hd_pos : (0 < d / 2)%Q) by (apply Q.Qmult_lt_0_compat; auto with qarith).
  apply (msp_triangle' (mkQpos hd_pos) (mkQpos hd_pos) y); [| apply A1 | apply A2].
  apply half_n_half.
+ destruct (decide (0 < e)) as [E | E]; [| contradiction].
  apply (msp_closed (msp X)). intro d.
  apply (msp_triangle' d (mkQpos E) y); [| apply A1 | apply A2].
  destruct d as [d d_pos]; change (d + e = e + d); ring.
Qed.

Instance : ExtMetricSpaceClass X.
Proof.
constructor.
+ apply _.
+ intros; apply I.
+ intros e e_neg x y A. unfold mspc_ball, ms_msb in A.
  destruct (decide (e = 0)); [eapply lt_ne; eauto |].
  destruct (decide (0 < e)); [eapply lt_flip; eauto | trivial].
+ intros e e_nonneg x. unfold mspc_ball, ms_msb.
  destruct (decide (e = 0)); [intro d; apply (msp_refl (msp X)) |].
  destruct (decide (0 < e)) as [A | A]; [apply (msp_refl (msp X)) |].
  apply A, lt_iff_le_ne. now split; [| apply neq_symm].
+ intros e x y A; unfold mspc_ball, ms_msb in *.
  destruct e as [e |]; [| trivial].
  destruct (decide (e = 0)); [intro d; now apply (msp_sym (msp X)) |].
  now destruct (decide (0 < e)); [apply (msp_sym (msp X)) |].
+ intros e1 e2 x y z A1 A2.
  destruct (decide (e1 = 0)) as [E1 | E1].
  - rewrite E1 in A1 |- *; rewrite plus_0_l.
    now apply mspc_triangle_0 with (y := y).
  - 
unfold mspc_ball, ms_msb in A1.

