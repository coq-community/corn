Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import
 Coq.Unicode.Utf8 Coq.Program.Program
 CoRN.reals.fast.CRArith CoRN.reals.fast.CRabs
 CoRN.tactics.Qauto Coq.QArith.Qround CoRN.model.metric2.Qmetric
 (*stdlib_omissions.P
 stdlib_omissions.Z
 stdlib_omissions.Q
 stdlib_omissions.N*).

Require Qinf QnonNeg QnnInf CRball.
Import
  QnonNeg Qinf.notations QnonNeg.notations QnnInf.notations CRball.notations
  Qinf.coercions
  Qabs propholds.

Require Import CoRN.ode.metric CoRN.ode.FromMetric2 CoRN.ode.AbstractIntegration CoRN.ode.SimpleIntegration CoRN.ode.BanachFixpoint.
Require Import MathClasses.interfaces.canonical_names MathClasses.misc.decision MathClasses.misc.setoid_tactics MathClasses.misc.util.
Require Import MathClasses.implementations.stdlib_rationals MathClasses.theory.rationals.
Close Scope uc_scope. (* There is a leak in some module *)
Open Scope signature_scope. (* To interpret "==>" *)

Bind Scope mc_scope with Q.

Local Notation ball := mspc_ball.

Lemma Qinf_lt_le (x y : Qinf) : x < y → x ≤ y.
Proof.
destruct x as [x |]; destruct y as [y |]; [| easy..].
change (x < y -> x ≤ y). intros; solve_propholds.
Qed.

Instance Q_nonneg (rx : QnonNeg) : PropHolds (@le Q _ 0 (proj1_sig rx)).
Proof. intros. apply (proj2_sig rx). Qed.

Instance Q_nonempty : NonEmpty Q := inhabits 0.

Program Instance sig_nonempty `{ExtMetricSpaceClass X}
  (r : QnonNeg) (x : X) : NonEmpty (sig (ball (proj1_sig r) x)) := inhabits x.
Next Obligation. apply mspc_refl; solve_propholds. Qed.

Instance prod_nonempty `{NonEmpty X, NonEmpty Y} : NonEmpty (X * Y).
Proof.
(* In order not to refer to the name of the variable that has type NonEmpty X *)
match goal with H : NonEmpty X |- _ => destruct H as [x] end.
match goal with H : NonEmpty Y |- _ => destruct H as [y] end.
exact (inhabits (x, y)).
Qed.

(* The following instances are needed to show that Lipschitz functions are
uniformly continuous: metric.lip_uc *)
Global Instance Qmsd : MetricSpaceDistance Q := λ x y, abs (x - y).

Global Instance Qmsc
  : @MetricSpaceClass Q (msp_mspc_ball Q_as_MetricSpace)
                      (msp_mspc_ball_ext Q_as_MetricSpace) Qmsd.
Proof.
  intros x1 x2; apply gball_Qabs; reflexivity.
Qed.

(*Instance Q_nonempty : NonEmpty Q := inhabits 0%Q.*)

Section Extend.

Context `{ExtMetricSpaceClass Y} (a : Q) (r : QnonNeg).

(* Sould [r] be [Q] or [QnonNeg]? If [r : Q], then [extend] below is not
necessarily continuous. This may be OK because we could add the premise [0
≤ r] to the lemma that says that [extend] is Lipschitz. However, the
definition below is not well-typed because if [r < 0], then [ball r a (a -
r)] is false, so we can't apply [f] to [a - r]. So we assume [r : QnonNeg]. *)

Lemma mspc_ball_edge_l
  : @ball Q (msp_mspc_ball Q_as_MetricSpace) (proj1_sig r) a (a - `r).
Proof.
destruct r as [e ?]; simpl.
apply gball_Qabs. mc_setoid_replace (a - (a - e)) with e by ring.
change (abs e ≤ e). rewrite abs.abs_nonneg; [reflexivity | trivial].
Qed.

Lemma mspc_ball_edge_r
  : @ball Q (msp_mspc_ball Q_as_MetricSpace) (proj1_sig r) a (a + `r).
Proof.
destruct r as [e ?]; simpl.
apply Qmetric.gball_Qabs. mc_setoid_replace (a - (a + e)) with (-e) by ring.
change (abs (-e) ≤ e). rewrite abs.abs_negate, abs.abs_nonneg; [reflexivity | trivial].
Qed.

Context (f : sig (@ball Q (msp_mspc_ball Q_as_MetricSpace) (proj1_sig r) a) -> Y).

(* Since the following is a Program Definition, we could write [f (a - r)]
and prove the obligation [mspc_ball r a (a - r)]. However, this obligation
would depend on x and [H1 : x ≤ a - r] even though they are not used in the
proof. So, if [H1 : x1 ≤ a - r] and [H2 : x2 ≤ a - r], then [extend x1]
would reduce to [f ((a - r) ↾ extend_obligation_1 x1 H1)] and [extend x2]
would reduce to [f ((a - r) ↾ extend_obligation_1 x2 H2)]. To apply
mspc_refl (see [extend_uc] below), we would need to prove that these
applications of f are equal, i.e., f is a morphism that does not depend on
the second component of the pair. So instead we prove mspc_ball_edge_l and
mspc_ball_edge_r, which don't depend on x. *)

Program Definition extend : Q -> Y :=
  λ x, if (decide (x < a - (proj1_sig r)))
       then f ((a - (r : Q)) ↾ mspc_ball_edge_l)
       else if (decide (a + r < x))
            then f ((a + r) ↾ mspc_ball_edge_r)
            else f (x ↾ _).
Next Obligation.
apply mspc_ball_Qle.
apply orders.not_lt_le_flip in H1. apply orders.not_lt_le_flip in H2. now split.
Qed.

(*
Global Instance extend_lip `{!IsLipschitz f L} : IsLipschitz extend L.
Proof with (assumption || (apply orders.le_flip; assumption) || reflexivity).
constructor; [apply (lip_nonneg f L) |].
intros x1 x2 e A.
assert (0 ≤ e) by now apply (radius_nonneg x1 x2).
assert (0 ≤ L) by apply (lip_nonneg f L).
assert (a - proj1_sig r ≤ a + proj1_sig r) by
  (destruct r; simpl; transitivity a;
    [apply rings.nonneg_minus_compat | apply semirings.plus_le_compat_r]; (easy || reflexivity)).
unfold extend.
destruct (decide (x1 ≤ a - proj1_sig r)); destruct (decide (x2 ≤ a - proj1_sig r)).
* apply mspc_refl; solve_propholds.
* destruct (decide (a + proj1_sig r ≤ x2));  apply (lip_prf f L).
  + apply (nested_balls A)...
  + apply (nested_balls A)...
* destruct (decide (a + proj1_sig r ≤ x1)); apply (lip_prf f L).
  + apply mspc_symm; apply mspc_symm in A. apply (nested_balls A)...
  + apply mspc_symm; apply mspc_symm in A. apply (nested_balls A)...
* destruct (decide (a + proj1_sig r ≤ x1)); destruct (decide (a + proj1_sig r ≤ x2));
  apply (lip_prf f L).
  + apply mspc_refl; solve_propholds.
  + apply mspc_symm; apply mspc_symm in A. apply (nested_balls A)...
  + apply (nested_balls A)...
  + apply A.
Qed.
*)

Global Instance extend_uc : ∀ mu_f : Q → Qinf,
         @IsUniformlyContinuous _
           (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig r) a)) Y H f mu_f
         → @IsUniformlyContinuous Q (msp_mspc_ball Q_as_MetricSpace) Y H extend mu_f.
Proof with (solve_propholds || (apply orders.not_lt_le_flip; assumption) || reflexivity).
  intros. constructor.
  apply (@uc_pos _ (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig r) a)) Y H f mu_f). exact H1.
intros e x1 x2 e_pos A.
assert (a - proj1_sig r ≤ a + proj1_sig r) by
  (destruct r; simpl; transitivity a;
    [apply rings.nonneg_minus_compat | apply semirings.plus_le_compat_r]; (easy || reflexivity)).
unfold extend.
destruct (decide (x1 < a - proj1_sig r)); destruct (decide (x2 < a - proj1_sig r)).
* apply mspc_refl...
* destruct (decide (a + proj1_sig r < x2));
  apply (@uc_prf _ (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig r) a)) Y H f mu_f); trivial.
  + apply (nested_balls _ _ A)...
  + apply (nested_balls _ _ A)...
* destruct (decide (a + proj1_sig r < x1));
    apply (@uc_prf _ (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig r) a)) Y H f mu_f); trivial.
  + apply @mspc_symm.
    exact (@sig_mspc Q (msp_mspc_ball Q_as_MetricSpace)
                         (msp_mspc_ball_ext Q_as_MetricSpace)
                         (ball (proj1_sig r) a)).
    apply @mspc_symm in A.
    apply (nested_balls _ _ A)...
    exact (msp_mspc_ball_ext Q_as_MetricSpace).
  + apply @mspc_symm.
    exact (@sig_mspc Q (msp_mspc_ball Q_as_MetricSpace)
                         (msp_mspc_ball_ext Q_as_MetricSpace)
                         (ball (proj1_sig r) a)).
    apply @mspc_symm in A.
    apply (nested_balls _ _ A)...
    exact (msp_mspc_ball_ext Q_as_MetricSpace).
* destruct (decide (a + proj1_sig r < x1)); destruct (decide (a + proj1_sig r < x2));
  apply (@uc_prf _ (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig r) a)) Y H f mu_f); trivial.
  + apply @mspc_refl'.
    exact (@sig_mspc Q (msp_mspc_ball Q_as_MetricSpace)
                         (msp_mspc_ball_ext Q_as_MetricSpace)
                         (ball (proj1_sig r) a)).
    apply Qinf_lt_le.
    apply (@uc_pos _ (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig r) a)) Y H f mu_f). assumption. assumption. 
  + apply @mspc_symm.
    exact (@sig_mspc Q (msp_mspc_ball Q_as_MetricSpace)
                         (msp_mspc_ball_ext Q_as_MetricSpace)
                         (ball (proj1_sig r) a)).
    apply @mspc_symm in A.
    apply (nested_balls _ _ A)...
    exact (msp_mspc_ball_ext Q_as_MetricSpace).
  + apply (nested_balls _ _ A)...
Qed.

End Extend.

Lemma extend_inside
: ∀ {Y : CProp} {H : MetricSpaceBall Y} { _ : @ExtMetricSpaceClass Y H },
  ∀ (a x : Q) (r : QnonNeg),
    @ball Q (msp_mspc_ball Q_as_MetricSpace) (proj1_sig r) a x
    → ∃ p : @ball Q (msp_mspc_ball Q_as_MetricSpace) (proj1_sig r) a x,
    ∀ f : sig (fun x : Q => @ball Q (msp_mspc_ball Q_as_MetricSpace) (proj1_sig r) a x) → Y,
      @extend Y a r f x = f (x ↾ p).
Proof.
  intros Y H H0 a x r A. 
  apply mspc_ball_Qle in A. destruct A as [A1 A2]. unfold extend.
destruct (decide (x < a - proj1_sig r)) as [H1 | H1].
(* [proj1_sig] is needed because otherwise [Negate QnonNeg] is unsatisfied.
Backtick [`] is not enough because the goal is not simplified. *)
* apply orders.lt_not_le_flip in H1; elim (H1 A1).
* destruct (decide (a + proj1_sig r < x)) as [H2 | H2].
  + apply orders.lt_not_le_flip in H2; elim (H2 A2).
  + eexists; intro f; reflexivity.
Qed.

Section Bounded.

Class Bounded {X : Type} (f : X -> CR) (M : Q) := bounded : forall x, abs (f x) ≤ 'M.

Global Instance comp_bounded {X Y : Type} (f : X -> Y) (g : Y -> CR)
  `{!Bounded g M} : Bounded (g ∘ f) M.
Proof. intro x; unfold Basics.compose; apply bounded. Qed.

Global Instance extend_bounded {a : Q} {r : QnonNeg}
       (f : {x | @ball Q (msp_mspc_ball Q_as_MetricSpace) (proj1_sig r) a x} -> CR)
  `{!Bounded f M} : Bounded (extend a r f) M.
Proof.
intro x. unfold extend.
destruct (decide (x < a - proj1_sig r));
  [| destruct (decide (a + proj1_sig r < x))]; apply bounded.
Qed.

Lemma bounded_nonneg {X : Type} (f : X -> CR) `{!Bounded f M} `{NonEmpty X} :
  (*PropHolds*) (0 ≤ M).
Proof.
match goal with H : NonEmpty X |- _ => destruct H as [x] end.
apply CRle_Qle. change (@zero CR _  ≤ 'M). transitivity (abs (f x)).
+ apply CRabs_nonneg.
+ apply bounded.
Qed.

End Bounded.

Global Instance bounded_int_uc {f : Q -> CR} {M : Q}
       `{!Bounded f M}
       `{!@IsUniformlyContinuous
          Q (msp_mspc_ball Q_as_MetricSpace) 
          CR (msp_mspc_ball CR) 
          f mu_f} (x0 : Q) :
  @IsUniformlyContinuous
    Q (msp_mspc_ball Q_as_MetricSpace) 
    CR (msp_mspc_ball CR) 
    (λ x, int f x0 x) (lip_modulus M).
Proof.
constructor.
+ intros. apply lip_modulus_pos; [apply (bounded_nonneg f) | easy].
+ intros e x1 x2 e_pos A. apply mspc_ball_CRabs.
  pose proof (CRabs_proper _ _ (int_diff f x0 x1 x2)).
  apply ball_0 in H0. rewrite H0. clear H0.
  transitivity ('(abs (x1 - x2) * M)).
  - apply int_abs_bound; [apply _ |]. intros x _; apply bounded.
  - apply CRle_Qle. change (abs (x1 - x2) * M ≤ e).
    unfold lip_modulus in A. destruct (decide (M = 0)) as [E | E].
    rewrite E, rings.mult_0_r. now apply orders.lt_le. (* why does [solve_propholds] not work? *)
    apply mspc_ball_Qabs in A. assert (0 ≤ M) by apply (bounded_nonneg f).
    apply (orders.order_preserving (.* M)) in A.
    now mc_setoid_replace (e / M * M) with e in A by (field; solve_propholds).
Qed.

Section Picard.

Context (x0 : Q) (y0 : CR) (rx ry : QnonNeg).

Notation sx := (sig (@ball Q (msp_mspc_ball Q_as_MetricSpace) (proj1_sig rx) x0)).
Notation sy := (sig (@ball CR (msp_mspc_ball CR) (proj1_sig ry) y0)).

Context (v : sx * sy -> CR) `{!Bounded v M}
        `{!@IsUniformlyContinuous
           _ (@Linf_product_metric_space_ball
                _ (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball r a))
                _ (@sig_mspc_ball CR (msp_mspc_ball CR) (@ball CR (msp_mspc_ball CR) (proj1_sig ry) y0)) )
           CR (msp_mspc_ball CR) 
           v mu_v} (L : Q).

Hypothesis v_lip : forall x : sx, IsLipschitz (λ y, v (x, y)) L.

Hypothesis L_rx : L * (proj1_sig rx) < 1.

Context {rx_M : PropHolds (`rx * M ≤ proj1_sig ry)}.

Instance L_nonneg : PropHolds (0 ≤ L).
Proof.
  assert (@ball Q (msp_mspc_ball Q_as_MetricSpace) (proj1_sig rx) x0 x0) as B.
  { apply @mspc_refl.
    exact (msp_mspc_ball_ext Q_as_MetricSpace).
    solve_propholds. }
  apply (lip_nonneg (λ y, v ((x0 ↾ B), y)) L).
Qed.

(* Needed to apply Banach fixpoint theorem, which requires a finite
distance between any two points *)
Global Instance uc_msd
     : MetricSpaceDistance
         (@UniformlyContinuous
            sx (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace)
                              (@ball Q (msp_mspc_ball Q_as_MetricSpace) (proj1_sig rx) x0))
            sy
            (@sig_mspc_ball CR (msp_mspc_ball CR) (@ball CR (msp_mspc_ball CR) (proj1_sig ry) y0)))
  := λ f1 f2, 2 * proj1_sig ry.

Global Instance uc_msc
  : @MetricSpaceClass
      _ _
      (@Linf_func_metric_space_class sx sy
            _ _ 
            (@sig_nonempty Q (msp_mspc_ball Q_as_MetricSpace)
               (msp_mspc_ball_ext Q_as_MetricSpace) rx x0)
            _ _)
      uc_msd.
Proof.
  intros f1 f2. unfold msd, uc_msd. intro x.
  apply (@mspc_triangle' CR (msp_mspc_ball CR)
                         (msp_mspc_ball_ext CR) (proj1_sig ry) (proj1_sig ry) y0).
+ change (proj1_sig ry + proj1_sig ry = 2 * (proj1_sig ry)). ring.
+ apply mspc_symm; apply (proj2_sig (func f1 x)).
+ apply (proj2_sig (func f2 x)).
Qed.

(*Check _ : MetricSpaceClass sx.
Check _ : IsUniformlyContinuous v _.

Context (f : sx -> sy) `{!IsUniformlyContinuous f mu_f}.

Check _ : IsUniformlyContinuous ((@Datatypes.id sx) ∘ (@Datatypes.id sx)) _.

Check _ : IsUniformlyContinuous (extend x0 rx (v ∘ (together Datatypes.id f) ∘ diag)) _.

Check _ : IsLocallyUniformlyContinuous (extend x0 rx (v ∘ (together Datatypes.id f) ∘ diag)) _*)
Definition picard' (f : sx -> sy)
           `{!@IsUniformlyContinuous
              sx (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
              sy (@sig_mspc_ball CR (msp_mspc_ball CR) (ball (proj1_sig ry) y0))
              f mu_f} : Q -> CR :=
  λ x, y0 +
       @int (extend x0 rx (v ∘ (together Datatypes.id f) ∘ diag))
(@Integral_instance_0
   (extend x0 rx (v ∘ (together Datatypes.id f) ∘ diag))
       _
       (@uc_ulc Q (msp_mspc_ball Q_as_MetricSpace) CR (msp_mspc_ball CR)
                (extend x0 rx (v ∘ (together Datatypes.id f) ∘ diag))
          _
          (@extend_uc CR (msp_mspc_ball CR) (msp_mspc_ball_ext CR) x0 rx
             _ _
             (@compose_uc sx 
                (sx and sx) CR
                (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
                (@Linf_product_metric_space_ball sx 
                   (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
                   sx
                   (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0)))
                (@Linf_product_metric_space_class sx
                   (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
                   (@sig_mspc Q (msp_mspc_ball Q_as_MetricSpace)
                      (msp_mspc_ball_ext Q_as_MetricSpace) 
                      (ball (proj1_sig rx) x0)) sx
                   (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
                   (@sig_mspc Q (msp_mspc_ball Q_as_MetricSpace)
                      (msp_mspc_ball_ext Q_as_MetricSpace) 
                      (ball (proj1_sig rx) x0))) (msp_mspc_ball CR)
                (@diag sx)
                (v
                 ∘ @together sx sx sx sy
                     (@Datatypes.id sx) f) 
                (lip_modulus 1)
                (@comp_inf Q Qinf
                   (λ e : Q,
                      @minmax.min Qinf Qinf_le metric.Decision_instance_0
                        (lip_modulus 1 e) (mu_f e)) mu_v Qinf.infinite)
                (@lip_uc sx
                   (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
                   (sx and sx)
                   (@Linf_product_metric_space_ball sx
                      (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
                      sx
                      (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0)))
                   (@sig_mspc Q (msp_mspc_ball Q_as_MetricSpace)
                      (msp_mspc_ball_ext Q_as_MetricSpace) 
                      (ball (proj1_sig rx) x0)) (@sig_msd Q (ball (proj1_sig rx) x0) Qmsd)
                   (@sig_mspc_distance Q_as_MetricSpace
                      (msp_mspc_ball Q_as_MetricSpace)
                      (msp_mspc_ball_ext Q_as_MetricSpace) 
                      (ball (proj1_sig rx) x0) Qmsd Qmsc)
                   (@Linf_product_metric_space_class sx
                      (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
                      (@sig_mspc Q (msp_mspc_ball Q_as_MetricSpace)
                         (msp_mspc_ball_ext Q_as_MetricSpace)
                         (ball (proj1_sig rx) x0)) sx
                      (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
                      (@sig_mspc Q (msp_mspc_ball Q_as_MetricSpace)
                         (msp_mspc_ball_ext Q_as_MetricSpace)
                         (ball (proj1_sig rx) x0))) (@diag sx) 1
                   (@diag_lip sx
                      (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
                      (@sig_mspc Q (msp_mspc_ball Q_as_MetricSpace)
                         (msp_mspc_ball_ext Q_as_MetricSpace)
                         (ball (proj1_sig rx) x0))))
                (@compose_uc (sx and sx)
                   (sx and sy) CR
                   (@Linf_product_metric_space_ball sx
                      (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
                      sx
                      (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0)))
                   (@Linf_product_metric_space_ball sx
                      (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
                      sy
                      (@sig_mspc_ball CR (msp_mspc_ball CR) (ball (proj1_sig ry) y0)))
                   (@Linf_product_metric_space_class sx
                      (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
                      (@sig_mspc Q (msp_mspc_ball Q_as_MetricSpace)
                         (msp_mspc_ball_ext Q_as_MetricSpace)
                         (ball (proj1_sig rx) x0)) sy
                      (@sig_mspc_ball CR (msp_mspc_ball CR) (ball (proj1_sig ry) y0))
                      (@sig_mspc CR (msp_mspc_ball CR)
                         (msp_mspc_ball_ext CR) 
                         (ball (proj1_sig ry) y0))) (msp_mspc_ball CR)
                   (@together sx sx
                      sx sy
                      (@Datatypes.id sx) f) v
                   (λ e : Q,
                      @minmax.min Qinf Qinf_le metric.Decision_instance_0
                        (lip_modulus 1 e) (mu_f e)) mu_v
                   (@together_uc sx
                      (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
                      (@sig_mspc Q (msp_mspc_ball Q_as_MetricSpace)
                         (msp_mspc_ball_ext Q_as_MetricSpace)
                         (ball (proj1_sig rx) x0)) sx
                      (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
                      (@sig_mspc Q (msp_mspc_ball Q_as_MetricSpace)
                         (msp_mspc_ball_ext Q_as_MetricSpace)
                         (ball (proj1_sig rx) x0)) sx
                      (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
                      (@sig_mspc Q (msp_mspc_ball Q_as_MetricSpace)
                         (msp_mspc_ball_ext Q_as_MetricSpace)
                         (ball (proj1_sig rx) x0)) sy
                      (@sig_mspc_ball CR (msp_mspc_ball CR) (ball (proj1_sig ry) y0))
                      (@sig_mspc CR (msp_mspc_ball CR)
                         (msp_mspc_ball_ext CR) 
                         (ball (proj1_sig ry) y0)) (@Datatypes.id sx) f
                      (lip_modulus 1)
                      (@lip_uc sx
                         (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace)
                            (ball (proj1_sig rx) x0)) sx
                         (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace)
                            (ball (proj1_sig rx) x0))
                         (@sig_mspc Q (msp_mspc_ball Q_as_MetricSpace)
                            (msp_mspc_ball_ext Q_as_MetricSpace)
                            (ball (proj1_sig rx) x0)) (@sig_msd Q (ball (proj1_sig rx) x0) Qmsd)
                         (@sig_mspc_distance Q_as_MetricSpace
                            (msp_mspc_ball Q_as_MetricSpace)
                            (msp_mspc_ball_ext Q_as_MetricSpace)
                            (ball (proj1_sig rx) x0) Qmsd Qmsc)
                         (@sig_mspc Q (msp_mspc_ball Q_as_MetricSpace)
                            (msp_mspc_ball_ext Q_as_MetricSpace)
                            (ball (proj1_sig rx) x0)) (@Datatypes.id sx) 1
                         (@id_lip sx
                            (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace)
                               (ball (proj1_sig rx) x0))
                            (@sig_mspc Q (msp_mspc_ball Q_as_MetricSpace)
                               (msp_mspc_ball_ext Q_as_MetricSpace)
                               (ball (proj1_sig rx) x0)))) mu_f _)
                   _)))))

            x0 x.

(*
Variable f : UniformlyContinuous sx sy.
Check _ : IsUniformlyContinuous f _.
Check _ : IsLocallyLipschitz (extend x0 rx (v ∘ (together Datatypes.id f) ∘ diag)) _.
Check _ : Integral (extend x0 rx (v ∘ (together Datatypes.id f) ∘ diag)).
Check _ : Integrable (extend x0 rx (v ∘ (together Datatypes.id f) ∘ diag)).
Check _ : IsLocallyLipschitz (λ x : Q, int (extend x0 rx (v ∘ (together Datatypes.id f) ∘ diag)) x0 x) _.
Check _ : IsLocallyLipschitz (picard' f) _. Goal True.
assert (0 ≤ proj1_sig rx). apply (proj2_sig rx).
Check _ : PropHolds (0 ≤ proj1_sig rx).
Check _ : IsLipschitz (restrict (picard' f) x0 rx) _.
*)

Definition picard'' (f : @UniformlyContinuous sx
         (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
         sy (@sig_mspc_ball CR (msp_mspc_ball CR) (ball (proj1_sig ry) y0)) )
: @UniformlyContinuous sx
                       (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0)) CR
                       (msp_mspc_ball CR).
Proof.
  apply (@Build_UniformlyContinuous
           sx (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
           CR (msp_mspc_ball CR) 
           (@restrict Q (msp_mspc_ball Q_as_MetricSpace) CR (picard' f) x0 (proj1_sig rx))
           ((λ _ _ e : Q,
              @minmax.min Qinf Qinf_le metric.Decision_instance_0
                          (lip_modulus 0 (e / 2)) (lip_modulus M (e / 2))) x0 (proj1_sig rx))
           (@luc_prf Q (msp_mspc_ball Q_as_MetricSpace) CR 
                     (msp_mspc_ball CR)
                     _ _
                     (@uc_ulc Q (msp_mspc_ball Q_as_MetricSpace) CR 
                              (msp_mspc_ball CR)
                              _ _

                              (@sum_uc Q (msp_mspc_ball Q_as_MetricSpace)
                                       (msp_mspc_ball_ext Q_as_MetricSpace) 
                                       (λ _ : Q, y0) _ _ _ _ _))
                     x0 (proj1_sig rx))).
Defined.

(* Needed below to be able to apply (order_preserving (.* M)) *)
Instance M_nonneg : PropHolds (0 ≤ M)
  := @bounded_nonneg (sx and sy) v M Bounded0
  (@prod_nonempty sx 
     (@sig_nonempty Q (msp_mspc_ball Q_as_MetricSpace)
        (msp_mspc_ball_ext Q_as_MetricSpace) rx x0)
     sy (@sig_nonempty CR (msp_mspc_ball CR) (msp_mspc_ball_ext CR) ry y0)).

Lemma picard_sy (f : UniformlyContinuous sx sy) (x : sx) : ball (proj1_sig ry) y0 (picard'' f x).
Proof.
destruct x as [x x_sx]. unfold picard''; simpl.
unfold restrict, Basics.compose; simpl.
unfold picard'. apply mspc_ball_CRabs.
assert (forall b, abs (y0 - (y0 + b)) [=] abs b).
{ intro b. pose proof (CRabs_negate b).
  apply ball_0 in H0. rewrite <- H0.
  rewrite <- ball_0. 
  apply CRabs_proper. apply ball_0.
  rewrite rings.negate_plus_distr, plus_assoc.
  rewrite rings.plus_negate_r, rings.plus_0_l. reflexivity. } 
rewrite H0. clear H0.
transitivity ('(abs (x - x0) * M)).
+ apply int_abs_bound; [apply _ |]. (* Should not be required *)
  intros t A.
  assert (@mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (proj1_sig rx) x0 t) as A1.
  apply (mspc_ball_convex x0 x).
  apply (@mspc_refl Q). exact (msp_mspc_ball_ext Q_as_MetricSpace).
  apply (proj2_sig rx). trivial. trivial.
  apply (extend_inside (Y:=CR)) in A1.
  destruct A1 as [p A1].
  specialize (A1 (v ∘ together Datatypes.id f ∘ diag)).
  pose proof (CRabs_proper _ _ A1). apply ball_0 in H0.
  rewrite H0. clear H0. apply bounded.
+ apply CRle_Qle. change (abs (x - x0) * M ≤ proj1_sig ry). transitivity (`rx * M).
  - now apply (orders.order_preserving (.* M)), mspc_ball_Qabs_flip.
  - apply rx_M.
Qed.

(*Require Import Integration.*)

Definition picard (f : @UniformlyContinuous sx
        (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
        sy (@sig_mspc_ball CR (msp_mspc_ball CR) (ball (proj1_sig ry) y0)))
  : @UniformlyContinuous sx
           (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
           sy
           (@sig_mspc_ball CR (msp_mspc_ball CR) (ball (proj1_sig ry) y0)).
Proof.
set (g := picard'' f).
set (h x := exist _ (g x) (picard_sy f x)).
assert (@IsUniformlyContinuous sx
      (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
      sy (@sig_mspc_ball CR (msp_mspc_ball CR) (ball (proj1_sig ry) y0)) h
      (@uc_mu sx
         (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0)) CR
         (msp_mspc_ball CR) g)) as C.
{ constructor.
  + exact (@uc_pos sx
                _ CR (msp_mspc_ball CR) g _
                (@uc_proof sx
                   (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
                   CR (msp_mspc_ball CR) g)).
  + intros e x1 x2 e_pos A.
    exact (@uc_prf sx _ CR (msp_mspc_ball CR) g _
                  (@uc_proof sx
                     (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
                     CR (msp_mspc_ball CR) g) e x1 x2 e_pos A). }
exact (Build_UniformlyContinuous _ _ C).
Defined.

Global Instance picard_contraction : IsContraction picard (L * proj1_sig rx).
Proof.
constructor; [| exact L_rx].
constructor; [solve_propholds |].
intros f1 f2 e A [x ?].
change (ball (L * proj1_sig rx * e) (picard' f1 x) (picard' f2 x)).
unfold picard'. apply mspc_ball_CRplus_l, mspc_ball_CRabs.
rewrite <- abs_int_minus. transitivity ('(abs (x - x0) * (L * e))).
+ apply int_abs_bound; [apply _ |]. (* remove [apply _] *)
  intros x' B.
  assert (@ball Q (msp_mspc_ball Q_as_MetricSpace) (proj1_sig rx) x0 x') as B1.
  { apply (mspc_ball_convex x0 x). apply (@mspc_refl Q).
    exact (msp_mspc_ball_ext Q_as_MetricSpace). 
    solve_propholds. trivial. trivial. }
  unfold plus, negate, ext_plus, ext_negate.
  apply (extend_inside (Y:=CR)) in B1. destruct B1 as [p B1].
  assert (forall i j k l : CR, i = j -> k = l -> abs (i-k) [=] abs (j-l)).
  { intros. apply ball_0. apply CRabs_proper.
    apply ball_0. apply ball_0 in H0. apply ball_0 in H1.
    rewrite H0, H1. reflexivity. }
  rewrite (H0 _ _ _ _ (B1 _) (B1 _)). clear H0.
  apply mspc_ball_CRabs. unfold diag, together, Datatypes.id, Basics.compose; simpl.
  apply (lip_prf (λ y, v (_, y)) L), A.
+ apply CRle_Qle.
  mc_setoid_replace (L * proj1_sig rx * e) with ((proj1_sig rx) * (L * e)) by ring.
  assert (0 ≤ e).
  { apply (@radius_nonneg
             _ _
             (@Linf_func_metric_space_class
                sx sy _ _ 
                (@sig_nonempty Q
                               (msp_mspc_ball
                                  Q_as_MetricSpace)
                               (msp_mspc_ball_ext Q_as_MetricSpace) rx x0)
                _ _ ) 
             f1 f2 e A). } 
  change ((abs (x - x0) * (L * e)) ≤ ((proj1_sig rx) * (L * e))).
  apply (orders.order_preserving (.* (L * e))).
  now apply mspc_ball_Qabs_flip.
Qed.

Program Definition f0 :
 @UniformlyContinuous sx
        (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
        sy (@sig_mspc_ball CR (msp_mspc_ball CR) (ball (proj1_sig ry) y0))
  :=
  Build_UniformlyContinuous (λ x, y0) (λ e, Qinf.infinite) _.
Next Obligation.
 eapply (mspc_refl (X:=CR)).
 solve_propholds. Qed.

Next Obligation.
constructor.
+ intros; easy.
+ intros e x1 x2 e_pos B. change (ball e y0 y0). apply mspc_refl; solve_propholds.
Qed.

Lemma ode_solution
  : let f := @fp _ _ _ uc_msd uc_msc _ picard (L * proj1_sig rx) picard_contraction f0 in
    picard f = f.
Proof. apply banach_fixpoint. Qed.

End Picard.

Import theory.rings orders.rings.

Section Computation.

Definition x0 : Q := 0.
Definition y0 : CR := 1.
Definition rx : QnonNeg := (1 # 2)%Qnn.
Definition ry : QnonNeg := 1.

Notation sx := (sig (@ball Q (msp_mspc_ball Q_as_MetricSpace) (proj1_sig rx) x0)). (* Why does Coq still print {x | ball rx x0 x} in full? *)
Notation sy := (sig (@ball CR (msp_mspc_ball CR) (proj1_sig ry) y0)).

Definition v (z : sx * sy) : CR := ` (snd z).
Definition M : Q := 2.
Definition mu_v (e : Q) : Qinf := e.
Definition L : Q := 1.

Instance : Bounded v M.
Proof.
intros [x [y H]]. unfold v; simpl. unfold M, ry, y0 in *.
apply mspc_ball_CRabs in H.
pose proof (CRdistance_CRle 1 1 y) as [_ H1].
specialize (H1 H). destruct H1 as [H1 H2].
change (1 - 1 ≤ y) in H1. change (y ≤ 1 + 1) in H2. change (abs y ≤ 2).
rewrite plus_negate_r in H1. apply CRabs_AbsSmall. split; [| assumption].
change (-2 ≤ y). transitivity (0 : CR); [| easy]. rewrite <- negate_0.
apply flip_le_negate. apply (CRle_trans H1 H2).
Qed.

Instance : @IsUniformlyContinuous
             _ (@Linf_product_metric_space_ball
                  _ (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball r a))
                  _ (@sig_mspc_ball CR (msp_mspc_ball CR) (@ball CR (msp_mspc_ball CR) (proj1_sig ry) y0)) )
           CR (msp_mspc_ball CR) 
           v mu_v.
Proof.
constructor.
* now intros.
* unfold mu_v. intros e z1 z2 e_pos H. now destruct H.
Qed.

Instance v_lip (x : sx) : IsLipschitz (λ y : sy, v (x, y)) L.
Proof.
constructor.
* unfold L. solve_propholds.
* intros y1 y2 e H. unfold L; rewrite mult_1_l. apply H.
Qed.

Lemma L_rx : L * proj1_sig rx < 1.
Proof.
unfold L, rx; simpl. rewrite mult_1_l. change (1 # 2 < 1)%Q. auto with qarith.
Qed.

Instance rx_M : PropHolds (proj1_sig rx * M ≤ proj1_sig ry).
Proof.
  unfold rx, ry, M; simpl.
  rewrite Qmake_Qdiv. change (1 * / 2 * 2 <= 1)%Q.
rewrite <- Qmult_assoc, Qmult_inv_l; [auto with qarith | discriminate].
Qed.

(*Notation ucf := (UniformlyContinuous sx sy).

Check _ : MetricSpaceBall ucf.
Check _ : ExtMetricSpaceClass ucf. (* Why two colons? *)
Check _ : MetricSpaceDistance ucf.
Check _ : MetricSpaceClass ucf.
Check _ : Limit ucf.*)
(* [Check _ : IsContraction (picard x0 y0 rx ry v rx_M) (L * rx)] At this point this does not work *)
(* The following is bad because it creates a proof different from
picard_contraction. Therefore, ode_solution cannot be applied. *)
(*
Instance : IsContraction (picard x0 y0 rx ry v rx_M) (L * rx).
Proof.
apply picard_contraction.
apply v_lip. (* Is this needed because there is an explicit argument before IsLipschitz in picard_contraction? *)
apply L_rx.
Qed.

Check _ : IsContraction (picard x0 y0 rx ry v rx_M) (L * rx).*)

Let f
  : @UniformlyContinuous
      sx (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
      sy (@sig_mspc_ball CR (msp_mspc_ball CR) (ball (proj1_sig ry) y0))
  := @fp _ _
         (@Linf_func_metric_space_class
            sx sy
            (@UniformlyContinuous
               sx (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
               sy (@sig_mspc_ball CR (msp_mspc_ball CR) (ball (proj1_sig ry) y0)))
            (@uniformly_continuous_func
               sx (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball (proj1_sig rx) x0))
               sy (@sig_mspc_ball CR (msp_mspc_ball CR) (ball (proj1_sig ry) y0)))
            (@sig_nonempty Q (msp_mspc_ball Q_as_MetricSpace)
                           (msp_mspc_ball_ext Q_as_MetricSpace) rx x0)
            (@sig_mspc_ball CR (msp_mspc_ball CR) (ball (proj1_sig ry) y0))
            (@sig_mspc CR (msp_mspc_ball CR) (msp_mspc_ball_ext CR)
                       (ball (proj1_sig ry) y0)))
         (uc_msd x0 y0 rx ry) (uc_msc x0 y0 rx ry)
         _
         (@picard x0 y0 rx ry v M Bounded_instance_0 0 0 mu_v
                  IsUniformlyContinuous_instance_0 rx_M)
         _
         (@picard_contraction x0 y0 rx ry v M Bounded_instance_0 _ _ mu_v
                              IsUniformlyContinuous_instance_0 L v_lip L_rx rx_M)
         (f0 x0 y0 rx ry).

(* L_rx should also be declared implicit using Context and omitted from the list of arguments *)

(* When [IsContraction (picard x0 y0 rx ry v rx_M) (L * rx)] did not work,
the error message was 'Error: Cannot infer the implicit parameter H of
fp. Could not find an instance for [MetricSpaceBall (UniformlyContinuous sx sy)]'.
In fact, [MetricSpaceBall (UniformlyContinuous sx sy)] worked fine. *)

(* f is indeed the fixpoint *)

Theorem f_fixpoint :
  @picard x0 y0 rx ry v M Bounded_instance_0 0 0 mu_v
         IsUniformlyContinuous_instance_0 rx_M f = f.
Proof. apply ode_solution. Qed.

Definition picard_iter (n : nat) :=
  iter_nat n _
           (@picard x0 y0 rx ry v M Bounded_instance_0 0 0 mu_v
                    IsUniformlyContinuous_instance_0 rx_M)
           (f0 x0 y0 rx ry).

(* (* This takes too long co compile. *)
Definition answer (n : positive) (r : CR) : Z :=
 let m := (iter_pos n (Pmult 10) 1%positive) in
 let (a,b) := (approximate r (1#m)%Qpos)*m in
 Zdiv a b.

Program Definition half : sx := 1 # 2.
Next Obligation.
apply mspc_ball_Qabs_flip. unfold x0. rewrite negate_0, plus_0_r.
rewrite abs.abs_nonneg; [reflexivity |].
change (0 <= 1 # 2)%Q. auto with qarith.
Qed.

(*
Time Compute answer 2 (` (picard_iter 3 half)). (* 10 minutes *)
Time Compute answer 1 (` (f half)). (* Too long *)
*)
*)
End Computation.

