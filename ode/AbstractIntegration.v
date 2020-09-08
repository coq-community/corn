(** An abstract interface for integrable uniformly continuous functions from Q to CR,
 with a proof that integrals satisfying this interface are unique. *)

Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import CoRN.model.reals.CRreal.
Require Import
 Coq.Unicode.Utf8 Coq.Program.Program
 CoRN.reals.fast.CRArith CoRN.reals.fast.CRabs
 CoRN.tactics.Qauto Coq.QArith.Qround CoRN.model.metric2.Qmetric
 CoRN.stdlib_omissions.P
 CoRN.stdlib_omissions.Z
 CoRN.stdlib_omissions.Q
 CoRN.stdlib_omissions.N.
Require Import CoRN.ode.metric CoRN.ode.FromMetric2 CoRN.ode.SimpleIntegration.

Require CoRN.model.structures.Qinf CoRN.model.structures.QnonNeg CoRN.model.structures.QnnInf CoRN.reals.fast.CRball.
Import Qinf.notations QnonNeg.notations QnnInf.notations CRball.notations Qabs (*canonical_names*).

Require CoRN.reals.fast.CRtrans CoRN.reals.faster.ARtrans. (* This is almost all CoRN *)

Import Qinf.coercions QnonNeg.coercions QnnInf.coercions CoRN.stdlib_omissions.Q.


Ltac done :=
  trivial; hnf; intros; solve
   [ repeat (first [solve [trivial | apply: sym_equal; trivial]
         | discriminate | contradiction | split])
(*   | case not_locked_false_eq_true; assumption*)
   | match goal with H : ~ _ |- _ => solve [case H; trivial] end ].

Local Open Scope Q_scope.
Local Open Scope CR_scope.

(* [SearchAbout ((Cmap _ _) (Cunit _)).] does not find anything, but it
should find metric2.Prelength.fast_MonadLaw3 *)

(** Any nonnegative width can be split up into an integral number of
 equal-sized pieces no bigger than a given bound: *)

Add Field Qfield : Qsft
 (decidable Qeq_bool_eq,
  completeness Qeq_eq_bool,
  constants [Qcst],
  power_tac Qpower_theory [Qpow_tac]).

(* To be added to stdlib.omissions.Q *)
Section QFacts.

Open Scope Q_scope.

Lemma Qmult_inv_l (x : Q) : ~ x == 0 -> / x * x == 1.
Proof. intros; rewrite Qmult_comm; apply Qmult_inv_r; trivial. Qed.

Lemma Qinv_0 (x : Q) : / x == 0 <-> x == 0.
Proof.
split; intro H; [| now rewrite H].
destruct x as [m n]; destruct m as [| p | p]; unfold Qinv in *; simpl in *; [reflexivity | |];
unfold Qeq in H; simpl in H; rewrite Pos.mul_1_r in H; discriminate H.
Qed.

Lemma Qinv_not_0 (x : Q) : ~ / x == 0 <-> ~ x == 0.
Proof. now rewrite Qinv_0. Qed.

Lemma Qdiv_l (x y z : Q) : ~ x == 0 -> (x * y == z <-> y == z / x).
Proof.
intro H1.
rewrite <- (Qmult_injective_l x H1 y (z / x)). unfold Qdiv.
now rewrite <- Qmult_assoc, (Qmult_inv_l x H1), Qmult_1_r, Qmult_comm.
Qed.

Lemma Qdiv_r (x y z : Q) : ~ y == 0 -> (x * y == z <-> x == z / y).
Proof. rewrite Qmult_comm; apply Qdiv_l. Qed.

Lemma Q_of_nat_inj (m n : nat) : m == n <-> m = n.
Proof.
split; intro H; [| now rewrite H].
rewrite QArith_base.inject_Z_injective in H. now apply Nat2Z.inj in H.
Qed.

End QFacts.

Definition split (w: QnonNeg) (bound: QposInf):
  { x: nat * QnonNeg | (from_nat (fst x) * snd x == w)%Qnn
                     /\ (QnnInf.Finite (snd x) <= from_QposInf bound)%QnnInf }.
Proof with simpl; auto with *.
 unfold QnonNeg.eq. simpl.
 destruct bound; simpl.
  Focus 2. exists (1%nat, w). simpl. split... ring.
 induction w using QnonNeg.rect.
  exists (0%nat, 0%Qnn)...
 set (p := SimpleIntegration.QposCeiling (proj1_sig ((n#d) * Qpos_inv q)%Qpos)).
 exists (nat_of_P p, from_Qpos (((n#d) * Qpos_inv (p#1))%Qpos))...
 split.
  rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
  change (p * ((n#d) * / p) == (n#d))%Q.
  field. discriminate.
 subst p.
 apply Qle_shift_div_r. reflexivity.
 rewrite SimpleIntegration.QposCeiling_Qceiling. simpl.
 setoid_replace (n#d:Q)
   with (proj1_sig q * ((n#d) * / proj1_sig q))%Q at 1 by (simpl; field)...
 apply Qmult_le_l. apply Qpos_ispos.
 apply Qle_ceiling.
Qed.

(** Riemann sums will play an important role in the theory about integrals, so let's
define very simple summation and a key property thereof: *)

Definition cmΣ {M: CMonoid} (n: nat) (f: nat -> M): M := cm_Sum (map f (enum n)).

(*Lemma cmΣ_sum {M: CMonoid} (n : nat) (f g : nat -> M) : cmΣ n 

M := cm_Sum (map f (enum n)).

SearchAbout cm_Sum.*)

(** If the elementwise distance between two summations over the same domain
 is bounded, then so is the distance between the summations: *)

(*
Lemma CRΣ_gball_ex (f g: nat -> CR) (e: QnnInf) (n: nat):
   (forall m, (m < n)%nat -> gball_ex e (f m) (g m)) ->
   (gball_ex (n * e)%QnnInf (cmΣ n f) (cmΣ n g)).
Proof with simpl; auto.
 destruct e...
 induction n.
  reflexivity.
 intros.
 change (gball (inject_Z (S n) * `q) (cmΣ (S n) f) (cmΣ (S n) g)).
 rewrite Q.S_Qplus.
 setoid_replace ((n+1) * q)%Q with (q + n * q)%Q by (simpl; ring).
 unfold cmΣ. simpl @cm_Sum.
 apply CRgball_plus...
Qed.
*)

Lemma cmΣ_0 (f : nat -> CR) (n : nat) :
  (forall m, (m < n)%nat -> f m [=] 0) -> cmΣ n f [=] 0.
Proof.
induction n as [| n IH]; intro H; [reflexivity |].
unfold cmΣ. simpl @cm_Sum. rewrite H by apply lt_n_Sn.
rewrite IH; [apply CRplus_0_l |].
intros m H1; apply H. now apply lt_S.
Qed.

Lemma CRΣ_gball (f g: nat -> CR) (e : Q) (n : nat):
   (forall m, (m < n)%nat -> ball e (f m) (g m)) ->
   (ball (n * e) (cmΣ n f) (cmΣ n g)).
Proof.
  induction n.
  - intros. apply ball_refl. rewrite Qmult_0_l. apply Qle_refl.
  - intros.
 rewrite Q.S_Qplus.
 setoid_replace ((n + 1) * e)%Q with (e + n * e)%Q by ring.
 unfold cmΣ. simpl @cm_Sum.
 apply CRgball_plus; auto.
Qed.

(*Instance cmΣ_proper : Proper (eq ==> @ext_equiv nat _ CR _ ==> @st_eq CR) cmΣ.
Proof.
intros n1 n2 E1 f1 f2 E2. rewrite E1.
change (gball 0 (cmΣ n2 f1) (cmΣ n2 f2)).
setoid_replace 0%Q with (n2 * 0)%Q by ring.
apply CRΣ_gball. now intros m _; apply E2.
Qed.*)

Hint Immediate ball_refl Qle_refl.

(** Next up, the actual interface for integrable functions. *)

Bind Scope Q_scope with Q.

(*Arguments integral_additive {f} {_} {_} a b c _ _.*)

Section integral_approximation.

  Context (f: Q → CR) `{Int: Integrable f}.

    (** The additive property implies that zero width intervals have zero surface: *)

    Lemma zero_width_integral q: ∫ f q 0%Qnn == 0.
    Proof with auto.
     apply CRplus_eq_l with (∫ f q 0%Qnn).
     generalize (integral_additive q 0%Qnn 0%Qnn).
     rewrite Qplus_0_r, QnonNeg.plus_0_l, CRplus_0_l...
    Qed.

    (** Iterating the additive property yields: *)

    Lemma integral_repeated_additive (a: Q) (b: QnonNeg) (n: nat):
      cmΣ n (fun i: nat => ∫ f (a + i * ` b) b)
      == ∫ f a (from_nat n * b)%Qnn.
    Proof with try ring.
     unfold cmΣ.
     induction n; simpl @cm_Sum.
      setoid_replace (QnonNeg.coercions.from_nat 0) with 0%Qnn by reflexivity.
      rewrite QnonNeg.mult_0_l, zero_width_integral...
     rewrite IHn.
     rewrite CRplus_comm.
     setoid_replace (from_nat (S n) * b)%Qnn with (from_nat n * b + b)%Qnn.
      rewrite integral_additive...
     change (S n * proj1_sig b == n * proj1_sig b + proj1_sig b)%Q.
     rewrite S_Qplus...
    Qed.

    (** As promised, we now move toward the aforementioned generalizations of the
    boundedness property. We start by generalizing mid to CR: *)

    Lemma bounded_with_real_mid (from: Q) (width: Qpos) (mid: CR) (r: Qpos):
      (forall x, from <= x <= from+proj1_sig width -> ball (proj1_sig r) (f x) mid) ->
      ball (proj1_sig (width * r)%Qpos) (∫ f from (from_Qpos width)) (scale (proj1_sig width) mid).
    Proof with auto.
     intros H d1 d2.
     simpl approximate.
     destruct (Qscale_modulus_pos width d2) as [P E].
     rewrite E. simpl.
     set (v := (exist (Qlt 0) (/ (proj1_sig width) * proj1_sig d2)%Q P)).
     assert (QposEq (d1 + width * r + d2)%Qpos (d1 + width * (r + v))%Qpos).
     { unfold QposEq; simpl; field. apply Qpos_nonzero. }
     unfold QposEq in H0. rewrite H0. clear H0.
     apply regFunBall_Cunit.
     apply integral_bounded_prim.
     intros.
     apply ball_triangle with mid...
     apply ball_approx_r.
    Qed.

    (** Next, we generalize r to QnonNeg: *)

    Lemma bounded_with_nonneg_radius (from: Q) (width: Qpos) (mid: CR) (r: QnonNeg):
      (forall (x: Q), (from <= x <= from+ proj1_sig width) -> ball (proj1_sig r) (f x) mid) ->
      ball (proj1_sig width * proj1_sig r) (∫ f from (from_Qpos width)) (scale (proj1_sig width) mid).
    Proof with auto.
     pattern r.
     apply QnonNeg.Qpos_ind.
     - intros ?? E.
       split. intros H ?. rewrite <- E. apply H. intros. rewrite E...
       intros H ?. rewrite E. apply H. intros. rewrite <- E...
     - rewrite Qmult_0_r, ball_0.
      intros.
      apply ball_eq. intros e epos.
      setoid_replace e with (proj1_sig (width * (exist _ _ epos * Qpos_inv width))%Qpos)
        by (simpl; field; apply Qpos_nonzero).
      apply bounded_with_real_mid.
      intros q ?.
      setoid_replace (f q) with mid...
      apply ball_refl. apply Qpos_nonneg.
      apply -> (@ball_0 CR)...
     - intros.
       apply bounded_with_real_mid.
       intros. apply H, H0.
    Qed.

    (** Next, we generalize r to a full CR: *)

    Lemma bounded_with_real_radius (from: Q) (width: Qpos) (mid: CR) (r: CR) (rnn: CRnonNeg r):
      (forall (x: Q), from <= x <= from+` width -> CRball r mid (f x)) ->
      CRball (scale (proj1_sig width) r) (∫ f from (from_Qpos width)) (scale (proj1_sig width) mid).
    Proof with auto.
     intro A.
     unfold CRball.
     intros.
     unfold CRball in A.
     setoid_replace q with (proj1_sig width * (q / proj1_sig width))%Q
       by (simpl; field; auto).
     assert (r <= ' (q / proj1_sig width)).
     { apply (mult_cancel_leEq CRasCOrdField) with (' (proj1_sig width)).
       simpl. apply CRlt_Qlt...
      rewrite mult_commutes.
      change (' (proj1_sig width) * r <= ' (q / proj1_sig width) * ' (proj1_sig width)).
      rewrite CRmult_Qmult.
      unfold Qdiv.
      rewrite <- Qmult_assoc.
      rewrite (Qmult_comm (/ proj1_sig width)).
      rewrite Qmult_inv_r...
      rewrite Qmult_1_r.
      rewrite CRmult_scale... }
     assert (0 <= (q / proj1_sig width))%Q as E.
      apply CRle_Qle.
      apply CRle_trans with r...
      apply -> CRnonNeg_le_0...
     apply (bounded_with_nonneg_radius from width mid (exist _ _ E)).
     intros. apply ball_sym...
    Qed.

    (** Finally, we generalize to nonnegative width: *)

    Lemma integral_bounded (from: Q) (width: QnonNeg) (mid: CR) (r: CR) (rnn: CRnonNeg r)
      (A: forall (x: Q), (from <= x <= from+` width) -> CRball r mid (f x)):
      CRball (scale (proj1_sig width) r) (∫ f from width) (scale (proj1_sig width) mid).
    Proof with auto.
     revert A.
     pattern width.
     apply QnonNeg.Qpos_ind; intros.
       intros ?? E.
       split; intro; intros.
        rewrite <- E. apply H. intros. apply A. rewrite <- E...
       rewrite E. apply H. intros. apply A. rewrite E...
      rewrite zero_width_integral, scale_0, scale_0.
      apply CRball.reflexive, CRnonNeg_0.
     apply (bounded_with_real_radius from q mid r rnn)...
    Qed.

    (** In some context a lower-bound-upper-bound formulation is more convenient
    than the the ball-based formulation: *)

    Lemma integral_lower_upper_bounded (from: Q) (width: QnonNeg) (lo hi: CR):
      (forall (x: Q), (from <= x <= from+` width)%Q -> lo <= f x /\ f x <= hi) ->
      scale (` width) lo <= ∫ f from width /\ ∫ f from width <= scale (` width) hi.
    Proof with auto with *.
     intro A.
     assert (from <= from <= from + `width) as B.
      split...
      rewrite <- (Qplus_0_r from) at 1.
      apply Qplus_le_compat...
     assert (lo <= hi) as lohi by (destruct (A _ B); now apply CRle_trans with (f from)).
     set (r := ' (1#2) * (hi - lo)).
     set (mid := ' (1#2) * (lo + hi)).
     assert (mid - r == lo) as loE by (subst mid r; ring).
     assert (mid + r == hi) as hiE by (subst mid r; ring).
     rewrite <- loE, <- hiE.
     rewrite scale_CRplus, scale_CRplus, scale_CRopp, CRdistance_CRle, CRdistance_comm.
     apply CRball.as_distance_bound.
     apply integral_bounded.
      subst r.
      apply CRnonNeg_le_0.
      apply mult_resp_nonneg.
       simpl. apply CRle_Qle...
      rewrite <- (CRplus_opp lo).
      apply (CRplus_le_r lo hi (-lo))...
     intros.
     apply CRball.as_distance_bound. apply -> CRdistance_CRle.
     rewrite loE, hiE...
    Qed.

    (** We now work towards unicity, for which we use that implementations must agree with Riemann
     approximations. But since those are only valid for locally uniformly continuous functions, our proof
     of unicity only works for such functions. Todo: There should really be a proof that does not depend
     on continuity. *)

    Context `{L : @IsLocallyUniformlyContinuous
                    Q (msp_mspc_ball Q_as_MetricSpace)
                    CR (msp_mspc_ball CR) f lmu}.

(*
    Lemma gball_integral (e: Qpos) (a a': Q) (ww: Qpos) (w: QnonNeg):
      (w <= @uc_mu _ _ _ (@luc_mu Q _ CR f _ (a, ww)) e)%QnnInf ->
      gball ww a a' ->
      gball_ex (w * e)%QnnInf (' w * f a') (∫ f a' w).
    Proof with auto.
     intros ??.
     simpl QnnInf.mult.
     apply in_CRgball.
     simpl.
     rewrite <- CRmult_Qmult.
     CRring_replace (' w * f a' - ' w * ' e) (' w * (f a' - ' e)).
     CRring_replace (' w * f a' + ' w * ' e) (' w * (f a' + ' e)).
     repeat rewrite CRmult_scale.
     apply (integral_lower_upper_bounded a' w (f a' - ' e) (f a' + ' e)).
     intros x [lo hi].
     apply in_CRball.
     apply (locallyUniformlyContinuous f a ww e).
      apply ball_gball...
     set (luc_mu f a ww e) in *.
     destruct q...
     apply in_Qball.
     split.
      unfold Qminus.
      rewrite <- (Qplus_0_r x).
      apply Qplus_le_compat...
      change (-q <= -0)%Q.
      apply Qopp_le_compat...
     apply Qle_trans with (a' + `w)%Q...
     apply Qplus_le_compat...
    Qed.
*)
    (** Iterating this result shows that Riemann sums are arbitrarily good approximations: *)

    Open Scope Q_scope.

    Lemma luc_gball (a w delta eps x y : Q) :
      0 < eps ->
      (delta <= lmu a w eps)%Qinf ->
      @ball Q_as_MetricSpace w a x
      -> @ball Q_as_MetricSpace w a y
      -> @ball Q_as_MetricSpace delta x y
      -> ball eps (f x) (f y).
    Proof.
     intros A A1 A2 A3 A4.
     destruct (@luc_prf
                 Q (msp_mspc_ball Q_as_MetricSpace)
                 CR (msp_mspc_ball CR)
                 f lmu L a w) as [_ H].
     change (f x) with (@restrict Q (msp_mspc_ball Q_as_MetricSpace) CR
                                  f a w (exist _ _ A2)).
     change (f y) with (@restrict Q (msp_mspc_ball Q_as_MetricSpace) CR
                                  f a w (exist _ _ A3)).
     apply H; [apply A |].
     destruct (lmu a w eps) as [q |] eqn:A5; [| easy].
     apply (@mspc_monotone _ _
              (@sig_mspc Q (msp_mspc_ball Q_as_MetricSpace)
                         (msp_mspc_ball_ext Q_as_MetricSpace)
                         (@mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) w a) )
              delta).
     apply A1. apply A4.
    Qed.

    Lemma Riemann_sums_approximate_integral (a: Q) (w: QnonNeg) (e: Qpos) (iw: Q) (n: nat):
     (S n * iw == proj1_sig w)%Q ->
     (iw <= lmu a (proj1_sig w) (proj1_sig e))%Qinf ->
     ball (proj1_sig e * proj1_sig w)
           (cmΣ (S n) (fun i => 'iw * f (a + i * iw))%CR) (∫ f a w).
    Proof.
     intros A B.
     assert (ne_sn_0 : ~ S n == 0) by
        (change 0 with (inject_Z (Z.of_nat 0)); rewrite Q_of_nat_inj; apply S_O).
     assert (iw_nn : 0 <= iw) by
       (apply Qdiv_l in A; [| assumption]; rewrite A; apply Qmult_le_0_compat; [now auto|];
        apply Qinv_le_0_compat, Qle_nat). (* This should be automated *)
     set (iw' := exist _ iw iw_nn : QnonNeg ).
     change iw with (proj1_sig iw').
     change (from_nat (S n) * iw' == w)%Qnn in A.
     rewrite <- A at 2.
     rewrite <- integral_repeated_additive.
     setoid_replace (proj1_sig e * proj1_sig w)%Q with (S n * (iw * proj1_sig e))%Q by
       (unfold QnonNeg.eq in A; simpl in A;
        rewrite Qmult_assoc; rewrite A; apply Qmult_comm).
     apply CRΣ_gball.
     intros m H.
     rewrite CRmult_scale.
     apply ball_sym. apply CRball.rational.
     setoid_replace (' (iw * proj1_sig e)) with (scale (proj1_sig iw') (' ` e))
       by now rewrite <- scale_Qmult.
     apply integral_bounded; [apply CRnonNegQpos |].
     intros x [A1 A2]. apply CRball.rational.
     apply (luc_gball a (proj1_sig w) (`iw')); trivial.
     + apply gball_Qabs.
       setoid_replace (a - (a + m * proj1_sig iw')) with (- (m * proj1_sig iw')) by ring.
       rewrite Qabs_opp. apply Qabs_le_nonneg; [Qauto_nonneg |].
       apply Qle_trans with (y := (S n * proj1_sig iw')).
       apply Qmult_le_compat_r. apply Qlt_le_weak.
       rewrite <- Zlt_Qlt. now apply inj_lt.
       apply (proj2_sig iw').
       change (S n * proj1_sig iw' == proj1_sig w) in A. rewrite <- A; reflexivity.
     + apply gball_Qabs, Qabs_Qle_condition.
       split.
       apply Qplus_le_l with (z := x), Qplus_le_l with (z := proj1_sig w).
       setoid_replace (- proj1_sig w + x + proj1_sig w) with x by ring.
       setoid_replace (a - x + x + proj1_sig w) with (a + proj1_sig w) by ring.
       apply Qle_trans with (y := (a + m * ` iw' + ` iw')); [easy |].
       setoid_rewrite <- (Qmult_1_l (` iw')) at 2. change 1%Q with (inject_Z (Z.of_nat 1)).
       rewrite <- Qplus_assoc, <- Qmult_plus_distr_l, <- Zplus_Qplus, <- Nat2Z.inj_add.
       apply Qplus_le_r. change (S n * proj1_sig iw' == proj1_sig w) in A. rewrite <- A.
       apply Qmult_le_compat_r. rewrite <- Zle_Qle. apply inj_le. rewrite Plus.plus_comm.
       now apply lt_le_S.
       apply (proj2_sig iw').
       apply Qplus_le_l with (z := x), Qplus_le_l with (z := - proj1_sig w).
       setoid_replace (a - x + x + - proj1_sig w) with (a - proj1_sig w) by ring.
       setoid_replace (proj1_sig w + x + - proj1_sig w) with x by ring.
       apply Qle_trans with (y := a). rewrite <- (Qplus_0_r a) at 2.
       apply Qplus_le_r. change 0 with (-0). apply Qopp_le_compat, (proj2_sig w).
       apply Qle_trans with (y := a + m * ` iw'); [| easy].
       rewrite <- (Qplus_0_r a) at 1. apply Qplus_le_r, Qmult_le_0_compat; [apply Qle_nat | apply (proj2_sig iw')].
     + apply gball_Qabs, Qabs_Qle_condition; split.
       apply (Qplus_le_r (x + `iw')).
       setoid_replace (x + `iw' + - `iw') with x by ring.
       setoid_replace (x + (proj1_sig iw') + (a + m * proj1_sig iw' - x))
         with (a + m * proj1_sig iw' + proj1_sig iw') by ring. apply A2.
       apply (Qplus_le_r (x - `iw')).
       setoid_replace (x - proj1_sig iw' + (a + m * proj1_sig iw' - x))
         with (a + m * proj1_sig iw' - proj1_sig iw') by ring.
       setoid_replace (x - `iw' + `iw') with x by ring.
       apply Qle_trans with (y := a + m * proj1_sig iw'); [| easy].
       apply Qminus_less. apply (proj2_sig iw').
    Qed.

    Definition step (w : Q) (n : positive) : Q := w * (1 # n).

    Lemma step_nonneg (w : Q) (n : positive) : 0 <= w -> 0 <= step w n.
    Proof. intros w_nn; unfold step; Qauto_nonneg. Qed.

    Lemma step_0 (n : positive) : step 0 n == 0.
    Proof. unfold step; now rewrite Qmult_0_l. Qed.

    Lemma step_mult (w : Q) (n : positive) : (inject_Z n : Q) * step w n == w.
    Proof.
      unfold step.
      rewrite Qmake_Qdiv. unfold Qdiv. rewrite Qmult_1_l, (Qmult_comm w), Qmult_assoc.
      rewrite Qmult_inv_r, Qmult_1_l; [reflexivity | auto with qarith].
    Qed.

    Definition riemann_sum (a w : Q) (n : positive) :=
      let iw := step w n in
        cmΣ (Pos.to_nat n) (fun i => 'iw * f (a + i * iw))%CR.

    (*Instance : Proper (Qeq ==> Qeq ==> eq ==> @st_eq CR) riemann_sum.
    Proof.
      intros a1 a2 Ea w1 w2 Ew n1 n2 En. apply cmΣ_proper; [now rewrite En |].
      intros i1 i2 Ei.*)

    Lemma riemann_sum_0 (a : Q) (n : positive) : riemann_sum a 0 n [=] 0%CR.
    Proof.
      unfold riemann_sum. apply cmΣ_0.
      intros m _.
      generalize (f(a+m*step 0 n)). intros.
      rewrite (step_0 n). ring.
    Qed.

    Lemma Riemann_sums_approximate_integral' (a : Q) (w : QnonNeg) (e : Qpos) (n : positive) :
      (step (proj1_sig w) n <= lmu a (proj1_sig w) (proj1_sig e))%Qinf ->
      ball (proj1_sig e * proj1_sig w) (riemann_sum a (proj1_sig w) n) (∫ f a w).
    Proof.
      intro A; unfold riemann_sum.
      destruct (Pos2Nat.is_succ n) as [m M]. rewrite M.
      apply Riemann_sums_approximate_integral; [rewrite <- M | easy].
      unfold step. change (Pos.to_nat n * (proj1_sig w * (1 # n)) == proj1_sig w).
      rewrite positive_nat_Z. unfold inject_Z.
      rewrite Qmult_comm, <- Qmult_assoc.
      setoid_replace ((1 # n) * (n # 1)) with (1#1) by reflexivity.
      ring.
    Qed.

    Lemma integral_approximation (a : Q) (w : QnonNeg) (e : Qpos) :
      exists N : positive, forall n : positive, (N <= n)%positive ->
        mspc_ball e (riemann_sum a (proj1_sig w) n) (∫ f a w).
    Proof.
    destruct (Qlt_le_dec 1 (proj1_sig w)) as [A1 | A1].
    * assert (0 < proj1_sig w) by (apply (Qlt_trans _ 1); auto with qarith).
      set (N := Z.to_pos (Qceiling (comp_inf (λ x, proj1_sig w / x) (lmu a (proj1_sig w)) 0 (proj1_sig e / proj1_sig w)))).
      exists N; intros n A2.
      assert (Qinf.eq (proj1_sig e) (proj1_sig e / proj1_sig w * proj1_sig w)).
      { simpl. unfold canonical_names.equiv.
        unfold stdlib_rationals.Q_eq. field. intro abs.
        rewrite abs in H. exact (Qlt_irrefl 0 H). }
      rewrite H0. clear H0.
      (* [apply Riemann_sums_approximate_integral'] does not unify because in
      this lemma, the radius is [(QposAsQ e) * (QnonNeg.proj1_sig w)], and in the
      goal the radius is [(QposAsQ e) / (QnonNeg.proj1_sig w) * (QnonNeg.proj1_sig w)]. *)
      assert (P : 0 < proj1_sig e / proj1_sig w).
      { (apply Qmult_lt_0_compat; [| apply Qinv_lt_0_compat]; auto). }
      change (proj1_sig e / proj1_sig w) with (proj1_sig (exist _ _ P)).
      apply (Riemann_sums_approximate_integral'
               a w ((exist (Qlt 0) (proj1_sig e / proj1_sig w) P))).
      change (` (exist (Qlt 0) (` e / proj1_sig w) P)) with (proj1_sig e / proj1_sig w).
      destruct (lmu a (proj1_sig w) (proj1_sig e / proj1_sig w)) as [mu |] eqn:A3; [| easy].
      subst N; unfold comp_inf in A2; rewrite A3 in A2.
      change (step (proj1_sig w) n <= mu); unfold step.
      setoid_replace (1#n) with (/(n#1)) by reflexivity.

      assert (0 < mu) as A4. change (Qinf.lt 0 mu). rewrite <- A3.
      apply (@uc_pos
               _ (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace)
                              (@mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (proj1_sig w) a))
               CR (msp_mspc_ball CR)
               (@restrict Q (msp_mspc_ball Q_as_MetricSpace) CR f a (proj1_sig w))
               (lmu a (proj1_sig w))).
      trivial. trivial.
      apply Qle_div_l; auto. reflexivity.
      now apply Z.Ple_Zle_to_pos, Q.Zle_Qle_Qceiling in A2.
    * set (N := Z.to_pos (Qceiling (comp_inf (λ x, 1 / x) (lmu a (proj1_sig w)) 0 (proj1_sig e)))).
      exists N; intros n A2.
      apply (mspc_monotone (proj1_sig e * proj1_sig w)).
    + change (proj1_sig e * proj1_sig w <= proj1_sig e).
      rewrite <- (Qmult_1_r (proj1_sig e)) at 2. apply Qmult_le_compat_l; auto.
      apply Qpos_nonneg.
      + apply Riemann_sums_approximate_integral'.
        destruct (lmu a (proj1_sig w) (proj1_sig e)) as [mu |] eqn:A3; [| easy].
        subst N; unfold comp_inf in A2; rewrite A3 in A2.
        change (step (proj1_sig w) n <= mu); unfold step.
        setoid_replace (1#n) with (/(n#1)) by reflexivity.
        assert (0 < mu) as A4. change (Qinf.lt 0 mu). rewrite <- A3.
        apply (@uc_pos _ (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace)
                              (@mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (proj1_sig w) a))
               CR (msp_mspc_ball CR)
               (@restrict Q (msp_mspc_ball Q_as_MetricSpace) CR f a (proj1_sig w)) (lmu a (proj1_sig w))).
        trivial. apply (proj2_sig e).
        apply Qle_div_l; auto. reflexivity.
        apply Z.Ple_Zle_to_pos, Q.Zle_Qle_Qceiling in A2.
        apply (Qle_trans _ (1 / mu)); trivial. apply Qmult_le_compat_r; trivial.
        now apply Qinv_le_0_compat, Qlt_le_weak.
    Qed.

  (** Unicity itself will of course have to be stated w.r.t. *two* integrals: *)
(*
  Lemma unique
    `{!LocallyUniformlyContinuous_mu f} `{!LocallyUniformlyContinuous f}
    (c1: Integral f)
    (c2: Integral f)
    (P1: @Integrable c1)
    (P2: @Integrable c2):
  forall (a: Q) (w: QnonNeg),
    @integrate f c1 a w == @integrate f c2 a w.
  Proof with auto.
   intros. apply ball_eq. intros.
   revert w.
   apply QnonNeg.Qpos_ind.
     intros ?? E. rewrite E. reflexivity.
    do 2 rewrite zero_width_integral...
   intro x.
   destruct (split x (@uc_mu _ _ _ (@luc_mu Q _ CR f _ (a, x)) ((1 # 2) * e * Qpos_inv x)))%Qpos as [[n t] [H H0]].
   simpl in H.
   simpl @snd in H0.
   setoid_replace e with (((1 # 2) * e / x) * x + ((1 # 2) * e / x) * x)%Qpos by (unfold QposEq; simpl; field)...
   apply ball_triangle with (cmΣ n (fun i: nat => (' `t * f (a + i * `t)%Q))).
    apply ball_sym.
    apply ball_gball.
    apply (Riemann_sums_approximate_integral a x ((1 # 2) * e / x)%Qpos t n H H0).
   apply ball_gball.
   apply (Riemann_sums_approximate_integral a x ((1 # 2) * e / x)%Qpos t n H H0).
  Qed.
*)

End integral_approximation.

(** If f==g, then an integral for f is an integral for g. *)

Lemma Integrable_proper_l (f g: Q → CR) {fint: Integral f}:
  canonical_names.equiv f g → Integrable f → @Integrable g fint.
Proof with auto.
 constructor.
   replace (@integrate g) with (@integrate f) by reflexivity.
   intros.
   apply integral_additive.
  replace (@integrate g) with (@integrate f) by reflexivity.
  intros.
  apply integral_bounded_prim...
  intros.
  assert (st_eq (f x) (g x)).
  { apply (@ball_0 CR). apply H. reflexivity. }
  rewrite H3...
 replace (@integrate g) with (@integrate f) by reflexivity.
 apply integral_wd...
Qed.

Import canonical_names abstract_algebra.

Local Open Scope mc_scope.

Add Ring CR : (rings.stdlib_ring_theory CR).

Lemma mult_comm `{SemiRing R} : Commutative (.*.).
Proof. apply commonoid_commutative with (Aunit := one), _. Qed.

Lemma mult_assoc `{SemiRing R} (x y z : R) : x * (y * z) = x * y * z.
Proof. apply sg_ass, _. Qed.

(* Should this lemma be used to CoRN.reals.fast.CRabs? That file does not use
type class notations from canonical_names like ≤ *)

Lemma CRabs_nonneg (x : CR) : 0 ≤ abs x.
Proof.
apply -> CRabs_cases; [| apply _ | apply _].
split; [trivial | apply (proj1 (rings.flip_nonpos_negate x))].
Qed.

Lemma cmΣ_empty {M : CMonoid} (f : nat -> M) : cmΣ 0 f = [0].
Proof. reflexivity. Qed.

Lemma cmΣ_succ {M : CMonoid} (n : nat) (f : nat -> M) : cmΣ (S n) f = f n [+] cmΣ n f.
Proof. reflexivity. Qed.

Lemma cmΣ_plus (n : nat) (f g : nat -> CR) : cmΣ n (f + g) = cmΣ n f + cmΣ n g.
Proof.
induction n as [| n IH].
+ symmetry. apply ball_0. 
  apply (@cm_rht_unit CRasCMonoid (cmΣ 0 (f + g))).
+ apply ball_0. rewrite cmΣ_succ.
  transitivity ((f + g) n [+] (cmΣ n f + cmΣ n g)).
  apply ucFun2_wd. reflexivity. 
  apply ball_0 in IH. exact IH. clear IH.
  rewrite cmΣ_succ.
  transitivity (f n [+] cmΣ n f + (g n [+] cmΣ n g)).
  change (f n + g n + (cmΣ n f + cmΣ n g) [=] f n + cmΣ n f + (g n + cmΣ n g))%CR.
  do 2 rewrite <- CRplus_assoc.
  apply CRplus_eq_r.
  rewrite CRplus_comm, <- CRplus_assoc.
  apply CRplus_eq_r. apply CRplus_comm.
  apply ucFun2_wd. reflexivity. 
  symmetry. exact (cmΣ_succ n g).
Qed.

Lemma cmΣ_negate (n : nat) (f : nat -> CR) : cmΣ n (- f) = - cmΣ n f.
Proof.
induction n as [| n IH].
+ apply ball_0. change ((0 : CR) [=] - 0)%CR.
  apply CRopp_0. 
+ apply ball_0.
  transitivity ((- f) n [+] cmΣ n (- f)).
  apply cmΣ_succ.
  apply ball_0 in IH.
  transitivity ( (- f) n [+] - cmΣ n f).
  apply ucFun2_wd. reflexivity. 
  exact IH. clear IH.
  change (- f n - cmΣ n f [=] - (f n + cmΣ n f))%CR.
  rewrite CRopp_plus_distr.
  reflexivity.
Qed.

Lemma cmΣ_const (n : nat) (m : CR) : cmΣ n (λ _, m) = m * '(n : Q).
Proof.
induction n as [| n IH].
+ apply ball_0. rewrite cmΣ_empty.
  change (0 [=] m * 0). symmetry; apply rings.mult_0_r.
+ apply ball_0. rewrite cmΣ_succ.
  apply ball_0 in IH.
  transitivity (m [+] (m*'n))%CR.
  apply ucFun2_wd. reflexivity. 
  exact IH. clear IH. rewrite S_Qplus, <- CRplus_Qplus.
  change (m + m * '(n : Q) [=] m * ('(n : Q) + 1)).
  rewrite rings.plus_mult_distr_l.
  rewrite rings.plus_comm.
  apply ucFun2_wd. reflexivity. 
  rewrite rings.mult_1_r. reflexivity.
Qed.

Lemma riemann_sum_const (a : Q) (w : Q) (m : CR) (n : positive) :
  riemann_sum (λ _, m) a w n = 'w * m.
Proof.
unfold riemann_sum. rewrite cmΣ_const, positive_nat_Z.
change ('step w n * m * '(n : Q) = 'w * m).
apply ball_0.
rewrite (mult_comm _ ('(inject_Z n : Q))), mult_assoc, CRmult_Qmult, step_mult; reflexivity.
Qed.

Lemma riemann_sum_plus (f g : Q -> CR) (a w : Q) (n : positive) :
  riemann_sum (f + g) a w n = riemann_sum f a w n + riemann_sum g a w n.
Proof.
  unfold riemann_sum. rewrite <- cmΣ_plus.
  apply ball_0. apply cm_Sum_eq. intro k.
change (
  cast Q CR (step w n) * (f (a + (k : Q) * step w n) + g (a + (k : Q) * step w n)) [=]
  cast Q CR (step w n) * f (a + (k : Q) * step w n) + cast Q CR (step w n) * g (a + (k : Q) * step w n)).
apply rings.plus_mult_distr_l. (* Without [change] unification fails, [apply:] loops *)
Qed.

Lemma riemann_sum_negate (f : Q -> CR) (a w : Q) (n : positive) :
  riemann_sum (- f) a w n = - riemann_sum f a w n.
Proof.
  unfold riemann_sum. rewrite <- cmΣ_negate.
  apply ball_0. apply cm_Sum_eq. intro k.
change ('step w n * (- f (a + (k : Q) * step w n)) [=] -('step w n * f (a + (k : Q) * step w n))).
  rewrite rings.negate_mult_distr_r. reflexivity.
Qed.

Section RiemannSumBounds.

Context (f : Q -> CR).

Global Instance Qle_nat (n : nat) : PropHolds (0 ≤ (n : Q)).
Proof. apply Qle_nat. Qed.

Instance step_nonneg' (w : Q) (n : positive) : PropHolds (0 ≤ w) -> PropHolds (0 ≤ step w n).
Proof. apply step_nonneg. Qed.

Lemma index_inside_l (a w : Q) (k : nat) (n : positive) :
  0 ≤ w -> k < Pos.to_nat n -> a ≤ a + (k : Q) * step w n.
Proof. intros; apply semirings.nonneg_plus_le_compat_r; solve_propholds. Qed.

Lemma index_inside_r (a w : Q) (k : nat) (n : positive) :
  0 ≤ w -> k < Pos.to_nat n -> a + (k : Q) * step w n ≤ a + w.
Proof.
intros A1 A2. apply (orders.order_preserving (a +)).
mc_setoid_replace w with ((inject_Z n : Q) * (step w n)) at 2 by (symmetry; apply step_mult).
apply (orders.order_preserving (.* step w n)).
rewrite <- Zle_Qle, <- positive_nat_Z. apply inj_le. change (k ≤ Pos.to_nat n). solve_propholds.
Qed.

Lemma riemann_sum_bounds (a w : Q) (m : CR) (e : Q) (n : positive) :
  0 ≤ w -> (forall (x : Q), (a ≤ x ≤ a + w) -> ball e (f x) m) ->
  ball (w * e) (riemann_sum f a w n) ('w * m).
Proof.
  intros w_nn A.
  pose proof (riemann_sum_const a w m n).
  apply ball_0 in H. rewrite <- H. clear H.
  unfold riemann_sum.
rewrite <- (step_mult w n), <- (Qmult_assoc (inject_Z n) _ e), <- (positive_nat_Z n).
apply CRΣ_gball. intros k A1. apply CRball.gball_CRmult_Q_nonneg; [now apply step_nonneg |].
apply A. split; [apply index_inside_l | apply index_inside_r]; trivial.
Qed.

End RiemannSumBounds.

Section IntegralBound.

Context (f : Q -> CR) `{Integrable f}.

Lemma scale_0_r (x : Q) : scale x 0 [=] 0.
Proof.
  rewrite <- CRmult_scale.
  change (cast Q CR x * 0 [=] 0).
  apply rings.mult_0_r.
Qed.

Require Import MathClasses.misc.propholds.

Lemma integral_abs_bound (from : Q) (width : QnonNeg) (M : Q) :
  (forall (x : Q), (from ≤ x ≤ from + proj1_sig width) -> CRabs (f x) ≤ 'M) ->
  CRabs (∫ f from width) ≤ '(`width * M).
Proof.
intro A. rewrite <- (CRplus_0_r (∫ f from width)), <- CRopp_0.
apply CRball.as_distance_bound. rewrite <- (scale_0_r (proj1_sig width)).
rewrite <- CRmult_Qmult, CRmult_scale.
apply integral_bounded; trivial.
+ apply CRnonNeg_le_0.
  apply CRle_trans with (y := CRabs (f from)); [apply CRabs_nonneg |].
  apply A. split; [reflexivity |].
  apply semirings.nonneg_plus_le_compat_r; change (0 <= proj1_sig width)%Q; Qauto_nonneg.
+ intros x A2. apply CRball.as_distance_bound. rewrite CRdistance_comm.
  change (CRabs (f x - 0) ≤ 'M).
  rewrite rings.minus_0_r; now apply A.
Qed.

(*apply CRball.as_distance_bound, CRball.rational. rewrite <- (scale_0_r width).
assert (A1 : 0 ≤ M).
+ apply CRle_Qle. apply CRle_trans with (y := CRabs (f from)); [apply CRabs_nonneg |].
  apply A. split; [reflexivity |].
  apply semirings.nonneg_plus_le_compat_r; change (0 <= width)%Q; Qauto_nonneg.
+ change M with (QnonNeg.proj1_sig (exist _ M A1)).
  apply bounded_with_nonneg_radius; [easy |].
  intros x A2. apply CRball.gball_CRabs. change (f x - 0%mc)%CR with (f x - 0).
  rewrite rings.minus_0_r; now apply A.
Qed.*)

End IntegralBound.

(*
Section IntegralOfSum.

Context (f g : Q -> CR)
        `{!IsLocallyUniformlyContinuous f f_mu, !IsLocallyUniformlyContinuous g g_mu}
        `{Integral f, !Integrable f, Integral g, !Integrable g}.

Global Instance integrate_sum : Integral (f + g) := λ a w, integrate f a w + integrate g a w.
Global Instance integrate_negate : Integral (- f) := λ a w, - integrate f a w.

Lemma integral_sum_additive (a : Q) (b c : QnonNeg) :
   ∫ (f + g) a b + ∫ (f + g) (a + ` b) c = ∫ (f + g) a (b + c)%Qnn.
Proof.
unfold integrate, integrate_sum.
rewrite <- !integral_additive; trivial.
change (
  ∫ f a b + ∫ g a b + (∫ f (a + ` b) c + ∫ g (a + ` b) c) =
  (∫ f a b + ∫ f (a + ` b) c) + (∫ g a b + ∫ g (a + ` b) c)). ring.
Qed.

Lemma integral_negate_additive (a : Q) (b c : QnonNeg) :
   ∫ (- f) a b + ∫ (- f) (a + ` b) c = ∫ (- f) a (b + c)%Qnn.
Proof.
unfold integrate, integrate_negate.
rewrite <- rings.negate_plus_distr. apply CRopp_wd_Proper. (* Where is it defined? *)
now apply integral_additive.
Qed.


(* When the last argument of ball is ('(width * mid)), typechecking diverges *)

Lemma integral_sum_integrable (from : Q) (width : Qpos) (mid : Q) (r : Qpos) :
 (∀ x : Q, from ≤ x ≤ from + width → ball r (f x + g x) ('mid))
 → ball (width * r) (∫ (f + g) from width) ('((width : Q) * mid)).
Proof.
intros A. apply ball_gball; simpl. apply gball_closed. intros e e_pos.
setoid_replace (width * r + e)%Q with (e + width * r)%Q by apply Qplus_comm.
destruct (Riemann_sums_approximate_integral'' f from width ((1#2) * mkQpos e_pos)%Qpos) as [Nf F].
destruct (Riemann_sums_approximate_integral'' g from width ((1#2) * mkQpos e_pos)%Qpos) as [Ng G].
set (n := Pos.max Nf Ng).
assert (le_Nf_n : (Nf <= n)%positive) by apply Pos.le_max_l.
assert (le_Ng_n : (Ng <= n)%positive) by apply Pos.le_max_r.
specialize (F n le_Nf_n). specialize (G n le_Ng_n).
apply gball_triangle with (b := riemann_sum (f + g) from width n).
+ rewrite riemann_sum_plus. setoid_replace e with ((1#2) * e + (1#2) * e)%Q by ring.
  apply CRgball_plus; apply gball_sym; trivial.
+ (* apply riemann_sum_bounds. diverges *)
  rewrite <- CRmult_Qmult. apply riemann_sum_bounds; [solve_propholds |].
  intros. apply ball_gball. apply A; trivial.
Qed.

(*Lemma integral_negate_integrable (from : Q) (width : Qpos) (mid : Q) (r : Qpos) :
 (∀ x : Q, from ≤ x ≤ from + width → ball r ((- f) x) ('mid))
 → ball (width * r) (∫ (- f) from width) ('((width : Q) * mid)).
Proof.
intros A. unfold integrate, integrate_negate.
SearchAbout gball CRopp.
SearchAbout (gball _ (CRopp _) (CRopp _)).*)

Global Instance : Integrable (f + g).
constructor.
+ apply integral_sum_additive.
+ apply integral_sum_integrable.
+ intros a1 a2 A1 w1 w2 A2. unfold integrate, integrate_sum. rewrite A1, A2; reflexivity.
Qed.

End IntegralOfSum.
*)

Add Field Q : (dec_fields.stdlib_field_theory Q).

(* In theory.rings, we have

[rings.plus_assoc : ... Associative plus]

and

[rings.plus_comm : ... Commutative plus].

One difference is that [Commutative] is defined directly while
[Associative] is defined through [HeteroAssociative]. For this or some
other reason, rewriting [rings.plus_comm] works while rewriting
[rings.plus_assoc] does not. Interestingly, all arguments before x y z in
[rings.plus_assoc] are implicit, and when we make [R] explicit, rewriting
works. However, in this case [rewrite] leaves a goal [SemiRing R], which is
not solved by [trivial], [auto] or [easy], but only by [apply _]. If
[rings.plus_assoc] is formulated as [x + (y + z) = (x + y) + z] instead of
[Associative plus], then rewriting works; however, then it cannot be an
instance (of [Associative]). Make this change in theory.rings? *)

Lemma plus_assoc `{SemiRing R} : forall (x y z : R), x + (y + z) = (x + y) + z.
Proof. exact simple_associativity. Qed.

Section RingFacts.

Context `{Ring R}.

Lemma plus_left_cancel (z x y : R) : z + x = z + y <-> x = y.
Proof.
split.
(* [apply (left_cancellation (+)).] leaves the goal [LeftCancellation plus z],
which is solved by [apply _]. Why is it left? *)
+ apply (left_cancellation (+) z).
+ intro A; now rewrite A.
Qed.

Lemma plus_right_cancel (z x y : R) : x + z = y + z <-> x = y.
Proof. rewrite (rings.plus_comm x z), (rings.plus_comm y z); apply plus_left_cancel. Qed.

Lemma plus_eq_minus (x y z : R) : x + y = z <-> x = z - y.
Proof.
split; intro A.
+ apply (right_cancellation (+) y).
  now rewrite <- plus_assoc, rings.plus_negate_l, rings.plus_0_r.
+ apply (right_cancellation (+) (-y)).
  now rewrite <- plus_assoc, rings.plus_negate_r, rings.plus_0_r.
Qed.

Lemma minus_eq_plus (x y z : R) : x - y = z <-> x = z + y.
Proof. now rewrite plus_eq_minus, rings.negate_involutive. Qed.

Lemma negate_inj (x y : R) : -x = -y <-> x = y.
Proof. now rewrite rings.flip_negate, rings.negate_involutive. Qed.

End RingFacts.

Import interfaces.orders orders.minmax theory.rings.

Lemma join_comm `{JoinSemiLatticeOrder L} : Commutative join.
Proof.
intros x y. apply antisymmetry with (R := (≤)); [apply _ | |];
(apply join_lub; [apply join_ub_r | apply join_ub_l]).
(* why is [apply _] needed? *)
Qed.

Lemma meet_comm `{MeetSemiLatticeOrder L} : Commutative meet.
Proof.
intros x y. apply antisymmetry with (R := (≤)); [apply _ | |];
(apply meet_glb; [apply meet_lb_r | apply meet_lb_l]).
Qed.

Definition Range (T : Type) := prod T T.

Instance contains_Q : Contains Q (Range Q) := λ x s, (fst s ⊓ snd s ≤ x ≤ fst s ⊔ snd s).

Lemma Qrange_comm (a b x : Q) : x ∈ (a, b) <-> x ∈ (b, a).
Proof.
unfold contains, contains_Q; simpl.
rewrite join_comm, meet_comm; reflexivity.
Qed.

Lemma range_le (a b : Q) : a ≤ b -> forall x, a ≤ x ≤ b <-> x ∈ (a, b).
Proof.
intros A x; unfold contains, contains_Q; simpl.
mc_setoid_replace (meet a b) with a by now apply lattices.meet_l.
mc_setoid_replace (join a b) with b by now apply lattices.join_r. reflexivity.
Qed.

Lemma CRabs_negate (x : CR) : abs (-x) = abs x.
Proof.
change (abs (-x)) with (CRabs (-x)).
apply ball_0. rewrite CRabs_opp; reflexivity.
Qed.

Lemma mspc_ball_Qle (r a x : Q)
  : @mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) r a x <-> a - r ≤ x ≤ a + r.
Proof. rewrite mspc_ball_Qabs; apply Qabs_diff_Qle. Qed.

Lemma mspc_ball_convex (x1 x2 r a x : Q) :
  @mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) r a x1
  -> @mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) r a x2
  -> x ∈ (x1, x2)
  -> @mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) r a x.
Proof.
intros A1 A2 A3.
rewrite mspc_ball_Qle in A1, A2. apply mspc_ball_Qle.
destruct A1 as [A1' A1'']; destruct A2 as [A2' A2'']; destruct A3 as [A3' A3'']. split.
+ now transitivity (meet x1 x2); [apply meet_glb |].
+ now transitivity (join x1 x2); [| apply join_lub].
Qed.

Section IntegralTotal.

Context (f : Q -> CR) `{Integrable f}.

Program Definition int (from to : Q) :=
  if (decide (from ≤ to))
  then integrate f from (to - from)
  else -integrate f to (from - to).
Next Obligation.
change (0 ≤ to - from). (* without [change], the following [apply] does not work *)
now apply rings.flip_nonneg_minus.
Qed.
Next Obligation.
change (0 ≤ from - to).
(* [apply rings.flip_nonneg_minus, orders.le_flip] does not work *)
apply rings.flip_nonneg_minus; now apply orders.le_flip.
Qed.

Lemma integral_additive' (a b : Q) (u v w : QnonNeg) :
  a + `u = b -> `u + `v = `w -> ∫ f a u + ∫ f b v = ∫ f a w.
Proof.
  intros A1 A2.
  assert (QnonNeg.eq (u+v)%Qnn w) as H0 by apply A2.
  assert (Qeq (a+`u) b) as H1 by apply A1.
  apply ball_0. 
  transitivity ( ∫ f a u + ∫ f (a+`u) v).
  apply ucFun2_wd. reflexivity. 
  rewrite <- A1. reflexivity. rewrite <- H0.
  apply integral_additive.
Qed.

Lemma int_add (a b c : Q) : int a b + int b c = int a c.
Proof.
unfold int.
destruct (decide (a ≤ b)) as [AB | AB];
destruct (decide (b ≤ c)) as [BC | BC];
destruct (decide (a ≤ c)) as [AC | AC].
+ apply integral_additive'; simpl; ring.
+ assert (A : a ≤ c) by (now transitivity b); elim (AC A).
+ apply ball_0. apply minus_eq_plus. symmetry.
  pose proof (integral_additive' a c ((c - a) ↾ int_obligation_1 a c AC)
                                 ((b - c) ↾ int_obligation_2 b c BC)
                                 ((b - a) ↾ int_obligation_1 a b AB) ).
  apply ball_0 in H0. apply H0. clear H0.
  simpl. ring. simpl. ring.
+ apply ball_0. apply minus_eq_plus.
  rewrite (rings.plus_comm (-integrate _ _ _)), <- plus_eq_minus, (rings.plus_comm (integrate _ _ _)).
  pose proof (integral_additive' c a ((a - c) ↾ int_obligation_2 a c AC)
                                 ((b - a) ↾ int_obligation_1 a b AB)
                                 ((b - c) ↾ int_obligation_2 b c BC) ).
  apply ball_0 in H0. apply H0. clear H0.
  simpl. ring. simpl. ring. 
+ apply ball_0.
  rewrite (rings.plus_comm (-integrate _ _ _)).
  apply minus_eq_plus. rewrite (rings.plus_comm (integrate _ _ _)).
  symmetry.
  pose proof (integral_additive' b a ((a - b) ↾ int_obligation_2 a b AB)
                                 ((c - a) ↾ int_obligation_1 a c AC)
                                 ((c - b) ↾ int_obligation_1 b c BC) ).
  apply ball_0 in H0. apply H0. clear H0.
  simpl. ring. simpl. ring. 
+ apply ball_0. rewrite (rings.plus_comm (-integrate _ _ _)).
  apply minus_eq_plus. rewrite (rings.plus_comm (-integrate _ _ _)), <- plus_eq_minus.
  pose proof (integral_additive' b c ((c - b) ↾ int_obligation_1 b c BC)
                                 ((a - c) ↾ int_obligation_2 a c AC)
                                 ((a - b) ↾ int_obligation_2 a b AB) ).
  apply ball_0 in H0. apply H0. clear H0.
  simpl. ring. simpl. ring. 
+ assert (b ≤ a) by (now apply orders.le_flip); assert (B : b ≤ c) by (now transitivity a); elim (BC B).
+ apply ball_0.
  rewrite <- rings.negate_plus_distr. apply negate_inj.
  rewrite (rings.plus_comm (integrate _ _ _)).
  pose proof (integral_additive' c b ((b - c) ↾ int_obligation_2 b c BC)
                                 ((a - b) ↾ int_obligation_2 a b AB)
                                 ((a - c) ↾ int_obligation_2 a c AC) ).
  apply ball_0 in H0. apply H0. clear H0.
  simpl. ring. simpl. ring. 
Qed.

Lemma int_diff (a b c : Q) : int a b - int a c = int c b.
Proof.
  apply ball_0. apply minus_eq_plus. symmetry.
  rewrite (rings.plus_comm (int c b) (int a c)).
  pose proof (int_add a c b). apply ball_0 in H0.
  apply H0.
Qed.

Lemma int_zero_width (a : Q) : int a a = 0.
Proof.
  apply ball_0.
  apply (plus_right_cancel (int a a)).
  rewrite rings.plus_0_l.
  pose proof (int_add a a a). apply ball_0 in H0. exact H0.
Qed.

Lemma int_opposite (a b : Q) : int a b = - int b a.
Proof.
  apply ball_0.
  apply (CRplus_eq_r (int b a)). rewrite CRplus_opp.
  pose proof (int_add b a b). apply ball_0 in H0. rewrite H0.
  pose proof (int_zero_width b).
  apply ball_0 in H1. exact H1.
Qed.

Lemma int_abs_bound (a b M : Q) :
  (forall x : Q, x ∈ (a, b) -> abs (f x) ≤ 'M)
  -> abs (int a b) ≤ '(abs (b - a) * M).
Proof.
  intros A. unfold int.
  assert (0 <= (' M))%CR as Mpos.
  { apply (@CRle_trans _ (abs (f a))).
    apply CRabs_nonneg. apply (A a).
    split. apply meet_lb_l.
    apply join_ub_l. }
  destruct (decide (a ≤ b)) as [AB | AB].
  - assert (∀ x : Q, a ≤ x ≤ a + ` ((b - a) ↾ int_obligation_1 a b AB)
                     → CRabs (f x) ≤ ' M).
    { intros. apply A. split; simpl.
      apply (Qle_trans _ a). apply meet_lb_l.
      apply H0.
      simpl in H0.
      apply (Qle_trans _ b).
      destruct H0.
      ring_simplify in H1.
      exact H1. apply join_ub_r. }
    apply (CRle_trans (integral_abs_bound
                         f a ((b - a) ↾ int_obligation_1 a b AB) M H0)).
    simpl.
    rewrite Qmult_comm, <- (Qmult_comm M).
    rewrite <- CRmult_Qmult, <- CRmult_Qmult.
    apply CRmult_le_compat_l. exact Mpos.
    apply CRle_Qle.
    apply Qle_Qabs.
  - unfold abs, abs_sig, CR_abs, proj1_sig. rewrite CRabs_opp.
    assert (∀ x : Q,
          b ≤ x ≤ b + ` ((a - b) ↾ int_obligation_2 a b AB) → CRabs (f x) ≤ ' M).
    { intros. apply A. split; simpl.
      apply (Qle_trans _ b). apply meet_lb_r.
      apply H0.
      simpl in H0.
      apply (Qle_trans _ a). 
      destruct H0.
      ring_simplify in H1.
      exact H1. apply join_ub_l. }
    apply (CRle_trans (integral_abs_bound
                  f b ((a - b) ↾ int_obligation_2 a b AB) M H0)).
    unfold proj1_sig, stdlib_rationals.Abs_instance_0.
    rewrite Qmult_comm, <- (Qmult_comm M).
    rewrite <- CRmult_Qmult, <- CRmult_Qmult.
    apply CRmult_le_compat_l. exact Mpos.
    apply CRle_Qle.
    rewrite (Qabs_Qminus b a).
    apply Qle_Qabs.
Qed.

End IntegralTotal.

(*Lemma int_plus (f g : Q -> CR) `{Integrable f, Integrable g}
  `{!IsLocallyUniformlyContinuous f f_mu, !IsLocallyUniformlyContinuous f f_mu} (a b : Q) :
  int f a b + int g a b = int (f + g) a b.
Proof.
unfold int. destruct (decide (a ≤ b)); [reflexivity |].
symmetry; unfold integrate at 1, integrate_sum.
apply rings.negate_plus_distr. (* does not work without unfold *)
Qed.*)

Lemma integrate_plus (f g : Q -> CR)
      `{@IsUniformlyContinuous
           Q (msp_mspc_ball Q_as_MetricSpace) 
           CR (msp_mspc_ball CR) 
          f f_mu,
        @IsUniformlyContinuous
           Q (msp_mspc_ball Q_as_MetricSpace) 
           CR (msp_mspc_ball CR) 
          g g_mu} 
      (a : Q) (w : QnonNeg) :
  @integrate (f + g) (@Integral_instance_0
                        (f+g) _ (@uc_ulc _ _ _ _ _ _
                                         (@sum_uc
                                            Q (msp_mspc_ball Q_as_MetricSpace)
                                            (msp_mspc_ball_ext Q_as_MetricSpace) 
                                            f g _ _ _ _))) a w
  = ∫ f a w + ∫ g a w.
Proof.
apply mspc_closed. intros e e_pos. (* Why is 0%Q? *)
mc_setoid_replace (0 + e) with e by ring.
assert (he_pos : 0 < e / 2) by solve_propholds.
assert (qe_pos : 0 < e / 4) by solve_propholds.
destruct (integral_approximation f a w (exist _ _ qe_pos)) as [Nf F].
destruct (integral_approximation g a w (exist _ _ qe_pos)) as [Ng G].
destruct (@integral_approximation
            (f + g)
            (@Integral_instance_0
               (f+g) _ (@uc_ulc _ _ _ _ _ _
                                (@sum_uc
                                   Q (msp_mspc_ball Q_as_MetricSpace)
                                   (msp_mspc_ball_ext Q_as_MetricSpace) 
                                   f g _ _ _ _)))
            _ _ (@uc_ulc _ _ _ _ _ _
                         (@sum_uc
                            Q (msp_mspc_ball Q_as_MetricSpace)
                            (msp_mspc_ball_ext Q_as_MetricSpace) 
                            f g _ _ _ _))
            a w (exist _ _ he_pos)) as [Ns S].
(* [Le positive] is not yet defined *)
set (n := Pos.max (Pos.max Nf Ng) Ns).
assert (Nf <= n)%positive by (transitivity (Pos.max Nf Ng); apply Pos.le_max_l).
assert (Ng <= n)%positive by (transitivity (Pos.max Nf Ng); [apply Pos.le_max_r | apply Pos.le_max_l]).
assert (Ns <= n)%positive by apply Pos.le_max_r.
apply (mspc_triangle' (e / 2) (e / 2) (riemann_sum (f + g) a (proj1_sig w) n)). 
- unfold Qdiv. rewrite <- Qmult_plus_distr_r.
  setoid_replace (/ 2 + / 2)%Q with 1%Q by reflexivity.
  apply Qmult_1_r.
- apply mspc_symm, S; assumption.
- rewrite riemann_sum_plus.
  mc_setoid_replace (e / 2) with (e / 4 + e / 4) by (field; split; discriminate).
  now apply mspc_ball_CRplus; [apply F | apply G].
Qed.

Lemma integrate_negate (f : Q -> CR)
  `{!IsUniformlyContinuous f f_mu} (a : Q) (w : QnonNeg) : ∫ (- f) a w = - ∫ f a w.
Proof.
apply mspc_closed. intros e e_pos.
mc_setoid_replace (0 + e) with e by ring.
assert (he_pos : 0 < e / 2) by solve_propholds.
destruct (integral_approximation (- f) a w (exist _ _ he_pos)) as [N1 F1].
destruct (integral_approximation f a w (exist _ _ he_pos)) as [N2 F2].
set (n := Pos.max N1 N2).
assert (N1 <= n)%positive by apply Pos.le_max_l.
assert (N2 <= n)%positive by apply Pos.le_max_r.
apply (mspc_triangle' (e / 2) (e / 2) (riemann_sum (- f) a (proj1_sig w) n)).
- unfold Qdiv. rewrite <- Qmult_plus_distr_r.
  setoid_replace (/ 2 + / 2)%Q with 1%Q by reflexivity.
  apply Qmult_1_r.
- now apply mspc_symm, F1.
- rewrite riemann_sum_negate. now apply mspc_ball_CRnegate, F2.
Qed.

Lemma int_plus (f g : Q -> CR)
      `{@IsUniformlyContinuous
           Q (msp_mspc_ball Q_as_MetricSpace) 
           CR (msp_mspc_ball CR) 
          f f_mu,
        @IsUniformlyContinuous
           Q (msp_mspc_ball Q_as_MetricSpace) 
           CR (msp_mspc_ball CR) 
          g g_mu} 
      (a b : Q) :
  @int (f + g)
       (@Integral_instance_0
                        (f+g) _ (@uc_ulc _ _ _ _ _ _
                                         (@sum_uc
                                            Q (msp_mspc_ball Q_as_MetricSpace)
                                            (msp_mspc_ball_ext Q_as_MetricSpace) 
                                            f g _ _ _ _)))
       a b
  = int f a b + int g a b.
Proof.
  unfold int; destruct (decide (a ≤ b)).
  rewrite integrate_plus. reflexivity.
  apply ball_0.
  pose proof (integrate_plus f g b ((a - b) ↾ int_obligation_2 a b n)).
  apply ball_0 in H1. rewrite H1. clear H1.
  apply rings.negate_plus_distr.
Qed.

Lemma int_negate (f : Q -> CR) `{!IsUniformlyContinuous f f_mu} (a b : Q) :
  int (- f) a b = - int f a b.
Proof.
  unfold int; destruct (decide (a ≤ b)).
  rewrite integrate_negate. reflexivity.
  apply ball_0.
  pose proof (integrate_negate f b ((a - b) ↾ int_obligation_2 a b n)).
  apply ball_0 in H. rewrite H. reflexivity.
Qed.

Lemma int_minus (f g : Q -> CR)
      `{@IsUniformlyContinuous
           Q (msp_mspc_ball Q_as_MetricSpace) 
           CR (msp_mspc_ball CR) 
          f f_mu,
        @IsUniformlyContinuous
           Q (msp_mspc_ball Q_as_MetricSpace) 
           CR (msp_mspc_ball CR) 
          g g_mu} 
      (a b : Q) :
  @int (f - g)
       (@Integral_instance_0
                        (f-g) _ (@uc_ulc _ _ _ _ _ _
                                         (@sum_uc
                                            Q (msp_mspc_ball Q_as_MetricSpace)
                                            (msp_mspc_ball_ext Q_as_MetricSpace) 
                                            f (-g) _ _ _ _)))
       a b
  = int f a b - int g a b.
Proof.
  rewrite int_plus.
  pose proof (int_negate g a b).
  apply ball_0. apply ball_0 in H1.
  transitivity (int f a b + - int g a b).
  apply ucFun2_wd. reflexivity. exact H1.
  reflexivity.
Qed.

Lemma abs_int_minus (f g : Q -> CR)
      `{@IsUniformlyContinuous
           Q (msp_mspc_ball Q_as_MetricSpace) 
           CR (msp_mspc_ball CR) 
          f f_mu,
        @IsUniformlyContinuous
           Q (msp_mspc_ball Q_as_MetricSpace) 
           CR (msp_mspc_ball CR) 
          g g_mu} 
      (a b : Q) :
  abs (@int (f - g)
       (@Integral_instance_0
                        (f-g) _ (@uc_ulc _ _ _ _ _ _
                                         (@sum_uc
                                            Q (msp_mspc_ball Q_as_MetricSpace)
                                            (msp_mspc_ball_ext Q_as_MetricSpace) 
                                            f (-g) _ _ _ _)))
       a b)
  [=] abs (int f a b - int g a b).
Proof.
  rewrite <- ball_0. apply CRabs_proper.
  apply int_minus.
Qed.

Import interfaces.orders orders.semirings.

Definition Qupper_bound (x : CR)
  := approximate x (Qpos2QposInf (1#1)) + 1.

(* To be proved by lifting from Q.
Lemma CRabs_triang (x y z : CR) : x = y + z -> abs x ≤ abs y + abs z.
*)

(* The section IntegralLipschitz is not used in the ODE solver through
Picard iterations. Instead of assuming the function that is being
integrated to be Lipschitz, the development assumes that it is uniformly
continuous and bounded. Then integral is Lispchitz, but it is only proved
that it is uniformly continuous. *)

Section IntegralLipschitz.

Notation ball := mspc_ball.

Context (f : Q -> CR) (x0 : Q)
        `{!@IsLocallyLipschitz
           Q (msp_mspc_ball Q_as_MetricSpace)
           CR (msp_mspc_ball CR) 
           f L}
        `{Integral f, !Integrable f}.

Let F (x : Q) := int f x0 x.

Section IntegralLipschitzBall.

Variables (a r x1 x2 : Q).

Hypotheses (I1 : @ball Q (msp_mspc_ball Q_as_MetricSpace) r a x1)
           (I2 : @ball Q (msp_mspc_ball Q_as_MetricSpace) r a x2)
           (r_nonneg : 0 ≤ r).

Let La := L a r.

Lemma int_lip (e M : Q) :
  (∀ x, @ball Q (msp_mspc_ball Q_as_MetricSpace) r a x -> abs (f x) ≤ 'M)
  -> @ball Q (msp_mspc_ball Q_as_MetricSpace) e x1 x2
  -> @ball CR (msp_mspc_ball CR) (M * e) (F x1) (F x2).
Proof.
intros A1 A2. apply CRball.gball_CRabs. subst F; cbv beta.
change (int f x0 x1 - int f x0 x2)%CR with (int f x0 x1 - int f x0 x2).
pose proof (int_diff f x0 x1 x2). apply ball_0 in H1.
rewrite H1.
change (abs (int f x2 x1) ≤ '(M * e)).
transitivity ('(M * abs (x1 - x2))).
+ rewrite mult_comm. apply int_abs_bound; trivial. intros x A3; apply A1, (mspc_ball_convex x2 x1); easy.
+ apply CRle_Qle. assert (0 ≤ M).
- apply CRle_Qle.
  transitivity (abs (f a)); [apply CRabs_nonneg | apply A1, @mspc_refl].
  exact (msp_mspc_ball_ext Q_as_MetricSpace).
  easy.
- change (M * abs (x1 - x2) ≤ M * e). apply (orders.order_preserving (M *.)).
    apply gball_Qabs, A2.
Qed.

End IntegralLipschitzBall.

Lemma lipschitz_bounded (a r M x : Q) :
  abs (f a) ≤ 'M
  -> @ball Q (msp_mspc_ball Q_as_MetricSpace) r a x
  -> abs (f x) ≤ '(M + L a r * r).
Proof.
  intros A1 A2.
  assert (f x = f x - 0) as H1.
  { apply ball_0. rewrite rings.minus_0_r. reflexivity. }
  pose proof (CRabs_proper _ _ H1).
  apply ball_0 in H2. rewrite H2. clear H2 H1.
  apply mspc_ball_CRabs, mspc_symm.
  apply (mspc_triangle _ _ _ (f a)).
  - apply mspc_ball_CRabs.
    assert (0 - f a = - f a) as H1.
    { apply ball_0. rewrite rings.plus_0_l. reflexivity. }
    pose proof (CRabs_proper _ _ H1).
    apply ball_0 in H2. rewrite H2. clear H2 H1.
    pose proof (CRabs_negate (f a)).
    apply ball_0 in H1. now rewrite H1.
  - apply (@llip _ _ _ _
              (msp_mspc_ball_ext Q_as_MetricSpace) f _ H).
  2: exact A2. 2: exact A2.
  apply mspc_refl.
  apply (@radius_nonneg _ _ (msp_mspc_ball_ext Q_as_MetricSpace) a x).
  exact A2.
Qed.

Global Instance integral_lipschitz :
  @IsLocallyLipschitz
    Q (msp_mspc_ball Q_as_MetricSpace)
    CR (msp_mspc_ball CR) 
    F (λ a r, Qupper_bound (abs (f a)) + L a r * r).
Proof.
intros a r r_nonneg. constructor.
+ apply nonneg_plus_compat.
  - apply CRle_Qle. transitivity (abs (f a)); [apply CRabs_nonneg | apply upper_CRapproximation].
  - apply nonneg_mult_compat. 2: exact r_nonneg.
    apply (@lip_nonneg
             _ (@sig_mspc_ball Q (msp_mspc_ball Q_as_MetricSpace) (ball r a))
             CR _ (@restrict Q (msp_mspc_ball Q_as_MetricSpace) CR 
                     f a r)).
    apply llip_prf. exact H. exact r_nonneg.
    (* Not good to provide [(restrict f a r)]. [IsLipschitz (restrict f a r) (L a r)] is generated *)
+ intros x1 x2 d A.
  destruct x1 as [x1 A1]; destruct x2 as [x2 A2].
  change (ball ((Qupper_bound (abs (f a)) + L a r * r) * d) (F x1) (F x2)).
  apply (int_lip a r); trivial.
  intros x B. now apply lipschitz_bounded; [apply upper_CRapproximation |].
Qed.

End IntegralLipschitz.

Import minmax (*Coq.Program.*)Basics.

(*Global Instance Qball_decidable (r : Qinf) (a x : Q) : Decision (mspc_ball r a x).
destruct r as [r |]; [| now left].
apply (decision_proper (Qabs (a - x) <= r)%Q); [symmetry; apply gball_Qabs | apply _].
Defined.*)

Section AbsFacts.

Context `{Ring R} `{!FullPseudoSemiRingOrder Rle Rlt} `{!Abs R}.

(* Should this be made a Class? It seems particular and complicated *)
Definition abs_cases_statement (P : R -> Prop) :=
  Proper (equiv ==> iff) P -> (forall x, Stable (P x)) ->
    forall x : R, (0 ≤ x -> P x) /\ (x ≤ 0 -> P (- x)) -> P (abs x).

Context `(abs_cases : forall P : R -> Prop, abs_cases_statement P)
        `{le_stable : forall x y : R, Stable (x ≤ y)}.

Lemma abs_nonneg' (x : R) : 0 ≤ abs x.
Proof.
apply abs_cases.
+ intros y1 y2 E; now rewrite E.
+ apply _.
+ split; [trivial |]. intros ?; now apply rings.flip_nonpos_negate.
Qed.

End AbsFacts.

Lemma Qabs_cases : forall P : Q -> Prop, abs_cases_statement P.
Proof.
intros P Pp Ps x [? ?].
destruct (decide (0 ≤ x)) as [A | A];
  [rewrite abs.abs_nonneg | apply le_flip in A; rewrite abs.abs_nonpos]; auto.
(* [easy] instead of [auto] does not work *)
Qed.

Lemma Qabs_nonneg (x : Q) : 0 ≤ abs x.
Proof. apply abs_nonneg'; [apply Qabs_cases | apply _]. Qed.

(*
Lemma integrate_proper
  (f g: Q → CR)
  `{!LocallyUniformlyContinuous_mu g}
  `{!LocallyUniformlyContinuous g}
  {fint: Integral f}
  {gint: Integral g}
  `{!@Integrable f fint}
  `{!@Integrable g gint}:
  canonical_names.equiv f g →
  ∀ (a: Q) (w: QnonNeg),
  @integrate f fint a w == @integrate g gint a w.
    (* This requires continuity for g only because [unique] does. *)
Proof with try assumption.
 intros.
 apply (unique g)...
 apply (Integrable_proper_l f)...
Qed.
*)

