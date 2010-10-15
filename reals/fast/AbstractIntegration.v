(** An abstract interface for integrable uniformly continuous functions from Q to CR,
 with a proof that integrals satisfying this interface are unique. *)

Require Import
 Program
 CRArith CRabs
 Qauto Qround Qmetric
 stdlib_omissions.P
 stdlib_omissions.Z
 stdlib_omissions.Q
 stdlib_omissions.N.

Require QnonNeg QnnInf CRball.
Import QnonNeg.notations QnnInf.notations CRball.notations.

Set Automatic Introduction.

Open Local Scope Q_scope.
Open Local Scope uc_scope.
Open Local Scope CR_scope.

(** Any nonnegative width can be split up into an integral number of
 equal-sized pieces no bigger than a given bound: *)

Definition split (w: QnonNeg) (bound: QposInf):
  { x: nat * QnonNeg | (fst x * snd x == w)%Qnn /\ (snd x <= bound)%QnnInf }.
Proof with simpl; auto with *.
 unfold QnonNeg.eq. simpl.
 destruct bound; simpl.
  Focus 2. exists (1%nat, w). simpl. split... ring.
 induction w using QnonNeg.rect.
  exists (0%nat, 0%Qnn)...
 set (p := QposCeiling (QposMake n d / q)%Qpos).
 exists (nat_of_P p, ((QposMake n d / p)%Qpos):QnonNeg)...
 split.
  rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
  change (p * ((n#d) * / p) == (n#d))%Q.
  field. discriminate.
 subst p.
 apply Qle_shift_div_r...
 rewrite QposCeiling_Qceiling. simpl.
 setoid_replace (n#d:Q) with (q * ((n#d) * / q))%Q at 1 by (simpl; field)...
 do 2 rewrite (Qmult_comm q).
 apply Qmult_le_compat_r...
Qed.

(** Riemann sums will play an important role in the theory about integrals, so let's
define very simple summation and a key property thereof: *)

Definition cmΣ {M: CMonoid} (n: nat) (f: nat -> M): M := cm_Sum M (map f (enum n)).

(** If the elementwise distance between two summations over the same domain
 is bounded, then so is the distance between the summations: *)

Lemma CRΣ_gball_ex (f g: nat -> CR) (e: QnnInf):
   (forall n, gball_ex e (f n) (g n)) ->
   (forall n: nat, gball_ex (n * e)%QnnInf (cmΣ n f) (cmΣ n g)).
Proof with simpl; auto.
 destruct e...
 induction n.
  reflexivity.
 change (gball (inject_Z (S n) * `q) (cmΣ (S n) f) (cmΣ (S n) g)).
 rewrite Q.S_Qplus.
 setoid_replace ((n+1) * q)%Q with (q + n * q)%Q by (simpl; ring).
 unfold cmΣ. simpl cm_Sum.
 apply CRgball_plus...
Qed.

Hint Immediate ball_refl Qle_refl.

(** Next up, the actual interface for integrable functions. *)

Class Integral (f: Q_as_MetricSpace --> CR) := integrate: forall (from: Q) (w: QnonNeg), CR.

Implicit Arguments integrate [[Integral]].

Notation "∫" := integrate.

Section integral_interface.

  Variable (f: Q_as_MetricSpace --> CR).

  Class Integrable `{!Integral f}: Prop :=
    { integral_additive:
      forall (a: Q) b c, ∫ f a b + ∫ f (a+` b) c == ∫ f a (b+c)%Qnn

    ; integral_bounded_prim: forall (from: Q) (width: Qpos) (mid: Q) (r: Qpos),
      (forall x, from <= x <= from+width -> ball r (f x) ('mid)) ->
      ball (width * r) (∫ f from width) (' (width * mid))

    ; integral_wd:> Proper (Qeq ==> QnonNeg.eq ==> @st_eq CRasCSetoid) (∫ f)
   }.

  (** This closely resembles the axiomatization given in
   Bridger's "Real Analysis: A Constructive Approach", Ch. 5. *)

  (** The boundedness property is stated very primitively here, in that r is a Qpos instead of a CR,
   w is a Qpos instead of a QnonNeg, and mid is a Q instead of a CR. This means that it's easy to
   show that particular implementations satisfy this interface, but hard to use this property directly.
   Hence, we will show in a moment that the property as stated actually implies its generalization
   with r and mid in CR and w in QnonNeg. *)

  (** Note: Another way to state the property still more primitively (and thus more easily provable) might
   be to make the inequalities in "from <= x <= from+width" strict. *)

  Section singular_props. (* Properties we can derive for a single integral of a function. *)

    Context `{Int: Integrable}.

    (** The additive property implies that zero width intervals have zero surface: *)

    Lemma zero_width_integral q: ∫ f q 0%Qnn == '0.
    Proof with auto.
     apply CRplus_eq_l with (∫ f q 0%Qnn).
     generalize (integral_additive q 0%Qnn 0%Qnn).
     rewrite Qplus_0_r QnonNeg.plus_0_l CRplus_0_l...
    Qed.

    (** Iterating the additive property yields: *)

    Lemma integral_repeated_additive (a: Q) (b: QnonNeg) (n: nat):
        cmΣ n (fun i: nat => ∫ f (a + i * ` b) b) == ∫ f a (n * b)%Qnn.
    Proof with try ring.
     unfold cmΣ.
     induction n; simpl cm_Sum.
      setoid_replace (QnonNeg.from_nat 0) with 0%Qnn by reflexivity.
      rewrite QnonNeg.mult_0_l zero_width_integral...
     rewrite IHn.
     rewrite CRplus_comm.
     setoid_replace (S n * b)%Qnn with (n * b + b)%Qnn.
      rewrite integral_additive...
     change (S n * b == n * b + b)%Q.
     rewrite S_Qplus...
    Qed.

    (** As promised, we now move toward the aforementioned generalizations of the
    boundedness property. We start by generalizing mid to CR: *)

    Lemma bounded_with_real_mid (from: Q) (width: Qpos) (mid: CR) (r: Qpos):
      (forall x, from <= x <= from+width -> ball r (f x) mid) ->
      ball (width * r) (∫ f from width) (scale width mid).
    Proof with auto.
     intros H d1 d2.
     simpl approximate.
     destruct (Qscale_modulus_pos width d2) as [P E].
     rewrite E. simpl.
     set (v := (exist (Qlt 0) (/ width * d2)%Q P)).
     setoid_replace (d1 + width * r + d2)%Qpos with (d1 + width * (r + v))%Qpos by
       (unfold QposEq; simpl; field)...
     apply regFunBall_Cunit.
     apply integral_bounded_prim.
     intros.
     apply ball_triangle with mid...
     apply ball_approx_r.
    Qed.

    (** Next, we generalize r to QnonNeg: *)

    Lemma bounded_with_nonneg_radius (from: Q) (width: Qpos) (mid: CR) (r: QnonNeg):
      (forall (x: Q), (from <= x <= from+width) -> gball r (f x) mid) ->
      gball (width * r) (∫ f from width) (scale width mid).
    Proof with auto.
     pattern r.
     apply QnonNeg.Qpos_ind.
       intros ?? E.
       split. intros H ?. rewrite <- E. apply H. intros. rewrite E...
       intros H ?. rewrite E. apply H. intros. rewrite <- E...
      rewrite Qmult_0_r gball_0.
      intros.
      apply ball_eq. intro .
      setoid_replace e with (width * (e * Qpos_inv width))%Qpos by (unfold QposEq; simpl; field)...
      apply bounded_with_real_mid.
      intros q ?.
      setoid_replace (f q) with mid...
      apply -> (@gball_0 CR)...
     intros.
     apply (ball_gball (width * q)%Qpos), bounded_with_real_mid.
     intros. apply ball_gball...
    Qed.

    (** Next, we generalize r to a full CR: *)

    Lemma bounded_with_real_radius (from: Q) (width: Qpos) (mid: CR) (r: CR) (rnn: CRnonNeg r):
      (forall (x: Q), from <= x <= from+` width -> CRball r mid (f x)) ->
      CRball (scale width r) (∫ f from width) (scale width mid).
    Proof with auto.
     intro A.
     unfold CRball.
     intros.
     unfold CRball in A.
     setoid_replace q with (width * (q / width))%Q by (simpl; field; auto).
     assert (r <= ' (q / width)).
      apply (mult_cancel_leEq CRasCOrdField) with (' width).
       simpl. apply CRlt_Qlt...
      rewrite mult_commutes.
      change (' width * r <= ' (q / width) * ' width).
      rewrite CRmult_Qmult.
      unfold Qdiv.
      rewrite <- Qmult_assoc.
      rewrite (Qmult_comm (/width)).
      rewrite Qmult_inv_r...
      rewrite Qmult_1_r.
      rewrite CRmult_scale...
     assert (0 <= (q / width))%Q as E.
      apply CRle_Qle.
      apply CRle_trans with r...
      apply -> CRnonNeg_le_0...
     apply (bounded_with_nonneg_radius from width mid (exist _ _ E)).
     intros. simpl. apply gball_sym...
    Qed.

    (** Finally, we generalize to nonnegative width: *)

    Lemma integral_bounded (from: Q) (width: QnonNeg) (mid: CR) (r: CR) (rnn: CRnonNeg r)
      (A: forall (x: Q), (from <= x <= from+` width) -> CRball r mid (f x)):
      CRball (scale width r) (∫ f from width) (scale width mid).
    Proof with auto.
     revert A.
     pattern width.
     apply QnonNeg.Qpos_ind; intros.
       intros ?? E.
       split; intro; intros.
        rewrite <- E. apply H. intros. apply A. rewrite <- E...
       rewrite E. apply H. intros. apply A. rewrite E...
      rewrite zero_width_integral scale_0 scale_0.
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
     assert (lo <= hi) as lohi. apply CRle_trans with (f from); apply A...
     set (r := ' (1#2) * (hi - lo)).
     set (mid := ' (1#2) * (lo + hi)).
     assert (mid - r == lo) as loE by (subst mid r; ring).
     assert (mid + r == hi) as hiE by (subst mid r; ring).
     rewrite <- loE, <- hiE.
     rewrite scale_CRplus scale_CRplus scale_CRopp CRdistance_CRle CRdistance_comm.
     apply CRball.as_distance_bound.
     apply integral_bounded.
      subst r.
      apply CRnonNeg_le_0.
      apply mult_resp_nonneg.
       simpl. apply CRle_Qle...
      rewrite <- (CRplus_opp lo).
      apply (CRplus_le_r lo hi (-lo))...
     intros.
     apply CRball.as_distance_bound, CRdistance_CRle.
     rewrite loE hiE...
    Qed.

    (** We now start working towards unicity. An easy first step is to show
     that the integral can be approximated arbitrarily well by a "rectangle"
     at sufficiently small intervals, where "sufficiently" is of course dictated
     by the mu from uniform continuity: *)

    Lemma gball_integral (e: QposInf) (w: QnonNeg):
      (w <= mu_ex f e)%QnnInf ->
      forall a, gball_ex (w * e)%QnnInf (' w * (f a)) (∫ f a w).
    Proof with auto.
     intros A ?.
     destruct e...
     rename q into e.
     simpl QnnInf.mult.
     apply in_CRgball.
     simpl.
     rewrite <- CRmult_Qmult.
     CRring_replace (' w * f a - ' w * ' e) (' w * (f a - ' e)).
     CRring_replace (' w * f a + ' w * ' e) (' w * (f a + ' e)).
     repeat rewrite CRmult_scale.
     apply (integral_lower_upper_bounded a w (f a - ' e) (f a + ' e)).
     intros x [lo hi].
     apply in_CRball.
     apply (uc_prf f e a x).
     simpl in A.
     destruct (mu f e); [| exact I].
     apply in_Qball.
     split.
      apply Qle_trans with a...
      apply Q.Qplus_le_l with (-a)%Q.
      ring_simplify.
      apply (Qopp_le_compat 0 q)...
     apply Qle_trans with (a + w)%Q...
     apply Qplus_le_compat...
    Qed.

    (** Iterating this result shows that Riemann sums are arbitrarily good approximations: *)

    Lemma Riemann_sums_approximate_integral (a: Q) (w: QnonNeg) (e: QposInf) (iw: QnonNeg) (n: nat):
     (n * iw == w)%Qnn ->
     (iw <= mu_ex f e)%QnnInf ->
     gball_ex (e * w)%QnnInf (cmΣ n (fun i => ' ` iw * f (a + i * ` iw)%Q)) (∫ f a w).
    Proof with auto.
     intros A B.
     rewrite <- A at 2.
     rewrite <- integral_repeated_additive...
     setoid_replace (e * w)%QnnInf with (n * (iw * e))%QnnInf.
      apply CRΣ_gball_ex.
      intros.
      apply gball_integral...
     rewrite QnnInf.mult_assoc.
     change (e * w == (n * iw)%Qnn * e)%QnnInf.
     rewrite A.
     apply QnnInf.mult_comm.
    Qed.

    (** Unicity itself will of course have to be stated w.r.t. *two* integrals: *)

  End singular_props.

  Lemma unique
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
   destruct (split x (mu_ex f (QposInf_mult  ((1 # 2) * e)%Qpos (Qpos_inv x))))%QposInf.
   destruct a0.
   destruct x0.
   simpl in H.
   simpl @snd in H0.
   set ( (((1 # 2) * e)%Qpos * Qpos_inv x))%Qpos in *.
   setoid_replace (e) with (q * x + q * x)%Qpos.
    apply ball_triangle with (cmΣ n (fun i: nat => (' `t * f (a + i * `t)%Q))).
     apply ball_sym.
     apply ball_gball.
     apply (Riemann_sums_approximate_integral a x ((1 # 2) * e / x)%Qpos t n H H0).
    apply ball_gball.
    apply (Riemann_sums_approximate_integral a x ((1 # 2) * e / x)%Qpos t n H H0).
   subst q.
   unfold QposEq.
   simpl.
   rewrite <- Qmult_assoc.
   rewrite (Qmult_comm (/x)).
   rewrite Qmult_inv_r...
   ring.
  Qed.

End integral_interface.

(** If f==g, then an integral for f is an integral for g. *)

Lemma Integrable_proper_l
  (f g: Q_as_MetricSpace --> CR)
   {fint: Integral f}:
  (forall q: Q, f q == g q) ->
   @Integrable f fint -> @Integrable g fint.
Proof with auto.
 constructor.
   replace (@integrate g) with (@integrate f) by reflexivity.
   apply integral_additive...
  replace (@integrate g) with (@integrate f) by reflexivity.
  intros.
  apply integral_bounded_prim...
  intros.
  rewrite (H x)...
 replace (@integrate g) with (@integrate f) by reflexivity.
 apply integral_wd...
Qed.

Lemma integrate_proper
  (f g: Q_as_MetricSpace --> CR)
  {fint: Integral f} {gint: Integral g}
  `{!@Integrable f fint}
  `{!Integrable g}:
  (forall q: Q, f q == g q) ->
  forall (a: Q) (w: QnonNeg),
  @integrate f fint a w == @integrate g gint a w.
Proof.
 intros.
 apply (unique g fint gint).
  apply (Integrable_proper_l f g H0 H).
 assumption.
Qed.

(** Finally, we offer a smart constructor for implementations that would need to recognize and
 treat the zero-width case specially anyway (which is the case for the implementation
with Riemann sums, because there, a positive width is needed to divide the error by). *)

Section extension_to_nn_width.

  Context
    (f: Q_as_MetricSpace --> CR)
    (pre_integral: Q -> Qpos -> CR) (* Note the Qpos instead of QnonNeg. *)
      (* The three properties limited to pre_integral: *)
    (pre_additive: forall (a: Q) (b c: Qpos),
      pre_integral a b + pre_integral (a + `b)%Q c[=]pre_integral a (b + c)%Qpos)
    (pre_bounded: forall (from: Q) (width: Qpos) (mid: Q) (r: Qpos),
      (forall x: Q, from <= x <= from + width -> ball r (f x) (' mid)) ->
      ball (width * r) (pre_integral from width) (' (width * mid)))
    {pre_wd: Proper (Qeq ==> QposEq ==> @st_eq _) pre_integral}.

  Instance integral_extended_to_nn_width: Integral f :=
    fun from => QnonNeg.rect (fun _ => CR)
      (fun _ _ => '0)
      (fun n d _ => pre_integral from (QposMake n d)).

  Let proper: Proper (Qeq ==> QnonNeg.eq ==> @st_eq _) (∫ f).
  Proof with auto.
   intros ?????.
   induction x0 using QnonNeg.rect;
    induction y0 using QnonNeg.rect.
       reflexivity.
     discriminate.
    discriminate.
   intros. apply pre_wd...
  Qed.

  Let bounded (from: Q) (width: Qpos) (mid: Q) (r: Qpos):
    (forall x, from <= x <= from + width -> ball r (f x) (' mid)) ->
    ball (width * r) (∫ f from width) (' (width * mid)).
  Proof.
   induction width using Qpos_positive_numerator_rect.
   apply (pre_bounded from (a#b) mid r).
  Qed.

  Let additive (a: Q) (b c: QnonNeg): ∫ f a b + ∫ f (a + `b)%Q c  == ∫ f a (b + c)%Qnn.
  Proof.
   unfold integrate.
   induction b using QnonNeg.rect;
    induction c using QnonNeg.rect; simpl integral_extended_to_nn_width; intros.
      ring.
     rewrite CRplus_0_l.
     apply pre_wd; unfold QposEq, Qeq; simpl; repeat rewrite Zpos_mult_morphism; ring.
    rewrite CRplus_0_r.
    apply pre_wd; unfold QposEq, Qeq; simpl; repeat rewrite Zpos_mult_morphism; ring.
   rewrite (pre_additive a (QposMake n d) (QposMake n0 d0)).
   apply pre_wd; reflexivity.
  Qed.

  Lemma integral_extended_to_nn_width_correct: Integrable f.
  Proof. constructor; auto. Qed.

End extension_to_nn_width.
