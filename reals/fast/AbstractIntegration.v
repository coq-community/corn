(* An abstract interface for integrable uniformly continuous functions from Q to CR,
 with a proof that integrals satisfying this interface are unique. *)

Require Import
 Program
 CRArith CRabs
 Qauto Qround Qmetric
 stdlib_omissions.P stdlib_omissions.Z stdlib_omissions.Q.

Require QnonNeg QnnInf CRball.
Import QnonNeg.notations QnnInf.notations CRball.notations.

Set Automatic Introduction.

Open Local Scope Q_scope.
Open Local Scope uc_scope.
Open Local Scope CR_scope.

(* Any nonnegative width can be split up into an integral number of
 equal-sized pieces no bigger than a given bound: *)

Definition split (w: QnonNeg) (bound: QposInf):
  { x: nat * QnonNeg | (fst x * snd x == w)%Qnn /\ (snd x <= bound)%QnnInf }.
Proof with simpl; auto with *.
 unfold QnonNeg.eq. simpl.
 destruct bound; simpl.
  Focus 2. exists (1%nat, w). simpl. split... ring.
 destruct (QnonNeg.is_pos w) as [[x e] | e].
  set (p := QposCeiling (x / q)).
  exists (nat_of_P p, ((x / p)%Qpos):QnonNeg)...
  split.
   rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P, <- e.
   change (p * (x * / p) == x)%Q.
   field. discriminate.
  subst p.
  apply Qle_shift_div_r...
  rewrite QposCeiling_Qceiling. simpl.
  setoid_replace (x:Q) with (q * (x * / q))%Q at 1 by (simpl; field)...
  do 2 rewrite (Qmult_comm q).
  apply Qmult_le_compat_r...
 exists (0%nat, 0%Qnn)...
Qed.

(* Riemann sums will play an important role in the theory about integrals, so let's
define very simple summation and a key property thereof: *)

Fixpoint enum (n: nat): list nat :=
  match n with
  | O => nil
  | S n' => n' :: enum n'
  end.

Definition cmΣ {M: CMonoid} (n: nat) (f: nat -> M): M := cm_Sum M (map f (enum n)).

(* If the elementwise distance between two summations over the same domain
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

(* Next up, the actual interface for integrable functions. *)

Section integral_interface.

  Variable (f: Q_as_MetricSpace --> CR).

  Class Integral := integrate: forall (from: Q) (w: QnonNeg), CR.

  Notation "∫" := integrate.

  Class Integrable `{Integral}: Prop :=
    { integral_additive:
      forall (a: Q) b c, ∫ a b + ∫ (a+` b) c == ∫ a (b+c)%Qnn
    ; integral_bounded_prim: forall (from: Q) (width: Qpos) (mid: CR) (r: Qpos),
      (forall x, from <= x <= from+width -> ball r (f x) mid) ->
      ball (width * r) (∫ from width) (scale width mid)
    ; integral_wd:> Proper (Qeq ==> QnonNeg.eq ==> @st_eq CRasCSetoid) ∫
   }.

  (* The boundedness property is stated very primitively here, in that r is a Qpos instead of a CR,
   and w is a Qpos instead of a QnonNeg. This means that it's easy to show that particular
   implementations satisfy this interface, but hard to use this property directly. Hence, we
   will show in a moment that the property as stated actually implies its generalization with r in CR
   and w in QnonNeg. *)

  (* Note: Other ways to state the property still more primitively (and thus more easily provable) might
   be (1) to make the inequalities in "from <= x <= from+width" strict, and (2) to make mid a Q. *)

  Section singular_props. (* Properties we can derive for a single integral of a function. *)

    Context `{Int: Integrable}.

    (* The additive property implies that zero width intervals have zero surface: *)

    Lemma zero_width_integral q: ∫ q 0%Qnn == '0.
    Proof with auto.
     apply CRplus_eq_l with (∫ q 0%Qnn).
     generalize (integral_additive q 0%Qnn 0%Qnn).
     rewrite Qplus_0_r QnonNeg.plus_0_l CRplus_0_l...
    Qed.

    (* Iterating the additive property yields: *)

    Lemma integral_repeated_additive (a: Q) (b: QnonNeg) (n: nat):
        cmΣ n (fun i: nat => ∫ (a + i * ` b) b) == ∫ a (n * b)%Qnn.
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

    (* As promised, we now move toward the aforementioned generalizations of the
    boundedness property. We start by generalizing r to QnonNeg. *)

    Lemma bounded_with_nonneg_radius (from: Q) (width: Qpos) (mid: CR) (r: QnonNeg):
      (forall (x: Q), (from <= x <= from+width) -> gball r (f x) mid) ->
      gball (width * r) (∫ from width) (scale width mid)%CR.
    Proof with auto.
     intro A.
     destruct (QnonNeg.is_pos r) as [[x E] | E].
      rewrite <- E.
      apply (ball_gball (width * x)%Qpos), integral_bounded_prim.
      intros. apply ball_gball.
      change (x == r)%Q in E. rewrite E...
     rewrite E Qmult_0_r gball_0.
     apply ball_eq. intro .
     setoid_replace e with (width * (e * Qpos_inv width))%Qpos by (unfold QposEq; simpl; field)...
     apply integral_bounded_prim.
     intros q ?.
     setoid_replace (f q) with mid...
     apply -> (@gball_0 CR).
     change (r == 0)%Q in E.
     rewrite <- E...
    Qed.

    (* Next, we generalize r to a full CR: *)

    Lemma bounded_with_real_radius (from: Q) (width: Qpos) (mid: CR) (r: CR) (rnn: CRnonNeg r):
      (forall (x: Q), from <= x <= from+` width -> CRball r mid (f x)) ->
      CRball (scale width r) (∫ from width) (scale width mid).
    Proof with auto.
     intros...
     unfold CRball.
     intros.
     unfold CRball in H0.
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

    (* Finally, we generalize to nonnegative width: *)

    Lemma integral_bounded (from: Q) (width: QnonNeg) (mid: CR) (r: CR) (rnn: CRnonNeg r)
      (A: forall (x: Q), (from <= x <= from+` width) -> CRball r mid (f x)):
      CRball (scale width r) (∫ from width) (scale width mid).
    Proof with auto.
     destruct (QnonNeg.is_pos width) as [[??]|?].
      rewrite <- e.
      apply (bounded_with_real_radius from x mid r rnn).
      intros. apply A. rewrite <- e...
     rewrite e zero_width_integral scale_0 scale_0.
     apply CRball.reflexive, CRnonNeg_0.
    Qed.

    (* In some context a lower-bound-upper-bound formulation is more convenient
    than the the ball-based formulation: *)

    Lemma integral_lower_upper_bounded (from: Q) (width: QnonNeg) (lo hi: CR):
      (forall (x: Q), (from <= x <= from+` width)%Q -> lo <= f x /\ f x <= hi) ->
      scale (` width) lo <= ∫ from width /\ ∫ from width <= scale (` width) hi.
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

    (* We now start working towards unicity. An easy first step is to show
     that the integral can be approximated arbitrarily well by a "rectangle"
     at sufficiently small intervals, where "sufficiently" is of course dictated
     by the mu from uniform continuity: *)

    Lemma gball_integral (e: QposInf) (w: QnonNeg):
      (w <= mu_ex f e)%QnnInf ->
      forall a, gball_ex (w * e)%QnnInf (' w * (f a)) (∫ a w).
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

    (* Iterating this result shows that Riemann sums are arbitrarily good approximations: *)

    Lemma Riemann_sums_approximate_integral (a: Q) (w: QnonNeg) (e: QposInf) (iw: QnonNeg) (n: nat):
     (n * iw == w)%Qnn ->
     (iw <= mu_ex f e)%QnnInf ->
     gball_ex (e * w)%QnnInf (cmΣ n (fun i => ' ` iw * f (a + i * ` iw)%Q))%CR (∫ a w).
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

    (* Unicity itself will of course have to be stated w.r.t. *two* integrals: *)

  End singular_props.

  Lemma unique
    (c1: Integral)
    (c2: Integral)
    (P1: @Integrable c1)
    (P2: @Integrable c2):
  forall (a: Q) (w: QnonNeg),
    (@integrate c1 a w == @integrate c2 a w)%CR.
  Proof with auto.
   intros. apply ball_eq. intros.
   destruct (QnonNeg.is_pos w).
    destruct s.
    rewrite <- e0.
    clear w e0.
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
    rewrite Qmult_inv_r.
     ring.
    apply Qpos_nonzero.
   rewrite e0.
   repeat rewrite zero_width_integral...
  Qed.

End integral_interface.
