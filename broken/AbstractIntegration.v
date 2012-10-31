(** An abstract interface for integrable uniformly continuous functions from Q to CR,
 with a proof that integrals satisfying this interface are unique. *)

Require Import
 Unicode.Utf8 Program
 CRArith CRabs
 Qauto Qround Qmetric
 stdlib_omissions.P
 stdlib_omissions.Z
 stdlib_omissions.Q
 stdlib_omissions.N.
Require Import metric FromMetric2.

Require Qinf QnonNeg QnnInf CRball.
Import Qinf.notations QnonNeg.notations QnnInf.notations CRball.notations Qabs.

(*Require Import CRtrans ARtrans.*) (* This is almost all CoRN *)

(*Notation Qinf := Qinf.T.

Module Qinf.

Definition le (x y : Qinf) : Prop :=
match y with
| Qinf.finite b =>
  match x with
  | Qinf.finite a => Qle a b
  | Qinf.infinite => False
  end
| Qinf.infinite => True
end.

Instance: Proper (Qinf.eq ==> Qinf.eq ==> iff) le.
Proof.
intros [x1 |] [x2 |] A1 [y1 |] [y2 |] A2; revert A1 A2;
unfold Qinf.eq, canonical_names.equiv, stdlib_rationals.Q_eq; simpl; intros A1 A2;
try contradiction; try reflexivity.
rewrite A1, A2; reflexivity.
Qed.

End Qinf.

Instance Qinf_le : canonical_names.Le Qinf := Qinf.le.*)

Open Local Scope Q_scope.
Open Local Scope uc_scope.
Open Local Scope CR_scope.

SearchAbout CRnonNeg.

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

Lemma CRΣ_gball (f g: nat -> CR) (e : Q) (n : nat):
   (forall m, (m < n)%nat -> gball e (f m) (g m)) ->
   (gball (n * e) (cmΣ n f) (cmΣ n g)).
Proof.
 induction n; [reflexivity |].
 intros.
 rewrite Q.S_Qplus.
 setoid_replace ((n+1) * e)%Q with (e + n * e)%Q by ring.
 unfold cmΣ. simpl @cm_Sum.
 apply CRgball_plus; auto.
Qed.

Hint Immediate ball_refl Qle_refl.

(** Next up, the actual interface for integrable functions. *)

Class Integral (f: Q → CR) := integrate: forall (from: Q) (w: QnonNeg), CR.

Implicit Arguments integrate [[Integral]].

Notation "∫" := integrate.

Section integral_interface.

  Context (f: Q → CR).

  Class Integrable `{!Integral f}: Prop :=
    { integral_additive:
      forall (a: Q) b c, ∫ f a b + ∫ f (a+` b) c == ∫ f a (b+c)%Qnn

    ; integral_bounded_prim: forall (from: Q) (width: Qpos) (mid: Q) (r: Qpos),
      (forall x, from <= x <= from+width -> ball r (f x) ('mid)) ->
      ball (width * r) (∫ f from width) (' (width * mid)%Q)

    ; integral_wd:> Proper (Qeq ==> QnonNeg.eq ==> @st_eq CRasCSetoid) (∫ f) }.

  (* Todo: Show that the sign function is integrable while not locally uniformly continuous. *)

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

    Lemma zero_width_integral q: ∫ f q 0%Qnn == 0.
    Proof with auto.
     apply CRplus_eq_l with (∫ f q 0%Qnn).
     generalize (integral_additive q 0%Qnn 0%Qnn).
     rewrite Qplus_0_r, QnonNeg.plus_0_l, CRplus_0_l...
    Qed.

    (** Iterating the additive property yields: *)

    Lemma integral_repeated_additive (a: Q) (b: QnonNeg) (n: nat):
        cmΣ n (fun i: nat => ∫ f (a + i * ` b) b) == ∫ f a (n * b)%Qnn.
    Proof with try ring.
     unfold cmΣ.
     induction n; simpl @cm_Sum.
      setoid_replace (QnonNeg.from_nat 0) with 0%Qnn by reflexivity.
      rewrite QnonNeg.mult_0_l, zero_width_integral...
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
      rewrite Qmult_0_r, gball_0.
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

    Context `{L : !IsLocallyUniformlyContinuous f lmu}.

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
      gball w a x -> gball w a y -> gball delta x y -> gball eps (f x) (f y).
    Proof.
     intros A A1 A2 A3 A4.
     destruct (luc_prf f lmu a w) as [_ H].
     change (f x) with (restrict f a w (exist _ _ A2)).
     change (f y) with (restrict f a w (exist _ _ A3)).
     apply H; [apply A |].
     destruct (lmu a w eps) as [q |] eqn:A5; [| easy].
     apply (mspc_monotone delta); [apply A1 | apply A4].
    Qed.

    Lemma Riemann_sums_approximate_integral (a: Q) (w: Qpos) (e: Qpos) (iw: Q) (n: nat):
     (n * iw == w)%Q ->
     (iw <= lmu a w e)%Qinf ->
     gball (e * w) (cmΣ n (fun i => 'iw * f (a + i * iw))%CR) (∫ f a w).
    Proof.
     intros A B.
     assert (iw_nn : 0 <= iw) by (apply Qlt_le_weak, (Qmult_pos_r n); [| rewrite A]; Qauto_nonneg).
     set (iw' := exist _ iw iw_nn : QnonNeg ).
     change iw with (QnonNeg.to_Q iw').
     change (n * iw' == w)%Qnn in A.
     rewrite <- A.
     rewrite <- integral_repeated_additive.
     setoid_replace (e * w)%Q with (n * (iw * e))%Q by
       (unfold QnonNeg.eq in A; simpl in A;
        rewrite Qmult_assoc; rewrite A; apply Qmult_comm).
     apply CRΣ_gball.
     intros m H.
     rewrite CRmult_scale.
     apply gball_sym. apply CRball.rational.
     setoid_replace (' (iw * e)) with (scale iw' (' ` e)) by now rewrite <- scale_Qmult.
     apply integral_bounded; [apply CRnonNegQpos |].
     intros x [A1 A2]. apply CRball.rational. apply (luc_gball a w (`iw')); trivial.
     + apply ball_gball, Qball_Qabs.
       setoid_replace (a - (a + m * iw')) with (- (m * iw')) by ring.
       rewrite Qabs_opp. apply Qabs_le_nonneg; [Qauto_nonneg |].
       apply Qle_trans with (y := (n * iw')).
       apply Qmult_le_compat_r. apply Qlt_le_weak. rewrite <- Zlt_Qlt. now apply inj_lt.
       apply (proj2_sig iw').
       change (n * iw' == w) in A. rewrite <- A; reflexivity.
     + apply gball_Qabs, Qabs_Qle_condition.
       split.
       apply Qplus_le_l with (z := x), Qplus_le_l with (z := w).
       setoid_replace (- w + x + w) with x by ring. setoid_replace (a - x + x + w) with (a + w) by ring.
       apply Qle_trans with (y := (a + m * ` iw' + ` iw')); [easy |].
       setoid_rewrite <- (Qmult_1_l (` iw')) at 2. change 1%Q with (inject_Z (Z.of_nat 1)).
       rewrite <- Qplus_assoc, <- Qmult_plus_distr_l, <- Zplus_Qplus, <- Nat2Z.inj_add.
       apply Qplus_le_r. change (n * iw' == w) in A. rewrite <- A.
       apply Qmult_le_compat_r. rewrite <- Zle_Qle. apply inj_le. rewrite Plus.plus_comm.
       now apply lt_le_S.
       apply (proj2_sig iw').
       apply Qplus_le_l with (z := x), Qplus_le_l with (z := -w).
       setoid_replace (a - x + x + - w) with (a - w) by ring.
       setoid_replace (w + x + - w) with x by ring.
       apply Qle_trans with (y := a). rewrite <- (Qplus_0_r a) at 2.
       apply Qplus_le_r. change 0 with (-0). apply Qopp_le_compat, Qlt_le_weak, (proj2_sig w).
       apply Qle_trans with (y := a + m * ` iw'); [| easy].
       rewrite <- (Qplus_0_r a) at 1. apply Qplus_le_r, Qmult_le_0_compat; [apply Qle_nat | apply (proj2_sig iw')].
     + apply gball_Qabs, Qabs_Qle_condition; split.
       apply (Qplus_le_r (x + `iw')).
       setoid_replace (x + `iw' + - `iw') with x by ring.
       setoid_replace (x + `iw' + (a + m * iw' - x)) with (a + m * iw' + `iw') by ring. apply A2.
       apply (Qplus_le_r (x - `iw')).
       setoid_replace (x - `iw' + (a + m * iw' - x)) with (a + m * iw' - `iw') by ring.
       setoid_replace (x - `iw' + `iw') with x by ring.
       apply Qle_trans with (y := a + m * iw'); [| easy].
       apply Qminus_less. apply (proj2_sig iw').
    Qed.

(*    Program Definition step (w : Qpos) (n : positive) : QnonNeg := exist _ (w * (1 # n)) _.
    Next Obligation. Qauto_nonneg. Qed.*)

    Definition step (w : Q) (n : positive) : Q := w * (1 # n).

    Lemma step_mult (w : Q) (n : positive) : (n : Q) * step w n == w.
    Proof.
      unfold step.
      rewrite Qmake_Qdiv. unfold Qdiv. rewrite Qmult_1_l, (Qmult_comm w), Qmult_assoc.
      rewrite Qmult_inv_r, Qmult_1_l; [reflexivity | auto with qarith].
    Qed.

    Definition riemann_sum (a : Q) (w : Q) (n : positive) :=
      let iw := step w n in
        cmΣ (Pos.to_nat n) (fun i => 'iw * f (a + i * iw))%CR.

    Lemma Riemann_sums_approximate_integral' (a : Q) (w : Qpos) (e : Qpos) (n : positive) :
      (step w n <= lmu a w e)%Qinf ->
      gball (e * w) (riemann_sum a w n) (∫ f a w).
    Proof.
      intro A; unfold riemann_sum. apply Riemann_sums_approximate_integral; [| easy].
      unfold step. change (Pos.to_nat n * (w * (1 # n)) == w).
      rewrite positive_nat_Z. unfold inject_Z. rewrite !Qmake_Qdiv; field; auto.
    Qed.

    Lemma Riemann_sums_approximate_integral'' (a : Q) (w : Qpos) (e : Qpos) :
      exists N : positive, forall n : positive, (N <= n)%positive ->
        gball e (riemann_sum a w n) (∫ f a w).
    Proof.
      set (N := Z.to_pos (Qceiling (comp_inf (λ x, w / x) (lmu a w) 0 (e / w)))).
      exists N; intros n A. setoid_replace (QposAsQ e) with ((e / w)%Qpos * w)
        by (change (e == e / w * w); field; auto).
      apply Riemann_sums_approximate_integral'.
      unfold step, comp_inf in *. change ((w * (1 # n))%Q <= lmu a w (e / w))%Qinf.
      assert (A2 : 0 < e / w) by (apply Qmult_lt_0_compat; [| apply Qinv_lt_0_compat]; auto).
      destruct (lmu a w (e / w)) as [mu |] eqn:A1; [| easy].
      assert (A3 := @uc_pos _ _ _ _ _ _ (L a w) (e / w) A2). rewrite A1 in A3.
      change (0 < mu) in A3.
      rewrite Qmake_Qdiv, injZ_One. unfold Qdiv. rewrite Qmult_assoc, Qmult_1_r.
      change (w / n <= mu). apply Qle_div_l; auto.
      subst N. now apply Z.Ple_Zle_to_pos, Q.Zle_Qle_Qceiling in A.
    Qed.

  End singular_props.

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
End integral_interface.

(** If f==g, then an integral for f is an integral for g. *)

Lemma Integrable_proper_l (f g: Q → CR) {fint: Integral f}:
  canonical_names.equiv f g → Integrable f → @Integrable g fint.
Proof with auto.
 constructor.
   replace (@integrate g) with (@integrate f) by reflexivity.
   intros.
   apply (integral_additive f).
  replace (@integrate g) with (@integrate f) by reflexivity.
  intros.
  apply (integral_bounded_prim f)...
  intros.
  rewrite (H x x (refl_equal _))...
 replace (@integrate g) with (@integrate f) by reflexivity.
 apply (integral_wd f)...
Qed.

Import abstract_algebra.

(* Should this lemma be used to CoRN.reals.fast.CRabs? That file does not use
type class notations from canonical_names like ≤ *)

Lemma CRabs_nonneg (x : CR) : 0 ≤ CRabs x.
Proof.
apply -> CRabs_cases; [| apply _ | apply _].
split; [trivial | apply (proj1 (rings.flip_nonpos_negate x))].
Qed.

Add Ring Q : (rings.stdlib_ring_theory CR).

Section RiemannSumBounds.

Lemma sum_empty (M : CMonoid) (f : nat -> M) : cmΣ 0 f = [0].
Proof. reflexivity. Qed.

Lemma sum_succ (M : CMonoid) (n : nat) (f : nat -> M) : cmΣ (S n) f = f n [+] cmΣ n f.
Proof. reflexivity. Qed.

Context (f : Q -> CR).

Lemma sum_const (n : nat) (m : CR) : cmΣ n (λ _, m) = m * '(n : Q).
Proof.
induction n as [| n IH].
+ rewrite sum_empty. change (0 = m * 0). symmetry; apply rings.mult_0_r.
+ rewrite sum_succ, IH, S_Qplus, <- CRplus_Qplus.
  change (m + m * '(n : Q) = m * ('(n : Q) + 1)). ring.
Qed.

Lemma mult_comm `{SemiRing R} : Commutative (.*.).
Proof. apply commonoid_commutative with (Aunit := one), _. Qed.

Lemma mult_assoc `{SemiRing R} (x y z : R) : x * (y * z) = x * y * z.
Proof. apply sg_ass, _. Qed.

Lemma riemann_sum_const (a : Q) (w : Q) (m : CR) (n : positive) :
  riemann_sum (λ _, m) a w n = 'w * m.
Proof.
unfold riemann_sum. rewrite sum_const, positive_nat_Z.
change ('step w n * m * '(n : Q) = 'w * m).
rewrite (mult_comm _ ('(n : Q))), mult_assoc, CRmult_Qmult, step_mult; reflexivity.
Qed.

Require Import CRtrans ARtrans. (* This is almost all CoRN *)
(*SearchAbout "ball" "mult".

Qball_Qmult_Q_r:
  ∀ (d : Qpos) (z x y : Q),
  Qball (d / QabsQpos z) x y → Qball d (x * z) (y * z)
Qball_Qmult_Q_l:
  ∀ (d : Qpos) (z x y : Q),
  Qball (d / QabsQpos z) x y → Qball d (z * x) (z * y)
Qball_Qmult_r:
  ∀ (d z : Qpos) (x y : Q), Qball (d / z) x y → Qball d (x * z) (y * z)
Qball_Qmult_l:
  ∀ (d z : Qpos) (x y : Q), Qball (d / z) x y → Qball d (z * x) (z * y)*)

SearchAbout "stable".
SearchAbout CRabs scale.

Lemma gball_mult (e a : Q) (x y : CR) :
  gball e x y -> gball (Qabs a * e) ('a * x) ('a * y).
Proof.
SearchAbout gball.
SearchAbout CRabs Qabs.
SearchAbout (abs _ * abs _)%mc.

CR_abs_obligation_1:
  ∀ x : CR, (0 ≤ x → CRabs x = x) ∧ (x ≤ 0 → CRabs x = - x)
CRball.gball_CRabs:
  ∀ (r : Q) (x y : CR), gball r x y ↔ CRabs (x - y)%CR <= (' r)%CR
in_CRgball:
  ∀ (r : Q) (x y : CR), (x - ' r)%CR <= y ∧ y <= (x + ' r)%CR ↔ gball r x y


Lemma riemann_sum_bounds (a w : Q) (m : CR) (e : Q) (n : positive) :
  0 ≤ w -> (forall (x : Q), (a ≤ x ≤ a + w) -> gball e (f x) m) ->
  gball (w * e) (riemann_sum f a w n) ('w * m).
Proof.
intros w_nn A. rewrite <- (riemann_sum_const a w m n). unfold riemann_sum.
rewrite <- (step_mult w n), <- (Qmult_assoc n _ e), <- (positive_nat_Z n).
apply CRΣ_gball. intros k A1.
SearchAbout (ball (_ * _) _ _).







End RiemannSumBounds.


Section IntegralBound.

Context (f : Q -> CR) `{Integrable f}.

Add Ring CR : (rings.stdlib_ring_theory CR).

Lemma scale_0_r (x : Q) : scale x 0 = 0.
Proof. rewrite <- CRmult_scale; change (cast Q CR x * 0 = 0); ring. Qed.

Require Import propholds.

Lemma integral_abs_bound (from : Q) (width : Qpos) (M : Q) :
  (forall (x : Q), (from ≤ x ≤ from + width) -> CRabs (f x) ≤ 'M) ->
  CRabs (∫ f from width) ≤ '(`width * M).
Proof.
intro A. rewrite <- (CRplus_0_r (∫ f from width)), <- CRopp_0.
apply CRball.as_distance_bound, CRball.rational. rewrite <- (scale_0_r width).
assert (A1 : 0 ≤ M).
+ apply CRle_Qle. apply CRle_trans with (y := CRabs (f from)); [apply CRabs_nonneg |].
  apply A. split; [reflexivity |].
  apply semirings.nonneg_plus_le_compat_r; change (0 <= width)%Q; Qauto_nonneg.
+ change M with (QnonNeg.to_Q (exist _ M A1)).
  apply bounded_with_nonneg_radius; [easy |].
  intros x A2. apply CRball.gball_CRabs. change (f x - 0%mc)%CR with (f x - 0).
  rewrite rings.minus_0_r; now apply A.
Qed.


(*
Section IntegralOfSum.

Context (f g : Q -> CR) `{Integral f, !Integrable f} `{Integral g, !Integrable g}.

Notation "f +1 g" := (λ x, f x + g x) (at level 50, left associativity).

Theorem integral_sum (a : Q) (w : Qpos) : ∫ (f +1 g) a w = ∫ f a w + ∫ g a w.
*)






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

(** Finally, we offer a smart constructor for implementations that would need to recognize and
 treat the zero-width case specially anyway (which is the case for the implementation
with Riemann sums, because there, a positive width is needed to divide the error by). *)

Section extension_to_nn_width.

  Context
    (f: Q → CR)
    (pre_integral: Q → Qpos → CR) (* Note the Qpos instead of QnonNeg. *)
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
*)
