(** A straightforward implementation of the abstract integration interface
 in AbstractionIntegration using Riemann sums. The sole product of
 this module are the Integrate and Integrable type class instances.
 Do not prove any additional properties about this implementation; all we
 care about is that it implements the abstract integration interface!
 This implementation works for any uniformly continuous function, which
 makes it relatively generic, but it also means that it is fairly inefficient. *)

Require Import CoRN.algebra.RSetoid.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.UniformContinuity.
Require Import
  CoRN.stdlib_omissions.List Coq.Numbers.Natural.Peano.NPeano Coq.Unicode.Utf8
  Coq.QArith.QArith Coq.QArith.Qabs
  CoRN.model.totalorder.QposMinMax CoRN.util.Qsums
  CoRN.model.metric2.Qmetric CoRN.model.setoids.Qsetoid (* Needs imported for Q_is_Setoid to be a canonical structure *)
  CoRN.reals.fast.CRArith (*AbstractIntegration*)
  QnonNeg
  CoRN.util.Qgcd
  Coq.Program.Program
  CoRN.reals.fast.uneven_CRplus
  CoRN.stdlib_omissions.P
  CoRN.stdlib_omissions.Z
  CoRN.stdlib_omissions.Q
  CoRN.tactics.Qauto
  CoRN.ode.metric CoRN.ode.FromMetric2
  MathClasses.implementations.stdlib_rationals.

Import QnonNeg.notations QnonNeg.coercions Qinf.coercions.

Bind Scope Q_scope with Q.
Local Open Scope Q_scope.

Lemma gball_mspc_ball {X : MetricSpace} (r : Q) (x y : X) :
  ball r x y <-> mspc_ball r x y.
Proof. reflexivity. Qed.

Lemma ball_mspc_ball {X : MetricSpace} (r : Qpos) (x y : X) :
  ball (proj1_sig r) x y <-> mspc_ball r x y.
Proof. reflexivity. Qed.

Class Integral (f: Q → CR) := integrate: forall (from: Q) (w: QnonNeg), CR.

Arguments integrate f {Integral}.

Notation "∫" := integrate.

Section integral_interface.

  Open Scope CR_scope.

  (*Context (f: Q → CR).*)

  Class Integrable `{!Integral f}: Prop :=
    { integral_additive:
      forall (a: Q) b c, ∫ f a b + ∫ f (a+` b) c == ∫ f a (b+c)%Qnn

    ; integral_bounded_prim: forall (from: Q) (width: Qpos) (mid: Q) (r: Qpos),
      (forall x, from <= x <= from+ proj1_sig width -> ball (proj1_sig r) (f x) ('mid)) ->
      ball (proj1_sig (width * r)%Qpos) (∫ f from (from_Qpos width)) (' (proj1_sig width * mid)%Q)

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

End integral_interface.

Arguments Integrable f {_}.

(** We offer a smart constructor for implementations that would need to recognize and
 treat the zero-width case specially anyway (which is the case for the implementation
with Riemann sums, because there, a positive width is needed to divide the error by). *)

Section extension_to_nn_width.

  Open Scope CR_scope.

  Context
    (f: Q → CR)
    (pre_integral: Q → Qpos → CR) (* Note the Qpos instead of QnonNeg. *)
      (* The three properties limited to pre_integral: *)
    (pre_additive: forall (a: Q) (b c: Qpos),
      pre_integral a b + pre_integral (a + `b)%Q c[=]pre_integral a (b + c)%Qpos)
    (pre_bounded: forall (from: Q) (width: Qpos) (mid: Q) (r: Qpos),
      (forall x: Q, from <= x <= from + proj1_sig width -> ball (proj1_sig r) (f x) (' mid)) ->
      ball (proj1_sig (width * r)%Qpos) (pre_integral from width) (' (proj1_sig width * mid)%Q))
    {pre_wd: Proper (Qeq ==> QposEq ==> @st_eq _) pre_integral}.

  Instance integral_extended_to_nn_width: Integral f :=
    fun from => QnonNeg.rect (fun _ => CR)
      (fun _ _ => '0%Q)
      (fun n d _ => pre_integral from (exist (Qlt 0) (n # d) eq_refl)).

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
    (forall x, from <= x <= from + proj1_sig width -> ball (proj1_sig r) (f x) (' mid)) ->
    ball (proj1_sig (width * r)%Qpos) (∫ f from (from_Qpos width)) (' (proj1_sig width * mid)%Q).
  Proof.
    destruct width as [[n d] wpos].
    destruct n as [|n|n]. inversion wpos. 2: inversion wpos.
    apply (pre_bounded from (n#d) mid r).
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
    rewrite (pre_additive a (exist (Qlt 0) (n#d) eq_refl)
                          (exist (Qlt 0) (n0#d0) eq_refl)).
   apply pre_wd; reflexivity.
  Qed.

  Lemma integral_extended_to_nn_width_correct: Integrable f.
  Proof. constructor; auto. Qed.

End extension_to_nn_width.

Open Scope uc_scope.

Hint Resolve Qpos_nonzero.
Hint Immediate Q.Qle_nat.
Hint Resolve Qmult_le_0_compat.
Hint Resolve QnonNeg.Qplus_nonneg.

Lemma half_Qpos (q: Qpos): proj1_sig q * (1#2) <= proj1_sig q.
Proof.
 intros.
 rewrite <- (Qmult_1_r (proj1_sig q)) at 2.
 apply Q.Qmult_le_compat_l.
 discriminate. apply Qpos_nonneg.
Qed.

Hint Immediate half_Qpos.

Lemma Qball_ex_plus_r e (x y y' : Q):
  @ball_ex Q_as_MetricSpace e y y' -> @ball_ex Q_as_MetricSpace e (x + y) (x + y').
Proof. destruct e. apply Qball_plus_r. intuition. Qed.

Definition plus_half_times (x y: Q): Q := x * y + (1#2)*y.

Lemma ball_ex_symm (X : MetricSpace) (e : QposInf) (x y : X) :
  ball_ex e x y -> ball_ex e y x.
Proof. destruct e as [e |]; [apply ball_sym | trivial]. Qed.

Lemma Pos2Nat_nonneg : forall p:positive,
    Pos.to_nat p <> O.
Proof.
  intros p abs. pose proof (Pos2Nat.is_pos p).
  rewrite abs in H. inversion H.
Qed.

Section definition.

  Add Field Qfield : Qsft
   (decidable Qeq_bool_eq,
    completeness Qeq_eq_bool,
    constants [Qcst],
    power_tac Qpower_theory [Qpow_tac]).

  Context (f: Q -> CR) `{UC : !IsLocallyUniformlyContinuous f lmu}.

  Instance luc_proper_st_eq : Proper (Qeq ==> @st_eq CR) f.
  Proof.
    intros x y exy a b. apply ball_0 in exy.
    pose proof (luc_proper f x y exy a b).
    rewrite Qplus_0_r in H. exact H.
  Qed.

  (** Note that in what follows we don't specialize for [0,1] or [0,w] ranges first. While this
  would make the definition marginally cleaner, the resulting definition is harder to prove
  correct. Part of the reason for this is that key primitives (such as mu and approximate)
  don't come with Proper proofs, which means that common sense reasoning about
  those operations with their arguments transformed doesn't work well. *)

  (* Reimplementation of Qpossec.QposCeiling that takes a Q instead of a Qpos *)

  Definition QposCeiling (q : Q) : positive :=
  match Qround.Qceiling q with
  | Zpos p => p
  | _ => 1%positive
  end.

  Lemma QposCeiling_Qceiling (q : Qpos)
    : Z.pos (QposCeiling (proj1_sig q)) = Qround.Qceiling (proj1_sig q).
  Proof with auto with qarith.
   unfold QposCeiling. destruct q as [q qpos]. simpl.
   pose proof Qround.Qle_ceiling q.
   destruct (Qround.Qceiling q); try reflexivity; exfalso; destruct q; simpl in *.
    exact (Qlt_not_le _ _ qpos H).
    apply (Qlt_not_le _ _ qpos).
   apply Qle_trans with (Zneg p)...
  Qed.

  Definition intervals (from: Q) (w: Qpos) (error: Qpos): positive :=
  match lmu from (proj1_sig w) (proj1_sig error / proj1_sig w) with
    (* Todo: This is nice and simple, but suboptimal. Better would be to take the luc_mu
     around the midpoint and with radius (w/2). *)
  | Qinf.infinite => 1%positive
  | Qinf.finite x => QposCeiling ((1#2) * proj1_sig w / x)
  end.

  Definition approx (from: Q) (w: Qpos) (e: Qpos): Q :=
    let halferror := (e * (1#2))%Qpos in
    let ints := intervals from w halferror in
    let iw := (proj1_sig w / ints) in
    let halfiw := ((1#2) * iw) in
    fastΣ (nat_of_P ints)
          (fun i => approximate (f (from + (i * iw + halfiw)))
                             (Qpos2QposInf (halferror * Qpos_inv w))) * iw.

  (** In several places in the correctness proof, we will be comparing different
   Riemann sums over the same range divided into different numbers of intervals.
   For these cases, the following lemma is very useful. *)

  Hint Resolve  Qinv_le_0_compat Qmult_le_0_compat.
  Hint Immediate Zle_0_POS Zlt_0_POS.

  Lemma sampling_over_subdivision (fr: Q) (i: nat) (t: positive) (he wb: Qpos) :
    (i < Pos.to_nat (intervals fr wb he * t))%nat ->
    ball (proj1_sig (he * Qpos_inv wb)%Qpos)
         (f (fr + plus_half_times (i / Pos.to_nat t)%nat (proj1_sig wb * / Zpos (intervals fr wb he))))
         (f (fr + i * / Zpos (intervals fr wb he * t) * proj1_sig wb)).
  Proof with auto.
   intro ile.
   unfold plus_half_times.
   apply ball_sym.
   assert (A1 : Qball (proj1_sig wb) fr (fr + i * / Zpos (intervals fr wb he * t) * proj1_sig wb)).
   { rewrite <- (Qplus_0_r fr) at 1.
    apply Qball_plus_r.
    apply in_Qball.
    split.
     apply Qle_trans with 0...
     unfold Qminus.
     rewrite Qplus_0_l.
     apply (Qopp_le_compat 0). apply Qpos_nonneg.
     apply Qmult_le_0_compat. auto. apply Qpos_nonneg.
    rewrite Qplus_0_l.
    apply (Qle_trans _ (1 * `wb)).
    apply Qmult_le_compat_r. 2: apply Qpos_nonneg.
    2: rewrite Qmult_1_l; apply Qle_refl.
    apply Qmult_le_r with (Zpos (intervals fr wb he * t))...
    rewrite <- Qmult_assoc.
    rewrite Qmult_inv_r.
     rewrite Qmult_1_r.
     rewrite Qmult_1_l.
     rewrite <- Zle_Qle.
     rewrite <- ZL9.
     apply inj_le; auto with arith.
    intro.
    assert (0 < / (intervals fr wb he * t)%positive).
     apply Qinv_lt_0_compat...
    revert H0.
    rewrite H.
    apply (Qlt_irrefl 0). }
   assert
     (A2 : mspc_ball
        (lmu fr (proj1_sig wb) (proj1_sig he / proj1_sig wb))
        (fr + i / ((intervals fr wb he * t) #1) * proj1_sig wb)
        (fr + ((i / Pos.to_nat t)%nat * (proj1_sig wb / ((intervals fr wb he)#1))
               + (1 # 2) * (proj1_sig wb / ((intervals fr wb he)#1))))).
   unfold intervals.
    destruct (lmu fr (proj1_sig wb) (proj1_sig he / proj1_sig wb))
      as [q |] eqn:L; [| apply mspc_inf].
    (* apply gball_mspc_ball. does not change the goal *)
    unfold mspc_ball, msp_mspc_ball.
    assert (q_pos : 0 < q).
    { change (Qinf.lt 0 q). rewrite <- L.
      apply (uc_pos (restrict f fr (proj1_sig wb))). apply UC.
      apply (Qpos_ispos (he * Qpos_inv wb)). }
    set (q' := exist _ q q_pos : Qpos).
    change q with (proj1_sig q').
    apply ball_sym, Qball_plus_r.
    change ((1 # 2) * proj1_sig wb / proj1_sig q')%Q
      with (proj1_sig ((1 # 2) * wb * Qpos_inv q')%Qpos).
    set (mym := QposCeiling (proj1_sig ((1 # 2) * wb * Qpos_inv q')%Qpos)).
    apply ball_weak_le with (proj1_sig (wb * (1#2) * Qpos_inv (mym#1))%Qpos).
    simpl.
    rewrite (Qmult_comm (proj1_sig wb)).
     subst mym.
     rewrite QposCeiling_Qceiling.
     apply Qle_shift_div_r...
     apply Qlt_le_trans with (proj1_sig ((1#2) * wb * Qpos_inv q')%Qpos)...
     apply Qround.Qle_ceiling.
     setoid_replace ((1#2) * proj1_sig wb)
       with (proj1_sig (q' * ((1#2) * wb * Qpos_inv q'))%Qpos).
      apply Qmult_le_l. exact q_pos.
      apply Qround.Qle_ceiling. simpl. field.
      intro abs. clear q'. rewrite abs in q_pos.
      exact (Qlt_irrefl 0 q_pos).
    apply Qball_Qdiv_inv with (Qpos_inv (mym#1) * wb)%Qpos.
    simpl. 
    field_simplify...
    unfold Qdiv.
    rewrite Qmult_plus_distr_l.
    field_simplify...
    try rewrite Qdiv_1_r.
    setoid_replace (proj1_sig wb * (1 # 2) * / (mym#1) * / (/ (mym#1) * proj1_sig wb))%Q
      with (1#2).
    Focus 2.
    simpl. field. split; try discriminate... 
     rewrite Zdiv.div_Zdiv...
     rewrite Q.Zdiv_Qdiv.
     setoid_replace ((mym # 1) * i / ((mym * t)%positive # 1))
       with (i / t).
     rewrite positive_nat_Z.
     apply (Qfloor_ball (i/t)).
     unfold Qeq; simpl. destruct i. reflexivity. simpl.
     do 2 rewrite Pos.mul_1_r. rewrite Pos.mul_assoc.
     rewrite (Pos.mul_comm mym). reflexivity.
     discriminate. split. discriminate.
     split. 2: apply Qpos_nonzero.
     unfold Qeq; discriminate.
     split. discriminate. apply Qpos_nonzero.
   assert (A3 : Qball (proj1_sig wb) fr (fr + ((i / Pos.to_nat t)%nat * (proj1_sig wb * / Zpos (intervals fr wb he)) + (1 # 2) * (proj1_sig wb * / Zpos (intervals fr wb he))))).
   { set (n := intervals fr wb he).
    rewrite <- (Qplus_0_r fr) at 1.
    apply Qball_plus_r.
    apply in_Qball; unfold Qminus; rewrite !Qplus_0_l; split.
    apply Qle_trans with (y := 0).
     apply (Qopp_le_compat 0), Qpos_nonneg.
     Qauto_nonneg. 
     rewrite <- Qmult_plus_distr_l, (Qmult_comm (proj1_sig wb)), Qmult_assoc.
     apply (Qle_trans _ (1 * proj1_sig wb)).
     2: simpl; rewrite Qmult_1_l; apply Qle_refl.
    apply Qmult_le_compat_r; [| auto].
    apply Qdiv_le_1. split. Qauto_nonneg. rewrite <- (positive_nat_Z n).
    apply Qlt_le_weak. apply Q.nat_lt_Qlt.
    apply Nat.div_lt_upper_bound.
    apply Pos2Nat_nonneg.
    rewrite <- (Pos2Nat.inj_mul t n).
    rewrite (Pos.mul_comm t n).
    apply ile. apply Qpos_nonneg. }
   apply ball_mspc_ball.
   eapply luc with (a := fr) (r := proj1_sig wb); [apply UC | | | |]. (* Why is [apply UC] not done automatically? *)
   apply Qpos_ispos.
     apply A1.
    apply A3.
   apply A2.
  Qed.

  (** To construct a CR, we'll need to prove that approx is a regular function.
   However, that property is essentially a specialization of a more general
   well-definedness property that we'll need anyway, so we prove that one first. *)

  Lemma wd
    (from1 from2: Q) (w: bool -> Qpos) (e: bool -> Qpos)
    (fE: from1 == from2) (wE: QposEq (w true) (w false)):
      @ball Q_as_MetricSpace (proj1_sig (e true + e false)%Qpos)
        (approx from1 (w true) (e true))
        (approx from2 (w false) (e false)).
  Proof with auto.
   set (halfe b := (e b * (1 # 2))%Qpos).
   set (m (b : bool) := intervals (if b then from1 else from2) (w b) (halfe b)).
   intros.
   unfold approx.
   simpl.
   do 2 rewrite fastΣ_correct.
   assert ((e true * (1#2))%Qpos = halfe true) by reflexivity.
   simpl in H. rewrite H. clear H.
   assert ((e false * (1#2))%Qpos = halfe false) by reflexivity.
   simpl in H. rewrite H. clear H.
   replace (intervals from1 (w true) (halfe true)) with (m true) by reflexivity.
   replace (intervals from2 (w false) (halfe false)) with (m false) by reflexivity.
   do 2 rewrite Σ_mult.
   apply Qball_hetero_Σ.
   unfold Basics.compose, Qdiv.
   intros.
   rewrite (Qmult_assoc (/m false)).
   rewrite (Qmult_assoc (/m true)).
   setoid_replace (/ m false * (proj1_sig (w true) * / m true))
     with (/ m true * (proj1_sig (w false) * / m false))
     by (unfold QposEq in wE; rewrite wE;
               change (Qeq (/ m false * (proj1_sig (w false) * / m true))
                           (/ m true * (proj1_sig (w false) * / m false)));
               ring).
   replace ((/ m true * (proj1_sig (w false) * / m false))%Q)
     with (proj1_sig (Qpos_inv (m true #1) * (w false * Qpos_inv (m false #1)))%Qpos)
     by reflexivity.
   apply (Qball_Qmult_l (((e true) + (e false)) * (1 # m true * m false))%Qpos).
   assert (QposEq (((e true + e false) * (1 # m true * m false) * Qpos_inv (Qpos_inv (m true #1) * (w false * Qpos_inv (m false #1))))%Qpos)
                  (halfe true * Qpos_inv (w true) + (halfe true * Qpos_inv (w true) + halfe false * Qpos_inv (w false)) + halfe false * Qpos_inv (w false))%Qpos).
   { unfold QposEq, Qpos_inv; simpl.
     setoid_replace (1 # m true * m false) with ((1 # m true) * (1# m false))
       by reflexivity.
     setoid_replace (/ (m true#1)) with (1# m true) by reflexivity.
     setoid_replace (/ (m false#1)) with (1# m false) by reflexivity.
     unfold QposEq in wE. rewrite wE. field.
     split. apply Qpos_nonzero. split; discriminate. }
   unfold QposEq in H0. rewrite H0. clear H0.
    repeat split; try discriminate...
   unfold intervals in m.
   apply (ball_triangle CR (proj1_sig (halfe true * Qpos_inv (w true))%Qpos)
                        (proj1_sig (halfe false * Qpos_inv (w false))%Qpos)
     _ (f (from2 + i * / (m true * m false)%positive * proj1_sig (w false))) _).
    rewrite <- fE.
    unfold QposEq in wE. rewrite <- wE.
    apply (sampling_over_subdivision from1 i (m false) (halfe true) (w true))...
   apply ball_sym.
   rewrite Pmult_comm.
   apply sampling_over_subdivision.
   rewrite Pmult_comm...
   
   unfold intervals in m.
   apply (ball_triangle CR (proj1_sig (halfe true * Qpos_inv (w true))%Qpos)
                        (proj1_sig (halfe false * Qpos_inv (w false))%Qpos)
     _ (f (from2 + i * / (m true * m false)%positive * proj1_sig (w false))) _).
    rewrite <- fE.
    unfold QposEq in wE. rewrite <- wE.
    apply (sampling_over_subdivision from1 i (m false) (halfe true) (w true))...
   apply ball_sym.
   rewrite Pmult_comm.
   apply sampling_over_subdivision.
   rewrite Pmult_comm...
  Qed.

  Lemma regular fr w: is_RegularFunction_noInf Q_as_MetricSpace (approx fr w).
  Proof.
   repeat intro.
   apply (wd fr fr (fun _ => w) (fun b => if b then e1 else e2)); reflexivity.
  Qed.

  Definition pre_result fr w: CR := mkRegularFunction (0:Q_as_MetricSpace) (regular fr w).

  Global Instance (*integrate*): Integral f := @integral_extended_to_nn_width f pre_result.

  Global Instance: Proper (Qeq ==> QposEq ==> @st_eq _) pre_result.
  Proof.
   repeat intro. simpl.
   apply (wd x y (fun b => if b then x0 else y0) (fun b => if b then e1 else e2)); assumption.
  Qed.

End definition.

Arguments intervals lmu from w error : clear implicits.

(** Next, we prove that this implements the abstract interface. *)

Section implements_abstract_interface.

  Add Field Qfield' : Qsft
   (decidable Qeq_bool_eq,
    completeness Qeq_eq_bool,
    constants [Qcst],
    power_tac Qpower_theory [Qpow_tac]).

  Context (f: Q → CR) `{!IsLocallyUniformlyContinuous f lmu}.

  Instance luc_proper_st_eq_2 : Proper (Qeq ==> @st_eq CR) f.
  Proof.
    intros x y exy a b. apply ball_0 in exy.
    pose proof (luc_proper f x y exy a b).
    rewrite Qplus_0_r in H. exact H.
  Qed.

  Section additivity.

    Variables (a: Q) (ww: bool -> Qpos).

    Let totalw := (ww true + ww false)%Qpos.

    Section with_epsilon.

      Variable e: Qpos.

      Let ec b := (e * (ww b * Qpos_inv totalw))%Qpos.
      Let wbints (b : bool) := intervals lmu (if b then a else a+ proj1_sig (ww true))
                                      (ww b) (ec b * (1 # 2)).
      Let w01ints := intervals lmu a totalw (e * (1 # 2)).
      Let approx0 (i: nat) :=
        approximate (f (a + plus_half_times i (proj1_sig (ww true) / ((wbints true) #1))))
                    (ec true * (1 # 2) * Qpos_inv (ww true))%Qpos.
      Let approx1 (i: nat) :=
        approximate (f (a + proj1_sig (ww true) + plus_half_times i (proj1_sig (ww false) / Zpos (wbints false))))
                    (ec false * (1 # 2) * Qpos_inv (ww false))%Qpos.
      Let approx01 (i: nat) :=
        approximate (f (a + plus_half_times i (proj1_sig totalw / Zpos w01ints)))
                    (e * (1 # 2) * Qpos_inv totalw)%Qpos.

      (*Let hint := luc_Proper f.*)

      Lemma added_summations: Qball (proj1_sig e + proj1_sig e)
        (Σ (Pos.to_nat (wbints true)) approx0 * (proj1_sig (ww true) / Zpos (wbints true)) +
         Σ (Pos.to_nat (wbints false)) approx1 * (proj1_sig (ww false) / Zpos (wbints false)))
        (Σ (Pos.to_nat w01ints) approx01 * (proj1_sig totalw / Zpos w01ints)).
      Proof with auto with *.
        destruct (Qpos_gcd3 (ww true * (1# wbints true))
                            (ww false * (1# wbints false)) (totalw * (1# w01ints)))
          as [x [i [E [j [F [k G]]]]]].
       rewrite <- E, <- F, <- G.
       repeat rewrite Qmult_assoc.
       rewrite <- Qmult_plus_distr_l.
       apply (Qball_Qmult_r (e+e)).
       rewrite <- (inject_nat_convert i), <- (inject_nat_convert j), <- (inject_nat_convert k).
       do 3 rewrite Qmult_Σ.
       replace (Pos.to_nat k * Pos.to_nat w01ints)%nat
         with (Pos.to_nat i * Pos.to_nat (wbints true)
               + Pos.to_nat j * Pos.to_nat (wbints false))%nat.
        Focus 2.
        apply surj_eq. (* lift equality to Z *)
        rewrite <- Q.Qeq_Zeq. (* lift equality to Q *)
        apply (Q.Qmult_injective_l (proj1_sig x)). 
        apply Qpos_nonzero.
        rewrite inj_plus, inj_mult, inj_mult, inj_mult.
        repeat rewrite inject_nat_convert.
        rewrite Q.Zplus_Qplus.
        repeat rewrite Q.Zmult_Qmult.
        rewrite Qmult_plus_distr_l.
        rewrite (Qmult_comm i). rewrite (Qmult_comm j). rewrite (Qmult_comm k).
        repeat rewrite <- Qmult_assoc.
        rewrite E, F, G.
        simpl.
        setoid_replace (wbints true #1) with (/ (1#wbints true)) by reflexivity.
        setoid_replace (wbints false #1) with (/ (1#wbints false)) by reflexivity.
        setoid_replace (w01ints #1) with (/ (1#w01ints)) by reflexivity.
        field.
        repeat split; discriminate. 
       do 2 rewrite <- nat_of_P_mult_morphism.
       rewrite Plus.plus_comm.
       rewrite Σ_plus_bound.
       setoid_replace (proj1_sig (e + e)%Qpos / proj1_sig x)
         with (proj1_sig ((ec true + ec true) * Qpos_inv x + (ec false + ec false) * Qpos_inv x)%Qpos).
       Focus 2.
       unfold ec, QposEq. simpl. field.
       split... 
       apply (Qpos_nonzero (ww true + ww false)).
       subst approx0 approx1 approx01.
       unfold flip, Basics.compose.
       assert (~ proj1_sig (ww true) + proj1_sig (ww false) == 0).
       apply (Qpos_nonzero (ww true + ww false)).
       assert (Zpos i == (proj1_sig (ww true) / wbints true / proj1_sig x)) as iE.
       apply (Qmult_injective_l (proj1_sig x)).
       apply Qpos_nonzero.
       rewrite E. simpl.
       setoid_replace (wbints true #1) with (/ (1#wbints true)) by reflexivity.
       field... split. discriminate. apply Qpos_nonzero.
       assert (Zpos j == (proj1_sig (ww false) / wbints false / proj1_sig x)) as jE.
       { apply (Qmult_injective_l (proj1_sig x)). apply Qpos_nonzero.
       rewrite F. simpl.
       setoid_replace (wbints false #1) with (/ (1#wbints false)) by reflexivity.
       field... split. discriminate. apply Qpos_nonzero. }
       assert (Zpos k == (proj1_sig totalw / w01ints / proj1_sig x)) as kE.
       { apply (Qmult_injective_l (proj1_sig x)). apply Qpos_nonzero.
         rewrite G. simpl.
         setoid_replace (w01ints #1) with (/ (1#w01ints)) by reflexivity.
         field... split. discriminate. apply Qpos_nonzero. }
       apply Qball_plus.
        (* left case: *)
        apply Σ_Qball_pos_bounds.
        intros i0 i0E.
        set (ebit (b : bool) := if b then (ec true * (1 # 2) * Qpos_inv (ww true))%Qpos
                             else (e * (1 # 2) * Qpos_inv totalw)%Qpos).
        setoid_replace (proj1_sig ((ec true + ec true) * Qpos_inv x)%Qpos
                        * (1# i * wbints true)%positive)
          with (proj1_sig (ebit true + (ebit true + ebit false) + ebit false)%Qpos).
        Focus 2.
        unfold QposEq. simpl.
         assert (proj1_sig x == (proj1_sig (ww true) / Zpos (wbints true) / Zpos i)) as xE.
          apply Q.Qmult_injective_r with i...
          rewrite <- E. simpl. field...
          rewrite xE. unfold Qpos_mult. simpl. 
          setoid_replace (1 # i * wbints true)
            with ((/i) * / wbints true) by reflexivity.
          field. split. apply (Qpos_nonzero (ww true + ww false)).
          split. apply Qpos_nonzero. split; discriminate.
        (* end Focus 2 *)
        subst ec. simpl in ebit.
        apply (ball_triangle CR (proj1_sig (ebit true))
                             (proj1_sig (ebit false)) (f _) (f (a + i0 * (proj1_sig totalw / (Zpos w01ints * Zpos k)))) (f _))...
        setoid_replace (proj1_sig (ebit true))
          with (proj1_sig (ebit false))
          by (simpl; field; auto).
         unfold ebit.
         setoid_replace (proj1_sig totalw / (w01ints * k))%Q
           with ((/ (Zpos (wbints true) * Zpos i) * proj1_sig (ww true)))
           by (unfold Q_eq; rewrite kE, iE; simpl; field; auto).
         setoid_replace (proj1_sig (e * (1 # 2) * Qpos_inv totalw)%Qpos)
           with (proj1_sig (e * (ww true * Qpos_inv totalw)
                            * (1 # 2) * Qpos_inv (ww true))%Qpos)
          by (simpl; field; auto).
         rewrite <- Pmult_Qmult.
         rewrite Qmult_assoc.
         apply sampling_over_subdivision...
         rewrite Pmult_comm...
        apply ball_sym.
        unfold ebit.
        setoid_replace (i0 * (proj1_sig totalw / (Zpos w01ints * Zpos k)))
          with (i0 * / Zpos (w01ints * k) * proj1_sig totalw).
         apply sampling_over_subdivision...
         rewrite Pmult_comm.
         apply lt_trans with (Pos.to_nat (i * wbints true))...
         apply inj_lt_iff.
         rewrite Zlt_Qlt.
         do 2 rewrite ZL9.
         do 2 rewrite Pmult_Qmult.
         fold w01ints.
         rewrite iE.
         rewrite kE.
         simpl.
         field_simplify...
         apply Qmult_lt_compat_r...
          apply Qinv_lt_0_compat...
         rewrite <- Qplus_0_r at 1.
         apply Qplus_lt_r...
        rewrite Pmult_Qmult.
        unfold Qdiv. unfold Q_eq. ring.
       (* right case: *)
       apply Σ_Qball_pos_bounds.
       intros i0 i0E.
       set (ebit (b : bool) := if b then (ec false * (1 # 2) * Qpos_inv (ww false))%Qpos
                            else (e * (1 # 2) * Qpos_inv totalw)%Qpos).
       assert (QposEq ((ec false + ec false) * Qpos_inv x * (1# j * wbints false)%positive)%Qpos
                      (ebit true + (ebit true + ebit false) + ebit false)%Qpos).
       { unfold QposEq. simpl.
          setoid_replace (1 # j * wbints false)
            with ((/j) * / wbints false) by reflexivity.
          rewrite jE. simpl. field.
          split. apply (Qpos_nonzero (ww true + ww false)).
          split. apply Qpos_nonzero. split. discriminate.
          apply Qpos_nonzero. }
       unfold QposEq in H0. rewrite H0. clear H0.
       apply (ball_triangle CR (proj1_sig (ebit true)) (proj1_sig (ebit false))
                            _ (f (a + proj1_sig (ww true) + i0 * (proj1_sig totalw / (Zpos w01ints * Zpos k)))) _)...
       setoid_replace (proj1_sig (ebit true)) with (proj1_sig (ebit false))
         by (simpl; field; auto).
        unfold ebit.
        setoid_replace (proj1_sig totalw / (Zpos w01ints * Zpos k))
          with ((/ (Zpos (wbints false) * Zpos j) * proj1_sig (ww false)))
          by (rewrite kE, jE; unfold Q_eq; simpl; field; auto).
        assert (QposEq (e * (1 # 2) * Qpos_inv totalw)%Qpos
                       (e * (ww false * Qpos_inv totalw) * (1 # 2) * Qpos_inv (ww false))%Qpos)
          by (unfold QposEq; simpl; field; auto).
        unfold QposEq in H0. rewrite H0. clear H0.
        rewrite <- Pmult_Qmult.
        rewrite Qmult_assoc.
        apply sampling_over_subdivision...
        rewrite Pmult_comm...
       apply ball_sym.
       setoid_replace (a + proj1_sig (ww true) + i0 * (proj1_sig totalw / (Zpos w01ints * Zpos k)))
         with (a + (i * wbints true + i0) * (proj1_sig totalw / (Zpos w01ints * Zpos k)))
        by (rewrite iE, kE; unfold Q_eq; simpl; field; auto).
       rewrite <- Pmult_Qmult.
       setoid_replace ((Zpos (i * wbints true) + i0) * (proj1_sig totalw / (Zpos w01ints * Zpos k))) with
         ((Pos.to_nat (i * wbints true) + i0)%nat * / Zpos (intervals lmu a totalw (e * (1#2)) * k) * proj1_sig totalw).
        apply (sampling_over_subdivision f a (Pos.to_nat (i * wbints true) + i0) k (e*(1#2)) totalw).
        fold w01ints.
        apply lt_le_trans with (Pos.to_nat (i * wbints true) + Pos.to_nat (j * wbints false)%positive)%nat...
        apply inj_le_iff.
        rewrite Zle_Qle.
        rewrite inj_plus.
        rewrite Zplus_Qplus.
        do 3 rewrite ZL9.
        do 3 rewrite Pmult_Qmult.
        rewrite iE, jE, kE.
        simpl.
        field_simplify...
       unfold Qdiv.
       rewrite (Qmult_comm (proj1_sig totalw)).
       rewrite inj_plus, Zplus_Qplus.
       rewrite <- Pmult_Qmult.
       rewrite Qmult_assoc.
       rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
       reflexivity.
      Qed. (* Todo: Still too long. *)

    End with_epsilon.

    Lemma pre_additive:
      (pre_result f a (ww true) + pre_result f (a+proj1_sig (ww true)) (ww false)
       == pre_result f a totalw)%CR.
    Proof with auto with *.
     intros.
     rewrite <- (uneven_CRplus_correct (ww true) (ww false)).
     simpl.
     apply regFunEq_e.
     intro e.
     simpl.
     unfold uneven_CRplus_approx.
     simpl.
     unfold approx.
     do 3 rewrite fastΣ_correct.
     apply added_summations.
    Qed.

  End additivity.

  Lemma data_points_in_range (from: Q) (width: Qpos) (ints: positive) (i : nat) (Ilt: (i < Pos.to_nat ints)%nat):
    from <= (from + (i * (`width / Zpos ints) + (1 # 2) * (`width / Zpos ints))) <= from + `width.
  Proof with auto with qarith.
   split.
    rewrite <- (Qplus_0_r from) at 1.
    apply Qplus_le_compat...
    change (0 <= i * ` (width * (1#ints))%Qpos + (1#2) * ` (width * (1#ints))%Qpos)...
   apply Qplus_le_compat...
   unfold Qdiv.
   setoid_replace (i * (`width * / Zpos ints) + (1 # 2) * (`width * / Zpos ints))
     with (((i+(1#2)) * / Zpos ints) * `width) by (unfold Q_eq; ring).
   rewrite <- (Qmult_1_l (`width)) at 2.
   apply Qmult_le_compat_r...
   apply Qdiv_le_1.
   split...
   apply Qlt_le_weak.
   rewrite (Zpos_eq_Z_of_nat_o_nat_of_P ints).
   apply nat_lt_Qlt...
  Qed.

  Let bounded (from: Q) (width: Qpos) (mid: Q) (r: Qpos):
    (forall x, from <= x <= from + proj1_sig width -> ball (proj1_sig r) (f x) ('mid)%CR) ->
    ball (proj1_sig (width * r)%Qpos)
         (pre_result f from width) (' (proj1_sig width * mid)%Q)%CR.
  Proof with auto with qarith.
   intros. apply (@regFunBall_Cunit Q_as_MetricSpace).
   intro. unfold pre_result. simpl approximate.
   unfold approx.
   rewrite fastΣ_correct.
   set (ints := intervals lmu from width (d * (1 # 2))).
   apply (@ball_weak_le Q_as_MetricSpace
                       (proj1_sig (d*(1#2) + width * r)%Qpos)
                       (` d + ` (width * r)%Qpos)).
    simpl. apply Qplus_le_compat...
   rewrite Σ_mult.
   setoid_replace (`width * mid) with (Pos.to_nat ints * (`width / ints * mid)).
    Focus 2. simpl. rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P. unfold Q_eq. field...
   rewrite <- Σ_const.
   apply Σ_Qball_pos_bounds.
   intros.
   unfold Basics.compose.
   apply (@Qball_Qmult_l ((d*(1#2)+width*r)*(1#ints)) (width * (1# ints))%Qpos).
   assert (QposEq ((d*(1#2) + width * r) * (1# ints) * Qpos_inv (width * (1# ints)))%Qpos
                  (d*(1#2) * Qpos_inv width + r)%Qpos).
   { unfold QposEq. simpl. field.
     split. apply Qpos_nonzero. discriminate. }
   unfold QposEq in H1. rewrite H1. clear H1.
   apply regFunBall_Cunit, H, data_points_in_range...
  Qed.

  Global Instance correct: Integrable f.
  Proof.
   apply integral_extended_to_nn_width_correct.
     intros. apply (@pre_additive a (fun t => if t then b else c)).
    assumption.
   apply _.
  Qed.

End implements_abstract_interface.
