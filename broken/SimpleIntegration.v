(*

(** A straightforward implementation of the abstract integration interface
 in AbstractionIntegration using Riemann sums. The sole product of
 this module are the Integrate and Integrable type class instances.
 Do not prove any additional properties about this implementation; all we
 care about is that it implements the abstract integration interface!
 This implementation works for any uniformly continuous function, which
 makes it relatively generic, but it also means that it is fairly inefficient. *)

Require Import
  List NPeano Unicode.Utf8
  QArith Qabs Qpossec Qsums
  Qmetric
  CRArith AbstractIntegration
  util.Qgcd
  Program
  uneven_CRplus
  stdlib_omissions.P
  stdlib_omissions.Z
  stdlib_omissions.Q
  metric2.Classified
  implementations.stdlib_rationals.

Open Scope uc_scope.

Hint Resolve Qpos_nonzero.
Hint Immediate Q.Qle_nat.
Hint Resolve Qmult_le_0_compat.
Hint Resolve QnonNeg.Qplus_nonneg.

Lemma half_Qpos (q: Qpos): q * (1#2) <= q.
Proof with auto.
 intros.
 rewrite <- (Qmult_1_r q) at 2.
 apply Q.Qmult_le_compat_l...
 discriminate.
Qed.

Hint Immediate half_Qpos.

Lemma Qball_ex_plus_r e (x y y' : Q):
  @ball_ex Q_as_MetricSpace e y y' -> @ball_ex Q_as_MetricSpace e (x + y) (x + y').
Proof. destruct e. apply Qball_plus_r. intuition. Qed.

Definition plus_half_times (x y: Q): Q := x * y + (1#2)*y.

Section definition.

  Context (f: Q -> CR) `{!LocallyUniformlyContinuous_mu f} `{!LocallyUniformlyContinuous f}.

  (** Note that in what follows we don't specialize for [0,1] or [0,w] ranges first. While this
  would make the definition marginally cleaner, the resulting definition is harder to prove
  correct. Part of the reason for this is that key primitives (such as mu and approximate)
  don't come with Proper proofs, which means that common sense reasoning about
  those operations with their arguments transformed doesn't work well. *)

  Definition intervals (from: Q) (w: Qpos) (error: Qpos): positive :=
    match luc_mu f from w (error / w) with
      (* Todo: This is nice and simple, but suboptimal. Better would be to take the luc_mu
       around the midpoint and with radius (w/2). *)
    | QposInfinity => 1%positive
    | Qpos2QposInf mue => QposCeiling ((1#2) * w / mue)%Qpos
    end.

  Definition approx (from: Q) (w: Qpos) (e: Qpos): Q :=
    let halferror := (e * (1#2))%Qpos in
    let ints := intervals from w halferror in
    let iw := (w / ints) in
    let halfiw := ((1#2) * iw) in
      fastΣ (nat_of_P ints) (fun i => approximate (f (from + (i * iw + halfiw))) (halferror / w)%Qpos) * iw.

  (** In several places in the correctness proof, we will be comparing different
   Riemann sums over the same range divided into different numbers of intervals.
   For these cases, the following lemma is very useful. *)

  Hint Resolve  Qinv_le_0_compat Qmult_le_0_compat.
  Hint Immediate Zle_0_POS Zlt_0_POS.

  Lemma sampling_over_subdivision (fr: Q) (i: nat) (t: positive) (he wb: Qpos) (ile: le i (intervals fr wb he * t)%positive): ball (he / wb)
    (f (fr + plus_half_times (i / t)%nat (wb * / intervals fr wb he)))
    (f (fr + i * / (intervals fr wb he * t)%positive * wb)).
  Proof with auto.
   unfold plus_half_times.
   apply ball_sym.
   apply (locallyUniformlyContinuous f fr wb (he / wb)).
    unfold mspc_ball.
    unfold CRGroupOps.MetricSpaceBall_instance_0.
    rewrite <- (Qplus_0_r fr) at 1.
    apply Qball_plus_r.
    apply in_Qball.
    split.
     apply Qle_trans with 0...
     unfold Qminus.
     rewrite Qplus_0_l.
     change (-wb <= -0).
     apply Qopp_le_compat...
    rewrite Qplus_0_l.
    rewrite <- (Qmult_1_l wb) at 2.
    apply Qmult_le_compat_r...
    apply Qmult_le_r with (intervals fr wb he * t)%positive...
    rewrite <- Qmult_assoc.
    rewrite Qmult_inv_r.
     rewrite Qmult_1_r.
     rewrite Qmult_1_l.
     rewrite <- Zle_Qle.
     rewrite <- ZL9.
     apply inj_le...
    intro.
    assert (0 < / (intervals fr wb he * t)%positive).
     apply Qinv_lt_0_compat...
    revert H0.
    rewrite H.
    apply (Qlt_irrefl 0).
   pose proof mspc_ball_ex_Symmetric.
   symmetry.
   apply Qball_ex_plus_r.
   unfold intervals.
   set (luc_mu f fr wb (he / wb)).
   destruct q; simpl...
   set (mym := QposCeiling ((1 # 2) * wb / q)).
   apply ball_weak_le with (wb * (1#2) * Qpos_inv mym)%Qpos.
    simpl.
    rewrite (Qmult_comm (wb)).
    simpl.
    subst mym.
    rewrite QposCeiling_Qceiling.
    apply Qle_shift_div_r...
     apply Qlt_le_trans with ((1#2) * wb / q)%Qpos...
     auto with *.
    setoid_replace ((1#2) * wb) with (q * ((1#2) * wb / q)).
     apply Qmult_le_compat_l...
     auto with *.
    change (Qeq ((1 # 2) * wb) (q * ((1 # 2) * wb / q))).
    field...
   simpl.
   rewrite Q.Pmult_Qmult.
   apply Qball_Qdiv_inv with (Qpos_inv mym * wb)%Qpos.
   simpl.
   field_simplify...
   unfold Qdiv.
   rewrite Qmult_plus_distr_l.
   field_simplify...
   rewrite Qdiv_1_r.
   setoid_replace (wb * (1 # 2) / mym / (Qpos_inv mym * wb))%Qpos with (1#2)%Qpos.
    rewrite Z.div_Zdiv...
    rewrite Q.Zdiv_Qdiv.
    rewrite inject_nat_convert.
    apply Qfloor_ball.
   unfold QposEq. simpl.
   field. split; try discriminate...
  Qed.

  (** To construct a CR, we'll need to prove that approx is a regular function.
   However, that property is essentially a specialization of a more general
   well-definedness property that we'll need anyway, so we prove that one first. *)

  Let hint := luc_Proper f.

  Lemma wd
    (from1 from2: Q) (w: bool -> Qpos) (e: bool -> Qpos)
    (fE: from1 == from2) (wE: w true == w false):
      @ball Q_as_MetricSpace (e true + e false)
        (approx from1 (w true) (e true))
        (approx from2 (w false) (e false)).
  Proof with auto.
   set (halfe b := (e b * (1 # 2))%Qpos).
   set (m (b : bool) := intervals (if b then from1 else from2) (w b) (halfe b)).
   intros.
   unfold approx.
   simpl.
   do 2 rewrite fastΣ_correct.
   replace (e true * (1#2))%Qpos with (halfe true) by reflexivity.
   replace (e false * (1#2))%Qpos with (halfe false) by reflexivity.
   replace (intervals from1 (w true) (halfe true)) with (m true) by reflexivity.
   replace (intervals from2 (w false) (halfe false)) with (m false) by reflexivity.
   do 2 rewrite Σ_mult.
   apply Qball_hetero_Σ.
   unfold Basics.compose, Qdiv.
   intros.
   rewrite (Qmult_assoc (/m false)).
   rewrite (Qmult_assoc (/m true)).
   setoid_replace (/ m false * (w true * / m true)) with (/ m true * (w false * / m false)).
    Focus 2.
    rewrite wE.
    change (Qeq (/ m false * (w false * / m true)) (/ m true * (w false * / m false))).
    ring.
   replace ((/ m true * (w false * / m false))%Q) with ((Qpos_inv (m true) * (w false * Qpos_inv (m false)))%Qpos: Q) by reflexivity.
   apply Qball_Qmult_l.
   setoid_replace (((e true + e false) / (m true * m false)%positive / (Qpos_inv (m true) * (w false / m false)))%Qpos)
     with (halfe true / w true + (halfe true / w true + halfe false / w false) + halfe false / w false)%Qpos.
    Focus 2.
    unfold QposEq, Qpos_inv.
    simpl. rewrite Q.Pmult_Qmult. rewrite wE. field.
    repeat split; try discriminate...
   unfold intervals in m.
   apply (ball_triangle CR (halfe true/w true) (halfe false/w false)
     _ (f (from2 + i * / (m true * m false)%positive * w false)) _).
    rewrite <- fE.
    rewrite <- wE.
    apply (sampling_over_subdivision from1 i (m false) (halfe true) (w true)).
    apply lt_le_weak...
   apply ball_sym.
   rewrite Pmult_comm.
   apply sampling_over_subdivision.
   rewrite Pmult_comm.
   apply lt_le_weak...
  Qed.

  Lemma regular fr w: is_RegularFunction_noInf Q_as_MetricSpace (approx fr w).
  Proof.
   repeat intro.
   apply (wd fr fr (fun _ => w) (fun b => if b then e1 else e2)); reflexivity.
  Qed.

  Definition pre_result fr w: CR := mkRegularFunction (0:Q_as_MetricSpace) (regular fr w).

  Global Instance integrate: Integral f := @integral_extended_to_nn_width f pre_result.

  Global Instance: Proper (Qeq ==> QposEq ==> @st_eq _) pre_result.
  Proof.
   repeat intro. simpl.
   apply (wd x y (fun b => if b then x0 else y0) (fun b => if b then e1 else e2)); assumption.
  Qed.

End definition.

(** Next, we prove that this implements the abstract interface. *)

Section implements_abstract_interface.

  Context (f: Q → CR) `{!LocallyUniformlyContinuous_mu f} `{!LocallyUniformlyContinuous f}.

  Section additivity.

    Variables (a: Q) (ww: bool -> Qpos).

    Let totalw := (ww true + ww false)%Qpos.

    Section with_epsilon.

      Variable e: Qpos.

      Let ec b := (e * (ww b / totalw))%Qpos.
      Let wbints (b : bool) := intervals f (if b then a else a+ww true) (ww b) (ec b * (1 # 2)).
      Let w01ints := intervals f a totalw (e * (1 # 2)).
      Let approx0 (i: nat) :=
        approximate (f (a + plus_half_times i (ww true / wbints true))) (ec true * (1 # 2) / ww true)%Qpos.
      Let approx1 (i: nat) :=
        approximate (f (a + ww true + plus_half_times i (ww false / wbints false))) (ec false * (1 # 2) / ww false)%Qpos.
      Let approx01 (i: nat) :=
        approximate (f (a + plus_half_times i (totalw / w01ints))) (e * (1 # 2) / totalw)%Qpos.

      Let hint := luc_Proper f.

      Lemma added_summations: Qball (e + e)
        (Σ (wbints true) approx0 * (ww true / wbints true) +
         Σ (wbints false) approx1 * (ww false / wbints false))
        (Σ w01ints approx01 * (totalw / w01ints)).
      Proof with auto with *.
       destruct (Qpos_gcd3 (ww true / wbints true) (ww false / wbints false) (totalw / w01ints)) as [x [i [E [j [F [k G]]]]]].
       rewrite <- E, <- F, <- G.
       repeat rewrite Qmult_assoc.
       rewrite <- Qmult_plus_distr_l.
       apply Qball_Qmult_r.
       rewrite <- (inject_nat_convert i), <- (inject_nat_convert j), <- (inject_nat_convert k).
       do 3 rewrite Qmult_Σ.
       replace (k * w01ints)%nat with (i * wbints true + j * wbints false)%nat.
        Focus 2.
        apply surj_eq.
        rewrite <- Q.Qeq_Zeq.
        apply Q.Qmult_injective_l with x...
        rewrite inj_plus, inj_mult, inj_mult, inj_mult.
        repeat rewrite inject_nat_convert.
        rewrite Q.Zplus_Qplus.
        repeat rewrite Q.Zmult_Qmult.
        rewrite Qmult_plus_distr_l.
        rewrite (Qmult_comm i). rewrite (Qmult_comm j). rewrite (Qmult_comm k).
        repeat rewrite <- Qmult_assoc.
        rewrite E, F, G.
        simpl. field.
        repeat split; discriminate.
       do 2 rewrite <- nat_of_P_mult_morphism.
       rewrite plus_comm.
       rewrite Σ_plus_bound.
       setoid_replace ((e + e) / x)%Qpos with ((ec true + ec true) / x + (ec false + ec false) / x)%Qpos.
        Focus 2.
        unfold ec, QposEq. simpl. field.
        split... change (~ (ww true + ww false)%Qpos == 0)...
       subst approx0 approx1 approx01.
       unfold flip, Basics.compose.
       assert (~ ww true + ww false == 0). change (~ (ww true + ww false)%Qpos == 0)...
       assert (i == (ww true / wbints true / x)%Qpos) as iE.
        apply Qmult_injective_l with x... rewrite E. simpl. field...
       assert (j == (ww false / wbints false / x)%Qpos) as jE.
        apply Qmult_injective_l with x... rewrite F. simpl. field...
       assert (k == (totalw / w01ints / x)%Qpos) as kE.
        apply Qmult_injective_l with x... rewrite G. simpl. field...
       apply Qball_plus.
        (* left case: *)
        apply Σ_Qball_pos_bounds.
        intros i0 i0E.
        set (ebit (b : bool) := if b then (ec true * (1 # 2) / ww true)%Qpos else (e * (1 # 2) / totalw)%Qpos).
        setoid_replace ((ec true + ec true) / x / (i * wbints true)%positive)%Qpos
        with (ebit true + (ebit true + ebit false) + ebit false)%Qpos.
         Focus 2.
         unfold QposEq. simpl.
         assert (x == (ww true / wbints true / i)) as xE.
          apply Q.Qmult_injective_r with i...
          rewrite <- E. field...
         rewrite xE.
         rewrite Q.Pmult_Qmult.
         field...
        subst ec. simpl in ebit.
        apply (ball_triangle CR (ebit true) (ebit false) (f _) (f (a + i0 * (totalw / (w01ints * k)))) (f _))...
         setoid_replace (ebit true) with (ebit false) by (unfold QposEq; simpl; field; auto).
         unfold ebit.
         setoid_replace (totalw / (w01ints * k)) with ((/ (wbints true * i) * ww true))
         by (unfold Q_eq; rewrite kE, iE; simpl; field; auto).
         setoid_replace (e * (1 # 2) / totalw)%Qpos with (e * (ww true / totalw) * (1 # 2) / ww true)%Qpos
          by (unfold QposEq; simpl; field; auto).
         rewrite <- Pmult_Qmult.
         rewrite Qmult_assoc.
         apply sampling_over_subdivision...
         rewrite Pmult_comm...
        apply ball_sym.
        unfold ebit.
        setoid_replace (i0 * (totalw / (w01ints * k))) with (i0 * / (w01ints * k)%positive * totalw).
         apply sampling_over_subdivision...
         rewrite Pmult_comm.
         apply lt_le_weak...
         apply lt_trans with (i * wbints true)%positive...
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
       set (ebit (b : bool) := if b then (ec false * (1 # 2) / ww false)%Qpos else (e * (1 # 2) / totalw)%Qpos).
       setoid_replace ((ec false + ec false) / x / (j * wbints false)%positive)%Qpos
       with (ebit true + (ebit true + ebit false) + ebit false)%Qpos.
        Focus 2.
        unfold QposEq. simpl. rewrite Pmult_Qmult, jE. simpl. field...
       apply (ball_triangle CR (ebit true) (ebit false) _ (f (a + ww true + i0 * (totalw / (w01ints * k)))) _)...
        setoid_replace (ebit true) with (ebit false) by (unfold QposEq; simpl; field; auto).
        unfold ebit.
        setoid_replace (totalw / (w01ints * k)) with ((/ (wbints false * j) * ww false)) by (rewrite kE, jE; unfold Q_eq; simpl; field; auto).
        setoid_replace (e * (1 # 2) / totalw)%Qpos with (e * (ww false / totalw) * (1 # 2) / ww false)%Qpos by (unfold QposEq; simpl; field; auto).
        rewrite <- Pmult_Qmult.
        rewrite Qmult_assoc.
        apply sampling_over_subdivision...
        rewrite Pmult_comm...
       apply ball_sym.
       setoid_replace (a + ww true + i0 * (totalw / (w01ints * k))) with (a + (i * wbints true + i0) * (totalw / (w01ints * k)))
        by (rewrite iE, kE; unfold Q_eq; simpl; field; auto).
       rewrite <- Pmult_Qmult.
       setoid_replace (((i * wbints true)%positive + i0) * (totalw / (w01ints * k))) with
         (((i * wbints true)%positive + i0)%nat * / (intervals f a totalw (e * (1#2)) * k)%positive * totalw).
        apply (sampling_over_subdivision f a ((i * wbints true)%positive + i0) k (e*(1#2)) totalw).
        fold w01ints.
        apply le_trans with ((i * wbints true)%positive + (j * wbints false)%positive)%nat...
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
       rewrite (Qmult_comm totalw).
       rewrite inj_plus, Zplus_Qplus. 
       rewrite <- Pmult_Qmult.
       rewrite Qmult_assoc.
       rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P.
       reflexivity.
      Qed. (* Todo: Still too long. *)

    End with_epsilon.

    Lemma pre_additive:
      (pre_result f a (ww true) + pre_result f (a+ww true) (ww false) == pre_result f a totalw)%CR.
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

  Lemma data_points_in_range (from: Q) (width: Qpos) (ints: positive) (i : nat) (Ilt: (i < ints)%nat):
    from <= (from + (i * (`width / ints) + (1 # 2) * (`width / ints))) <= from + `width.
  Proof with auto.
   split.
    rewrite <- (Qplus_0_r from) at 1.
    apply Qplus_le_compat...
    change (0 <= i * ` (width / ints)%Qpos + (1#2) * ` (width / ints)%Qpos)...
   apply Qplus_le_compat...
   unfold Qdiv.
   setoid_replace (i * (`width * / ints) + (1 # 2) * (`width * / ints))
     with (((i+(1#2)) * / ints) * `width) by (unfold Q_eq; ring).
   rewrite <- (Qmult_1_l (`width)) at 2.
   apply Qmult_le_compat_r...
   apply Qdiv_le_1.
   split...
   apply Qlt_le_weak.
   rewrite (Zpos_eq_Z_of_nat_o_nat_of_P ints).
   apply nat_lt_Qlt...
  Qed.

  Let bounded (from: Q) (width: Qpos) (mid: Q) (r: Qpos):
    (forall x, from <= x <= from + width -> ball r (f x) ('mid)%CR) ->
    ball (width * r) (pre_result f from width) (' (width * mid))%CR.
  Proof with auto.
   intros. apply (@regFunBall_Cunit Q_as_MetricSpace).
   intro. unfold pre_result. simpl approximate.
   unfold approx.
   rewrite fastΣ_correct.
   set (ints := intervals f from width (d * (1 # 2))).
   apply (ball_weak_le Q_as_MetricSpace (d*(1#2) + width * r) (d + width * r)).
    simpl. apply Qplus_le_compat...
   simpl.
   rewrite Σ_mult.
   setoid_replace (`width * mid) with ((ints:nat) * (`width / ints * mid)).
    Focus 2. simpl. rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P. unfold Q_eq. field...
   rewrite <- Σ_const.
   apply Σ_Qball_pos_bounds.
   intros.
   unfold Basics.compose.
   apply (@Qball_Qmult_l ((d*(1#2)+width*r)/ints) (width / ints)%Qpos).
   setoid_replace ((d*(1#2) + width * r) / ints / (width / ints))%Qpos
    with (d*(1#2) / width + r)%Qpos by (unfold QposEq; simpl; field)...
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
*)
