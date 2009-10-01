(** This module provides C-CoRN models for modules implementing the QType
 signature.

One example of such a module is BigQ, which uses fast machine integers, so with
the current module one can say:

  [Require Import BigQ.]
  [Module BigCQ := QType_instances BigQ.]
  [Check BigCQ.CR.]

to obtain an equivalent of CR that uses BigQ instead of of Q.

*)


Require Import
 CSetoidFun
 CSemiGroups
 CMonoids
 CGroups
 CAbGroups
 CRings
 CFields
 COrdFields
 COrdAbs.

Require Export
 Metric
 Complete
 SetoidDec
 SetoidClass.

Require Import
 Qabs
 Qordfield
 Qmetric
 Qsec
 QSig.

Require decsetoid.

Module QType_instances (anyQ: QType).

Coercion anyQ.to_Q: anyQ.t >-> Q.
Coercion anyQ.of_Q: Q >-> anyQ.t.

Lemma spec_to_Q q: anyQ.eq (anyQ.of_Q (anyQ.to_Q q)) q.
Proof.
 intros.
 unfold anyQ.eq.
 rewrite anyQ.spec_of_Q.
 reflexivity.
Qed.

(* anyQ.eq is an equivalence and thus makes anyQ a setoid: *)

Instance Equivalence: Equivalence anyQ.eq.
Proof with auto.
 unfold anyQ.eq.
 constructor; repeat intro.
   reflexivity.
  symmetry...
 transitivity y...
Qed.

Instance std_Setoid: Setoid anyQ.t := { equiv := anyQ.eq; setoid_equiv := Equivalence }.

(* furthermore, the equality is decidable *)

Instance eq_dec: EqDec std_Setoid.
Proof.
 intros x y.
 pose proof (anyQ.spec_eq_bool x y).
 destruct anyQ.eq_bool in H; intuition.
Qed.

(* also, all the operations are morphisms w.r.t. this equality: *)

Add Morphism anyQ.add with signature (anyQ.eq ==> anyQ.eq ==> anyQ.eq) as add_mor.
Proof.
 unfold anyQ.eq.
 intros x y H x0 y0 H0.
 do 2 rewrite anyQ.spec_add.
 rewrite H H0.
 reflexivity.
Qed.

Add Morphism anyQ.sub with signature (anyQ.eq ==> anyQ.eq ==> anyQ.eq) as sub_mor.
Proof.
 unfold anyQ.eq.
 intros x y H x0 y0 H0.
 do 2 rewrite anyQ.spec_sub.
 rewrite H H0.
 reflexivity.
Qed.

Add Morphism anyQ.mul with signature (anyQ.eq ==> anyQ.eq ==> anyQ.eq) as mul_mor.
Proof.
 unfold anyQ.eq.
 intros x y H x0 y0 H0.
 do 2 rewrite anyQ.spec_mul.
 rewrite H H0.
 reflexivity.
Qed.

Add Morphism anyQ.opp with signature (anyQ.eq ==> anyQ.eq) as opp_mor.
Proof.
 unfold anyQ.eq.
 intros x y H.
 do 2 rewrite anyQ.spec_opp.
 rewrite H. reflexivity.
Qed.

Add Morphism anyQ.inv with signature (anyQ.eq ==> anyQ.eq) as inv_mor.
Proof.
 unfold anyQ.eq.
 intros x y H.
 do 2 rewrite anyQ.spec_inv.
 rewrite H. reflexivity.
Qed.

Add Morphism anyQ.lt with signature (anyQ.eq ==> anyQ.eq ==> iff) as lt_mor.
Proof.
 unfold anyQ.lt, anyQ.eq.
 intros x y H x0 y0 H0.
 do 2 rewrite anyQ.spec_compare.
 rewrite H H0. tauto.
Qed.

Add Morphism anyQ.le with signature (anyQ.eq ==> anyQ.eq ==> iff) as le_mor.
Proof.
 unfold anyQ.le, anyQ.eq.
 intros x y H x0 y0 H0.
 do 2 rewrite anyQ.spec_compare.
 rewrite H H0. tauto.
Qed.

(* anyQ is a ring *)

Lemma anyQ_ring_theory: ring_theory anyQ.zero anyQ.one anyQ.add anyQ.mul anyQ.sub anyQ.opp anyQ.eq.
 constructor; unfold anyQ.eq; intros;
  repeat rewrite anyQ.spec_add;
  repeat rewrite anyQ.spec_mul;
  repeat rewrite anyQ.spec_0;
  repeat rewrite anyQ.spec_mul;
  repeat rewrite anyQ.spec_sub;
  repeat rewrite anyQ.spec_opp;
  repeat rewrite anyQ.spec_1; try ring.
 rewrite anyQ.spec_add.
 ring.
Qed.

Add Ring anyQ: anyQ_ring_theory.

(* relating anyQ relations to Q relations: *)

Lemma anyQlt_from_Qlt (x y: anyQ.t): x < y -> anyQ.lt x y.
Proof.
 intros.
 unfold anyQ.lt.
 rewrite anyQ.spec_compare.
 by apply -> Qlt_alt.
Qed.

Lemma Qlt_to_anyQlt (x y: Q): x < y -> anyQ.lt x y.
Proof.
 intros.
 unfold anyQ.lt.
 rewrite anyQ.spec_compare.
 by do 2 rewrite anyQ.spec_of_Q.
Qed.

Lemma anyQlt_to_Qlt (x y: anyQ.t): anyQ.lt x y -> x < y.
Proof with auto.
 intros x y.
 unfold anyQ.lt.
 rewrite anyQ.spec_compare.
 intros.
 apply <- Qlt_alt...
Qed.

Lemma Qlt_from_anyQlt (x y: Q): anyQ.lt x y -> x < y.
Proof with auto.
 intros x y.
 unfold anyQ.lt.
 rewrite anyQ.spec_compare.
 do 2 rewrite anyQ.spec_of_Q...
Qed.

Lemma anyQle_from_Qle (x y: anyQ.t): x <= y -> anyQ.le x y.
Proof with auto.
 intros.
 unfold anyQ.le.
 rewrite anyQ.spec_compare.
 apply -> Qle_alt...
Qed.

Lemma Qle_to_anyQle (x y: Q): x <= y -> anyQ.le x y.
Proof with auto.
 intros.
 unfold anyQ.le.
 rewrite anyQ.spec_compare.
 do 2 rewrite anyQ.spec_of_Q...
Qed.

Lemma Qle_from_anyQle (x y: Q): anyQ.le x y -> x <= y.
Proof with auto.
 intros x y.
 unfold anyQ.le.
 rewrite anyQ.spec_compare.
 do 2 rewrite anyQ.spec_of_Q...
Qed.

Lemma anyQle_to_Qle (x y: anyQ.t): anyQ.le x y -> x <= y.
Proof with auto.
 intros x y.
 unfold anyQ.le.
 rewrite anyQ.spec_compare.
 intros.
 apply <- Qle_alt...
Qed.

Hint Resolve anyQlt_to_Qlt.
Hint Resolve anyQle_to_Qle.
Hint Resolve anyQlt_from_Qlt.
Hint Resolve anyQle_from_Qle.

(* We now build models for the CoRN hierarchy, starting with CSetoid, which we
 get for free (using module decsetoid) because our setoid equality is decidable. *)

Let ap := decsetoid.ap.

Definition CSetoid: CSetoid := @Build_CSetoid anyQ.t (@equiv anyQ.t std_Setoid) ap decsetoid.is_CSetoid.

Canonical Structure CSetoid.
Canonical Structure is_Setoid := cs_crr CSetoid.

(* Some more CSetoid-specific morphism-like things: *)

Lemma add_wd: bin_fun_wd CSetoid CSetoid CSetoid anyQ.add.
Proof.
 repeat intro.
 apply add_mor; assumption.
Qed.

Lemma add_strext: bin_fun_strext _ _ _ anyQ.add.
Proof. apply decsetoid.bin_fun_strext. auto with *. Qed.

Lemma mul_strext: bin_fun_strext _ _ _ anyQ.mul.
Proof. apply decsetoid.bin_fun_strext. auto with *. Qed.

Lemma opp_strext: fun_strext anyQ.opp.
Proof. apply decsetoid.fun_strext. auto with *. Qed.

Lemma inv_strext: fun_strext anyQ.inv.
Proof. apply decsetoid.fun_strext. auto with *. Qed.

Lemma lt_strext: Crel_strext CSetoid anyQ.lt.
Proof. apply decsetoid.Crel_strext. auto with *. Qed.

(* Some more nice properties: *)

Definition add_is_bin_fun := Build_CSetoid_bin_fun _ _ _ _ add_strext.
Definition mul_is_bin_fun := Build_CSetoid_bin_fun _ _ _ _ mul_strext.
Definition anyQ_opp_fun := Build_CSetoid_fun _ _ _ opp_strext.

Canonical Structure add_is_bin_fun.

Lemma add_assoc: associative anyQ.add.
Proof. repeat intro. simpl. ring. Qed.

Lemma mul_assoc: associative mul_is_bin_fun.
Proof. repeat intro. simpl. ring. Qed.

Lemma ZEROQ_as_rht_unit3 : is_rht_unit (S:=CSetoid) add_is_bin_fun anyQ.zero.
Proof. red. simpl. intros. ring. Qed.

Lemma ZEROQ_as_lft_unit3 : is_lft_unit (S:=CSetoid) add_is_bin_fun anyQ.zero.
Proof. red. simpl. intros. ring. Qed.

Lemma ONEQ_as_rht_unit : is_rht_unit (S:=CSetoid) mul_is_bin_fun anyQ.one.
Proof. red. simpl. intros. ring. Qed.

Lemma ONEQ_as_lft_unit : is_lft_unit (S:=CSetoid) mul_is_bin_fun anyQ.one.
Proof. red. simpl. intros. ring. Qed.

Lemma mul_plus_distributive: distributive mul_is_bin_fun add_is_bin_fun.
Proof. red. simpl. intros. ring. Qed.

Instance lt_asymmetric: Asymmetric anyQ.lt.
Proof with auto.
 repeat intro.
 apply (Qlt_is_antisymmetric_unfolded x y)...
Qed.

Instance lt_transitive: Transitive anyQ.lt.
Proof with auto.
 repeat intro.
 apply anyQlt_from_Qlt.
 apply Qlt_trans with y...
Qed.

Definition lt_is_strict_order: strictorder anyQ.lt :=
  Build_strictorder lt_transitive lt_asymmetric.

(* We now have the following two CSemiGroups: *)

Definition additive_CSemiGroup: CSemiGroup
  := Build_CSemiGroup _ add_is_bin_fun add_assoc.
Definition multiplicative_CSemiGroup: CSemiGroup
  := Build_CSemiGroup _ mul_is_bin_fun mul_assoc.

Canonical Structure additive_CSemiGroup.

(* And two CMonoids, too. *)

Definition is_additive_CMonoid: is_CMonoid additive_CSemiGroup anyQ.zero
  := Build_is_CMonoid additive_CSemiGroup _ ZEROQ_as_rht_unit3 ZEROQ_as_lft_unit3.
Definition is_multiplicative_CMonoid: is_CMonoid multiplicative_CSemiGroup anyQ.one
  := Build_is_CMonoid multiplicative_CSemiGroup _ ONEQ_as_rht_unit ONEQ_as_lft_unit.

Definition additive_CMonoid: CMonoid := Build_CMonoid _ _ is_additive_CMonoid.
Definition multiplicative_CMonoid: CMonoid := Build_CMonoid _ _ is_multiplicative_CMonoid.

Canonical Structure additive_CMonoid.

(* And a CGroup: *)

Lemma is_CGroup: is_CGroup additive_CMonoid anyQ_opp_fun.
Proof. split; simpl; ring. Qed.

Definition CGroup: CGroup := Build_CGroup _ anyQ_opp_fun is_CGroup.

Canonical Structure CGroup.

(* And a CAbGroup: *)

Lemma is_CAbGroup: is_CAbGroup CGroup.
Proof. repeat intro. simpl. ring. Qed.

Definition CAbGroup: CAbGroup := Build_CAbGroup _ is_CAbGroup.

Canonical Structure CAbGroup.

(* And a CRing: *)

Definition is_CRing: is_CRing CAbGroup anyQ.one mul_is_bin_fun.
Proof with auto.
 apply Build_is_CRing with mul_assoc.
    apply is_multiplicative_CMonoid.
   repeat intro. simpl. ring.
  repeat intro. simpl. ring.
 simpl. intro.
 apply Q_apart_0_1.
 rewrite <- anyQ.spec_1.
 rewrite <- anyQ.spec_0...
Qed.

Definition CRing: CRing := Build_CRing _ _ _ is_CRing.

Canonical Structure CRing.

(* And a CField: *)

Lemma is_CField: is_CField CRing (fun x _ => anyQ.inv x).
Proof with auto.
 red.
 unfold is_inverse. simpl.
 unfold ap, decsetoid.ap. simpl.
 unfold anyQ.eq.
 intro x.
 do 2 rewrite anyQ.spec_mul.
 rewrite anyQ.spec_inv.
 rewrite anyQ.spec_1.
 rewrite anyQ.spec_0.
 split; field...
Qed.

Definition CField: CField := Build_CField _ _ is_CField (fun a b c d e => inv_strext a b e).

Canonical Structure CField.

(* And a COrdField: *)

Definition lt_CCSetoid_relation: CCSetoid_relation CField :=
 Build_CCSetoid_relation CSetoid anyQ.lt lt_strext.

Definition Q_is_COrdField := Build_is_COrdField Q_as_CField
 Qlt_is_CSetoid_relation Qle (default_greater Q_as_CField Qlt_is_CSetoid_relation)
 (default_grEq Q_as_CField Qle) Qlt_is_strict_order Qplus_resp_Qlt
 Qmult_resp_pos_Qlt Qlt_gives_apartness Qle_is_not_lt Qgt_is_lt Qge_is_not_gt.

Program Definition is_COrdField
  := Build_is_COrdField _
 lt_CCSetoid_relation anyQ.le (default_greater _ lt_CCSetoid_relation)
 (default_grEq CField anyQ.le) lt_is_strict_order _ _ _ _ _ _.

Next Obligation. Proof with auto.
 apply anyQlt_from_Qlt.
 do 2 rewrite anyQ.spec_add.
 apply Qplus_resp_Qlt...
Qed.

Next Obligation. Proof with auto.
 apply anyQlt_from_Qlt.
 rewrite anyQ.spec_0 anyQ.spec_mul.
 apply Qmult_resp_pos_Qlt; rewrite <- anyQ.spec_0...
Qed.

Next Obligation. Proof with auto.
 unfold ap.
 destruct (Qlt_gives_apartness x y)...
 split; intro.
  cut ((anyQ.to_Q x < anyQ.to_Q y) or (anyQ.to_Q y < anyQ.to_Q x))...
  intros [A|B]; [left | right]; apply anyQlt_from_Qlt...
 apply q.
 intuition.
Qed.

Next Obligation. Proof with auto 20.
 destruct (Qle_is_not_lt x y).
 split; intro...
 intro.
 apply H...
Qed.

Next Obligation. firstorder. Qed.
Next Obligation. unfold default_grEq. firstorder. Qed.

Definition COrdField: COrdField := Build_COrdField _ _ _ _ _ is_COrdField.

Canonical Structure COrdField.

(* Next, we work toward making anyQ.t a metric space. To this end, we first define the ball relation: *)

Definition ball (e : Qpos): relation anyQ.t
  := fun a b => AbsSmall (anyQ.of_Q e) (anyQ.sub a b).

Add Morphism ball with signature QposEq ==> anyQ.eq ==> anyQ.eq ==> iff as anyQball_wd.
Proof with auto.
 unfold ball.
 intros.
 rewrite H0.
 rewrite H1.
 apply AbsSmall_morph_wd.
  unfold QposEq in H.
  simpl.
  unfold anyQ.eq.
  do 2 rewrite anyQ.spec_of_Q...
 reflexivity.
Qed.

(* .. which corresponds to Qball: *)

Lemma Qball_ball e (x y: Q): Qball e x y <-> ball e x y.
 intros.
 unfold Qball, ball, AbsSmall.
 simpl.
 split; intros [A B].
  split; apply anyQle_from_Qle.
   rewrite anyQ.spec_opp.
   rewrite anyQ.spec_sub.
   by repeat rewrite anyQ.spec_of_Q.
  rewrite anyQ.spec_sub.
  by repeat rewrite anyQ.spec_of_Q.
 split.
  clear B.
  pose proof anyQle_to_Qle _ _ A.
  revert H.
  rewrite anyQ.spec_sub.
  rewrite anyQ.spec_opp.
  do 3 rewrite anyQ.spec_of_Q.
  tauto.
 clear A.
 pose proof anyQle_to_Qle _ _ B.
 revert H.
 repeat rewrite anyQ.spec_of_Q.
 rewrite anyQ.spec_sub.
 repeat rewrite anyQ.spec_of_Q.
 tauto.
Qed.

Lemma Qball_ball' e (x y: anyQ.t): Qball e x y <-> ball e x y.
Proof with auto.
 intros.
 destruct (Qball_ball e x y).
 split; intro.
  rewrite <- (spec_to_Q x).
  rewrite <- (spec_to_Q y)...
 apply H0.
 do 2 rewrite spec_to_Q...
Qed.

(* .. and has desireable properties (which we just translate from Qball's): *)

Instance ball_reflexive e: Reflexive (ball e).
 destruct Q_is_MetricSpace.
 repeat intro.
 apply -> Qball_ball'.
 apply msp_refl.
Qed.

Instance ball_symmetric e: Symmetric (ball e).
Proof with auto.
 destruct Q_is_MetricSpace.
 repeat intro.
 apply -> Qball_ball'.
 apply msp_sym.
 apply <- Qball_ball'...
Qed.

Lemma ball_triangle (e1 e2: Qpos) (a b c: is_Setoid):
 ball e1 a b -> ball e2 b c -> ball (e1 + e2) a c.
Proof with auto.
 destruct Q_is_MetricSpace.
 repeat intro.
 apply -> Qball_ball'.
 apply msp_triangle with b.
  apply <- Qball_ball'...
 apply <- Qball_ball'...
Qed.

Lemma is_MetricSpace: is_MetricSpace is_Setoid ball.
Proof with auto.
 destruct Q_is_MetricSpace.
 simpl in *.
 split.
     apply ball_reflexive.
    apply ball_symmetric.
   apply ball_triangle.
  intros.
  apply -> Qball_ball'.
  apply msp_closed.
  intros.
  apply <- Qball_ball'...
 intros.
 simpl.
 unfold anyQ.eq.
 apply msp_eq.
 intros.
 apply <- Qball_ball'...
Qed.

Definition MetricSpace: MetricSpace
  := @Build_MetricSpace is_Setoid _ anyQball_wd is_MetricSpace.

(* Finally, we take the completion to make "reals": *)

Definition CR := Complete MetricSpace.

End QType_instances.
