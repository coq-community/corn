(* This module provides C-CoRN models for modules implementing the QType
 signature.

One example of such a module is BigQ, which uses fast machine integers, so with
the current module one can say:

  Require Import BigQ.
  Module BigCQ := QType_instances BigQ.
  Check BigCQ.CR.

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

Require Import
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

(* The semantics of anyQ are specified by translation to Q. Consequently, many of our proofs
 will just follow this translation and use existing results for Q. We use a little
 rewrite database to automate the translation to and from Q. *)

Hint Rewrite
 anyQ.spec_add anyQ.spec_sub anyQ.spec_mul anyQ.spec_div
 anyQ.spec_opp anyQ.spec_inv anyQ.spec_0 anyQ.spec_1
 anyQ.spec_of_Q anyQ.spec_compare
   : toQ_db.

Hint Rewrite <-
 anyQ.spec_add anyQ.spec_sub anyQ.spec_mul anyQ.spec_div
 anyQ.spec_opp anyQ.spec_inv anyQ.spec_0 anyQ.spec_1
 anyQ.spec_of_Q anyQ.spec_compare
   : fromQ_db.

Ltac toQ := unfold anyQ.eq in *; try autorewrite with toQ_db; intros; autorewrite with toQ_db.
Ltac fromQ := intros; autorewrite with fromQ_db.

(* First, all operations on anyQ are morphisms: *)

Instance add_mor: Morphism (equiv ==> equiv ==> equiv) anyQ.add.
Proof. repeat intro. simpl in *. toQ. by rewrite H H0. Qed.
 (* Hm, why can't congruence do these rewrites? *)

Instance sub_mor: Morphism (equiv ==> equiv ==> equiv) anyQ.sub.
Proof. repeat intro. simpl in *. toQ. by rewrite H H0. Qed.

Instance mul_mor: Morphism (equiv ==> equiv ==> equiv) anyQ.mul.
Proof. repeat intro. simpl in *. toQ. by rewrite H H0. Qed.

Instance opp_mor: Morphism (equiv ==> equiv) anyQ.opp.
Proof. repeat intro. simpl in *. toQ. by rewrite H. Qed.

Instance inv_mor: Morphism (equiv ==> equiv) anyQ.inv.
Proof. repeat intro. simpl in *. toQ. by rewrite H. Qed.

Instance lt_mor: Morphism (equiv ==> equiv ==> iff) anyQ.lt.
Proof. repeat intro. simpl in *. unfold anyQ.lt. toQ. by rewrite H H0. Qed.

Instance le_mor: Morphism (equiv ==> equiv ==> iff) anyQ.le.
Proof. repeat intro. unfold anyQ.le. simpl in *. toQ. by rewrite H H0. Qed.

Instance of_Q_mor: Morphism (Qeq ==> equiv) anyQ.of_Q.
Proof. repeat intro. simpl. by toQ. Qed.

(* anyQ is a ring *)

Lemma anyQ_ring_theory: ring_theory anyQ.zero anyQ.one anyQ.add anyQ.mul anyQ.sub anyQ.opp anyQ.eq.
Proof. constructor; unfold anyQ.eq; toQ; ring. Qed.

Add Ring anyQ: anyQ_ring_theory.

(* relating anyQ relations to Q relations: *)

Lemma anyQlt_Qlt_bidir_in_anyQ (x y: anyQ.t): anyQ.lt x y <-> x < y.
Proof. unfold anyQ.lt. by toQ. Qed.

Lemma anyQle_Qle_bidir_in_anyQ (x y: anyQ.t): anyQ.le x y <-> x <= y.
Proof. unfold anyQ.le. by toQ. Qed.

Hint Rewrite anyQlt_Qlt_bidir_in_anyQ anyQle_Qle_bidir_in_anyQ spec_to_Q: toQ_db.
Hint Rewrite <- anyQlt_Qlt_bidir_in_anyQ anyQle_Qle_bidir_in_anyQ spec_to_Q: fromQ_db.

(* We now build models for the CoRN hierarchy, starting with CSetoid, which we
 get for free (using module decsetoid) because our setoid equality is decidable. *)

Let ap := decsetoid.apart.

Canonical Structure CSetoid := decsetoid.CSetoid_from_class.
Canonical Structure is_Setoid := cs_crr CSetoid.

(* Some more CSetoid-specific morphism-like things: *)

Lemma add_wd: bin_fun_wd CSetoid CSetoid CSetoid anyQ.add.
Proof. repeat intro. apply add_mor; assumption. Qed.

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

Canonical Structure add_is_bin_fun := Build_CSetoid_bin_fun _ _ _ _ add_strext.
Canonical Structure mul_is_bin_fun := Build_CSetoid_bin_fun _ _ _ _ mul_strext.
Canonical Structure anyQ_opp_fun := Build_CSetoid_fun _ _ _ opp_strext.

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
Proof. repeat intro. apply (Qlt_is_antisymmetric_unfolded x y); by fromQ. Qed.

Instance lt_transitive: Transitive anyQ.lt.
Proof. repeat intro. toQ. apply Qlt_trans with y; by fromQ. Qed.

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
Proof.
 apply Build_is_CRing with mul_assoc.
    apply is_multiplicative_CMonoid.
   repeat intro. simpl. ring.
  repeat intro. simpl. ring.
 simpl. intro. apply Q_apart_0_1. by fromQ.
Qed.

Definition CRing: CRing := Build_CRing _ _ _ is_CRing.

Canonical Structure CRing.

(* And a CField: *)

Lemma is_CField: is_CField CRing (fun x _ => anyQ.inv x).
Proof. red. unfold is_inverse. simpl. intro x. toQ. split; by field. Qed.

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

Next Obligation. Proof. toQ. apply Qplus_resp_Qlt. by fromQ. Qed.
Next Obligation. Proof. toQ. apply Qmult_resp_pos_Qlt; by fromQ. Qed.

Next Obligation. Proof.
 destruct (Qlt_gives_apartness x y).
 split; intro.
  by destruct s; [| left | right]; toQ.
 apply q.
 destruct H; [left | right]; by fromQ.
Qed.

Next Obligation. Proof.
 unfold Not.
 destruct (Qle_is_not_lt x y).
 split; toQ; auto.
 by apply H.
Qed.

Next Obligation. firstorder. Qed.
Next Obligation. unfold default_grEq. firstorder. Qed.

Definition COrdField: COrdField := Build_COrdField _ _ _ _ _ is_COrdField.

Canonical Structure COrdField.

(* Next, we work toward making anyQ.t a metric space. To this end, we first define the ball relation: *)

Definition ball (e : Qpos): relation anyQ.t
  := fun a b => AbsSmall (anyQ.of_Q e) (anyQ.sub a b).

Instance QposAsQ_mor: Morphism (QposEq ==> Qeq) QposAsQ.
Proof. done. Qed.

Instance ball_mor: Morphism (QposEq ==> equiv ==> equiv ==> iff) ball.
Proof. repeat intro. unfold ball. rewrite H H0 H1. reflexivity. Qed.

(* .. which corresponds to Qball: *)

Lemma ball_Qball e (x y: anyQ.t): ball e x y <-> Qball e x y.
Proof. unfold Qball, ball, AbsSmall. by toQ. Qed.

Hint Rewrite ball_Qball: toQ_db.
Hint Rewrite <- ball_Qball: fromQ_db.

(* .. and has desireable properties (which we just translate from Qball's): *)

Instance ball_reflexive e: Reflexive (ball e).
Proof. repeat intro. toQ. reflexivity. Qed.

Instance ball_symmetric e: Symmetric (ball e).
Proof with auto. repeat intro. toQ. symmetry. fromQ... Qed.

Lemma ball_triangle (e1 e2: Qpos) (a b c: is_Setoid):
 ball e1 a b -> ball e2 b c -> ball (e1 + e2) a c.
Proof. toQ. apply (@msp_triangle _ _ Q_is_MetricSpace) with b; by fromQ. Qed.

Lemma is_MetricSpace: is_MetricSpace is_Setoid ball.
Proof.
 split; auto with typeclass_instances.
   apply ball_triangle.
  toQ. apply (@msp_closed _ _ Q_is_MetricSpace). by fromQ.
 simpl. toQ. apply (@msp_eq _ _ Q_is_MetricSpace). by fromQ.
Qed.

Definition MetricSpace: MetricSpace
  := @Build_MetricSpace is_Setoid _ ball_mor is_MetricSpace.

(* Finally, we take the completion to make "reals": *)

Definition CR := Complete MetricSpace.

End QType_instances.
