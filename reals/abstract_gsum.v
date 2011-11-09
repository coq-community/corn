
(* Import in the following order to minimize trouble:
   stdlib, old corn things, mathclasses, new corn things *)

Require Import Limit.
Require Import abstract_algebra orders additional_operations streams series.

(** shorthand (Agda) notation for streams. *)
Notation "∞ x" := (Stream x) (at level 50).

(*
Lemma forall_impl {A} (P Q: ∞ A → Prop) (H1:∀ t, P t → Q t) :
 ∀ t, ForAll P t → ForAll Q t.
Proof.
 cofix G. 
 split.
 apply (H1 t). 
 destruct H as [Ha _]. 
 exact Ha.
 destruct H as [_ Hb].
 apply (G (tl t) Hb).
Qed.
*)

(** This section is about computing a generalized version of
 a geometric series.

 A geometric series has the form $s_{i+1} = r * s_i$ for some
 ratio $0 < r < 1$ (should we allow negative values for $a$
 the series will be alternating, however, we don't allow this).

 We impose a further positivity restriction on the elements
 of the series, $0 ≤ s_i$.

*)

Section geom_sum.

(** We work abstractly of an ordered ring R *)
Context `{FullPseudoSemiRingOrder R}.

(** R is not automatically a SemiRing as this causes loops in
   instance search. So we add it locally as this is needed for
   rewrites, e.g. (1)
*)
Instance: SemiRing R := pseudo_srorder_semiring.

(** A geometric series is a series with a constant ratio
    between succesive terms. Here we parametrize by this ratio
*)
Variable r : R.
Hypothesis Hr : 0 < r < 1.


(** A slightly stricter (positive) version of [GeometricSeries],
  which specifies a slightly more general (less-than instead of
  equality) version of a geometric series.
*)
Definition ARGeometricSeries : ∞ R → Prop :=
  ForAll (λ xs, 0 ≤ hd (tl xs) ≤ r * hd xs).


Section properties.

Context `(gs: ARGeometricSeries s).

(** If [s] is a geometric series, then so is it's tail *)
Lemma gs_tl : ARGeometricSeries (tl s).
Proof.
  apply ForAll_tl; now assumption.
Qed.

(** Every element in a geometric series is positive *)
Lemma gs_positive : 0 ≤ hd s.
Proof.
  destruct gs as [GS FA].
  apply (maps.order_reflecting_pos (.*.) r); try tauto.
  rewrite rings.mult_0_r.
  transitivity (hd (tl s)); tauto.
Qed. 

(** A geometric series is always decreasing *)
Lemma gs_decreasing : hd (tl s) ≤ hd s.
Proof.
  destruct gs.
  apply (maps.order_reflecting_pos (.*.) r); try tauto.
  transitivity (hd (tl s)); try tauto.
  rewrite <- (rings.mult_1_l (hd (tl s))) at 2.
  apply semirings.mult_le_compat; try solve [apply orders.lt_le; tauto].
   tauto.
  reflexivity. 
Qed.

Notation "'x₀'" := (hd s).

(* if only...

   Notation "'xₙ₊1'" := (Str_nth (n + 1) s).
   Notation "'xₙ'"   := (Str_nth n s).
*)
Require Import nat_pow.

Lemma should_work x y: x ≤ y → r * x ≤ r * y. 
 apply (maps.order_preserving_nonneg (.*.) r).
 destruct Hr as [Ha Hb].
 (* 0 ≤ r ?? *)
Admitted.

(* [peano_naturals.nat_induction] is a induction scheme that uses
   type classed naturals. *)

Lemma gs_nth_rn n : Str_nth n s ≤ r^n * x₀.
Proof.
  induction n using peano_naturals.nat_induction.
   rewrite nat_pow_0, rings.mult_1_l; compute; reflexivity.
  rewrite nat_pow_S.
  apply (ForAll_Str_nth_tl n) in gs.
  destruct gs as [[GS1 GS2] FA].
  replace (hd (Str_nth_tl n s)) with (Str_nth n s) in GS2 by auto.
  replace (hd (tl (Str_nth_tl n s))) with (Str_nth (1+n) s) in GS2 by (eapply _).
  (* hmm *)
  replace (Str_nth n s ≤ r ^ n * x₀) with (r * Str_nth n s ≤ r * r ^ n * x₀) in IHn.
  rewrite <- IHn.
  apply GS2.
Admitted.

End properties.

(** A geometric series is decreasing and non negative. *)
Lemma gs_dnn `(gs: ARGeometricSeries s) : DecreasingNonNegative s.
Proof.
 unfold DecreasingNonNegative.
 revert s gs.
 cofix FIX; intros s gs.
 constructor.
  now split; auto using gs_positive, gs_tl, gs_decreasing.
 apply FIX, gs_tl; now assumption.
Qed.

End geom_sum.