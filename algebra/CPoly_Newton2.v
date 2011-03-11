Require Import
 Unicode.Utf8
 Setoid Arith List Program Permutation metric2.Classified
 CSetoids CPoly_ApZero CRings CPoly_Degree
 CRArith Qmetric Qring CReals
 stdlib_omissions.Pair stdlib_omissions.Q
 list_separates SetoidPermutation
 util.Container NewAbstractIntegration
 algebra.CPoly_Newton.

Require ne_list.
Import ne_list.notations.
Opaque CR.

Section contents.

  Notation QPoint := (Q * CR)%type.
  Notation CRPoint := (CR * CR)%type.
  Local Notation Σ := cm_Sum.
Require Import Qabs.
  Section inner_space.
(* Need vector space, norm, inner product, metric from norm, Lipschitz continuity from boundedness *)
  Definition norm `(x: Vector.t Q n):=Σ (map Qabs x).
  
  Definition inner (n:nat)(x y : Vector.t Q n):=Σ(map (λ p, Qmult (fst p) (snd p)) (zip x y)).
  
  End Hilbert_space.

  Section divdiff_as_repeated_integral.

    Context
      (n: nat) (points: Vector.t Q (S n)).

    Context 
      (nth_deriv_bound: Range CR)
      (nth_deriv: Q → sig ((∈ nth_deriv_bound)))
        (* Todo: only require boundedness on the interval that contains the points. *)
        `{!UniformlyContinuous_mu nth_deriv}
        `{!UniformlyContinuous nth_deriv}.
          (* Todo: This should be replaced with some "n times differentiable" requirement on a subject function. *)

    Opaque Qmult Qplus Qminus.
       (* Without these, instance resolution gets a little too enthusiastic and breaks these operations open when
       looking for PointFree instances below. It's actually kinda neat that it can put these in PointFree form though. *)


    Definition totalweight {n} (ws: Vector.t Q n): Q := cm_Sum ws.

    Notation SomeWeights n := (sig (λ ts: Vector.t Q n, totalweight ts <= 1)%Q).

    (** apply_weights: *)
    (** Note that this an innerproduct *)
    (** |<points,w>|≤|points| |w|
         |<points,w>-<points,v>|=|<points,w-v>| ≤||points|| ||w-v||
       , the function is Lipshitz  with constant norm ||points||*)
    Definition apply_weights (w: Vector.t Q (S n)): Q :=
      cm_Sum (map (λ p, Qmult (fst p) (snd p)) (zip points (Vector.to_list w))).

    Instance apply_weights_mu: UniformlyContinuous_mu apply_weights.
    constructor. exact (fun x => x).
    Defined.

    Instance apply_weights_uc: UniformlyContinuous apply_weights.
    constructor; try apply _.
    intros ??? H.
    Check apply_weights. 
    Obligation Tactic := idtac.

    (** "inner", the function of n weights: *)

    Program Definition inner: SomeWeights n → sig ((∈ nth_deriv_bound))
      := λ ts, nth_deriv (apply_weights (Vector.cons _ (1 - totalweight ts) _ ts))%Q.

    Instance inner_mu: UniformlyContinuous_mu inner.
     unfold inner.
     apply compose_mu.
      apply _.
     apply (@compose_mu (SomeWeights n) (Vector.t Q (S n)) Q (apply_weights)).
      apply _.
    Admitted.

    Instance inner_uc: UniformlyContinuous inner.
    Admitted.

    (** Next up is "reduce" *)

    Definition G (n: nat): Type := UCFunction (SomeWeights n) (sig ((∈ nth_deriv_bound))).

Open Local Scope CR_scope.

Local Notation Σ := cm_Sum.
Local Notation Π := cr_Product.

    Section reduce.

      Variables (m: nat) (X: G (S m)).

      Program Definition integrand (ts: SomeWeights m) (t: sig ((∈ (0, (1 - totalweight ts))))%Q): sig ((∈ nth_deriv_bound)) :=
        X (@uncurry_Vector_cons Q m (` t, ` ts)).

      Next Obligation. intros. change (`t + Σ  (` ts) <= 1)%Q. admit. Qed.

      Instance integrand_mu: ∀ ts, UniformlyContinuous_mu (integrand ts).
       unfold integrand.
       intros.
       apply compose_mu.
        apply _.
       constructor.
       intro.
       apply Qpos2QposInf.
       exact H.
      Defined.

      Instance integrand_uc: ∀ ts, UniformlyContinuous (integrand ts).
      Proof.
       unfold integrand. intros.
       apply compose_uc. apply _.
       constructor; try apply _.
       simpl. intros.
       constructor. assumption.
       simpl.
       admit. (* doable *)
      Qed.
(* Does not compile 
      Program Definition reduce_raw: SomeWeights m → sig ((∈ nth_deriv_bound))
       := λ ts, @integrate_ucFunc_wrapped_for_continuity nth_deriv_bound (existT _ (0, 1 - totalweight  (` ts))%Q
         (ucFunction (integrand ts))).

      Next Obligation.
       intros.
       unfold integrate_ucFunc_wrapped_for_continuity.
       simpl.
      Admitted. (* need to show that the result is bounded *)

      Instance reduce_mu: UniformlyContinuous_mu reduce_raw.
      Proof with auto.
       unfold reduce_raw.
       apply exist_mu.
       set (integrate_ucFunc_wrapped_for_continuity nth_deriv_bound).
       apply (@compose_mu  (SomeWeights m)  {r : Range Q & UCFunction (sig ((∈r))) (sig ((∈nth_deriv_bound)))} CR s).
        apply _.
       admit.
      Defined.

      Instance reduce_uc: UniformlyContinuous reduce_raw.
      Proof with auto.
       unfold reduce_raw.
       apply exist_uc.
       set (integrate_ucFunc_wrapped_for_continuity nth_deriv_bound).
       apply (@compose_uc  (SomeWeights m)  _ _ {r : Range Q & UCFunction (sig ((∈r))) (sig ((∈nth_deriv_bound)))} _ _ CR _ _ s).
        apply _.
       admit.
      Qed.

      Definition reduce: G m := ucFunction reduce_raw.
*)
    End reduce.

    (** Finally, the divided difference arises from iterated reduction of the inner function: *)
(*
    Definition alt_divdiff: CR.
     apply (iterate reduce (ucFunction inner)).
     exists (Vector.nil Q).
     abstract (unfold totalweight; simpl; auto).
    Defined. (* Todo: Why won't Program work here? *)
*)
  End divdiff_as_repeated_integral.
(*  Print Assumptions alt_divdiff.*)
End contents.