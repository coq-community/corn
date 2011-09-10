Require Import 
  Program CornTac workaround_tactics
  Qmetric Qdlog CRGeometricSum
  ApproximateRationals ARArith Limit
  abstract_algebra int_pow theory.streams theory.series
  ARAlternatingSum.

Local Notation "∞ x" := (Stream x) (at level 37).

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

(** This section is about computing a generalized version of
 a geometric series.

 A geometric series has the form $s_{i+1} = r * s_i$ for some
 ratio $0 < r < 1$ (should we allow negative values for $a$
 the series will be alternating, however, we don't allow this).

 We impose a further positivity restriction on the elements
 of the series, $0 ≤ s_i$.

*)

Section geom_sum.
Context `{AppRationals AQ}.

(** The ratio *)
Variable r : Q_as_MetricSpace.
Hypothesis Hr : 0 < r < 1.


(** A slightly stricter version of [GeometricSeries] *)
Definition ARGeometricSeries : ∞ Q_as_MetricSpace → Prop :=
  ForAll (λ xs, 0 ≤ hd (tl xs) ≤ r * hd xs).

(** If [s] is a geometric series, then so is it's tail *)

Lemma gs_tl `(gs: ARGeometricSeries s) : ARGeometricSeries (tl s).
Proof.
 apply ForAll_tl; now assumption.
Qed.

Lemma ARGeomSum_dnn `(gs: ARGeometricSeries s) : DecreasingNonNegative s.
Proof.
 unfold DecreasingNonNegative.
 revert s gs.
 cofix FIX; intros s gs.
 constructor.
  destruct gs.
  split; try tauto.
  apply (maps.order_reflecting_pos (.*.) r); try tauto.
  transitivity (hd (tl s)); try tauto.
  rewrite <-(rings.mult_1_l (hd (tl s))) at 2.
  apply semirings.mult_le_compat; try solve [apply orders.lt_le; tauto].
  tauto.
  reflexivity. 
 apply FIX.
 apply gs_tl; now assumption.
Qed.

Lemma gs_nth_rn `(gs: ARGeometricSeries sQ):
  ∀ n, ForAll (λ s, hd s ≤ (r ^ n) * (hd sQ)) (Str_nth_tl n sQ).
Proof.
  admit.
(*
  induction n.
   revert sQ gs.
   cofix FIX.
    constructor.
     destruct gs.
     simpl.
     admit. (* TODO: rewrite (nat_pow_0 r). *)
 Guarded.
   apply FIX.
   simpl. 
   constructor.
*)
Qed.



(** We now proof that as $i → ∞$ then $x_i → 0$, ie. the series has limit 0 *)

Section gs_zl.

Context `(d : DivisionStream sQ sN sD).
Context `{gs : ARGeometricSeries sQ}.

(*
Require Import Qround.

(* For a given ε, we want to know how deep
 we need to go into the stream such that
 $x_i < ε$.  *)

Definition slen (ε: Qpos) : Z := 
  Qceiling ((ε/(hd sQ) * (1 - r))). (* → r ^ n <= ε *)
 
(*[??] how to go from (abs a) : Z to (abs a) : nat ? *)
(*[??] TODO ceiling in canonical_names like abs? *)

Lemma gs_length (ε : Qpos)`(gs: ARGeometricSeries s) : 
  ForAll (λ s, hd s ≤ ε) (Str_nth_tl (' slen ε)  s).

Lemma ARGeomSum_zl `(gs: ARGeometricSeries s) : Limit s 0.
 unfold Limit. 
 intros.
 case ε.
 intros.
 unfold NearBy.
 admit.
Qed.
*)


(** Again, similar to the alternating sum, we want to postpone
 the division operation.

 This functions sums [l] entries of the the [sN/sD] stream with
 precision [2^k].
*)
Fixpoint ARGeomSum (sN sD : Stream AQ) (l : nat) (k : Z) :=
  match l with 
  | O => 0
  | S l' => app_div (hd sN) (hd sD) k + ARGeomSum (tl sN) (tl sD) l' k
  end.

(*
Definition ARInfGeomSum_raw (ε : Qpos) : AQ_as_MetricSpace :=
 let εk := Qdlog2 ε - 1 in
 let l  := ARInfAltSum_length εk
 in ARGeomSum sN sD l (εk - Z.log2_up (Z_of_nat l)).

(** We compute a upper bound on the length that we need to sum *)
Program Definition ARGeomSum_length (e : Qpos) : positive :=
  Qceiling (1 + (e * (1 - r))).

Lemma ARInfGeomSum_correct:
 'ARInfGeomSum = InfiniteGeometricSum sQ.

(** At this point we can reuse a lot of stuff from ARAlternatingSum:
 
  - DivisionStream,
  - ARInfAltSum_stream + lemmas (DivisionStream with logarithmically
    increasing division precision),
  - *ball lemmas, 
*)

End geom_sum.

Section geom_main.

Context `(d : DivisionStream sQ sN sD).
Context {dnn : DecreasingNonNegative sQ} {zl : Limit sQ 0}.

Program Definition ARInfGeomSum_length (k : Z) : nat :=
  let P :=  λ s, AQball_bool k (hd s) 0 in
  let s := ARInfAltSum_stream sN sD k 0 in
  takeUntil_length P (LazyExists_inc big s _).


CoFixpoint ARInfGeomSum_stream (sN sD : ∞AQ) (k l : Z) : ∞AQ := Cons 
  (app_div_above (hd sN) (hd sD) (k - Z.log2_up l))
  (ARInfGeomSum_stream (tl sN) (tl sD) k (l + 1)).

(* TODO proof
    - tl S = S tl
    - nth_tl S = S nth_tl
*)


(* use GeometricCovergenceLemma:
      1/(ε*(1 - r)) ≤ n → r^n ≤ ε
*)

(*
Notation "t $ r" := (t r)
  (at level 100, right associativity, only parsing).
*)

(**
  This function calculates the n-th position at which
  the stream has a value ≤ ε

  Let [s_0, s_1, ...] be a geometric series.
  We then have [|s_n| ≤ a^n * |s₀|], so in order to
  get the n-th position at which the stream is ≤ ε
  we need to calculate log (ε * s₀) in base a.
*)

Definition bar `(g : GeometricSeries s) (ε:QposInf) : nat :=
  (* convert to base a *)
  let lg := Qdlog(a) / Qdlog(ε / hd s) in
    Qround.Qceiling(lg).

*)