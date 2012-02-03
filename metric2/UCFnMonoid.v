Require Import Utf8 Streams UniformContinuity abstract_algebra.


(** Uniform continuous maps from a metric space to itself (endomaps)
    form a monoid under composition
*)
Section uniform_cont_fn_monoid.

  Context {X:MetricSpace}.
  Open Scope uc_scope. (* for the _ --> _ notation *)

  Instance ucfn_unit: MonUnit (X --> X) := @uc_id X.
  Instance ucfn_compose {X}: SgOp (X --> X) := @uc_compose X X X.

  Instance ucfn_monoid: Monoid (X --> X).
  Proof.
    repeat split; try apply _; easy.
  Qed.

End uniform_cont_fn_monoid.
