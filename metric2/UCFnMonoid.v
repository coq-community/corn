Require Import Coq.Unicode.Utf8 MathClasses.theory.CoqStreams CoRN.metric2.UniformContinuity MathClasses.interfaces.abstract_algebra.


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
    repeat split.
    - apply Qle_refl.
    - reflexivity.
    - apply Qle_refl.
    - intros; symmetry; apply H.
    - apply Qle_refl.
    - intros. transitivity (y a). apply H. apply H0.
    - apply Qle_refl.
    - reflexivity.
    - apply Qle_refl.
    - intros. simpl. transitivity (x (y0 a)). 
      destruct H0. rewrite H1. reflexivity.
      apply H.
    - apply Qle_refl.
    - reflexivity.
    - apply Qle_refl.
    - reflexivity.
  Qed.

End uniform_cont_fn_monoid.
