Require Import Unicode.Utf8 Qmetric CRmetric UniformContinuity.


(** The uniformly continuous constant function [Q_as_MetricSpace --> CR]. *)
Section const_fun_uc.
 Variable c : Q_as_MetricSpace.

 Definition const_raw : Q_as_MetricSpace → CR := λ _, ('(c%Q))%CR.
 Definition const_mu (ε:Qpos) : QposInf := ε.

(* Anything modulus bigger than 0 will do, so we pick [id : Qpos → QposInf]
 written as [(λ ε, ε)%Qpos]. *)
 Lemma const_uc_prf : is_UniformlyContinuousFunction const_raw (λ ε, ε)%Qpos.
 Proof.
   admit.
 Qed.

 (** [const_uc c] defines the uniformly continuous function [λ _, c] *)
 Open Scope uc_scope.
 Definition const_uc : Q_as_MetricSpace --> CR :=
   Build_UniformlyContinuousFunction (const_uc_prf).
End const_fun_uc.
