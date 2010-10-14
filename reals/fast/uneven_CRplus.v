Require Import
  QArith Qpossec Qmetric CRArith.

Set Automatic Introduction.

(** The approximation function for CRplus results distributes a given error evenly
among its two operands. This is a perfectly reasonable implementation choice,
but it is conceptually arbitrary: any ratio works fine. Furthermore, when
reasoning about particular uses of CRplus, different ratios can be more
natural fits to the proof at hand. For instance, in the additivity proof for the Riemann
integral implementation, having the error for the sum of two integrals distributed
proportionally to the widths of the two contiguous ranges makes it nicely match the
error for the full integral on both sides.

For situations like these, we now do a very ad-hoc redefinition of addition with
a user-specified error distribution ratio, and show that it is equivalent to the
normal CRplus. *)

Section uneven_CRplus.

  Variables
    (l r: Qpos) (* These are the error weights for x and y. *)
    (x y: CR).

  Let ll: Qpos := (l * Qpos_inv (l + r))%Qpos.
  Let rr: Qpos := (r * Qpos_inv (l + r))%Qpos.

  Let llrr: ll + rr == 1.
  Proof.
   unfold ll, rr. simpl.
   field. intro.
   apply (Qpos_nonzero (l+r)%Qpos).
   assumption.
  Qed.

  Definition uneven_CRplus_approx (e: Qpos): Q_as_MetricSpace := approximate x (e * ll) + approximate y (e * rr).

  Lemma uneven_CRplus_is_RegularFunction: is_RegularFunction_noInf _ uneven_CRplus_approx.
  Proof with auto.
   intros e1 e2.
   unfold uneven_CRplus_approx. simpl.
   setoid_replace (e1 + e2)%Qpos with ((e1 * ll + e2 * ll) + (e1 * rr + e2 * rr))%Qpos.
    apply Qball_plus.
     apply (regFun_prf x (e1*ll)%Qpos (e2*ll)%Qpos).
    apply (regFun_prf y (e1*rr)%Qpos (e2*rr)%Qpos).
   unfold QposEq.
   transitivity ((e1 + e2) * (ll + rr))%Qpos; simpl.
    rewrite llrr. ring.
   ring.
  Qed.

  Definition uneven_CRplus: CR := @mkRegularFunction Q_as_MetricSpace 0 _ uneven_CRplus_is_RegularFunction.

  Lemma uneven_CRplus_correct: (uneven_CRplus == x + y)%CR.
  Proof with simpl; try ring.
   simpl.
   apply regFunEq_e. intro e.
   rewrite approximate_CRplus...
   unfold uneven_CRplus_approx.
   setoid_replace (e + e)%Qpos with ((e * ll + (1#2) * e) + (e * rr + (1#2) * e))%Qpos.
    apply Qball_plus; apply regFun_prf.
   unfold QposEq.
   transitivity (e + e * (ll + rr))%Qpos...
   rewrite llrr...
  Qed.

End uneven_CRplus.
