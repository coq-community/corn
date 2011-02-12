Require Import CRArith CRpartialorder CRpower.
Require Import abstract_algebra theory.rings stdlib_rationals additional_operations.

Local Opaque CR.

(* I use underscores in the names to distinguish these instances from their definitions *)
Instance CR_inject_Q: Inject Q CR := inject_Q.
Instance CR_0: RingZero CR := (' 0)%CR.
Instance CR_1: RingOne CR := (' 1)%CR.
Instance CR_plus: RingPlus CR := ucFun2 CRplus.
Instance CR_mult: RingMult CR := CRmult.
Instance CR_inv: GroupInv CR := CRopp.
Instance CR_le: Order CR := CRle.
Instance CR_lt: CSOrder CR := CRlt.
Instance CR_apart: Apart CR := CRapart.

Instance: Ring CR.
Proof. apply (rings.from_stdlib_ring_theory CR_ring_theory). Qed.

Instance: PartialOrder CRle.
Proof.
  repeat (split; try apply _).
    intros x. apply CRle_refl.
   intros x y z. apply CRle_trans.
  intros x y E F. apply CRle_def. intuition.
Qed.
  
Instance: SemiRing_Morphism inject_Q.
Proof.
  repeat (split; try apply _); intros; try reflexivity; symmetry.
   apply CRplus_Qplus.
  apply CRmult_Qmult.
Qed.

Instance: Injective inject_Q.
Proof.
  repeat (split; try apply _); intros.
  apply CReq_Qeq. assumption.
Qed.