Require Import CRArith CRpartialorder CRpower.
Require Import abstract_algebra theory.rings stdlib_rationals additional_operations.

Local Opaque CR.

(* I use underscores in the names to distinguish these instances from their definitions *)
Instance inject_Q_CR: Coerce Q CR :=inject_Q.
Instance CR_0: RingZero CR := ('0 : CR).
Instance CR_1: RingOne CR := ('1 : CR).
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

Instance: OrderEmbedding inject_Q.
Proof. repeat (split; try apply _); now apply CRle_Qle. Qed.

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

Instance: RingOrder CR_le.
Proof.
  repeat (split; try apply _).
   intros x y E. now apply CRplus_le_l.
  intros x E1 y E2.
  rewrite <-(rings.mult_0_r x).
  now apply: mult_resp_leEq_lft.
Qed.

Instance: ∀ x y : CR, Stable (x = y).
Proof. exact (stableEq _ (Complete_stable Qmetric.stableQ)). Qed.

Instance CR_power_N: Pow CR N := λ x n, CRpower_N n x.

Instance: NatPowSpec CR N _.
Proof.
  split; unfold pow, CR_power_N. 
    solve_proper.
   intros x. change ('(1 : Q) = (1 : CR)). now apply rings.preserves_1.
  intros x n.
  rewrite <-(CRasIRasCR_id x).
  rewrite <-?CRpower_N_correct.
  rewrite <-IR_mult_as_CR.
  rewrite Nnat.nat_of_Nplus.
  apply IRasCR_wd. symmetry. now apply nexp_Sn.
Qed. 
  