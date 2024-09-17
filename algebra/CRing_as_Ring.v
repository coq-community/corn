
Require Export CoRN.algebra.CRings.
From Coq Require Export Ring.
Definition CRing_Ring(R:CRing):(ring_theory (@cm_unit R) (@cr_one R) (@csg_op R) (@cr_mult R) (fun x y => x [-] y) (@cg_inv R) (@cs_eq R)).
Proof.
 split;algebra.
Qed.
