Require Export CSetoidFun.

Section move_us.

Lemma csr_wd :
 forall (S:CSetoid) (R:CSetoid_relation S) (x1 x2 y1 y2:S),
   R x1 x2 -> (x1[=]y1) -> (x2[=]y2) -> R y1 y2.
Proof
  fun S R x1 x2 y1 y2 h h0 h1 =>
    csr_wdl S R x1 y2 y1 (csr_wdr S R x1 x2 y2 h h1) h0.

Lemma Ccsr_wd :
 forall (S:CSetoid) (R:CCSetoid_relation S) (x1 x2 y1 y2:S),
   R x1 x2 -> (x1[=]y1) -> (x2[=]y2) -> R y1 y2.
Proof
  fun S R x1 x2 y1 y2 h h0 h1 =>
    Ccsr_wdl S R x1 y2 y1 (Ccsr_wdr S R x1 x2 y2 h h1) h0.

Lemma eq_wd :
 forall (S:CSetoid) (x1 x2 y1 y2:S),
   (x1[=]x2) -> (x1[=]y1) -> (x2[=]y2) -> y1[=]y2.
Proof
  fun S x1 x2 y1 y2 h h0 h1 =>
    eq_transitive S y1 x1 y2 (eq_symmetric S x1 y1 h0)
      (eq_transitive S x1 x2 y2 h h1).

Lemma ap_wd :
 forall (S:CSetoid) (x1 x2 y1 y2:S),
   (x1[#]x2) -> (x1[=]y1) -> (x2[=]y2) -> y1[#]y2.
Proof
  fun S x1 x2 y1 y2 h h0 h1 =>
    ap_wdl S x1 y2 y1 (ap_wdr S x1 x2 y2 h h1) h0.

Lemma COr_elim : forall A B C:CProp, (A -> C) -> (B -> C) -> A or B -> C.
intros A B C H H0 H1.
elim H1; intro H2; [ exact (H H2) | exact (H0 H2) ].
Qed.

End move_us.
