(*
Copyright © 2009 Valentin Blot

Permission is hereby granted, free of charge, to any person obtaining a copy of
this proof and associated documentation files (the "Proof"), to deal in
the Proof without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Proof, and to permit persons to whom the Proof is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Proof.

THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
*)

Require Import CPoly_Degree Lia.
Import CRing_Homomorphisms.coercions.

Set Implicit Arguments.
Unset Strict Implicit.

Section poly_eucl.
Variable CR : CRing.

Add Ring CR: (CRing_Ring CR).
Add Ring cpolycring_th : (CRing_Ring (cpoly_cring CR)).

Lemma degree_poly_div : forall (m n : nat) (f g : cpoly CR),
  let f1 := (_C_ (nth_coeff n g) [*] f [-] _C_ (nth_coeff (S m) f) [*] ((_X_ [^] ((S m) - n)) [*] g)) in
    S m >= n -> degree_le (S m) f -> degree_le n g -> degree_le m f1.
Proof.
 intros m n f g f1 ge_m_n df dg p Hp; unfold f1; clear f1.
 rewrite -> nth_coeff_minus, nth_coeff_c_mult_p, nth_coeff_c_mult_p, nth_coeff_mult.
 rewrite -> (Sum_term _ _ _ (S m - n)); [ | lia | lia | intros ].
  rewrite -> nth_coeff_nexp_eq.
  destruct Hp.
   replace (S m - (S m - n)) with n by lia.
   unfold cg_minus. ring.
  rewrite -> (dg (S m0 - (S m - n))); [ | lia].
  rewrite -> df; [ unfold cg_minus; ring | lia].
 rewrite nth_coeff_nexp_neq. ring. assumption.
Qed.

Theorem cpoly_div1 : forall (m n : nat) (f g : cpoly_cring CR),
  degree_le m f -> degree_le (S n) g -> n <= m ->
    {qr: (cpoly_cring CR)*(cpoly_cring CR) &
    let (q,r):=qr in f [*] _C_ ((nth_coeff (S n) g) [^] (m - n)) [=] q [*] g [+] r &
    let (q,r):=qr in degree_le n r}.
Proof.
 intros m n; generalize (refl_equal (m - n)).
 generalize (m - n) at 1 as p; intro p; revert m n; induction p; intros.
  exists (([0] : cpoly_cring CR),f).
   rewrite <- H.
   simpl (nth_coeff (S n) g[^]0). rewrite <- c_one. ring.
  replace n with m by lia; assumption.
 set (f1 := (_C_ (nth_coeff (S n) g) [*] f [-] _C_ (nth_coeff m f) [*] ((_X_ [^] (m - (S n))) [*] g))).
 destruct (IHp (m - 1) n) with (f := f1) (g := g); [ lia | | assumption | lia | ].
  unfold f1; clear f1.
  assert (HypTmp : m = S (m - 1)); [ lia | rewrite HypTmp; rewrite <- HypTmp at 1 ].
  apply degree_poly_div; [ lia | rewrite <- HypTmp; assumption | assumption ].
 destruct x as [q1 r1].
 exists (q1 [+] _C_ ((nth_coeff (S n) g)[^](m - S n) [*] (nth_coeff m f)) [*] _X_ [^] (m - S n), r1); [ | assumption].
 unfold f1 in y.
 rewrite -> ring_distl_unfolded. rewrite <- plus_assoc_unfolded. rewrite -> (cag_commutes _ _ r1). rewrite -> plus_assoc_unfolded. rewrite  <- y.
 replace (m - n) with (S (m - S n)) by lia.
 replace (m - 1 - n) with (m - S n) by lia.
 rewrite <- nexp_Sn.
 generalize (nth_coeff (S n) g) (nth_coeff m f) (m - S n).
 intros. rewrite c_mult, c_mult. unfold cg_minus. ring.
Qed.

Definition degree_lt_pair (p q : cpoly_cring CR) := (forall n : nat, degree_le (S n) q -> degree_le n p) and (degree_le O q -> p [=] [0]).
Lemma cpoly_div2 : forall (n m : nat) (a b c : cpoly_cring CR),
  degree_le n a -> monic m b -> degree_lt_pair c b -> a [*] b [=] c ->
    a [=] [0].
Proof.
 induction n.
  intros m a b c H X H1 H2; destruct (degree_le_zero _ _ H) as [x s].
  revert H1. rewrite -> s; destruct X as [H0 H1]; rewrite -> c_zero. rewrite -> s in H2. intro. apply cpoly_const_eq.
  destruct m.
   generalize (nth_coeff_wd _ 0 _ _ H2); destruct H3 as [d s0].
   rewrite -> nth_coeff_c_mult_p, H0, mult_one, (nth_coeff_wd _ _ _ _ (s0 H1)). intro tmp; apply tmp.
   generalize (nth_coeff_wd _ (S m) _ _ H2); destruct H3 as [d s0].
  rewrite -> nth_coeff_c_mult_p, H0, mult_one, (d m H1 (S m)).  intro; assumption. apply le_n.
  intros.
 induction a as [ | a s ] using cpoly_induc; [ reflexivity | ].
 apply _linear_eq_zero.
 revert H2. rewrite -> cpoly_lin, ring_distl_unfolded. intro H2.
 cut (a [=] [0]); [ intro aeqz; split; [ | apply aeqz ] | ].
  assert (s [=] nth_coeff m (_C_ s[*]b[+]_X_[*]a[*]b)).
   destruct H0; rewrite -> nth_coeff_plus, nth_coeff_c_mult_p, H0.
   rewrite -> (nth_coeff_wd _ _ _ [0]); [ simpl; ring | ].
   rewrite -> aeqz; ring.
  rewrite -> H3.
  rewrite -> (nth_coeff_wd _ _ _ _ H2).
  destruct H1 as [d s0].
  destruct H0 as [H0 H1].
  destruct m; [ rewrite -> (nth_coeff_wd _ _ _ _ (s0 H1)); reflexivity | apply (d m H1); apply le_n ].
 apply (IHn (S m) _ ([0] [+X*] b) (c [-] _C_ s [*] b)); [ | | | rewrite <- H2, cpoly_lin, <- c_zero; unfold cg_minus; ring ].
   unfold degree_le; intros; rewrite <- (coeff_Sm_lin _ _ s).
   apply H; apply lt_n_S; apply H3.
  split; [ rewrite -> coeff_Sm_lin; destruct H0; apply H0 | unfold degree_le; intros ].
  destruct m0; [ inversion H3 | simpl; destruct H0 ].
  apply H4; apply lt_S_n; apply H3.
 unfold degree_lt_pair.
 split; intros.
  unfold degree_le; intros.
  rewrite -> nth_coeff_minus, nth_coeff_c_mult_p, (degree_le_cpoly_linear _ _ _ _ H3); [ | apply H4 ].
  rewrite -> cring_mult_zero, cg_inv_zero; destruct H1 as [d s0].
  destruct m; [ destruct H0; apply (nth_coeff_wd _ _ _ _ (s0 H1)) | ].
  apply (d n0); [ | apply H4 ].
  apply (degree_le_mon _ _ n0); [ apply le_S; apply le_n | apply (degree_le_cpoly_linear _ _ _ _ H3) ].
 destruct (degree_le_zero _ _ H3) as [x s0]. revert s0. rewrite -> cpoly_C_. intro s0.
 destruct (linear_eq_linear_ _ _ _ _ _ s0) as [H4 H5].
 rewrite <- H2, -> H5. unfold cg_minus. ring.
Qed.

Lemma cpoly_div : forall (f g : cpoly_cring CR) (n : nat), monic n g ->
  ex_unq (fun (qr : ProdCSetoid (cpoly_cring CR) (cpoly_cring CR)) => f[=](fst qr)[*]g[+](snd qr) and degree_lt_pair (snd qr) g).
Proof.
 intros f g n H; destruct n.
  destruct H; destruct (degree_le_zero _ _ H0).
  rewrite -> (nth_coeff_wd _ _ _ _ s) in H. simpl in H; rewrite -> H in s.
  exists (f,[0]).
   intros; destruct y; simpl (snd (s0, s1)) in *; simpl (fst (s0, s1)) in *.
   rename H1 into X. destruct X; destruct d; split; [ | symmetry; apply (s3 H0) ].
   rewrite -> s2, (s3 H0), s, <- c_one; ring.
  simpl (fst (f, [0] : cpoly_cring CR)); simpl (snd (f, [0] : cpoly_cring CR)).
  replace (cpoly_zero CR) with ([0] : cpoly_cring CR) by (simpl;reflexivity).
  split; [ rewrite -> s, <- c_one; ring | ].
  split; [ | reflexivity ].
  unfold degree_le; intros; apply nth_coeff_zero.
 destruct (@cpoly_div1 (Nat.max (lth_of_poly f) n) n f g); [ | destruct H; assumption | apply le_max_r | ].
  apply (@degree_le_mon _ _ (lth_of_poly f)); [ apply le_max_l | apply poly_degree_lth ].
 destruct H; destruct x as [q r].
 rewrite -> H, one_nexp, mult_one in y.
 assert (f[=]q[*]g[+]r and degree_lt_pair r g).
  split; [ assumption | ].
  split.
   intros; unfold degree_le; intros; apply y0; apply Nat.le_lt_trans with n0; [ | assumption ].
   unfold degree_le in H1; apply not_gt; intro; unfold gt in H3.
   set (tmp := (H1 (S n) (lt_n_S _ _ H3))); rewrite -> H in tmp.
   apply (eq_imp_not_ap _ _ _ tmp); apply ring_non_triv.
  intro; unfold degree_le in H1; rewrite -> H1 in H; [ | apply Nat.lt_0_succ ].
  destruct (eq_imp_not_ap _ _ _ H); apply ap_symmetric; apply ring_non_triv.
 exists (q,r); [ | assumption ].
 intros y1 X0; destruct y1 as [q1 r1]; simpl (fst (q1, r1)); simpl (snd (q1, r1)) in X0.
 rename H1 into X. destruct X; destruct X0; rewrite -> s in s0; assert (q [=] q1).
  apply cg_inv_unique_2.
  apply (@cpoly_div2 (lth_of_poly (q [-] q1)) (S n) (q [-] q1) g (r1 [-] r)); [ apply poly_degree_lth | split; assumption | | ].
   destruct d; destruct d0; split.
    intros; apply degree_le_minus; [ apply d0 | apply d ]; assumption.
   intro; rewrite -> (s1 H1) ,(s2 H1); unfold cg_minus; ring.
  assert (r1[=]q1[*]g[+]r1[-]q1[*]g); [ unfold cg_minus; ring | ].
  rewrite -> H1, <- s0; unfold cg_minus; ring.
 split; [ assumption | ].
 rewrite -> H1 in s0; apply (cg_cancel_lft _ _ _ _ s0).
Qed.

End poly_eucl.
