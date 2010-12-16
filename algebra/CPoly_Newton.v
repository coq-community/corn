
Require Import
 Unicode.Utf8
 Setoid Arith List Program Permutation
 CSetoids CPoly_ApZero CRings CPoly_Degree
 CRArith Qmetric Qring CReals
 stdlib_omissions.Pair stdlib_omissions.Q
 list_separates SetoidPermutation.
Require ne_list.
Import ne_list.notations.

Set Automatic Introduction.

Open Local Scope CR_scope.

Local Notation Σ := cm_Sum.
Local Notation Π := cr_Product.

Section contents.

  Notation QPoint := (Q * CR)%type.
  Notation CRPoint := (CR * CR)%type.

  (** Definition of the Newton polynomial: *)

  Fixpoint divdiff_l (a: QPoint) (xs: list QPoint): CR :=
    match xs with
    | nil => snd a
    | cons b l => (divdiff_l a l - divdiff_l b l) * ' / (fst a - fst b)
    end.

  Definition divdiff (l: ne_list QPoint): CR := divdiff_l (ne_list.head l) (ne_list.tail l).

  Let an (xs: ne_list QPoint): cpoly CRasCRing :=
    _C_ (divdiff xs) [*] Π (map (fun x => ' (- fst x) [+X*] One) (tl xs)).

  Section with_qpoints.

    Variable qpoints: ne_list QPoint.

    Definition N: cpoly CRasCRing := Σ (map an (ne_list.tails qpoints)).

    (** Degree: *)

    Let an_degree (xs: ne_list QPoint): degree_le (length (tl xs)) (an xs).
    Proof with auto.
     intros.
     unfold an.
     replace (length (tl xs)) with (0 + length (tl xs))%nat by reflexivity.
     apply degree_le_mult.
      apply degree_le_c_.
     replace (length (tl xs)) with (length (map (fun x => ' (-fst x)[+X*]One) (tl xs)) * 1)%nat.
      apply degree_le_Product.
      intros.
      apply in_map_iff in H.
      destruct H.
      destruct H.
      rewrite <- H.
      apply degree_le_cpoly_linear_inv.
      apply (degree_le_c_ CRasCRing One).
     ring_simplify.
     rewrite map_length.
     destruct xs; reflexivity.
    Qed.

    Lemma degree: degree_le (length (tl qpoints)) N.
    Proof with auto.
     intros.
     unfold N.
     apply degree_le_Sum.
     intros.
     apply in_map_iff in H.
     destruct H as [x [H H0]].
     subst p.
     apply degree_le_mon with (length (tl x)).
      pose proof (ne_list.tails_are_shorter qpoints x H0).
      destruct x, qpoints; auto with arith.
     apply an_degree.
    Qed.

    (** Applying this polynomial gives what you'd expect: *)

    Definition an_applied (x: Q) (txs: ne_list QPoint) := divdiff txs [*] ' Π (map (Qminus x ∘ fst) (tail txs)).

    Definition applied (x: Q) := Σ (map (an_applied x) (ne_list.tails qpoints)).

    Lemma apply x: (N ! ' x) [=] applied x.
    Proof.
     unfold N, applied, an, an_applied.
     rewrite cm_Sum_apply map_map.
     apply cm_Sum_eq.
     intro.
     autorewrite with apply.
     apply mult_wd. reflexivity.
     rewrite inject_Q_product.
     rewrite cr_Product_apply.
     do 2 rewrite map_map.
     apply (@cm_Sum_eq (Build_multCMonoid CRasCRing)).
     intro.
     unfold Basics.compose.
     rewrite <- CRminus_Qminus.
     change ((' (- fst x1) + ' x * (' 1 + ' x * ' 0)) [=] (' x - ' fst x1)).
     ring.
    Qed.

  End with_qpoints.

  (** Next, some lemmas leading up to the proof that the polynomial does
   indeed interpolate the given points: *)

  Let applied_cons (y: Q) (x: QPoint) (xs: ne_list QPoint):
    applied (x ::: xs) y = an_applied y (x ::: xs) + applied xs y.
  Proof. reflexivity. Qed.

  Let N_cons (x: QPoint) (xs: ne_list QPoint):
    N (x ::: xs) = an (x ::: xs) [+] N xs.
  Proof. reflexivity. Qed.

  Lemma an_applied_0 (t: QPoint) (x: Q) (xs: ne_list QPoint):
    In x (map fst xs) -> an_applied x (t ::: xs) [=] '0.
  Proof with auto.
   intros. unfold an_applied.
   simpl @tl.
   rewrite (cr_Product_0 (x - x))%Q.
     change (divdiff (t ::: xs) [*] Zero [=] Zero).
     apply cring_mult_zero.
    change (x - x == 0)%Q. ring.
   unfold Basics.compose.
   rewrite <- map_map.
   apply in_map...
  Qed.

  Lemma applied_head (x y: QPoint) (xs: ne_list QPoint):
    Qred (fst x) <> Qred (fst y) ->
    applied (x ::: y ::: xs) (fst x) [=] applied (x ::: xs) (fst x).
  Proof with auto.
   intro E.
   repeat rewrite applied_cons.
   cut (an_applied (fst x) (x ::: y ::: xs) [+] (an_applied (fst x) (y ::: xs)) [=] an_applied (fst x) (x ::: xs)).
    intro H. rewrite <- H.
    change (an_applied (fst x) (x ::: y ::: xs) + (an_applied (fst x) (y ::: xs) + applied xs (fst x)) ==
      an_applied (fst x) (x ::: y ::: xs)+an_applied (fst x) (y ::: xs) + applied xs (fst x))%CR.
    ring.
   change ((divdiff_l x xs - divdiff_l y xs) * ' (/ (fst x - fst y))[*]
     ' (Qminus (fst x) (fst y) * Π (map (Qminus (fst x) ∘ fst) xs))+
     divdiff_l y xs[*]' Π (map (Qminus (fst x) ∘ fst) xs)[=]
     divdiff_l x xs[*]' Π (map (Qminus (fst x) ∘ fst) xs)).
   generalize (Π (map (Qminus (fst x) ∘ fst) xs)).
   intros.
   rewrite <- mult_assoc.
   change ((((divdiff_l x xs - divdiff_l y xs)*(' (/ (fst x - fst y))%Q*' ((fst x - fst y)*s)%Q) + divdiff_l y xs * ' s)) == divdiff_l x xs*' s)%CR.
   rewrite CRmult_Qmult.
   setoid_replace ((/ (fst x - fst y) * ((fst x - fst y) * s)))%Q with s.
    ring.
   rewrite Qmult_assoc.
   change ((/ (fst x - fst y) * (fst x - fst y) * s)==s)%Q.
   field. intro.
   apply -> Q.Qminus_eq in H.
   apply E.
   apply Qred_complete...
  Qed.

  Section again_with_qpoints.

    Variables (qpoints: ne_list QPoint) (H: QNoDup (map fst qpoints)).

    Let crpoints := ne_list.map (first inject_Q) qpoints.

    Lemma interpolates: interpolates crpoints (N qpoints).
    Proof with simpl; auto.
     unfold interpolates.
     unfold crpoints.
     rewrite ne_list.list_map.
     intros xy H0.
     destruct (proj1 (in_map_iff _ _ _) H0) as [[x y] [? B]]. clear H0.
     subst xy.
     unfold first. simpl @fst. simpl @snd.
     rewrite apply.
     revert x y B.
     induction qpoints using ne_list.two_level_rect.
       intros u v [? | []]. subst x. change (v * '1 + '0 == v)%CR. ring.
      intros.
      rewrite applied_cons.
      change (((snd x - snd y) * ' (/ (fst x - fst y)) [*] ' ((x0 - fst y) * 1) + (snd y * ' 1 + ' 0)) == y0)%CR.
      rewrite Qmult_1_r.
      destruct B.
       subst.
       rewrite <- mult_assoc.
       change ((y0 - snd y)*(' (/ (x0 - fst y))*' (x0 - fst y)) + (snd y * ' 1 + ' 0)==y0)%CR.
       rewrite CRmult_Qmult.
       setoid_replace  (/ (x0 - fst y) * (x0 - fst y))%Q with 1%Q. ring.
       simpl. field. intro.
       apply -> Q.Qminus_eq in H0.
       inversion_clear H.
       apply H1.
       rewrite H0...
      destruct H0.
       subst.
       simpl @fst. simpl @snd.
       rewrite (proj2 (Q.Qminus_eq x0 x0)).
        rewrite cring_mult_zero.
        change (' 0 + (y0 * ' 1 + ' 0) == y0)%CR. ring.
       reflexivity.
      exfalso...
     clear qpoints.
     simpl @In.
     intros x0 y0 [H1 | H1].
      subst.
      rewrite applied_head.
       apply H0...
       inversion_clear H.
       unfold QNoDup.  simpl.
       apply NoDup_cons. intuition.
       inversion_clear H2. intuition.
      intro. inversion_clear H. apply H2. rewrite H1...
     rewrite applied_cons.
     assert (QNoDup (map fst (y :: l))).
      inversion_clear H...
     rewrite (H0 y H2 x0 y0).
      rewrite an_applied_0...
       change ('0 + y0 == y0). ring.
      destruct H1. subst...
      right...
      apply (in_map fst l (x0, y0))...
     destruct H1...
    Qed. (* Todo: Clean up more. *)

    Lemma interpolates_economically: interpolates_economically crpoints (N qpoints).
    Proof.
     split. apply interpolates.
     unfold crpoints.
     rewrite ne_list.list_map tl_map map_length.
     apply degree.
    Qed.

    (** Uniqueness of interpolating polynomials of minimal degree now lets us
     prove some things about any such polynomial based on what we know about
     this Newton polynomial: *)

    Lemma coincides_with_polynomial_interpolators (p: cpoly CRasCRing):
      CPoly_ApZero.interpolates_economically crpoints p →
      N qpoints [=] p.
    Proof with auto.
     apply (interpolation_unique crpoints).
      rewrite ne_list.list_map map_fst_map_first.
      apply (CNoDup_map _ inject_Q).
      apply CNoDup_weak with Qap...
       intros. apply Qap_CRap...
      apply QNoDup_CNoDup_Qap...
     apply interpolates_economically.
    Qed.

    Lemma N_leading_coefficient: nth_coeff (length (tl qpoints)) (N qpoints) == divdiff qpoints.
    Proof with try ring.
     destruct qpoints.
      change (divdiff (ne_list.one p) * ' 1 + ' 0[=]divdiff (ne_list.one p))...
     simpl @length.
     rewrite N_cons.
     rewrite nth_coeff_plus.
     rewrite (degree l).
      2: destruct l; simpl; auto.
     change (nth_coeff (length l) (an (p ::: l))+'0==divdiff (p ::: l)). (* to change [+] into + *)
     ring_simplify.
     unfold an.
     rewrite nth_coeff_c_mult_p.
     simpl tl.
     set (f := fun x: Q and CR => ' (- fst x)[+X*]One).
     replace (length l) with (length (map f l) * 1)%nat.
      rewrite lead_coeff_product_1.
       change (divdiff (p ::: l)*' 1[=]divdiff (p ::: l))... (* to change [*] into * *)
      intros q. rewrite in_map_iff. intros [x [[] B]].
      split. reflexivity.
      apply degree_le_cpoly_linear_inv.
      apply (degree_le_c_ CRasCRing One).
     rewrite map_length...
    Qed.

    (** So now we know that the divided difference is the leading coefficient of /any/
    economically interpolating polynomial: *)

    Lemma leading_coefficient (p: cpoly CRasCRing):
      CPoly_ApZero.interpolates_economically crpoints p →
      nth_coeff (length (tl qpoints)) p == divdiff qpoints.
    Proof with auto.
     intros.
     rewrite <- coincides_with_polynomial_interpolators...
     apply N_leading_coefficient.
    Qed.

  End again_with_qpoints.

  Lemma N_Permutation (x y: ne_list QPoint): QNoDup (map fst x) → ne_list.Permutation x y → N x [=] N y.
  Proof with auto.
   intros D E.
   apply (interpolation_unique (ne_list.map (first inject_Q) x)).
     rewrite ne_list.list_map.
     rewrite map_fst_map_first.
     apply (CNoDup_map _ inject_Q).
     apply CNoDup_weak with Qap...
      intros. apply Qap_CRap...
     apply QNoDup_CNoDup_Qap...
    apply interpolates_economically...
   rewrite E.
   apply interpolates_economically.
   unfold QNoDup.
   rewrite <- E...
  Qed.

  Lemma divdiff_Permutation (x y: ne_list QPoint): QNoDup (map fst x) →
   ne_list.Permutation x y →
   divdiff x [=] divdiff y.
    (* Bah, can't express this as a Proper because of the NoDup requirement and the inability of
     the current setoid rewriting infrastructure to deal with dependently typed functions. :-( *)
  Proof with auto.
   intros D P.
   rewrite <- N_leading_coefficient...
   rewrite <- N_leading_coefficient...
    rewrite (ne_list.Permutation_ne_tl_length x y)...
    rewrite (N_Permutation x y)...
    reflexivity.
   unfold QNoDup.
   rewrite <- P...
  Qed.

End contents.
