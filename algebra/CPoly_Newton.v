
Require Import
 Unicode.Utf8
 Setoid Arith List Program Permutation
 CSetoids CPoly_ApZero CRings CPoly_Degree
 CRArith Qmetric Qring CReals
 stdlib_omissions.Pair stdlib_omissions.Q
 list_separates SetoidPermutation.
Require ne_list.
Import ne_list.notations.

Require CPoly_Lagrange.
Import CPoly_Lagrange.notations.

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

  Lemma interpolates (qpoints: ne_list QPoint):
    QNoDup (map fst qpoints) →
    interpolates (map (first inject_Q) qpoints) (N qpoints).
  Proof with simpl; auto.
   unfold interpolates.
   intros H xy H0.
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
   assert (QNoDup (map fst (y :: qpoints))).
    inversion_clear H...
   rewrite (H0 y H2 x0 y0).
    rewrite an_applied_0...
     change ('0 + y0 == y0). ring.
    destruct H1. subst...
    right...
    apply (in_map fst qpoints (x0, y0))...
   destruct H1...
  Qed. (* Todo: Clean up more. *)

  (** Uniqueness of interpolating polynomials of minimal degree now gives us
   that this Newton polynomial is equal to the Lagrange polynomial. *)

  Lemma coincides_with_Lagrange (l: ne_list QPoint): QNoDup (map fst l) ->
    N l [=] lagrange_poly l.
  Proof with auto.
   intros. Locate interpolation_unique.
   apply (@interpolation_unique CRasCField (ne_list.map (first inject_Q) l)).
       rewrite ne_list.list_map.
       rewrite map_fst_map_first.
       apply CNoDup_map.
       apply CNoDup_weak with Qap...
        intros.
        apply Qap_CRap...
       apply QNoDup_CNoDup_Qap...
      rewrite ne_list.list_map.
      rewrite tl_map.
      rewrite map_length.
      apply degree.
     rewrite ne_list.list_map.
     apply interpolates...
    rewrite ne_list.list_map.
    rewrite tl_map.
    rewrite map_length.
    apply CPoly_Lagrange.degree...
   rewrite ne_list.list_map.
   apply CPoly_Lagrange.interpolates...
  Qed.

End contents.
