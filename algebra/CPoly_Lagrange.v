Require Import
 Unicode.Utf8
 Setoid Arith List Program Permutation
 CSetoids CRings CPoly_Degree CPoly_ApZero
 CRArith Qmetric Qring CReals
 stdlib_omissions.Pair stdlib_omissions.Q
 list_separates SetoidPermutation.
Require ne_list.
Import ne_list.notations.

Open Local Scope CR_scope.

Local Notation Σ := cm_Sum.
Local Notation Π := cr_Product.

Section contents.

  Notation QPoint := (Q * CR)%type.
  Notation CRPoint := (CR * CR)%type.

  Variables
    (qpoints: list QPoint)
    (distinct: QNoDup (map fst qpoints)).

  Let crpoints := map (first inject_Q_CR) qpoints.

  (** Definition of the Lagrange polynomial: *)

  Definition L: cpoly CRasCRing :=
    Σ (map (fun p => let '((x, y), rest) := p in
      _C_ y [*] Π (map (fun xy' => (' (- fst xy')%Q [+X*] [1]) [*] _C_ (' (/ (x - fst xy')))) rest))
     (separates qpoints)).

  (** Its degree follows easily from its structure: *)

  Lemma degree: degree_le (length (tl qpoints)) L.
  Proof with auto.
   unfold L.
   apply degree_le_Sum. intros ? H.
   destruct (proj1 (in_map_iff _ _ _) H) as [[[] v] [[] B]]. clear H.
   apply degree_le_mult_constant_l.
   clear crpoints.
   destruct qpoints.
    simpl in B.
    exfalso...
   simpl length.
   replace (@length (prod Q (RegularFunction Q_as_MetricSpace)) l) 
    with (length (map (fun xi => (' (- fst xi)%Q[+X*][1])[*]_C_ (' (/ (q - fst xi)))) v) * 1)%nat.
    apply degree_le_Product.
    intros.
    destruct (proj1 (in_map_iff _ _ _) H) as [?[[]?]].
    apply degree_le_mult_constant_r.
    apply degree_le_cpoly_linear_inv.
    apply (degree_le_c_ CRasCRing [1]).
   rewrite map_length.
   ring_simplify.
   apply eq_add_S.
   rewrite <- (separates_elem_lengths (p0 :: l) v)...
   replace v with (snd ((q, s), v))...
   apply in_map...
  Qed.

  (** Applying the polynomial gives what you'd expect: *)

  Definition functional (x: Q): CR :=
    Σ (map (fun p => let '((xj, y), rest) := p in y [*] ' Π (map (fun xi => (x - fst xi) * / (xj - fst xi))%Q rest))
     (separates qpoints)).

  Lemma apply x: (L ! ' x) [=] functional x.
  Proof.
   unfold L, functional.
   rewrite cm_Sum_apply.
   autorewrite with apply.
   rewrite map_map.
   apply (@cm_Sum_eq _). intros [[u v] w].
   autorewrite with apply.
   apply mult_wd. reflexivity.
   rewrite inject_Q_product.
   rewrite cr_Product_apply.
   do 2 rewrite map_map.
   apply (@cm_Sum_eq (Build_multCMonoid CRasCRing)).
   intros [p q].
   rewrite <- CRmult_Qmult.
   autorewrite with apply.
   change (((' (- p)%Q + ' x * (1 + ' x * 0)) * ' (/ (u - p))) == (' (x + - p)%Q * ' (/ (u - p))))%CR.
   rewrite <- CRplus_Qplus.
   generalize (/ (u - p)).
   intros. ring.
  Qed.

  (** Finally, the polynomial actually interpolates the given points: *)

  Lemma interpolates: interpolates crpoints L.
  Proof with auto.
   intros xy.
   unfold crpoints. rewrite in_map_iff.
   intros [[xi y] [V W]].
   subst. simpl @fst. simpl @snd.
   rewrite apply. unfold functional.
   destruct (move_to_front _ _ W) as [x H1].
   set (fun p => let '(xj, y1, rest) := p in y1[*] ' Π (map (fun xi0 : Q and CR => ((xi - fst xi0) * / (xj - fst xi0))%Q) rest)).
   assert ((pair_rel eq (@Permutation _) ==> @st_eq _) s s) as H2.
    intros [u w] [[p q]] [A B].
    simpl in A, B. subst u. cbv beta iota.
    apply mult_wd. reflexivity.
    apply inject_Q_CR_wd.
    rewrite B. reflexivity.
   pose proof (separates_Proper _ _ H1) as H3.
   assert (@Equivalence ((Q * CR) * list (Q * CR)) (pair_rel (@eq _) (@Permutation _))) as T.
    apply Pair.Equivalence_instance_0.
     apply _.
    apply _.
   (* I'm really clueless why this rewrite has ever worked? *)
   etransitivity. apply cm_Sum_Proper. apply cag_commutes. symmetry.
   apply (@map_perm_proper _ CR (pair_rel eq (@Permutation _)) (@st_eq _) T _ _ _ H2 _ _ H3).
   clear H2 H3.
   subst s.
   simpl @cm_Sum.
   rewrite cm_Sum_units.
    setoid_replace (' Π (map (fun xi0 : Q and CR => ((xi - fst xi0) * / (xi - fst xi0))%Q) x)) with 1%CR.
     change (y * 1 + 0 == y). ring.
    apply inject_Q_CR_wd.
    rewrite cr_Product_ones. reflexivity.
    intros.
    destruct (proj1 (in_map_iff _ _ _) H) as [x1 [[] H4]].
    simpl.
    apply Qmult_inv_r.
    unfold QNoDup in distinct.
    revert distinct.
    apply Permutation_sym in H1. (* only needed to work around evar anomaly *)
    rewrite H1.
    intros H3 H5.
    simpl in H3.
    inversion_clear H3.
    apply H0.
    apply in_map_iff.
    exists (fst x1).
    split...
     apply Qred_complete.
     symmetry...
     apply -> Qminus_eq...
    apply in_map... 
   intros.
   destruct (proj1 (in_map_iff _ _ _) H) as [[[v w] u] [[] H4]]. clear H.
   destruct (proj1 (in_map_iff _ _ _) H4) as [[[n m] k] [A B]].
   inversion_clear A.
   simpl @cr_Product.
   setoid_replace (xi - xi)%Q with 0%Q by (simpl; ring).
   repeat rewrite Qmult_0_l.
   change ((w: CR) * 0 == 0).
   ring.
  Qed. (* Todo: Clean up more. *)

End contents.

Lemma interpolates_economically (qpoints: ne_list (Q * CR)): QNoDup (map fst qpoints) →
  interpolates_economically (ne_list.map (first inject_Q_CR) qpoints) (L qpoints).
Proof with auto.
 split.
  rewrite ne_list.list_map.
  apply interpolates...
 rewrite ne_list.list_map.
 rewrite tl_map.
 rewrite map_length.
 apply degree...
Qed.

Module notations.

  Notation lagrange_poly := L.

End notations.
