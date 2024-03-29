Require Import CoRN.model.totalorder.QposMinMax.
Require Import
 Unicode.Utf8
 Setoid Arith List Program Permutation metric2.Classified
 CSetoids CPoly_ApZero CPoly_Degree
 CRArith CRArith_alg Qmetric Qring CReals Ranges
 stdlib_omissions.Pair stdlib_omissions.Q
 list_separates SetoidPermutation CRings.
Require MathClasses.implementations.ne_list.
Import CRing_Homomorphisms.coercions.
Import ne_list.notations ne_list.coercions.


Coercion Vector.to_list: Vector.t >-> list.

Local Open Scope CR_scope.

Local Notation Σ := cm_Sum.
Local Notation Π := cr_Product.

Section continuous_vector_operations.

  Context `{MetricSpaceClass X} (n: nat).

  Definition uncurry_Vector_cons: X * Vector.t X n → Vector.t X (S n)
    := λ p, Vector.cons _ (fst p) _ (snd p).

  Global Instance Vector_cons_mu: UniformlyContinuous_mu uncurry_Vector_cons := { uc_mu := Qpos2QposInf }.

End continuous_vector_operations.


Section contents.

  Notation QPoint := (Q * CR)%type.
  Notation CRPoint := (CR * CR)%type.

  (** Definition of the Newton polynomial: *)

  Fixpoint divdiff_l (a: QPoint) (xs: list QPoint) {struct xs} : CR :=
    match xs with
    | nil => snd a
    | cons b l => (divdiff_l a l - divdiff_l b l) * ' / (fst a - fst b)
    end.

  Definition divdiff (l: ne_list QPoint): CR := divdiff_l (ne_list.head l) (ne_list.tail l).

  Lemma divdiff_e (l: ne_list QPoint):
    divdiff l = 
      match l with
      | ne_list.one a => snd a
      | a ::: ne_list.one b => (snd a - snd b) * ' / (fst a - fst b)
      | a ::: b ::: l =>
         (divdiff (ne_list.cons a l) - divdiff (ne_list.cons b l)) * ' / (fst a - fst b)
      end.
  Proof. induction l as [|?[|]]; auto. Qed.

  Definition divdiff_ind {T} (P: ne_list T → Prop)
    (Pone: ∀ p, P (ne_list.one p))
    (Ptwo: ∀ p q, P (p ::: ne_list.one q))
    (Pmore: ∀ a b l, P (a ::: l) → P (b ::: l) → P (a ::: b ::: l)):
    forall l, P l.
  Proof with simpl; auto.
   cut (forall t h, P (ne_list.from_list h t)).
    intros. rewrite (ne_list.decomp_eq l)...
   induction t...
   destruct t; simpl...
   intros. apply Pmore; apply IHt.
  Qed.

  Opaque CR.

  Lemma divdiff_sum (xs: ne_list (Q * (CR * CR))):
    divdiff (ne_list.map (second fst) xs) + divdiff (ne_list.map (second snd) xs) ==
    divdiff (ne_list.map (second (λ x: CR * CR, fst x + snd x)) xs).
  Proof with auto.
   induction xs using divdiff_ind; do 3 rewrite divdiff_e; simpl in *.
     reflexivity.
    generalize (' (/ (fst p - fst q))). intro. simpl. ring.
   generalize (' (/ (fst a - fst b))).  intro. simpl.
   rewrite <- IHxs, <- IHxs0.
   simpl. ring.
  Qed.

  Lemma divdiff_scalar_mult (c: CR) (xs: ne_list QPoint):
    c * divdiff xs == divdiff (ne_list.map (second (CRmult c)) xs).
  Proof with auto.
   induction xs using divdiff_ind; simpl.
     reflexivity.
    change ((c * ((snd p - snd q) * ' (/ (fst p - fst q)))) == (c * snd p - c * snd q) * ' (/ (fst p - fst q))).
    set (/ (fst p - fst q)). ring.
   rewrite divdiff_e.
   set (' (/ (fst a - fst b))).
   transitivity ((c * divdiff (a ::: xs) - c * divdiff (b ::: xs)) * m). ring.
   rewrite IHxs, IHxs0.
   symmetry. rewrite divdiff_e.
   simpl. fold m. ring.
  Qed.

  Lemma divdiff_product (xs: ne_list (Q * (CR * CR))):
      divdiff (ne_list.map (second (λ x: CR * CR, fst x * snd x)) xs) ==
      @cm_Sum CRasCMonoid (map (λ p, divdiff (ne_list.map (second fst) (fst p)) * divdiff (ne_list.map (second snd) (snd p)))
        (zip (ne_list.tails xs) (ne_list.inits xs))).
  Proof with simpl in *; auto.
   intros.
   induction xs using divdiff_ind.
     unfold divdiff... ring.
    unfold divdiff... set (' (/ (fst p - fst q))). ring.
   rewrite divdiff_e.
   set (λ p : ne_list (Q and CR and CR) and ne_list (Q and CR and CR),
       divdiff (ne_list.map (second fst) (fst p)) * divdiff (ne_list.map (second snd) (snd p))) as s in *.
   simpl in *.
   rewrite IHxs, IHxs0.
   repeat rewrite ne_list.list_map.
   repeat rewrite zip_map_snd.
   repeat rewrite map_map_comp.
   generalize (zip (ne_list.tails xs) (ne_list.inits xs)). intro.
   set (s0 := ' (/ (fst a - fst b))).
   transitivity ((s (a ::: xs, ne_list.one a) - s (b ::: xs, ne_list.one b)) * s0 +
     (@Σ CRasCMonoid (map (s ∘ second (ne_list.cons a))%prg l) - @Σ CRasCMonoid (map (s ∘ second (ne_list.cons b))%prg l)) * s0)...
    ring.
   setoid_replace ((s (a ::: xs, ne_list.one a) - s (b ::: xs, ne_list.one b)) * s0)
     with (s (a ::: b ::: xs, ne_list.one a) + (s (b ::: xs, a ::: ne_list.one b))).
    setoid_replace ((@Σ CRasCMonoid (map (s ∘ second (ne_list.cons a))%prg l) - @Σ CRasCMonoid (map (s ∘ second (ne_list.cons b))%prg l)) * s0)
      with (@Σ CRasCMonoid (map (s ∘ second (ne_list.cons a) ∘ second (ne_list.cons b))%prg l))...
     ring.
    induction l... ring.
    rewrite <- IHl.
    unfold Basics.compose at 1 3 5 6...
    subst s...
    rewrite (divdiff_e (second snd a ::: second snd b ::: ne_list.map (second snd) (snd a0)))...
    fold s0. ring.
   subst s...
   unfold divdiff at 2 4 6...
   rewrite (divdiff_e (second fst a ::: second fst b ::: ne_list.map (second fst) xs)).
   generalize (divdiff (second fst a ::: ne_list.map (second fst) xs)). intro.
   generalize (divdiff (second fst b ::: ne_list.map (second fst) xs)). intro.
   rewrite divdiff_e...
   fold s0. ring.
  Qed.

  Lemma divdiff_chain (f : Q ->CR) (x y u v: Q): 
   let l:=(x,u):::ne_list.one (y,v) in
   let sndl:=(ne_list.map snd l) in
   ¬(u-v == 0)%Q ->
   (divdiff (ne_list.map (second f ) l)) == 
   (divdiff (ne_zip sndl (ne_list.map f sndl))) * (divdiff (ne_list.map (second inject_Q_CR) l)).
  Proof with auto;simpl.
  intros. do 3 rewrite divdiff_e...
  (* want a combination of ring and a rewrite database for inject_Q ? *)  
  set (s:=f u - f v). set (t:='(/ (x - y))). 
  rewrite CRminus_Qminus. set (a:=(u-v)%Q).
  transitivity (s * ' (/ (a) * (a))%Q * t).
  rewrite <- (Qmult_comm a).
  rewrite Qmult_inv_r... ring.
  rewrite <- (@CRmult_Qmult (/a) a). set (' (/a)). ring.
  Qed.

  Let an (xs: ne_list QPoint): cpoly CRasCRing :=
    (polyconst CRasCRing (divdiff xs))
      [*] Π (map (fun x => @cpoly_linear_fun' CRasCRing (' (- fst x)%Q) [1]) (tl xs)).

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
      replace (length (tl xs))
        with (length (map (fun x => @cpoly_linear_fun' CRasCRing (' (-fst x)%Q) [1]) (tl xs)) * 1)%nat.
      apply degree_le_Product.
      intros.
      apply in_map_iff in H.
      destruct H.
      destruct H.
      rewrite <- H.
      apply degree_le_cpoly_linear_inv.
      apply (degree_le_c_ CRasCRing [1]).
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

    Definition an_applied (x: Q) (txs: ne_list QPoint) : CR
      := divdiff txs * ' @cr_Product Q_as_CRing (map (Qminus x ∘ fst)%prg (tail txs)).

    Definition applied (x: Q) := @Σ CRasCMonoid (map (an_applied x) (ne_list.tails qpoints)).

    Lemma apply x: (N ! ' x) [=] applied x.
    Proof.
     unfold N, applied, an, an_applied.
     rewrite cm_Sum_apply, map_map.
     apply (@cm_Sum_eq CRasCMonoid).
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
     change ((' (- fst x1)%Q + ' x * (1 + ' x * 0)) == (' x - ' fst x1)).
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
    In x (map fst xs) -> an_applied x (t ::: xs) == 0.
  Proof with auto.
   intros. unfold an_applied.
   simpl @tl.
   rewrite (@cr_Product_0 Q_as_CRing (x - x))%Q.
     change (divdiff (t ::: xs) * 0 == 0).
     apply (cring_mult_zero CRasCRing).
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
   cut (an_applied (fst x) (x ::: y ::: xs) + (an_applied (fst x) (y ::: xs)) == an_applied (fst x) (x ::: xs)).
    intro H. rewrite <- H.
    change (an_applied (fst x) (x ::: y ::: xs) + (an_applied (fst x) (y ::: xs) + applied xs (fst x)) ==
      an_applied (fst x) (x ::: y ::: xs)+an_applied (fst x) (y ::: xs) + applied xs (fst x))%CR.
    ring.
   change ((divdiff_l x xs - divdiff_l y xs) * ' (/ (fst x - fst y)) * 
     ' (Qminus (fst x) (fst y) * @cr_Product Q_as_CRing (map (Qminus (fst x) ∘ fst)%prg xs))%Q+
     divdiff_l y xs * ' @cr_Product Q_as_CRing (map (Qminus (fst x) ∘ fst)%prg xs) ==
     divdiff_l x xs * ' @cr_Product Q_as_CRing (map (Qminus (fst x) ∘ fst)%prg xs)).
   generalize (@cr_Product Q_as_CRing (map (Qminus (fst x) ∘ fst)%prg xs)).
   intros.
   rewrite CRmult_assoc.
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

    Let crpoints := ne_list.map (first inject_Q_CR) qpoints.

    Lemma interpolates: @interpolates CRasCField crpoints (N qpoints).
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
       intros u v [? | []]. subst x. change (v * 1 + 0 == v)%CR. ring.
      intros.
      rewrite applied_cons.
      change (((snd x - snd y) * ' (/ (fst x - fst y)) * ' ((x0 - fst y) * 1)%Q + (snd y * 1 + 0)) == y0)%CR.
      rewrite Qmult_1_r.
      destruct B.
       subst.
       rewrite CRmult_assoc.
       change ((y0 - snd y)*(' (/ (x0 - fst y))* '(x0 - fst y)%Q) + (snd y * 1 + 0)==y0)%CR.
       rewrite CRmult_Qmult.
       setoid_replace  (/ (x0 - fst y) * (x0 - fst y))%Q with 1%Q. ring.
       simpl. field. intro.
       apply -> Q.Qminus_eq in H0.
       inversion_clear H.
       apply H1.
       simpl.
       left.
       apply Q.Proper_instance_0. (* For some reason using [rewrite] here is crazy slow. Todo: Investigate. *)
       symmetry.
       assumption.
      destruct H0.
       subst.
       simpl @fst. simpl @snd.
       rewrite (proj2 (Q.Qminus_eq x0 x0)).
        rewrite (cring_mult_zero CRasCRing).
        change (0 + (y0 * 1 + 0) == y0)%CR. ring.
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
      intro. inversion_clear H. apply H2. simpl in H1. rewrite H1...
     rewrite applied_cons.
     assert (QNoDup (map fst (y :: l))).
      inversion_clear H...
     rewrite (H0 y H2 x0 y0).
      rewrite an_applied_0...
       change (0 + y0 == y0). ring.
      destruct H1. subst...
      right...
      apply (in_map fst l (x0, y0))...
     destruct H1...
    Qed. (* Todo: Clean up more. *)

    Lemma interpolates_economically: @interpolates_economically CRasCField crpoints (N qpoints).
    Proof.
     split. apply interpolates.
     unfold crpoints.
     rewrite ne_list.list_map, tl_map, map_length.
     apply degree.
    Qed.

    (** Uniqueness of interpolating polynomials of minimal degree now lets us
     prove some things about any such polynomial based on what we know about
     this Newton polynomial: *)

    Lemma coincides_with_polynomial_interpolators (p: cpoly CRasCRing):
      @CPoly_ApZero.interpolates_economically CRasCField crpoints p →
      N qpoints [=] p.
    Proof with auto.
     apply (@interpolation_unique CRasCField crpoints).
      unfold crpoints. rewrite ne_list.list_map, map_fst_map_first.
      apply (CNoDup_map _ inject_Q_CR).
      apply CNoDup_weak with Qap...
       intros. apply Qap_CRap...
      apply QNoDup_CNoDup_Qap...
     apply interpolates_economically.
    Qed.

    Lemma N_leading_coefficient: nth_coeff (length (tl qpoints)) (N qpoints) == divdiff qpoints.
    Proof with try ring.
     destruct qpoints.
      change (divdiff (ne_list.one p) * 1 + 0 == divdiff (ne_list.one p))...
     simpl @length.
     rewrite N_cons.
     rewrite nth_coeff_plus.
     rewrite (degree l (length l)).
      2: destruct l; simpl; auto.
     change (nth_coeff (length l) (an (p ::: l))+0==divdiff (p ::: l)). (* to change [+] into + *)
     ring_simplify.
     unfold an.
     rewrite nth_coeff_c_mult_p.
     simpl tl.
     set (f := fun x: Q and CR => @cpoly_linear_fun' CRasCRing (' (- fst x)%Q) [1]).
     replace (length l) with (length (map f l) * 1)%nat.
      rewrite lead_coeff_product_1.
       change (divdiff (p ::: l)*1 == divdiff (p ::: l))... (* to change [*] into * *)
      intros q. rewrite in_map_iff. intros [x [[] B]].
      split. reflexivity.
      apply degree_le_cpoly_linear_inv.
      apply (degree_le_c_ CRasCRing [1]).
     rewrite map_length...
    Qed.

    (** So now we know that the divided difference is the leading coefficient of /any/
    economically interpolating polynomial: *)

    Lemma leading_coefficient (p: cpoly CRasCRing):
      @CPoly_ApZero.interpolates_economically CRasCField crpoints p →
      nth_coeff (length (tl qpoints)) p == divdiff qpoints.
    Proof with auto.
     intros.
     rewrite <- coincides_with_polynomial_interpolators...
     apply N_leading_coefficient.
    Qed.

  End again_with_qpoints.

Fixpoint ne_list_zip {X Y} (xs: ne_list X) (ys: ne_list Y): ne_list (X * Y) :=
  match xs, ys with
  | ne_list.cons x xs', ne_list.cons y ys' => ne_list.cons (x, y) (ne_list_zip xs' ys')
  | _, _ => ne_list.one (ne_list.head xs, ne_list.head ys)
  end.

Definition Q01 := sig (λ x: Q, 0 <= x <= 1).
Definition Range (T: Type) := prod T T.
Class Container (Elem C: Type) := In: C → Elem → Prop.
Hint Unfold In.
Notation "x ∈ y" := (In y x) (at level 40).
Notation "(∈ y )" := (In y) (at level 40).
Notation "x ∉ y" := (In y x → False) (at level 40).
Instance in_QRange: Container Q (Range Q) := λ r x, fst r <= x <= snd r. 
Arguments proj1_sig {A P}.
Program Instance in_sig_QRange (P: Q → Prop): Container (sig P) (Range (sig P)) := λ r x, fst r <= x <= snd r. 
Definition B01: Ball Q Qpos := (1#2, (1#2)%Qpos).
  Section divdiff_as_repeated_integral.

    Context
      (n: nat) (points: Vector.t Q (S n))
      (lo hi: Q).

    Definition lohi (q: Q): Prop := lo <= q <= hi.
    Definition Qbp: Type := sig lohi.

(*    Context 
      (points_lohi: Vector.Forall lohi points)
      (upper: CR)
      (nth_deriv: Q → CR (*sig (λ x: CR, x <= upper)*))
        `{!UniformlyContinuous_mu nth_deriv}
        `{!UniformlyContinuous nth_deriv}
          (* Todo: This should be replaced with some "n times differentiable" requirement on a subject function. *)
      (integrate: Range Q01 * UCFunction Q01 CR → CR)
        `{!UniformlyContinuous_mu integrate}
        `{!UniformlyContinuous integrate}.
          (* Todo: The integration function should not be a parameter. We should just use SimpleIntegration's implementation. *)
*)
(*
Require Import CRabs.
Import QnonNeg.notations.
Definition ZeroRangeToBall (q: QnonNeg.T): Ball Q QnonNeg.T := (0, ((1#2) * q)%Qnn).
    Variable integrate_on_01:
      ∀ (u: QnonNeg.T) (f: sig (contains (ZeroRangeToBall u)) → CR) c,
        (∀ x, CRabs (f x) <= c) →
        CRabs (integrate _ f) <= c.
*)
    Opaque Qmult Qplus Qminus.
       (* Without these, instance resolution gets a little too enthusiastic and breaks these operations open when
       looking for PointFree instances below. It's actually kinda neat that it can put these in PointFree form though. *)


    Notation SomeWeights n := ((*sig (λ ts:*) Vector.t Q01 n (*, cm_Sum (map proj1_sig ts) <= 1)%Q*)).
    Notation Weights := ((*sig (λ ts:*) Vector.t Q01 (S n) (*, cm_Sum (map proj1_sig ts) == 1)%Q*)).

    (** apply_weights: *)

    Obligation Tactic := idtac.

    (** "inner", the function of n weights: *)
    (* Next up is "reduce", which *)
  End divdiff_as_repeated_integral.

End contents.
