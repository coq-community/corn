(*
Require Import
 Unicode.Utf8
 Setoid Arith List Program Permutation metric2.Classified
 CSetoids CPoly_ApZero CRings CPoly_Degree
 CRArith Qmetric Qring CReals
 stdlib_omissions.Pair stdlib_omissions.Q
 list_separates SetoidPermutation
 util.Container NewAbstractIntegration
 algebra.CPoly_Newton Ranges.

Require ne_list.
Import ne_list.notations.
Opaque CR.

Section contents.

  Notation QPoint := (Q * CR)%type.
  Notation CRPoint := (CR * CR)%type.
  Local Notation Σ := cm_Sum.
Require Import Qabs.


(* Some utility operations and lemmas for ne_list/vector (todo: move these): *)

Definition Vec_to_ne_list {A}: ∀ {n}, Vector.t A (S n) → ne_list A :=
  @Vector.rectS A (fun _ _ => ne_list A) ne_list.one (fun a _ _ x => ne_list.cons a x).

Lemma ne_list_head_map {A B} (f: A → B) (l: ne_list A): ne_list.head (ne_list.map f l) = f (ne_list.head l).
Proof. induction l. reflexivity. simpl. congruence. Qed.

Lemma ne_list_tail_map {A B} (f: A → B) (l: ne_list A): ne_list.tail (ne_list.map f l) = map f (ne_list.tail l).
Proof. destruct l. reflexivity. simpl. induction l. reflexivity. simpl. congruence. Qed.

Lemma ding_vec n A (v: Vector.t A (S n)): v = Vector.cons _ (Vector.hd v) _ (Vector.tl v).
Proof. dependent destruction v. simpl. reflexivity. Qed.

Lemma through_ne A n (v: Vector.t A (S n)):
  ne_list.to_list (Vec_to_ne_list _ v) = v.
Proof with auto.
 induction n.
  dependent destruction v.
  dependent destruction v.
  simpl.
  reflexivity.
 dependent destruction v.
 simpl.
 rewrite IHn.
 reflexivity.
Qed.

Lemma Vec_cons_to_ne_list {A} n (a: A) (v: Vector.t A (S n)): Vec_to_ne_list _ (Vector.cons _ a _ v) = ne_list.cons a (Vec_to_ne_list _ v).
Admitted.

Lemma Vec_cons_to_ne_list' {A} n (v: Vector.t A n): ∀ a, Vec_to_ne_list _ (Vector.cons _ a _ v) = ne_list.from_list a v.
Proof with auto.
 induction n.
  dependent destruction v.
  reflexivity.
 dependent destruction v.
 intros.
 change (Vec_to_ne_list (S n) (Vector.cons A a (S n) (Vector.cons A h n v)) = a ::: ne_list.from_list h v).
 rewrite <- IHn.
 reflexivity.
Qed.

Lemma ne_head_from_list {X} (x: X) (xs: list X): ne_list.head (ne_list.from_list x xs) = x.
Proof. destruct xs; reflexivity. Qed.

Lemma ne_to_from_list {X} (xs: list X): ∀ x, ne_list.to_list (ne_list.from_list x xs) = x :: xs.
Proof. induction xs. reflexivity. simpl. rewrite IHxs. reflexivity. Qed.

Lemma ne_tail_from_list {X} (x: X) (xs: list X): ne_list.tail (ne_list.from_list x xs) = xs.
Proof.
 induction xs.
  reflexivity.
 simpl.
 rewrite ne_to_from_list.
 reflexivity.
Qed.

Lemma ne_list_map_from_list {X Y} (f: X → Y) (xs: list X): ∀ h,
  ne_list.map f (ne_list.from_list h xs) = ne_list.from_list (f h) (map f xs).
Proof. induction xs; simpl; congruence. Qed.




(*
  Section inner_space.
(* Need vector space, norm, inner product, metric from norm, Lipschitz continuity from boundedness *)
  Definition norm `(x: Vector.t Q n):=Σ (map Qabs x).
  
  Definition inner (n:nat)(x y : Vector.t Q n):=Σ(map (λ p, Qmult (fst p) (snd p)) (zip x y)).
  
  End inner_space.*)

  Section divdiff_as_repeated_integral.

    Context 
      (nth_deriv_bound: Range CR)
      (nth_deriv: Q → sig ((∈ nth_deriv_bound)))
        (* Todo: only require boundedness on the interval that contains the points. *)
        `{!UniformlyContinuous_mu nth_deriv}
        `{!UniformlyContinuous nth_deriv}.
          (* Todo: This should be replaced with some "n times differentiable" requirement on a subject function. *)

    Context
      (n: nat) (points: Vector.t Q (S n)).

    Opaque Qmult Qplus Qminus.
       (* Without these, instance resolution gets a little too enthusiastic and breaks these operations open when
       looking for PointFree instances below. It's actually kinda neat that it can put these in PointFree form though. *)


    Definition totalweight {n} (ws: Vector.t Q n): Q := cm_Sum ws.

    Notation SomeWeights n := (sig (λ ts: Vector.t Q n, totalweight ts <= 1)%Q).

    (** apply_weights: *)
    (** Note that this an innerproduct *)
    (** |<points,w>|≤|points| |w|
         |<points,w>-<points,v>|=|<points,w-v>| ≤||points|| ||w-v||
       , the function is Lipshitz  with constant norm ||points||*)
    Definition apply_weights (w: Vector.t Q (S n)): Q :=
      cm_Sum (map (λ p, Qmult (fst p) (snd p)) (zip points (Vector.to_list w))).

    Instance apply_weights_mu: UniformlyContinuous_mu apply_weights.
    constructor. exact (fun x => x).
    Defined.

    Instance apply_weights_uc: UniformlyContinuous apply_weights.
    constructor; try apply _.
    intros ??? H.
    (*Check apply_weights. *)
    Admitted.

    Obligation Tactic := idtac.

    (** "inner", the function of n weights: *)

    Program Definition inner: SomeWeights n → sig ((∈ nth_deriv_bound))
      := λ ts, nth_deriv (apply_weights (Vector.cons _ (1 - totalweight ts) _ ts))%Q.

    Instance inner_mu: UniformlyContinuous_mu inner.
     unfold inner.
     apply compose_mu.
      apply _.
     apply (@compose_mu (SomeWeights n) (Vector.t Q (S n)) Q (apply_weights)).
      apply _.
    Admitted.

    Instance inner_uc: UniformlyContinuous inner.
    Admitted.

    (** Next up is "reduce" *)

    Definition G (n: nat): Type := UCFunction (SomeWeights n) (sig ((∈ nth_deriv_bound))).

Open Local Scope CR_scope.

    Section reduce.

      Variables (m: nat) (X: G (S m)).

      Program Definition integrand (ts: SomeWeights m) (t: sig ((∈ (0, (1 - totalweight ts))))%Q): sig ((∈ nth_deriv_bound)) :=
        X (@uncurry_Vector_cons Q m (` t, ` ts)).

      Next Obligation. intros. change (`t + Σ  (` ts) <= 1)%Q. admit. Qed.

      Instance integrand_mu: ∀ ts, UniformlyContinuous_mu (integrand ts).
       unfold integrand.
       intros.
       apply compose_mu.
        apply _.
       constructor.
       intro.
       apply Qpos2QposInf.
       exact H.
      Defined.

      Instance integrand_uc: ∀ ts, UniformlyContinuous (integrand ts).
      Proof.
       unfold integrand. intros.
       apply compose_uc. apply _.
       constructor; try apply _.
       simpl. intros.
       constructor. assumption.
       simpl.
       admit. (* doable *)
      Qed.

      Program Definition reduce_raw: SomeWeights m → sig ((∈ nth_deriv_bound))
       := λ ts, @integrate_ucFunc_wrapped_for_continuity nth_deriv_bound (existT _ (0, 1 - totalweight  (` ts))%Q
         (ucFunction (integrand ts))).

      Next Obligation.
       intros.
       unfold integrate_ucFunc_wrapped_for_continuity.
       simpl.
      Admitted. (* need to show that the result is bounded *)

      Instance reduce_mu: UniformlyContinuous_mu reduce_raw.
      Proof with auto.
       unfold reduce_raw.
       apply exist_mu.
       set (integrate_ucFunc_wrapped_for_continuity nth_deriv_bound).
       apply (@compose_mu  (SomeWeights m)  {r : Range Q & UCFunction (sig ((∈r))) (sig ((∈nth_deriv_bound)))} CR s).
        apply _.
       admit.
      Defined.

      Instance reduce_uc: UniformlyContinuous reduce_raw.
      Proof with auto.
       unfold reduce_raw.
       apply exist_uc.
       set (integrate_ucFunc_wrapped_for_continuity nth_deriv_bound).
       apply (@compose_uc  (SomeWeights m)  _ _ {r : Range Q & UCFunction (sig ((∈r))) (sig ((∈nth_deriv_bound)))} _ _ CR _ _ s).
        apply _.
       admit.
      Qed.

      Definition reduce: G m := ucFunction reduce_raw.

    End reduce.

    (** Finally, the divided difference arises from iterated reduction of the inner function: *)

    Definition alt_divdiff: CR.
     refine (proj1_sig (iterate reduce (ucFunction inner) _)).
     exists (Vector.nil Q).
     abstract (unfold totalweight; simpl; auto).
    Defined. (* Todo: Why won't Program work here? *)

  End divdiff_as_repeated_integral.

  Section divdiffs_equal.

    Context (f: Q → CR) (nth_deriv_bound: Range CR) (nth_deriv: Q → sig (∈nth_deriv_bound)).

    Lemma divdiffs_equal: ∀ n (xs: Vector.t Q (S n)),
      (divdiff (ne_list.map (λ x, (x, f x)) (Vec_to_ne_list _ xs)) == alt_divdiff nth_deriv_bound nth_deriv _ xs)%CR.
    Proof with auto.
     induction n.
      intros.
      assert (xs = Vector.cons _ (Vector.hd xs) _ (Vector.nil _)) as E.
       do 2 dependent destruction xs.
       reflexivity.
      rewrite E.
      change (f (Vector.hd xs) [=] proj1_sig (nth_deriv (Vector.hd xs * (1 - 0) + 0))).
      admit. (* in this case the nth derivative is f itself *)
     intros.
     simpl in *.
     unfold Basics.compose.
     dependent destruction xs.
     dependent destruction xs.
     rewrite Vec_cons_to_ne_list.
     unfold divdiff.
     rewrite ne_list_head_map.
     rewrite ne_list_tail_map.
     simpl @ne_list.head.
     change (divdiff_l (h, f h) (map (λ x : Q, (x, f x)) (Vec_to_ne_list n (Vector.cons Q h0 n xs)))[=]
       alt_divdiff nth_deriv_bound nth_deriv (S n) (Vector.cons Q h (S n) (Vector.cons Q h0 n xs))).
     rewrite through_ne.
     change (divdiff_l (h, f h) ((h0, f h0) :: map (λ x : Q, (x, f x)) xs)[=]
       alt_divdiff nth_deriv_bound nth_deriv (S n) (Vector.cons Q h (S n) (Vector.cons Q h0 n xs))).
     simpl.
     replace (divdiff_l (h, f h) (map (λ x : Q, (x, f x)) xs)) with (divdiff (ne_list.from_list (h, f h) (map (λ x : Q, (x, f x)) xs))).
      Focus 2.
      unfold divdiff.
      rewrite ne_head_from_list.
      rewrite ne_tail_from_list.
      reflexivity.
     replace (divdiff_l (h0, f h0) (map (λ x : Q, (x, f x)) xs)) with (divdiff (ne_list.from_list (h0, f h0) (map (λ x : Q, (x, f x)) xs))).
      Focus 2.
      unfold divdiff.
      rewrite ne_head_from_list.
      rewrite ne_tail_from_list.
      reflexivity.
     rewrite <- (ne_list_map_from_list (λ x: Q, (x, f x)) xs h).
     rewrite <- (ne_list_map_from_list (λ x: Q, (x, f x)) xs h0).
     rewrite <- Vec_cons_to_ne_list'.
     rewrite <- Vec_cons_to_ne_list'.
     rewrite IHn.
     rewrite IHn.
     clear IHn.
     unfold alt_divdiff.
     (* now it's "just" an equation between repeated integrals *)
     admit.
    Qed.

  End divdiffs_equal.

End contents.
*)
