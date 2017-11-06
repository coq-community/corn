Require Import
 Unicode.Utf8 Program
 CRArith CRabs
 Qminmax Qauto Qround Qmetric
 stdlib_omissions.P
 stdlib_omissions.Z
 stdlib_omissions.Q
 stdlib_omissions.N
 metric2.Classified
 util.Container Ranges
 decision.

Require QnonNeg QnnInf CRball.
Import QnonNeg.notations QnnInf.notations CRball.notations.

Implicit Arguments proj1_sig [[A] [P]].

Local Open Scope Q_scope.
Local Open Scope uc_scope.
Local Open Scope CR_scope.

Hint Immediate ball_refl Qle_refl.

(** Some missing theory about positive: *)

Lemma Pmax_le_l (x y: positive): (x <= Pmax x y)%positive.
Admitted.

Lemma Pmax_le_r (x y: positive): (x <= Pmax y x)%positive.
Admitted.

Hint Immediate Pmax_le_l Pmax_le_r.



(** A few summing/enumming utilities: *)

Program Fixpoint enum' (n: nat): list (sig (ge n)) :=
  match n with
  | O => nil
  | S n' => n' :: map (λ x: sig (ge n'), x) (enum' n')
  end.

Lemma enum_enum' (n: nat): enum n = map (@proj1_sig _ _) (enum' n).
Proof.
 induction n; simpl. reflexivity.
 rewrite IHn, map_map. reflexivity.
Qed.

Lemma length_enum' n: length (enum' n) = n.
Proof with auto with arith.
 induction n...
 simpl. rewrite map_length...
Qed.

Definition cmΣ {M: CMonoid} (n: nat) (f: nat -> M): M := cm_Sum (map f (enum n)).
Definition cmΣ' {M: CMonoid} (n: nat) (f: sig (ge n) → M): M := cm_Sum (map f (enum' n)).

Opaque CR.

Lemma cm_Sum_constant (c: CR) (l: list CR): (forall x, List.In x l → x == c) → cm_Sum l == ' length l * c.
Proof with auto.
 intros.
 induction l.
  simpl.
  admit.
 simpl.
 rewrite IHl...
 admit.
Qed.

Lemma cmΣ'_constant (c: CR) (n: nat): cmΣ' n (λ _, c) == ' n * c.
Proof with auto.
 unfold cmΣ'.
 rewrite (cm_Sum_constant c).
  rewrite map_length, length_enum'. reflexivity.
 intros.
 apply in_map_iff in H.
 destruct H.
 symmetry.
 destruct H.
 subst.
 reflexivity.
Qed.

(** A straightforward definition of a Riemann approximation with n samples: *)

Program Definition Riemann (r: Range Q) (f: sig (In r) → CR) (n: positive): CR :=
  let w := (snd r - fst r)%Q in
  let iw: Q := w / n in
    ' iw * cmΣ' (nat_of_P n) (λ i, f (fst r + (` i: nat) * iw)%Q).

Next Obligation. Proof with auto with *.
 apply alt_in_QRange.
 exists (i / n).
 split.
  split.
   apply Qmult_le_0_compat.
    admit.
   apply Qinv_le_0_compat...
  apply Qdiv_le_1.
  split...
  admit.
 unfold Qdiv.
 generalize (Qinv n).
 intro.
 ring.
Qed.

(** ... and some properties thereof: *)

Lemma Riemann_plus (r: Range Q) (f g: sig (In r) → CR) n:
  Riemann r (λ x, f x + g x) n == Riemann r f n + Riemann r g n.
Proof with auto.
 unfold Riemann.
 unfold cmΣ'.
Admitted.

Lemma Riemann_scale (r: Range Q) (f: sig (In r) → CR) (c: CR) n:
  Riemann r (CRmult c ∘ f)%prg n == c * Riemann r f n.
Proof with auto.
 unfold Riemann.
 unfold cmΣ'.
 unfold Basics.compose.
Admitted.



(** Finally, we say what it means for a value to be the integral of a function on some range: *)

Class Integral (r: Range Q) (f: sig (∈ r) → CR): Type := integral:
  sig (λ x: CR, ∀ e: Qpos, ∃ n: positive, ∀ m: positive,
   (n <= m)%positive → ball e (Riemann r f m) x).
    (* this used to be just [∃ n, ball e (Riemann r f n) x], but i couldn't prove unicity that way *)

Implicit Arguments Integral [[r]].
Implicit Arguments integral [[r] [Integral]].

Notation "∫" := integral.


Lemma integral_unique (r: Range Q) (f: sig (In r) → CR)
  {i0: Integral f} {i1: Integral f}: ` i0 == ` i1.
Proof with auto.
 destruct i0, i1.
 simpl @proj1_sig.
 apply ball_eq.
 intros.
 set (h := (e1 * (1#2))%Qpos).
 setoid_replace e1 with (h+h)%Qpos.
  2: subst h; unfold QposEq; simpl; ring.
 specialize (e h).
 specialize (e0 h).
 destruct e, e0.
 apply ball_triangle with (Riemann r f (Pmax x1 x2))...
 apply ball_sym...
Qed.


(** We know what the integral must be for constant functions: *)

Obligation Tactic := idtac.

Section constant_integral.

  Context (r: Range Q) (y: CR).

  Notation f := (λ _: sig (In r), y).

  Program Definition integrate_constant: Integral f := ' (snd r - fst r)%Q * y.

  Next Obligation. Proof with auto.
   intros.
   exists 1%positive.
   intros.
   apply ball_eq_iff.
   unfold Riemann.
   clear H.
   rewrite cmΣ'_constant.
   admit. (* arithmetic *)
  Qed.

  Program Lemma constant_integral `{!Integral (λ _: sig (In r), y)}:
    ∫ f == integrate_constant.
  Proof. intros. apply integral_unique. Qed.

End constant_integral.

(** ...and for sums: *)

Section additive.

  Context
    (r: Range Q)
    (f g: sig (In r) → CR)
    `{!Integral f}
    `{!Integral g}.

  Let summed := (λ x, f x + g x).

  Program Definition sum_integrals: Integral summed := ∫ f + ∫ g.
  Next Obligation.
   intro.
   unfold integral.
   destruct Integral0, Integral1.
   simpl @proj1_sig.
   set (h := (e * (1#2))%Qpos).
   specialize (e0 h).
   specialize (e1 h).
   destruct e0, e1.
   exists (Pmax x1 x2).
   intros.
   setoid_replace e with (h+h)%Qpos.
    2: subst h; unfold QposEq; simpl; ring.
   unfold summed. rewrite Riemann_plus.
   admit. (* not hard *)
  Qed.

  Program Lemma summed_integral `{!Integral summed}:
    ∫ summed == sum_integrals.
  Proof. intro. apply integral_unique. Qed.

End additive.

(** ...and for scaled functions: *)

Section scalar_mult.

  Context (r: Range Q) (f: sig (∈ r) → CR) `{!Integral f} (c: Qpos).

  Let scaled := (CRmult (' c) ∘ f)%prg.

  Program Definition scale_integral: Integral scaled := ' c * ∫ f.
  Next Obligation.
   intro.
   unfold integral.
   destruct Integral0.
   simpl @proj1_sig.
   specialize (e0 (e / c)%Qpos).
   destruct e0.
   exists x0.
   intros.
   specialize (H m H0).
   unfold scaled.
   rewrite Riemann_scale.
   admit. (* not hard *)
  Qed.

  Program Lemma scaled_integral `{!Integral scaled}:
    ∫ scaled == scale_integral.
  Proof. intro. apply integral_unique. Qed.

End scalar_mult. (* Todo: generalize to more than just Qpos *)

(** ...and if we know the integral for a function at two adjacent ranges, we know the
 integral on the merged range: *)

Section adjacent.

  Context
    (a b c: Q)
    (fab: sig (In (a, b)) → CR)
    (fbc: sig (In (b, c)) → CR)
    (fac: sig (In (a, c)) → CR)
    (fab_good: ∀ x x', (` x == ` x')%Q → fab x == fac x')
    (fbc_good: ∀ x x', (` x == ` x')%Q → fac x == fac x')
    `{!Integral fab}
    `{!Integral fbc}.

  Program Definition integrate_merged: Integral fac := ∫ fab + ∫ fbc.
  Next Obligation.
   intro.
   unfold integral.
   destruct Integral0, Integral1.
   simpl @proj1_sig.
   set (h := (e * (1#2))%Qpos).
   specialize (e0 h).
   specialize (e1 h).
   destruct e0, e1.
   exists (x1 * x2)%positive.
   intros.
  Admitted. (* hassle, but doable, i think *)

  Context `{!Integral fac}.

  Program Lemma adjacent: ∫ fac == ∫ fab + ∫ fbc.
  Proof.
   transitivity (` integrate_merged).
    apply integral_unique.
   reflexivity.
  Qed.

End adjacent.


(** More generally, we can implement integration of uniformly continuous functions: *)

Section implementable.

  Context (r: Range Q) (f: sig (∈ r) → CR)
    `{!UniformlyContinuous_mu f}
    `{!UniformlyContinuous f}.

  Definition integrate_ucFunc: Integral f.
  Admitted.

End implementable.

(* Note: This should be much easier than it was in the old setting, because now all
 we'll need to do (hopefully) in the implementation is show that it does indeed produce
 Riemann approximations, and we no longer have to show Bishop's properties. *)

(** It should be fairly easy to prove that the implementation above
 is continuous in the function parameter: *)

Section continuity_in_f. (* with fixed range *)

  Context (r: Range Q) .

  Program Let raw (u: UCFunction (sig (∈ r)) CR): CR := integrate_ucFunc r u.
    (* needed to remove the type dependency by dropping the Integral wrapping around the result CR *)

  Instance: UniformlyContinuous_mu raw.
   constructor.
   intro. admit.
  Defined.

  Instance: UniformlyContinuous raw.
  Proof with auto.
   constructor.
     apply _.
    apply _.
   intros.
   unfold raw.
   unfold uc_mu in H.
   simpl in H.
  Admitted.

End continuity_in_f.


(** Continuity in both range and function simultaneously is trickier. *)

Section extend.

  Context (T: Type) (P: T → Prop) `{∀ t, Decision (P t)} (f: sig P → CR).

  Definition extend (t: T): CR :=
    match decide (P t) with
    | left H => f (exist _ _ H)
    | right _ => 0
    end.

  Context `{te: canonical_names.Equiv T}.

  Global Instance: Proper canonical_names.equiv extend.
  Admitted.

End extend.

Section continuity_in_both.

  Context (bound: Range CR).

  Definition IntegrationInput := sigT (λ r: Range Q, UCFunction (sig (∈ r)) (sig (∈ bound))).
    (* Hm, I think this probably needs an a-priori bound on r as well.. *)

  Instance dec_in: ∀ (a: Range Q), (∀ t : Q, Decision ((∈ a) t)).
  Admitted.

  Program Definition metric: IntegrationInput → Range Q * @sig (Q → CR) (Proper canonical_names.equiv) :=
   λ ab, (projT1 ab, (@extend Q (∈ projT1 ab) _ (@proj1_sig _ _ ∘ ucFun_itself (projT2 ab))%prg)).
     (* should never actually run at runtime *)
(*
  Global Instance IntegrationInput_equiv: canonical_names.Equiv IntegrationInput := delegated_equiv _ metric.
  Global Instance IntegrationInput_ball: MetricSpaceBall IntegrationInput := delegated_ball _ metric.
  Global Instance IntegrationInput_mspc: MetricSpaceClass IntegrationInput.
  Proof. apply (delegated_mspc _ metric). Qed.

  Program Definition integrate_ucFunc_wrapped_for_continuity: IntegrationInput → CR :=
    λ p, integrate_ucFunc (fst (projT1 p), snd (projT1 p)) (λ x, projT2 p (` x)).

  Next Obligation.
   intros.
   destruct x.
   simpl.
   assumption.
  Qed.

  Global Instance integrate_ucFunc_wrapped_for_continuity_mu: UniformlyContinuous_mu integrate_ucFunc_wrapped_for_continuity.
  Admitted.

  Global Instance integrate_ucFunc_wrapped_for_continuity_uc: UniformlyContinuous integrate_ucFunc_wrapped_for_continuity.
  Proof.
   constructor.
     apply _.
    apply _.
   admit.
  Qed.
*)
End continuity_in_both.
