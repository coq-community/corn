Require Import 
  Streams
  CRseries Qpossec CornTac Metric
  abstract_algebra interfaces.additional_operations
  theory.nat_pow theory.rings interfaces.naturals
  ARArith ApproximateRationals.

Section series.
Context `{SemiRing A}.
Add Ring A : (rings.stdlib_semiring_theory A).

Definition mult_Streams : Stream A → Stream A → Stream A := zipWith ring_mult.

Section powers.
  Context `{np : !NatPow A nat} (a : A).

  CoFixpoint powers_help (c : A) : Stream A := Cons c (powers_help (c * a)).
  Definition powers : Stream A := powers_help 1.

  Lemma Str_nth_powers_help (n : nat) (c : A) : Str_nth n (powers_help c) = c * a ^ n.
  Proof.
    revert c.
    induction n; intros c; unfold Str_nth in *; simpl.
     rewrite nat_pow_0. ring.
    rewrite peano_naturals.S_nat_1_plus nat_pow_S.
    rewrite IHn. ring.
  Qed.

  Lemma Str_nth_powers (n : nat) : Str_nth n powers = a ^ n.
  Proof.
    unfold powers.
    rewrite ->Str_nth_powers_help.
    ring.
  Qed.
End powers.

Section positives.
  CoFixpoint positives_help (x : A) : Stream A := Cons x (positives_help (1 + x)).

  Definition positives : Stream A := positives_help 1.

  Lemma Str_nth_positives_help (n : nat) (x : A) : 
    Str_nth n (positives_help x) = x + (naturals.naturals_to_semiring nat A n).
  Proof.
    revert x.
    induction n; intros c; unfold Str_nth in *; simpl.
     replace (0%nat) with (0:nat) by reflexivity.
     rewrite rings.preserves_0. ring.
    rewrite peano_naturals.S_nat_1_plus.
    rewrite preserves_plus preserves_1.
    rewrite IHn.
    ring.
  Qed.

  Lemma Str_nth_positives (n : nat) : 
    Str_nth n positives = 1 + (naturals.naturals_to_semiring nat A n).
  Proof.
    unfold positives.
    rewrite ->Str_nth_positives_help. reflexivity.
  Qed.
End positives.
End series.

Section ar_series. 
Context `{AppRationals AQ}.

Section recip_positives.
  Context (ε : Qpos).
  
  Program CoFixpoint aq_recip_positives_help (x : AQ) (P : 0 < x) := Cons (app_mult_inv x ε) (aq_recip_positives_help (x + 1) _).
  Next Obligation. 
    apply not_symmetry, orders.neq_precedes_sprecedes. 
    assumption. 
  Qed.
  
  Next Obligation. 
    apply semirings.pos_plus_compat_l. trivial. 
    apply (semirings.precedes_0_1). 
  Qed. 

  Definition aq_recip_positives : Stream AQ := aq_recip_positives_help 1 semirings.sprecedes_0_1.

  Lemma Str_nth_recip_positives_help (n : nat) (x : AQ) (P1 : 0 < x) (P2 : x + naturals_to_semiring nat AQ n ≠ 0) :
    Str_nth n (aq_recip_positives_help x P1) = app_mult_inv (exist _ (x + naturals_to_semiring nat AQ n) P2) ε.
  Proof with try reflexivity; auto.
    generalize dependent x.
    induction n; intros c P1 P2; unfold Str_nth in *; simpl.
     apply aq_mult_inv_proper...
     unfold equiv, sig_equiv, sig_relation. simpl. 
     replace (0%nat) with (0:nat) by reflexivity.
     rewrite preserves_0 plus_0_r...
    assert ((c + 1) + naturals_to_semiring nat AQ n ≠ 0) as P3.
     intros E. apply P2. 
     rewrite peano_naturals.S_nat_1_plus.
     rewrite preserves_plus preserves_1 associativity...
    rewrite (IHn (c + 1) _ P3).
    apply aq_mult_inv_proper...
    unfold equiv, sig_equiv, sig_relation. simpl. 
    rewrite peano_naturals.S_nat_1_plus.
    rewrite preserves_plus preserves_1 associativity...
  Qed.

  Lemma Str_nth_recip_positives (n : nat) (P2 : 1 + naturals_to_semiring nat AQ n ≠ 0) : 
    Str_nth n aq_recip_positives = app_mult_inv (exist _ (1 + naturals_to_semiring nat AQ n) P2) ε.
  Proof.
    unfold aq_recip_positives.
    rewrite (Str_nth_recip_positives_help n 1 semirings.sprecedes_0_1 P2).
    reflexivity.
  Qed.
End recip_positives.
End ar_series.
