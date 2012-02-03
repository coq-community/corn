Require Import
 CRArith CRabs.

Hint Immediate CRle_refl. (* todo: move *)

Open Scope CR_scope.

Section contents.

  Context {M: MetricSpace}.

  Definition CRball (r: CR) (x y: M): Prop := forall q, r <= ' q -> gball q x y.

  Global Instance proper: Proper (@st_eq _ ==> @st_eq _ ==> @st_eq _ ==> iff) CRball.
  Proof.
   intros ?? E ?? F ?? G.
   apply iff_under_forall.
   intro. rewrite E, F, G.
   reflexivity.
  Qed.

  Global Instance reflexive (r: CR): CRnonNeg r -> Reflexive (CRball r).
  Proof with auto.
   unfold CRball, Reflexive.
   intros.
   apply gball_refl.
   apply CRle_Qle.
   apply CRle_trans with r...
   apply -> CRnonNeg_le_0...
  Qed.

  Lemma zero (x y: M): x [=] y <-> CRball 0 x y.
  Proof with auto.
   rewrite <- gball_0.
   split; repeat intro...
   apply gball_weak_le with 0%Q...
   apply CRle_Qle...
  Qed.

  Lemma weak_le (r r': CR): r <= r' -> forall x y, CRball r x y -> CRball r' x y.
  Proof. intros ??? E ??. apply E. apply CRle_trans with r'; assumption. Qed.

  Lemma rational (r: Q) (x y: M): gball r x y <-> CRball ('r) x y.
  Proof with auto.
   split...
   repeat intro.
   apply CRle_Qle in H0.
   apply gball_weak_le with r...
  Qed.

End contents.

(* In the CR metric space, CRball is what you'd expect. *)

Lemma as_distance_bound (r x y: CR): CRball r x y <-> CRdistance x y <= r.
Proof with auto.
 unfold CRball.
 rewrite <- CRdistance_CRle.
 rewrite <- (@iff_under_forall Q
   (fun q: Q => (r <= 'q) -> (x - ' q <= y) /\ (y <= x + ' q))
   (fun q: Q => (r <= 'q) -> gball q x y)).
  2: intros; rewrite in_CRgball; intuition.
 split; intros.
  split.
   apply CRplus_le_l with (r - y).
   CRring_replace (r - y + (x - r)) (x - y).
   CRring_replace (r - y + y) r.
   apply (proj1 (Qle_CRle_r _ _)).
   intros.
   apply CRplus_le_l with (y - ' y').
   CRring_replace (y - 'y' + (x - y)) (x - 'y').
   CRring_replace (y - 'y' + 'y') y.
   now apply (H y').
  apply CRplus_le_r with (-x).
  CRring_replace (x + r - x) r.
  apply (proj1 (Qle_CRle_r _ _)). intros.
  apply CRplus_le_l with x.
  CRring_replace (x + (y - x)) y...
  apply H...
 split.
  apply CRle_trans with (x - r).
   apply CRplus_le_compat...
   apply -> CRle_opp...
  apply H.
 apply CRle_trans with (x + r).
  apply H.
 apply CRplus_le_compat...
Qed. (* todo: clean up *)

Module notations.

  Notation CRball := CRball.

End notations.
