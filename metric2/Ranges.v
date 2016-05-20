
Require Import Program MathClasses.interfaces.canonical_names util.Container QArith QMinMax CRlattice.

Definition Range (T: Type) := prod T T.

Instance in_QRange: Container Q (Range Q)
  := λ r x, (Qmin (fst r) (snd r) <= x <= Qmax (fst r) (snd r))%Q.

Instance in_CRRange: Container CR (Range CR)
  := λ r x, (CRmin (fst r) (snd r) <= x ∧ x <= CRmax (fst r) (snd r))%CR.

Instance in_sig_Range `{Container A (Range A)} (P: A → Prop): Container (sig P) (Range (sig P))
  := λ r x, In (` (fst r), ` (snd r)) (` x).

(*Lemma alt_in_QRange (q: Q) (r: Range Q): q ∈ r <->
  (∃ e, 0 <= e <= 1 ∧ fst r + e * (snd r - fst r) == q)%Q.
Proof with auto.
Admitted.*)
  (* also: ∃ e, 0 <= e <= 1 ∧ q == fst r * e + snd r * (1 - e) *)
