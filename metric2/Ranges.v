
Require Import Program MathClasses.interfaces.canonical_names util.Container QArith QMinMax CRlattice.

Definition Range (T: Type) := prod T T.

#[global]
Instance in_QRange: Container Q (Range Q)
  := λ r x, (Qmin (fst r) (snd r) <= x <= Qmax (fst r) (snd r))%Q.

#[global]
Instance in_CRRange: Container (msp_car CR) (Range (msp_car CR))
  := λ r x,
     (ucFun (ucFun CRmin (fst r)) (snd r) <= x)%CR
     ∧ (x <= ucFun (ucFun CRmax (fst r)) (snd r))%CR.

#[global]
Instance in_sig_Range `{Container A (Range A)} (P: A → Prop): Container (sig P) (Range (sig P))
  := λ r x, In (` (fst r), ` (snd r)) (` x).

