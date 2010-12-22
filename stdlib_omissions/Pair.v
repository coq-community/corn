Require Import Unicode.Utf8 Setoid List.

Section pair_rel.

  Context {A B} (Ra: relation A) (Rb: relation B) `{!Equivalence Ra} `{!Equivalence Rb}.

  Definition pair_rel: relation (A * B) :=
    fun a b => Ra (fst a) (fst b) /\ Rb (snd a) (snd b).

  Global Instance: Equivalence pair_rel.
  Proof. firstorder. Qed.

End pair_rel.

Definition first {A B C} (f: A → B) (p: A * C): B * C := (f (fst p), snd p).

Lemma map_fst_map_first {A B C} (l: list (A * B)) (f: A -> C): map (@fst _ _) (map (first f) l) = map f (map (@fst _ _) l).
Proof. induction l; simpl; congruence. Qed.

Definition curry {A B C} (f: A * B → C) (a: A) (b: B): C := f (a, b).
Definition uncurry {A B C} (f: A → B → C) (p: A * B): C := f (fst p) (snd p).

Definition map_pair {X Y A B} (f: X → Y) (g: A → B) (xa: X * A): Y * B := (f (fst xa), g (snd xa)).

Definition diagonal {X} (x: X): X * X := (x, x).
