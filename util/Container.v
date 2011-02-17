Require Import canonical_names.

Class Container (Elem C: Type) := In: C → Elem → Prop.
Hint Unfold In.
Notation "x ∈ y" := (In y x) (at level 40).
Notation "(∈ y )" := (In y) (at level 40).
Notation "x ∉ y" := (¬In y x) (at level 40).