Require Import MathClasses.interfaces.canonical_names.

Class Container (Elem C: Type) := In: C → Elem → Prop.
#[global]
Hint Unfold In.
Notation "x ∈ y" := (In y x) (at level 70).
Notation "x ∉ y" := (¬In y x) (at level 70).
Notation "(∈ y )" := (In y).
