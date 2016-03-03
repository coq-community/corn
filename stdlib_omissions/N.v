Require Import CoRN.stdlib_omissions.List.

Fixpoint enum (n: nat): list nat :=
  match n with
  | O => nil
  | S n' => n' :: enum n'
  end.
