(* $Id: freem_to_Nm.v,v 1.1 2004/09/22 11:06:13 loeb Exp $ *)

Require Export CMonoids.
Require Export Nmonoid.

Section p71E2.

(** **A morphism from a free monoid to the natural numbers
%\begin{convention}%
Let [A:CSetoid].
%\end{convention}%
*) 

Variable A:CSetoid.

Let L: (free_monoid_as_CMonoid A)-> nat_as_CMonoid.
simpl.
unfold Astar.
intros l.
exact (length l).
Defined.

Lemma L_strext: (fun_strext L).
simpl.
unfold fun_strext.
simpl.
unfold Astar.
intros x.
induction x.
intro y.
case y.
simpl.
unfold ap_nat.
unfold CNot.
intuition.

simpl.
intuition.

intro y.
case y.
simpl.
intuition.

simpl.
intros c l H.
right.
apply IHx.
unfold ap_nat in H |- *.
unfold CNot in H |- *.
intuition.
Qed.

Definition L_as_CSetoid_fun:=
(Build_CSetoid_fun _ _ L L_strext).

Lemma L_is_morphism: (morphism _ _ L_as_CSetoid_fun).
unfold morphism.
simpl.
split.
reflexivity.

unfold Astar.
intros a.
induction a.
simpl.
reflexivity.

simpl.
intuition.
Qed.

End p71E2.
