
(** printing included %\ensuremath{\subseteq}% #&sube;# *)

Require Export CSetoidFun.

Section inclusion.

(** ** Inclusion

Let [S] be a setoid, and [P], [Q], [R] be predicates on [S]. *)

Variable S : CSetoid.

Definition included (P Q : S -> CProp) : CProp := forall x : S, P x -> Q x.

Section Basics.

Variables P Q R : S -> CProp.

Lemma included_refl : included P P.
red in |- *; intros.
auto.
Qed.

Lemma included_trans : included P Q -> included Q R -> included P R.
intros.
red in |- *; intros.
apply X0; apply X; auto.
Qed.

Lemma included_conj : forall P Q R, included P Q -> included P R -> included P (Conj Q R).
intros.
red in |- *; red in X, X0.
intros; red in |- *.
split.
apply X; assumption.
apply X0; assumption.
Qed.

Lemma included_conj' : included (Conj P Q) P.
exact (prj1 _ P Q).
Qed.

Lemma included_conj'' : included (Conj P Q) Q.
exact (prj2 _ P Q).
Qed.

Lemma included_conj_lft : included R (Conj P Q) -> included R P.
red in |- *.
unfold conjP.
intros H1 x H2.
elim (H1 x); auto.
Qed.

Lemma included_conj_rht : included R (Conj P Q) -> included R Q.
red in |- *. unfold conjP.
intros H1 x H2.
elim (H1 x); auto.
Qed.

Lemma included_extend : forall (H : forall x, P x -> CProp),
 included R (extend P H) -> included R P.
intros H0 H1.
red in |- *.
unfold extend in H1.
intros.
elim (H1 x); auto.
Qed.

End Basics.

(**
%\begin{convention}% Let [I,R:S->CProp] and [F G:(PartFunct S)], and denote
by [P] and [Q], respectively, the domains of [F] and [G].
%\end{convention}%
*)

Variables F G : (PartFunct S).

(* begin hide *)
Let P := Dom F.
Let Q := Dom G.
(* end hide *)

Variable R : S -> CProp.

Lemma included_FComp : included R P -> (forall x Hx, (R x) -> Q (F x Hx)) -> included R (Dom (G[o]F)).
intros HP HQ.
simpl in |- *.
red in |- *; intros x Hx.
exists (HP x Hx).
apply HQ.
assumption.
Qed.

Lemma included_FComp' : included R (Dom (G[o]F)) -> included R P.
intro H; simpl in H; red in |- *; intros x Hx.
elim (H x Hx); auto.
Qed.

End inclusion.

Implicit Arguments included [S].

Hint Resolve included_refl included_FComp : included.

Hint Immediate included_trans included_FComp' : included.
