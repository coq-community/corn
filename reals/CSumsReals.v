(* $Id$ *)

Require Export CReals1.

Opaque IR.

(** * Sums over Reals

%\begin{convention}%
Let [c] be a real.
%\end{convention}%

Here we prove that
$\Sigma_{m\leq i \leq n}~c^k = \frac{c^{n+1}-c^m}{c-1}.$
#sum_(m&le; i &le; n) c^k = frac (c^(n+1) -c^m) (c-1)#
*)

Section Sums_over_Reals.

Variable c : IR.

Lemma Sum0_c_exp :
 forall (H : c[-]One[#]Zero) (m : nat),
 Sum0 m (fun i : nat => c[^]i)[=](c[^]m[-]One[/] c[-]One[//]H).
intros.
elim m.
simpl in |- *.
rational.
simpl in |- *.
intros.
AStepl ((nexp IR n c[-]One[/] c[-]One[//]H)[+]nexp IR n c).
rational.
Qed.

Hint Resolve Sum0_c_exp.

Lemma Sum_c_exp :
 forall (H : c[-]One[#]Zero) (m n : nat),
 Sum m n (fun i : nat => c[^]i)[=](c[^]S n[-]c[^]m[/] c[-]One[//]H).
intros.
unfold Sum in |- *.
unfold Sum1 in |- *.
AStepl ((c[^]S n[-]One[/] c[-]One[//]H)[-](c[^]m[-]One[/] c[-]One[//]H)).
rational.
Qed.
Hint Resolve Sum_c_exp.

(** The following formulation is often more useful if [c<1]. *)

Lemma Sum_c_exp' :
 forall (H : One[-]c[#]Zero) (m n : nat),
 Sum m n (fun i : nat => c[^]i)[=](c[^]m[-]c[^]S n[/] One[-]c[//]H).
intros.
cut (c[-]One[#]Zero).
intro H0.
AStepl (c[^]S n[-]c[^]m[/] c[-]One[//]H0).
rational.
RStepl ([--](One[-]c)).
apply inv_resp_ap_zero.
assumption.
Qed.

Hint Resolve Sum_c_exp'.

End Sums_over_Reals.

Hint Resolve Sum0_c_exp Sum_c_exp Sum_c_exp': algebra.

Lemma diff_is_Sum0 :
 forall (s : nat -> IR) (n : nat),
 s n[-]s 0[=]Sum0 n (fun i : nat => s (S i)[-]s i).
Proof.
intros s.
simple induction n.
simpl in |- *. Algebra.
intros.
simpl in |- *.
apply eq_transitive_unfolded with (s (S n0)[-]s n0[+](s n0[-]s 0)).
rational.
apply
 eq_transitive_unfolded
  with (s (S n0)[-]s n0[+]Sum0 n0 (fun i : nat => s (S i)[-]s i)).
exact (plus_resp_eq _ _ _ _ H).
rational.
Qed.

Lemma diff_is_sum :
 forall (s : nat -> IR) (N m : nat),
 N < m -> s m[-]s N[=]Sum N (pred m) (fun i : nat => s (S i)[-]s i).
Proof.
intros s N m ltNm.
unfold Sum in |- *. unfold Sum1 in |- *.
generalize (S_pred m N ltNm).
intro H.
rewrite <- H.
generalize (diff_is_Sum0 s N).
intro HsN.
generalize (diff_is_Sum0 s m).
intro Hsm.
apply eq_transitive_unfolded with (s m[-]s 0[-](s N[-]s 0)).
rational.
apply (cg_minus_wd IR).
assumption.
assumption.
Qed.

Lemma Sum0_pres_less :
 forall s t : nat -> IR,
 (forall i : nat, s i[<]t i) -> forall n : nat, Sum0 n s[<=]Sum0 n t.
Proof.
intros s t H.
simple induction n.
simpl in |- *.
exact (leEq_reflexive _ _).
intros.
simpl in |- *.
apply leEq_transitive with (Sum0 n0 t[+]s n0).
apply plus_resp_leEq.
assumption.
apply plus_resp_leEq_lft.
apply less_leEq; exact (H _).
Qed.

Lemma Sum_pres_less :
 forall s t : nat -> IR,
 (forall i : nat, s i[<]t i) ->
 forall N m : nat, N <= m -> Sum N m s[<=]Sum N m t.
intros.
apply less_leEq.
apply Sum_resp_less; auto.
Qed.

Lemma Sum_pres_leEq :
 forall s t : nat -> IR,
 (forall i : nat, s i[<=]t i) ->
 forall N m : nat, N <= m -> Sum N m s[<=]Sum N m t.
intros.
apply Sum_resp_leEq; auto.
Qed.

Lemma Sum0_comm_scal :
 forall (s : nat -> IR) (a : IR) (m : nat),
 Sum0 m (fun i : nat => s i[*]a)[=]Sum0 m (fun i : nat => s i)[*]a.
intros. induction  m as [| m Hrecm]; intros.
simpl in |- *. Algebra.
simpl in |- *. Step_final (Sum0 m (fun i : nat => s i)[*]a[+]s m[*]a).
Qed.

Hint Resolve Sum0_comm_scal: algebra.

Lemma Sum_comm_scal :
 forall (s : nat -> IR) (a : IR) (N m : nat),
 Sum N m (fun i : nat => s i[*]a)[=]Sum N m (fun i : nat => s i)[*]a.
unfold Sum in |- *. unfold Sum1 in |- *. intros.
Step_final
 (Sum0 (S m) (fun i : nat => s i)[*]a[-]Sum0 N (fun i : nat => s i)[*]a).
Qed.

Lemma Sum0_comm_scal' :
 forall (c : IR) (x : nat -> IR) (m : nat),
 Sum0 m (fun i : nat => c[*]x i)[=]c[*]Sum0 m x.
intros.
apply eq_transitive_unfolded with (Sum0 m (fun n : nat => x n)[*]c).
2: AStepr (Sum0 m x[*]c); apply mult_wd_lft.
2: apply Sum0_wd; Algebra.
eapply eq_transitive_unfolded.
2: apply Sum0_comm_scal.
apply Sum0_wd; Algebra.
Qed.

Lemma Sum_comm_scal' :
 forall (c : IR) (x : nat -> IR) (m n : nat),
 Sum m n (fun i : nat => c[*]x i)[=]c[*]Sum m n x.
intros.
unfold Sum, Sum1 in |- *.
eapply eq_transitive_unfolded.
2: apply eq_symmetric_unfolded; apply dist_2a.
apply cg_minus_wd; apply Sum0_comm_scal'.
Qed.

Lemma Sumx_comm_scal' :
 forall (n : nat) (c : IR) (f : forall i : nat, i < n -> IR),
 Sumx (fun (i : nat) (H : i < n) => c[*]f i H)[=]c[*]Sumx f.
simple induction n.
intros; simpl in |- *; Algebra.
clear n; intros; simpl in |- *.
eapply eq_transitive_unfolded.
2: apply eq_symmetric_unfolded; apply ring_dist_unfolded.
apply bin_op_wd_unfolded.
apply H with (f := fun (i : nat) (l : i < n) => f i (lt_S _ _ l)).
Algebra.
Qed.

Lemma Sum2_comm_scal' :
 forall (c : IR) (m n : nat),
 m <= S n ->
 forall f,
 Sum2 (fun (i : nat) (Hm : m <= i) (Hn : i <= n) => c[*]f i Hm Hn)[=]
 c[*]Sum2 f.
intros; unfold Sum2 in |- *.
eapply eq_transitive_unfolded.
2: apply Sum_comm_scal'.
apply Sum_wd'.
assumption.
intros.
elim (le_lt_dec m i); intros; simpl in |- *.
elim (le_lt_dec i n); intros; simpl in |- *; Algebra.
Algebra.
Qed.