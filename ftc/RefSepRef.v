(* $Id$ *)

(* begin hide *)

Require Export IntegralLemmas.

Section Refining_Separated.

Variables a b : IR.
Hypothesis Hab : a[<=]b.
Let I := compact a b Hab.

Variable F : PartIR.
Hypothesis contF : Continuous_I Hab F.
Hypothesis incF : included (compact a b Hab) (Dom F).

Variables m n : nat.
Variable P : Partition Hab n.
Variable R : Partition Hab m.

Hypothesis HPR : Separated P R.

Let HP : _Separated P.
elim HPR; intros; assumption.
Qed.

Let HP' : a[=]b -> 0 = n.
intro.
apply _Separated_imp_length_zero with (P := P).
exact HP.
assumption.
Qed.

Let HR : _Separated R.
elim HPR; intros.
elim b0; intros; assumption.
Qed.

Let HR' : a[=]b -> 0 = m.
intro.
apply _Separated_imp_length_zero with (P := R).
exact HR.
assumption.
Qed.

Let mn0 : 0 = m -> 0 = n.
intro; apply HP'; apply partition_length_zero with Hab.
rewrite H; apply R.
Qed.

Let nm0 : 0 = n -> 0 = m.
intro; apply HR'; apply partition_length_zero with Hab.
rewrite H; apply P.
Qed.

Let H' :
  forall i j : nat,
  0 < i ->
  0 < j ->
  i < n -> j < m -> forall (Hi : i <= n) (Hj : j <= m), P i Hi[#]R j Hj.
elim HPR; do 2 intro.
elim b0; do 2 intro; assumption.
Qed.

Let f' (i : nat) (H : i < pred n) := P _ (lt_8 _ _ H).
Let g' (j : nat) (H : j < pred m) := R _ (lt_8 _ _ H).

Let f'_nlnf : nat_less_n_fun _ _ f'.
red in |- *; intros; unfold f' in |- *; apply prf1; auto.
Qed.

Let g'_nlnf : nat_less_n_fun _ _ g'.
red in |- *; intros; unfold g' in |- *; apply prf1; auto.
Qed.

Let f'_mon : forall (i i' : nat) Hi Hi', i < i' -> f' i Hi[<]f' i' Hi'.
intros.
apply local_mon_imp_mon_lt with (n := pred n).
intros; unfold f' in |- *; apply HP.
assumption.
Qed.

Let g'_mon : forall (j j' : nat) Hj Hj', j < j' -> g' j Hj[<]g' j' Hj'.
intros.
apply local_mon_imp_mon_lt with (n := pred m).
intros; unfold g' in |- *; apply HR.
assumption.
Qed.

Let f'_ap_g' : forall (i j : nat) Hi Hj, f' i Hi[#]g' j Hj.
intros.
unfold f', g' in |- *; apply H'.
apply lt_O_Sn.
apply lt_O_Sn.
apply pred_lt; assumption.
apply pred_lt; assumption.
Qed.

Let h := om_fun _ _ _ _ _ f'_ap_g'.

Let h_nlnf : nat_less_n_fun _ _ h.
unfold h in |- *; apply om_fun_1; auto.
Qed.

Let h_mon : forall (i i' : nat) Hi Hi', i < i' -> h i Hi[<]h i' Hi'.
unfold h in |- *; apply om_fun_2; auto.
Qed.

Let h_mon' : forall (i i' : nat) Hi Hi', i <= i' -> h i Hi[<=]h i' Hi'.
intros; apply mon_imp_mon'_lt with (n := pred m + pred n).
apply h_nlnf.
apply h_mon.
assumption.
Qed.

Let h_f' : forall (i : nat) Hi, {j : nat | {Hj : _ < _ | f' i Hi[=]h j Hj}}.
unfold h in |- *; apply om_fun_3a; auto.
Qed.

Let h_g' : forall (j : nat) Hj, {i : nat | {Hi : _ < _ | g' j Hj[=]h i Hi}}.
unfold h in |- *; apply om_fun_3b; auto.
Qed.

Let h_PropAll :
  forall P : IR -> Prop,
  pred_well_def' IR P ->
  (forall (i : nat) Hi, P (f' i Hi)) ->
  (forall (j : nat) Hj, P (g' j Hj)) -> forall (k : nat) Hk, P (h k Hk).
unfold h in |- *; apply om_fun_4b.
Qed.

Let h_PropEx :
  forall P : IR -> Prop,
  pred_well_def' IR P ->
  {i : nat | {Hi : _ < _ | P (f' i Hi)}}
  or {j : nat | {Hj : _ < _ | P (g' j Hj)}} ->
  {k : nat | {Hk : _ < _ | P (h k Hk)}}.
unfold h in |- *; intros; apply om_fun_4d; auto.
Qed.

Definition Separated_Refinement_fun : forall i : nat, i <= pred (m + n) -> IR.
intros.
elim (le_lt_eq_dec _ _ H); intro.
elim (le_lt_dec i 0); intro.
apply a.
apply (h (pred i) (lt_10 _ _ _ b0 a0)).
apply b.
Defined.

Lemma Separated_Refinement_lemma1 :
 forall i j : nat,
 i = j ->
 forall (Hi : i <= pred (m + n)) (Hj : j <= pred (m + n)),
 Separated_Refinement_fun i Hi[=]Separated_Refinement_fun j Hj.
do 3 intro.
rewrite <- H; intros; unfold Separated_Refinement_fun in |- *; simpl in |- *.
elim (le_lt_eq_dec _ _ Hi); elim (le_lt_eq_dec _ _ Hj); elim (le_lt_dec i 0);
 intros; simpl in |- *.
Algebra.
apply h_nlnf; reflexivity.
elimtype False; rewrite <- b0 in a1; apply (lt_irrefl _ a1).
elimtype False; rewrite <- b1 in a0; apply (lt_irrefl _ a0).
elimtype False; rewrite <- b0 in a1; apply (lt_irrefl _ a1).
elimtype False; rewrite <- b1 in a0; apply (lt_irrefl _ a0).
Algebra.
Algebra.
Qed.

Lemma Separated_Refinement_lemma3 :
 forall H : 0 <= pred (m + n), Separated_Refinement_fun 0 H[=]a.
intros; unfold Separated_Refinement_fun in |- *; simpl in |- *.
elim (le_lt_eq_dec _ _ H); elim (le_lt_dec 0 0); intros; simpl in |- *.
Algebra.
elimtype False; inversion b0.
apply eq_symmetric_unfolded; apply partition_length_zero with Hab.
cut (m + n <= 1); [ intro | omega ].
elim (plus_eq_one_imp_eq_zero _ _ H0); intro.
rewrite <- a1; apply R.
rewrite <- b1; apply P.
elimtype False; inversion b0.
Qed.

Lemma Separated_Refinement_lemma4 :
 forall H : pred (m + n) <= pred (m + n),
 Separated_Refinement_fun (pred (m + n)) H[=]b.
intros; unfold Separated_Refinement_fun in |- *; simpl in |- *.
elim (le_lt_eq_dec _ _ H); elim (le_lt_dec 0 0); intros; simpl in |- *.
Algebra.
elimtype False; apply (lt_irrefl _ a1).
elimtype False; apply (lt_irrefl _ a0).
Algebra.
Algebra.
Qed.

Lemma Separated_Refinement_lemma2 :
 forall (i : nat) (H : i <= pred (m + n)) (H' : S i <= pred (m + n)),
 Separated_Refinement_fun i H[<=]Separated_Refinement_fun (S i) H'.
intros; unfold Separated_Refinement_fun in |- *; simpl in |- *.
elim (le_lt_eq_dec _ _ H); elim (le_lt_eq_dec _ _ H'0); intros; simpl in |- *.
elim (le_lt_dec i 0); elim (le_lt_dec (S i) 0); intros; simpl in |- *.
elimtype False; inversion a2.
apply h_PropAll with (P := fun x : IR => a[<=]x).
red in |- *; intros.
apply leEq_wdr with x; assumption.
intros; unfold f' in |- *.
AStepl (P 0 (le_O_n _)).
apply Partition_mon; apply le_O_n.
intros; unfold g' in |- *.
AStepl (R 0 (le_O_n _)).
apply Partition_mon; apply le_O_n.
elimtype False; inversion a2.
apply less_leEq; apply h_mon; auto with arith.
elim (le_lt_dec i 0); elim (le_lt_dec (S i) 0); intros; simpl in |- *.
elimtype False; inversion a1.
assumption.
elimtype False; inversion a1.
apply h_PropAll with (P := fun x : IR => x[<=]b).
red in |- *; intros.
apply leEq_wdl with x; assumption.
intros; unfold f' in |- *.
apply leEq_wdr with (P _ (le_n _)).
apply Partition_mon; apply le_trans with (pred n); auto with arith.
apply finish.
intros; unfold g' in |- *.
apply leEq_wdr with (R _ (le_n _)).
apply Partition_mon; apply le_trans with (pred m); auto with arith.
apply finish.
elimtype False; rewrite <- b0 in H'0; apply (le_Sn_n _ H'0).
apply leEq_reflexive.
Qed.

Definition Separated_Refinement : Partition Hab (pred (m + n)).
apply Build_Partition with Separated_Refinement_fun.
exact Separated_Refinement_lemma1.
exact Separated_Refinement_lemma2.
exact Separated_Refinement_lemma3.
exact Separated_Refinement_lemma4.
Defined.

Let auxP : nat -> nat.
intro i.
elim (le_lt_dec i 0); intro.
apply 0.
elim (le_lt_dec n i); intro.
apply (pred (m + n) + (i - n)).
apply (S (ProjT1 (h_f' (pred i) (lt_pred' _ _ b0 b1)))).
Defined.

Let auxR : nat -> nat.
intro i.
elim (le_lt_dec i 0); intro.
apply 0.
elim (le_lt_dec m i); intro.
apply (pred (m + n) + (i - m)).
apply (S (ProjT1 (h_g' (pred i) (lt_pred' _ _ b0 b1)))).
Defined.

Let not_not_lt : forall i j : nat, ~ ~ i < j -> i < j.
intros; omega.
Qed.

Let plus_pred_pred_plus :
  forall i j k : nat, k <= pred i + pred j -> k <= pred (i + j).
intros; omega.
Qed.

Let auxP_lemma0 : auxP 0 = 0.
unfold auxP in |- *.
elim (le_lt_dec 0 0); intro; simpl in |- *.
reflexivity.
elimtype False; inversion b0.
Qed.

Let h_inj : forall (i j : nat) Hi Hj, h i Hi[=]h j Hj -> i = j.
intros.
eapply mon_imp_inj_lt with (f := h).
exact h_mon.
apply H.
Qed.

Let auxP_lemmai :
  forall (i : nat) (Hi : 0 < i) (Hi' : i < n),
  auxP i = S (ProjT1 (h_f' (pred i) (lt_pred' _ _ Hi Hi'))).
intros.
unfold auxP in |- *.
elim (le_lt_dec n i); intro; simpl in |- *.
elimtype False; apply le_not_lt with n i; auto.
elim (le_lt_dec i 0); intro; simpl in |- *.
elimtype False; apply lt_irrefl with 0; apply lt_le_trans with i; auto.
set (x := ProjT1 (h_f' _ (lt_pred' _ _ b1 b0))) in *.
set (y := ProjT1 (h_f' _ (lt_pred' _ _ Hi Hi'))) in *.
cut (x = y).
intro; auto with arith.
assert (H := ProjT2 (h_f' _ (lt_pred' _ _ b1 b0))).
assert (H0 := ProjT2 (h_f' _ (lt_pred' _ _ Hi Hi'))).
elim H; clear H; intros Hx Hx'.
elim H0; clear H0; intros Hy Hy'.
apply h_inj with Hx Hy.
eapply eq_transitive_unfolded.
2: apply Hy'.
eapply eq_transitive_unfolded.
apply eq_symmetric_unfolded; apply Hx'.
apply f'_nlnf; reflexivity.
Qed.

Let auxP_lemman : auxP n = pred (m + n).
unfold auxP in |- *.
elim (le_lt_dec n 0); intro; simpl in |- *.
cut (n = 0); [ intro | auto with arith ].
transitivity (pred m).
2: rewrite H; auto.
cut (0 = m); [ intro; rewrite <- H0; auto | apply HR' ].
apply partition_length_zero with Hab; rewrite <- H; apply P.
elim (le_lt_dec n n); intro; simpl in |- *.
rewrite <- minus_n_n; auto.
elimtype False; apply lt_irrefl with n; auto.
Qed.

Let auxP_lemma1 : forall i j : nat, i < j -> auxP i < auxP j.
intros; unfold auxP in |- *.
elim (le_lt_dec i 0); intro.
elim (le_lt_dec j 0); intros; simpl in |- *.
apply lt_le_trans with j; try apply le_lt_trans with i; auto with arith.
elim (le_lt_dec n j); intros; simpl in |- *.
omega.
apply lt_O_Sn.
elim (le_lt_dec n i); elim (le_lt_dec j 0); intros; simpl in |- *.
elim (lt_irrefl 0); apply lt_le_trans with j; try apply le_lt_trans with i;
 auto with arith.
elim (le_lt_dec n j); intro; simpl in |- *.
apply plus_lt_compat_l.
apply plus_lt_reg_l with n.
repeat rewrite <- le_plus_minus; auto.
elim (le_not_lt n i); auto; apply lt_trans with j; auto.
elim (lt_irrefl 0); apply lt_trans with i; auto; apply lt_le_trans with j;
 auto.
elim (le_lt_dec n j); intro; simpl in |- *.
apply lt_le_trans with (S (pred m + pred n)).
apply lt_n_S.
apply (ProjT1 (ProjT2 (h_f' (pred i) (lt_pred' _ _ b0 b2)))).
rewrite plus_n_Sm.
rewrite <- S_pred with n 0.
2: apply lt_trans with i; auto.
replace (pred m + n) with (pred (m + n)).
auto with arith.
cut (S (pred (m + n)) = S (pred m + n)); auto.
rewrite <- plus_Sn_m.
rewrite S_pred with m 0; auto with arith.
apply neq_O_lt.
intro.
apply lt_irrefl with 0.
apply lt_trans with i; auto.
rewrite mn0; auto.
apply lt_n_S.
cut
 (~
  ~
  ProjT1 (h_f' (pred i) (lt_pred' _ _ b0 b2)) <
  ProjT1 (h_f' (pred j) (lt_pred' _ _ b1 b3))); intro.
apply not_not_lt; assumption.
cut
 (ProjT1 (h_f' (pred j) (lt_pred' _ _ b1 b3)) <=
  ProjT1 (h_f' (pred i) (lt_pred' _ _ b0 b2))); intros.
2: apply not_lt; assumption.
cut
 (h _ (ProjT1 (ProjT2 (h_f' (pred j) (lt_pred' _ _ b1 b3))))[<=]
  h _ (ProjT1 (ProjT2 (h_f' (pred i) (lt_pred' _ _ b0 b2))))).
intro.
2: apply h_mon'; assumption.
cut (f' (pred j) (lt_pred' _ _ b1 b3)[<=]f' (pred i) (lt_pred' _ _ b0 b2)).
2: apply
    leEq_wdl
     with (h _ (ProjT1 (ProjT2 (h_f' (pred j) (lt_pred' _ _ b1 b3))))).
2: apply
    leEq_wdr
     with (h _ (ProjT1 (ProjT2 (h_f' (pred i) (lt_pred' _ _ b0 b2))))).
2: assumption.
3: apply eq_symmetric_unfolded;
    exact (ProjT2 (ProjT2 (h_f' (pred j) (lt_pred' _ _ b1 b3)))).
2: apply eq_symmetric_unfolded;
    exact (ProjT2 (ProjT2 (h_f' (pred i) (lt_pred' _ _ b0 b2)))).
clear H2 H1; intro.
cut (f' _ (lt_pred' _ _ b0 b2)[<]f' _ (lt_pred' _ _ b1 b3)).
2: apply f'_mon.
2: apply lt_pred'; assumption.
intro.
elimtype False.
apply less_irreflexive_unfolded with (x := f' _ (lt_pred' _ _ b1 b3)).
eapply leEq_less_trans; [ apply H1 | apply X ].
Qed.

Let auxP_lemma2 :
  forall (i : nat) (H : i <= n),
  {H' : auxP i <= _ | P i H[=]Separated_Refinement _ H'}.
intros.
unfold Separated_Refinement in |- *; simpl in |- *.
unfold Separated_Refinement_fun in |- *; simpl in |- *.
elim (le_lt_dec i 0); intro; simpl in |- *.
cut (i = 0); [ intro | auto with arith ].
generalize H; clear a0 H; rewrite H0.
rewrite auxP_lemma0.
clear H0; intros.
exists (le_O_n (pred (m + n))).
elim le_lt_eq_dec; intro; simpl in |- *.
elim (le_lt_dec 0 0); intro; simpl in |- *.
apply start.
elimtype False; inversion b0.
apply eq_transitive_unfolded with a.
apply start.
apply partition_length_zero with Hab.
cut (m + n <= 1).
intro.
elim (plus_eq_one_imp_eq_zero _ _ H0); intro.
rewrite <- a0; apply R.
rewrite <- b1; apply P.
generalize b0; clear b0.
case (m + n).
auto.
intros.
simpl in b0; rewrite <- b0; auto.
elim (le_lt_eq_dec _ _ H); intro.
cut (pred i < pred n);
 [ intro | apply lt_pred; rewrite <- S_pred with i 0; auto ].
cut (auxP i <= pred (m + n)).
intro; exists H1.
elim le_lt_eq_dec; intro; simpl in |- *.
elim (le_lt_dec (auxP i) 0); intro; simpl in |- *.
cut (auxP i = 0); [ intro | auto with arith ].
rewrite <- auxP_lemma0 in H2.
cut (auxP 0 < auxP i); [ intro | apply auxP_lemma1; assumption ].
elimtype False; rewrite H2 in H3; apply (lt_irrefl _ H3).
generalize b1 a1; clear b1 a1.
rewrite (auxP_lemmai i b0 a0); intros.
simpl in |- *.
elim (ProjT2 (h_f' _ (lt_pred' i n b0 a0))); intros.
eapply eq_transitive_unfolded.
2: eapply eq_transitive_unfolded.
2: apply p.
unfold f' in |- *.
apply prf1; apply S_pred with 0; auto.
apply h_nlnf; reflexivity.
rewrite <- auxP_lemman in b1.
cut (i = n).
intro; elimtype False; rewrite H2 in a0; apply (lt_irrefl _ a0).
apply nat_mon_imp_inj with (h := auxP).
apply auxP_lemma1.
assumption.
unfold auxP in |- *.
elim (le_lt_dec i 0); intro; simpl in |- *.
apply le_O_n.
elim (le_lt_dec n i); intro; simpl in |- *.
elim (lt_irrefl n); apply le_lt_trans with i; auto.
apply plus_pred_pred_plus.
elim (ProjT2 (h_f' _ (lt_pred' i n b1 b2))); intros.
assumption.
generalize H; clear H; rewrite b1; intro.
rewrite auxP_lemman.
exists (le_n (pred (m + n))).
elim le_lt_eq_dec; intro; simpl in |- *.
elimtype False; apply (lt_irrefl _ a0).
apply finish.
Qed.

Lemma Separated_Refinement_lft : Refinement P Separated_Refinement.
clear auxR.
exists auxP; repeat split.
exact auxP_lemman.
intros; apply auxP_lemma1; assumption.
exact auxP_lemma2.
Qed.

Let auxR_lemma0 : auxR 0 = 0.
unfold auxR in |- *.
elim (le_lt_dec 0 0); intro; simpl in |- *.
reflexivity.
elimtype False; inversion b0.
Qed.

Let auxR_lemmai :
  forall (i : nat) (Hi : 0 < i) (Hi' : i < m),
  auxR i = S (ProjT1 (h_g' (pred i) (lt_pred' _ _ Hi Hi'))).
intros.
unfold auxR in |- *.
elim (le_lt_dec m i); intro; simpl in |- *.
elimtype False; apply le_not_lt with m i; auto.
elim (le_lt_dec i 0); intro; simpl in |- *.
elimtype False; apply lt_irrefl with 0; apply lt_le_trans with i; auto.
set (x := ProjT1 (h_g' _ (lt_pred' _ _ b1 b0))) in *.
set (y := ProjT1 (h_g' _ (lt_pred' _ _ Hi Hi'))) in *.
cut (x = y).
intro; auto with arith.
assert (H := ProjT2 (h_g' _ (lt_pred' _ _ b1 b0))).
assert (H0 := ProjT2 (h_g' _ (lt_pred' _ _ Hi Hi'))).
elim H; clear H; intros Hx Hx'.
elim H0; clear H0; intros Hy Hy'.
apply h_inj with Hx Hy.
eapply eq_transitive_unfolded.
2: apply Hy'.
eapply eq_transitive_unfolded.
apply eq_symmetric_unfolded; apply Hx'.
apply g'_nlnf; reflexivity.
Qed.

Let auxR_lemmam : auxR m = pred (m + n).
unfold auxR in |- *.
elim (le_lt_dec m 0); intro; simpl in |- *.
cut (m = 0); [ intro | auto with arith ].
transitivity (pred m).
rewrite H; auto.
cut (0 = n); [ intro; rewrite <- H0; auto | apply HP' ].
apply partition_length_zero with Hab; rewrite <- H; apply R.
elim (le_lt_dec m m); intro; simpl in |- *.
rewrite <- minus_n_n; auto.
elim (lt_irrefl _ b1).
Qed.

Let auxR_lemma1 : forall i j : nat, i < j -> auxR i < auxR j.
intros; unfold auxR in |- *.
elim (le_lt_dec i 0); intro.
elim (le_lt_dec j 0); intros; simpl in |- *.
apply le_lt_trans with i; try apply lt_le_trans with j; auto with arith.
elim (le_lt_dec m j); intros; simpl in |- *.
omega.
apply lt_O_Sn.
elim (le_lt_dec m i); elim (le_lt_dec j 0); intros; simpl in |- *.
elim (lt_irrefl 0); apply le_lt_trans with i; try apply lt_le_trans with j;
 auto with arith.
elim (le_lt_dec m j); intro; simpl in |- *.
apply plus_lt_compat_l.
apply plus_lt_reg_l with m.
repeat rewrite <- le_plus_minus; auto.
elim (le_not_lt m i); auto; apply lt_trans with j; auto.
elim (lt_irrefl 0); apply lt_trans with i; auto; apply lt_le_trans with j;
 auto.
elim (le_lt_dec m j); intro; simpl in |- *.
set (H0 := nm0) in *; set (H1 := mn0) in *;
 apply lt_le_trans with (S (pred m + pred n)).
apply lt_n_S.
apply (ProjT1 (ProjT2 (h_g' (pred i) (lt_pred' _ _ b0 b2)))).
rewrite <- plus_Sn_m.
rewrite <- S_pred with m 0.
2: apply lt_trans with i; auto.
replace (m + pred n) with (pred (m + n)).
auto with arith.
cut (S (pred (m + n)) = S (m + pred n)); auto.
rewrite plus_n_Sm.
rewrite <- S_pred with n 0; auto with arith.
symmetry  in |- *; apply S_pred with 0.
apply lt_le_trans with m; auto with arith.
apply lt_trans with i; auto.
apply neq_O_lt.
intro.
apply lt_irrefl with 0.
apply lt_trans with i; auto.
rewrite nm0; auto.
apply lt_n_S.
cut
 (~
  ~
  ProjT1 (h_g' (pred i) (lt_pred' _ _ b0 b2)) <
  ProjT1 (h_g' (pred j) (lt_pred' _ _ b1 b3))); intro.
apply not_not_lt; assumption.
cut
 (ProjT1 (h_g' (pred j) (lt_pred' _ _ b1 b3)) <=
  ProjT1 (h_g' (pred i) (lt_pred' _ _ b0 b2))); intros.
2: apply not_lt; assumption.
cut
 (h _ (ProjT1 (ProjT2 (h_g' (pred j) (lt_pred' _ _ b1 b3))))[<=]
  h _ (ProjT1 (ProjT2 (h_g' (pred i) (lt_pred' _ _ b0 b2))))).
intro.
2: apply h_mon'; assumption.
cut (g' (pred j) (lt_pred' _ _ b1 b3)[<=]g' (pred i) (lt_pred' _ _ b0 b2)).
2: apply
    leEq_wdl
     with (h _ (ProjT1 (ProjT2 (h_g' (pred j) (lt_pred' _ _ b1 b3))))).
2: apply
    leEq_wdr
     with (h _ (ProjT1 (ProjT2 (h_g' (pred i) (lt_pred' _ _ b0 b2))))).
2: assumption.
3: apply eq_symmetric_unfolded;
    exact (ProjT2 (ProjT2 (h_g' (pred j) (lt_pred' _ _ b1 b3)))).
2: apply eq_symmetric_unfolded;
    exact (ProjT2 (ProjT2 (h_g' (pred i) (lt_pred' _ _ b0 b2)))).
clear H2 H1; intro.
cut (g' _ (lt_pred' _ _ b0 b2)[<]g' _ (lt_pred' _ _ b1 b3)).
2: apply g'_mon.
2: apply lt_pred'; assumption.
intro.
elimtype False.
apply less_irreflexive_unfolded with (x := g' _ (lt_pred' _ _ b1 b3)).
eapply leEq_less_trans; [ apply H1 | apply X ].
Qed.

Let auxR_lemma2 :
  forall (j : nat) (H : j <= m),
  {H' : auxR j <= _ | R j H[=]Separated_Refinement _ H'}.
intros.
unfold Separated_Refinement in |- *; simpl in |- *.
unfold Separated_Refinement_fun in |- *; simpl in |- *.
elim (le_lt_dec j 0); intro; simpl in |- *.
cut (j = 0); [ intro | auto with arith ].
generalize H; clear a0 H; rewrite H0.
rewrite auxR_lemma0.
clear H0; intros.
exists (le_O_n (pred (m + n))).
elim le_lt_eq_dec; intro; simpl in |- *.
elim (le_lt_dec 0 0); intro; simpl in |- *.
apply start.
elimtype False; inversion b0.
apply eq_transitive_unfolded with a.
apply start.
apply partition_length_zero with Hab.
cut (m + n <= 1).
intros.
elim (plus_eq_one_imp_eq_zero _ _ H0); intro.
rewrite <- a0; apply R.
rewrite <- b1; apply P.
generalize b0; clear b0.
case (m + n).
auto.
intros.
simpl in b0; rewrite <- b0; auto.
elim (le_lt_eq_dec _ _ H); intro.
cut (pred j < pred m);
 [ intro | red in |- *; rewrite <- S_pred with j 0; auto; apply le_2; auto ].
cut (auxR j <= pred (m + n)).
intro; exists H1.
elim le_lt_eq_dec; intro; simpl in |- *.
elim (le_lt_dec (auxR j) 0); intro; simpl in |- *.
cut (auxR j = 0); [ intro | auto with arith ].
rewrite <- auxR_lemma0 in H2.
cut (auxR 0 < auxR j); [ intro | apply auxR_lemma1; assumption ].
elimtype False; rewrite H2 in H3; apply (lt_irrefl _ H3).
generalize b1 a1; clear b1 a1.
rewrite (auxR_lemmai j b0 a0); intros.
simpl in |- *.
elim (ProjT2 (h_g' _ (lt_pred' _ _ b0 a0))); intros.
eapply eq_transitive_unfolded.
2: eapply eq_transitive_unfolded.
2: apply p.
unfold g' in |- *.
apply prf1; apply S_pred with 0; auto.
apply h_nlnf; reflexivity.
rewrite <- auxR_lemmam in b1.
cut (j = m).
intro; elimtype False; rewrite H2 in a0; apply (lt_irrefl _ a0).
apply nat_mon_imp_inj with (h := auxR).
apply auxR_lemma1.
assumption.
unfold auxR in |- *.
elim (le_lt_dec j 0); intro; simpl in |- *.
apply le_O_n.
elim (le_lt_dec m j); intro; simpl in |- *.
rewrite not_le_minus_0.
rewrite <- plus_n_O; auto with arith.
apply lt_not_le; auto.
apply plus_pred_pred_plus.
elim (ProjT2 (h_g' _ (lt_pred' _ _ b1 b2))); intros.
assumption.
generalize H; clear H; rewrite b1; intro.
rewrite auxR_lemmam.
exists (le_n (pred (m + n))).
elim le_lt_eq_dec; intro; simpl in |- *.
elimtype False; apply (lt_irrefl _ a0).
apply finish.
Qed.

Lemma Separated_Refinement_rht : Refinement R Separated_Refinement.
exists auxR; repeat split.
exact auxR_lemmam.
intros; apply auxR_lemma1; assumption.
exact auxR_lemma2.
Qed.

End Refining_Separated.

(* end hide *)