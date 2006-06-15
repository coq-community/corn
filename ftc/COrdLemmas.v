(* $Id$ *)

Require Export COrdCauchy.

Section Lemmas.

(** *Lemmas for Integration

Here we include several lemmas valid in any ordered field [F] which 
are useful for integration.

** Merging orders

We first prove that any two strictly ordered sets of points which have
an empty intersection can be ordered as one (this will be the core of
the proof that any two partitions with no common point have a common
refinement).
*)

Variable F : COrdField.

Lemma om_fun_lt : forall m n : nat, S m < S n -> m < n.
auto with zarith.
Qed.

Definition om_fun n m (f : forall i, i < n -> F) (g : forall i, i < m -> F)
  (Hfg : forall i j Hi Hj, f i Hi [#] g j Hj) : forall i, i < m + n -> F.
intro n. induction  n as [| n Hrecn].
 intros. apply (g i). rewrite <- plus_n_O in H; auto.
intro m. induction  m as [| m Hrecm].
 do 3 intro. apply f.
intros.
elim (ap_imp_less _ _ _ (Hfg n m (lt_n_Sn n) (lt_n_Sn m))); intro.
 set (h := fun (i : nat) (Hi : i < m) => g i (lt_S _ _ Hi)) in *.
 elim (le_lt_eq_dec _ _ H); intro.
  apply Hrecm with (f := f) (g := h) (i := i); unfold h in |- *; auto.
  apply om_fun_lt; auto.
 apply (g m (lt_n_Sn m)).
clear Hrecm.
set (h := fun (i : nat) (Hi : i < n) => f i (lt_S _ _ Hi)) in *.
elim (le_lt_eq_dec _ _ H); intro.
 apply Hrecn with (f := h) (g := g) (i := i); unfold h in |- *; auto.
 apply om_fun_lt. rewrite plus_n_Sm. auto.
apply (f n (lt_n_Sn n)).
Defined.

Lemma om_fun_1 : forall n m f g Hfg,
 nat_less_n_fun f -> nat_less_n_fun g -> nat_less_n_fun (om_fun n m f g Hfg).
intro n. induction  n as [| n Hrecn].
 red in |- *; simpl in |- *; auto.
intro m; induction  m as [| m Hrecm].
 red in |- *; simpl in |- *; auto.
red in |- *; intros.
simpl in |- *; elim ap_imp_less; simpl in |- *; intro;
 repeat (elim le_lt_eq_dec; simpl in |- *; intro);
 try (elimtype False; auto with zarith; fail);
 try apply eq_reflexive_unfolded.
set (h := fun (i : nat) (Hi : i < m) => g i (lt_S _ _ Hi)) in *.
set (Hfh := fun i j Hi Hj => Hfg i j Hi (lt_S _ _ Hj)) in *.
assert (Hh : nat_less_n_fun h). red in |- *; unfold h in |- *; auto.
exact (Hrecm f h Hfh H Hh i j H1 (om_fun_lt _ _ a0) (om_fun_lt _ _ a1)).
apply Hrecn; try red in |- *; auto.
Qed.

Lemma om_fun_2a : forall n m f g Hfg (x : F), (forall i Hi, f i Hi [<] x) ->
 (forall i Hi, g i Hi [<] x) -> forall i Hi, om_fun n m f g Hfg i Hi [<] x.
intro n. induction  n as [| n Hrecn].
 simpl in |- *; auto.
intro m; induction  m as [| m Hrecm].
 simpl in |- *; auto.
intros.
simpl in |- *; elim ap_imp_less; simpl in |- *; intro; elim le_lt_eq_dec;
 simpl in |- *; intro; auto.
set (h := fun (i : nat) (Hi : i < m) => g i (lt_S _ _ Hi)) in *.
set (Hfh := fun i j Hi Hj => Hfg i j Hi (lt_S _ _ Hj)) in *.
set (Hh := fun i Hi => X0 i (lt_S _ _ Hi)) in *.
exact (Hrecm f h Hfh x X Hh i (om_fun_lt _ _ a0)).
Qed.

Lemma om_fun_2 : forall n m f g Hfg, nat_less_n_fun f -> nat_less_n_fun g ->
 (forall i i' Hi Hi', i < i' -> f i Hi [<] f i' Hi') -> (forall i i' Hi Hi', i < i' -> g i Hi [<] g i' Hi')
 -> forall i i' Hi Hi', i < i' -> om_fun n m f g Hfg i Hi [<] om_fun n m f g Hfg i' Hi'.
intro n. induction  n as [| n Hrecn].
 simpl in |- *; auto.
intro m; induction  m as [| m Hrecm].
 simpl in |- *; auto.
intros.
simpl in |- *; elim ap_imp_less; simpl in |- *; intro;
 repeat (elim le_lt_eq_dec; simpl in |- *; intro);
 try (elimtype False; auto with zarith; fail).
   set (h := fun (i : nat) (Hi : i < m) => g i (lt_S _ _ Hi)) in *.
   set (Hfh := fun i j Hi Hj => Hfg i j Hi (lt_S _ _ Hj)) in *.
   assert (Hh : nat_less_n_fun h). red in |- *; unfold h in |- *; auto.
   set
    (inch :=
     fun i i' Hi Hi' Hii' => X0 i i' (lt_S _ _ Hi) (lt_S _ _ Hi') Hii') 
    in *.
   exact
    (Hrecm f h Hfh H Hh X inch i i' (om_fun_lt _ _ a0) (om_fun_lt _ _ a1) H1).
  set (h := fun (i : nat) (Hi : i < m) => g i (lt_S _ _ Hi)) in *.
  set (Hfh := fun i j Hi Hj => Hfg i j Hi (lt_S _ _ Hj)) in *.
  assert (Hh : nat_less_n_fun h). red in |- *; unfold h in |- *; auto.
  refine (om_fun_2a _ _ f h Hfh (g m (lt_n_Sn m)) _ _ i (om_fun_lt _ _ a0)).
   intros j Hj. elim (le_lt_eq_dec _ _ Hj); intro.
    apply less_transitive_unfolded with (f n (lt_n_Sn n)); auto with arith.
   apply less_wdl with (f n (lt_n_Sn n)); auto.
   apply H; auto. inversion b0. auto.
  unfold h in |- *; auto.
 apply Hrecn; auto. red in |- *; auto.
apply om_fun_2a; auto.
intros j Hj. elim (le_lt_eq_dec _ _ Hj); intro.
 apply less_transitive_unfolded with (g m (lt_n_Sn m)); auto with arith.
apply less_wdl with (g m (lt_n_Sn m)); auto.
apply H0; auto. inversion b1. auto.
Qed.

Lemma om_fun_3a : forall n m f g Hfg, nat_less_n_fun f -> nat_less_n_fun g ->
 forall i Hi, {j : nat | {Hj : j < m + n | f i Hi [=] om_fun n m f g Hfg j Hj}}.
intro n. induction  n as [| n Hrecn].
 simpl in |- *; intros. elimtype False; inversion Hi.
intro m; induction  m as [| m Hrecm].
 simpl in |- *; intros. exists i. exists Hi. algebra.
intros.
simpl in |- *; elim ap_imp_less; simpl in |- *; intro.
 set (h := fun i Hi => g i (lt_S _ _ Hi)) in *.
 set (Hfh := fun i j Hi Hj => Hfg i j Hi (lt_S _ _ Hj)) in *.
 assert (Hh : nat_less_n_fun h). red in |- *; unfold h in |- *; auto.
 elim (Hrecm f h Hfh H Hh i Hi); intros j Hj.
 elim Hj; clear Hj; intros Hj Hj'.
 exists j; exists (lt_S _ _ Hj).
 elim le_lt_eq_dec; simpl in |- *; intro.
  astepl (om_fun _ _ f h Hfh _ Hj).
  refine (om_fun_1 _ _ f h Hfh H Hh j j _ Hj (om_fun_lt _ _ a0)). auto.
 elimtype False; auto with zarith.
elim (le_lt_eq_dec _ _ Hi); intro.
 set (h := fun i Hi => f i (lt_S _ _ Hi)) in *.
 set (Hfh := fun i j Hi Hj => Hfg i j (lt_S _ _ Hi) Hj) in *.
 assert (Hh : nat_less_n_fun h). red in |- *; unfold h in |- *; auto.
 elim (Hrecn _ h g Hfh Hh H0 i (om_fun_lt _ _ a)); intros j Hj.
 elim Hj; clear Hj; intros Hj Hj'.
 cut (j < S (m + S n)). intro. 2: auto with zarith.
 exists j; exists H1.
 elim le_lt_eq_dec; simpl in |- *; intro.
  eapply eq_transitive_unfolded. eapply eq_transitive_unfolded. 2: apply Hj'.
   unfold h in |- *; apply H; auto.
  apply om_fun_1; auto.
 elimtype False; auto with zarith.
exists (m + S n). exists (lt_n_Sn (m + S n)).
elim le_lt_eq_dec; simpl in |- *; intro.
 elimtype False; auto with zarith.
apply H. inversion b0. auto.
Qed.

Lemma om_fun_3b : forall n m f g Hfg, nat_less_n_fun f -> nat_less_n_fun g ->
 forall i Hi, {j : nat | {Hj : j < m + n | g i Hi [=] om_fun n m f g Hfg j Hj}}.
intro n. induction  n as [| n Hrecn].
 simpl in |- *; intros. exists i.
 assert (i < m + 0). rewrite <- plus_n_O. auto.
 exists H1. algebra.
intro m; induction  m as [| m Hrecm].
 simpl in |- *; intros. elimtype False; inversion Hi.
intros.
simpl in |- *; elim ap_imp_less; simpl in |- *; intro.
 elim (le_lt_eq_dec _ _ Hi); intro.
  set (h := fun i Hi => g i (lt_S _ _ Hi)) in *.
  set (Hfh := fun i j Hi Hj => Hfg i j Hi (lt_S _ _ Hj)) in *.
  assert (Hh : nat_less_n_fun h). red in |- *; unfold h in |- *; auto.
  elim (Hrecm f h Hfh H Hh i (om_fun_lt _ _ a0)); intros j Hj.
  elim Hj; clear Hj; intros Hj Hj'.
  exists j; exists (lt_S _ _ Hj).
  elim le_lt_eq_dec; simpl in |- *; intro.
   eapply eq_transitive_unfolded. eapply eq_transitive_unfolded. 2: apply Hj'.
    unfold h in |- *; apply H0; auto.
   refine (om_fun_1 _ _ f h Hfh H Hh j j _ Hj (om_fun_lt _ _ a1)). auto.
  elimtype False; auto with zarith.
 exists (m + S n). exists (lt_n_Sn (m + S n)).
 elim le_lt_eq_dec; simpl in |- *; intro.
  elimtype False; auto with zarith.
 apply H0. inversion b. auto.
set (h := fun i Hi => f i (lt_S _ _ Hi)) in *.
set (Hfh := fun i j Hi Hj => Hfg i j (lt_S _ _ Hi) Hj) in *.
assert (Hh : nat_less_n_fun h). red in |- *; unfold h in |- *; auto.
elim (Hrecn _ h g Hfh Hh H0 i Hi); intros j Hj.
elim Hj; clear Hj; intros Hj Hj'.
cut (j < S (m + S n)). intro. 2: auto with zarith.
exists j; exists H1.
elim le_lt_eq_dec; simpl in |- *; intro.
 eapply eq_transitive_unfolded. apply Hj'. apply om_fun_1; auto.
elimtype False; auto with zarith.
Qed.

Lemma om_fun_4a : forall n m f g Hfg (P : F -> CProp), pred_wd F P ->
 (forall i Hi, P (f i Hi)) -> (forall j Hj, P (g j Hj)) -> forall k Hk, P (om_fun n m f g Hfg k Hk).
intro n. induction  n as [| n Hrecn].
 simpl in |- *; auto.
intro m; induction  m as [| m Hrecm].
 simpl in |- *; auto.
intros.
simpl in |- *; elim ap_imp_less; simpl in |- *; intro; elim le_lt_eq_dec;
 simpl in |- *; intro; auto.
 set (h := fun i Hi => g i (lt_S _ _ Hi)) in *.
 set (Hfh := fun i j Hi Hj => Hfg i j Hi (lt_S _ _ Hj)) in *.
 set (Hh := fun i Hi => X1 i (lt_S _ _ Hi)) in *.
 exact (Hrecm f h Hfh P X X0 Hh k (om_fun_lt _ _ a0)).
apply Hrecn; auto.
Qed.

Lemma om_fun_4b : forall n m f g Hfg (P : F -> Prop), pred_wd' F P ->
 (forall i Hi, P (f i Hi)) -> (forall j Hj, P (g j Hj)) -> forall k Hk, P (om_fun n m f g Hfg k Hk).
intro n. induction  n as [| n Hrecn].
 simpl in |- *; auto.
intro m; induction  m as [| m Hrecm].
 simpl in |- *; auto.
intros.
simpl in |- *; elim ap_imp_less; simpl in |- *; intro; elim le_lt_eq_dec;
 simpl in |- *; intro; auto.
 set (h := fun i Hi => g i (lt_S _ _ Hi)) in *.
 set (Hfh := fun i j Hi Hj => Hfg i j Hi (lt_S _ _ Hj)) in *.
 set (Hh := fun i Hi => H1 i (lt_S _ _ Hi)) in *.
 exact (Hrecm f h Hfh P H H0 Hh k (om_fun_lt _ _ a0)).
apply Hrecn; auto.
Qed.

Lemma om_fun_4c : forall n m f g Hfg (P : F -> CProp), pred_wd F P ->
 nat_less_n_fun f -> nat_less_n_fun g ->
 {i : nat | {Hi : i < n | P (f i Hi)}} or {j : nat | {Hj : j < m | P (g j Hj)}} ->
 {k : nat | {Hk : k < m + n | P (om_fun n m f g Hfg k Hk)}}.
intros n m f g Hfg P HP Hf Hg H.
elim H; intro H'; elim H'; intros i Hi; elim Hi; clear H H' Hi; intros Hi Hi'.
 elim (om_fun_3a _ _ _ _ Hfg Hf Hg i Hi). intros j Hj. elim Hj; clear Hj.
 intros Hj Hj'.
 exists j; exists Hj; apply HP with (x := f i Hi); auto.
elim (om_fun_3b _ _ _ _ Hfg Hf Hg i Hi). intros j Hj. elim Hj; clear Hj.
intros Hj Hj'.
exists j; exists Hj; apply HP with (x := g i Hi); auto.
Qed.

Lemma om_fun_4d : forall n m f g Hfg (P : F -> Prop), pred_wd' F P ->
 nat_less_n_fun f -> nat_less_n_fun g ->
 {i : nat | {Hi : i < n | P (f i Hi)}} or {j : nat | {Hj : j < m | P (g j Hj)}} ->
 {k : nat | {Hk : k < m + n | P (om_fun n m f g Hfg k Hk)}}.
intros n m f g Hfg P HP Hf Hg H.
elim H; intro H'; elim H'; intros i Hi; elim Hi; clear H H' Hi; intros Hi Hi'.
 elim (om_fun_3a _ _ _ _ Hfg Hf Hg i Hi). intros j Hj. elim Hj; clear Hj.
 intros Hj Hj'.
 exists j; exists Hj; apply HP with (x := f i Hi); auto.
elim (om_fun_3b _ _ _ _ Hfg Hf Hg i Hi). intros j Hj. elim Hj; clear Hj.
intros Hj Hj'.
exists j; exists Hj; apply HP with (x := g i Hi); auto.
Qed.

(* begin hide *)
Variable f : nat -> nat.
Hypothesis f0 : f 0 = 0.
Hypothesis f_mon : forall i j : nat, i < j -> f i < f j.

Variable h : nat -> F.
(* end hide *)

(** ** Summations
Also, some technical stuff on sums.  The first lemma relates two
different kinds of sums; the other two ones are variations, where the
structure of the arguments is analyzed in more detail.
*)

(* begin show *)
Lemma Sumx_Sum_Sum
 (* end show *)
 (* begin hide *)
 : forall n,
 Sumx (fun i (H : i < n) => Sum (f i) (pred (f (S i))) h) [=]
   Sumx (fun i (H : i < f n) => h i).
simple induction n.
rewrite f0; simpl in |- *; algebra.
clear n; intros.
elim (le_lt_dec n 0); intro.
cut (n = 0); [ clear a; intro | auto with arith ].
rewrite H0 in H.
rewrite H0.
simpl in |- *.
astepl (Sum (f 0) (pred (f 1)) h).
rewrite f0.
apply eq_symmetric_unfolded.
eapply eq_transitive_unfolded.
apply Sumx_to_Sum.
pattern 0 at 1 in |- *; rewrite <- f0; apply f_mon; apply lt_n_Sn.
red in |- *; intros.
rewrite H1; algebra.
clear H; apply Sum_wd'; unfold part_tot_nat_fun in |- *.
auto with arith.
intros.
elim (le_lt_dec (f 1) i); intro; simpl in |- *.
cut (0 < f 1).
intro; elimtype False; omega.
pattern 0 at 1 in |- *; rewrite <- f0; apply f_mon; apply lt_n_Sn.
algebra.
cut (0 < f n); [ intro | rewrite <- f0; apply f_mon; assumption ].
simpl in |- *.
eapply eq_transitive_unfolded.
2: apply eq_symmetric_unfolded; apply Sumx_to_Sum.
apply
 eq_transitive_unfolded
  with
    (Sum 0 (pred (f n))
       (part_tot_nat_fun _ _ (fun (i : nat) (H : i < f n) => h i)) [+]
     Sum (f n) (pred (f (S n))) h).
apply bin_op_wd_unfolded.
eapply eq_transitive_unfolded.
apply H.
apply Sumx_to_Sum.
assumption.
red in |- *; intros.
rewrite H1; algebra.
algebra.
cut (f n = S (pred (f n))); [ intro | apply S_pred with 0; auto ].
pattern (f n) at 4 in |- *; rewrite H1.
eapply eq_transitive_unfolded.
2: apply Sum_Sum with (m := pred (f n)).
apply bin_op_wd_unfolded; apply Sum_wd'.
rewrite <- H1; apply lt_le_weak; assumption.
intros; unfold part_tot_nat_fun in |- *.
elim (le_lt_dec (f n) i); intro; simpl in |- *.
elimtype False; omega.
elim (le_lt_dec (f (S n)) i); intro; simpl in |- *.
cut (f n < f (S n)); [ intro | apply f_mon; apply lt_n_Sn ].
elimtype False; apply (le_not_lt (f n) i); auto.
apply le_trans with (f (S n)); auto with arith.
algebra.
rewrite <- H1.
cut (0 < f (S n)); [ intro | rewrite <- f0; auto with arith ].
cut (f (S n) = S (pred (f (S n)))); [ intro | apply S_pred with 0; auto ].
rewrite <- H3.
apply lt_le_weak; auto with arith.
intros.
unfold part_tot_nat_fun in |- *.
elim (le_lt_dec (f (S n)) i); intro; simpl in |- *.
elimtype False; omega.
algebra.
apply lt_trans with (f n); auto with arith.
red in |- *; intros.
rewrite H1; algebra.
Qed.
(* end hide *)

(* begin show *)
Lemma str_Sumx_Sum_Sum
 (* end show *)
 (* begin hide *)
 :
 forall n (g : (forall i Hi, nat -> F)),
 (forall i j Hi, f i <= j -> j < f (S i) -> g i Hi j [=] h j) ->
 forall m, m = f n ->
 Sumx (fun i (H : i < n) => Sum (f i) (pred (f (S i))) (g i H)) [=]
 Sumx (fun i (H : i < m) => h i).
intros.
rewrite H0.
eapply eq_transitive_unfolded.
2: apply Sumx_Sum_Sum.
apply Sumx_wd.
intros.
apply Sum_wd'.
cut (0 < f (S i)); [ intro | rewrite <- f0; auto with arith ].
cut (f (S i) = S (pred (f (S i)))); [ intro | apply S_pred with 0; auto ].
rewrite <- H3.
apply lt_le_weak; auto with arith.
intros; apply H.
assumption.
rewrite (S_pred (f (S i)) 0); auto with arith.
rewrite <- f0; auto with arith.
Qed.

End Lemmas.

Section More_Lemmas.

Let f' (m : nat) (f : forall i, i <= m -> nat) : nat -> nat.
intros m f i.
elim (le_lt_dec i m); intro.
apply (f i a).
apply (f m (le_n m) + i).
Defined.
(* end hide *)

Variable F : COrdField.

(* begin show *)
Lemma str_Sumx_Sum_Sum'
 (* end show *)
 (* begin hide *)
 :
 forall (m : nat) (f : forall i, i <= m -> nat),
 f 0 (le_O_n _) = 0 ->
 (forall (i j : nat) Hi Hj, i = j -> f i Hi = f j Hj) ->
 (forall (i j : nat) Hi Hj, i < j -> f i Hi < f j Hj) ->
 forall (h : nat -> F) (n : nat) (g : forall i : nat, i < m -> nat -> F),
 (forall (i j : nat) Hi Hi' Hi'',
  f i Hi' <= j -> j < f (S i) Hi'' -> g i Hi j [=] h j) ->
 (forall H, n = f m H) ->
 Sumx
   (fun (i : nat) (H : i < m) =>
    Sum (f i (lt_le_weak _ _ H)) (pred (f (S i) H)) (g i H)) [=] 
 Sumx (fun (i : nat) (_ : i < n) => h i).
intros.
cut (forall (i : nat) (H : i <= m), f i H = f' m f i).
intros.
apply
 eq_transitive_unfolded
  with
    (Sumx
       (fun (i : nat) (H3 : i < m) =>
        Sum (f' m f i) (pred (f' m f (S i))) (g i H3))).
apply Sumx_wd; intros.
rewrite <- (H4 i (lt_le_weak _ _ H5)); rewrite <- (H4 (S i) H5);
 apply Sum_wd'.
rewrite <-
 (S_pred (f (S i) H5) (f i (lt_le_weak _ _ H5)) (H1 _ _ _ _ (lt_n_Sn i)))
 .
apply lt_le_weak; apply H1; apply lt_n_Sn.
intros; algebra.
apply str_Sumx_Sum_Sum.
unfold f' in |- *; simpl in |- *.
elim (le_lt_dec 0 m); intro; simpl in |- *.
transitivity (f 0 (le_O_n m)).
apply H0; auto.
apply H.
elimtype False; inversion b.
intros; apply nat_local_mon_imp_mon.
clear H5 j i; intros.
unfold f' in |- *.
elim (le_lt_dec i m); elim (le_lt_dec (S i) m); intros; simpl in |- *.
apply H1; apply lt_n_Sn.
cut (i = m); [ intro | apply le_antisym; auto with arith ].
generalize a; clear a; pattern i at 1 2 in |- *; rewrite H5; intro.
set (x := f m a) in *.
cut (x = f m (le_n m)).
2: unfold x in |- *; apply H0; auto.
intro.
rewrite <- H6.
rewrite <- plus_n_Sm; auto with arith.
elimtype False; apply (le_not_lt i m); auto with arith.
set (x := f m (le_n m)) in *; clearbody x; auto with arith.
assumption.
intros.
apply H2 with (Hi' := lt_le_weak _ _ Hi) (Hi'' := Hi).
rewrite H4; assumption.
rewrite H4; assumption.
unfold f' in |- *.
elim (le_lt_dec m m); intro; simpl in |- *.
apply H3.
elim (lt_irrefl _ b).
clear H3 H2 g n h; intros.
unfold f' in |- *.
elim (le_lt_dec i m); intro; simpl in |- *.
apply H0; auto.
elim (le_not_lt i m); auto.
Qed.
(* end hide *)

End More_Lemmas.
