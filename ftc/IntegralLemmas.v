(* $Id$ *)

Require Export Partitions.

Section Lemmas.

(** *Lemmas for Integration

In this file we prepare the way for the definition of integral with lots of (very) technical stuff.

%\begin{convention}% Throughout this section, let [a,b:IR] and [I] be $[a,b]$#[a,b]#.
%\end{convention}%

** Lemmas

We first prove that any two strictly ordered sets of points which have an empty intersection can be ordered as one (this will be the core of the proof that any two partitions with no common point have a common refinement).
*)

Definition pred_well_def' (S : CSetoid) (P : S -> Prop) :=
  forall x y : S, P x -> x[=]y -> P y.

Variable F : COrdField.

(*
Section Ordered_Insertion.

Definition oi_fun [n:nat][f:(i:nat)(lt i n)->F]
  [x:F][Hx:((i:nat)(Hi:(lt i n))(f i Hi) [#] x)] : (i:nat)(lt i (S n))->F.
Intro n; Induction n.
 Intros. Apply x.
Do 3 Intro.
Assert Hxn := (Hx n (lt_n_Sn n)).
Elim (ap_imp_less ??? Hxn); Intro H0.
 Intros i Hi.
 Elim (le_lt_eq_dec ?? Hi); Intro.
  Cut (lt i (S n)); [Intro | Auto with arith].
  Apply (f i H).
 Apply x.
LetTac g:=[i:nat][Hi:(lt i n)](f i (lt_S ?? Hi)).
Intros i Hi.
Elim (le_lt_eq_dec ?? Hi); Intro.
 Apply (Hrecn g x) with i.
  Unfold g; Auto.
 Auto with arith.
Apply (f n (lt_n_Sn n)).
Defined.

Lemma oi_fun_1 : (n,f,x,Hx:?)
  (nat_less_n_fun ?? f)->(nat_less_n_fun ?? (oi_fun n f x Hx)).
Intro n; Induction n.
 Intros; Red; Intros; Algebra.
Intros; Simpl.
Elim ap_imp_less; Simpl; Red; Intros; Elim le_lt_eq_dec; Simpl; Elim le_lt_eq_dec; Simpl; Intros; Algebra; Try (ElimType False; Auto with zarith; Fail).
Apply Hrecn; Auto. Red; Intros; Auto.
Qed.

Lemma oi_fun_2a : (n,f,x,Hx:?)(y:F)(x[<]y)->
  ((i,Hi:?)(f i Hi)[<]y)->(i,Hi:?)(oi_fun n f x Hx i Hi)[<]y.
Intro n; Induction n.
 Auto.
Intros; Simpl; Elim ap_imp_less; Simpl; Elim le_lt_eq_dec; Simpl; Auto.
Qed.

Lemma oi_fun_2 : (n:nat;f:(i:nat)(lt i n)->F)(x,Hx:?)
 (nat_less_n_fun ?? f)->
 ((i,i':nat)(Hi:(lt i n))(Hi':(lt i' n))(lt i i')->((f i Hi) [<] (f i' Hi')))->
  ((i,i':nat)(Hi,Hi':?)(lt i i')->
  ((oi_fun n f x Hx i Hi) [<] (oi_fun n f x Hx i' Hi'))).
Intro n; Induction n.
 Intros. ElimType False; Auto with zarith.
Intros; Simpl.
Elim ap_imp_less; Simpl; Elim le_lt_eq_dec; Simpl; Elim le_lt_eq_dec; Simpl; Intros; Try (ElimType False; Auto with zarith; Fail).
   Auto.
  Elim (le_lt_eq_dec ?? a); Intro.
   Apply less_transitive_unfolded with (f n (lt_n_Sn n)); Auto with zarith.
  Generalize a. Inversion b0. Rewrite H2. Intro.
  EApply less_wdl. Apply a0. Apply H; Auto.
 Apply Hrecn; Auto. Red; Intros; Auto.
Apply oi_fun_2a; Auto.
Qed.

Lemma oi_fun_3a : (n,f,x,Hx:?)(P:F->Prop)(pred_well_def' F P)->
  ((i:nat)(Hi:(lt i n))(P (f i Hi)))->(P x)->(j:nat)(Hj:(lt j (S n)))
  (P (oi_fun n f x Hx j Hj)).
Intro n; Induction n.
 Auto.
Intros; Simpl; Elim ap_imp_less; Simpl; Elim le_lt_eq_dec; Simpl; Auto.
Intros; Apply Hrecn; Auto.
Qed.

Lemma oi_fun_3b : (n,f,x,Hx:?)(P:F->CProp)(pred_well_def F P)->
  ((i:nat)(Hi:(lt i n))(P (f i Hi)))->(P x)->(j:nat)(Hj:(lt j (S n)))
  (P (oi_fun n f x Hx j Hj)).
Intro n; Induction n.
 Auto.
Intros; Simpl; Elim ap_imp_less; Simpl; Elim le_lt_eq_dec; Simpl; Auto.
Intros; Apply Hrecn; Auto.
Qed.

Lemma oi_fun_4a : (n,f,x,Hx:?)(P:F->Prop)(pred_well_def' F P)->
  {i:nat | (lt i n) | (Hi:?)(P (f i Hi))}->
    {j:nat | (lt j (S n)) | (Hj:?)(P (oi_fun n f x Hx j Hj))}.
Intro n; Induction n; Intros f x Hx P HP H.
 ElimType False; Elim H; Intros i Hi. Inversion Hi.
Elim H; Clear H; Intros i Hi Hi''.
Simpl; Elim ap_imp_less; Simpl; Intro.
 Exists i. Auto. Intro; Elim le_lt_eq_dec; Simpl. Auto.
 Intro. ElimType False. Auto with zarith.
Elim (le_lt_eq_dec ?? Hi); Intro.
 LetTac g:=[i:nat][Hi:(lt i n)](f i (lt_S ?? Hi)).
 Assert Hg:=[i:nat; Hi:(lt i n)](Hx i (lt_S i n Hi)).
 Cut (lt i n); [Intro | Auto with arith].
 Elim (Hrecn g x Hg P HP). Intros j Hj Hj'.
  Exists j. Auto.
  Intro; Simpl; Elim le_lt_eq_dec; Simpl; Intros. Auto.
  ElimType False; Auto with zarith.
 Exists i; Unfold g; Auto.
Exists (S n). Auto.
Intro. Elim le_lt_eq_dec; Simpl.
 Intro. ElimType False; Auto with zarith.
Intro. Inversion b0. Rewrite H0 in Hi''. Auto.
Qed.

Lemma oi_fun_4b : (n,f,x,Hx:?)(P:F->CProp)(pred_well_def F P)->
  {i:nat | (lt i n) | (Hi:?)(P (f i Hi))}->
    {j:nat | (lt j (S n)) | (Hj:?)(P (oi_fun n f x Hx j Hj))}.
Intro n; Induction n; Intros f x Hx P HP H.
 ElimType False; Elim H; Intros i Hi. Inversion Hi.
Elim H; Clear H; Intros i Hi Hi''.
Simpl; Elim ap_imp_less; Simpl; Intro.
 Exists i. Auto. Intro; Elim le_lt_eq_dec; Simpl. Auto.
 Intro. ElimType False. Auto with zarith.
Elim (le_lt_eq_dec ?? Hi); Intro.
 LetTac g:=[i:nat][Hi:(lt i n)](f i (lt_S ?? Hi)).
 Assert Hg:=[i:nat; Hi:(lt i n)](Hx i (lt_S i n Hi)).
 Cut (lt i n); [Intro | Auto with arith].
 Elim (Hrecn g x Hg P HP). Intros j Hj Hj'.
  Exists j. Auto.
  Intro; Simpl; Elim le_lt_eq_dec; Simpl; Intros. Auto.
  ElimType False; Auto with zarith.
 Exists i; Unfold g; Auto.
Exists (S n). Auto.
Intro. Elim le_lt_eq_dec; Simpl.
 Intro. ElimType False; Auto with zarith.
Intro. Inversion b0. Rewrite H0 in Hi''. Auto.
Qed.

Lemma oi_fun_4c : (n,f,x,Hx:?)(P:F->Prop)(P x)->
    {j:nat | (lt j (S n)) | (Hj:?)(P (oi_fun n f x Hx j Hj))}.
Intro n; Induction n; Intros f x Hx P H.
 Exists (0); Auto.
Simpl; Elim ap_imp_less; Simpl; Intro.
 Exists (S n). Auto. Intro; Elim le_lt_eq_dec; Simpl; Auto.
 Intro. ElimType False. Auto with zarith.
LetTac g:=[i:nat][Hi:(lt i n)](f i (lt_S ?? Hi)).
Assert Hg:=[i:nat; Hi:(lt i n)](Hx i (lt_S i n Hi)).
Elim (Hrecn g x Hg P). Intros j Hj Hj'.
 Exists j. Auto.
 Intro; Simpl; Elim le_lt_eq_dec; Simpl; Intros. Auto.
 ElimType False; Auto with zarith.
Auto.
Qed.

Lemma oi_fun_4d : (n,f,x,Hx:?)(P:F->CProp)(P x)->
    {j:nat | (lt j (S n)) | (Hj:?)(P (oi_fun n f x Hx j Hj))}.
Intro n; Induction n; Intros f x Hx P H.
 Exists (0); Auto.
Simpl; Elim ap_imp_less; Simpl; Intro.
 Exists (S n). Auto. Intro; Elim le_lt_eq_dec; Simpl; Auto.
 Intro. ElimType False. Auto with zarith.
LetTac g:=[i:nat][Hi:(lt i n)](f i (lt_S ?? Hi)).
Assert Hg:=[i:nat; Hi:(lt i n)](Hx i (lt_S i n Hi)).
Elim (Hrecn g x Hg P). Intros j Hj Hj'.
 Exists j. Auto.
 Intro; Simpl; Elim le_lt_eq_dec; Simpl; Intros. Auto.
 ElimType False; Auto with zarith.
Auto.
Qed.

End Ordered_Insertion.
*)

Section Ordered_Merge.

Lemma om_fun_lt : forall m n : nat, S m < S n -> m < n.
auto with zarith.
Qed.

Definition om_fun (n m : nat) (f : forall i : nat, i < n -> F)
  (g : forall i : nat, i < m -> F)
  (Hfg : forall (i j : nat) Hi Hj, f i Hi[#]g j Hj) :
  forall i : nat, i < m + n -> F.
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

Lemma om_fun_1 :
 forall n m f g Hfg,
 nat_less_n_fun _ _ f ->
 nat_less_n_fun _ _ g -> nat_less_n_fun _ _ (om_fun n m f g Hfg).
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
assert (Hh : nat_less_n_fun _ _ h). red in |- *; unfold h in |- *; auto.
exact (Hrecm f h Hfh H Hh i j H1 (om_fun_lt _ _ a0) (om_fun_lt _ _ a1)).
apply Hrecn; try red in |- *; auto.
Qed.

Lemma om_fun_2a :
 forall n m f g Hfg (x : F),
 (forall (i : nat) Hi, f i Hi[<]x) ->
 (forall (i : nat) Hi, g i Hi[<]x) ->
 forall (i : nat) Hi, om_fun n m f g Hfg i Hi[<]x.
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

Lemma om_fun_2 :
 forall n m f g Hfg,
 nat_less_n_fun _ _ f ->
 nat_less_n_fun _ _ g ->
 (forall (i i' : nat) Hi Hi', i < i' -> f i Hi[<]f i' Hi') ->
 (forall (i i' : nat) Hi Hi', i < i' -> g i Hi[<]g i' Hi') ->
 forall (i i' : nat) Hi Hi',
 i < i' -> om_fun n m f g Hfg i Hi[<]om_fun n m f g Hfg i' Hi'.
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
   assert (Hh : nat_less_n_fun _ _ h). red in |- *; unfold h in |- *; auto.
   set
    (inch :=
     fun i i' Hi Hi' Hii' => X0 i i' (lt_S _ _ Hi) (lt_S _ _ Hi') Hii') 
    in *.
   exact
    (Hrecm f h Hfh H Hh X inch i i' (om_fun_lt _ _ a0) (om_fun_lt _ _ a1) H1).
  set (h := fun (i : nat) (Hi : i < m) => g i (lt_S _ _ Hi)) in *.
  set (Hfh := fun i j Hi Hj => Hfg i j Hi (lt_S _ _ Hj)) in *.
  assert (Hh : nat_less_n_fun _ _ h). red in |- *; unfold h in |- *; auto.
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

Lemma om_fun_3a :
 forall n m f g Hfg,
 nat_less_n_fun _ _ f ->
 nat_less_n_fun _ _ g ->
 forall (i : nat) (Hi : i < n),
 {j : nat | {Hj : j < m + n | f i Hi[=]om_fun n m f g Hfg j Hj}}.
intro n. induction  n as [| n Hrecn].
 simpl in |- *; intros. elimtype False; inversion Hi.
intro m; induction  m as [| m Hrecm].
 simpl in |- *; intros. exists i. exists Hi. Algebra.
intros.
simpl in |- *; elim ap_imp_less; simpl in |- *; intro.
 set (h := fun i Hi => g i (lt_S _ _ Hi)) in *.
 set (Hfh := fun i j Hi Hj => Hfg i j Hi (lt_S _ _ Hj)) in *.
 assert (Hh : nat_less_n_fun _ _ h). red in |- *; unfold h in |- *; auto.
 elim (Hrecm f h Hfh H Hh i Hi); intros j Hj.
 elim Hj; clear Hj; intros Hj Hj'.
 exists j; exists (lt_S _ _ Hj).
 elim le_lt_eq_dec; simpl in |- *; intro.
  AStepl (om_fun _ _ f h Hfh _ Hj).
  refine (om_fun_1 _ _ f h Hfh H Hh j j _ Hj (om_fun_lt _ _ a0)). auto.
 elimtype False; auto with zarith.
elim (le_lt_eq_dec _ _ Hi); intro.
 set (h := fun i Hi => f i (lt_S _ _ Hi)) in *.
 set (Hfh := fun i j Hi Hj => Hfg i j (lt_S _ _ Hi) Hj) in *.
 assert (Hh : nat_less_n_fun _ _ h). red in |- *; unfold h in |- *; auto.
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

Lemma om_fun_3b :
 forall n m f g Hfg,
 nat_less_n_fun _ _ f ->
 nat_less_n_fun _ _ g ->
 forall (i : nat) (Hi : i < m),
 {j : nat | {Hj : j < m + n | g i Hi[=]om_fun n m f g Hfg j Hj}}.
intro n. induction  n as [| n Hrecn].
 simpl in |- *; intros. exists i.
 assert (i < m + 0). rewrite <- plus_n_O. auto.
 exists H1. Algebra.
intro m; induction  m as [| m Hrecm].
 simpl in |- *; intros. elimtype False; inversion Hi.
intros.
simpl in |- *; elim ap_imp_less; simpl in |- *; intro.
 elim (le_lt_eq_dec _ _ Hi); intro.
  set (h := fun i Hi => g i (lt_S _ _ Hi)) in *.
  set (Hfh := fun i j Hi Hj => Hfg i j Hi (lt_S _ _ Hj)) in *.
  assert (Hh : nat_less_n_fun _ _ h). red in |- *; unfold h in |- *; auto.
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
assert (Hh : nat_less_n_fun _ _ h). red in |- *; unfold h in |- *; auto.
elim (Hrecn _ h g Hfh Hh H0 i Hi); intros j Hj.
elim Hj; clear Hj; intros Hj Hj'.
cut (j < S (m + S n)). intro. 2: auto with zarith.
exists j; exists H1.
elim le_lt_eq_dec; simpl in |- *; intro.
 eapply eq_transitive_unfolded. apply Hj'. apply om_fun_1; auto.
elimtype False; auto with zarith.
Qed.

Lemma om_fun_4a :
 forall n m f g Hfg (P : F -> CProp),
 pred_well_def F P ->
 (forall (i : nat) (Hi : i < n), P (f i Hi)) ->
 (forall (j : nat) (Hj : j < m), P (g j Hj)) ->
 forall (k : nat) (Hk : k < m + n), P (om_fun n m f g Hfg k Hk).
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

Lemma om_fun_4b :
 forall n m f g Hfg (P : F -> Prop),
 pred_well_def' F P ->
 (forall (i : nat) (Hi : i < n), P (f i Hi)) ->
 (forall (j : nat) (Hj : j < m), P (g j Hj)) ->
 forall (k : nat) (Hk : k < m + n), P (om_fun n m f g Hfg k Hk).
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

Lemma om_fun_4c :
 forall n m f g Hfg (P : F -> CProp),
 pred_well_def F P ->
 nat_less_n_fun _ _ f ->
 nat_less_n_fun _ _ g ->
 {i : nat | {Hi : i < n | P (f i Hi)}}
 or {j : nat | {Hj : j < m | P (g j Hj)}} ->
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

Lemma om_fun_4d :
 forall n m f g Hfg (P : F -> Prop),
 pred_well_def' F P ->
 nat_less_n_fun _ _ f ->
 nat_less_n_fun _ _ g ->
 {i : nat | {Hi : i < n | P (f i Hi)}}
 or {j : nat | {Hj : j < m | P (g j Hj)}} ->
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

End Ordered_Merge.

(*
Lemma can_be_ordered
 : (m,n:nat)(f:(i:nat)(lt i n)->F)(g:(j:nat)(lt j m)->F)(nat_less_n_fun ?? f)->(nat_less_n_fun ?? g)->
  ((i,i':nat)(Hi:(lt i n))(Hi':(lt i' n))(lt i i')->((f i Hi) [<] (f i' Hi')))->
  ((j,j':nat)(Hj:(lt j m))(Hj':(lt j' m))(lt j j')->((g j Hj) [<] (g j' Hj')))->
  ((i,j:nat)(Hi:(lt i n))(Hj:(lt j m))(f i Hi) [#] (g j Hj))->
  {h:(i:nat)(lt i (plus m n))->F | 
    (nat_less_n_fun ?? h) and
    ((i,i':nat)(Hi:(lt i (plus m n)))(Hi':(lt i' (plus m n)))(lt i i')->((h i Hi) [<] (h i' Hi'))) and
    ((i:nat)(Hi:(lt i n)){j:nat | {Hj:(Clt j (plus m n)) | (f i Hi) [=] (h j (Clt_to ?? Hj))}}) and
    ((j:nat)(Hj:(lt j m)){i:nat | {Hi:(Clt i (plus m n)) | (g j Hj) [=] (h i (Clt_to ?? Hi))}}) and
    ((P:F->CProp)(pred_well_def F P)->((i:nat)(Hi:(lt i n))(P (f i Hi)))->((j:nat)(Hj:(lt j m))(P (g j Hj)))->
       (k:nat)(Hk:(lt k (plus m n)))(P (h k Hk))) and
    ((P:F->CProp)(pred_well_def F P)->
      ({i:nat | {Hi:(Clt i n) | (P (f i (Clt_to ?? Hi)))}} or {j:nat | {Hj:(Clt j m) | (P (g j (Clt_to ?? Hj)))}})->
        {k:nat | {Hk:(Clt k (plus m n)) | (P (h k (Clt_to ?? Hk)))}}) and
    (((P:F->Prop)(pred_well_def' F P)->((i:nat)(Hi:(lt i n))(P (f i Hi)))->((j:nat)(Hj:(lt j m))(P (g j Hj)))->
       (k:nat)(Hk:(lt k (plus m n)))(P (h k Hk)))) and
    (P:F->Prop)(pred_well_def' F P)->
      ({i:nat | {Hi:(Clt i n) | (P (f i (Clt_to ?? Hi)))}} or {j:nat | {Hj:(Clt j m) | (P (g j (Clt_to ?? Hj)))}})->
        {k:nat | {Hk:(Clt k (plus m n)) | (P (h k (Clt_to ?? Hk)))}}}.
Induction m.
Clear m; Simpl; Intros.
Exists f.
Repeat Split.
Assumption.
Assumption.
Intros; Exists i.
Exists (toCProp_lt ?? Hi).
Apply H; Reflexivity.
Intros; ElimType False; Inversion Hj.
Do 4 Intro; Assumption.
Intros; Inversion_clear H5.
Assumption.
Inversion_clear H6.
Inversion_clear H5.
ElimType False.
LetTac Hx0:= (Clt_to ?? x0); Inversion Hx0.
Do 4 Intro; Assumption.
Intros; Inversion_clear H5.
Assumption.
Inversion_clear H6.
Inversion_clear H5.
ElimType False.
LetTac Hx0:= (Clt_to ?? x0); Inversion Hx0.
Clear m; Intro m; Intros.
LetTac g':=[j:nat][Hj:(lt j m)](g j (lt_S ?? Hj)).
Cut (nat_less_n_fun ?? g'); Intro.
2: Intros; Unfold g'; Apply H1; Assumption.
Cut (j,j':nat)(Hj:(lt j m))(Hj':(lt j' m))(lt j j')->(g' j Hj) [<] (g' j' Hj'); Intros.
2: Unfold g'; Apply H3; Assumption.
Cut (i,j:nat)(Hi:(lt i n))(Hj:(lt j m))(f i Hi) [#] (g' j Hj); Intros.
2: Unfold g'; Apply H4; Assumption.
Elim (H n f g' H0 H5 H2 H6 H7).
Intros h' Hh'.
Inversion_clear Hh'.
Rename H9 into h_PropEx.
Inversion_clear H8.
Rename H10 into h_PropAll.
Inversion_clear H9.
Rename H10 into h_CPropEx.
Inversion_clear H8.
Rename H10 into h_CPropAll.
Inversion_clear H9.
Rename H10 into g'_h'_Ex.
Inversion_clear H8.
Rename H10 into f_h'_Ex.
Inversion_clear H9.
Rename H10 into h'_mon.
Rename H8 into h'_less.
Elim (ordered_insertion ?? h'_less h'_mon (g ? (lt_n_Sn ?))).
Intros h Hh.
Inversion_clear Hh.
Rename H9 into H_CPropEx.
Inversion_clear H8.
Rename H10 into H_PropEx.
Inversion_clear H9.
Rename H10 into h_less.
Inversion_clear H8.
Rename H10 into H_CProp.
Inversion_clear H9.
Rename H8 into h_mon.
Rename H10 into H_Prop.
Exists h; Repeat Split.
Assumption.
Assumption.
Intros.
Elim (f_h'_Ex i Hi); Intros j Hj.
Elim Hj; Clear Hj; Intros Hj Hj'.
Cut (lt j (plus m n)); [Intro | Apply Clt_to; Assumption].
Simpl.
Apply H_PropEx with P:=[x:F](f i Hi) [=] x.
Red; Intros.
Apply eq_transitive_unfolded with x; Assumption.
Left; Exists j; Exists Hj; Exact Hj'.
Intros.
Elim (le_lt_eq_dec ?? Hj); Intro.
Cut (lt j m); [Clear a; Intro Hj' | Auto with arith].
Elim (g'_h'_Ex j Hj'); Intros i Hi.
Elim Hi; Clear Hi; Intros Hi Hi'.
Cut (lt i (plus m n)); [Intro | Apply Clt_to; Assumption].
Apply H_PropEx with P:=[x:F](g j Hj) [=] x.
Red; Intros.
Apply eq_transitive_unfolded with x; Assumption.
Unfold g' in Hi'.
Left; Exists i; Exists Hi.
EApply eq_transitive_unfolded.
2: Apply Hi'.
Apply H1; Reflexivity.
Apply H_PropEx with P:=[x:F](g j Hj) [=] x.
Red; Intros.
Apply eq_transitive_unfolded with x; Assumption.
Right; Apply H1; Auto.
Intros.
Simpl in Hk.
Apply H_CProp.
Assumption.
Intros; Apply h_CPropAll.
Assumption.
Assumption.
Unfold g'; Intros; Apply H10.
Apply H10.
Intros.
Apply H_CPropEx.
Assumption.
Inversion_clear H9.
Left; Apply h_CPropEx.
Assumption.
Left; Assumption.
Elim H10; Intros j Hj.
Elim Hj; Clear H10 Hj; Intros Hj Hj'.
Elim (le_lt_eq_dec ?? (Clt_to ?? Hj)); Intro.
Cut (lt j m); [Intro | Auto with arith].
Left.
Elim (g'_h'_Ex j H9); Intros i Hi.
Elim Hi; Clear Hi; Intros Hi Hi'.
Exists i; Exists Hi.
EApply H8.
2: Apply Hi'.
Unfold g'.
EApply H8.
Apply Hj'.
Apply H1; Reflexivity.
Right.
EApply H8.
Apply Hj'.
Apply H1; Auto.
Intros.
Simpl in Hk.
Apply H_Prop.
Assumption.
Intros; Apply h_PropAll.
Assumption.
Assumption.
Unfold g'; Intros; Apply H10.
Apply H10.
Intros.
Apply H_PropEx.
Assumption.
Inversion_clear H9.
Left; Apply h_PropEx.
Assumption.
Left; Assumption.
Elim H10; Intros j Hj.
Elim Hj; Clear H10 Hj; Intros Hj Hj'.
Elim (le_lt_eq_dec ?? (Clt_to ?? Hj)); Intro.
Cut (lt j m); [Intro | Auto with arith].
Left.
Elim (g'_h'_Ex j H9); Intros i Hi.
Elim Hi; Clear Hi; Intros Hi Hi'.
Exists i; Exists Hi.
EApply H8.
2: Apply Hi'.
Unfold g'.
EApply H8.
Apply Hj'.
Apply H1; Reflexivity.
Right.
EApply H8.
Apply Hj'.
Apply H1; Auto.
Apply h_CPropAll with P:=[x:F](x [#] (g m (lt_n_Sn m))).
Red; Intros.
AStepl x; Assumption.
Intros; Apply H4.
Unfold g'; Intros; Apply less_imp_ap.
Apply H3; Assumption.
Qed.
*)

(* begin hide *)
Variable f : nat -> nat.
Hypothesis f0 : f 0 = 0.
Hypothesis f_mon : forall i j : nat, i < j -> f i < f j.

Variable h : nat -> F.
(* end hide *)

(**
Also, some technical stuff on sums.  The first lemma relates two different kinds of sums; the other two ones are variations, where the structure of the arguments is analyzed in more detail.
*)

(* begin show *)
Lemma Sumx_Sum_Sum
 (* end show *)
 (* begin hide *)
 :
 forall n : nat,
 Sumx (fun (i : nat) (H : i < n) => Sum (f i) (pred (f (S i))) h)[=]
 Sumx (fun (i : nat) (H : i < f n) => h i).
simple induction n.
rewrite f0; simpl in |- *; Algebra.
clear n; intros.
elim (le_lt_dec n 0); intro.
cut (n = 0); [ clear a; intro | auto with arith ].
rewrite H0 in H.
rewrite H0.
simpl in |- *.
AStepl (Sum (f 0) (pred (f 1)) h).
rewrite f0.
apply eq_symmetric_unfolded.
eapply eq_transitive_unfolded.
apply Sumx_to_Sum.
pattern 0 at 1 in |- *; rewrite <- f0; apply f_mon; apply lt_n_Sn.
red in |- *; intros.
rewrite H1; Algebra.
clear H; apply Sum_wd'; unfold part_tot_nat_fun in |- *.
auto with arith.
intros.
elim (le_lt_dec (f 1) i); intro; simpl in |- *.
cut (0 < f 1).
intro; elimtype False; omega.
pattern 0 at 1 in |- *; rewrite <- f0; apply f_mon; apply lt_n_Sn.
Algebra.
cut (0 < f n); [ intro | rewrite <- f0; apply f_mon; assumption ].
simpl in |- *.
eapply eq_transitive_unfolded.
2: apply eq_symmetric_unfolded; apply Sumx_to_Sum.
apply
 eq_transitive_unfolded
  with
    (Sum 0 (pred (f n))
       (part_tot_nat_fun _ _ (fun (i : nat) (H : i < f n) => h i))[+]
     Sum (f n) (pred (f (S n))) h).
apply bin_op_wd_unfolded.
eapply eq_transitive_unfolded.
apply H.
apply Sumx_to_Sum.
assumption.
red in |- *; intros.
rewrite H1; Algebra.
Algebra.
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
Algebra.
rewrite <- H1.
cut (0 < f (S n)); [ intro | rewrite <- f0; auto with arith ].
cut (f (S n) = S (pred (f (S n)))); [ intro | apply S_pred with 0; auto ].
rewrite <- H3.
apply lt_le_weak; auto with arith.
intros.
unfold part_tot_nat_fun in |- *.
elim (le_lt_dec (f (S n)) i); intro; simpl in |- *.
elimtype False; omega.
Algebra.
apply lt_trans with (f n); auto with arith.
red in |- *; intros.
rewrite H1; Algebra.
Qed.
(* end hide *)

(* begin show *)
Lemma str_Sumx_Sum_Sum
 (* end show *)
 (* begin hide *)
 :
 forall (n : nat) (g : forall (i : nat) (Hi : i < n), nat -> F),
 (forall (i j : nat) (Hi : i < n), f i <= j -> j < f (S i) -> g i Hi j[=]h j) ->
 forall m : nat,
 m = f n ->
 Sumx (fun (i : nat) (H : i < n) => Sum (f i) (pred (f (S i))) (g i H))[=]
 Sumx (fun (i : nat) (H : i < m) => h i).
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

Let f' (m : nat) (f : forall i : nat, i <= m -> nat) : nat -> nat.
intros m f i.
elim (le_lt_dec i m); intro.
apply (f i a).
apply (f m (le_n m) + i).
Defined.
(* end hide *)

(* begin show *)
Lemma str_Sumx_Sum_Sum'
 (* end show *)
 (* begin hide *)
 :
 forall (m : nat) (F : COrdField) (f : forall i : nat, i <= m -> nat),
 f 0 (le_O_n _) = 0 ->
 (forall (i j : nat) Hi Hj, i = j -> f i Hi = f j Hj) ->
 (forall (i j : nat) Hi Hj, i < j -> f i Hi < f j Hj) ->
 forall (h : nat -> F) (n : nat) (g : forall i : nat, i < m -> nat -> F),
 (forall (i j : nat) Hi Hi' Hi'',
  f i Hi' <= j -> j < f (S i) Hi'' -> g i Hi j[=]h j) ->
 (forall H, n = f m H) ->
 Sumx
   (fun (i : nat) (H : i < m) =>
    Sum (f i (lt_le_weak _ _ H)) (pred (f (S i) H)) (g i H))[=]
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
intros; Algebra.
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

(**
A different version of a lemma already proved for natural numbers.
*)

Lemma weird_mon_covers :
 forall (n : nat) (f : nat -> nat),
 (forall i : nat, f i < n -> f i < f (S i)) ->
 {m : nat | n <= f m | forall i : nat, i < m -> f i < n}.
intros; induction  n as [| n Hrecn].
exists 0.
auto with arith.
intros; inversion H0.
elim Hrecn.
2: auto.
intros m Hm Hm'.
elim (le_lt_eq_dec _ _ Hm); intro.
exists m.
assumption.
auto with arith.
exists (S m).
apply le_lt_trans with (f m).
rewrite b; auto with arith.
apply H.
rewrite b; apply lt_n_Sn.
intros.
elim (le_lt_eq_dec _ _ H0); intro.
auto with arith.
cut (i = m); [ intro | auto ].
rewrite b; rewrite <- H1.
apply lt_n_Sn.
Qed.

Variables a b : IR.
(* begin hide *)
Let I := compact a b.
(* end hide *)
Hypothesis Hab : a[<=]b.

(**
An interesting property: in a partition, if [ai [<] aj] then [(lt i j)].
*)

Lemma Partition_Points_mon :
 forall (n : nat) (P : Partition Hab n) (i j : nat) Hi Hj,
 P i Hi[<]P j Hj -> i < j.
intros.
cut (~ j <= i); intro.
apply not_ge; auto.
elimtype False.
apply less_irreflexive_unfolded with (x := P i Hi).
apply less_leEq_trans with (P j Hj).
assumption.
apply
 local_mon'_imp_mon'_le with (f := fun (i : nat) (Hi : i <= n) => P i Hi).
intros; apply prf2.
intro; intros; apply prf1; assumption.
assumption.
Qed.

End More_Lemmas.

Section More_Definitions.

(** **Definitions

Some auxiliary definitions.  A partition is said to be separated if all its points are distinct.
*)

Variables a b : IR.
Hypothesis Hab : a[<=]b.

Definition _Separated (n : nat) (P : Partition Hab n) :=
  forall (i : nat) Hi H', P i Hi[<]P (S i) H'.

(**
Two partitions are said to be (mutually) separated if they are both separated and all their points are distinct (except for the endpoints).

%\begin{convention}% Let [P,Q] be partitions of [I] with, respectively, [n] and [m] points.
%\end{convention}%
*)

Variables n m : nat.

Variable P : Partition Hab n.
Variable Q : Partition Hab m.

Definition Separated :=
  _Separated _ P
  and _Separated _ Q
      and (forall i j : nat,
           0 < i ->
           0 < j ->
           i < n ->
           j < m -> forall (Hi : i <= n) (Hj : j <= m), P i Hi[#]Q j Hj).

End More_Definitions.

Implicit Arguments _Separated [a b Hab n].
Implicit Arguments Separated [a b Hab n m].

Section Even_Partitions.

(** **More Lemmas

More technical stuff.  Two equal partitions have the same mesh.
*)

Lemma Mesh_wd :
 forall (n : nat) (a b b' : IR) (Hab : a[<=]b) (Hab' : a[<=]b')
   (P : Partition Hab n) (Q : Partition Hab' n),
 (forall (i : nat) (Hi : i <= n), P i Hi[=]Q i Hi) -> Mesh P[=]Mesh Q.
simple induction n.
intros.
unfold Mesh in |- *; simpl in |- *; Algebra.
clear n; intro.
case n.
intros.
unfold Mesh in |- *; simpl in |- *.
apply cg_minus_wd; apply H0.
clear n; intros.
unfold Mesh in |- *.
apply
 eq_transitive_unfolded
  with
    (Max (P _ (le_n (S (S n)))[-]P _ (le_S _ _ (le_n (S n))))
       (maxlist (Part_Mesh_List (Partition_Dom P)))).
simpl in |- *; Algebra.
apply
 eq_transitive_unfolded
  with
    (Max (Q _ (le_n (S (S n)))[-]Q _ (le_S _ _ (le_n (S n))))
       (maxlist (Part_Mesh_List (Partition_Dom Q)))).
2: simpl in |- *; Algebra.
apply max_wd_unfolded.
apply cg_minus_wd; apply H0.
apply eq_transitive_unfolded with (Mesh (Partition_Dom P)).
unfold Mesh in |- *; Algebra.
apply eq_transitive_unfolded with (Mesh (Partition_Dom Q)).
apply H.
intros.
unfold Partition_Dom in |- *; simpl in |- *.
apply H0.
unfold Mesh in |- *; Algebra.
Qed.

Lemma Mesh_wd' :
 forall (n : nat) (a b : IR) (Hab : a[<=]b) (P Q : Partition Hab n),
 (forall (i : nat) (Hi : i <= n), P i Hi[=]Q i Hi) -> Mesh P[=]Mesh Q.
intros.
apply Mesh_wd.
intros; apply H.
Qed.

(**
The mesh of an even partition is easily calculated.
*)

Lemma even_partition_Mesh :
 forall (m : nat) (Hm : 0 <> m) (a b : IR) (Hab : a[<=]b),
 Mesh (Even_Partition Hab m Hm)[=](b[-]a[/] _[//]nring_ap_zero' _ _ Hm).
simple induction m.
intros; elimtype False; apply Hm; auto.
intros.
unfold Mesh in |- *.
elim (le_lt_dec n 0); intro.
cut (0 = n); [ intro | auto with arith ].
generalize Hm; clear H a0 Hm.
rewrite <- H0; intros.
simpl in |- *.
rational.
apply
 eq_transitive_unfolded
  with
    (Max
       (a[+]nring (S n)[*](b[-]a[/] _[//]nring_ap_zero' _ _ Hm)[-]
        (a[+]nring n[*](b[-]a[/] _[//]nring_ap_zero' _ _ Hm)))
       (maxlist (Part_Mesh_List (Partition_Dom (Even_Partition Hab _ Hm))))).
cut (n = S (pred n)); [ intro | apply S_pred with 0; auto ].
generalize Hm; rewrite H0; clear Hm; intro.
simpl in |- *; Algebra.
eapply eq_transitive_unfolded.
apply Max_comm.
simpl in |- *.
eapply eq_transitive_unfolded.
apply leEq_imp_Max_is_rht.
2: rational.
apply eq_imp_leEq.
RStepr (b[-]a[/] nring n[+]One[//]nring_ap_zero' _ _ Hm).
apply
 eq_transitive_unfolded with (Mesh (Partition_Dom (Even_Partition Hab _ Hm))).
simpl in |- *; Algebra.
cut (0 <> n); intro.
eapply eq_transitive_unfolded.
apply
 Mesh_wd'
  with
    (Q := Even_Partition
            (part_pred_lemma _ _ Hab (S n) (Even_Partition Hab _ Hm) n
               (le_n_Sn n)) _ H0).
intros; simpl in |- *; rational.
eapply eq_transitive_unfolded.
apply H.
simpl in |- *; rational.
apply (lt_O_neq n); auto.
Qed.

(**
Even partitions always have a common refinement.
*)

Variables a b : IR.
(* begin hide *)
Let I := compact a b.
(* end hide *)
Hypothesis Hab : a[<=]b.

Lemma refinement_resp_mult :
 forall (m n : nat) Hm Hn,
 {k : nat | m = n * k} ->
 Refinement (Even_Partition Hab n Hn) (Even_Partition Hab m Hm).
intros m n Hm Hn H.
elim H; intros k Hk.
red in |- *.
cut (0 <> k); intro.
exists (fun i : nat => i * k); repeat split.
symmetry  in |- *; assumption.
intros.
apply mult_lt_compat_r.
assumption.
apply neq_O_lt; auto.
intros.
cut (i * k <= m).
intro.
exists H2.
simpl in |- *.
apply bin_op_wd_unfolded.
Algebra.
generalize Hm; rewrite Hk.
clear Hm; intro.
RStepl
 (nring i[*]nring k[*]
  (b[-]a[/] _[//]
   mult_resp_ap_zero _ _ _ (nring_ap_zero' _ _ Hn) (nring_ap_zero' _ _ H0))).
apply mult_wd.
apply eq_symmetric_unfolded; apply nring_comm_mult.
apply div_wd.
Algebra.
apply eq_symmetric_unfolded; apply nring_comm_mult.
rewrite Hk.
apply mult_le_compat_r; assumption.
apply Hm.
rewrite Hk.
rewrite <- H0.
auto.
Qed.

(**
%\begin{convention}% Assume [m,n] are positive natural numbers and denote by [P] and [Q] the even partitions with, respectively, [m] and [n] points.
%\end{convention}%
*)

Variables m n : nat.
Hypothesis Hm : 0 <> m.
Hypothesis Hn : 0 <> n.

(* begin hide *)
Let P := Even_Partition Hab m Hm.
Let Q := Even_Partition Hab n Hn.
(* end hide *)

Lemma even_partition_refinement :
 {N : nat |
 {HN : 0 <> N | Refinement P (Even_Partition Hab N HN) |
 Refinement Q (Even_Partition Hab N HN)}}.
exists (m * n).
cut (0 <> m * n); intro.
exists H.
unfold P in |- *; apply refinement_resp_mult.
exists n; auto.
unfold Q in |- *; apply refinement_resp_mult.
exists m; auto with arith.
clear P Q.
cut (nring (R:=IR) (m * n)[#]Zero).
rewrite <- H; simpl in |- *.
apply ap_irreflexive_unfolded.
AStepl (nring m[*]nring (R:=IR) n).
apply mult_resp_ap_zero; apply Greater_imp_ap; AStepl (nring (R:=IR) 0);
 apply nring_less; apply neq_O_lt; auto.
Qed.

End Even_Partitions.

Section Partitions.

Variables a b : IR.
(* begin hide *)
Let I := compact a b.
(* end hide *)
Hypothesis Hab : a[<=]b.

(**
The antimesh of a separated partition is always positive.
*)

Lemma pos_AntiMesh :
 forall (n : nat) (P : Partition Hab n),
 0 < n -> _Separated P -> Zero[<]AntiMesh P.
intro; case n; clear n.
 intros P H H0; elimtype False; apply (lt_irrefl _ H).
intros n P H H0.
unfold AntiMesh in |- *.
apply less_minlist.
 simpl in |- *; auto with arith.
intros y H1.
elim (Part_Mesh_List_lemma _ _ _ _ _ _ H1); intros i Hi.
elim Hi; clear Hi; intros Hi Hi'.
elim Hi'; clear Hi'; intros Hi' H'.
eapply less_wdr.
 2: apply eq_symmetric_unfolded; apply H'.
apply shift_less_minus; AStepl (P i Hi).
apply H0.
Qed.

(**
A partition can have only one point iff the endpoints of the interval are the same; moreover, if the partition is separated and the endpoints of the interval are the same then it must have one point.
*)

Lemma partition_length_zero : Partition Hab 0 -> a[=]b.
intro H.
Step_final (H 0 (le_O_n 0)).
Qed.

Lemma _Separated_imp_length_zero :
 forall (n : nat) (P : Partition Hab n), _Separated P -> a[=]b -> 0 = n.
intros n P H H0.
cut (~ 0 <> n); [ auto with zarith | intro ].
cut (0 < n); [ intro | apply neq_O_lt; auto ].
cut (a[#]b).
exact (eq_imp_not_ap _ _ _ H0).
AStepl (P _ (le_O_n _)).
AStepr (P _ (le_n _)).
apply less_imp_ap.
apply local_mon_imp_mon_le with (f := fun (i : nat) (H : i <= n) => P i H).
exact H.
assumption.
Qed.

Lemma partition_less_imp_gt_zero :
 forall (n : nat) (P : Partition Hab n), a[<]b -> 0 < n.
intros n P H.
cut (0 <> n); intro.
 apply neq_O_lt; auto.
elimtype False.
cut (a[=]b).
 intro; apply less_irreflexive_unfolded with (x := a).
 AStepr b; assumption.
apply partition_length_zero.
rewrite H0; apply P.
Qed.

End Partitions.