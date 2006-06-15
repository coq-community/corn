Require Export CReals1.

(* Consider Reals are enumerated by function f *)

Section IntervalSequence.

Variable f : nat -> IR.

Record interv : Type := 
  {interv_lft     : IR;
   interv_rht     : IR;
   interv_lft_rht : interv_lft [<] interv_rht}.

Lemma interv_0_correct: 
f 0[+]One[<]f 0[+]Two.
apply plus_resp_less_lft.
apply one_less_two.
Qed. 

Let interv_0 := (Build_interv (f 0 [+] One) (f 0[+]Two) interv_0_correct).

(* FIXME: Reuse this code from IVT -----------------------------------*) 

Let Small : IR := Two [/]ThreeNZ.
Let lft (a b : IR) := (Two[*]a[+]b) [/]ThreeNZ.
Let rht (a b : IR) := (a[+]Two[*]b) [/]ThreeNZ.

Lemma less_pres_lft : forall a b :IR, a[<] b ->  a [<] lft a b.
intros.
unfold lft in |- *.
apply shift_less_div.
apply pos_three.
rstepl (Two[*]a[+]a).
apply plus_resp_less_lft.
auto.
Qed.

Lemma less_pres_rht : forall a b :IR, a[<] b ->  rht a b [<] b.
intros.
unfold rht in |- *.
apply shift_div_less.
apply pos_three.
rstepr (b[+]Two[*]b).
apply plus_resp_less_rht.
auto.
Qed.

Lemma less_pres_lft_rht : forall a b :IR, a[<] b -> lft a b [<] rht a b.
intros.
unfold lft in |- *. unfold rht in |- *.
apply div_resp_less_rht.
rstepl (a[+]b[+]a).
rstepr (a[+]b[+]b).
apply plus_resp_less_lft.
auto.
apply pos_three.
Qed.

Lemma smaller_rht : forall (a b : IR),  rht a b[-]a [=] Small[*] (b[-]a).
intros.
unfold Small in |- *. unfold rht in |- *.
rational.
Qed.

Lemma smaller_lft : forall (a b : IR), b[-]lft a b [=] Small[*] (b[-]a).
intros.
unfold Small in |- *. unfold lft in |- *.
rational.
Qed.

Hint Resolve smaller_lft smaller_rht: algebra.

Lemma small_greater_zero : Zero [<=] Small.
unfold Small.
assert (Zero[<](Two[/]ThreeNZ:IR)).
apply pos_div_three; auto.
apply pos_two; auto.
apply less_leEq; auto.
Qed.

Lemma small_less_one : Small [<] One.
unfold Small.
apply mult_cancel_less with (Three:IR).
apply pos_three.
astepl (Two:IR).
astepr (Three:IR).
apply two_less_three.
Qed.

(* -------------------------------------------------------------- *)


Definition seq_fun (I : interv) (n:nat) : interv.
intros I n.
case (less_cotransitive_unfolded IR _ _  (less_pres_lft_rht _ _ (interv_lft_rht I)) (f n)).
intro H1.
apply (Build_interv (interv_lft I) (lft (interv_lft I) (interv_rht I))).
apply less_pres_lft.
apply interv_lft_rht.
intro H2. 
apply (Build_interv (rht (interv_lft I) (interv_rht I)) (interv_rht I)).
apply less_pres_rht.
apply interv_lft_rht.
Defined.

Fixpoint seq1 (n:nat):interv :=
match n with
  0     => interv_0
| (S p) => seq_fun (seq1 p) (S p)
end.

Definition seq1_lft := fun n:nat => interv_lft (seq1 n).
Definition seq1_rht := fun n:nat => interv_rht (seq1 n).

Lemma next_smaller : forall (I : interv) (n : nat),
seq1_rht (S n)[-]seq1_lft (S n) [<=]
Small [*](seq1_rht n[-]seq1_lft n).
intros.
unfold seq1_lft. unfold seq1_rht.
astepl (interv_rht (seq_fun (seq1 n) (S n))[-]interv_lft (seq_fun (seq1 n) (S n))).
unfold seq_fun.
case (less_cotransitive_unfolded IR _ _  (less_pres_lft_rht _ _ (interv_lft_rht (seq1 n))) (f (S n))).

intros.
simpl.
apply leEq_transitive with (rht (interv_lft (seq1 n)) (interv_rht (seq1 n))[-]interv_lft (seq1 n)).
apply minus_resp_leEq.
apply less_leEq.
apply less_pres_lft_rht.
apply interv_lft_rht.
apply eq_imp_leEq.
apply smaller_rht. 

intros.
simpl.
apply leEq_transitive with (interv_rht (seq1 n)[-]lft (interv_lft (seq1 n)) (interv_rht (seq1 n))).
apply minus_resp_leEq_rht.
apply less_leEq.
apply less_pres_lft_rht.
apply interv_lft_rht.
apply eq_imp_leEq.
apply smaller_lft.
Qed.

Lemma intervals_smaller : forall N : nat,
seq1_rht N[-]seq1_lft N [<=]Small[^]N. 
intros.
induction N.
astepl ((One[-]Zero):IR).
astepr (One:IR).
astepl (One:IR).
apply leEq_reflexive.
unfold seq1_lft.
unfold seq1_rht.
simpl.
astepr ((Two [-] One):IR); rational.
apply leEq_transitive with (Small[*](seq1_rht N[-]seq1_lft N)); auto.
apply next_smaller; auto.
astepr (Small[*]Small[^]N).
apply mult_resp_leEq_lft; auto.
apply small_greater_zero.
Qed.

Lemma grow_lft : forall N m : nat, N <= m ->
interv_lft (seq1 N) [<=] interv_lft (seq1 m).
intros.
induction m. destruct N; auto.
apply leEq_reflexive.
assert (S N = 0); auto with arith.
elim H0.
apply leEq_reflexive.
elim H.
apply leEq_reflexive.
clear IHm. clear H. clear m.
intros.
apply leEq_transitive with (interv_lft (seq1 m)); auto.
astepr (interv_lft (seq_fun (seq1 m) (S m))).
unfold seq_fun.
case (less_cotransitive_unfolded IR _ _  (less_pres_lft_rht _ _ (interv_lft_rht (seq1 m))) (f (S m))).
intros. simpl. apply leEq_reflexive.
intros. simpl.
apply less_leEq.
apply less_transitive_unfolded with (lft (interv_lft (seq1 m)) (interv_rht (seq1 m))).
apply less_pres_lft.
apply interv_lft_rht.
apply less_pres_lft_rht.
apply interv_lft_rht.
Qed.

Lemma grow_rht : forall N m : nat, N <= m ->
interv_rht (seq1 m) [<=] interv_rht (seq1 N).
intros.
induction m. destruct N; auto.
apply leEq_reflexive.
assert (S N = 0); auto with arith.
elim H0.
apply leEq_reflexive.
elim H.
apply leEq_reflexive.
clear IHm. clear H. clear m.
intros.
apply leEq_transitive with (interv_rht (seq1 m)); auto.
astepl (interv_rht (seq_fun (seq1 m) (S m))).
unfold seq_fun.
case (less_cotransitive_unfolded IR _ _  (less_pres_lft_rht _ _ (interv_lft_rht (seq1 m))) (f (S m))).
simpl. intros. 
apply less_leEq.
apply less_transitive_unfolded with (rht (interv_lft (seq1 m)) (interv_rht (seq1 m))).
apply less_pres_lft_rht.
apply interv_lft_rht.
apply less_pres_rht.
apply interv_lft_rht.
simpl. intros.
apply leEq_reflexive.
Qed.

Lemma intervals_embed : forall N m : nat, N <= m ->
AbsSmall (R:=IR) (seq1_rht N[-]seq1_lft N) (seq1_lft m[-]seq1_lft N).
intros.
unfold seq1_rht. unfold seq1_lft.
unfold AbsSmall. split.
apply leEq_transitive with (Zero:IR).
astepr ([--]Zero:IR).
apply inv_resp_leEq.
apply shift_leEq_lft.
apply less_leEq.
apply interv_lft_rht.
apply shift_leEq_lft.
2: apply minus_resp_leEq.
apply grow_lft; auto.
apply leEq_transitive with (interv_rht (seq1 m)).
apply less_leEq. apply interv_lft_rht.
apply grow_rht; auto.
Qed.

Lemma Cauchy_seq1_lft : Cauchy_prop seq1_lft.
unfold Cauchy_prop in |- *.
intro eps. intros H.
assert ({ N : nat | Small[^]N[<=]eps}).
apply (qi_yields_zero (Two[/]ThreeNZ) small_greater_zero small_less_one eps); auto.
destruct X as [N H1].
exists N. intros.
apply AbsSmall_leEq_trans with (seq1_rht N[-]seq1_lft N); auto.
apply leEq_transitive with (Small[^]N); auto.
apply intervals_smaller; auto.
apply intervals_embed; auto.
Qed.

Definition f_lim := Lim (Build_CauchySeq _ seq1_lft Cauchy_seq1_lft).

Lemma lim_smaller: 
forall (n : nat), f_lim [<=] (seq1_rht n).
intros. unfold f_lim.
apply str_seq_leEq_so_Lim_leEq.
exists n. intros. simpl.
unfold seq1_lft. unfold seq1_rht.
apply leEq_transitive with (interv_rht (seq1 i)).
apply less_leEq. apply interv_lft_rht.
apply grow_rht. auto.
Qed.

Lemma lim_bigger: 
forall (n : nat), (seq1_lft n) [<=] f_lim.
intros.
unfold f_lim.
apply str_leEq_seq_so_leEq_Lim.
exists n. intros. simpl.
unfold seq1_lft. unfold seq1_rht.
apply grow_lft; auto.
Qed.


Lemma f_n_not_in_int : 
forall (n : nat), (f n) [<] (seq1_lft n) or (seq1_rht n) [<] (f n).
intros.
unfold seq1_lft. unfold seq1_rht.
induction n.
simpl. left.
apply less_plusOne.

cut (f (S n)[<]interv_lft (seq_fun (seq1 n) (S n)) or interv_rht (seq_fun (seq1 n) (S n))[<]f (S n)); auto.
unfold seq_fun.
elim less_cotransitive_unfolded.
intros.
simpl in |- *.
right.
auto.
intros.
simpl in |- *.
left.
auto.
Qed.

Lemma lim_not_in_ranf :
forall (n : nat), f_lim [#] (f n). 
intros.
elim (f_n_not_in_int n); intros.
assert (f n [<] f_lim).
apply less_leEq_trans with (seq1_lft n); auto.
apply lim_bigger.
apply ap_symmetric.
apply less_imp_ap; auto.
assert (f_lim [<] f n).
apply leEq_less_trans with (seq1_rht n); auto.
apply lim_smaller.
apply less_imp_ap; auto.
Qed.

End IntervalSequence.

Theorem reals_not_countable : 
  forall (f : nat -> IR),{x :IR | forall n : nat, x [#] (f n)}.
intros.
exists (f_lim f).
intros.
apply lim_not_in_ranf.
Qed.
