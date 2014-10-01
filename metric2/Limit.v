(*
Copyright © 2006-2008 Russell O’Connor

Permission is hereby granted, free of charge, to any person obtaining a copy of
this proof and associated documentation files (the "Proof"), to deal in
the Proof without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Proof, and to permit persons to whom the Proof is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Proof.

THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
*)

Require Import QArith.
Require Import Bool.
Require Export Complete.
Require Export Coq.Lists.Streams.
Require Import abstract_algebra theory.streams orders.naturals.

(**
** Limits
A predicate saying there exists a point in the stream where a predicate
is satsified.

We take the unusual step of putting this inductive type in Prop even
though it contains constructive information.  This is because we expect
this proof to only be used in proofs of termination. *)
Inductive LazyExists {A} (P : Stream A → Prop) (x : Stream A) : Prop :=
  | LazyHere : P x → LazyExists P x
  | LazyFurther : (unit → LazyExists P (tl x)) → LazyExists P x.
Implicit Arguments LazyHere [[A] [P] [x]].
Implicit Arguments LazyFurther [[A] [P] [x]].

Instance LazyExists_proper `{Setoid A} `{!Proper ((=) ==> iff) (P : Stream A → Prop)} : Proper ((=) ==> iff) (LazyExists P).
Proof.
  assert (∀ s1, LazyExists P s1 → ∀ s2, s1 = s2 → LazyExists P s2) as prf.
   induction 1 as [|? ? IH]; intros s2 E.
    left. now rewrite <-E.
   right. intros _. apply (IH tt). now rewrite E.
  split; repeat intro; eapply prf; eauto.
Qed.

Lemma LazyExists_tl `{P : Stream A → Prop} `(ex : LazyExists P s) (Ptl : EventuallyForAll P s) : 
  LazyExists P (tl s).
Proof. 
  destruct ex as [? | further]. 
   left. destruct Ptl. now auto.
  apply (further tt).
Defined.

Lemma LazyExists_Str_nth_tl `{P : Stream A → Prop} `(ex : !LazyExists P s) (Ptl : EventuallyForAll P s) (n : nat) : 
   LazyExists P (Str_nth_tl n s).
Proof.
  induction n.
   easy.
  intros. 
  simpl. rewrite <-tl_nth_tl.
  apply LazyExists_tl.
   now apply IHn.
  now apply ForAll_Str_nth_tl.
Defined.

Fixpoint LazyExists_inc `{P : Stream A → Prop}
    (n : nat) s : LazyExists P (Str_nth_tl n s) → LazyExists P s :=
  match n return LazyExists P (Str_nth_tl n s) → LazyExists P s with
  | O => λ x, x
  | S n => λ ex, LazyFurther (λ _, LazyExists_inc n (tl s) ex)
  end.

(*
Fixpoint f (n m : nat) :=
  match n with
  | O => m
  | S n => S (f n (f n m))
  end.
Fixpoint LazyExists_inc `{P : Stream A → Prop}
    (n : nat) `(ex : LazyExists P s) (H : EventuallyForAll P s) : LazyExists P s :=
  match n with
  | O => ex
  | S n => LazyFurther (λ _, LazyExists_inc n 
     (LazyExists_inc n 
       (LazyExists_tl ex H)
       (EventuallyForAll_tl _ _ H))
     (EventuallyForAll_tl _ _ H))
  end.
*)

Section TakeUntil.
(* begin hide *)
Coercion Local Is_true : bool >-> Sortclass.
(* end hide *)
(** takeUntil creates a list of of elements upto a the point where the predicate
P is satisfied.  For efficency reasons it doesn't actually build a list, but
takes continuations for cons and nil instead.  To build an actual list pass in
the const and nil constructors. *)
Fixpoint takeUntil {A B : Type} (P : Stream A → bool) {s : Stream A} (ex:LazyExists P s) (cons: A → B → B) (nil : B) : B :=
  (if P s as b return ((P s → b) → B)
   then λ _, nil
   else λ (n : P s → False), cons (hd s)
     (@takeUntil A B P (tl s)
      match ex with
      | LazyHere H => (False_ind _ (n H))
      | LazyFurther ex0 => ex0 tt
      end cons nil))
  (λ x, x).

Lemma Is_true_neq_left x : x ≡ false → ¬x.
Proof.
  intros E1 E2.
  pose proof (Is_true_eq_true x E2).
  subst. discriminate.
Qed.

Lemma takeUntil_wd {A B} {P : Stream A → bool} {s:Stream A} (ex1 ex2 : LazyExists P s) (cons : A → B → B) (nil : B) : 
  takeUntil P ex1 cons nil ≡ takeUntil P ex2 cons nil.
Proof.
 assert (H:=ex1).
 induction H; case ex1; clear ex1; case ex2; clear ex2; simpl;
   destruct (P x); try contradiction; auto.
 intros ex2 ex1.
 rewrite (H0 tt (ex1 tt) (ex2 tt)).
 reflexivity.
Qed.

Lemma takeUntil_wd_alt `{Setoid A} `{Setoid B} `{!Proper ((=) ==> eq) (P : Stream A → bool)} `(ex1 : LazyExists P s1) 
       `(ex2 : LazyExists P s2) (cons: A → B → B) `{!Proper ((=) ==> (=) ==> (=)) cons} (nil : B) :
  s1 = s2 → takeUntil P ex1 cons nil = takeUntil P ex2 cons nil.
Proof with try easy.
  revert s2 ex2.
  assert (ex1':=ex1).
  induction ex1' as [s1 P1 | s1 P1 IH]; intros ? ? E; case ex1; clear ex1; case ex2; clear ex2; 
       simpl; case_eq (P s1); case_eq (P s2); intros P2 P3 ? ?...
           destruct (eq_true_false_abs (P s1))... now rewrite E.
          destruct (eq_true_false_abs (P s1))... now rewrite E.
         destruct (eq_true_false_abs (P s1))... now rewrite E.
        destruct (eq_true_false_abs (P s1))... now rewrite E.
       now destruct (Is_true_neq_left _ P3).
      destruct (eq_true_false_abs (P s1))... now rewrite E.
     destruct (eq_true_false_abs (P s1))... now rewrite E.
    destruct (eq_true_false_abs (P s1))... now rewrite E.
   destruct (eq_true_false_abs (P s1))... now rewrite E.
  rewrite (IH tt); now rewrite E.
Qed.

Lemma takeUntil_end {A B} (P:Stream A → bool) `(ex:LazyExists P seq) (cons:A → B → B) (nil : B) :
 P seq → takeUntil P ex cons nil ≡ nil.
Proof.
 intros H.
 rewrite <- (takeUntil_wd (B:=B) (LazyHere (P:=P) H)).
 unfold takeUntil.
 destruct (P seq);[|contradiction].
 reflexivity.
Qed.

Lemma takeUntil_step {A B} (P:Stream A → bool) `(ex:LazyExists P s) (cons: A → B → B) (nil: B) :
  ¬P s → ∃ ex' : LazyExists P (tl s), takeUntil P ex cons nil ≡ cons (hd s) (takeUntil P ex' cons nil).
Proof.
 intros H.
 assert (ex':=ex).
 destruct ex' as [H0|ex'].
  elim H; assumption.
 exists (ex' tt).
 rewrite <- (takeUntil_wd (B:=B) (LazyFurther ex')).
 simpl.
 destruct (P s).
  elim H; constructor.
 reflexivity.
Qed.

Lemma takeUntil_elim {A B} (P:Stream A → bool) (cons: A → B → B) (nil: B) (Q: Stream A → B → Prop) :
  (∀ s, P s → Q s nil) →
  (∀ s x, Q (tl s) x → ¬P s → Q s (cons (hd s) x)) →
  ∀ `(ex : LazyExists P s), Q s (takeUntil P ex cons nil).
Proof.
 intros c1 c2 s ex.
 assert (ex':=ex).
 induction ex'.
  rewrite takeUntil_end; try assumption.
  eapply c1.
  apply H.
 assert (Z0:=takeUntil_end P ex cons nil).
 assert (Z1:=takeUntil_step P ex cons nil).
 assert (Z0':=c1 x).
 assert (Z1':=c2 x).
 destruct (P x).
  clear Z1.
  rewrite Z0; try constructor.
  apply Z0'.
  constructor.
 clear Z0 Z0'.
 destruct (Z1 (λ x, x)) as [ex' Z].
 rewrite Z.
 clear Z Z1.
 eapply Z1'; auto.
 apply H0.
 constructor.
Qed.

(* Alternatively we can first compute the required length. This is useful in case we actually have to use the length *)
Definition takeUntil_length `(P : Stream A → bool) `(ex : LazyExists P s)
  := takeUntil P ex (λ _, S) O.

Fixpoint take {A B} (s : Stream A) (n : nat) (cons: A → B → B) (nil : B) : B := 
  match n with 
  | O => nil
  | S m => cons (hd s) (take (tl s) m cons nil)
  end.

Lemma takeUntil_length_correct {A} (P : Stream A → bool) `(ex : !LazyExists P s) :
  P (Str_nth_tl (takeUntil_length P ex) s).
Proof.
  assert (ex':=ex). unfold takeUntil_length.
  induction ex' as [s|s ? IH].
   now rewrite takeUntil_end.
  case_eq (P s); intros E.
   rewrite takeUntil_end; auto with *.
  destruct (takeUntil_step P ex (λ _ : A, S) O) as [ex1 E1].
   now apply Is_true_neq_left.
  rewrite E1.
  now apply (IH tt).
Qed.

Lemma takeUntil_correct {A B} (P : Stream A → bool) `(ex : !LazyExists P s) (cons: A → B → B) (nil : B) :
  takeUntil P ex cons nil ≡ take s (takeUntil_length P ex) cons nil.
Proof with auto using Is_true_eq_left, Is_true_neq_left.
  assert (ex':=ex). unfold takeUntil_length.
  induction ex' as [s|s ? IH].
   repeat rewrite takeUntil_end...
  case_eq (P s); intros E.
   repeat rewrite takeUntil_end...
  destruct (takeUntil_step P ex cons nil) as [ex1 E1]...
  rewrite E1. rewrite (IH tt)...
  destruct (takeUntil_step P ex (λ _, S) O) as [ex2 E2]...
  rewrite E2. simpl.
  rewrite (takeUntil_wd ex1 ex2 (λ _, S) O)...
Qed.

Lemma takeUntil_length_tl {A} (P : Stream A → bool) `(ex : !LazyExists P s) (Ptl : EventuallyForAll P s) :
  takeUntil_length P ex ≤ S (takeUntil_length P (LazyExists_tl ex Ptl)).
Proof.
  unfold takeUntil_length.
  destruct ex.
   rewrite takeUntil_end. now apply nat_nonneg. easy. 
  simpl.
  case_eq (P s); intros E.
   rewrite takeUntil_end. 
    now apply nat_nonneg. 
   apply Ptl. auto with *.
  reflexivity.
Qed.

Lemma takeUntil_length_Str_nth_tl {A} (P : Stream A → bool) `(ex : !LazyExists P s) (Ptl : EventuallyForAll P s) (n : nat) :
  takeUntil_length P ex ≤ n + takeUntil_length P (LazyExists_Str_nth_tl ex Ptl n).
Proof with auto with *.
  revert s ex Ptl.
  induction n; intros.
   easy.
  transitivity (S (takeUntil_length P (LazyExists_tl ex Ptl))).
   apply takeUntil_length_tl.
  simpl.
  apply le_n_S.
  unfold takeUntil_length.
  setoid_rewrite (takeUntil_wd (LazyExists_Str_nth_tl ex Ptl (S n)) 
    (LazyExists_Str_nth_tl (LazyExists_tl ex Ptl) (ForAll_Str_nth_tl 1 Ptl) n) (λ _, S) O).
  apply IHn.
Qed.

Lemma takeUntil_length_ForAllIf {A1 A2} (P1 : Stream A1 → bool) `(ex1 : LazyExists P1 s1)
       {P2 : Stream A2 → bool} `(ex2 : LazyExists P2 s2) (F : ForAllIf P2 P1 s2 s1) :
  takeUntil_length P1 ex1 ≤ takeUntil_length P2 ex2.
Proof with auto using Is_true_eq_left, Is_true_neq_left.
  revert s2 ex2 F.
  assert (ex1':=ex1).
  unfold takeUntil_length.
  induction ex1' as [s1|s1 ? IH]; intros.
   rewrite takeUntil_end... apply le_0_n.
  case_eq (P1 s1); intros EP1.
   rewrite takeUntil_end... apply le_0_n.
  destruct (takeUntil_step _ ex1 (λ _, S) O) as [ex1' E1']...
  rewrite E1'. 
  assert (ex2':=ex2).
  induction ex2' as [s2|s2 ? IH2].
   destruct F. 
   rewrite takeUntil_end in E1'...
   discriminate.
  case_eq (P2 s2); intros EP2.
   destruct F. 
   rewrite takeUntil_end in E1'...
   discriminate.
  destruct (takeUntil_step _ ex2 (λ _, S) O) as [ex2' E2']...
  rewrite E2'.
   apply le_n_S, (IH tt).
  destruct F...
Qed.

End TakeUntil.

Section Limit.
Context {X : MetricSpace}.

(** This proposition says that the entire stream is within e of l *)
Definition NearBy (l : X) (ε : QposInf) := ForAll (λ s, ball_ex ε (hd s) l).

Lemma NearBy_comp l1 l2 :
  l1 = l2 → ∀ ε1 ε2, QposEq ε1 ε2 → ∀ s, (NearBy l1 ε1 s ↔ NearBy l2 ε2 s).
Proof.
 revert l1 l2.
 cut (∀ l1 l2 : X, l1 = l2 → ∀ ε1 ε2 : Qpos,
   QposEq ε1 ε2 → ∀ s : Stream X, NearBy l1 ε1 s → NearBy l2 ε2 s).
  intros.
  split.
   firstorder.
  intros.
  eapply H.
    symmetry.
    apply H0.
   unfold QposEq; symmetry.
   apply H1.
  assumption.
 unfold NearBy; simpl.
 intros l1 l2 Hl ε1 ε2 Hε.
 cofix.
 intros s [H0 H].
 constructor.
  simpl.
  rewrite <- Hl.
  rewrite <- Hε.
  assumption.
 auto.
Qed.

Lemma NearBy_weak l (ε1 ε2 : Qpos) : 
  ε1 <= ε2 → ∀ s, NearBy l ε1 s → NearBy l ε2 s.
Proof.
 unfold NearBy; simpl.
 cofix.
 intros Hε s [H0 H].
 constructor.
  eapply ball_weak_le.
   apply Hε.
  assumption.
 auto.
Qed.

Lemma NearBy_Infinity (s : Stream X) (x : X) : NearBy x QposInfinity s.
Proof with trivial.
  unfold NearBy. simpl.
  revert s.
  cofix.
  constructor...
Qed.

Lemma Nearby_tl `(H : NearBy l ε s) : NearBy l ε (tl s).
Proof. now destruct H. Defined.

Lemma Nearby_Str_nth_tl `(H : NearBy l ε s) : ∀ n, NearBy l ε (Str_nth_tl n s).
Proof.
  induction n.
   easy.
  simpl. rewrite <-tl_nth_tl. now apply Nearby_tl.
Defined.

Lemma Nearby_EventuallyForAll l ε s : EventuallyForAll (NearBy l ε) s.
Proof.
  revert s.
  cofix FIX. constructor.
   now apply Nearby_tl.
  now apply (FIX (tl s)).
Defined.

(** l is the limit if for every e there exists a point where the stream is
always within e of l. *)
Class Limit (s : Stream X) (l:X) := limit: ∀ ε, LazyExists (NearBy l ε) s.

Global Instance Limit_tl `(H : Limit s l) : Limit (tl s) l.
Proof.
 intros ε.
 destruct (H ε) as [[_ H']|H'].
  left; auto.
 apply H'.
 constructor.
Defined.

Global Instance Limit_Str_nth_tl `(H : Limit s l) : ∀ n, Limit (Str_nth_tl n s) l.
Proof.
 intros n.
 revert s l H.
 induction n.
  tauto.
 intros.
 simpl.
 apply IHn.
 now apply Limit_tl.
Defined.

End Limit.
(* begin hide *)
Implicit Arguments NearBy [X].
Implicit Arguments Limit [X].
(* end hide *)
