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
Require Export Streams.
Require Import Unicode.Utf8 Utf8_core.
Require Import abstract_algebra theory.streams orders.naturals.

Set Implicit Arguments.
(**
** Limits
A predicate saying there exists a point in the stream where a predicate
is satsified.

We take the unusual step of puting this inductive type in Prop even
though it contains constructive information.  This is because we expect
this proof to only be used in proofs of termination. *)
Inductive LazyExists A (P:Stream A -> Prop) (x: Stream A) : Prop :=
  | LazyHere : P x -> LazyExists P x
  | LazyFurther : (unit -> LazyExists P (tl x)) -> LazyExists P x.

Lemma LazyExists_tl {A} (P:Stream A → Prop) `(ex : !LazyExists P s) (Ptl : EventuallyForAll P s) : 
  LazyExists P (tl s).
Proof. 
  destruct ex as [? | further]. 
   left. destruct Ptl. now auto.
  apply (further tt).
Defined.

Lemma LazyExists_Str_nth_tl {A} (P:Stream A → Prop) `(ex : !LazyExists P s) (Ptl : EventuallyForAll P s) (n : nat) : 
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

Section TakeUntil.
(* begin hide *)
Coercion Local Is_true : bool >-> Sortclass.
(* end hide *)
(** takeUntil creates a list of of elements upto a the point where the predicate
P is satisfied.  For efficency reasons it doesn't actually build a list, but
takes continuations for cons and nil instead.  To build an actual list pass in
the const and nil constructors. *)
Fixpoint takeUntil (A B:Type) (P : Stream A -> bool)(s:Stream A) (ex:LazyExists P s) (cons: A -> B -> B) (nil : B) {struct ex} : B :=
(if P s as b return ((P s -> b) -> B)
then fun _ => nil
else fun (n : P s -> False) => cons (hd s)
     (@takeUntil A B P (tl s)
      match ex with
      | LazyHere H => (False_ind _ (n H))
      | LazyFurther ex0 => ex0 tt
      end cons nil))
(fun x => x).

Lemma Is_true_neq_left x : x ≡ false → ¬x.
Proof.
  intros E1 E2.
  pose proof (Is_true_eq_true x E2).
  subst. discriminate.
Qed.

Lemma takeUntil_wd : forall (A B:Type) (P : Stream A -> bool)(s:Stream A)(ex1 ex2:LazyExists P s) (cons: A -> B -> B) (nil:B),
  takeUntil P ex1 cons nil ≡ takeUntil P ex2 cons nil.
Proof.
 intros A B P s ex1 ex2 cons nil.
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
       now destruct (Is_true_neq_left P3).
      destruct (eq_true_false_abs (P s1))... now rewrite E.
     destruct (eq_true_false_abs (P s1))... now rewrite E.
    destruct (eq_true_false_abs (P s1))... now rewrite E.
   destruct (eq_true_false_abs (P s1))... now rewrite E.
  now rewrite (IH tt) E. 
Qed.

Lemma takeUntil_end : forall (A B:Type) (P:Stream A -> bool) seq (ex:LazyExists P seq) (cons:A -> B -> B) (nil : B),
 P seq -> takeUntil P ex cons nil ≡ nil.
Proof.
 intros A B P seq ex cons nil H.
 rewrite <- (takeUntil_wd (B:=B) P (LazyHere P _ H)).
 unfold takeUntil.
 destruct (P seq);[|contradiction].
 reflexivity.
Qed.

Lemma takeUntil_step : forall (A B:Type) (P:Stream A -> bool) seq (ex:LazyExists P seq) (cons: A -> B -> B) (nil: B),
 ~P seq -> exists ex':(LazyExists P (tl seq)), takeUntil P ex cons nil ≡ cons (hd seq) (takeUntil P ex' cons nil).
Proof.
 intros A B P seq ex cons nil H.
 assert (ex':=ex).
 destruct ex' as [H0|ex'].
  elim H; assumption.
 exists (ex' tt).
 rewrite <- (takeUntil_wd (B:=B) P (LazyFurther seq ex')).
 simpl.
 destruct (P seq).
  elim H; constructor.
 reflexivity.
Qed.

Lemma takeUntil_elim : forall (A B:Type) (P:Stream A -> bool) (cons: A -> B -> B) (nil: B)
 (Q: Stream A -> B -> Prop),
 (forall seq, P seq -> Q seq nil) ->
 (forall seq x, Q (tl seq) x -> ~P seq -> Q seq (cons (hd seq) x)) ->
 forall seq (ex:LazyExists P seq), Q seq (takeUntil P ex cons nil).
Proof.
 intros A B P cons nil Q c1 c2 seq ex.
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
 destruct (Z1 (fun x => x)) as [ex' Z].
 rewrite Z.
 clear Z Z1.
 eapply Z1'; auto.
 apply H0.
 constructor.
Qed.

(* Alternatively we can first compute the required length. This is useful in case we actually have to use the length *)
Definition takeUntil_length {A} (P : Stream A → bool) (s : Stream A) (ex : LazyExists P s)
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
  rewrite (takeUntil_wd P ex1 ex2 (λ _, S) O)...
Qed.

Lemma takeUntil_length_tl {A} (P : Stream A → bool) `(ex : !LazyExists P s) (Ptl : EventuallyForAll P s) :
  takeUntil_length P ex ≤ S (takeUntil_length P (LazyExists_tl ex Ptl)).
Proof.
  unfold takeUntil_length.
  destruct ex.
   rewrite takeUntil_end. now apply naturals_nonneg. easy. 
  simpl.
  case_eq (P s); intros E.
   rewrite takeUntil_end. 
    now apply naturals_nonneg. 
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
  rewrite (takeUntil_wd P (LazyExists_Str_nth_tl ex Ptl (S n)) 
    (LazyExists_Str_nth_tl (LazyExists_tl ex Ptl) (ForAll_Str_nth_tl 1 Ptl) n) (λ _, S) O).
  apply IHn.
Qed.

Lemma takeUntil_length_ForAllIf {A1 A2} (P1 : Stream A1 → bool) {s1 : Stream A1} (ex1 : LazyExists P1 s1)
       (P2 : Stream A2 → bool) {s2 : Stream A2} (ex2 : LazyExists P2 s2) (F : ForAllIf P2 P1 s2 s1) :
  takeUntil_length P1 ex1 ≤ takeUntil_length P2 ex2.
Proof with auto using Is_true_eq_left, Is_true_neq_left.
  revert s2 ex2 F.
  assert (ex1':=ex1).
  unfold takeUntil_length.
  induction ex1' as [s1|s1 ? IH]; intros.
   rewrite takeUntil_end... apply le_0_n.
  case_eq (P1 s1); intros EP1.
   rewrite takeUntil_end... apply le_0_n.
  destruct (takeUntil_step P1 ex1 (λ _, S) O) as [ex1' E1']...
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
  destruct (takeUntil_step P2 ex2 (λ _, S) O) as [ex2' E2']...
  rewrite E2'.
   apply le_n_S, (IH tt).
  destruct F...
Qed.

End TakeUntil.

Section Limit.

Variable X : MetricSpace.

(** This proposition says that the entire stream is within e of l *)
Definition NearBy (l:X)(e:QposInf) := ForAll (fun (s:Stream X) => ball_ex e (hd s) l).

Lemma NearBy_comp: forall l1 l2, st_eq l1 l2 -> forall (e1 e2:Qpos), QposEq e1 e2 -> forall s, (NearBy l1 e1 s <-> NearBy l2 e2 s).
Proof.
 cut (forall l1 l2 : X, st_eq l1 l2 -> forall e1 e2 : Qpos,
   QposEq e1 e2 -> forall s : Stream X, NearBy l1 e1 s -> NearBy l2 e2 s).
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
 intros l1 l2 Hl e1 e2 He.
 cofix.
 intros s [H0 H].
 constructor.
  simpl.
  rewrite <- Hl.
  rewrite <- He.
  assumption.
 auto.
Qed.

Lemma NearBy_weak: forall l (e1 e2:Qpos), e1 <= e2 -> forall s, NearBy l e1 s -> NearBy l e2 s.
Proof.
 unfold NearBy; simpl.
 intros l e1 e2 He.
 cofix.
 intros s [H0 H].
 constructor.
  eapply ball_weak_le.
   apply He.
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

(** l is the limit if for every e there exists a point where the stream is
always within e of l. *)
Class Limit (s:Stream X) (l:X) := limit: forall e, LazyExists (NearBy l e) s.

Global Instance Limit_tl `{H : Limit s l} : Limit (tl s) l.
Proof.
 intros e.
 destruct (H e) as [[_ H']|H'].
  left; auto.
 apply H'.
 constructor.
Defined.

Global Instance Limit_Str_nth_tl `{H : Limit s l} : forall n, Limit (Str_nth_tl n s) l.
Proof.
 intros n.
 revert s l H.
 induction n.
  tauto.
 intros.
 simpl.
 apply IHn.
 apply Limit_tl.
Defined.

End Limit.
(* begin hide *)
Implicit Arguments NearBy [X].
Implicit Arguments Limit [X].
(* end hide *)
