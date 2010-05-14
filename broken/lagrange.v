Require Import ssreflect CSetoids CSetoidFun 
  CFields CPolynomials Program  
  Omega Equivalence Morphisms 
  Wf Morphisms CRings  
  CRing_Homomorphisms Rational Setoid 
  CPoly_NthCoeff CPoly_Degree CReals Intervals
  CauchySeq IntervalFunct MoreIntervals
  MoreFunctions Composition.
Require Import seq.

Open Scope program_scope.

(**
 * The sq(uash) and unsq(uash) tricks are just
 * hacks because we are dealing with a flaw in
 * the Program Fixpoint construct. Bas and other
 * people are working on this. It is assumed that
 * this construct will not be required in the
 * final version of this proof.
 *)
Inductive sq (A : Type) : Prop := 
  insq : A -> (sq A).

Axiom unsq : forall A : Type, (sq A) -> A.

(**
 * A 'fresh' sequence is a sequence where no two 
 * elements are the same. Therefore, we know that 
 * for elements a, b in such a sequence it holds 
 * that a - b =/= 0. The following section deals 
 * with fresh sequences. 
 *)
Section FreshSeq.

Variable A : CSetoid.

(**
 * Freshness of a sequence relative to one
 * element. 
 *)
Lemma fresh (s : seq A) : A -> Type.
intro s. 
induction s as [a|b s fresh_s].
exact (fun _ => True).
exact (fun a => (b [#] a) and (fresh_s a)).
Defined.

(**
 * 'Squashed' version of the freshness property.
 * For more information, read the Type vs. Prop
 * discussion above.
 *)
Definition sqfresh (s : seq A) (a : A) := 
  (sq (fresh s a)).

(**
 * A fresh sequence is a sequence where every
 * two elements lie apart. It is similar to the
 * normal sequence type. 
 *)
Inductive fresh_seq : seq A -> Prop :=
  | fresh_nil : fresh_seq nil
  | fresh_cons : forall x s, 
      sqfresh s x -> fresh_seq s -> 
      fresh_seq (x :: s).

(**
 * If we an element a is fresh (relative to a 
 * sequence s), then a is also fresh relative
 * to any subsequence of s.
 *)
Lemma take_fresh : forall (n : nat) 
  (s : seq A) (a : A), fresh s a -> 
  fresh (take n s) a.
Proof.
  intro n; induction n.  
  intros s a H; rewrite take0; simpl; auto.
  intros s a H; destruct s; simpl; auto.
  simpl; split.
  by inversion H.
  apply IHn; by inversion H.
Defined.

(**
 * Any subsequence we take from the beginning of a fresh
 * sequence is still fresh.
 *)
Lemma take_fresh_seq : forall (n : nat) 
  (s : seq A), fresh_seq s -> 
  fresh_seq (take n s).
Proof.
  intro n; induction n.
  intros s H; simpl; rewrite take0; exact fresh_nil.
  intros s H; destruct s; simpl; auto.
  simpl; apply fresh_cons.
  unfold sqfresh; apply insq; apply take_fresh.
  apply unsq; by inversion H.
  apply IHn; by inversion H.
Defined.

(**
 * If an element is fresh with respect to a certain
 * sequence, it results in a fresh sequence if we add
 * this element to the rear of this sequence.
 *)
Lemma rcons_fresh : forall (s : seq A) 
  (a t : A), fresh (t :: s) a -> fresh (rcons s t) a.
Proof.
  intros s a t H; induction s.
  simpl; by inversion H.
  simpl; inversion H; inversion X0; split.
  auto.
  apply IHs; simpl; by split.
Defined.

(**
 * The inverse of the previous theorem. If an element
 * added to the rear of a sequence results in a fresh
 * sequence, we might instead add this element in the
 * front and still come up with a fresh sequence.
 *)
Lemma fresh_rcons : forall (s : seq A)
  (a t : A), fresh (rcons s t) a -> fresh (t :: s) a.
Proof.
  intros s a t H; induction s.
  simpl; by inversion H.
  simpl; simpl in H; split.
  apply IHs; by inversion H.
  split.
  by inversion H.
  apply IHs; by inversion H.
Defined.

(**
 * Freshness remains if we reverse a sequence.
 *)
Lemma rev_fresh : forall (s : seq A) (a : A),
  fresh s a -> fresh (rev s) a.
Proof.
  intros s a H; induction s.
  auto. 
  rewrite rev_cons; apply rcons_fresh; simpl; split.
  by inversion H.
  apply IHs; by inversion H.
Defined.

(**
 * If we have a fresh sequence with one element on front,
 * the sequence remains fresh if we add this element to
 * the rear.
 *)
Lemma rcons_fresh_seq : forall (s : seq A) 
  (a : A), fresh_seq (a :: s) -> 
  fresh_seq (rcons s a).
Proof.
  intros s a H; induction s.
  auto.
  simpl; apply fresh_cons.
  unfold sqfresh; inversion H; apply insq.
  apply rcons_fresh; simpl; unfold sqfresh in H2.
  assert (fresh (t :: s) a).
  by apply unsq.
  inversion X.
  split.
  algebra.
  assert (sq (fresh s t)).
  inversion H3; auto.
  by apply unsq in H4.
  apply IHs; inversion H; apply fresh_cons.
  inversion H2; inversion X; unfold sqfresh; by apply insq.
  by inversion H3.
Defined.

(**
 * If a sequence with a specific element on its rear is
 * fresh, the sequence is still fresh if we would have
 * added this element in the front.
 *)
Lemma fresh_seq_rcons : forall (s : seq A) 
  (a : A), fresh_seq (rcons s a) -> 
  fresh_seq (a :: s).
Proof.
  intros; induction s. auto.
  simpl in H; inversion H; apply fresh_cons.
  unfold sqfresh; apply insq.
  assert (fresh (a :: s) t); apply fresh_rcons.
  unfold sqfresh in H2; by apply unsq in H2.
  simpl; simpl in X; inversion X; apply unsq; inversion H.
  assert (fresh_seq (a :: s)). 
  by apply IHs.
  apply insq; apply rcons_fresh; simpl; split.
  algebra. 
  apply unsq; inversion H8. 
  unfold sqfresh in H11; apply unsq in H11; by apply insq.
  apply fresh_cons; unfold sqfresh in H2; apply unsq in H2.
  apply fresh_rcons in H2; inversion H2; unfold sqfresh.
  by apply insq.
  assert (fresh_seq (a :: s)).
  by apply IHs.
  by inversion H4.
Defined.

(**
 * If a sequence is fresh, it remains fresh if we completely
 * reverse it.
 *)
Lemma rev_fresh_seq : forall (s : seq A),
  fresh_seq s -> fresh_seq (rev s).
Proof.
  intros; induction s. auto.
  rewrite rev_cons; apply rcons_fresh_seq; apply fresh_cons.
  inversion H; unfold sqfresh; apply insq; apply rev_fresh.
  unfold sqfresh in H2; by apply unsq.
  apply IHs; by inversion H.
Defined.

Hint Constructors fresh_seq.
  
End FreshSeq.

(**
 * The definitions and lemmas for Newton 
 * polynomials hold for polynomials over an
 * arbitrary field K. We will later confine
 * this K to the real numbers R.
 *)

Section NewtonPolynomials.

Variable K : CField.
Variable f : K -> K.

(**
 * The definition of the divided differences
 * follows here. This is the function f [..]
 * as described in the paper written by Bas.
 * To avoid any confusion, the notation f ()
 * is used for the polynomial subject to
 * interpolation.
 *)
Program Fixpoint dd (s : seq K) (P : fresh_seq K s) 
  {measure (size s)} : K :=
match s with
| nil => Zero
| (a :: nil) => (f a)
| (a :: b :: s') =>
    ((dd (a :: s') _) [-] (dd (b :: s') _) [/]
    (a [-] b) [//] _)
end.

Next Obligation.
apply fresh_cons; inversion P; inversion H1.
inversion X; unfold sqfresh; by apply insq.
inversion P; by inversion H2.
Qed.

Next Obligation.
by inversion P.
Qed.

Next Obligation.
apply minus_ap_zero; apply unsq; inversion P; inversion H1.
inversion X; apply insq; algebra.
Qed.


(**
 * Now that we have solved all obligations for
 * the definition of divided differences, we  
 * continue with our definitions of the functions
 * N, alpha and eta.
 *)
Variable s : seq K.
Variable k : nat.
Hypothesis fresh_s : fresh_seq K s.

(**
 * This definition still uses the bigopsClass, but it will be
 * replaced by a fold until the problems in bigopsClass are
 * resolved. This definition of eta corresponds to the 
 * definition of n_j(x) in the paper written by Bas.
 *
 * TODO: Replace bigopsClass definitions by folds
 *)
Require Export bigopsClass.
Definition eta (j : nat) : cpoly_cring K :=
  \big[(cpoly_mult_cs K)/(cpoly_one K)]_(x_i <- take j s)
    (cpoly_linear _ ([--] x_i) (cpoly_one _)).

(**
 * This definition corresponds to the definition of a_j in
 * the paper. It is basically a direct call to the definition
 * of divided differences using the vector x_j, ..., x_0.
 *)
Definition alpha (j : nat) : K :=
  dd (rev (take (j + 1) s))
    ((rev_fresh_seq K (take (j + 1) s))
      (take_fresh_seq K (j + 1) s fresh_s)).

(**
 * This is the definition of N from the paper. The mkseq
 * construct creates an increasing sequence. 
 * 
 * TODO: Replace bigopsClass definitions by folds.
 *)
Definition N : cpoly_cring K :=
  \big[cpoly_plus_cs K/(cpoly_zero K)]_(j <- 
    (mkseq (fun x => x) (k + 1)) | (fun x => true) j)
     (_C_ (alpha j) [*] (eta j)).

End NewtonPolynomials.

Section BigopsTheory.

Variable K : CField.
Variable f : K -> K.

(**
 * This is proof independence of divided differences with
 * respect to freshness. 
 *)
Lemma dd_indep : forall (l1 l2 : seq K) (P1 : fresh_seq K l1)
  (P2 : fresh_seq K l2), l1 = l2 -> 
    dd K f l1 P1 [=] dd K f l2 P2.
Proof.
  intros.
  unfold dd.
  replace (existT (fun s : seq K => fresh_seq K s) l2 P2) with
    (existT (fun s : seq K => fresh_seq K s) l1 P1).
  reflexivity.
  by apply subsetT_eq_compat.
Qed.

(**
 * Equality of CPolynomials over a field K is reflexive,
 * symmetric and transitive according to the following 
 * three type class instances.
 *)
Instance cpoly_eq_refl : Reflexive (cpoly_eq K).
unfold Reflexive; by reflexivity. Qed.

Instance cpoly_eq_symm : Symmetric (cpoly_eq K).
unfold Symmetric; by symmetry. Qed.

Instance cpoly_eq_trans : Transitive (cpoly_eq K).
unfold Transitive; intros x y z; by transitivity y. Qed.

Instance eqv_cpoly : Equivalence (cpoly_eq K).

Instance eqv_K : Equivalence (@st_eq K).

(**
 * TODO: This definition is not required because we have
 * an equivalent construct in the type class system.
 *)
Add Parametric Relation : (cpoly_cring K) (cpoly_eq K)
  reflexivity proved by cpoly_eq_refl
  symmetry proved by cpoly_eq_symm
  transitivity proved by cpoly_eq_trans
  as cpeq.

(**
 * This is meant to prove that addition of polynomials 
 * is a morphism with respect to equality. However, I
 * cannot complete the proof because it somehow seems
 * that this exact morphism is required to finish the
 * proof.
 *
 * TODO: Fix this proof.
 *)
Instance morph_cpoly : Proper ((cpoly_eq K) ==> (cpoly_eq K) ==>
  (cpoly_eq K)) (cpoly_plus_cs K).
Admitted.

(**
 * Multiplication of polynomials is also a morphism with
 * respect to equality. However, the same problem as in
 * the previous proof arises here.
 * 
 * TODO: Complete this proof.
 *)
Instance morph_cpoly_mult : Proper ((cpoly_eq K) ==> (cpoly_eq K) ==> 
  (cpoly_eq K)) (cpoly_mult_cs K).
Admitted.

(**
 * Multiplication in an arbitrary field K is a morphism with
 * respect to the standard equality defined in K.
 * 
 * TODO: Are definitions like these really required? Aren't
 * they already defined in the CoRN libraries?
 *)
Instance morph_K_mult : Proper ((@st_eq K) ==> (@st_eq K) ==> (@st_eq K))
  cr_mult.
unfold Proper; unfold respectful.
intros x y H x0 y0 H0; rewrite H H0; reflexivity.
Qed.

(**
 * Addition in a field K is a morphism with respect to the
 * standard equality defined on K.
 *)
Instance morph_K_plus : Proper ((@st_eq K) ==> (@st_eq K) ==> (@st_eq K))
  csg_op.
unfold Proper; unfold respectful.
intros x y H x0 y0 H0; rewrite H H0; reflexivity.
Qed.

(**
 * Addition of polynomials is associative.
 *
 * TODO: As OperationClasses is no longer compiling, this
 * has to be replaced with another construct.
 *)
Instance assoc_cpoly : @OperationClasses.associative (cpoly_cring K) 
  (cpoly_eq K) eqv_cpoly (cpoly_plus_cs K).
unfold OperationClasses.associative.
intros x y z; red.
set cpoly_plus_associative.
unfold associative in a; simpl in a; apply a.
Qed.

(**
 * Multiplication of polynomials is associatve.
 * 
 * TODO: Fix usage of OperationClasses.
 *)
Instance assoc_cpoly_mult : @OperationClasses.associative (cpoly_cring K) 
  (cpoly_eq K) eqv_cpoly (cpoly_mult_cs K).
unfold OperationClasses.associative.
intros x y z; red.
set cpoly_mult_assoc.
unfold associative in a; simpl in a; apply a.
Qed.

(**
 * Multiplication is associative in any field K
 *
 * TODO: This should be replaced by a standard lemma from
 * the CoRN libraries.
 *)
Instance assoc_K_mult : @OperationClasses.associative K
  (@st_eq K) eqv_K cr_mult.
unfold OperationClasses.associative.
intros x y z; red; algebra.
Qed.

(**
 * Addition is associative in any field K
 *
 * TODO: This is very probably already somewhere in the
 * libraries.
 *)
Instance assoc_K_plus : @OperationClasses.associative K
  (@st_eq K) eqv_K csg_op.
unfold OperationClasses.associative.
intros x y z; red; algebra.
Qed.

(**
 * The zero-polynomial is a left-unit element with respect
 * to addition.
 *
 * TODO: Fix OperationClasses usage.
 *)
Instance left_unit_cpoly : @OperationClasses.left_unit (cpoly_cring K) 
  (cpoly_eq K) eqv_cpoly (cpoly_plus_cs K) (cpoly_zero K).
intro x; red.
simpl; reflexivity.
Qed.

(**
 * The one-polynomial is a left-unit element with respect
 * to multiplication.
 *
 * TODO: Fix OperationClasses usage.
 *)
Instance left_unit_cpoly_mult : @OperationClasses.left_unit (cpoly_cring K) 
  (cpoly_eq K) eqv_cpoly (cpoly_mult_cs K) (cpoly_one K).
intro x; red.
rewrite cpoly_mult_commutative.
rewrite cpoly_mult_one.
reflexivity.
Qed.

(**
 * TODO: Deprecated, do not use OperationClasses.
 *)
Instance left_unit_K_mult : @OperationClasses.left_unit K 
  (@st_eq K) eqv_K cr_mult (One:K).
intro x; red; algebra.
Qed.

(**
 * TODO: Deprecated, do not use Operationclasses.
 *)
Instance left_unit_K_plus : @OperationClasses.left_unit K
  (@st_eq K) eqv_K csg_op (Zero:K).
intro x; red; algebra.
Qed.

(**
 * The zero-polynomial is a right-unit element with respect
 * to to addition of polynomials.
 * 
 * TODO: Get rid of OperationClasses code.
 *)
Instance right_unit_cpoly : @OperationClasses.right_unit (cpoly_cring K)
  (cpoly_eq K) eqv_cpoly (cpoly_plus_cs K) (cpoly_zero K).
intro x; red.
rewrite cpoly_plus_commutative; simpl; reflexivity.
Qed.

(**
 * The one-polynomial is a right-unit element with respect
 * to multiplication of polynomials.
 *
 * TODO: Get rid of OperationClasses code.
 *)
Instance right_unit_cpoly_mult : @OperationClasses.right_unit (cpoly_cring K)
  (cpoly_eq K) eqv_cpoly (cpoly_mult_cs K) (cpoly_one K).
intro x; red.
rewrite cpoly_mult_one; reflexivity.
Qed.

(**
 * TODO: Deprecated, do not use OperationClasses code.
 *)
Instance right_unit_K_mult : @OperationClasses.right_unit K
  (@st_eq K) eqv_K cr_mult (One:K).
intro x; red; algebra.
Qed.

(**
 * TODO: Deprecated, do not use OperationClasses code.
 *)
Instance right_unit_K_plus : @OperationClasses.right_unit K
  (@st_eq K) eqv_K csg_op (Zero:K).
intro x; red; algebra.
Qed.

(**
 * Application of polynomials (over K) is a morphism with 
 * respect to the standard equality defined on K.
 *
 * TODO: Fix this proof. To be honest, I have no clue why
 * this cannot be done. Will take a look at it later.
 *)
Add Parametric Morphism : (@cpoly_apply K) with
 signature (@cpoly_eq K) ==> (@st_eq K) ==> (@st_eq K) as cpoly_apply_mor.
Admitted.

(**
 * Multiplication of polynomials is a morphism with respect
 * to the equality defined on polynomials.
 *
 * TODO: Replace with type class instance.
 *)
Add Parametric Morphism : (@cpoly_mult_cs K) with
 signature (@cpoly_eq K) ==> (@cpoly_eq K) ==> (@cpoly_eq K) as cpoly_mult_mor.
intros x y H x0 y0 H0.
rewrite H; rewrite H0; reflexivity.
Qed.

(**
 * TODO: Replace with type class instance.
 *)
Add Parametric Morphism : (@polyconst K) with
  signature (@st_eq K) ==> (@cpoly_eq K) as cpoly_const_mor.
intros x y H; rewrite H; reflexivity.
Qed.

(**
 * Multiplication of a polynomial (over any field K) and an
 * element from K is invariant under both equality over poly(K)
 * and K.
 *
 * TODO: Fix this proof. Seems to mutually depend on a previous
 * morphism for polynomial-multiplication.
 *)
Add Parametric Morphism : (@cpoly_mult_cr_cs K) with
  signature (@cpoly_eq K) ==> (@st_eq K) ==> (cpoly_eq K) as cpoly_mult_cr_mor.
intros x y H x0 y0 H0.
Admitted.

(**
 * TODO: Replace with corresponding type class instance.
 *)
Add Parametric Morphism : (@cg_minus K) with
  signature (@st_eq K) ==> (@st_eq K) ==> (@st_eq K) as cg_minus_mor.
intros x y H x0 y0 H0; rewrite H; rewrite H0; reflexivity.
Qed.

(**
 * Getting the nth coefficient of a polynomial is a morphism
 * with respect to equality over nat.
 *
 * TODO: Fix this proof. Should not be very difficult. Will
 * take a look at it later.
 *)
Add Parametric Morphism : (@nth_coeff K) with
  signature (@eq nat) ==> (@cpoly_eq K) ==> (@st_eq K) as nth_coeff_mor.
intros y x y0 H.
Admitted.

(**
 * TODO: Replace with corresponding type class instance
 *)
Add Parametric Morphism : (@csg_op K) with
  signature (@st_eq K) ==> (@st_eq K) ==> (@st_eq K) as csg_op_mor.
intros x y H x0 y0 H0; rewrite H H0; reflexivity.
Qed.

(**
 * TODO: Replace with corresponding type class instance
 *)
Add Parametric Morphism : (@cg_inv K) with
  signature (@st_eq K) ==> (@st_eq K) as cg_inv_mor.
intros x y H; rewrite H; reflexivity.
Qed.

(**
 * The equality on K can be continued to an equality on
 * polynomials. However, it was not immediately clear how
 * to prove this. 
 *
 * TODO: Replace with corresponding definition from the
 * CoRN libraries.
 *)
Add Parametric Morphism : (@cpoly_linear K) with
  signature (@st_eq K) ==> (@cpoly_eq K) ==> (@cpoly_eq K) as cpoly_lin_mor.
intros x y H x0 y0 H0.
Admitted.

(**
 * I have not been able to get rings to work for polynomials.
 * 
 * TODO: Fix this because it makes many proofs easier to
 * understand.
 * 
 * Add Ring cpolyk_th : (CRing_Ring (cpoly_cring K)).
 * Add Ring cring_K : (CRing_Ring K).
 *
 *)

(**
 * If a bigops-expression results in a polynomial, and if
 * this expression is therefore applied to a particular 
 * value, the application results in the same value as if
 * the application was done inside the bigops-expression.
 *
 * TODO: This should be more general.
 * TODO: Replace the bigops expression with a corresponding
 * fold.
 *)
Lemma apply_bigops : forall (r : seq K) F x,
  (\big[cpoly_mult_cs K/cpoly_one K]_(i <- r) F i) ! x [=]
  \big[cr_mult/(One:K)]_(i <- r) ((F i) ! x).
Proof.
  intros r F x; destruct r; simpl.
  rewrite cring_mult_zero; algebra.
  induction r.
  simpl; rewrite mult_one; rewrite cpoly_mult_one. 
  reflexivity.
  repeat rewrite big_cons; simpl in IHr; rewrite mult_assoc.
  rewrite (mult_commutes K (cpoly_apply K (F s) x)
    (cpoly_apply K (F t) x)).
  rewrite <- mult_assoc; rewrite <- IHr.
  set (@mult_apply); simpl in s0; rewrite <- s0.
  rewrite cpoly_mult_fast_equiv.
  set (@cpoly_mult_assoc); unfold CSetoids.associative in a.
  simpl in a; repeat rewrite a.
  rewrite (cpoly_mult_commutative K (F s) (F t)).
  reflexivity.
Qed.
  
(**
 * If we take a subsequence from (the start of) 
 * another sequence, it does not matter if this
 * sequence was already the result of a 'take' operation.
 *)
Lemma take_nest_redun : forall (n m : nat)
  (s : seq K), m <= n -> m <= size s ->
  take m (take n s) = take m s.
Proof.
  intro n; induction n.
  intros m s H H0; rewrite take0; inversion H.
  repeat rewrite take0; reflexivity.
  intros m s H H0. destruct s. simpl; reflexivity.
  assert (take (S n) (s :: s0) = s :: take n s0) by auto.
  rewrite H1; destruct m. simpl; reflexivity.
  simpl; rewrite IHn. reflexivity. omega.
  inversion H0. auto. omega.
Qed.

(**
 * This lemma effectively says that:
 *
 * x_0, x_1, ..., x_(k+1) = x_0, x_1, ..., x_i, x_(i+1), 
 * ..., x_(k+1)
 *
 * TODO: Perhaps all these takes, nths and drops can be
 * set up a bit more clearer. 
 *)
Lemma take_nth_drop : forall (i k : nat) (s : seq K),
  i <= k -> k < size s -> 
  take (S k) s = take i s ++ (nth Zero s i) ::
    (take (k - i) (drop (i + 1) s)).
Proof.
  intro i; induction i.
  intros k s H H0; destruct s.
  inversion H0; simpl.
  replace (k - 0) with k by omega; simpl.
  rewrite drop0; reflexivity.
  intros k s H H0; destruct s.
  inversion H0; simpl.
  replace (k - S i) with ((k - 1) - i) by omega.
  simpl; rewrite <- IHi.
  replace (S (k - 1)) with k by omega; reflexivity.
  omega. inversion H0.
  assert (1 <= k) by omega; omega.
  assert (1 <= k) by omega; omega.
Qed.

(**
 * This lemma asserts that the repeated multiplication 
 * of an expression (-x_i) + x_i is equal to zero.
 *)
Lemma lem11a : forall i s k,
  size s > 1 -> k < size s -> i <= k ->
  \big[cr_mult/(One:K)]_(x_i <- take (S k) s)
    (cpoly_linear K [--]x_i (cpoly_one K)) ! (nth Zero s i) [=] Zero.
Proof.
  intros.
  rewrite (@eq_big_idx_seq K (@st_eq K)
    eqv_K (cr_mult) (One:K) morph_K_mult
    right_unit_K_mult (One:K) K 
    (take (S k) s) _ 
    (fun x : K => (cpoly_linear K [--]x (cpoly_one K)) !
    (nth Zero s i)) right_unit_K_mult).
  assert (take (S k) s = (take i s) ++ ((nth Zero s i) :: 
    (take (k - i) (drop (i + 1) s)))).
  apply take_nth_drop.
  omega.
  exact H0.
  rewrite H2.
  rewrite (@big_cat K (@st_eq K) eqv_K
    cr_mult (One:K) morph_K_mult
    assoc_K_mult left_unit_K_mult 
    K (take i s) (nth Zero s i :: take (k - i) (drop (i + 1) s))  
    (fun x : K => true)).
  rewrite big_cons.
  assert ((cpoly_linear K [--](nth Zero s i) (cpoly_one K)) !
    (nth Zero s i) [=] Zero).
  simpl.
  rewrite cring_mult_zero.
  rewrite cm_rht_unit_unfolded.
  rewrite mult_one.
  rewrite cg_lft_inv_unfolded.
  reflexivity.
  rewrite H3.
  rewrite mult_assoc.
  rewrite cring_mult_zero.
  rewrite mult_commutes.
  rewrite cring_mult_zero.
  reflexivity.
  destruct s.
  inversion H.
  simpl; auto.
Qed.

(**
 * If we have a fresh sequence s, it is clear that the kth
 * element is fresh with respect to a subsequence of s.
 *)
Lemma nth_fresh : forall (s : seq K) (k c : nat),
  k < size s -> fresh_seq K s ->
  fresh K (take (k - c) s) (nth Zero s k).
Proof.
  intros.
  induction c.
  assert (k - 0 = k) by omega.
  rewrite H1.
  assert (fresh_seq K (take (k + 1) s)).
  apply take_fresh_seq.
  exact H0.
  cut (take (k + 1) s = take k s ++ [:: nth Zero s k]).
  intro.
  rewrite H3 in H2.
  assert (fresh_seq K ((nth Zero s k) :: 
    take k s)).
  apply fresh_seq_rcons.
  rewrite <- cat_rcons in H2.
  rewrite cats0 in H2.
  exact H2.
  apply unsq.
  inversion H4.
  unfold sqfresh in H7.
  exact H7.
  rewrite <- cat_rcons.
  rewrite cats0.
  rewrite <- take_nth.
  replace (S k) with (k + 1) by omega.
  reflexivity.
  apply (ssrbool.introT (P := S k <= size s)).
  apply ssrnat.leP.
  omega.
  cut (take (k - S c) s = take (k - S c)
    (take (k - c) s)).
  intro.
  rewrite H1.
  apply take_fresh.
  exact IHc.
  rewrite take_nest_redun.
  reflexivity.
  omega.
  omega.
Qed.  

(**
 * If a sequence of elements is fresh, than any two
 * elements from this sequence lie apart. This is not
 * immediately clear from the definition (although it 
 * seems so) because of difficulty with the definition
 * of nth. 
 *
 * TODO: This proof can be made a bit shorter. 
 *)
Lemma ap_fresh_nth : forall (s : seq K)
  (k c : nat), 0 < k -> c < k -> k < size s -> 
  fresh_seq K s ->
  (nth Zero s k) [-] (nth Zero s (k - S c)) [#] Zero.
Proof.
  intros.
  apply minus_ap_zero.
  assert (fresh K (take (k - c) s) (nth Zero s k)).
  apply nth_fresh.
  exact H1.
  exact H2.
  assert (take (k - c) s = take (k - S c) s ++
    [:: nth Zero s (k - S c)]).
  rewrite <- cat_rcons.
  rewrite <- take_nth.
  replace (S (k - S c)) with (k - c) by omega.
  rewrite cats0.
  reflexivity.
  apply (ssrbool.introT (P := S (k - S c) <= size s)).
  apply ssrnat.leP.
  omega.
  rewrite H3 in X.
  rewrite <- cat_rcons in X.
  rewrite cats0 in X.
  apply fresh_rcons in X.
  inversion X.
  algebra.
Qed.

(**
 * This lemma is essentially a one-step reduction in the
 * definition of divided differences. However, it is not
 * as straightforwardly provable as it might seem. 
 *
 * TODO: Fix this proof. 
 *)
Lemma dd_reduce : forall (s : seq K) (a b : K)
  (P1 : fresh_seq K (a :: b :: s)) 
  (P2 : fresh_seq K (a :: s))
  (P3 : fresh_seq K (b :: s))
  (P4 : a [-] b [#] Zero),
  (dd K f (a :: b :: s) P1) = 
  (((dd K f (a :: s) P2) [-] (dd K f (b :: s) P3)) 
  [/] (a [-] b) [//] P4).
Proof.
  intros.
  Admitted.
    
(**
 * This rather complicated lemma states that if we have a
 * one-step reduction for divided differences, we also have
 * an n-step reduction according to a specific pattern.
 *
 * TODO: This lemma is very unreadable. Perhaps this can be
 * made more clear using appropriate syntax elements.
 *)
Lemma dd_reduce_nth : forall (s : seq K) (k c : nat)
  (P : fresh_seq K 
    (nth Zero s k :: rev (take (k - c) s)))
  (Q : fresh_seq K
    (nth Zero s k :: rev (take (k - S c) s)))
  (R : fresh_seq K (rev (take (k - c) s)))
  (X : (nth Zero s k) [-] (nth Zero s (k - S c)) 
    [#] Zero),
  0 < k -> c < k -> k < size s -> fresh_seq K s ->
  (dd K f (nth Zero s k :: rev (take (k - c) s)) P) [=]
  ((dd K f (nth Zero s k :: rev (take (k - S c) s)) Q)[-]
   (dd K f (rev (take (k - c) s)) R)[/]
  (nth Zero s k[-]nth Zero s (k - S c))[//]X).
Proof.
  intros. 
  assert (fresh_seq K  
    (nth Zero s k :: nth Zero s (k - S c) ::
      rev (take (k - S c) s))).
  apply fresh_cons.
  unfold sqfresh.
  apply insq.
  simpl.
  split.
  apply zero_minus_apart.
  algebra.
  apply rev_fresh.
  apply nth_fresh.
  exact H1. 
  exact H2.
  apply fresh_cons.
  unfold sqfresh.
  apply insq.
  assert (forall k, k < size s -> 
     fresh K (rev (take k s))
    (nth Zero s k)).  
  intros.
  apply rev_fresh.
  assert (take k0 s = take (k0 - 0) s).
  replace (k0 - 0) with k0 by omega; reflexivity.
  rewrite H4.
  apply nth_fresh.
  exact H3.
  exact H2.
  apply X0.
  omega.
  apply rev_fresh_seq.
  apply take_fresh_seq.
  exact H2.
  assert (rev (take (k - c) s) = 
    nth Zero s (k - S c) :: rev (take (k - S c) s)).
  assert (k - c = (S (k - S c))) by omega.
  rewrite H4.
  set (@take_nth).
  rewrite (@take_nth K Zero (k - S c) s).
  rewrite rev_rcons; reflexivity.
  apply (ssrbool.introT (P := S (k - S c) <= size s)).
  apply ssrnat.leP.
  omega.
  assert ((dd K f (nth Zero s k :: rev (take (k - c) s)) P) [=] 
    (dd K f [:: nth Zero s k, nth Zero s (k - S c) &
       rev (take (k - S c) s)] H3)).
  apply dd_indep.
  rewrite H4; reflexivity.
  rewrite H5.
  assert (fresh_seq K ((nth Zero s (k - S c)) ::
    rev (take (k - S c) s))).
  inversion H3.
  exact H9.
  assert ((dd K f (rev (take (k - c) s)) R) [=]
    (dd K f (nth Zero s (k - S c) :: rev (take (k - S c) s)) H6)).
  apply dd_indep.
  rewrite H4; reflexivity.
  unfold cf_div.
  rewrite H7.
  set (dd_reduce (rev (take (k - S c) s)) 
    (nth Zero s k) (nth Zero s (k - S c))
    H3 Q H6 X).
  unfold cf_div in e.
  rewrite e.
  reflexivity.
Qed.
    
(**
 * The Newton polynomial coincides with the Lagrange 
 * polynomial. This lemma essentially proves this. 
 *
 * TODO: Replace bigopsClass operators with corresponding
 * folds. 
 *)
Lemma lem11b : forall (k c : nat) (s : seq K) 
  (Q : fresh_seq K s)
  (R : fresh_seq K ((nth Zero s k) :: 
    (rev (take (k - c) s)))),
  0 < k -> c <= k -> k < size s -> 
  (N K f s k Q) ! (nth Zero s k) [=]
  (\big[(cpoly_plus_cs K)/(cpoly_zero K)]_(j <- (mkseq (fun x => x) (k - c)) | (fun x => true) j)
    (_C_ (alpha K f s Q j) [*] (eta K s j)))
  ! (nth Zero s k) [+] 
  (dd K f ((nth Zero s k) :: 
    (rev (take (k - c) s))) R) [*] 
  (eta K s (k - c)) ! (nth Zero s k).
Proof.
  intros.
  induction c.
  assert (k - 0 = k) by omega.
  assert (mkseq ssrfun.id (k - 0) =
    mkseq ssrfun.id k).
  rewrite H2; reflexivity.
  rewrite H3.
  clear H2 H3.
  assert (fresh_seq K (rev (take k s))).
  apply rev_fresh_seq.
  apply take_fresh_seq.
  exact Q.
  assert (dd K f (nth Zero s k ::
    rev (take (k - 0) s)) R [=]
    alpha K f s Q k).
  unfold alpha.
  apply dd_indep.
  rewrite <- cat1s.
  assert (rev [:: nth Zero s k] = [:: nth Zero s k]).
  auto.
  rewrite <- H3.
  rewrite <- rev_cat.
  assert (take (k - 0) s ++ [:: nth Zero s k] =
    take (k + 1) s).
  rewrite cats1.
  assert (k - 0 = k) by omega.
  rewrite H4.
  rewrite <- take_nth.
  assert (S k = k + 1) by omega.
  rewrite H5.
  reflexivity.
  apply (ssrbool.introT (P := S k <= size s)).
  apply ssrnat.leP.
  auto.
  rewrite H4.
  reflexivity.
  rewrite H3.
  rewrite <- c_mult_apply.
  rewrite <- plus_apply.
  assert (k - 0 = k) by omega.
  rewrite H4.
  rewrite <- (@big_seq1 (cpoly K) (cpoly_eq K)
    eqv_cpoly (cpoly_plus_cs K) (cpoly_zero K)
    right_unit_cpoly nat k  
    (fun x => cr_mult (_C_ (alpha K f s Q x)) (eta K s x))).
  rewrite <- (@big_cat (cpoly K) (cpoly_eq K)
    (eqv_cpoly) (cpoly_plus_cs K) (cpoly_zero K)
    morph_cpoly assoc_cpoly left_unit_cpoly nat
    (mkseq ssrfun.id k) ([:: k])
    (fun x => true) (fun x => cr_mult (_C_ (alpha K f s Q x)) (eta K s x))
    ).
  simpl.
  assert (mkseq ssrfun.id k ++ [:: k] =
    mkseq ssrfun.id (k + 1)).
  unfold mkseq.
  assert ([:: k] = map ssrfun.id [:: k]).
  auto.
  rewrite H5.
  rewrite <- map_cat.
  assert ([:: k] = iota k 1).
  auto.
  rewrite H6.
  rewrite <- iota_add.
  auto.  
  rewrite H5.
  reflexivity. 
  assert (fresh_seq K (nth Zero s k ::
    rev (take (k - c) s))).
  apply fresh_cons.
  unfold sqfresh.
  apply insq.
  apply rev_fresh.
  apply nth_fresh.
  exact H1.
  exact Q.
  apply rev_fresh_seq.
  apply take_fresh_seq.
  exact Q.
  rewrite (IHc H2).
  assert (mkseq ssrfun.id (k - c) =
    mkseq ssrfun.id (k - S c) ++
    [:: (k - S c)]).
  unfold mkseq.
  assert ([:: k - S c] =
    map ssrfun.id (iota (k - S c) 1))
    by auto.
  rewrite H3.
  rewrite <- map_cat.
  assert (iota (k - S c) 1 = 
    iota (0 + (k - S c)) 1) by auto.
  rewrite H4.
  rewrite <- iota_add.
  assert (ssrnat.addn (k - S c) 1 = k - c).
  rewrite ssrnat.addn1.
  omega.
  rewrite H5; reflexivity.
  rewrite H3.
  rewrite (@big_cat (cpoly K) (cpoly_eq K)
    eqv_cpoly (cpoly_plus_cs K) (cpoly_zero K)
    morph_cpoly assoc_cpoly left_unit_cpoly nat
    (mkseq ssrfun.id (k - S c)) [:: k - S c]
    ).
  rewrite plus_apply.
  set (CSemiGroups.plus_assoc K).
  unfold associative in a.
  rewrite <- a.
  rewrite (@big_seq1 (cpoly K) (cpoly_eq K)
    eqv_cpoly (cpoly_plus_cs K) (cpoly_zero K)
    right_unit_cpoly nat (k - S c)).
  assert (fresh_seq K (rev (take (k - c) s))).
  apply rev_fresh_seq.
  apply take_fresh_seq.
  exact Q.
  assert ((nth Zero s k) [-] (nth Zero s (k - S c)) [#]
    Zero).
  apply ap_fresh_nth.
  omega.
  omega.
  exact H1.
  exact Q.
  assert ((dd K f (nth Zero s k :: 
    rev (take (k - c) s)) H2) [=]
    (((dd K f (nth Zero s k :: 
      rev (take (k - S c) s)) R) [-] 
    (dd K f (rev (take (k - c) s)) H4)) [/]
    ((nth Zero s k) [-] (nth Zero s (k - S c))) [//]
    X)).
  apply dd_reduce_nth.
  exact H.
  omega.
  exact H1.
  exact Q.
  rewrite H5.
  unfold eta at 3.
  assert (\big[cpoly_mult_cs K/cpoly_one K]_(x_i <- take (k - c) s)
    (cpoly_linear K (cg_inv x_i) (cpoly_one K)) [=]
    \big[cpoly_mult_cs K/cpoly_one K]_(x_i <- (take (k - S c) s) ++ [:: nth Zero s (k - S c)])
      (cpoly_linear K (cg_inv x_i) (cpoly_one K))).    
  assert (take (k - c) s = take (k - S c) s ++
    [:: nth Zero s (k - S c)]).
  rewrite <- cat_rcons.
  rewrite <- take_nth.
  assert (k - c = S (k - S c)) by omega.
  rewrite H6.
  rewrite cats0; reflexivity.
  apply (ssrbool.introT (P := S (k - S c) <= size s)).
  apply ssrnat.leP.
  omega.
  rewrite H6.
  reflexivity.
  rewrite H6.
  rewrite (@big_cat (cpoly K) (cpoly_eq K)
    eqv_cpoly (cpoly_mult_cs K) (cpoly_one K)
    morph_cpoly_mult assoc_cpoly_mult
    left_unit_cpoly_mult K (take (k - S c) s)
    [:: nth Zero s (k - S c)]). 
  rewrite (@big_seq1 (cpoly K) (cpoly_eq K)
    eqv_cpoly (cpoly_mult_cs K) (cpoly_one K)
    right_unit_cpoly_mult K (nth Zero s (k - S c))).
  rewrite (mult_apply K _ 
    (cpoly_linear K (cg_inv (nth Zero s (k - S c))) 
    (cpoly_one K))).
  assert (cpoly_apply_fun (cpoly_linear K
    (cg_inv (nth Zero s (k - S c))) (cpoly_one K))
    (nth Zero s k) [=] nth Zero s k [-]
    nth Zero s (k - S c)).
  simpl.
  rewrite cring_mult_zero.
  rewrite cm_rht_unit_unfolded.
  rewrite mult_one.
  rewrite cg_minus_unfolded.
  algebra.
  rewrite H7.
  rewrite (mult_commutes K _ 
    (nth Zero s k [-] nth Zero s (k - S c))).
  rewrite mult_assoc.
  rewrite div_1.
  rewrite (mult_commutes K (_ [-] _) _).
  rewrite ring_dist_minus.
  unfold alpha at 2.
  assert (dd K f (rev (take (k - S c + 1) s))
    (rev_fresh_seq K (take (k - S c + 1) s)
      (take_fresh_seq K (k - S c + 1) s Q)) [=]
    dd K f (rev (take (k - c) s)) H4).
  apply dd_indep.
  assert (k - S c + 1 = k - c) by omega.
  rewrite H8.
  reflexivity.
  rewrite H8.
  rewrite cg_minus_unfolded.
  rewrite (cag_commutes K _ (cg_inv _)).
  rewrite (a _ (cg_inv _)).
  unfold eta at 2.
  rewrite c_mult_apply.
  rewrite (mult_commutes K _ (dd _ _ _ H4)).
  rewrite cg_rht_inv_unfolded.
  rewrite cm_lft_unit_unfolded.
  rewrite (mult_commutes K (dd _ _ _ _) _).
  unfold eta at 3.
  reflexivity.
  omega.
Qed.

(**
 * This lemma corresponds with lemma 13 in the paper as 
 * sent to me on january 11th. It is called 'lem11' here
 * because it was based on a previous version of the paper.
 * It relies on lemmas 11a and 11b (see before). 
 *)
Lemma lem11 : forall (k i : nat) (s : seq K) (P : i <= k) 
  (Q : fresh_seq K s), k < size s ->
  f (nth Zero s i) [=] (N K f s k Q) ! (nth Zero s i).
Proof.
  intros.
  induction k.
  inversion P.
  destruct s.
  inversion H.
  simpl.
  unfold alpha.
  assert (fresh_seq K [:: s]).
  apply fresh_cons.
  unfold sqfresh.
  apply insq.
  simpl; auto.
  apply fresh_nil.
  assert (dd K f (rev (take (0 + 1) (s :: s0)))
    (rev_fresh_seq K (take (0 + 1) (s :: s0))
      (take_fresh_seq K (0 + 1) (s :: s0) Q)) [=] 
    dd K f [:: s] H1).
  apply dd_indep.
  simpl.
  rewrite take0.
  reflexivity.  
  rewrite H2.
  assert (f s [=] dd K f [:: s] H1).
  algebra.
  rewrite <- H3.
  rewrite cring_mult_zero.
  rewrite cm_rht_unit_unfolded.
  rewrite cm_rht_unit_unfolded.
  algebra.
  inversion P.
  assert (fresh_seq K (nth Zero s (S k) :: 
    rev (take (S k - S k) s))).
  assert (S k - S k = 0) by omega.
  rewrite H1.
  rewrite take0.
  apply fresh_cons.
  unfold sqfresh.
  apply insq.
  simpl; auto.
  apply rev_fresh_seq.
  apply fresh_nil.
  rewrite (lem11b (S k) (S k) _ _ H1).
  assert (mkseq ssrfun.id (S k - S k) =
    Nil nat).
  assert (S k - S k = 0) by omega.
  rewrite H2.
  auto.
  rewrite H2.
  rewrite big_nil.
  assert (fresh_seq K [:: nth Zero s (S k)]).
  apply fresh_cons.
  unfold sqfresh.
  apply insq.
  simpl; auto.
  apply fresh_nil.
  setoid_replace (dd K f (nth Zero s (S k) ::
    (rev (take (S k - S k) s))) H1) with
    (dd K f [:: nth Zero s (S k)] H3).
  assert (cpoly_apply_fun (cpoly_zero K) 
    (nth Zero s (S k)) [=] Zero).
  algebra.
  rewrite H4.
  rewrite cm_lft_unit_unfolded.
  unfold eta.
  assert (take (S k - S k) s = Nil K).
  assert (S k - S k = 0) by omega.
  rewrite H5.
  rewrite take0; reflexivity.
  rewrite H5.
  rewrite apply_bigops.
  rewrite big_nil.
  rewrite mult_one.
  algebra.
  apply dd_indep.
  assert (S k - S k = 0) by omega.
  rewrite H4.
  rewrite take0.
  auto.
  omega.
  auto.
  omega.
  unfold N.
  rewrite (@eq_big_idx_seq (cpoly K) (cpoly_eq K)
    eqv_cpoly (cpoly_plus_cs K) (cpoly_zero K)
    morph_cpoly 
    right_unit_cpoly (cpoly_zero K) nat
    (mkseq ssrfun.id (S k + 1)) (fun x : nat => true)
    (fun x : nat => cr_mult (_C_ (alpha K f s Q x)) (eta K s x))
    right_unit_cpoly).
  assert (mkseq ssrfun.id (S (k + 1)) = 
    (mkseq ssrfun.id (S k)) ++ [:: S k]).
  unfold mkseq.
  replace (S (S k)) with (S k + 1).
  rewrite (iota_add 0 (S k) 1).
  rewrite map_cat; auto.
  omega.
  rewrite H2.
  clear H2.
  rewrite (@big_cat (cpoly K) (cpoly_eq K) eqv_cpoly
    (cpoly_plus_cs K) (cpoly_zero K) morph_cpoly assoc_cpoly
    left_unit_cpoly nat 
    (mkseq ssrfun.id (S k)) ([:: S k]) (fun x : nat => true)
    (fun x : nat => _C_ (alpha K f s Q x) [*] (eta K s x))).
  unfold N in IHk.
  rewrite (@big_seq1 (cpoly K) (cpoly_eq K) eqv_cpoly
    (cpoly_plus_cs K) (cpoly_zero K) right_unit_cpoly nat (S k)
    (fun x : nat => _C_ (alpha K f s Q x) [*] (eta K s x))).
  rewrite (@plus_apply K
    ((\big[cpoly_plus_cs K/cpoly_zero K]_(i0 <- mkseq ssrfun.id (S k))
         (_C_ (alpha K f s Q i0) [*] (eta K s i0))))
    (_C_ (alpha K f s Q (S k)) [*] (eta K s (S k)))
    (nth Zero s i)).
  assert ((_C_ (alpha K f s Q (S k)) [*] (eta K s (S k))) !
    (nth Zero s i) [=] Zero).
  rewrite c_mult_apply.
  unfold eta.
  rewrite (@apply_bigops (take (S k) s)).
  rewrite lem11a.
  rewrite cring_mult_zero.
  reflexivity.
  omega.
  omega.
  exact H1.
  rewrite H2.
  rewrite IHk.
  assert (S k = k + 1) by omega.
  rewrite H3.
  rewrite cm_rht_unit_unfolded.
  reflexivity.
  exact H1.
  omega.
  auto.
Qed.

(**
 * Getting the nth coefficient of a polynomial can be done
 * outside a bigop, as well as inside, resulting in the 
 * same value (with the bigop applied in the latter case,
 * of course).
 *
 * TODO: Generalise to arbitrary bigop.
 * TODO: Replace bigopsClass construct with corresponding
 * folds.
 *)
Lemma nth_coeff_bigops : forall (k : nat) (r : seq nat) F,
  nth_coeff k (\big[cpoly_plus_cs K/cpoly_zero K]_(i <- r) F i) [=]
  \big[csg_op/(Zero:K)]_(i <- r) (nth_coeff k (F i)).
Proof.
  intros. 
  induction r.
  rewrite big_nil.
  simpl; reflexivity.
  rewrite big_cons.
  rewrite nth_coeff_plus.
  rewrite IHr.
  rewrite big_cons.
  reflexivity.
Qed.  

(**
 * A small lemma to ascertain compatibility between two
 * types of multiplication between polynomials and constant
 * values. 
 *)
Lemma cpoly_mult_cr_c_ : forall p c,
  (cpoly_mult_cr K p c [=] p [*] _C_ c).
Proof.
  intros.
  simpl.
  induction p.
  simpl; auto.
  simpl.
  split.
  rewrite cm_rht_unit_unfolded.
  rewrite mult_commutes.
  reflexivity.
  rewrite IHp.
  reflexivity.
Qed.

(**
 * This corrolary corresponds to corrolary 14 in the PDF as
 * e-mailed to me on january 11th. It states that the divided
 * difference f[a_1, ..., a_n] is the coefficient of x^n in
 * the (Newton) polynomial that interpolates f at a_1, ..., a_n.
 *
 * TODO: Fix usage of bigopsClass constructs.
 * TODO: Shorten proof.
 *)
Lemma cor12 : forall (k : nat) (s : seq K) 
  (Q : fresh_seq K s), k < size s -> 
  nth_coeff k (N K f s k Q) [=] alpha K f s Q k.
Proof.
  intros.
  unfold N.
  cut (mkseq ssrfun.id (k + 1) =
    mkseq ssrfun.id k ++ [:: k]).
  intro.
  rewrite H0.
  rewrite (@big_cat (cpoly K) (cpoly_eq K)
    eqv_cpoly (cpoly_plus_cs K) (cpoly_zero K) 
    morph_cpoly assoc_cpoly left_unit_cpoly).
  rewrite (@big_seq1 (cpoly K) (cpoly_eq K)
    eqv_cpoly (cpoly_plus_cs K) (cpoly_zero K)
    right_unit_cpoly).
  rewrite nth_coeff_plus.
  rewrite nth_coeff_c_mult_p.
  assert (nth_coeff k (eta K s k) [=] One).
  unfold eta.
  clear H0.
  induction k.
  rewrite take0.
  simpl; reflexivity.
  cut (take (S k) s = take k s ++ 
    [:: nth Zero s k]).
  intro.
  rewrite H0.
  rewrite (@big_cat (cpoly K) (cpoly_eq K)
    eqv_cpoly (cpoly_mult_cs K) (cpoly_one K) 
    morph_cpoly_mult assoc_cpoly_mult left_unit_cpoly_mult).
  rewrite (@big_seq1 (cpoly K) (cpoly_eq K)
    eqv_cpoly (cpoly_mult_cs K) (cpoly_one K)
    right_unit_cpoly_mult).
  rewrite cpoly_mult_lin.
  rewrite nth_coeff_plus.
  rewrite coeff_Sm_lin.
  rewrite cpoly_mult_one.
  rewrite IHk.
  unfold cpoly_mult_cr_cs.
  rewrite cpoly_mult_cr_c_.
  rewrite nth_coeff_p_mult_c_.
  assert (degree_le k
    (\big[cpoly_mult_cs K/cpoly_one K]_(i <- take k s)
      cpoly_linear K (cg_inv i) (cpoly_one K))).
  clear IHk H0.
  induction k.
  rewrite take0.
  unfold degree_le.
  intros.
  rewrite big_nil.
  destruct m.
  inversion H0.
  simpl; reflexivity.
  cut (take (S k) s = take k s ++
    [:: nth Zero s k]).
  intro.
  rewrite H0.
  unfold degree_le.
  intros.
  rewrite (@big_cat (cpoly K) (cpoly_eq K)
    eqv_cpoly (cpoly_mult_cs K) (cpoly_one K) 
    morph_cpoly_mult assoc_cpoly_mult left_unit_cpoly_mult).
  set degree_mult_aux.
  simpl in s0.
  destruct m.
  inversion H1.
  replace (S m) with (m + 1) by omega.
  rewrite <- cpoly_mult_fast_equiv.
  rewrite s0.
  simpl.
  rewrite mult_one.
  rewrite cm_rht_unit_unfolded.
  rewrite mult_one.
  unfold degree_le in IHk.
  rewrite IHk.
  reflexivity.
  omega.
  omega.
  unfold degree_le in IHk.
  unfold degree_le.
  intros.
  rewrite IHk.
  reflexivity.
  omega.
  omega.
  unfold degree_le.
  intros.
  destruct m0.
  inversion H2.
  destruct m0.
  inversion H2.
  inversion H4.
  simpl.
  reflexivity.
  rewrite cats1.
  rewrite <- take_nth.
  reflexivity.
  apply (ssrbool.introT (P := S k <= size s)).
  apply ssrnat.leP.
  omega.
  unfold degree_le in H1.
  rewrite H1.
  rewrite mult_commutes.
  rewrite cring_mult_zero.
  algebra.
  omega.
  omega.
  rewrite cats1.
  rewrite <- take_nth.
  reflexivity.
  apply (ssrbool.introT (P := S k <= size s)).
  apply ssrnat.leP.
  omega.
  rewrite H1.
  rewrite mult_one.
  assert (degree_le (k - 1)
     (\big[cpoly_plus_cs K/cpoly_zero K]_(i <- mkseq ssrfun.id k)
         cr_mult (_C_ (alpha K f s Q i)) (eta K s i))).
  unfold degree_le.
  clear H0 H1.
  induction k.
  simpl.
  intros.
  reflexivity.
  intros.
  cut (mkseq ssrfun.id (S k) = 
    mkseq ssrfun.id k ++ [:: k]).
  intro.
  rewrite H1.  
  rewrite (@big_cat (cpoly K) (cpoly_eq K)
    eqv_cpoly (cpoly_plus_cs K) (cpoly_zero K) 
    morph_cpoly assoc_cpoly left_unit_cpoly).
  rewrite (@big_seq1 (cpoly K) (cpoly_eq K)
    eqv_cpoly (cpoly_plus_cs K) (cpoly_zero K)
    right_unit_cpoly).
  rewrite nth_coeff_plus.
  unfold degree_le in IHk.
  rewrite IHk.
  rewrite cm_lft_unit_unfolded.
  rewrite nth_coeff_c_mult_p.
  clear IHk.
  assert (degree_le k (eta K s k)).
  unfold degree_le.
  induction k.
  unfold degree_le, eta.
  intros.
  rewrite take0.
  destruct m0.
  assert (1 < 0) by omega.
  inversion H2.
  simpl; reflexivity.
  unfold degree_le, eta.
  intros.
  cut (take (S k) s = take k s ++
    [:: nth Zero s k]).
  intro.
  rewrite H3.
  rewrite (@big_cat (cpoly K) (cpoly_eq K)
    eqv_cpoly (cpoly_mult_cs K) (cpoly_one K) 
    morph_cpoly_mult assoc_cpoly_mult left_unit_cpoly_mult).
  set degree_mult_aux.
  simpl in s0.
  rewrite <- cpoly_mult_fast_equiv.
  destruct m0.
  inversion H2.
  replace (S m0) with (m0 + 1) by omega.
  rewrite s0.
  unfold degree_le in IHk.
  rewrite IHk.
  rewrite mult_commutes.
  rewrite cring_mult_zero.
  reflexivity.
  omega.
  omega.
  unfold mkseq.
  assert ([:: k] = map ssrfun.id (iota k 1)).
  simpl; reflexivity.
  rewrite H4.
  rewrite <- map_cat.
  rewrite <- iota_add.
  rewrite ssrnat.addn1.
  reflexivity.
  omega.
  unfold degree_le.
  intros.
  rewrite IHk.
  reflexivity.
  omega.
  omega.
  unfold mkseq.
  assert ([:: k] = map ssrfun.id (iota k 1)).
  simpl; reflexivity.
  rewrite H5.
  rewrite <- map_cat.
  rewrite <- iota_add.
  rewrite ssrnat.addn1.
  reflexivity.
  omega.
  unfold degree_le.
  intros.
  simpl.
  destruct m1.
  inversion H4.
  destruct m1.
  inversion H4.
  inversion H6.
  reflexivity.
  rewrite cats1.
  rewrite <- take_nth.
  reflexivity.
  apply (ssrbool.introT (P := S k <= size s)).
  apply ssrnat.leP.
  omega.
  unfold degree_le in H2.
  rewrite H2.
  rewrite cring_mult_zero.
  reflexivity.
  omega.
  omega.
  omega.
  unfold mkseq.
  assert ([:: k] = map ssrfun.id (iota k 1)).
  simpl; reflexivity.
  rewrite H1.
  rewrite <- map_cat.
  rewrite <- iota_add.
  rewrite ssrnat.addn1.
  reflexivity.
  destruct k.
  simpl.
  rewrite cm_lft_unit_unfolded.
  reflexivity.
  unfold degree_le in H2.
  rewrite H2.
  rewrite cm_lft_unit_unfolded.
  reflexivity.
  omega.
  unfold mkseq.
  assert ([:: k] = map ssrfun.id (iota k 1)).
  simpl; reflexivity.
  rewrite H0.
  rewrite <- map_cat.
  rewrite <- iota_add.
  rewrite ssrnat.addn1.
  replace (S k) with (k + 1) by omega.
  reflexivity.
Qed.

End BigopsTheory.

(**
 * Since we don't have decidable equality for elements
 * in a Field K, we have to define our own permutation
 * for sequences. 
 *)

Section Permutations.

Variable A : CSetoid.

(**
 * Alternative definition for permutations. This one
 * matches the definition of dd a bit better.
 *)
Inductive permutation : seq A -> seq A -> Prop :=
  | permutation_nil : permutation nil nil
  | permutation_singleton : 
      forall (a : A), permutation [:: a] [:: a]
  | permutation_skip :
      forall (a b : A) (s1 s2 : seq A),
      permutation s1 s2 ->
      permutation (a :: s1) (a :: s2) -> 
      permutation (b :: s1) (b :: s2) ->
      permutation (a :: b :: s1) (a :: b :: s2)
  | permutation_swap :
      forall (a b : A) (s : seq A), 
      permutation (a :: b :: s) (b :: a :: s)
  | permutation_trans :
      forall s1 s2 s3 : seq A,
      permutation s1 s2 -> permutation s2 s3 -> 
      permutation s1 s3.

Hint Constructors permutation.

(**
 * A type of induction on sequences that suits the 
 * definition of divided differences a bit better. 
 *
 * TODO: Fix this proof, which should not be too hard. 
 * A solution might be to distinguish between sequences
 * of even and odd length.
 *)
Lemma dd_type_ind : forall P, P [::] ->
  (forall (a : A), P [:: a]) ->
  (forall (a b : A) (s : seq A), 
    P s -> P (a :: s) ->
    P (b :: s) -> P (a :: b :: s)) ->
  (forall (s : seq A), P s).
Proof.
  intros.
  Admitted.

(**
 * Permutations are reflexive.
 *)
Lemma permutation_refl : forall s : seq A, 
  permutation s s.
Proof.
  intros.
  induction s using dd_type_ind.
  apply permutation_nil.
  apply permutation_singleton.
  apply permutation_skip.
  exact IHs.
  exact IHs0.
  exact IHs1.
Qed.

Hint Resolve permutation_refl.

(**
 * Permutations are symmetric.
 *)
Lemma permutation_sym :
 forall l m : seq A, permutation l m -> 
 permutation m l.
Proof.
intros l1 l2 H'; elim H'.
apply permutation_nil.
intro a.
apply permutation_singleton.
intros.
apply permutation_skip.
exact H0.
exact H2.
exact H4.
intros.
apply permutation_swap.
intros l1' l2' l3' H1 H2 H3 H4.
apply permutation_trans with (1 := H4) (2 := H2).
Qed.

(**
 * The length of a sequence does not change under
 * permutation.
 *)
Lemma permutation_size :
 forall l m : seq A, permutation l m -> 
 size l = size m.
Proof.
intros l m H'; elim H'; simpl in |- *; auto.
intros l1 l2 l3 H'0 H'1 H'2 H'3.
rewrite <- H'3; auto.
Qed.

(**
 * The permutation nil originates from nil.
 *)
Lemma permutation_nil_inv : forall l : seq A, 
  permutation l nil -> l = nil.
Proof.
intros l H; 
generalize (permutation_size _ _ H); case l; 
simpl in |- *; auto.
intros; discriminate.
Qed.

(**
 * Permutation on sequences of length 1 is an identity
 * operation.
 *)
Lemma permutation_one_inv_aux :
  forall l1 l2 : seq A,
  permutation l1 l2 -> 
  forall a : A, l1 = a :: nil -> l2 = a :: nil.
Proof.
intros l1 l2 H; elim H; clear H l1 l2; auto.
intros.
inversion H5.
intros.
inversion H.
Qed.

(**
 * TODO: Do we really require this lemma?
 *)
Lemma permutation_one_inv :
 forall (a : A) (l : seq A), 
 permutation (a :: nil) l -> l = a :: nil.
intros a l H; 
apply permutation_one_inv_aux with (l1 := a :: nil); 
auto.
Qed.

End Permutations.

Section PermProperties.

Variable K : CField.
Variable f : K -> K.

(**
 * The property of freshness is preserved under permutation.
 *)
Lemma perm_fresh : forall (s1 s2 : seq K),
  fresh_seq K s1 -> permutation K s1 s2 ->
  fresh_seq K s2.
Proof.
  intros.
  induction H0.
  apply fresh_nil.
  apply fresh_cons.
  unfold sqfresh; simpl.
  apply insq; auto.
  apply fresh_nil.
  apply fresh_cons.
  assert (fresh_seq K (a :: s2)).
  apply IHpermutation2.
  apply fresh_cons.
  inversion H.
  inversion H2.
  inversion X.
  unfold sqfresh.
  apply insq.
  exact X1.
  inversion H.
  inversion H3.
  exact H7.
  inversion H.
  inversion H3.
  inversion X.
  unfold sqfresh.
  apply insq.
  simpl.
  split.
  exact X0.
  apply unsq.
  inversion H0.
  unfold sqfresh in H7.
  exact H7.
  apply IHpermutation3.
  inversion H.
  exact H3.
  apply fresh_cons.
  inversion H.
  inversion H2.
  inversion X.
  unfold sqfresh.
  apply insq.
  simpl. 
  split.
  apply ap_symmetric.
  exact X0.
  apply unsq.
  inversion H3.
  unfold sqfresh in H6.
  exact H6.
  apply fresh_cons.
  inversion H.
  inversion H2.
  inversion X.
  unfold sqfresh.
  apply insq.
  exact X1.
  inversion H.
  inversion H3.
  exact H7.
  apply IHpermutation2.
  apply IHpermutation1.
  exact H.
Qed.
 
(** 
 * Lemma 14 - The result of dd is invariant under 
 * permutation of its sequence of arguments.
 * 
 * In the paper as sent to me on january 11th, this is
 * referred to as lemma 16.
 * 
 * TODO: Shorten proof.
 *)
Lemma lem14 : forall (s1 s2 : seq K)
  (P1 : fresh_seq K s1) (P2 : fresh_seq K s2),
  (permutation K s1 s2) -> dd K f s1 P1 [=] dd K f s2 P2.
Proof.
  intros s1 s2 P1 P2 perm.
  induction perm.
  algebra.
  algebra.
  assert (fresh_seq K (a :: s1)).
  apply fresh_cons.
  inversion P1.
  inversion H1.
  inversion X.
  unfold sqfresh.
  apply insq.
  exact X1.
  inversion P1.
  inversion H2.
  exact H6.
  assert (fresh_seq K (b :: s1)).
  inversion P1.
  exact H3.
  inversion P1.
  inversion H3.
  inversion X.
  assert (a [-] b [#] Zero).
  apply minus_ap_zero.
  apply ap_symmetric.
  exact X0.
  rewrite (dd_reduce K f s1 a b P1 H H0 X2).
  assert (fresh_seq K (a :: s2)).
  apply fresh_cons.
  inversion P2.
  inversion H7.
  inversion X3.
  apply insq.
  exact X5.
  inversion P2.
  inversion H8.
  exact H12.
  assert (fresh_seq K (b :: s2)).
  inversion P2.
  exact H9.
  rewrite (dd_reduce K f s2 a b P2 H5 H6 X2).
  apply div_wd.
  rewrite (IHperm2 H H5).
  rewrite (IHperm3 H0 H6).
  reflexivity.
  reflexivity.
  assert (fresh_seq K (a :: s)).
  inversion P2.
  exact H2.
  assert (fresh_seq K (b :: s)).
  inversion P1.
  exact H3.
  inversion P1.
  inversion H3.
  inversion X.
  assert (a [-] b [#] Zero).
  apply minus_ap_zero.
  apply ap_symmetric.
  exact X0.
  rewrite (dd_reduce K f s a b P1 H H0 X2).
  assert (b [-] a [#] Zero).
  apply minus_ap_zero.
  exact X0.
  rewrite (dd_reduce K f s b a P2 H0 H X3).
  apply eq_div.
  rewrite ring_dist_minus.
  rewrite ring_dist_minus.
  rewrite dist_2b.
  rewrite dist_2b.
  rewrite dist_2b.
  rewrite dist_2b.
  set (cr_mult (dd K f (a :: s) H) b).
  set (cr_mult (dd K f (b :: s) H0) b).
  set (cr_mult (dd K f (a :: s) H) a).
  set (cr_mult (dd K f (b :: s) H0) a).
  rewrite assoc_1.
  rewrite assoc_1.
  rewrite <- minus_plus.
  rewrite <- minus_plus.
  rewrite (cag_commutes_unfolded K s3 s2).
  rewrite (cag_commutes_unfolded K _ s1).
  rewrite assoc_2.
  rewrite (cag_commutes_unfolded K _ s4).
  rewrite assoc_2.
  rewrite cg_minus_unfolded.
  rewrite cg_minus_unfolded.
  rewrite (cag_commutes_unfolded K s1 s4).
  reflexivity.
  assert (fresh_seq K s2).
  apply (perm_fresh s1).
  exact P1.
  exact perm1.
  rewrite (IHperm1 P1 H).
  rewrite (IHperm2 H P2).
  reflexivity.
Qed.

End PermProperties.

(**
 * This is the end of the section about permutations. As I
 * indicated before in our conversations, from this point on
 * I have much concern about the proper heading of this 
 * research. For instance, many lemmas below are only 
 * required to get NAH-material to work (while it is still
 * a bit uncertain if we require this at all). Another 
 * important mistake (in my opinion) is the usage of two
 * different definitions of continuity, differentiability
 * etc. 
 *
 * I therefore propose the following: 
 *
 * - Keep the file from line 0 up until here intact 
 *   (but fix the proofs, of course). 
 * - Start over again to work on multi-variable integration
 *   as a separate branch (but only what is really required
 *   for this project). 
 * - Bridge the gap between these two, and complete the
 *   proof.
 *)

Section Derivations.

(**
 * Lemma 15 - If a < b then C[a,b] is an algebra over
 * the ring R. 
 *)
Require Import Structures.

Variable a b : IR.
Hypothesis Hab : a [<] b.

(**
 * These are the partial functions on IR such that for
 * each n, they are n-times differentiable.
 *)
Record C_inf_ab := {
  f_crr : PartFunct IR ;
  f_pdf : forall n, Diffble_I_n Hab n f_crr}.

(**
 * These are type class instances and not further explained.
 *)
Instance IR_plus : RingPlus IR := csg_op.

Instance IR_mult : RingMult IR := cr_mult.

Instance IR_inv : GroupInv IR := cg_inv.

Instance IR_zero : RingZero IR := Zero.

Instance IR_one : RingOne IR := One.

Instance IR_equiv : Equiv IR := (@st_eq IR).

Instance IR_equivalence : Equivalence (@st_eq IR).

(**
 * Addition is associative for IR
 *)
Instance IR_associative : @Associative IR (@st_eq IR) IR_plus.
unfold Associative.
intros.
unfold IR_plus.
unfold equiv.
algebra.
Qed.

(**
 * Addition is a morphism with respect to the standard
 * equality on IR.
 *)
Instance IR_proper : Proper ((@st_eq IR) ==> (@st_eq IR) ==>
  (@st_eq IR)) IR_plus.
unfold Proper.
unfold respectful.
intros.
rewrite H.
rewrite H0.
reflexivity.
Qed.

(**
 * These two facts allow us to state IR as a semigroup for
 * addition.
 *)
Instance IR_semigroup : @SemiGroup IR (@st_eq IR) IR_plus.

(**
 * IR is a monoid for addition over IR.
 *)
Instance IR_monoid : @Monoid IR (@st_eq IR) IR_plus Zero.
assert (forall x : IR, Zero [+] x == x).
intros.
rewrite cm_lft_unit_unfolded.
reflexivity.
assert (forall x : IR, x [+] Zero == x).
intros.
rewrite cm_rht_unit_unfolded.
reflexivity.
apply (Build_Monoid IR (@st_eq IR) IR_plus Zero
  IR_semigroup H H0).
Qed.

(**
 * Type instance stating that inversion for IR is a
 * morphism with respect to the standard equality on IR.
 *)
Instance IR_proper_inv : Proper ((@st_eq IR) ==> 
  (@st_eq IR)) IR_inv.
unfold Proper.
unfold respectful.
intros.
rewrite H.
reflexivity.
Qed.

(**
 * This makes IR a group with addition, inversion and zero.
 *)
Instance IR_group : @Group IR (@st_eq IR) IR_plus
  Zero IR_inv.
assert (forall x : IR, IR_plus (IR_inv x) x == Zero).
intros.
unfold IR_plus, IR_inv.
assert (csg_op (cg_inv x) x [=] Zero).
algebra.
rewrite H.
reflexivity.
assert (forall x : IR, IR_plus x (IR_inv x) == Zero).
intros.
unfold IR_plus, IR_inv.
assert (csg_op x (cg_inv x) [=] Zero).
algebra.
rewrite H0.
reflexivity.
apply (Build_Group IR (@st_eq IR) IR_plus Zero IR_inv
  IR_monoid IR_proper_inv H H0).
Qed.

(**
 * IR is also an Abelian group because of the commutativity
 * of addition.
 *)
Instance IR_abgroup : @AbGroup IR (@st_eq IR) IR_plus
  Zero IR_inv.
assert (Commutative IR_plus).
unfold Commutative.
intros.
assert (IR_plus x y [=] IR_plus y x).
unfold IR_plus.
algebra.
rewrite H.
reflexivity.
apply (Build_AbGroup IR (@st_eq IR) IR_plus Zero 
  IR_inv IR_group H).
Qed.

(**
 * Multiplication on IR is clearly associative.
 *)
Instance IR_associative_mult : @Associative IR (@st_eq IR) IR_mult.
unfold Associative.
intros.
unfold IR_mult.
unfold equiv.
algebra.
Qed.

(**
 * Multiplication on IR is a morphism with respect to the
 * standard equality on IR.
 *)
Instance IR_proper_mult : Proper ((@st_eq IR) ==> (@st_eq IR) ==>
  (@st_eq IR)) IR_mult.
unfold Proper.
unfold respectful.
intros.
rewrite H.
rewrite H0.
reflexivity.
Qed.

(**
 * This makes IR a semigroup with respect to multiplication.
 *)
Instance IR_semigroup_mult : @SemiGroup IR (@st_eq IR) IR_mult.

(**
 * We may now conclude that IR is a monoid with one as the
 * neutral element in multiplication.
 *)
Instance IR_monoid_mult : @Monoid IR (@st_eq IR) IR_mult One.
assert (forall x : IR, One [*] x == x).
intros.
rewrite mult_commutes.
rewrite mult_one.
reflexivity.
assert (forall x : IR, x [*] One == x).
intros.
rewrite mult_one.
reflexivity.
apply (Build_Monoid IR (@st_eq IR) IR_mult One
  IR_semigroup_mult H H0).
Qed.

(**
 * The reals form a ring with addition and multiplication.
 *
 * TODO: All these lemmas (this one and the ones before) are
 * probably defined in the CoRN libraries as well and are 
 * therefore not required to be stated here (but I am not
 * sure if they are already present as type class instances).
 *)
Instance IR_ring : @Ring IR (@st_eq IR) IR_plus
  IR_mult IR_inv Zero One.
assert (Commutative IR_mult).
unfold Commutative.
intros.
assert (IR_mult x y [=] IR_mult y x).
unfold IR_mult.
algebra.
rewrite H.
reflexivity.
assert (Distribute IR_mult IR_plus).
assert (forall a b c, IR_mult a (IR_plus b c) ==
  IR_plus (IR_mult a b) (IR_mult a c)).
intros.
unfold IR_mult, IR_plus.
assert (cr_mult a0 (csg_op b0 c) [=]
  csg_op (cr_mult a0 b0) (cr_mult a0 c)).
algebra.
rewrite H0.
reflexivity.
assert (forall a b c, IR_mult (IR_plus a b) c ==
  IR_plus (IR_mult a c) (IR_mult b c)).
intros.
unfold IR_mult, IR_plus.
assert (cr_mult (csg_op a0 b0) c [=]
  csg_op (cr_mult a0 c) (cr_mult b0 c)).
algebra.
rewrite H1.
reflexivity.
apply (Build_Distribute IR (@st_eq IR) IR_mult IR_plus
  H0 H1).
apply (Build_Ring IR (@st_eq IR) IR_plus IR_mult 
  IR_inv Zero One IR_abgroup IR_monoid_mult H H0).
Qed.

(**
 * If f' and g' are the nth derivatives of respectively
 * f and g, then f'+g' is the nth derivative of f+g.
 *
 * TODO: Is it possible to make these proofs a bit shorter?
 *)
Lemma Derivative_I_n_add : forall (n : nat)
  (f g f' g' : PartFunct IR) (Pfderiv : Derivative_I_n Hab n f f')
  (Pgderiv : Derivative_I_n Hab n g g'), 
  Derivative_I_n Hab n (f{+}g) (f'{+}g').
Proof.
  intro n.
  induction n.
  intros.
  apply Feq_plus.
  exact Pfderiv.
  exact Pgderiv.
  intros.
  simpl.
  elim Pfderiv.
  intros.
  elim Pgderiv.
  intros.
  exists (IPlus x x0).
  apply Derivative_I_wdr with (PartInt x{+}PartInt x0).
  apply part_int_plus.
  apply Feq_reflexive.
  apply derivative_imp_inc' with f.
  exact p.
  apply Feq_reflexive.
  apply derivative_imp_inc' with g.
  exact p0.
  apply Derivative_I_plus.
  exact p.
  exact p0.
  apply Derivative_I_n_wdl with (PartInt x{+}PartInt x0).
  apply part_int_plus.
  apply Feq_reflexive.
  apply derivative_imp_inc' with f.
  exact p.
  apply Feq_reflexive.
  apply derivative_imp_inc' with g.
  exact p0.
  apply IHn.
  exact q.
  exact q0.
Qed.

(**
 * Now that we have an exact representation of the nth
 * derivative under addition, we can more easily prove
 * n-times differentiability for the addition of functions.
 *)
Lemma Diffble_I_n_plus : forall (n : nat)
  (f g : PartFunct IR) (Pfdf : Diffble_I_n Hab n f)
  (Pgdf : Diffble_I_n Hab n g), 
  Diffble_I_n Hab n (Fplus f g).
Proof.
  intros.
  assert ({f0' : CSetoid_fun (subset (Compact (less_leEq _ _ _ Hab))) IR |
    Derivative_I_n Hab n f (PartInt f0')}).
  apply Diffble_I_n_imp_deriv_n.
  exact Pfdf.
  assert ({g' : CSetoid_fun (subset (Compact (less_leEq _ _ _ Hab))) IR |
    Derivative_I_n Hab n g (PartInt g')}).
  apply Diffble_I_n_imp_deriv_n.
  exact Pgdf.
  inversion_clear X.
  inversion_clear X0.
  apply deriv_n_imp_Diffble_I_n with (PartInt x{+}PartInt x0).
  apply Derivative_I_n_add.
  exact X1.
  exact X.
Qed.

(**
 * If f' and g' are the nth derivatives of respectively
 * f and g, then f'-g' is the nth derivative of f-g.
 *)
Lemma Derivative_I_n_minus : forall (n : nat)
  (f g f' g' : PartFunct IR) (Pfderiv : Derivative_I_n Hab n f f')
  (Pgderiv : Derivative_I_n Hab n g g'), 
  Derivative_I_n Hab n (f{-}g) (f'{-}g').
Proof.
  intro n.
  induction n.
  intros.
  apply Feq_minus.
  exact Pfderiv.
  exact Pgderiv.
  intros.
  simpl.
  elim Pfderiv.
  intros.
  elim Pgderiv.
  intros.
  exists (IMinus x x0).
  apply Derivative_I_wdr with (PartInt x{-}PartInt x0).
  apply part_int_minus.
  apply Feq_reflexive.
  apply derivative_imp_inc' with f.
  exact p.
  apply Feq_reflexive.
  apply derivative_imp_inc' with g.
  exact p0.
  apply Derivative_I_minus.
  exact p.
  exact p0.
  apply Derivative_I_n_wdl with (PartInt x{-}PartInt x0).
  apply part_int_minus.
  apply Feq_reflexive.
  apply derivative_imp_inc' with f.
  exact p.
  apply Feq_reflexive.
  apply derivative_imp_inc' with g.
  exact p0.
  apply IHn.
  exact q.
  exact q0.
Qed.

(**
 * The n-times differentiability of two functions f and g
 * continues to the n-times differentiability of f-g.
 *
 * TODO: Prove this lemma using only backward reasoning.
 *)
Lemma Diffble_I_n_minus : forall (n : nat)
  (f g : PartFunct IR) (Pfdf : Diffble_I_n Hab n f)
  (Pgdf : Diffble_I_n Hab n g), 
  Diffble_I_n Hab n (f{-}g).
Proof.
  intros.
  assert ({f0' : CSetoid_fun (subset (Compact (less_leEq _ _ _ Hab))) IR |
    Derivative_I_n Hab n f (PartInt f0')}).
  apply Diffble_I_n_imp_deriv_n.
  exact Pfdf.
  assert ({g' : CSetoid_fun (subset (Compact (less_leEq _ _ _ Hab))) IR |
    Derivative_I_n Hab n g (PartInt g')}).
  apply Diffble_I_n_imp_deriv_n.
  exact Pgdf.
  inversion_clear X.
  inversion_clear X0.
  apply deriv_n_imp_Diffble_I_n with (PartInt x{-}PartInt x0).
  apply Derivative_I_n_minus.
  exact X1.
  exact X.
Qed.

(**
 * Use addition of functions to create a semigroup-operation
 * for infinitely-differentiable functions.
 *)
Program Instance C_inf_ab_plus : SemiGroupOp C_inf_ab := 
  (fun f g => Build_C_inf_ab 
    (@Fplus IR (f_crr f) (f_crr g)) _ ).

Next Obligation.
apply Diffble_I_n_plus.
destruct f.
assert (f_crr (Build_C_inf_ab f_crr0 f_pdf0) = f_crr0).
auto.
rewrite H.
apply f_pdf0.
destruct g.
assert (f_crr (Build_C_inf_ab f_crr0 f_pdf0) = f_crr0).
auto.
rewrite H.
apply f_pdf0.
Qed.

(**
 * The standard equality between functions can be continued
 * to an equality on C_inf_ab (the functions that are
 * infinitely-times differentiable).
 *)
Program Instance C_inf_ab_eq : Equiv C_inf_ab :=
  (fun f g => sq (Feq (Compact (less_leEq _ _ _ Hab)) 
    (f_crr f) (f_crr g))).

(**
 * The addition in C_inf_ab is associative. This is 
 * represented here using a type class instance.
 *)
Instance C_inf_ab_associative : @Associative C_inf_ab
  (C_inf_ab_eq) C_inf_ab_plus.
unfold Associative.
intros.
unfold C_inf_ab_plus.
red.
unfold C_inf_ab_eq.
apply insq.
simpl.
FEQ.
apply included_FPlus.
destruct x.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply included_FPlus.
destruct y.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct z.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply included_FPlus.
apply included_FPlus.
destruct x.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct y.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct z.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
Qed.

(**
 * The addition we defined on C_inf_ab is a morphism 
 * with respect to our equality.
 *)
Instance C_inf_ab_proper : Proper (C_inf_ab_eq ==>
  C_inf_ab_eq ==> C_inf_ab_eq) C_inf_ab_plus.
unfold Proper.
unfold respectful.
intros.
red in H.
apply unsq in H.
red in H0.
apply unsq in H0.
unfold C_inf_ab_eq.
apply insq.
unfold C_inf_ab_plus.
simpl.
apply Feq_plus.
exact H.
exact H0.
Qed.

(**
 * Short proof that the equality we defined is also an
 * equivalence.
 *)
Instance C_inf_ab_equivalence : Equivalence C_inf_ab_eq.
assert (Reflexive C_inf_ab_eq).
unfold Reflexive.
intros.
unfold C_inf_ab_eq.
apply insq.
apply Feq_reflexive.
destruct x.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) with
  f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
assert (Symmetric C_inf_ab_eq).
unfold Symmetric.
intros.
unfold C_inf_ab_eq in H0.
apply unsq in H0.
unfold C_inf_ab_eq.
apply insq.
apply Feq_symmetric.
exact H0.
assert (Transitive C_inf_ab_eq).
unfold Transitive.
intros.
unfold C_inf_ab_eq in H1, H2.
apply unsq in H1; apply unsq in H2.
unfold C_inf_ab_eq; apply insq.
apply Feq_transitive with (f_crr y).
exact H1.
exact H2.
apply (Build_Equivalence C_inf_ab (C_inf_ab_eq) 
  H H0 H1).
Qed.

(**
 * This makes the infinitely differentiable functions on
 * [a,b] a semigroup with respect to functional addition.
 *)
Instance C_inf_ab_semigroup : @SemiGroup C_inf_ab 
  C_inf_ab_eq C_inf_ab_plus.

(** 
 * An n-times differentiable function can be multiplied with
 * an arbitrary constant.
 *)
Lemma Diffble_I_n_const : forall (n : nat) (c : IR),
  Diffble_I_n Hab n (Fconst c).
Proof.
  intro n.
  induction n.
  intro c.
  simpl.
  unfold included. 
  auto.
  intro c. 
  simpl.
  assert (Diffble_I Hab [-C-] c).
  apply Diffble_I_const.
  exists X.
  destruct X.
  simpl.
  assert (Derivative_I Hab [-C-]c [-C-]Zero).
  apply Derivative_I_const.
  apply Diffble_I_n_wd with ([-C-]Zero).
  apply Derivative_I_unique with ([-C-]c).
  exact X.
  exact d.
  apply IHn.
Qed.

(**
 * The constant zero function is a neutral element in
 * the definition of C_inf_ab as a monoid under addition.
 *)
Instance C_inf_ab_mon_unit : @MonoidUnit C_inf_ab :=
  (Build_C_inf_ab (Fconst Zero) _).
intros.
apply Diffble_I_n_const.
Defined.

(**
 * The infinitely-differentiable functions on [a,b] are
 * a monoid under addition.
 *)
Instance C_inf_ab_monoid : @Monoid C_inf_ab
  C_inf_ab_eq C_inf_ab_plus C_inf_ab_mon_unit.
assert (forall x, C_inf_ab_plus C_inf_ab_mon_unit
  x == x).
intros.
unfold C_inf_ab_mon_unit.
red.
unfold C_inf_ab_eq.
apply insq.
unfold C_inf_ab_plus.
simpl.
FEQ.
apply included_FPlus.
simpl.
unfold included.
auto.
destruct x.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) 
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct x.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) 
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
assert (forall x, 
  C_inf_ab_plus x C_inf_ab_mon_unit == x).
intros.
unfold C_inf_ab_mon_unit.
red.
unfold C_inf_ab_eq.
apply insq.
unfold C_inf_ab_plus.
simpl.
FEQ.
apply included_FPlus.
destruct x.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) 
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
simpl.
unfold included.
auto.
destruct x.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) 
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply (Build_Monoid C_inf_ab C_inf_ab_eq
  C_inf_ab_plus C_inf_ab_mon_unit
  C_inf_ab_semigroup H H0).
Qed.

(**
 * If a function is n-times differentiable, its functional
 * inverse also has this property. To prove this, we first
 * need an exact representation of the nth derivative.
 *)
Lemma Derivative_I_n_inv : forall (n : nat) (f f' : PartFunct IR),
  Derivative_I_n Hab n f f' -> Derivative_I_n Hab n (Finv f) (Finv f').
Proof.
  intro.
  induction n.
  intros.
  simpl.
  simpl in X.
  apply Feq_inv.
  exact X.
  intros.
  simpl.
  destruct X.
  exists (IInv x).
  apply Derivative_I_wdr with (Finv (PartInt x)).  
  apply part_int_inv.
  apply Feq_reflexive.
  apply derivative_imp_inc' with f.
  exact d.
  apply Derivative_I_inv.
  exact d.
  apply Derivative_I_n_wdl with (Finv (PartInt x)).
  apply part_int_inv.
  apply Feq_reflexive.
  apply derivative_imp_inc' with f.
  exact d.
  apply IHn.
  exact d0.
Qed.
  

(**
 * This is a small lemma to get from the nth derivative to
 * the n-times differentiability of the functional inverse.
 *)
Lemma Diffble_I_n_inv : forall (n : nat) (f : PartFunct IR),
  Diffble_I_n Hab n f -> Diffble_I_n Hab n (Finv f).
Proof.
  intros.
  assert ({f0' : CSetoid_fun (subset (Compact (less_leEq _ _ _ Hab))) IR |
    Derivative_I_n Hab n f (PartInt f0')}).   
  apply Diffble_I_n_imp_deriv_n.
  exact X.
  elim X0.
  intros.
  apply deriv_n_imp_Diffble_I_n with (Finv (PartInt x)).
  apply Derivative_I_n_inv.
  exact p.
Qed.

(**
 * Type class instance to define the inverse on C_inf_ab
 * as a group inversion operation.
 *)
Program Instance C_inf_ab_inv : GroupInv C_inf_ab := 
  (fun f => Build_C_inf_ab (Finv (f_crr f)) _).

Next Obligation.
apply Diffble_I_n_inv.
destruct f.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) with
  f_crr0 by auto. 
apply f_pdf0.
Defined.

(**
 * This inversion operation on C_inf_ab is a morphism with
 * respect to the equality as previously defined on C_inf_ab.
 *)
Instance C_inf_ab_proper_inv : Proper (C_inf_ab_eq ==>
  C_inf_ab_eq) C_inf_ab_inv.
intros.
unfold Proper.
unfold respectful.
intros.
red.
apply insq.
unfold C_inf_ab_inv.
simpl.
apply Feq_inv.
apply unsq.
inversion H.
apply insq.
exact X.
Qed.

(**
 * The infinitely-differentiable functions on [a,b] form
 * a group with respect to addition, inversion and the 
 * constant zero function.
 *)
Instance C_inf_ab_group : @Group C_inf_ab C_inf_ab_eq
  C_inf_ab_plus C_inf_ab_mon_unit C_inf_ab_inv.
assert (forall x, C_inf_ab_plus (C_inf_ab_inv x) x 
  == C_inf_ab_mon_unit).
intros.
red.
unfold C_inf_ab_eq.
apply insq.
unfold C_inf_ab_plus.
unfold C_inf_ab_inv.
simpl.
FEQ.
apply included_FPlus.
apply included_FInv.
destruct x.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct x.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
assert (forall x, C_inf_ab_plus x (C_inf_ab_inv x) 
  == C_inf_ab_mon_unit).
intros.
red.
unfold C_inf_ab_eq.
apply insq.
unfold C_inf_ab_plus.
unfold C_inf_ab_inv.
simpl.
FEQ.
apply included_FPlus.
destruct x.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply included_FInv.
destruct x.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply (Build_Group C_inf_ab C_inf_ab_eq C_inf_ab_plus
  C_inf_ab_mon_unit C_inf_ab_inv C_inf_ab_monoid 
  C_inf_ab_proper_inv H H0).
Qed.

(**
 * The addition operator we defined is commutative, 
 * resulting in an Abelian group for C_inf_ab.
 *)
Instance C_inf_ab_abgroup : @AbGroup C_inf_ab C_inf_ab_eq
  C_inf_ab_plus C_inf_ab_mon_unit C_inf_ab_inv.
assert (Commutative C_inf_ab_plus).
unfold Commutative.
intros.
unfold C_inf_ab_plus.
red.
unfold C_inf_ab_eq.
apply insq.
simpl.
FEQ.
apply included_FPlus.
destruct x.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) with
  f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct y.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) with
  f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply included_FPlus.
destruct y.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) with
  f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct x.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) with
  f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply (Build_AbGroup C_inf_ab C_inf_ab_eq C_inf_ab_plus
  C_inf_ab_mon_unit C_inf_ab_inv C_inf_ab_group H).
Qed.

(**
 * If f' is the nth derivative if f, it is immediate that
 * c*f' is the nth derivative of c*f.
 *)
Lemma Derivative_I_n_cmul : forall (n : nat) (f f' : PartFunct IR)
  (c : IR), Derivative_I_n Hab n f f' -> 
  Derivative_I_n Hab n (c{**}f) (c{**}f').
Proof.
  intro n.
  induction n.
  intros.
  simpl.
  simpl in X.
  unfold Fscalmult.
  apply Feq_mult.
  apply Feq_reflexive.
  unfold included.
  simpl.
  auto.
  exact X.
  intros.
  simpl.
  destruct X.
  exists (IMult (IConst c) x).
  apply Derivative_I_wdr with ((Fconst c) {*} PartInt x).
  apply part_int_mult.
  apply part_int_const.
  apply Feq_reflexive.
  apply derivative_imp_inc' with f.
  exact d.
  apply Derivative_I_scal.
  exact d.
  apply Derivative_I_n_wdl with ((Fconst c) {*} PartInt x).
  apply part_int_mult.
  apply part_int_const.
  apply Feq_reflexive.
  apply derivative_imp_inc' with f.
  exact d.
  apply IHn.
  exact d0.
Qed.

(**
 * Because of the previous lemma, it is only a small step to
 * the n-times differentiability of constant-multiplication.
 *)
Lemma Diffble_I_n_cmul : forall (n : nat) (f : PartFunct IR)
  (c : IR), Diffble_I_n Hab n f -> Diffble_I_n Hab n (c{**}f).
Proof.
  intros.
  assert ({f0' : CSetoid_fun (subset (Compact (less_leEq _ _ _ Hab))) IR |
    Derivative_I_n Hab n f (PartInt f0')}).   
  apply Diffble_I_n_imp_deriv_n.
  exact X.
  inversion_clear X0.
  apply deriv_n_imp_Diffble_I_n with (c{**}PartInt x).
  apply Derivative_I_n_cmul.
  exact X1.
Qed.

(**
 * Define the algebra-action (terminology from NAH) as an
 * operation on C_inf_ab using type class instances.
 *)
Program Instance C_inf_ab_ralg_act : RalgebraAction IR C_inf_ab :=
  (fun c f => Build_C_inf_ab (c {**} (f_crr f)) _).

Next Obligation.
apply Diffble_I_n_cmul.
destruct f.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) with
  f_crr0 by auto.
apply f_pdf0.
Defined.

(**
 * Addition and multiplication on IR, as well as addition
 * on C_inf_ab can be used to prove that the infinitely-
 * differentiable functions on [a,b] are an R-module.
 *)
Instance C_inf_ab_rmodule : @Rmodule IR (@st_eq IR) 
  C_inf_ab C_inf_ab_eq C_inf_ab_ralg_act IR_plus IR_mult
  IR_inv IR_zero IR_one C_inf_ab_plus C_inf_ab_mon_unit
  C_inf_ab_inv.
assert (forall (a b : C_inf_ab) (x : IR), 
  C_inf_ab_ralg_act x (C_inf_ab_plus a b) == 
  C_inf_ab_plus (C_inf_ab_ralg_act x a) (C_inf_ab_ralg_act x b)).
intros.
unfold C_inf_ab_ralg_act.
unfold C_inf_ab_plus.
simpl.
red.
unfold C_inf_ab_eq.
apply insq.
simpl.
FEQ.
apply included_FMult.
unfold included; simpl.
auto.
apply included_FPlus.
destruct a0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) with
  f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct b0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) with
  f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply included_FPlus.
apply included_FMult.
unfold included; simpl; auto.
destruct a0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) with
  f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply included_FMult.
unfold included; simpl; auto.
destruct b0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) with
  f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
assert (forall (a : C_inf_ab) (x y : IR), 
  C_inf_ab_ralg_act (x [+] y) a == 
  C_inf_ab_plus (C_inf_ab_ralg_act x a) 
    (C_inf_ab_ralg_act y a)).
intros.
unfold C_inf_ab_ralg_act, C_inf_ab_plus.
simpl.
red.
unfold C_inf_ab_eq.
apply insq.
simpl.
FEQ.
apply included_FMult.
unfold included; simpl; auto.
destruct a0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) with
  f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply included_FPlus.
apply included_FMult.
unfold included; simpl; auto.
destruct a0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) with
  f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply included_FMult.
unfold included; simpl; auto.
destruct a0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) with
  f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
assert (forall (a : C_inf_ab) (x y : IR), 
  C_inf_ab_ralg_act (x [*] y) a == 
  C_inf_ab_ralg_act x (C_inf_ab_ralg_act y a)).
intros.
unfold C_inf_ab_ralg_act; simpl.
red; unfold C_inf_ab_eq; simpl.
apply insq; FEQ.
apply included_FMult.
unfold included; simpl; auto.
destruct a0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) with
  f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply included_FMult.
unfold included; simpl; auto.
apply included_FMult.
unfold included; simpl; auto.
destruct a0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) with
  f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply (Build_Rmodule IR (@st_eq IR) C_inf_ab C_inf_ab_eq
  C_inf_ab_ralg_act IR_plus IR_mult IR_inv IR_zero IR_one
  C_inf_ab_plus C_inf_ab_mon_unit C_inf_ab_inv IR_ring
  C_inf_ab_abgroup H H0 H1).
Qed.

(**
 * The property of n-times differentiability is preserved
 * under multiplication. 
 *)
Lemma Diffble_I_n_mult : forall (n : nat)
  (f g : PartFunct IR) (Pfdf : Diffble_I_n Hab n f)
  (Pgdf : Diffble_I_n Hab n g), 
  Diffble_I_n Hab n (Fmult f g).
Proof.  
  intro n.
  induction n.
  intros.
  simpl.
  apply included_conj.
  simpl in Pfdf.
  exact Pfdf.
  simpl in Pgdf.
  exact Pgdf.
  intros.
  simpl.
  elim Pfdf.
  intros.
  inversion x.
  elim Pgdf.
  intros.
  inversion x1.
  assert (included (Compact (less_leEq _ _ _ Hab)) (Dom f)).
  apply derivative_imp_inc with (PartInt x0).
  exact X.
  assert (included (Compact (less_leEq _ _ _ Hab)) (Dom g)).
  apply derivative_imp_inc with (PartInt x2).
  exact X0.
  assert (Diffble_I Hab (f{*}g)).
  apply Diffble_I_mult.
  exact x.
  exact x1.
  exists X3.
  destruct X3.
  simpl.
  assert (Derivative_I Hab (f{*}g) 
    ((f{*}PartInt x2){+}(PartInt x0{*}g))).
  apply Derivative_I_mult.
  exact X.
  exact X0.
  apply Diffble_I_n_wd with (f{*}PartInt x2{+}PartInt x0{*}g).
  apply Derivative_I_unique with (f{*}g).
  exact X3.
  exact d.
  apply Diffble_I_n_plus.
  apply IHn.
  apply le_imp_Diffble_I with (S n).
  omega.
  exact Pfdf.
  destruct x1.
  simpl in p0.
  apply Diffble_I_n_wd with (PartInt x1).
  apply Derivative_I_unique with g.
  exact d0.
  exact X0.
  exact p0.
  apply IHn.
  destruct x.
  simpl in p.
  apply Diffble_I_n_wd with (PartInt x).
  apply Derivative_I_unique with f.
  exact d0.
  exact X.
  exact p.
  apply le_imp_Diffble_I with (S n).
  omega.
  exact Pgdf.
Qed.

(** 
 * Using the previous lemma, we can come up with a 
 * straightforward (but lengthy) proof about the 
 * n-times differentiability of functional division.
 *)
Lemma Diffble_I_n_div : forall (n : nat)
  (f g : PartFunct IR) (Pfdf : Diffble_I_n Hab n f)
  (Pgdf : Diffble_I_n Hab n g) 
  (Pbnd : bnd_away_zero (Compact (less_leEq _ _ _ Hab)) g), 
  Diffble_I_n Hab n (Fdiv f g).
Proof.
  intro n.
  induction n.
  intros f0 g Hf0 Hg Hbnd.
  simpl.
  unfold included.
  intros.
  red.
  split.
  simpl in Hf0.
  unfold included in Hf0.
  apply Hf0.
  exact H.
  red.
  split.
  simpl in Hg.
  unfold included in Hg.
  apply Hg.
  exact H.  
  intros.
  elim Hbnd.
  intros.
  elim b0.
  intros.
  apply AbsIR_cancel_ap_zero.
  apply pos_ap_zero.
  apply less_leEq_trans with x0.
  exact p.
  apply q.
  exact H.
  intros.
  simpl.
  simpl in Pfdf.
  inversion Pfdf.
  inversion x.
  simpl in Pgdf.
  inversion Pgdf.
  inversion x1.
  assert (Derivative_I Hab (f{/}g)
    (((PartInt x0){*}g{-}f{*}(PartInt x2)){/}
    (g{*}g))).
  apply Derivative_I_div.
  exact X0.
  exact X2.
  exact Pbnd.
  assert (Diffble_I Hab (f{/}g)).
  apply deriv_imp_Diffble_I with
    ((PartInt x0{*}g{-}f{*}PartInt x2){/}g{*}g).
  exact X3.
  exists X4.
  destruct X4.
  simpl.
  apply Diffble_I_n_wd with
    ((PartInt x0{*}g{-}f{*}PartInt x2){/}g{*}g).
  apply Derivative_I_unique with (f{/}g).
  exact X3.
  exact d.
  apply IHn.
  apply Diffble_I_n_minus.
  apply Diffble_I_n_mult.
  replace n with (pred (S n)) by omega.
  apply Diffble_I_imp_le with f.
  omega.
  simpl.
  exists x.
  exact X.
  exact X0.
  apply le_imp_Diffble_I with (S n).
  omega.
  simpl.
  exact Pgdf.
  apply Diffble_I_n_mult.
  apply le_imp_Diffble_I with (S n).
  omega.
  simpl.
  exact Pfdf.
  replace n with (pred (S n)) by omega.
  apply Diffble_I_imp_le with g.
  omega.
  simpl.
  exact Pgdf.
  exact X2.
  apply Diffble_I_n_mult.
  apply le_imp_Diffble_I with (S n).
  omega.
  simpl.
  exact Pgdf.
  apply le_imp_Diffble_I with (S n).
  omega.
  simpl.
  exact Pgdf.
  unfold bnd_away_zero.
  split. 
  apply included_FMult.
  apply Diffble_I_n_imp_inc with (S n).
  simpl.
  exact Pgdf.
  apply Diffble_I_n_imp_inc with (S n).
  simpl.
  exact Pgdf.
  unfold bnd_away_zero in Pbnd.
  inversion Pbnd.
  inversion X5.
  exists (x4[*]x4).
  apply mult_resp_pos.
  exact X6.
  exact X6. 
  intros.
  rewrite AbsIR_resp_mult.
  apply mult_resp_leEq_both.
  algebra.
  algebra.
  apply H.
  exact H0.
  apply H.
  exact H0.
Qed.

(**
 * We are now able to create a type class instance of
 * multiplication on C_inf_ab as a semi-group operation.
 *)
Program Instance C_inf_ab_mult : SemiGroupOp C_inf_ab := 
  (fun f g => Build_C_inf_ab 
    (@Fmult IR (f_crr f) (f_crr g)) _ ).

Next Obligation.
apply Diffble_I_n_mult.
destruct f.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
  with f_crr0 by auto.
apply f_pdf0.
destruct g.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
  with f_crr0 by auto.
apply f_pdf0.
Qed.

(**
 * Multiplication on C_inf_ab is associative.
 *)
Instance C_inf_ab_associative_mult : @Associative C_inf_ab
  (C_inf_ab_eq) C_inf_ab_mult.
unfold Associative.
intros.
unfold C_inf_ab_mult; simpl.
red; unfold C_inf_ab_eq.
apply insq; simpl.
FEQ.
apply included_FMult.
destruct x.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply included_FMult.
destruct y.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct z.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply included_FMult.
apply included_FMult.
destruct x.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct y.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct z.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
Qed.

(**
 * Multiplication on C_inf_ab is a morphism with respect
 * to the equality we previously defined. 
 *)
Instance C_inf_ab_proper_mult : Proper (C_inf_ab_eq ==>
  C_inf_ab_eq ==> C_inf_ab_eq) C_inf_ab_mult.
unfold Proper.
unfold respectful.
intros.
unfold C_inf_ab_eq, C_inf_ab_mult.
apply insq; simpl.
apply Feq_mult.
apply unsq; inversion H.
apply insq.
exact X.
apply unsq; inversion H0.
apply insq.
exact X.
Qed.

(**
 * The type class instance of C_inf_ab as a semigroup
 * under multiplication.
 *)
Instance C_inf_ab_semigroup_mult : @SemiGroup C_inf_ab 
  C_inf_ab_eq C_inf_ab_mult.

(**
 * The constant function one is a neutral element in the
 * multiplication of C_inf_ab.
 *)
Instance C_inf_ab_mon_unit_mult : @MonoidUnit C_inf_ab :=
  (Build_C_inf_ab (Fconst One) _).
intros.
apply Diffble_I_n_const.
Defined.

(**
 * C_inf_ab is a monoid under multiplication with 
 * the constant function one as unit element.
 *)
Instance C_inf_ab_monoid_mult : @Monoid C_inf_ab
  C_inf_ab_eq C_inf_ab_mult C_inf_ab_mon_unit_mult.
assert (forall x, C_inf_ab_mult C_inf_ab_mon_unit_mult
  x == x).
intros.
unfold C_inf_ab_mon_unit_mult.
red.
unfold C_inf_ab_eq.
apply insq.
unfold C_inf_ab_mult.
simpl.
FEQ.
apply included_FMult.
simpl.
unfold included.
auto.
destruct x.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) 
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct x.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) 
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
assert (forall x, 
  C_inf_ab_mult x C_inf_ab_mon_unit_mult == x).
intros.
unfold C_inf_ab_mon_unit_mult.
red.
unfold C_inf_ab_eq.
apply insq.
unfold C_inf_ab_mult.
simpl.
FEQ.
apply included_FMult.
destruct x.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) 
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
simpl.
unfold included.
auto.
destruct x.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0)) 
  with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply (Build_Monoid C_inf_ab C_inf_ab_eq
  C_inf_ab_mult C_inf_ab_mon_unit_mult
  C_inf_ab_semigroup_mult H H0).
Qed.

(**
 * C_inf_ab is a ring with respect to its addition and
 * multiplication operators.
 *)
Instance C_inf_ab_ring : @Ring C_inf_ab C_inf_ab_eq
  C_inf_ab_plus C_inf_ab_mult C_inf_ab_inv
  C_inf_ab_mon_unit C_inf_ab_mon_unit_mult.
assert (Commutative C_inf_ab_mult).
unfold Commutative.
intros; red.
unfold C_inf_ab_mult, C_inf_ab_eq.
apply insq; simpl.
FEQ.
apply included_FMult.
destruct x.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct y.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply included_FMult.
destruct y.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct x.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
assert (Distribute C_inf_ab_mult C_inf_ab_plus).
assert (forall a b c, C_inf_ab_mult a (C_inf_ab_plus b c) ==
  C_inf_ab_plus (C_inf_ab_mult a b) (C_inf_ab_mult a c)).
intros.
unfold C_inf_ab_mult, C_inf_ab_plus; red; simpl.
unfold C_inf_ab_eq; simpl; apply insq; FEQ.
apply included_FMult.
destruct a0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply included_FPlus.
destruct b0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct c.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply included_FPlus.
apply included_FMult.
destruct a0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct b0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply included_FMult.
destruct a0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct c.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
assert (forall a b c, C_inf_ab_mult (C_inf_ab_plus a b) c ==
  C_inf_ab_plus (C_inf_ab_mult a c) (C_inf_ab_mult b c)).
intros.
unfold C_inf_ab_mult, C_inf_ab_plus; simpl; red.
unfold C_inf_ab_eq; simpl; apply insq; FEQ.
apply included_FMult.
apply included_FPlus.
destruct a0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct b0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct c.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply included_FPlus.
apply included_FMult.
destruct a0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct c.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply included_FMult.
destruct b0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct c.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply (Build_Distribute C_inf_ab C_inf_ab_eq
  C_inf_ab_mult C_inf_ab_plus H0 H1).
apply (Build_Ring C_inf_ab C_inf_ab_eq C_inf_ab_plus
  C_inf_ab_mult C_inf_ab_inv C_inf_ab_mon_unit C_inf_ab_mon_unit_mult
  C_inf_ab_abgroup C_inf_ab_monoid_mult H H0).
Qed.

(**
 * Together with the operations in IR, we may use the 
 * addition and multiplication in C_inf_ab to define
 * and R-algebra for the infinitely-differentiable functions.
 *)
Instance C_inf_ab_ralgebra : @Ralgebra IR (@st_eq IR) 
  C_inf_ab C_inf_ab_eq C_inf_ab_ralg_act IR_plus IR_mult
  IR_inv IR_zero IR_one C_inf_ab_plus C_inf_ab_mult 
  C_inf_ab_mon_unit C_inf_ab_mon_unit_mult C_inf_ab_inv.
assert (forall (a b : C_inf_ab) (x : IR), 
  C_inf_ab_ralg_act x (C_inf_ab_mult a b) == 
  C_inf_ab_mult (C_inf_ab_ralg_act x a) b).
intros.
unfold C_inf_ab_ralg_act, C_inf_ab_mult; red.
unfold C_inf_ab_eq; simpl.
apply insq; FEQ.
apply included_FMult.
unfold included; simpl; auto.
apply included_FMult.
destruct a0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct b0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply included_FMult.
apply included_FMult.
unfold included; simpl; auto.
destruct a0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
destruct b0.
replace (f_crr (Build_C_inf_ab f_crr0 f_pdf0))
 with f_crr0 by auto.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply (Build_Ralgebra IR (@st_eq IR) C_inf_ab C_inf_ab_eq
  C_inf_ab_ralg_act IR_plus IR_mult IR_inv IR_zero IR_one
  C_inf_ab_plus C_inf_ab_mult C_inf_ab_mon_unit C_inf_ab_mon_unit_mult
  C_inf_ab_inv C_inf_ab_rmodule C_inf_ab_ring H).
Qed.

(**
 * This is the definition of the abstract property of 
 * derivation on an R-algebra.
 *)
Definition is_derivation `(Ralgebra Scalar Elem) 
  (D : Elem -> Elem) : Prop.
repeat intro.
exact (
  (forall (a b : Elem), e' (elem_plus (D a) (D b)) (D (elem_plus a b))) and
  (forall (a : Elem) (c : Scalar), e' (H c (D a)) (D (H c a))) and
  (forall (a b : Elem), e' (D (elem_mult a b)) 
    (elem_plus (elem_mult a (D b)) (elem_mult (D a) b)))).
Defined.

(**
 * Define the derivative of a function in C_inf_ab as a
 * directly-callable operation. That is, the result of 
 * the expression is the required derivative.
 *)
Definition deriv_I_C_inf (f : C_inf_ab) : C_inf_ab.
intro.
destruct f.
assert (Diffble_I_n Hab 1 f_crr0).
apply f_pdf0.
set (n_deriv_I a b Hab 1 f_crr0 X).
assert (forall n, Diffble_I_n Hab n p).
intro n.
replace n with (pred (S n)) by omega.
apply Diffble_I_imp_le with f_crr0.
omega.
apply f_pdf0.
assert (Diffble_I_n Hab 0 f_crr0).
simpl.
apply Diffble_I_n_imp_inc with 42.
apply f_pdf0.
apply Derivative_I_wdl with (n_deriv_I a b Hab 0 f_crr0 X0).
simpl.
apply Feq_symmetric.
apply FRestr_wd.
apply n_Sn_deriv.
exact (Build_C_inf_ab p X0).
Defined.

(**
 * This corresponds to proposition 25 in the PDF as sent to 
 * me on january 11th. We prove that the derivation operator
 * deriv_I_C_inf on C_inf_ab is a derivation with respect
 * to the R_algebra we defined on C_inf_ab.
 *
 * TODO: This proof can be made shorter
 *)
Lemma lem18 : is_derivation C_inf_ab_ralgebra deriv_I_C_inf.
Proof.
  unfold is_derivation.
  split.
  intros.
  unfold C_inf_ab_eq.
  apply insq.
  unfold C_inf_ab_plus.
  destruct a0.
  destruct b0.
  assert (forall x y, f_crr
    (Build_C_inf_ab x y) = x).
  intros.
  auto.
  rewrite H.
  assert (f_crr (deriv_I_C_inf (Build_C_inf_ab f_crr0 f_pdf0)) = 
    n_deriv_I a b Hab 1 f_crr0 (f_pdf0 1)).
  auto.
  rewrite H0.
  assert (f_crr (deriv_I_C_inf (Build_C_inf_ab f_crr1 f_pdf1)) = 
    n_deriv_I a b Hab 1 f_crr1 (f_pdf1 1)).
  auto.
  rewrite H1.
  assert (f_crr
    (deriv_I_C_inf
      (Build_C_inf_ab
        (f_crr (Build_C_inf_ab f_crr0 f_pdf0){+}
         f_crr (Build_C_inf_ab f_crr1 f_pdf1))
           (C_inf_ab_plus_obligation_1 
              (Build_C_inf_ab f_crr0 f_pdf0)
              (Build_C_inf_ab f_crr1 f_pdf1)))) = 
    n_deriv_I a b Hab 1 
      (f_crr0{+}f_crr1)
      (C_inf_ab_plus_obligation_1 
        (Build_C_inf_ab f_crr0 f_pdf0) 
        (Build_C_inf_ab f_crr1 f_pdf1) 1)).
  auto.
  rewrite H2.
  clear H H0 H1 H2. 
  apply Feq_transitive with 
    (n_deriv_I a b Hab 1 (f_crr0{+}f_crr1) 
      (Diffble_I_n_plus 1 f_crr0 f_crr1 
        (f_pdf0 1) (f_pdf1 1))).
  assert ({f_crr0' : CSetoid_fun (subset (Compact (less_leEq _ _ _ Hab))) IR | 
   Derivative_I_n Hab 1 f_crr0 (PartInt f_crr0')}).
  apply Diffble_I_n_imp_deriv_n.
  apply f_pdf0.
  inversion_clear X.
  assert (Derivative_I_n Hab 1 f_crr0
    (n_deriv_I a b Hab 1 f_crr0 (f_pdf0 1))).  
  apply n_deriv_lemma.
  assert (Feq (Compact (less_leEq IR a b Hab))
    (PartInt x) (n_deriv_I a b Hab 1 f_crr0 (f_pdf0 1))).
  apply (Derivative_I_n_unique a b Hab 1 f_crr0).
  exact X0.
  exact X.
  assert ({f_crr1' : CSetoid_fun (subset (Compact (less_leEq _ _ _ Hab))) IR | 
   Derivative_I_n Hab 1 f_crr1 (PartInt f_crr1')}).
  apply Diffble_I_n_imp_deriv_n.
  apply f_pdf1.
  inversion_clear X2.
  assert (Derivative_I_n Hab 1 f_crr1
    (n_deriv_I a b Hab 1 f_crr1 (f_pdf1 1))).  
  apply n_deriv_lemma.
  assert (Feq (Compact (less_leEq IR a b Hab))
    (PartInt x0) (n_deriv_I a b Hab 1 f_crr1 (f_pdf1 1))).
  apply (Derivative_I_n_unique a b Hab 1 f_crr1).
  exact X3.
  exact X2.
  assert (Feq (Compact (less_leEq IR a b Hab)) 
    (PartInt x{+}PartInt x0)
    ((n_deriv_I a b Hab 1 f_crr0 (f_pdf0 1)){+}
     (n_deriv_I a b Hab 1 f_crr1 (f_pdf1 1)))).
  apply Feq_plus.
  exact X1.
  exact X4.
  apply Feq_transitive with (PartInt x{+}PartInt x0).
  apply Feq_plus.
  apply Feq_symmetric; exact X1.
  apply Feq_symmetric; exact X4.
  assert (Derivative_I_n Hab 1 (f_crr0{+}f_crr1)
    (PartInt x{+}PartInt x0)).
  apply Derivative_I_n_add.
  exact X0.
  exact X3.
  assert (Derivative_I_n Hab 1 (f_crr0{+}f_crr1)
    ((n_deriv_I a b Hab 1 (f_crr0{+}f_crr1)
     (Diffble_I_n_plus 1 f_crr0 f_crr1 (f_pdf0 1) (f_pdf1 1))))).
  apply n_deriv_lemma.
  apply (Derivative_I_n_unique a b Hab 1 
    (f_crr0{+}f_crr1)).
  exact X6.
  exact X7.
  apply n_deriv_I_wd.
  apply Feq_plus.
  apply Feq_reflexive.
  apply Diffble_I_n_imp_inc with 42.
  apply f_pdf0.
  apply Feq_reflexive.
  apply Diffble_I_n_imp_inc with 42.
  apply f_pdf1.
  split.
  intros.
  unfold C_inf_ab_eq.
  apply insq.
  unfold C_inf_ab_ralg_act.
  assert (forall x y, 
    f_crr (Build_C_inf_ab x y) = x) by auto.
  rewrite H.
  destruct a0.
  assert (f_crr (deriv_I_C_inf
    (Build_C_inf_ab f_crr0 f_pdf0)) =
    n_deriv_I a b Hab 1 f_crr0 (f_pdf0 1)).
  auto.
  rewrite H0.
  assert ( 
    f_crr
     (deriv_I_C_inf
       (Build_C_inf_ab (c{**}f_crr (Build_C_inf_ab f_crr0 f_pdf0)) 
       (C_inf_ab_ralg_act_obligation_1 c 
         (Build_C_inf_ab f_crr0 f_pdf0)))) =
    n_deriv_I a b Hab 1 (c{**}f_crr0)
      (C_inf_ab_ralg_act_obligation_1 c 
        (Build_C_inf_ab f_crr0 f_pdf0) 1)).
  auto.
  rewrite H1.
  clear H H0 H1.
  apply Feq_transitive with
    (n_deriv_I a b Hab 1 (c{**}f_crr0)
      (Diffble_I_n_cmul 1 f_crr0 c (f_pdf0 1))).
  assert ({f_crr0' : CSetoid_fun (subset (Compact (less_leEq _ _ _ Hab))) IR | 
    Derivative_I_n Hab 1 f_crr0 (PartInt f_crr0')}).
  apply Diffble_I_n_imp_deriv_n.
  apply f_pdf0.
  inversion_clear X.
  assert (Derivative_I_n Hab 1 f_crr0
    (n_deriv_I a b Hab 1 f_crr0 (f_pdf0 1))).
  apply n_deriv_lemma.
  assert (Feq (Compact (less_leEq IR a b Hab))
    (PartInt x) (n_deriv_I a b Hab 1 f_crr0 (f_pdf0 1))).
  apply (Derivative_I_n_unique a b Hab 1 f_crr0).
  exact X0.
  exact X.
  assert (Derivative_I_n Hab 1 (c{**}f_crr0)
    (c{**}PartInt x)).
  apply Derivative_I_n_cmul.
  exact X0.
  assert (Derivative_I_n Hab 1 (c{**}f_crr0) 
    ((n_deriv_I a b Hab 1 (c{**}f_crr0) 
      (Diffble_I_n_cmul 1 f_crr0 c (f_pdf0 1))))).
  apply n_deriv_lemma.
  apply Feq_transitive with (c{**}PartInt x).
  unfold Fscalmult.
  apply Feq_mult.
  apply Feq_reflexive.
  unfold included; simpl; auto.
  apply Feq_symmetric.
  exact X1.
  assert (Derivative_I_n Hab 1 (c{**}f_crr0)
    (c{**}(n_deriv_I a b Hab 1 f_crr0 (f_pdf0 1)))).
  apply Derivative_I_n_cmul.
  apply n_deriv_lemma.
  assert (Derivative_I_n Hab 1 (c{**}f_crr0)
    (c{**}PartInt x)).
  apply Derivative_I_n_cmul.
  exact X0.
  apply Feq_transitive with 
    (c{**}n_deriv_I a b Hab 1 f_crr0 (f_pdf0 1)).
  unfold Fscalmult.
  apply Feq_mult.
  apply Feq_reflexive.
  unfold included; simpl; auto.
  exact X1.
  apply Feq_transitive with (c{**}PartInt x).
  apply (Derivative_I_n_unique a b Hab 1 
    (c{**}f_crr0)). 
  exact X4.
  exact X2.
  apply Feq_transitive with
    (c{**}n_deriv_I a b Hab 1 f_crr0 (f_pdf0 1)).
  unfold Fscalmult.
  apply Feq_mult.
  apply Feq_reflexive.
  unfold included; simpl; auto.
  exact X1.
  apply (Derivative_I_n_unique a b Hab 1
    (c{**}f_crr0)).
  exact X4.
  exact X3.
  apply n_deriv_I_wd.
  unfold Fscalmult.
  apply Feq_mult.
  apply Feq_reflexive.
  unfold included; simpl; auto.
  apply Feq_reflexive.
  apply Diffble_I_n_imp_inc with 42.
  apply f_pdf0.
  intros.
  unfold C_inf_ab_eq. 
  apply insq.
  destruct a0.
  destruct b0.
  unfold C_inf_ab_mult, C_inf_ab_plus.
  set (f_crr (Build_C_inf_ab f_crr0 f_pdf0)).
  set (f_crr (Build_C_inf_ab f_crr1 f_pdf1)).
  set (deriv_I_C_inf (Build_C_inf_ab f_crr0 f_pdf0)).
  set (deriv_I_C_inf (Build_C_inf_ab f_crr1 f_pdf1)).
  set (Build_C_inf_ab f_crr0 f_pdf0).
  set (Build_C_inf_ab f_crr1 f_pdf1).
  replace 
    (f_crr
      (deriv_I_C_inf
        (Build_C_inf_ab (p{*}p0) 
           (C_inf_ab_mult_obligation_1 c1 c2))))
  with
    (n_deriv_I a b Hab 1 (p{*}p0)
      (C_inf_ab_mult_obligation_1 c1 c2 1)) by auto.
  replace
    (f_crr
      (Build_C_inf_ab
        (f_crr
           (Build_C_inf_ab (p{*}f_crr c0) 
           (C_inf_ab_mult_obligation_1 c1 c0)){+}
         f_crr
           (Build_C_inf_ab (f_crr c{*}p0) 
           (C_inf_ab_mult_obligation_1 c c2)))
        (C_inf_ab_plus_obligation_1
           (Build_C_inf_ab (p{*}f_crr c0) 
           (C_inf_ab_mult_obligation_1 c1 c0))
           (Build_C_inf_ab (f_crr c{*}p0) 
           (C_inf_ab_mult_obligation_1 c c2)))))
  with
    (f_crr
      (Build_C_inf_ab (p{*}f_crr c0) 
      (C_inf_ab_mult_obligation_1 c1 c0)){+}
     f_crr
      (Build_C_inf_ab (f_crr c{*}p0) 
      (C_inf_ab_mult_obligation_1 c c2))) by auto.
  replace (f_crr ((Build_C_inf_ab 
    (f_crr c{*}p0) 
    (C_inf_ab_mult_obligation_1 c c2))))
  with
    (f_crr c{*}p0) by auto.
  replace (f_crr (Build_C_inf_ab 
    (p{*}f_crr c0) 
    (C_inf_ab_mult_obligation_1 c1 c0)))
  with
    (p{*}f_crr c0) by auto.
  assert (Derivative_I_n Hab 1 (p{*}p0)
    (n_deriv_I a b Hab 1 (p{*}p0) 
      (C_inf_ab_mult_obligation_1 c1 c2 1))).
  apply n_deriv_lemma.
  assert ({f_crr0' : CSetoid_fun (subset (Compact (less_leEq _ _ _ Hab))) IR | 
    Derivative_I_n Hab 1 f_crr0 (PartInt f_crr0')}).
  apply Diffble_I_n_imp_deriv_n.
  apply f_pdf0.
  inversion_clear X0.
  assert ({f_crr1' : CSetoid_fun (subset (Compact (less_leEq _ _ _ Hab))) IR |
    Derivative_I_n Hab 1 f_crr1 (PartInt f_crr1')}).
  apply Diffble_I_n_imp_deriv_n.
  apply f_pdf1.
  inversion_clear X0.
  assert (Derivative_I_n Hab 1 (p{*}p0)
    (f_crr0{*}PartInt x0{+}PartInt x{*}f_crr1)).
  simpl.
  assert (included (Compact (less_leEq _ _ _ Hab)) (Dom 
    (f_crr0{*}PartInt x0{+}PartInt x{*}f_crr1))).
  apply included_FPlus.
  apply included_FMult.
  apply (Derivative_I_n_imp_inc a b Hab 1 f_crr0
    (PartInt x)).
  exact X1.
  apply (Derivative_I_n_imp_inc' a b Hab 1 
    f_crr1 (PartInt x0)).
  exact X2.
  apply included_FMult.
  apply (Derivative_I_n_imp_inc' a b Hab 1 
    f_crr0 (PartInt x)).
  exact X1.
  apply (Derivative_I_n_imp_inc a b Hab 1 f_crr1
    (PartInt x0)).
  exact X2.
  exists (@IntPartIR 
    (f_crr0{*}PartInt x0{+}PartInt x{*}f_crr1)
    a b (less_leEq _ _ _ Hab) X0).
  apply Derivative_I_wdr with 
    (f_crr0{*}PartInt x0{+}PartInt x{*}f_crr1).
  apply int_part_int.
  replace p with f_crr0 by auto.
  replace p0 with f_crr1 by auto.
  apply Derivative_I_mult.
  simpl in X1.
  inversion_clear X1.
  apply Derivative_I_wdr with (PartInt x1).
  exact X4.
  exact X3.
  simpl in X2.
  inversion_clear X2.
  apply Derivative_I_wdr with (PartInt x1).
  exact X4.
  exact X3.
  apply Feq_symmetric.
  apply int_part_int.
  apply Feq_transitive with
    (p{*}f_crr c0{+}f_crr c{*}p0).
  apply (Derivative_I_n_unique a b Hab 1 (p{*}p0)).
  exact X.
  replace p with f_crr0 by auto.
  replace p0 with f_crr1 by auto.
  replace (f_crr c0) with
    (n_deriv_I a b Hab 1 f_crr1 (f_pdf1 1)) by auto.
  replace (f_crr c) with
    (n_deriv_I a b Hab 1 f_crr0 (f_pdf0 1)) by auto.
  replace p with f_crr0 in X0 by auto.
  replace p0 with f_crr1 in X0 by auto.
  apply Derivative_I_n_wdr with
    (f_crr0{*}PartInt x0{+}PartInt x{*}f_crr1).
  apply Feq_plus.
  apply Feq_mult.
  apply Feq_reflexive.
  apply (Derivative_I_n_imp_inc a b Hab 1 f_crr0
    (PartInt x)).
  exact X1.
  assert (Derivative_I_n Hab 1 f_crr1
    (n_deriv_I a b Hab 1 f_crr1 (f_pdf1 1))).
  apply n_deriv_lemma.
  apply (Derivative_I_n_unique a b Hab 1 f_crr1).
  exact X2.
  apply n_deriv_lemma.
  apply Feq_mult.
  apply (Derivative_I_n_unique a b Hab 1 f_crr0).
  exact X1.
  apply n_deriv_lemma.
  apply Feq_reflexive.
  apply (Derivative_I_n_imp_inc a b Hab 1 f_crr1
    (PartInt x0)).
  exact X2.
  exact X0.
  apply Feq_reflexive.
  apply included_FPlus.
  apply included_FMult.
  replace p with f_crr0 by auto.
  apply (Derivative_I_n_imp_inc a b Hab 1 f_crr0
    (PartInt x)).
  exact X1.
  replace (f_crr c0) with
    (n_deriv_I a b Hab 1 f_crr1 (f_pdf1 1)) by auto.
  apply n_deriv_inc.
  apply included_FMult.
  replace (f_crr c) with
    (n_deriv_I a b Hab 1 f_crr0 (f_pdf0 1)) by auto.
  apply n_deriv_inc.
  replace p0 with f_crr1 by auto.
  apply (Derivative_I_n_imp_inc a b Hab 1 f_crr1
    (PartInt x0)).
  exact X2.
Qed.

End Derivations.

(**
 * This section contains lemmas and definitions about the 
 * function L. Note that the order in which things appear
 * in the proof differs from the order in the paper because
 * the proof is still based on a previous version of the
 * paper.
 *)

Section Lfunct.

Variables a b c d : IR.
Hypothesis Hab : a [<] b.
Hypothesis Hcd : c [<] d.

Hypothesis Hac : a [<=] c.
Hypothesis Hdb : d [<=] b.

(**
 * TODO: This lemma is unneccesary.
 *)
Lemma ab_diff : b [-] a [#] Zero.
Proof.
  apply minus_ap_zero.
  apply Greater_imp_ap.
  exact Hab.
Qed.

(**
 * We don't define L_inner as a direct lambda-expression
 * but instead as a composition of functions because this
 * enhances the usage of this definition in the proof.
 *)
Definition L_inner :=
  Fplus (Fconst c)
    (Fmult (Fminus (Fconst d) (Fconst c))
      (Fdiv (Fminus (Fid IR) (Fconst a))
        (Fminus (Fconst b) (Fconst a)))).

Definition L_func (f : C_inf_ab c d Hcd) :=
  Fcomp (f_crr c d Hcd f) L_inner.

(**
 * Prove that the function L is n-times differentiable for
 * each n. This effectively proves that the function L 
 * belongs to the class C_inf_ab.
 *)
Lemma L_diffble : forall (n : nat) (f : C_inf_ab c d Hcd), 
  Diffble_I_n Hab n  (L_func f).
Proof.
  intro n.
  induction n.
  intro f0.
  unfold L_func.
  simpl.
  unfold included.
  intros.
  assert (Conj (fun _ : IR => True) (Conj (Conj (fun _ : IR => True) 
    (fun _ : IR => True)) (Conj (Conj (fun _ : IR => True) 
    (fun _ : IR => True)) (extend (Conj (fun _ : IR => True) 
    (fun _ : IR => True)) (fun (x0 : IR) (_ : Conj (fun _ : IR => True) 
    (fun _ : IR => True) x0) => b[-]a[#]Zero)))) x).
  unfold extend.
  red.
  split.
  auto.
  red.
  split.
  red.
  auto.
  red.
  split.
  red.
  auto.
  split.
  red.
  auto.
  intro.
  apply ab_diff.
  exists X.
  destruct f0.
  replace (f_crr c d Hcd (Build_C_inf_ab c d Hcd f_crr0 f_pdf0))
    with f_crr0 by auto.
  destruct f_crr0.
  simpl.
  assert (included (Compact (less_leEq _ _ _ Hcd)) pfdom).
  assert (Diffble_I_n Hcd 0
    (Build_PartFunct IR pfdom dom_wd pfpfun pfstrx)).
  apply f_pdf0.
  simpl in X0.
  exact X0.
  unfold included in X0.
  apply X0.
  red.
  split.
  red in H.
  rewrite <- cm_rht_unit_unfolded at 1.
  apply plus_resp_leEq_lft.
  rewrite <- (cring_mult_zero_op IR Zero).
  apply mult_resp_leEq_both.
  apply leEq_reflexive.  
  apply leEq_reflexive.
  apply shift_leEq_lft.
  algebra.
  apply shift_leEq_div.
  apply shift_zero_less_minus.
  exact Hab.
  rewrite cring_mult_zero_op.
  apply shift_leEq_lft.
  inversion H.
  exact H0.
  apply shift_plus_leEq'.
  rewrite <- (mult_one IR (d[-]c)) at 2.
  apply mult_resp_leEq_both.
  apply shift_leEq_lft.
  algebra.
  apply shift_leEq_div.
  apply shift_zero_less_minus.
  exact Hab.
  rewrite cring_mult_zero_op.
  red in H.
  inversion H.
  apply shift_leEq_lft.
  exact H0.
  apply leEq_reflexive.
  apply shift_div_leEq.
  apply shift_zero_less_minus.
  exact Hab.
  rewrite mult_commutes.
  rewrite mult_one.
  apply minus_resp_leEq_both.
  red in H.
  inversion H.
  exact H1.
  apply leEq_reflexive.
  intro f0.
  simpl.
  assert (Derivative_I Hab L_inner
    (
      ([-C-] Zero) {+}
      (
        ([-C-] d {-} [-C-] c) {*}
          (
            Fdiv 
              ((([-C-] One) {*} ([-C-] b {-} [-C-] a)) {-}
               ((Fid IR {-} [-C-] a) {*} ([-C-] Zero)))
              (([-C-] b {-} [-C-] a) {*} ([-C-] b {-} [-C-] a))
          )
        {+}
        ([-C-] Zero) {*}
          (
            Fdiv (Fid IR {-} [-C-] a)
                 ([-C-] b {-} [-C-] a)
          )
      )
    )).
  unfold L_inner.
  apply Derivative_I_plus.
  apply Derivative_I_const.
  apply Derivative_I_mult.
  apply Derivative_I_wdr with ([-C-]Zero{-}[-C-]Zero).
  FEQ.
  apply Derivative_I_minus.
  apply Derivative_I_const.
  apply Derivative_I_const.
  apply Derivative_I_div.
  apply Derivative_I_wdr with ([-C-]One{-}[-C-]Zero).
  FEQ.
  apply Derivative_I_minus.
  apply Derivative_I_id.
  apply Derivative_I_const.
  apply Derivative_I_wdr with ([-C-]Zero{-}[-C-]Zero).
  FEQ.
  apply Derivative_I_minus.
  apply Derivative_I_const.
  apply Derivative_I_const.
  red.
  split.
  apply included_FMinus.
  unfold included; simpl; auto.
  unfold included; simpl; auto.
  exists (AbsIR (b[-]a)).
  apply AbsIR_pos.  
  apply ab_diff.
  intros.
  simpl.
  apply leEq_reflexive.
  assert (Diffble_I Hcd (f_crr c d Hcd f0)).  
  destruct f0; simpl.
  apply Diffble_I_n_imp_diffble with 42.
  omega.
  apply f_pdf0.
  destruct X0.
  assert (forall n, Diffble_I_n Hcd n (PartInt x)).
  intro n0.
  replace n0 with (pred (S n0)) by omega.
  apply Diffble_I_imp_le with (f_crr c d Hcd f0).
  omega.
  destruct f0.
  replace (f_crr c d Hcd (Build_C_inf_ab c d Hcd f_crr0 f_pdf0))
    with f_crr0 by auto.
  apply f_pdf0.
  exact d0.
  assert (Derivative_I Hab (L_func f0)
    ((L_func (Build_C_inf_ab c d Hcd (PartInt x) X0)) {*} 
    (([-C-]Zero{+}
       (([-C-]d{-}[-C-]c){*}
        (([-C-]One{*}([-C-]b{-}[-C-]a){-}(FId{-}[-C-]a){*}[-C-]Zero){/}
         ([-C-]b{-}[-C-]a){*}([-C-]b{-}[-C-]a)){+}
        [-C-]Zero{*}((FId{-}[-C-]a){/}([-C-]b{-}[-C-]a))))))
  ).
  unfold L_func.
  apply (Derivative_I_comp _ _ _ _ _ _ _ c d Hcd).
  exact X.
  simpl.
  exact d0.
  unfold maps_into_compacts.
  split.
  destruct f0.
  simpl.
  apply Diffble_I_n_imp_inc with 42.
  apply f_pdf0.
  intros.
  red.
  split.
  unfold L_inner.
  simpl.
  rewrite <- cm_rht_unit_unfolded at 1.
  apply plus_resp_leEq_lft.
  rewrite <- (cring_mult_zero_op IR Zero).
  apply mult_resp_leEq_both.
  apply leEq_reflexive.  
  apply leEq_reflexive.
  apply shift_leEq_lft.
  algebra.
  apply shift_leEq_div.
  apply shift_zero_less_minus.
  exact Hab.
  rewrite cring_mult_zero_op.
  apply shift_leEq_lft.
  inversion H.
  exact H0.
  unfold L_inner.
  simpl.
  apply shift_plus_leEq'.
  rewrite <- (mult_one IR (d[-]c)) at 2.
  apply mult_resp_leEq_both.
  apply shift_leEq_lft.
  algebra.
  apply shift_leEq_div.
  apply shift_zero_less_minus.
  exact Hab.
  rewrite cring_mult_zero_op.
  inversion H.
  apply shift_leEq_lft.
  exact H0.
  apply leEq_reflexive.
  apply shift_div_leEq.
  apply shift_zero_less_minus.
  exact Hab.
  rewrite mult_commutes.
  rewrite mult_one.
  apply minus_resp_leEq_both.
  inversion H.
  exact H1.
  apply leEq_reflexive.
  assert (Diffble_I Hab (L_func f0)).
  apply (deriv_imp_Diffble_I _ _ _ _ _ X1).
  exists X2.
  destruct X2.
  simpl.
  apply Diffble_I_n_wd with
    (L_func (Build_C_inf_ab c d Hcd (PartInt x) X0){*}
      ([-C-]Zero{+}(([-C-]d{-}[-C-]c){*}
       (([-C-]One{*}([-C-]b{-}[-C-]a){-}(FId{-}[-C-]a){*}[-C-]Zero){/}
       ([-C-]b{-}[-C-]a){*}([-C-]b{-}[-C-]a)){+}
       [-C-]Zero{*}((FId{-}[-C-]a){/}([-C-]b{-}[-C-]a))))).
  apply Derivative_I_unique with (L_func f0).
  exact X1.
  exact d1.
  apply Diffble_I_n_mult.
  apply IHn.
  apply Diffble_I_n_plus.
  apply Diffble_I_n_const.
  apply Diffble_I_n_plus.
  apply Diffble_I_n_mult.
  apply Diffble_I_n_minus.
  apply Diffble_I_n_const.
  apply Diffble_I_n_const.
  apply Diffble_I_n_div.
  apply Diffble_I_n_minus.
  apply Diffble_I_n_mult.
  apply Diffble_I_n_const.
  apply Diffble_I_n_minus.
  apply Diffble_I_n_const.
  apply Diffble_I_n_const.
  apply Diffble_I_n_wd with ([-C-] Zero).
  FEQ.
  apply Diffble_I_n_const.
  apply Diffble_I_n_mult.
  apply Diffble_I_n_minus.
  apply Diffble_I_n_const.
  apply Diffble_I_n_const.
  apply Diffble_I_n_minus.
  apply Diffble_I_n_const.
  apply Diffble_I_n_const.
  unfold bnd_away_zero.
  split.
  apply included_FMult.
  apply included_FMinus.
  unfold included; simpl; auto.
  unfold included; simpl; auto.
  apply included_FMinus.  
  unfold included; simpl; auto.
  unfold included; simpl; auto.
  exists ((b[-]a)[*](b[-]a)).
  apply mult_resp_pos.
  apply shift_zero_less_minus.
  exact Hab.
  apply shift_zero_less_minus.
  exact Hab.
  intros.
  rewrite AbsIR_resp_mult.
  apply mult_resp_leEq_both.
  apply shift_zero_leEq_minus.
  algebra.
  apply shift_zero_leEq_minus.
  algebra.
  apply eq_imp_leEq.
  symmetry.
  apply AbsIR_eq_x.
  apply shift_zero_leEq_minus.
  algebra.
  apply eq_imp_leEq.
  symmetry.
  apply AbsIR_eq_x.
  algebra.
  apply Diffble_I_n_wd with ([-C-] Zero).
  apply eq_imp_Feq.
  unfold included; simpl; auto.
  apply included_FMult.
  unfold included; simpl; auto.
  apply included_FDiv.
  apply included_FMinus.
  unfold included; simpl; auto.
  unfold included; simpl; auto.
  apply included_FMinus.
  unfold included; simpl; auto.
  unfold included; simpl; auto.
  intros.
  simpl.
  apply pos_ap_zero.
  apply shift_zero_less_minus.
  exact Hab.
  intros.
  simpl.
  rewrite mult_commutes.
  rewrite cring_mult_zero.
  reflexivity.
  apply Diffble_I_n_const.
Qed.

Lemma L_diffble_all_n : forall (f : C_inf_ab c d Hcd) 
  (n : nat), Diffble_I_n Hab n (L_func f).
Proof.
  intros.
  apply L_diffble.
Qed.

(**
 * Define L as a member of the class C_inf_ab. 
 *)
Definition L (f : C_inf_ab c d Hcd) : (C_inf_ab a b Hab) := 
  Build_C_inf_ab a b Hab (L_func f) 
    (L_diffble_all_n f).

End Lfunct.

(**
 * The following section is vague at best. Various versions
 * of lemmas (e.g. continuity) are used. One of the main
 * improvements should be to make things more consistent.
 *)

Section Integration.

Require Import ProductMetric.
Require Import CRIR.
Require Import Integration.
Require Import Qmetric.
Require Import QposMinMax.

Variable a b : CR.
Hypothesis Hab : a [<] b.

(**
 * Define equality on a sub-metricspace (a sub-metricspace
 * is a collection of elements from a metric space restricted
 * to certain property).
 *)
Definition eqSubMS (X : MetricSpace) 
  (P : X -> Prop) (a : {X | P X}) 
  (b : {X | P X}) := (projT1 a) [=] (projT1 b).

(**
 * Because a metric space is a setoid, it follows 
 * automatically that a sub-metricspace is also a setoid.
 *)
Definition setoidSubMS (X : MetricSpace) 
  (P : X -> Prop) : Setoid.
intros X P.
assert (Reflexive (eqSubMS X P)).
unfold Reflexive, eqSubMS.
intro x.
reflexivity.
assert (Symmetric (eqSubMS X P)).
unfold Symmetric, eqSubMS.
intros x y H42.
symmetry.
exact H42.
assert (Transitive (eqSubMS X P)).
unfold Transitive, eqSubMS.
intros x y z H37 H42.
transitivity (projT1 y).
exact H37.
exact H42.
apply (@Build_Setoid {X | P X} (eqSubMS X P)
  (Build_Equivalence {X | P X} (eqSubMS X P) H H0 H1)).
Defined.

(**
 * The usual definition of a ball can be used in a 
 * sub-metricspace as well. 
 *)
Program Definition ballSubMS (X : MetricSpace)
  (P : X -> Prop) (x : Qpos)
  (a : {X | P X}) (b : {X | P X}) := 
  (@ball X x a b).

(**
 * The actual definition of sub-metricspace. 
 *
 * TODO: Perhaps P should be directly dicidable (although
 * we axiomatized anything in Prop to be decidable using
 * sq and unsq).
 *)
Definition SubMS (X : MetricSpace) (P : X -> Prop) : 
  MetricSpace.
intros X P.
apply (@Build_MetricSpace (setoidSubMS X P) 
  (ballSubMS X P)).
intros e1 e2 H x1 x2 H0 y1 y2 H1.
split.
intro H2.
unfold ballSubMS.
unfold ballSubMS in H2.
assert ((`x1) [=] (`x2)).
destruct x1.
destruct x2.
auto.
assert ((`y1) [=] (`y2)).
destruct y1.
destruct y2.
auto.
apply (ball_wd X H (`x1) (`x2) H3 (`y1) (`y2) H4).
exact H2.
intro H2.
unfold ballSubMS.
unfold ballSubMS in H2.
assert ((`x1) [=] (`x2)).
destruct x1.
destruct x2.
auto.
assert ((`y1) [=] (`y2)).
destruct y1.
destruct y2.
auto.
apply (ball_wd X H (`x1) (`x2) H3 (`y1) (`y2) H4).
exact H2.
assert (forall e : Qpos, Reflexive (ballSubMS X P e)).
intro e; unfold Reflexive.
intro x; unfold ballSubMS.
apply (msp_refl (msp X) e (`x)).
assert (forall e : Qpos, Symmetric (ballSubMS X P e)).
intro e; unfold Symmetric.
intros x y H0; unfold ballSubMS; unfold ballSubMS in H0.
apply (msp_sym (msp X) e (`x) (`y)).
exact H0.
assert (forall (e1 e2 : Qpos) (a b c : (setoidSubMS X P)),
  (ballSubMS X P e1 a b) -> (ballSubMS X P e2 b c) ->
  (ballSubMS X P ((e1 + e2)%Qpos) a c)).
intros e1 e2 a0 b0 c H1 H2.
unfold ballSubMS; unfold ballSubMS in H1; unfold ballSubMS in H2.
apply (msp_triangle (msp X) _ _ _ (`b0)).
exact H1.
exact H2.
assert (forall (e : Qpos) (a b : (setoidSubMS X P)),
  (forall d : Qpos, ballSubMS X P ((e + d)%Qpos) a b) ->
  ballSubMS X P e a b).
intros e a0 b0 H2.
unfold ballSubMS.
apply (msp_closed (msp X)).
exact H2.
assert (forall a b : (setoidSubMS X P), (forall e : Qpos,
  ballSubMS X P e a b) -> a [=] b).
intros a0 b0 H3.
destruct a0.
destruct b0.
simpl.
unfold eqSubMS.
simpl.
apply (msp_eq (msp X)).
unfold ballSubMS in H3.
simpl in H3.
exact H3.
apply (Build_is_MetricSpace (setoidSubMS X P)
  (ballSubMS X P) H H0 H1 H2 H3).
Defined.

(**
 * The abstract concept of nultiplication of a 
 * MetricSpace (as in IR x IR etc). This results in
 * a product space (which is again a metric space).
 *)
Fixpoint XpowM (X : MetricSpace) (m : nat)
  {struct m} : MetricSpace :=
match m with
| 0 => X    (* Should not be used *)
| 1 => X
| S n => ProductMS X (XpowM X n)
end.

(**
 * If an element is known to be inside a sub-metricspace, it
 * can also be typed as an element from the original metric
 * space.
 *)
Definition unres (m : nat) (P : CR -> Prop) 
  (X : XpowM (SubMS CR P) m) : XpowM CR m.
intros m P x.
induction m.
simpl; simpl in x.
inversion x.
exact x0.
destruct m.
simpl.
simpl in x.
inversion x.
exact x0.
simpl.
split.
simpl in x.
inversion x.
inversion X.
exact x0.
apply IHm.
simpl in x.
inversion x.
exact X0.
Defined.

(**
 * The definition of continuity according to the book of
 * Bishop. Please note that this definition does not use
 * the continuity-definitions from CoRN/ftc. 
 *
 * TODO: Find a way to make continuity and differentiability
 * as consistent as possible throughout the proof.
 *)
Definition Bcont (m : nat) (X : MetricSpace) 
  (f : (XpowM CR m) -> X) := forall (a b : CR)
  (Hab : a [<] b) (g : (XpowM (SubMS CR 
  (fun x => sq (a [<] x and x [<] b))) m) -> X),
  (forall x : (XpowM (SubMS CR 
    (fun x => sq (a [<] x and x [<] b))) m), 
    (f (unres m (fun x => 
      sq (a [<] x and x [<] b)) x) [=] g x)) ->
  {m | is_UniformlyContinuousFunction g m}.

(**
 * Application of a pair of functions to an element from a
 * metric space resulting in an element of a product space.
 *)
Definition pairFG (m : nat) (X : MetricSpace) (Y : MetricSpace)
  (f : (XpowM CR m) -> X) (g : (XpowM CR m) -> Y) :  
  (XpowM CR m) -> ProductMS X Y.
intros m X Y f g x.
unfold ProductMS.
simpl; split.
apply f.
exact x.
apply g.
exact x.
Defined.

(**
 * This lemma corresponds to lemma 20 in the PDF as sent to
 * me on january 11th. It states that Bishop-continuity of
 * individual functions can be continued to pairs of functions.
 *)
Lemma lem20 : forall (m : nat) (X : MetricSpace) (Y : MetricSpace)
  (f : (XpowM CR m) -> X) (g : (XpowM CR m) -> Y)
  (Hf : Bcont m X f) (Hg : Bcont m Y g),
  Bcont m (ProductMS X Y) (pairFG m X Y f g).
Proof.
  intros m X Y f g Hf Hg.
  unfold Bcont.
  intros a0 b0 Ha0b0 g0 Hg0.
  unfold Bcont in Hf.
  assert ({f' : XpowM (SubMS CR
    (fun x : CR => sq (cof_less a0 x and cof_less x b0))) m -> X |
    (forall x : XpowM (SubMS CR (fun x : CR => sq (cof_less a0 x and cof_less x b0))) m,
      f (unres m (fun x0 : CR => sq (cof_less a0 x0 and cof_less x0 b0)) x) [=] f' x)}).
  exists (fun x => fst (g0 x)).
  intro x.
  unfold pairFG in Hg0.
  destruct (Hg0 x).
  rewrite <- H.
  simpl; reflexivity.
  inversion X0.
  elim (Hf a0 b0 Ha0b0 x H).
  intros mu1 H0.
  unfold Bcont in Hg.
  assert ({g' : XpowM (SubMS CR
    (fun x : CR => sq (cof_less a0 x and cof_less x b0))) m -> Y |
    (forall x : XpowM (SubMS CR (fun x : CR => sq (cof_less a0 x and cof_less x b0))) m,
      g (unres m (fun x0 : CR => sq (cof_less a0 x0 and cof_less x0 b0)) x) [=] g' x)}).
  exists (fun x => snd (g0 x)).
  intro x0.
  unfold pairFG in Hg0.
  destruct (Hg0 x0).
  rewrite <- H2.
  simpl; reflexivity.
  inversion X1.
  elim (Hg a0 b0 Ha0b0 x0 H1).
  intros mu2 H2.
  exists (fun x : Qpos => 
    QposInf_min (mu1 x) (mu2 x)).
  unfold is_UniformlyContinuousFunction.
  intros e a1 b1 H3.
  unfold is_UniformlyContinuousFunction in H0, H2.
  assert (ball_ex (mu1 e) a1 b1).
  apply ball_ex_weak_le with 
    (QposInf_min (mu1 e) (mu2 e)).
  apply QposInf_min_lb_l.
  exact H3.
  assert (ball_ex (mu2 e) a1 b1).
  apply ball_ex_weak_le with
    (QposInf_min (mu1 e) (mu2 e)).
  apply QposInf_min_lb_r.
  exact H3.
  assert (ball e (x a1) (x b1)).
  apply H0.
  exact H4.
  assert (ball e (x0 a1) (x0 b1)).
  apply H2.
  exact H5.
  simpl; unfold prod_ball; split.
  destruct (Hg0 a1).
  rewrite <- H8.
  destruct (Hg0 b1).
  rewrite <- H10.
  simpl.
  rewrite H.
  rewrite H.
  exact H6.
  simpl.
  destruct (Hg0 a1).
  rewrite <- H9.
  destruct (Hg0 b1).
  rewrite <- H11.
  simpl.
  rewrite H1.
  rewrite H1.
  exact H7.
Qed.

(**
 * TODO: This should be formulated either directly in the
 * proof or in a more general way.
 *)
Definition betw01 (x : CR) : Prop :=
  Zero [<=] x and x [<=] One.

Require Import QMinMax.
Require Import iso_CReals.

(**
 * A quick definition to have the computational reals (CR)
 * represented as CR^1.
 *)
Definition CRasCRpow1 (c : CR) : XpowM CR 1.
intro c.
simpl.
simpl in c.
exact c.
Defined.

(**
 * A somewhat general definition of a subspace of 
 * the rationals. 
 *)
Definition QsubMS (a b : Q) := SubMS Q_as_MetricSpace
  (fun x : Q_as_MetricSpace => (a <= x)%Q and (x <= b)%Q).

(**
 * Any element in a subset of Q is - of course - an element
 * in Q. 
 *)
Definition QsubMSasQ (a b : Q) (m : QsubMS a b) : Q.
intros a0 b0 m.
inversion m.
exact x.
Defined.

(**
 * A 'flatten' function because apparently total functions
 * can be handled better by CoRN compared tot partial 
 * funtions. 
 *
 * flat_raw takes a function f from ([a,b] <intersect> Q) to
 * R and returns a function f':Q -> R according to the 
 * following diagram:
 *                              
 *                       ---(b)--------------   
 *                      /
 *                     /
 *                  -- 
 *                 /
 *   --------(a)--/
 *
 * That is: the result of f'(x) in x<a and x>b is equal to
 * f(a) and f(b) respectively. 
 *)
Definition flat_raw (a b : Q) (Hab : (a < b)%Q) 
  (f : (QsubMS a b) -> CR) (Hf : Bcont 1 CR f) := 
  (fun x : Q_as_MetricSpace => 
    match (Qlt_le_dec_fast a x) with 
    | left _ => match (Qlt_le_dec_fast x b) with
                | left _ => f (CRasCRpow1 (IRasCR (inj_Q IR x)))
                | right _ => f (CRasCRpow1 (IRasCR (inj_Q IR b)))
                end
    | right _ => f (CRasCRpow1 (IRasCR (inj_Q IR a)))
    end
  ).

(**
 * A proof that the 'flatten' operation indeed preserves
 * uniform continuity.
 *)
Lemma flat_prf : forall (a b : Qpos) (Hab : (a < b)%Q)
  (f : (XpowM CR 1) -> CR) (Hf : Bcont 1 CR f), 
  {m | is_UniformlyContinuousFunction 
   (flat_raw a b Hab f Hf) m}.
Proof.
  intros a0 b0 Ha0b0 f Hf.
  unfold Bcont in Hf.
  set (IRasCR (inj_Q IR a0)).
  set (IRasCR (inj_Q IR b0)).
  assert ({g : XpowM (SubMS CR
    (fun x : CR => sq (cof_less s x and cof_less x s0))) 1 -> CR |
    (forall x : XpowM (SubMS CR (fun x : CR => sq (cof_less s x and cof_less x s0))) 1,
      f (unres 1 (fun x0 : CR => sq (cof_less s x0 and cof_less x0 s0)) x) [=] g x)}).
  exists (fun x : XpowM (SubMS CR 
    (fun x : CR => sq (cof_less s x and cof_less x s0))) 1 =>
      f (unres 1 (fun x0 : CR => sq (cof_less s x0 and cof_less x0 s0)) x)).
  intro x; reflexivity.
  inversion X.
  assert (cof_less s s0).
  unfold s.
  unfold s0.
  Admitted.

(**
 * A 'flattened' function typed as a uniformly continuous 
 * space.
 *)
Definition flat (a b : Qpos) (Hab : (a < b)%Q)
  (f : (XpowM CR 1) -> CR) (Hf : Bcont 1 CR f) : 
  UniformlyContinuousSpace Q_as_MetricSpace CR.
intros a0 b0 Ha0b0 f Hf.
set (flat_prf a0 b0 Ha0b0 f Hf).
inversion s.
exact (Build_UniformlyContinuousFunction H).
Defined.


(**
 * The is a repeated attempt at the definition of the
 * function L (see above). The function L0 is again a
 * translation function. It transforms a function 
 * f : ([a,b] <intersect> Q) -> R to a function 
 * f' : ([c,d] <intersect> Q) -> R. 
 *
 * TODO: Finish or reconsider this proof.
 *)
Definition L0_def (a b c d : Q) (Hab : (a < b)%Q) (Hcd : (c < d)%Q)
  (f : (QsubMS a b) -> CR) : (QsubMS c d) -> CR.
intros a0 b0 c d Ha0b0 Hcd f x.
inversion x.
set (Qplus c (Qmult (Qminus d c) (Qdiv 
  (Qminus (QsubMSasQ c d x) a0) (Qminus b0 a0)))).
cut ((a0 <= q)%Q and (q <= b0)%Q).
intro Hq.
apply f.
simpl.
exists q.
exact Hq.
Admitted.

(** 
 * A new definition of L0 in terms of Q as a metric space.
 *
 * TODO: This proof (and the whole L0 construct, for that
 * matter) should be set up in a different way.
 *)
Definition L0_ext_def (a b c d : Q) (Hab : (a < b)%Q)
  (Hcd : (c < d)%Q) (f : (QsubMS a b) -> CR) :
  Q_as_MetricSpace -> CR.
intros a0 b0 c d Ha0b0 Hcd f x.
case (Qlt_le_dec_fast c x).
intro H.
case (Qlt_le_dec_fast x d).
intro H0.
apply (L0_def a0 b0 c d Ha0b0 Hcd f).
simpl.
exists x.
split.
auto with *.
auto with *.
intro H0.
apply (L0_def a0 b0 c d Ha0b0 Hcd f).
simpl.
exists d.
split.
auto with *.
auto with *.
intro H.
apply (L0_def a0 b0 c d Ha0b0 Hcd f).
simpl.
exists c.
split.
auto with *.
auto with *.
Defined.

(**
 * TODO: Lemma should be replaced/removed.
 *)
Lemma L0_ext_uc : forall (a b c d : Q) (f : (QsubMS a b) -> CR)
  (Hab : (a < b)%Q) (Hcd : (c < d)%Q),
  {m : Qpos -> QposInf | is_UniformlyContinuousFunction 
    (L0_ext_def a b c d Hab Hcd f) m}.
Admitted.

(**
 * TODO: Definition should be replaced/removed.
 *)
Definition L0 (a b c d : Q) (f : (QsubMS a b) -> CR)
  (Hab : (a < b)%Q) (Hcd : (c < d)%Q) : 
  UniformlyContinuousSpace Q_as_MetricSpace CR.
intros a0 b0 c d f Ha0b0 Hcd.
set (L0_ext_uc a0 b0 c d f Ha0b0 Hcd).
inversion s.
exact (Build_UniformlyContinuousFunction H).
Defined.

(**
 * Integration as a total function from Q to R. However, this
 * part of the proof probably has to be set up in a different
 * way (as I indicated before during our discussions).
 *)
Definition F (a b : Qpos) (Hab : (a < b)%Q)
  (f : (XpowM CR 1) -> CR) (Hf : Bcont 1 CR f) :=
  (fun x : Q_as_MetricSpace =>
    match (Qlt_le_dec_fast x (1%Q)) with 
    | left _ => IRasCR Zero
    | right _ => (Integrate01 (flat a b Hab f Hf))
    end
  ).
    
  
   


    