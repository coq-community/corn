Require Import Bernstein.
Require Import CRing_Homomorphisms.
Require Import COrdFields2.
Require Export Qordfield.
Require Import QMinMax.
Require Import CornTac.
Require Import Qauto.
Require Import Qmetric.
Require Import Qabs.
Require Import CRabs.
Require Import ModulusDerivative.
Require Import CRArith.

Set Implicit Arguments.

Opaque cpoly_cring.
Opaque cpoly_apply_fun.
Opaque polyconst.

Section MultivariatePolynomial.

(**
** Multivariable polynomails

Here we prove that multivariable polynomials over the rationals are uniformly continuous
on the unit hyperinterval.  Hence they can be lifted to apply to real numbers.
This allows real numbers to be used in polynomial expressions so that each variable
is only approximated once.
*)

Variable F : CRing.

(** Define the type of multivariable polynomials with [n] variables *)
Fixpoint MultivariatePolynomial (n:nat) : CRing :=
match n with
| O => F
| S n' => cpoly_cring (MultivariatePolynomial n')
end.

(** The constant multivariable polynomial *)
Fixpoint MVP_C_ (n:nat) : RingHom F (MultivariatePolynomial n) :=
match n return RingHom F (MultivariatePolynomial n) with
| O => RHid _
| S n' =>  RHcompose _ _ _ _C_ (MVP_C_ n')
end.

(** Apply a multivariable polynomial to a vector of input values *)
Fixpoint MVP_apply (n:nat) : MultivariatePolynomial n -> (vector F n) -> F :=
match n return MultivariatePolynomial n -> vector F n -> F with
| O => fun x _ => x
| (S n') => fun p v => (MVP_apply (p ! (MVP_C_ _ (Vhead _ _ v))) (Vtail _ _ v))
end.

End MultivariatePolynomial.

(* begin hide *)
Add Parametric Morphism F n : (@MVP_apply F n) with signature (@st_eq (MultivariatePolynomial F n)) ==> (@eq _) ==> (@st_eq _) as MVP_apply_wd.
Proof.
 induction n; intros x y Hxy z.
  assumption.
 simpl.
 apply IHn.
 rewrite -> Hxy.
 reflexivity.
Qed.
(* end hide *)

(* Multivariable polynomial application by a constant set of inputs is a ring homomorphism. *)

Lemma zero_MVP_apply : forall F n v, MVP_apply F (Zero:MultivariatePolynomial F n) v[=]Zero.
Proof.
 induction v.
  reflexivity.
 simpl.
 rewrite <- IHv.
 reflexivity.
Qed.

Lemma one_MVP_apply : forall F n v, MVP_apply F (One:MultivariatePolynomial F n) v[=]One.
Proof.
 induction v.
  reflexivity.
 simpl.
 rewrite <- IHv.
 rewrite -> one_apply.
 reflexivity.
Qed.

Lemma C_MVP_apply : forall F n q v, MVP_apply F (MVP_C_ F n q) v[=]q.
Proof.
 induction v.
  reflexivity.
 simpl.
 rewrite -> c_apply.
 assumption.
Qed.

Lemma MVP_plus_apply: forall F n (p q : MultivariatePolynomial F n) v,
  MVP_apply F (p[+]q) v [=] MVP_apply F p v[+]MVP_apply F q v.
Proof.
 induction v.
  reflexivity.
 simpl.
 rewrite -> plus_apply.
 apply IHv.
Qed.

Lemma MVP_mult_apply: forall F n (p q : MultivariatePolynomial F n) v,
  MVP_apply F (p[*]q) v [=] MVP_apply F p v[*]MVP_apply F q v.
Proof.
 induction v.
  reflexivity.
 simpl.
 rewrite -> mult_apply.
 apply IHv.
Qed.

Lemma MVP_c_mult_apply: forall F n (p : MultivariatePolynomial F n) c v,
  MVP_apply F (MVP_C_ _ _ c[*]p) v[=]c[*]MVP_apply F p v.
Proof.
 induction v.
  reflexivity.
 simpl.
 rewrite <- IHv.
 rewrite -> c_mult_apply.
 reflexivity.
Qed.

Lemma MVP_apply_hom_strext : forall (F:CRing) n (v:vector F n), fun_strext (fun (p:MultivariatePolynomial F n) => MVP_apply _ p v).
Proof.
 induction n.
  intros v x y.
  simpl.
  auto with *.
 intros v x y H.
 simpl in H.
 destruct (csbf_strext _ _ _ _ _ _ _ _ (IHn _ _ _ H)) as [H0 | H0].
  assumption.
 elim (ap_irreflexive _ _ H0).
Defined.

Definition MVP_apply_hom_csf (F:CRing) n (v:vector F n) :=
Build_CSetoid_fun _ _ _ (MVP_apply_hom_strext F v).

Definition MVP_apply_hom (F:CRing) n (v:vector F n) : RingHom (MultivariatePolynomial F n) F.
Proof.
 intros F n v.
 exists (MVP_apply_hom_csf F v).
   intros x y; apply: MVP_plus_apply.
  intros x y; apply: MVP_mult_apply.
 apply: one_MVP_apply.
Defined.

(** [MVP_map] applies a ring homomorphism to the coefficents of a multivariable polynomial *)
Fixpoint MVP_map R S (f:RingHom R S) (n:nat) : RingHom (MultivariatePolynomial R n) (MultivariatePolynomial S n) :=
match n return RingHom (MultivariatePolynomial R n) (MultivariatePolynomial S n) with
| O => f
| (S n') => cpoly_map (MVP_map f n')
end.

Lemma MVP_map_C_ : forall R S (f:RingHom R S) n c,
 MVP_map f n (MVP_C_ _ _ c)[=]MVP_C_ _ _ (f c).
Proof.
 induction n.
  intros c; reflexivity.
 intros c.
 simpl.
 change (cpoly_map (MVP_map f n) (_C_ (MVP_C_ R n c))[=]_C_ (MVP_C_ S n (f c))).
 rewrite -> cpoly_map_C.
 rewrite -> IHn.
 reflexivity.
Qed.

(* In practice we use the Bernstein coeffecients to bound the polynomials *)
(** Some upper bound on the polynomial on [0,1] *)
Fixpoint MVP_upperBound (n:nat) : MultivariatePolynomial Q_as_CRing n -> Q :=
match n return MultivariatePolynomial Q_as_CRing n -> Q with
| O => fun x => x
| (S n') => fun p => let (m,b) := BernsteinCoefficents (MVP_C_ Q_as_CRing n') p
                      in vector_rec _ (fun _ _ => Q) 0%Q
                         (fun c _ _ rec => Qmax (MVP_upperBound n' c) rec) m b
end.

(** Some lower bound on the polynomial on [0,1] *)
Fixpoint MVP_lowerBound (n:nat) : MultivariatePolynomial Q_as_CRing n -> Q :=
match n return MultivariatePolynomial Q_as_CRing n -> Q with
| O => fun x => x
| (S n') => fun p => let (m,b) := BernsteinCoefficents (MVP_C_ Q_as_CRing n') p
                      in vector_rec _ (fun _ _ => Q) 0%Q
                         (fun c _ _ rec => Qmin (MVP_lowerBound n' c) rec) m b
end.

Open Local Scope Q_scope.

(** Definition of the unit hyperinterval of n dimensions *)
Fixpoint UnitHyperInterval (n:nat) (v:vector Q n) : Prop :=
match v with
| Vnil => True
| Vcons a _ v' => 0 <= a <= 1 /\ UnitHyperInterval v'
end.

(* begin hide *)
Lemma BernsteinApplyRingHom : forall R F (eta: RingHom R F) n i (H:(i <= n)%nat) a,
 (Bernstein F H) ! (eta a)[=](eta (Bernstein R H) ! a).
Proof.
 induction n.
  simpl.
  intros _ _ a.
  do 2 rewrite -> one_apply.
  auto with *.
 intros [|i] H a; simpl;[|destruct (le_lt_eq_dec (S i) (S n) H)]; autorewrite with apply ringHomPush;
   repeat rewrite -> IHn; reflexivity.
Qed.

Lemma MVP_BernsteinNonNeg : forall m n i (H:(i <= n)%nat) v (a:Q), 0 <= a -> a <= 1 ->
 0 <= @MVP_apply Q_as_CRing m ((Bernstein _ H)!(MVP_C_ _ _ a)) v.
Proof.
 intros m n i H v a Ha0 Ha1.
 induction v.
  apply: BernsteinNonNeg; auto.
 simpl.
 replace RHS with (MVP_apply Q_as_CRing (Bernstein _ H) ! (MVP_C_ Q_as_CRing n0 a) v).
  apply IHv.
 apply MVP_apply_wd;try reflexivity.
 rewrite -> BernsteinApplyRingHom.
 auto with *.
Qed.
(* end hide *)

(** Return the ith entry of a vector *)
Fixpoint Vector_ix A (n i:nat) (H:(i < n)%nat) (v:vector A n) : A :=
match v in vector _ m return (i < m)%nat -> A with
| Vnil => fun p => False_rect _ (lt_n_O _ p)
| Vcons c n' v' => fun _ => match lt_le_dec i n' with
                            | left p => Vector_ix p v'
                            | right _ => c
                            end
end H.

(** The upper and lower bounds are correct. *)
Lemma MVP_upperBound_correct : forall n p v, UnitHyperInterval v -> MVP_apply _ p v[<=]MVP_upperBound n p.
Proof.
 induction n; intros p v H.
  apply Qle_refl.
 revert p H.
 dependent inversion v.
 clear H0.
 intros p [[Ha0 Ha1] Hv].
 stepl (@MVP_apply Q_as_CRing (S n) (let (n0, b) := BernsteinCoefficents (MVP_C_ Q_as_CRing n) p in
   evalBernsteinBasis (MultivariatePolynomial Q_as_CRing n) b) (@Vcons Q a n v0));
     [|apply MVP_apply_wd;[apply evalBernsteinCoefficents|reflexivity]].
 simpl (MVP_upperBound (S n) p).
 destruct (BernsteinCoefficents (MVP_C_ Q_as_CRing n) p) as [m b].
 apply Qle_trans with (vector_rec (MultivariatePolynomial Q_as_CRing n)
   (fun (n1 : nat) (_ : vector (MultivariatePolynomial Q_as_CRing n) n1) => Q) 0
     (fun (c : MultivariatePolynomial Q_as_CRing n) (n1 : nat)
       (_ : vector (MultivariatePolynomial Q_as_CRing n) n1) (rec : Q) =>
         Qmax (MVP_apply _ c v0) rec) m b).
  clear IHn Hv.
  destruct m as [|m].
   rewrite (V0_eq _ b).
   unfold evalBernsteinBasis.
   simpl.
   rewrite -> zero_MVP_apply.
   apply Qle_refl.
  unfold evalBernsteinBasis.
  match goal with |- (?A <= ?B) => set (L:=A); set (R:=B) end.
  change (L[<=]R).
  rstepr (R[*]One).
  rewrite <- (@one_MVP_apply Q_as_CRing _ (Vcons a v0)).
  stepr (R[*](@MVP_apply Q_as_CRing (S n) (@Sumx (cpoly_cring _) _ (fun i H => Bernstein _ (lt_n_Sm_le i m (lt_le_trans _ _ _ H (le_refl _))))) (Vcons a v0))).
   fold (MultivariatePolynomial Q_as_CRing n).
   unfold L, R; clear L R.
   generalize (le_refl (S m)).
   revert b.
   generalize (S m) at 1 2 5 6 7 8 9.
   induction b; intros l.
    simpl.
    rewrite -> zero_MVP_apply.
    apply Qle_refl.
   simpl (vector_rec (MultivariatePolynomial Q_as_CRing n)
     (fun (n2 : nat) (_ : vector (MultivariatePolynomial Q_as_CRing n) n2) => Q) 0
       (fun (c : MultivariatePolynomial Q_as_CRing n) (n2 : nat)
         (_ : vector (MultivariatePolynomial Q_as_CRing n) n2) (rec : Q) =>
           Qmax (MVP_apply Q_as_CRing c v0) rec) (S n1)
             (Vcons a0 b)).
   simpl (evalBernsteinBasisH (MultivariatePolynomial Q_as_CRing n)
     (@Vcons (MultivariatePolynomial Q_as_CRing n) a0 n1 b) l).
   simpl (Sumx (fun (i : nat) (H : (i < S n1)%nat) => Bernstein (MultivariatePolynomial Q_as_CRing n)
     (lt_n_Sm_le i m (lt_le_trans i (S n1) (S m) H l)))).
   do 2 rewrite -> MVP_plus_apply.
   rewrite ->  (Qplus_comm (@MVP_apply Q_as_CRing (S n) (Sumx (fun (i : nat) (l0 : (i < n1)%nat) =>
     Bernstein (MultivariatePolynomial Q_as_CRing n)
       (lt_n_Sm_le i m (lt_le_trans i (S n1) (S m) (lt_S i n1 l0) l)))) (@Vcons Q a n v0))).
   rewrite -> Qmult_comm.
   rewrite -> Qmult_plus_distr_l.
   apply Qplus_le_compat; rewrite -> Qmult_comm; rewrite -> Qmax_mult_pos_distr_l.
      replace LHS with (MVP_apply Q_as_CRing a0 v0 * @MVP_apply Q_as_CRing (S n)
        (Bernstein (MultivariatePolynomial Q_as_CRing n)
          (lt_n_Sm_le n1 m (lt_le_trans n1 (S n1) (S m) (lt_n_Sn n1) l))) (Vcons a v0)).
       apply Qmax_ub_l.
      simpl.
      rewrite <- (MVP_mult_apply Q_as_CRing).
      apply: MVP_apply_wd; try reflexivity.
      replace (lt_n_Sm_le n1 m (lt_le_trans n1 (S n1) (S m) (lt_n_Sn n1) l))
        with (le_S_n n1 m l) by apply le_irrelevent.
      apply c_mult_apply.
     apply MVP_BernsteinNonNeg; auto.
    eapply Qle_trans;[|apply Qmax_ub_r].
    set (R:=vector_rec (MultivariatePolynomial Q_as_CRing n)
      (fun (n2 : nat) (_ : vector (MultivariatePolynomial Q_as_CRing n) n2) => Q) 0
        (fun (c : MultivariatePolynomial Q_as_CRing n) (n2 : nat)
          (_ : vector (MultivariatePolynomial Q_as_CRing n) n2) (rec : Q) =>
            Qmax (MVP_apply Q_as_CRing c v0) rec) n1 b) in *.
    replace RHS with (R*@MVP_apply Q_as_CRing (S n) (Sumx (fun (i : nat) (l0 : (i < n1)%nat) =>
      Bernstein (MultivariatePolynomial Q_as_CRing n)
        (lt_n_Sm_le i m (lt_le_trans i n1 (S m) l0 (le_Sn_le _ _ l))))) (Vcons a v0)).
     apply IHb.
    apply: mult_wdr.
    apply MVP_apply_wd; try reflexivity.
    apply Sumx_wd.
    intros i H.
    replace (lt_n_Sm_le i m (lt_le_trans i (S n1) (S m) (lt_S i n1 H) l))
      with (lt_n_Sm_le i m (lt_le_trans i n1 (S m) H (le_Sn_le n1 (S m) l))) by apply le_irrelevent.
    reflexivity.
   clear - Ha0 Ha1.
   induction n1.
    rewrite -> zero_MVP_apply.
    auto with *.
   simpl (Sumx (fun (i : nat) (l0 : (i < S n1)%nat) => Bernstein (MultivariatePolynomial Q_as_CRing n)
     (lt_n_Sm_le i m (lt_le_trans i (S (S n1)) (S m) (lt_S i (S n1) l0) l)))).
   rewrite -> MVP_plus_apply.
   apply: plus_resp_nonneg.
    stepr (@MVP_apply Q_as_CRing (S n) (Sumx (fun (i : nat) (l0 : (i < n1)%nat) =>
      Bernstein (MultivariatePolynomial Q_as_CRing n)
        (lt_n_Sm_le i m (lt_le_trans i (S n1) (S m) (lt_S i n1 l0) (le_Sn_le _ _ l))))) (Vcons a v0)).
     apply IHn1.
    apply MVP_apply_wd; try reflexivity.
    apply Sumx_wd.
    intros i H.
    replace (lt_n_Sm_le i m (lt_le_trans i (S n1) (S m) (lt_S i n1 H) (le_Sn_le (S n1) (S m) l)))
      with (lt_n_Sm_le i m (lt_le_trans i (S (S n1)) (S m) (lt_S i (S n1) (lt_S i n1 H)) l))
        by apply le_irrelevent.
    reflexivity.
   apply MVP_BernsteinNonNeg; auto with *.
  apply mult_wdr.
  apply MVP_apply_wd; try reflexivity.
  simpl (MultivariatePolynomial Q_as_CRing (S n)).
  rewrite <- (fun X => partitionOfUnity X m).
  apply Sumx_wd.
  intros i H.
  replace (lt_n_Sm_le i m (lt_le_trans i (S m) (S m) H (le_refl (S m))))
    with (lt_n_Sm_le i m H) by apply le_irrelevent.
  reflexivity.
 clear - IHn Hv.
 induction b.
  auto with *.
 apply Qmax_le_compat.
  apply IHn; apply Hv.
 auto.
Qed.

Lemma MVP_lowerBound_correct : forall n p v, UnitHyperInterval v -> MVP_lowerBound n p[<=]MVP_apply _ p v.
Proof.
 induction n; intros p v H.
  apply Qle_refl.
 revert p H.
 dependent inversion v.
 clear H0.
 intros p [[Ha0 Ha1] Hv].
 stepr (@MVP_apply Q_as_CRing (S n) (let (n0, b) := BernsteinCoefficents (MVP_C_ Q_as_CRing n) p in
   evalBernsteinBasis (MultivariatePolynomial Q_as_CRing n) b) (Vcons a v0));
     [|apply MVP_apply_wd;[apply evalBernsteinCoefficents|reflexivity]].
 simpl (MVP_lowerBound (S n) p).
 destruct (BernsteinCoefficents (MVP_C_ Q_as_CRing n) p) as [m b].
 apply Qle_trans with (vector_rec (MultivariatePolynomial Q_as_CRing n)
   (fun (n1 : nat) (_ : vector (MultivariatePolynomial Q_as_CRing n) n1) => Q) 0
     (fun (c : MultivariatePolynomial Q_as_CRing n) (n1 : nat)
       (_ : vector (MultivariatePolynomial Q_as_CRing n) n1) (rec : Q) =>
         Qmin (MVP_apply _ c v0) rec) m b).
  clear - IHn Hv.
  induction b.
   auto with *.
  apply Qmin_le_compat.
   apply IHn; apply Hv.
  auto.
 clear IHn Hv.
 destruct m as [|m].
  rewrite (V0_eq _ b).
  unfold evalBernsteinBasis.
  simpl.
  rewrite -> zero_MVP_apply.
  apply Qle_refl.
 unfold evalBernsteinBasis.
 match goal with |- (?A <= ?B) => set (R:=A); set (L:=B) end.
 change (R[<=]L).
 rstepl (R[*]One).
 rewrite <- (@one_MVP_apply Q_as_CRing _ (Vcons a v0)).
 stepl (R[*](@MVP_apply Q_as_CRing (S n) (@Sumx (cpoly_cring _) _ (fun i H => Bernstein _ (lt_n_Sm_le i m (lt_le_trans _ _ _ H (le_refl _))))) (Vcons a v0))).
  fold (MultivariatePolynomial Q_as_CRing n).
  unfold L, R; clear L R.
  generalize (le_refl (S m)).
  revert b.
  generalize (S m) at 1 2 4 5 6 7 10.
  induction b; intros l.
   simpl.
   rewrite -> zero_MVP_apply.
   apply Qle_refl.
  simpl (vector_rec (MultivariatePolynomial Q_as_CRing n)
    (fun (n2 : nat) (_ : vector (MultivariatePolynomial Q_as_CRing n) n2) => Q) 0
      (fun (c : MultivariatePolynomial Q_as_CRing n) (n2 : nat)
        (_ : vector (MultivariatePolynomial Q_as_CRing n) n2) (rec : Q) =>
          Qmin (MVP_apply Q_as_CRing c v0) rec) (S n1)
            (Vcons a0 b)).
  simpl (evalBernsteinBasisH (MultivariatePolynomial Q_as_CRing n)
    (Vcons a0 b) l).
  simpl (Sumx (fun (i : nat) (H : (i < S n1)%nat) => Bernstein (MultivariatePolynomial Q_as_CRing n)
    (lt_n_Sm_le i m (lt_le_trans i (S n1) (S m) H l)))).
  do 2 rewrite -> MVP_plus_apply.
  rewrite ->  (Qplus_comm (@MVP_apply Q_as_CRing (S n) (Sumx (fun (i : nat) (l0 : (i < n1)%nat) =>
    Bernstein (MultivariatePolynomial Q_as_CRing n)
      (lt_n_Sm_le i m (lt_le_trans i (S n1) (S m) (lt_S i n1 l0) l)))) (Vcons a v0))).
  rewrite ->  Qmult_comm.
  rewrite -> Qmult_plus_distr_l.
  apply Qplus_le_compat; rewrite -> Qmult_comm; rewrite -> Qmin_mult_pos_distr_l.
     replace RHS with (MVP_apply Q_as_CRing a0 v0 * @MVP_apply Q_as_CRing (S n)
       (Bernstein (MultivariatePolynomial Q_as_CRing n)
         (lt_n_Sm_le n1 m (lt_le_trans n1 (S n1) (S m) (lt_n_Sn n1) l))) (Vcons a v0)).
      apply Qmin_lb_l.
     simpl.
     rewrite <- (MVP_mult_apply Q_as_CRing).
     apply: MVP_apply_wd; try reflexivity.
     replace (lt_n_Sm_le n1 m (lt_le_trans n1 (S n1) (S m) (lt_n_Sn n1) l))
       with (le_S_n n1 m l) by apply le_irrelevent.
     apply c_mult_apply.
    apply MVP_BernsteinNonNeg; auto.
   eapply Qle_trans;[apply Qmin_lb_r|].
   set (R:=vector_rec (MultivariatePolynomial Q_as_CRing n)
     (fun (n2 : nat) (_ : vector (MultivariatePolynomial Q_as_CRing n) n2) => Q) 0
       (fun (c : MultivariatePolynomial Q_as_CRing n) (n2 : nat)
         (_ : vector (MultivariatePolynomial Q_as_CRing n) n2) (rec : Q) =>
           Qmin (MVP_apply Q_as_CRing c v0) rec) n1 b) in *.
   replace LHS with (R*@MVP_apply Q_as_CRing (S n) (Sumx (fun (i : nat) (l0 : (i < n1)%nat) =>
     Bernstein (MultivariatePolynomial Q_as_CRing n)
       (lt_n_Sm_le i m (lt_le_trans i n1 (S m) l0 (le_Sn_le _ _ l))))) (Vcons a v0)).
    apply IHb.
   apply: mult_wdr.
   apply MVP_apply_wd; try reflexivity.
   apply Sumx_wd.
   intros i H.
   replace (lt_n_Sm_le i m (lt_le_trans i (S n1) (S m) (lt_S i n1 H) l))
     with (lt_n_Sm_le i m (lt_le_trans i n1 (S m) H (le_Sn_le n1 (S m) l))) by apply le_irrelevent.
   reflexivity.
  clear - Ha0 Ha1.
  induction n1.
   rewrite -> zero_MVP_apply.
   auto with *.
  simpl (Sumx (fun (i : nat) (l0 : (i < S n1)%nat) => Bernstein (MultivariatePolynomial Q_as_CRing n)
    (lt_n_Sm_le i m (lt_le_trans i (S (S n1)) (S m) (lt_S i (S n1) l0) l)))).
  rewrite -> MVP_plus_apply.
  apply: plus_resp_nonneg.
   stepr (@MVP_apply Q_as_CRing (S n) (Sumx (fun (i : nat) (l0 : (i < n1)%nat) =>
     Bernstein (MultivariatePolynomial Q_as_CRing n)
       (lt_n_Sm_le i m (lt_le_trans i (S n1) (S m) (lt_S i n1 l0) (le_Sn_le _ _ l))))) (Vcons a v0)).
    apply IHn1.
   apply MVP_apply_wd; try reflexivity.
   apply Sumx_wd.
   intros i H.
   replace (lt_n_Sm_le i m (lt_le_trans i (S n1) (S m) (lt_S i n1 H) (le_Sn_le (S n1) (S m) l)))
     with (lt_n_Sm_le i m (lt_le_trans i (S (S n1)) (S m) (lt_S i (S n1) (lt_S i n1 H)) l))
       by apply le_irrelevent.
   reflexivity.
  apply MVP_BernsteinNonNeg; auto with *.
 apply mult_wdr.
 apply MVP_apply_wd; try reflexivity.
 simpl (MultivariatePolynomial Q_as_CRing (S n)).
 rewrite <- (fun X => partitionOfUnity X m).
 apply Sumx_wd.
 intros i H.
 replace (lt_n_Sm_le i m (lt_le_trans i (S m) (S m) H (le_refl (S m))))
   with (lt_n_Sm_le i m H) by apply le_irrelevent.
 reflexivity.
Qed.

Open Local Scope Q_scope.

(** Use the upper and lower bounds of the derivative of a polynomial to
define its modulus of continuity. *)
Definition MVP_apply_modulus n (p:MultivariatePolynomial Q_as_CRing (S n)) :=
let p' := (_D_ p) in
Qscale_modulus (Qmax (MVP_upperBound (S n) p') (-(MVP_lowerBound (S n) p'))).

Lemma MVP_apply_modulus_correct : forall n (p:MultivariatePolynomial Q_as_CRing (S n)) x y e,
 (0 <= x) -> (x <= 1) -> (0 <= y) -> (y <= 1) ->
 ball_ex (MVP_apply_modulus p e) x y ->
 forall (v:vector Q n), UnitHyperInterval v -> ball e (MVP_apply _ p (Vcons x v):Q) (MVP_apply _ p (Vcons y v)).
Proof.
 intros n p x y e Hx0 Hx1 Hy0 Hy1 Hxy v Hv.
 assert (Hx : (Qmax 0 (Qmin 1 x))==x).
  rewrite ->  Qle_min_r in Hx1.
  rewrite -> Hx1.
  rewrite ->  Qle_max_r in Hx0.
  rewrite -> Hx0.
  reflexivity.
 assert (Hy : (Qmax 0 (Qmin 1 y))==y).
  rewrite -> Qle_min_r in Hy1.
  rewrite -> Hy1.
  rewrite ->  Qle_max_r in Hy0.
  rewrite -> Hy0.
  reflexivity.
 simpl.
 rewrite <- Hx.
 rewrite <- Hy.
 unfold MVP_apply_modulus in Hxy.
 set (c:=(Qmax (MVP_upperBound (S n) (_D_ p)) (- MVP_lowerBound (S n) (_D_ p)))) in *.
 set (fp:=cpoly_map (RHcompose _ _ _ (inj_Q_hom IR) (MVP_apply_hom _ v)) p).
 apply (fun A B e => is_UniformlyContinuousD_Q (Some 0) (Some 1) refl_equal (FPoly _ fp) (FPoly _ (_D_ fp)) (Derivative_poly _ _ _)
   (fun x => (MVP_apply _ p (Vcons x v))) A c B e x y); try assumption.
  unfold fp.
  simpl.
  intros q _ _.
  clear - p.
  change (inj_Q_hom IR (MVP_apply_hom Q_as_CRing v p ! (MVP_C_ Q_as_CRing n q))[=]
    (cpoly_map (RHcompose (MultivariatePolynomial Q_as_CRing n) Q_as_CRing IR
      (inj_Q_hom IR) (MVP_apply_hom Q_as_CRing v)) p) ! (inj_Q_hom IR q)).
  rewrite -> cpoly_map_compose.
  rewrite <- cpoly_map_apply.
  apply inj_Q_wd.
  rewrite -> cpoly_map_apply.
  apply csbf_wd; try reflexivity.
  apply: C_MVP_apply.
 simpl.
 clear - c Hv.
 intros x _ [H0x Hx1].
 change (AbsIR (_D_ (cpoly_map (RHcompose (MultivariatePolynomial Q_as_CRing n) Q_as_CRing IR
   (inj_Q_hom IR) (MVP_apply_hom Q_as_CRing v)) p)) ! (inj_Q_hom IR x)[<=] inj_Q IR c).
 rewrite <- cpoly_map_diff.
 rewrite -> cpoly_map_compose.
 rewrite <- cpoly_map_apply.
 change (AbsIR (inj_Q IR (cpoly_map (MVP_apply_hom Q_as_CRing v) (_D_ p)) ! x)[<=]inj_Q IR c).
 rewrite -> AbsIR_Qabs.
 apply inj_Q_leEq.
 assert (Hx: 0 <= x <= 1).
  split; apply (leEq_inj_Q IR).
   rewrite -> inj_Q_Zero.
   rstepl (Zero[/]Zero[+]One[//]den_is_nonzero IR 0); auto.
  rewrite -> inj_Q_One.
  rstepr (One[/]Zero[+]One[//]den_is_nonzero IR 1); auto.
 setoid_replace ((cpoly_map (MVP_apply_hom Q_as_CRing v) (_D_ p)) ! x)
   with (@MVP_apply Q_as_CRing (S n) (_D_ p) (Vcons x v)).
  apply Qabs_case; intros H.
   eapply Qle_trans;[|apply Qmax_ub_l].
   apply MVP_upperBound_correct.
   split; auto.
  eapply Qle_trans;[|apply Qmax_ub_r].
  apply Qopp_le_compat.
  apply MVP_lowerBound_correct.
  split; auto.
 generalize (_D_ p).
 intros s; clear -s.
 simpl.
 change ((cpoly_map_fun (MultivariatePolynomial Q_as_CRing n) Q_as_CRing
   (MVP_apply_hom Q_as_CRing v) s) ! x == MVP_apply_hom Q_as_CRing v (s ! (MVP_C_ Q_as_CRing n x))).
 rewrite -> cpoly_map_apply.
 simpl.
 rewrite -> C_MVP_apply.
 reflexivity.
Qed.

Open Local Scope uc_scope.

(** Clamp a value to the unit interval *)
Definition Qclamp01 := QboundBelow_uc (0) ∘ QboundAbove_uc 1.

Lemma Qclamp01_clamped : forall x, 0 <= Qclamp01 x <= 1.
Proof.
 intros x.
 unfold Qclamp01.
 split; simpl.
  apply Qmax_ub_l.
 rewrite -> Qmax_min_distr_r.
 apply Qmin_lb_l.
Qed.

Lemma Qclamp01_le : forall x y, x <= y -> Qclamp01 x <= Qclamp01 y.
Proof.
 intros x y H.
 simpl.
 apply Qmax_le_compat; auto with *.
 apply Qmin_le_compat; auto with *.
Qed.

Lemma Qclamp01_close : forall e x y, Qabs (x-y) <= e -> Qabs (Qclamp01 x - Qclamp01 y) <= e.
Proof.
 intros e.
 cut (forall x y : Q, y <= x -> x - y <= e -> Qclamp01 x - Qclamp01 y <= e).
  intros H x y.
  destruct (Qle_total x y).
   rewrite -> Qabs_neg.
    intros He.
    rewrite -> Qabs_neg.
     replace LHS with (Qclamp01 y - Qclamp01 x) by simpl; ring.
     apply H; auto.
     replace LHS with (- (x-y)) by simpl; ring.
     auto.
    apply (shift_minus_leEq Q_as_COrdField).
    stepr (Qclamp01 y); [| by (simpl; ring)].
    apply Qclamp01_le.
    auto.
   apply (shift_minus_leEq Q_as_COrdField).
   stepr y; [| by (simpl; ring)].
   auto.
  rewrite -> Qabs_pos.
   intros He.
   rewrite -> Qabs_pos.
    apply H; auto.
   apply: shift_zero_leEq_minus.
   apply Qclamp01_le.
   auto.
  apply: shift_zero_leEq_minus.
  auto.
 intros x y Hxy He.
 simpl.
 apply (Qmin_case 1 y).
  intros Hy.
  assert (Hx:=Qle_trans _ _ _ Hy Hxy).
  rewrite ->  Qle_min_l in Hx.
  rewrite -> Hx.
  replace LHS with  0 by simpl; ring.
  eapply Qle_trans;[|apply He].
  apply: shift_zero_leEq_minus; auto.
 apply (Qmin_case 1 x).
  intros Hx Hy.
  eapply Qle_trans;[|apply He].
  apply Qplus_le_compat; auto.
  apply Qopp_le_compat.
  apply Qmax_ub_r.
 intros _ _.
 apply (Qmax_case 0 x); intros Hx.
  assert (Hy:=Qle_trans _ _ _ Hxy Hx).
  rewrite ->  Qle_max_l in Hy.
  rewrite -> Hy.
  eapply Qle_trans;[|apply He].
  apply: shift_zero_leEq_minus; auto.
 apply (Qmax_case 0 y); intros Hy.
  eapply Qle_trans;[|apply He].
  apply Qplus_le_compat; auto with *.
 auto.
Qed.

Require Import RSetoid.

(** Definition of a setoid function type of n parameters *)
Fixpoint n_Function X Y (n:nat) :=
match n with
|O => Y
|S n' => extSetoid X (n_Function X Y n')
end.

(** Definition of a uniformly continuous function type of n parameters *)
Fixpoint n_UniformlyContinuousFunction (X Y:MetricSpace) (n:nat) :=
match n with
|O => Y
|S n' => X --> (n_UniformlyContinuousFunction X Y n')
end.

(** [MVP_uc_sig] is a recursive type definition that is needed for part of the definition of
 of a multivariable polynomial as a uniformly continuous function. *)
Fixpoint MVP_uc_sig (n:nat) :MultivariatePolynomial Q_as_CRing n -> n_UniformlyContinuousFunction Q_as_MetricSpace Q_as_MetricSpace n -> Type :=
match n return MultivariatePolynomial Q_as_CRing n -> n_UniformlyContinuousFunction Q_as_MetricSpace Q_as_MetricSpace n -> Type with
| O => fun p x => p==x
| (S n') => fun p f => forall v, MVP_uc_sig n' (p ! (MVP_C_ Q_as_CRing _ (Qclamp01 v))) (f v)
end.

(** Multivariable polynomials are uniformly continuous on the unit hyper interval *)
Definition MVP_uc : forall n (p:MultivariatePolynomial Q_as_CRing n),
 {f:n_UniformlyContinuousFunction Q_as_MetricSpace Q_as_MetricSpace n
 |MVP_uc_sig _ p f}.
Proof.
 induction n.
  intros x.
  exists x.
  simpl.
  reflexivity.
 intros p.
 assert (is_UniformlyContinuousFunction (fun (x:Q_as_CRing) => ProjT1 (IHn (p ! (MVP_C_ Q_as_CRing _ (Qclamp01 x))))) (MVP_apply_modulus p)) by abstract
   (intros e x y Hxy; assert (Hxy' : ball_ex (MVP_apply_modulus p e) (Qclamp01 x) (Qclamp01 y)) by
     (destruct (MVP_apply_modulus p e); auto; simpl; rewrite -> Qball_Qabs; apply: Qclamp01_close;
       rewrite <- Qball_Qabs; auto); destruct (Qclamp01_clamped x) as [Hx0 Hx1];
         destruct (Qclamp01_clamped y) as [Hy0 Hy1];
           assert (X:=@MVP_apply_modulus_correct _ p (Qclamp01 x) (Qclamp01 y) e Hx0 Hx1 Hy0 Hy1 Hxy');
             clear Hxy Hxy'; generalize (proj2_sigT _  _ (IHn p ! (MVP_C_ Q_as_CRing n (Qclamp01 x))))
               (proj2_sigT _  _ (IHn p ! (MVP_C_ Q_as_CRing n (Qclamp01 y))));
                 set (x':=Qclamp01 x) in *; set (y':=Qclamp01 y) in *; simpl in X; revert X;
                   generalize (ProjT1 (IHn p ! (MVP_C_ Q_as_CRing n x')))
                     (ProjT1 (IHn p ! (MVP_C_ Q_as_CRing n y')));
                       change (Q_as_CSetoid) with (csg_crr Q_as_CRing);
                         generalize (p ! (MVP_C_ Q_as_CRing n x')) (p ! (MVP_C_ Q_as_CRing n y'));
                           clear - e; induction n;[ simpl; intros p q s t H Hs Ht;
                             rewrite <- Hs, <- Ht; apply (H Vnil); constructor|]; simpl;
                               intros p q s t H Hs Ht v; apply (fun H => IHn _ _ _ _ H (Hs v) (Ht v));
                                 intros v0 Hv0; apply (H (Vcons (Qclamp01 v) v0)); split; auto;
                                   apply Qclamp01_clamped).
 exists (Build_UniformlyContinuousFunction H).
 simpl.
 intros v.
 exact (ProjT2 (IHn p ! (MVP_C_ Q_as_CRing n (Qclamp01 v)))).
Defined.

Definition MVP_uc_Q := (fun n p => ProjT1 (MVP_uc n p)).

Add Parametric Morphism n : (@MVP_uc_Q n) with signature (@st_eq _) ==> (@st_eq _) as MVP_uc_Q_wd.
Proof.
 induction n.
  simpl.
  unfold MVP_uc_Q.
  simpl.
  auto.
 intros x y Hxy a.
 apply: IHn.
 rewrite -> Hxy.
 reflexivity.
Qed.

Fixpoint n_Cap X Y (plX : PrelengthSpace X) n : Complete (n_UniformlyContinuousFunction X Y n) -->
 n_UniformlyContinuousFunction (Complete X) (Complete Y) n :=
match n return Complete (n_UniformlyContinuousFunction X Y n) -->
 n_UniformlyContinuousFunction (Complete X) (Complete Y) n with
| O => uc_id _
| (S n') => (uc_compose_uc _ _ _ (@n_Cap X Y plX n')) ∘ (@Cap X _ plX)
end.

(** A [Cmap] for an n parameter function. *)
Definition n_Cmap X Y (plX : PrelengthSpace X) n : n_UniformlyContinuousFunction X Y n -->
 n_UniformlyContinuousFunction (Complete X) (Complete Y) n :=
(@n_Cap X Y plX n) ∘ (@Cunit _).

Add Parametric Morphism X Y plX n : (@n_Cap X Y plX n)
 with signature (@st_eq _) ==> (@st_eq _) as n_Cap_wd.
Proof.
 induction n.
  simpl.
  auto.
 intros x y Hxy z.
 apply: IHn.
 apply: Cap_wd; auto.
 reflexivity.
Qed.

Add Parametric Morphism X Y plX n : (@n_Cmap X Y plX n)
 with signature (@st_eq _) ==> (@st_eq _) as n_Cmap_wd.
Proof.
 intros x y Hxy.
 unfold n_Cmap.
 simpl.
 rewrite -> Hxy.
 reflexivity.
Qed.

(** Multivariable polynomials on the unit hyper interval can be applied to real numbers *)
Definition MVP_uc_fun n (p:MultivariatePolynomial _ n) :
 n_UniformlyContinuousFunction CR CR n :=
n_Cmap _ QPrelengthSpace n (MVP_uc_Q n p).

Add Parametric Morphism n : (@MVP_uc_fun n)
 with signature (@st_eq _) ==> (@st_eq _) as MVP_uc_fun_wd.
Proof.
 intros x y Hxy.
 unfold MVP_uc_fun.
 rewrite -> Hxy.
 reflexivity.
Qed.

Section MVP_correct.

(** Correctness lemmas for [MVP_uc_fun]. *)
Lemma MVP_uc_fun_sub_Q : forall n (p:MultivariatePolynomial _ (S n)) x,
 0 <= x -> x <= 1 ->
 (MVP_uc_fun (S n) p ('x)%CR)[=](MVP_uc_fun n (p!(MVP_C_ _ _ x))).
Proof.
 intros n p x Hx0 Hx1.
 unfold MVP_uc_fun.
 apply: n_Cap_wd.
 intros e1 e2.
 simpl.
 unfold Cap_raw.
 simpl.
 change (ball (e1 + e2) (MVP_uc_Q n p ! (MVP_C_ Q_as_CRing n (Qmax 0 (Qmin 1 x))))
   (MVP_uc_Q n p ! (MVP_C_ Q_as_CRing n x))).
 rewrite ->  Qle_min_r in Hx1.
 rewrite -> Hx1.
 rewrite ->  Qle_max_r in Hx0.
 rewrite -> Hx0.
 apply ball_refl.
Qed.

Fixpoint MVP_CR_apply n : extSetoid (MultivariatePolynomial CRasCRing n) (n_Function CR CR n) :=
match n return extSetoid (MultivariatePolynomial CRasCRing n) (n_Function CR CR n) with
| O => id
| S n' => Build_Morphism _ (n_Function CR CR (S n')) (fun p => Build_Morphism _ _ (fun x => MVP_CR_apply n' (p!(MVP_C_ _ n' x)))
 (fun (x y : RegularFunction Q_as_MetricSpace) (Hxy : regFunEq x y) =>
       Morphism_prf (MVP_CR_apply n') p ! (MVP_C_ CRasCRing n' x)
         p ! (MVP_C_ CRasCRing n' y)
         (cpoly_apply_wd (MultivariatePolynomial CRasCRing n') p p
            (MVP_C_ CRasCRing n' x) (MVP_C_ CRasCRing n' y) (reflexivity p)
            (csf_wd CRasCSetoid (MultivariatePolynomial CRasCRing n')
               (MVP_C_ CRasCRing n') x y Hxy))))
 (fun (x1 x2 : cpoly_cring (MultivariatePolynomial CRasCRing n'))
         (H : x1[=]x2) (x : RegularFunction Q_as_MetricSpace) =>
       Morphism_prf (MVP_CR_apply n') x1 ! (MVP_C_ CRasCRing n' x)
         x2 ! (MVP_C_ CRasCRing n' x)
         (cpoly_apply_wd (MultivariatePolynomial CRasCRing n') x1 x2
            (MVP_C_ CRasCRing n' x) (MVP_C_ CRasCRing n' x) H
            (reflexivity (MVP_C_ CRasCRing n' x))))
end.

Fixpoint MVP_uc_fun_correct_sig_Q n : n_UniformlyContinuousFunction CR CR n -> n_Function CR CR n -> Prop :=
match n return n_UniformlyContinuousFunction CR CR n -> n_Function CR CR n -> Prop with
| O => fun a b => st_eq a b
| S n' => fun f g => forall x, (0 <= x)%Q -> (x <= 1)%Q -> MVP_uc_fun_correct_sig_Q n' (f ('x)%CR) (g ('x)%CR)
end.

Add Parametric Morphism n :
 (@MVP_uc_fun_correct_sig_Q n) with signature (@st_eq _) ==> (@st_eq _) ==> iff as MVP_uc_fun_correct_sig_Q_wd.
 induction n; intros x y Hxy a b Hab.
Proof.
  change (x==a <-> y==b)%CR.
  rewrite -> Hxy, Hab.
  reflexivity.
 simpl.
 split; intros H c.
  rewrite <- (IHn _ _ (Hxy (' c)%CR) _ _ (Hab ('c)%CR)).
  auto.
 rewrite -> (IHn _ _ (Hxy ('c)%CR) _ _ (Hab ('c)%CR)).
 auto.
Qed.

Lemma MVP_uc_fun_correct_Q : forall n (p:MultivariatePolynomial Q_as_CRing n),
 MVP_uc_fun_correct_sig_Q n (MVP_uc_fun n p) (MVP_CR_apply n (MVP_map inject_Q_hom n p)).
Proof.
 induction n; intros p.
  change ('p=='p)%CR.
  reflexivity.
 intros x Hx0 Hx1.
 change (MVP_uc_fun_correct_sig_Q n (MVP_uc_fun (S n) p ('x)%CR)
   (MVP_CR_apply n ((MVP_map inject_Q_hom (S n) p)!(MVP_C_ _ _ ('x)%CR)))).
 eapply MVP_uc_fun_correct_sig_Q_wd;[apply MVP_uc_fun_sub_Q; auto| |apply IHn].
 apply Morphism_prf.
 simpl.
 setoid_replace (MVP_C_ CRasCRing n (' x)%CR) with ((MVP_map inject_Q_hom n) (MVP_C_ Q_as_CRing n x)).
  symmetry.
  apply cpoly_map_apply.
 clear - n.
 induction n.
  change ('x[=]'x)%CR.
  reflexivity.
 simpl.
 apply: csf_wd.
 apply IHn.
Qed.

Fixpoint MVP_uc_fun_close_sig n e : n_UniformlyContinuousFunction CR CR n -> n_Function CR CR n -> Prop :=
match n return n_UniformlyContinuousFunction CR CR n -> n_Function CR CR n -> Prop with
| O => fun a b => ball e a b
| S n' => fun f g => forall x, ('0 <= x)%CR -> (x <= '1)%CR -> MVP_uc_fun_close_sig n' e (f x) (g x)
end.

Add Parametric Morphism n :
 (@MVP_uc_fun_close_sig n) with signature QposEq ==> (@st_eq _) ==> (@st_eq _) ==> iff as MVP_uc_fun_close_sig_wd.
 induction n; intros e1 e2 He x y Hxy a b Hab.
Proof.
  change (ball e1 x a <-> ball e2 y b).
  rewrite -> He, Hxy, Hab.
  reflexivity.
 simpl.
 split; intros H c.
  rewrite <- (IHn _ _ He _ _ (Hxy c) _ _ (Hab c)).
  auto.
 rewrite -> (IHn _ _ He _ _ (Hxy c) _ _ (Hab c)).
 auto.
Qed.

Lemma MVP_uc_fun_close_weaken : forall n (e1 e2:Qpos) f g, (e1 <= e2) ->
 MVP_uc_fun_close_sig n e1 f g ->
 MVP_uc_fun_close_sig n e2 f g.
Proof.
 induction n; intros e1 e2 f g He H.
  apply: ball_weak_le.
   apply He.
  apply H.
 intros x Hx0 Hx1.
 apply: IHn.
  apply He.
 apply H; auto.
Qed.

Fixpoint n_Function_ball01 n e : n_Function CR CR n -> n_Function CR CR n -> Prop :=
match n return n_Function CR CR n -> n_Function CR CR n -> Prop with
| O => ball e
| S n' => fun f g => forall x, ('0 <= x)%CR -> (x <= '1)%CR -> n_Function_ball01 n' e (f x) (g x)
end.

Add Parametric Morphism n :
 (@n_Function_ball01 n) with signature QposEq ==> (@st_eq _) ==> (@st_eq _) ==> iff as n_Function_ball01_wd.
 induction n; intros e1 e2 He x y Hxy a b Hab.
Proof.
  change (ball e1 x a <-> ball e2 y b).
  rewrite -> He, Hxy, Hab.
  reflexivity.
 simpl.
 split; intros H c.
  rewrite <- (IHn _ _ He _ _ (Hxy c) _ _ (Hab c)).
  auto.
 rewrite -> (IHn _ _ He _ _ (Hxy c) _ _ (Hab c)).
 auto.
Qed.


Lemma MVP_uc_fun_close_left : forall n (e1 e2:Qpos) f1 f2 g,
 ball e1 f1 f2 ->
 MVP_uc_fun_close_sig n e2 f2 g ->
 MVP_uc_fun_close_sig n (e1+e2) f1 g.
Proof.
 induction n; intros e1 e2 f g1 g2 H0 H1.
  eapply ball_triangle.
   apply H0.
  apply H1.
 intros x Hx0 Hx1.
 apply: IHn.
  apply H0; auto.
 apply H1; auto.
Qed.

Lemma MVP_uc_fun_close_right : forall n (e1 e2:Qpos) f g1 g2,
 MVP_uc_fun_close_sig n e1 f g1 ->
 n_Function_ball01 n e2 g1 g2 ->
 MVP_uc_fun_close_sig n (e1+e2) f g2.
Proof.
 induction n; intros e1 e2 f g1 g2 H0 H1.
  eapply ball_triangle.
   apply H0.
  apply H1.
 intros x Hx0 Hx1.
 apply: IHn.
  apply H0; auto.
 apply H1; auto.
Qed.

Lemma n_Function_ball01_sym : forall n e f g,
(n_Function_ball01 n e f g) ->
(n_Function_ball01 n e g f).
Proof.
 induction n.
  apply ball_sym.
 intros e f g H x Hx0 Hx1.
 apply IHn.
 apply H; auto.
Qed.

Lemma n_Function_ball01_triangle : forall n e1 e2 f g h,
(n_Function_ball01 n e1 f g) ->
(n_Function_ball01 n e2 g h) ->
(n_Function_ball01 n (e1+e2)%Qpos f h).
Proof.
 induction n.
  apply ball_triangle.
 intros e1 e2 f g h H0 H1 x Hx0 Hx1.
 apply: IHn.
  apply H0; auto.
 apply H1; auto.
Qed.

Lemma n_Function_ball01_plus : forall n e p1 p2 p3,
(n_Function_ball01 n e (MVP_CR_apply n p2) (MVP_CR_apply n p3)) ->
(n_Function_ball01 n e (MVP_CR_apply n (p1[+]p2)) (MVP_CR_apply n (p1[+]p3))).
Proof.
 induction n; intros e p1 p2 p3 H.
  intros d1 d2.
  simpl.
  unfold Qball.
  unfold Cap_raw.
  simpl.
  replace RHS with ((approximate p1 ((1 # 2) * d1)%Qpos - approximate p1 ((1 # 2) * d2)%Qpos)
    +(approximate p2 ((1 # 2) * d1)%Qpos - approximate p3 ((1 # 2) * d2)%Qpos)) by simpl; ring.
  replace LHS with (((1 # 2) * d1 + (1 # 2) * d2)%Qpos+((1 # 2) * d1 + e + (1 # 2) * d2)%Qpos) by simpl; QposRing.
  apply AbsSmall_plus.
   change (ball ((1 # 2) * d1 + (1 # 2) * d2) (approximate p1 ((1 # 2) * d1)%Qpos) (approximate p1 ((1 # 2) * d2)%Qpos)).
   generalize ((1#2)*d1)%Qpos ((1#2)*d2)%Qpos.
   change (p1[=]p1).
   reflexivity.
  generalize ((1#2)*d1)%Qpos ((1#2)*d2)%Qpos.
  apply H.
 intros x Hx0 Hx1.
 change (n_Function_ball01 n e (MVP_CR_apply _ (p1[+]p2) ! (MVP_C_ _ _ x))
   (MVP_CR_apply _ (p1[+]p3) ! (MVP_C_ _ _ x))).
 eapply n_Function_ball01_wd;[| | |apply IHn].
    reflexivity.
   apply Morphism_prf.
   apply plus_apply.
  apply Morphism_prf.
  apply plus_apply.
 apply: H; auto.
Qed.

Lemma n_Function_ball01_mult_C : forall n e c q1 q2,
('0 <= c)%CR -> (c <= '1)%CR ->
(n_Function_ball01 n e (MVP_CR_apply n q1) (MVP_CR_apply n q2)) ->
(n_Function_ball01 n e (MVP_CR_apply n ((MVP_C_ _ _ c)[*]q1))
                       (MVP_CR_apply n ((MVP_C_ _ _ c)[*]q2))).
Proof.
 induction n; intros e c q1 q2 Hc0 Hc1 H.
  change (ball e (c * q1)%CR (c * q2)%CR).
  rewrite <- CRAbsSmall_ball.
  change (AbsSmall (' e)%CR (c[*]q1[-]c[*]q2)).
  rstepr (c[*](q1[-]q2)).
  apply AbsSmall_leEq_trans with (c[*]'e)%CR.
   rstepr (One[*]('e))%CR.
   apply mult_resp_leEq_rht; auto.
   change ('0<='e)%CR.
   rewrite -> CRle_Qle.
   auto with *.
  apply mult_resp_AbsSmall; auto.
  rewrite -> CRAbsSmall_ball.
  auto.
 intros x Hx0 Hx1.
 change (n_Function_ball01 n e (MVP_CR_apply _ (MVP_C_ _ _ c[*]q1) ! (MVP_C_ _ _ x))
   (MVP_CR_apply _ (MVP_C_ _ _ c[*]q2) ! (MVP_C_ _ _ x))).
 eapply n_Function_ball01_wd.
    reflexivity.
   apply Morphism_prf.
   eapply eq_transitive.
    apply mult_apply.
   apply mult_wdl.
   simpl.
   apply c_apply.
  apply Morphism_prf.
  eapply eq_transitive.
   apply mult_apply.
  apply mult_wdl.
  simpl.
  apply c_apply.
 apply IHn; auto.
 apply: H; auto.
Qed.

Fixpoint MVP_is_Bound01 n (M:CR) : MultivariatePolynomial CRasCRing n -> Prop :=
match n return MultivariatePolynomial CRasCRing n -> Prop with
| O => fun a => AbsSmall M a
| S n' => fun p => forall x, ('0 <= x)%CR -> (x <= '1)%CR ->
  MVP_is_Bound01 n' M (p ! (MVP_C_ _ _ x))
end.

Add Parametric Morphism n :
 (@MVP_is_Bound01 n) with signature (@st_eq _) ==> (@st_eq _) ==> iff as MVP_is_Bound01_wd.
Proof.
 induction n; intros x y Hxy a b Hab.
  simpl.
  rewrite -> Hxy.
  rewrite -> Hab.
  reflexivity.
 split; intros H c Hc0 Hc1.
  change (MVP_is_Bound01 n y b ! (MVP_C_ CRasCRing n c)).
  rewrite <- (IHn _ _ Hxy (a!(MVP_C_ CRasCRing n c)) (b!(MVP_C_ CRasCRing n c))).
   apply H; auto.
  rewrite -> Hab.
  reflexivity.
 change (MVP_is_Bound01 n x a ! (MVP_C_ CRasCRing n c)).
 rewrite <- (fun A => IHn y x A (b!(MVP_C_ CRasCRing n c)) (a!(MVP_C_ CRasCRing n c))).
   apply H; auto.
  symmetry; auto.
 rewrite -> Hab.
 reflexivity.
Qed.

Lemma MVP_is_Bound01_plus : forall n M N p q,
 MVP_is_Bound01 n M p -> MVP_is_Bound01 n N q ->
 MVP_is_Bound01 n (M+N)%CR (p[+]q).
Proof.
 induction n; intros M N p q Hp Hq.
  apply: AbsSmall_plus; auto.
 simpl.
 intros x Hx0 Hx1.
 rewrite -> plus_apply.
 auto.
Qed.

Lemma MVP_is_Bound01_mult01 : forall n M p x,
 ('0 <= x)%CR -> (x <= '1)%CR ->
 MVP_is_Bound01 n M p ->
 MVP_is_Bound01 n M (MVP_C_ _ n x[*]p).
Proof.
 induction n; intros M p x Hx0 Hx1 H.
  simpl.
  change (st_car CR) in p.
  eapply AbsSmall_leEq_trans;[|apply mult_resp_AbsSmall;[|apply H]]; auto.
  rstepr ((One:CR)[*]M).
  apply mult_resp_leEq_rht; auto.
  simpl in H.
  rewrite <- CRabs_AbsSmall in H.
  eapply leEq_transitive;[|apply H].
  rewrite <- (CRasIRasCR_id p).
  rewrite <- CRabs_correct.
  simpl.
  rewrite <- IR_Zero_as_CR.
  rewrite <- IR_leEq_as_CR.
  apply AbsIR_nonneg.
 simpl.
 intros y Hy0 Hy1.
 rewrite -> mult_apply.
 rewrite -> c_apply.
 apply IHn; auto.
Qed.

Lemma n_Function_ball01_mult : forall n e x y p M,
MVP_is_Bound01 n ('M)%CR p ->
ball_ex (Qscale_modulus M e) x y ->
n_Function_ball01 n e
  (MVP_CR_apply n (MVP_C_ CRasCRing n x[*]p))
  (MVP_CR_apply n (MVP_C_ CRasCRing n y[*]p)).
Proof.
 induction n; intros e x y p b Hb Hxy.
  change (ball e (x*p) (y*p))%CR.
  rewrite <- CRAbsSmall_ball.
  change (AbsSmall (' e)%CR (x[*]p[-]y[*]p)).
  rstepr (p[*](x[-]y)).
  simpl in Hb.
  case_eq (Qscale_modulus b e).
   intros q Hq.
   apply AbsSmall_leEq_trans with (CRabs p[*]'q)%CR.
    destruct b as [[|nb|nb] db].
      discriminate Hq.
     simpl in Hq.
     injection Hq; clear Hq; intros Hq; rewrite <- Hq.
     assert (Z: (' ((db # nb) * e)%Qpos)%CR[#]Zero).
      apply: Qap_CRap.
      apply Qpos_nonzero.
     apply shift_mult_leEq with Z.
      apply: CRlt_Qlt; auto with *.
     rewrite <- CRabs_AbsSmall in Hb.
     stepr ('(nb#db))%CR; auto.
     change ((' (nb # db))%CR[=](' e)%CR[*]CRinv (' ((db # nb) * e)%Qpos)%CR Z).
     rewrite -> CRinv_Qinv.
     rewrite -> CRmult_Qmult.
     rewrite -> CReq_Qeq.
     autorewrite with QposElim.
     rewrite -> Qinv_mult_distr.
     replace RHS with ((/(db#nb) * e) * /e) by simpl; ring.
     change (nb#db == ((nb#db)*e/e)).
     rewrite -> Qdiv_mult_l.
      reflexivity.
     apply Qpos_nonzero.
    elim (Qle_not_lt 0 (Zneg nb # db)); auto with *.
    rewrite <- CRle_Qle.
    apply: AbsSmall_nonneg.
    apply Hb.
   cut (Not (Not (AbsSmall (CRabs p[*](' q)%CR) (p[*](x[-]y))))).
    unfold Not, AbsSmall.
    repeat rewrite -> leEq_def.
    unfold Not; tauto.
   generalize (leEq_or_leEq CRasCOrdField Zero p).
   cut (((Zero:CR)[<=]p or (p:CR)[<=]Zero) -> AbsSmall (CRabs p[*](' q)%CR) (p[*](x[-]y))).
    unfold Not; tauto.
   intros [Hp|Hp].
    rewrite -> CRabs_pos; auto.
    apply mult_resp_AbsSmall;auto.
    rewrite Hq in Hxy.
    rewrite -> CRAbsSmall_ball.
    auto.
   rewrite -> CRabs_neg; auto.
   rstepr (([--]p)[*](y[-]x)).
   apply mult_resp_AbsSmall.
    rstepl ([--]Zero:CR).
    apply inv_resp_leEq.
    auto.
   rewrite Hq in Hxy.
   rewrite -> CRAbsSmall_ball.
   apply ball_sym.
   apply Hxy.
  intros Hq.
  destruct b as [[|nb|nb] db]; try discriminate Hq.
  stepr (Zero:CR).
   apply zero_AbsSmall.
   simpl.
   rewrite -> CRle_Qle; auto with *.
  rstepl (Zero[*](x[-]y))%CR.
  apply mult_wdl.
  destruct Hb as [Hb0 Hb1].
  apply: leEq_imp_eq.
   stepl (-(' (0 # db)))%CR; auto.
   rewrite -> CRopp_Qopp.
   change ('(0#db)=='0)%CR.
   rewrite -> CReq_Qeq.
   unfold Qeq; reflexivity.
  stepr ((' (0 # db)))%CR; auto.
  change ('(0#db)=='0)%CR.
  rewrite -> CReq_Qeq.
  unfold Qeq; reflexivity.
 simpl.
 intros a Ha0 Ha1.
 eapply n_Function_ball01_wd.
    reflexivity.
   apply Morphism_prf.
   eapply eq_transitive.
    apply mult_apply.
   apply csbf_wd.
    apply c_apply.
   reflexivity.
  apply Morphism_prf.
  eapply eq_transitive.
   apply mult_apply.
  apply csbf_wd.
   apply c_apply.
  reflexivity.
 apply: IHn; auto.
Qed.

Fixpoint MVP_poor_Bound01 n : MultivariatePolynomial Q_as_CRing n -> Q :=
match n return MultivariatePolynomial Q_as_CRing n -> Q with
| O => Qabs
| S n' => fix MVP_poor_Bound01_H p : Q :=
          match p with
          | cpoly_zero => 0
          | cpoly_linear s p' => MVP_poor_Bound01 n' s + MVP_poor_Bound01_H p'
          end
end.

Lemma MVP_poor_Bound01_zero : forall n, MVP_poor_Bound01 n (Zero)==0.
Proof.
 induction n.
  reflexivity.
 reflexivity.
Qed.

Add Parametric Morphism n :
 (@MVP_poor_Bound01 n) with signature (@st_eq _) ==> Qeq as MVP_poor_Bound01_wd.
Proof.
 induction n.
  intros x y Hxy.
  simpl in *.
  rewrite -> Hxy.
  reflexivity.
 induction x.
  induction y.
   reflexivity.
  intros [H0 H1].
  simpl in *.
  change 0 with (0+0).
  apply Qplus_comp.
   rewrite <- (MVP_poor_Bound01_zero n).
   apply IHn.
   symmetry; auto.
  apply IHy.
  apply H1.
 intros [|t y] [H0 H1].
  simpl.
  change 0 with (0+0).
  apply Qplus_comp.
   rewrite <- (MVP_poor_Bound01_zero n).
   apply IHn.
   auto.
  change (MVP_poor_Bound01 (S n) x==0).
  rewrite <- (MVP_poor_Bound01_zero (S n)).
  apply IHx.
  apply eq_symmetric.
  apply H1.
 simpl.
 apply Qplus_comp.
  apply IHn.
  auto.
 apply IHx.
 auto.
Qed.

Lemma MVP_poor_is_Bound01 : forall n p,
MVP_is_Bound01 n ('(MVP_poor_Bound01 n p))%CR (MVP_map inject_Q_hom n p).
Proof.
 induction n.
  split.
   change (-('Qabs p)<='p)%CR.
   rewrite -> CRopp_Qopp.
   rewrite -> CRle_Qle.
   simpl in p.
   replace RHS with (- (- p)) by simpl; ring.
   apply Qopp_le_compat.
   rewrite <- Qabs_opp.
   apply Qle_Qabs.
  change ('p<=('Qabs p))%CR.
  rewrite -> CRle_Qle.
  apply Qle_Qabs.
 simpl.
 induction p; intros x Hx0 Hx1.
  change (MVP_is_Bound01 n ('0)%CR (Zero)).
  clear - n.
  induction n.
   apply AbsSmall_reflexive.
   apply leEq_reflexive.
  intros y _ _.
  apply IHn.
 change (MVP_is_Bound01 n (' (MVP_poor_Bound01 n s + (fix MVP_poor_Bound01_H (p0 : cpoly
   (MultivariatePolynomial Q_as_CRing n)) : Q := match p0 with | cpoly_zero => 0
     | cpoly_linear s0 p' => (MVP_poor_Bound01 n s0 + MVP_poor_Bound01_H p')%Q end) p))%CR
       (MVP_map inject_Q_hom n s[+]MVP_C_ CRasCRing n x[*](cpoly_map (MVP_map inject_Q_hom n) p) ! (MVP_C_ CRasCRing n x))).
 rewrite <- CRplus_Qplus.
 apply MVP_is_Bound01_plus.
  apply IHn.
 apply MVP_is_Bound01_mult01; auto.
Qed.

Lemma MVP_CR_apply_cont : forall n e (p:MultivariatePolynomial Q_as_CRing (S n)),
 {d | forall x y,
 ('0 <= x)%CR -> (x <= '1)%CR ->
 ('0 <= 'y)%CR -> ('y <= '1)%CR ->
 ball_ex d x ('y)%CR ->
 n_Function_ball01 n e (MVP_CR_apply _ (MVP_map inject_Q_hom _ p) x)
                       (MVP_CR_apply _ (MVP_map inject_Q_hom _ p) ('y)%CR)}.
Proof.
 intros n e p.
 revert e.
 induction p; intros e.
  exists QposInfinity.
  intros x y _ _ _ _ _.
  change (n_Function_ball01 n e (MVP_CR_apply n Zero) (MVP_CR_apply n Zero)).
  generalize (MVP_CR_apply n Zero).
  induction n.
   apply ball_refl.
  intros s a _ _.
  apply IHn.
 simpl.
 destruct (IHp ((1#2)*e)%Qpos) as [d0 Hd0].
 set (b:=MVP_poor_Bound01 (S n) p).
 set (d1:=(Qscale_modulus b ((1 # 2) * e))).
 exists (QposInf_min d0 d1).
 intros x y Hx0 Hx1 Hy0 Hy1 Hxy.
 change (n_Function_ball01 n e (MVP_CR_apply n
   ((MVP_map inject_Q_hom n s)[+](MVP_C_ CRasCRing n x)[*]((cpoly_map (MVP_map inject_Q_hom n) p))
     ! (MVP_C_ CRasCRing n x))) (MVP_CR_apply n
       ((MVP_map inject_Q_hom n s)[+](MVP_C_ CRasCRing n ('y)%CR)[*]((cpoly_map (MVP_map inject_Q_hom n) p))
         ! (MVP_C_ CRasCRing n (inject_Q_hom y)%CR)))).
 apply n_Function_ball01_plus.
 setoid_replace e with ((1#2)*e + (1#2)*e)%Qpos by QposRing.
 apply n_Function_ball01_triangle with (MVP_CR_apply n (MVP_C_ CRasCRing n x[*]
   (cpoly_map (MVP_map inject_Q_hom n) p) ! (MVP_C_ CRasCRing n (inject_Q_hom y)%CR))).
  apply n_Function_ball01_mult_C; auto.
  change (n_Function_ball01 n ((1 # 2) * e) (MVP_CR_apply (S n) (MVP_map inject_Q_hom (S n) p) x)
    (MVP_CR_apply (S n) (MVP_map inject_Q_hom (S n) p) ('y)%CR)).
  apply Hd0; auto with *.
  eapply ball_ex_weak_le;[|apply Hxy].
  apply QposInf_min_lb_l.
 eapply n_Function_ball01_wd.
    reflexivity.
   apply Morphism_prf.
   apply mult_wdr.
   eapply eq_transitive.
    apply csbf_wd;[apply eq_reflexive|].
    symmetry.
    apply MVP_map_C_.
   symmetry.
   apply cpoly_map_apply.
  apply Morphism_prf.
  apply mult_wdr.
  eapply eq_transitive.
   apply csbf_wd;[apply eq_reflexive|].
   symmetry.
   apply MVP_map_C_.
  symmetry.
  apply cpoly_map_apply.
 apply n_Function_ball01_mult with b.
  assert (Z:=MVP_poor_is_Bound01 (S n) p _ Hy0 Hy1).
  unfold b.
  change (MVP_is_Bound01 n (' MVP_poor_Bound01 (S n) p)%CR
    (MVP_map inject_Q_hom (S n) p) ! (MVP_C_ CRasCRing n (' y)%CR)) in Z.
  eapply MVP_is_Bound01_wd;[| |apply Z].
   reflexivity.
  simpl.
  change (MVP_map inject_Q_hom n p ! (MVP_C_ Q_as_CRing n y)[=] (cpoly_map (MVP_map inject_Q_hom n) p)
    ! (MVP_C_ CRasCRing n (inject_Q_hom y)%CR)).
  rewrite <- MVP_map_C_.
  apply cpoly_map_apply.
 eapply ball_ex_weak_le;[|apply Hxy].
 apply QposInf_min_lb_r.
Qed.

Lemma MVP_uc_fun_close : forall n e (p:MultivariatePolynomial Q_as_CRing n),
 MVP_uc_fun_close_sig n e (MVP_uc_fun n p) (MVP_CR_apply n (MVP_map inject_Q_hom n p)).
Proof.
 induction n; intros e p.
  change (ball e ('p) ('p))%CR.
  apply ball_refl.
 intros x Hx0 Hx1.
 change (MVP_uc_fun_close_sig n e (MVP_uc_fun (S n) p x)
   (MVP_CR_apply (S n) (MVP_map inject_Q_hom (S n) p) x)).
 setoid_replace e with ((((1#3)*e)+(1#3)*e)+(1#3)*e)%Qpos by QposRing.
 set (e3:=((1#3)*e)%Qpos).
 destruct (MVP_CR_apply_cont e3 p) as [d0 Hd].
 set (d1:=mu (MVP_uc_fun (S n) p) e3).
 set (d:=QposInf_min d0 d1).
 set (y:=Qclamp01 (approximate x d)).
 destruct (Qclamp01_clamped (approximate x d)) as [Hy0 Hy1].
 rewrite <- CRle_Qle in Hy0.
 rewrite <- CRle_Qle in Hy1.
 assert (Hd0:=Hd _ _ Hx0 Hx1 Hy0 Hy1).
 assert (Z:ball_ex d x (' Qclamp01 (approximate x d))%CR).
  clear - Hx0 Hx1.
  destruct d as [d|];[|constructor].
  change (ball d x (' Qclamp01 (approximate x d))%CR).
  rewrite <- CRAbsSmall_ball.
  assert (Z:=ball_approx_r x d).
  rewrite <- CRAbsSmall_ball in Z.
  change (AbsSmall (' d)%CR (x[-]'(approximate x d)))%CR in Z.
  revert Z.
  generalize (approximate x d).
  clear - Hx0 Hx1.
  intros s [Z0 Z1].
  simpl.
  split.
   apply Qmax_case.
    intros _.
    apply leEq_transitive with (Zero:CR).
     rstepr ([--](Zero:CR)).
     apply inv_resp_leEq.
     change ('0<='d)%CR.
     rewrite -> CRle_Qle.
     auto with *.
    change (Zero[<=]x[-]Zero)%CR.
    rstepr x.
    auto.
   intros H.
   eapply leEq_transitive;[apply Z0|].
   apply minus_resp_leEq_rht.
   rewrite ->  CRle_Qle.
   apply Qmin_lb_r.
  rewrite -> Qmax_min_distr_r.
  apply Qmin_case.
   intros _.
   eapply leEq_transitive with ('1[-]'1)%CR.
    apply minus_resp_leEq.
    auto.
   rstepl (Zero:CR).
   change ('0<='d)%CR.
   rewrite -> CRle_Qle.
   auto with *.
  intros H.
  eapply leEq_transitive;[|apply Z1].
  apply minus_resp_leEq_rht.
  rewrite ->  CRle_Qle.
  apply Qmax_ub_r.
 eapply MVP_uc_fun_close_right; [|apply n_Function_ball01_sym;apply Hd0].
  eapply MVP_uc_fun_close_left.
   apply uc_prf.
   eapply ball_ex_weak_le;[|apply Z].
   apply QposInf_min_lb_r.
  rewrite ->  CRle_Qle in Hy0.
  rewrite ->  CRle_Qle in Hy1.
  rewrite -> MVP_uc_fun_sub_Q;auto.
  eapply MVP_uc_fun_close_sig_wd.
     reflexivity.
    reflexivity.
   simpl.
   apply Morphism_prf.
   eapply eq_transitive.
    apply csbf_wd.
     reflexivity.
    symmetry.
    apply (MVP_map_C_ inject_Q_hom).
   symmetry.
   change (cpoly_map_fun (MultivariatePolynomial Q_as_CRing n)
     (MultivariatePolynomial CRasCRing n) (MVP_map inject_Q_hom n) p)
       with (cpoly_map (MVP_map inject_Q_hom n) p).
   apply cpoly_map_apply.
  apply IHn.
 eapply ball_ex_weak_le;[|apply Z].
 apply QposInf_min_lb_l.
Qed.

Fixpoint MVP_uc_fun_correct_sig n : n_UniformlyContinuousFunction CR CR n -> n_Function CR CR n -> Prop :=
match n return n_UniformlyContinuousFunction CR CR n -> n_Function CR CR n -> Prop with
| O => fun a b => a[=]b
| S n' => fun f g => forall x, ('0 <= x)%CR -> (x <= '1)%CR -> MVP_uc_fun_correct_sig n' (f x) (g x)
end.

(** Finally, the correctness lemma. *)
Lemma MVP_uc_fun_correct : forall n (p:MultivariatePolynomial Q_as_CRing n),
 MVP_uc_fun_correct_sig n (MVP_uc_fun n p) (MVP_CR_apply n (MVP_map inject_Q_hom n p)).
Proof.
 intros n p.
 generalize (fun e => MVP_uc_fun_close n e p).
 generalize (MVP_uc_fun n p) (MVP_CR_apply n (MVP_map inject_Q_hom n p)).
 clear p.
 induction n; intros a b H.
  apply ball_eq.
  auto.
 intros x Hx0 Hx1.
 apply IHn.
 intros e.
 apply H; auto.
Qed.

End MVP_correct.
