Require Import Bernstein.
Require Import CRing_Homomorphisms.
Require Import COrdFields2.
Require Export Qordfield.
Require Import QMinMax.
Require Import CornTac.

Set Implicit Arguments.

Opaque cpoly_cring.
Opaque cpoly_apply_fun.
Opaque _C_.

Section MultivariatePolynomial.

Variable F : CRing.

Fixpoint MultivariatePolynomial (n:nat) : CRing :=
match n with
| O => F
| S n' => cpoly_cring (MultivariatePolynomial n')
end.

Fixpoint MVP_C_ (n:nat) : RingHom F (MultivariatePolynomial n) :=
match n return RingHom F (MultivariatePolynomial n) with
| O => RHid _
| S n' =>  RHcompose _ _ _ _C_ (MVP_C_ n')
end.

Fixpoint MVP_apply (n:nat) : MultivariatePolynomial n -> (vector F n) -> F :=
match n return MultivariatePolynomial n -> vector F n -> F with
| O => fun x _ => x
| (S n') => fun p v => (MVP_apply (p ! (MVP_C_ _ (Vhead _ _ v))) (Vtail _ _ v))
end.

Add Parametric Morphism n : (@MVP_apply n) with signature (@st_eq (MultivariatePolynomial n)) ==> (@eq _) ==> (@st_eq _) as MVP_apply_wd.
Proof.
induction n;
 intros x y Hxy z.
 assumption.
simpl.
apply IHn.
rewrite Hxy.
reflexivity.
Qed.

Lemma zero_MVP_apply : forall n v, MVP_apply (Zero:MultivariatePolynomial n) v[=]Zero.
Proof.
induction v.
 reflexivity.
simpl.
rewrite <- IHv.
reflexivity.
Qed.

Lemma one_MVP_apply : forall n v, MVP_apply (One:MultivariatePolynomial n) v[=]One.
Proof.
induction v.
 reflexivity.
simpl.
rewrite <- IHv.
rewrite one_apply.
reflexivity.
Qed.

Lemma MVP_plus_apply: forall n (p q : MultivariatePolynomial n) v,
  MVP_apply (p[+]q) v [=] MVP_apply p v[+]MVP_apply q v.
Proof.
induction v.
 reflexivity.
simpl.
rewrite plus_apply.
apply IHv.
Qed.

Lemma MVP_mult_apply: forall n (p q : MultivariatePolynomial n) v,
  MVP_apply (p[*]q) v [=] MVP_apply p v[*]MVP_apply q v.
Proof.
induction v.
 reflexivity.
simpl.
rewrite mult_apply.
apply IHv.
Qed.

Lemma MVP_c_mult_apply: forall n (p : MultivariatePolynomial n) c v,
  MVP_apply (MVP_C_ _ c[*]p) v[=]c[*]MVP_apply p v.
Proof.
induction v.
 reflexivity.
simpl.
rewrite <- IHv.
rewrite _c_mult_apply.
reflexivity.
Qed.

End MultivariatePolynomial.

(* Some upper bound on the polynomial on [0,1] *)
Fixpoint MVP_upperBound (n:nat) : MultivariatePolynomial Q_as_CRing n -> Q :=
match n return MultivariatePolynomial Q_as_CRing n -> Q with
| O => fun x => x
| (S n') => fun p => let (m,b) := BernsteinCoefficents (MVP_C_ Q_as_CRing n') p
                      in vector_rec _ (fun _ _ => Q) 0%Q 
                         (fun c _ _ rec => Qmax (MVP_upperBound n' c) rec) m b
end.

(* Some lower bound on the polynomial on [0,1] *)
Fixpoint MVP_lowerBound (n:nat) : MultivariatePolynomial Q_as_CRing n -> Q :=
match n return MultivariatePolynomial Q_as_CRing n -> Q with
| O => fun x => x
| (S n') => fun p => let (m,b) := BernsteinCoefficents (MVP_C_ Q_as_CRing n') p
                      in vector_rec _ (fun _ _ => Q) 0%Q 
                         (fun c _ _ rec => Qmin (MVP_lowerBound n' c) rec) m b
end.

Open Scope Q_scope.

Fixpoint UnitHyperInterval (n:nat) (v:vector Q n) : Prop :=
match v with
| Vnil => True
| Vcons a _ v' => 0 <= a <= 1 /\ UnitHyperInterval v'
end.

Lemma BernsteinApplyRingHom : forall R F (eta: RingHom R F) n i (H:(i <= n)%nat) a,
 (Bernstein F H) ! (eta a)[=](eta (Bernstein R H) ! a).
Proof.
induction n.
 simpl.
 intros _ _ a.
 do 2 rewrite one_apply.
 auto with *.
intros [|i] H a; simpl;[|destruct (le_lt_eq_dec (S i) (S n) H)];
 autorewrite with apply ringHomPush;
 repeat rewrite IHn;
 reflexivity.
Qed. 

Lemma MVP_BernsteinNonNeg : forall m n i (H:(i <= n)%nat) v (a:Q), 0 <= a -> a <= 1 ->
 0 <= @MVP_apply Q_as_CRing m ((Bernstein _ H)!(MVP_C_ _ _ a)) v.
Proof.
intros m n i H v a Ha0 Ha1.
induction v.
 rapply BernsteinNonNeg; auto.
simpl.
replace RHS with (MVP_apply Q_as_CRing
  (Bernstein _ H) ! (MVP_C_ Q_as_CRing n0 a) v).
 apply IHv.
rapply MVP_apply_wd;try reflexivity.
rewrite BernsteinApplyRingHom.
auto with *.
Qed.

Fixpoint Vector_ix A (n i:nat) (H:(i < n)%nat) (v:vector A n) : A :=
match v in vector _ m return (i < m)%nat -> A with
| Vnil => fun p => False_rect _ (lt_n_O _ p)
| Vcons c n' v' => fun _ => match lt_le_dec i n' with
                            | left p => Vector_ix p v'
                            | right _ => c
                            end
end H.

Lemma MVP_upperBound_correct : forall n p v, UnitHyperInterval v -> MVP_apply _ p v[<=]MVP_upperBound n p.
Proof.
induction n;
 intros p v H.
 apply Qle_refl.
revert p H.
dependent inversion v.
clear H0.
intros p [[Ha0 Ha1] Hv].
stepl (@MVP_apply Q_as_CRing (S n) (let (n0, b) := BernsteinCoefficents (MVP_C_ Q_as_CRing n) p in
        evalBernsteinBasis (MultivariatePolynomial Q_as_CRing n) b) (Vcons Q a n v0));
 [|apply MVP_apply_wd;[apply evalBernsteinCoefficents|reflexivity]].
simpl (MVP_upperBound (S n) p).
destruct (BernsteinCoefficents (MVP_C_ Q_as_CRing n) p) as [m b].
apply Qle_trans with
 (vector_rec (MultivariatePolynomial Q_as_CRing n)
  (fun (n1 : nat) (_ : vector (MultivariatePolynomial Q_as_CRing n) n1) => Q)
  0
  (fun (c : MultivariatePolynomial Q_as_CRing n) (n1 : nat)
     (_ : vector (MultivariatePolynomial Q_as_CRing n) n1) (rec : Q) =>
   Qmax (MVP_apply _ c v0) rec) m b).
 clear IHn Hv.
 destruct m as [|m].
  rewrite (V0_eq _ b).
  unfold evalBernsteinBasis.
  simpl.
  rewrite zero_MVP_apply.
  apply Qle_refl.
 unfold evalBernsteinBasis.
 match goal with 
  |- (?A <= ?B) => set (L:=A); set (R:=B)
 end.
 change (L[<=]R).
 rstepr (R[*]One).
 rewrite <- (@one_MVP_apply Q_as_CRing _ (Vcons _ a _ v0)).
 stepr (R[*](@MVP_apply Q_as_CRing (S n) (@Sumx (cpoly_cring _) _ (fun i H => Bernstein _ (lt_n_Sm_le i m (lt_le_trans _ _ _ H (le_refl _))))) (Vcons _ a _ v0))).
  fold (MultivariatePolynomial Q_as_CRing n).
  unfold L, R; clear L R.
  generalize (le_refl (S m)).
  revert b.
  generalize (S m) at 1 2 5 6 7 8 9.
  induction b; intros l.
   simpl.
   rewrite zero_MVP_apply.
   apply Qle_refl.
  simpl (vector_rec (MultivariatePolynomial Q_as_CRing n)
  (fun (n2 : nat) (_ : vector (MultivariatePolynomial Q_as_CRing n) n2) => Q)
  0
  (fun (c : MultivariatePolynomial Q_as_CRing n) (n2 : nat)
     (_ : vector (MultivariatePolynomial Q_as_CRing n) n2) (rec : Q) =>
   Qmax (MVP_apply Q_as_CRing c v0) rec) (S n1)
  (Vcons (MultivariatePolynomial Q_as_CRing n) a0 n1 b)).
  simpl (evalBernsteinBasisH (MultivariatePolynomial Q_as_CRing n)
    (Vcons (MultivariatePolynomial Q_as_CRing n) a0 n1 b) l).
  simpl (Sumx
      (fun (i : nat) (H : (i < S n1)%nat) =>
       Bernstein (MultivariatePolynomial Q_as_CRing n)
         (lt_n_Sm_le i m (lt_le_trans i (S n1) (S m) H l)))).
  do 2 rewrite MVP_plus_apply.
  rewrite (Qplus_comm (@MVP_apply Q_as_CRing (S n)
   (Sumx
      (fun (i : nat) (l0 : (i < n1)%nat) =>
       Bernstein (MultivariatePolynomial Q_as_CRing n)
         (lt_n_Sm_le i m (lt_le_trans i (S n1) (S m) (lt_S i n1 l0) l))))
   (Vcons Q a n v0))).
  rewrite Qmult_comm.
  rewrite Qmult_plus_distr_l.
  apply Qplus_le_compat; rewrite Qmult_comm; rewrite Qmax_mult_pos_distr_l.
     replace LHS with (MVP_apply Q_as_CRing a0 v0 *
   @MVP_apply Q_as_CRing (S n)
     (Bernstein (MultivariatePolynomial Q_as_CRing n)
        (lt_n_Sm_le n1 m (lt_le_trans n1 (S n1) (S m) (lt_n_Sn n1) l)))
     (Vcons Q a n v0)).
      apply Qmax_ub_l.
     simpl.
     rewrite <- (MVP_mult_apply Q_as_CRing).
     rapply MVP_apply_wd; try reflexivity.
     replace (lt_n_Sm_le n1 m (lt_le_trans n1 (S n1) (S m) (lt_n_Sn n1) l))
      with (le_S_n n1 m l) by apply le_irrelevent.
     apply _c_mult_apply.
    apply MVP_BernsteinNonNeg; auto.
   eapply Qle_trans;[|apply Qmax_ub_r].
   set (R:=vector_rec (MultivariatePolynomial Q_as_CRing n)
  (fun (n2 : nat) (_ : vector (MultivariatePolynomial Q_as_CRing n) n2) => Q)
  0
  (fun (c : MultivariatePolynomial Q_as_CRing n) (n2 : nat)
     (_ : vector (MultivariatePolynomial Q_as_CRing n) n2) (rec : Q) =>
   Qmax (MVP_apply Q_as_CRing c v0) rec) n1 b) in *.
   replace RHS with (R*@MVP_apply Q_as_CRing (S n)
    (Sumx
        (fun (i : nat) (l0 : (i < n1)%nat) =>
         Bernstein (MultivariatePolynomial Q_as_CRing n)
          (lt_n_Sm_le i m (lt_le_trans i n1 (S m) l0 (le_Sn_le _ _ l)))))
      (Vcons Q a n v0)).
    apply IHb.
   rapply mult_wdr.
   apply MVP_apply_wd; try reflexivity.
   apply Sumx_wd.
   intros i H.
   replace (lt_n_Sm_le i m (lt_le_trans i (S n1) (S m) (lt_S i n1 H) l))
    with (lt_n_Sm_le i m (lt_le_trans i n1 (S m) H (le_Sn_le n1 (S m) l))) by apply le_irrelevent.
   reflexivity.
  clear - Ha0 Ha1.
  induction n1.
   rewrite zero_MVP_apply.
   auto with *.
  simpl (Sumx
     (fun (i : nat) (l0 : (i < S n1)%nat) =>
      Bernstein (MultivariatePolynomial Q_as_CRing n)
        (lt_n_Sm_le i m (lt_le_trans i (S (S n1)) (S m) (lt_S i (S n1) l0) l)))).
  rewrite MVP_plus_apply.
  rapply plus_resp_nonneg.
   stepr (@MVP_apply Q_as_CRing (S n)
         (Sumx
            (fun (i : nat) (l0 : (i < n1)%nat) =>
             Bernstein (MultivariatePolynomial Q_as_CRing n)
               (lt_n_Sm_le i m (lt_le_trans i (S n1) (S m) (lt_S i n1 l0) (le_Sn_le _ _ l))))) (Vcons Q a n v0)).
    apply IHn1.
   apply MVP_apply_wd; try reflexivity.
   apply Sumx_wd.
   intros i H.
   replace (lt_n_Sm_le i m
     (lt_le_trans i (S n1) (S m) (lt_S i n1 H) (le_Sn_le (S n1) (S m) l)))
    with (lt_n_Sm_le i m
     (lt_le_trans i (S (S n1)) (S m) (lt_S i (S n1) (lt_S i n1 H)) l))
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
induction n;
 intros p v H.
 apply Qle_refl.
revert p H.
dependent inversion v.
clear H0.
intros p [[Ha0 Ha1] Hv].
stepr (@MVP_apply Q_as_CRing (S n) (let (n0, b) := BernsteinCoefficents (MVP_C_ Q_as_CRing n) p in
        evalBernsteinBasis (MultivariatePolynomial Q_as_CRing n) b) (Vcons Q a n v0));
 [|apply MVP_apply_wd;[apply evalBernsteinCoefficents|reflexivity]].
simpl (MVP_lowerBound (S n) p).
destruct (BernsteinCoefficents (MVP_C_ Q_as_CRing n) p) as [m b].
apply Qle_trans with
 (vector_rec (MultivariatePolynomial Q_as_CRing n)
  (fun (n1 : nat) (_ : vector (MultivariatePolynomial Q_as_CRing n) n1) => Q)
  0
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
 rewrite zero_MVP_apply.
 apply Qle_refl.
unfold evalBernsteinBasis.
match goal with 
 |- (?A <= ?B) => set (R:=A); set (L:=B)
end.
change (R[<=]L).
rstepl (R[*]One).
rewrite <- (@one_MVP_apply Q_as_CRing _ (Vcons _ a _ v0)).
stepl (R[*](@MVP_apply Q_as_CRing (S n) (@Sumx (cpoly_cring _) _ (fun i H => Bernstein _ (lt_n_Sm_le i m (lt_le_trans _ _ _ H (le_refl _))))) (Vcons _ a _ v0))).
 fold (MultivariatePolynomial Q_as_CRing n).
 unfold L, R; clear L R.
 generalize (le_refl (S m)).
 revert b.
 generalize (S m) at 1 2 4 5 6 7 10.
 induction b; intros l.
  simpl.
  rewrite zero_MVP_apply.
  apply Qle_refl.
 simpl (vector_rec (MultivariatePolynomial Q_as_CRing n)
  (fun (n2 : nat) (_ : vector (MultivariatePolynomial Q_as_CRing n) n2) => Q)
  0
  (fun (c : MultivariatePolynomial Q_as_CRing n) (n2 : nat)
     (_ : vector (MultivariatePolynomial Q_as_CRing n) n2) (rec : Q) =>
   Qmin (MVP_apply Q_as_CRing c v0) rec) (S n1)
  (Vcons (MultivariatePolynomial Q_as_CRing n) a0 n1 b)).
 simpl (evalBernsteinBasisH (MultivariatePolynomial Q_as_CRing n)
   (Vcons (MultivariatePolynomial Q_as_CRing n) a0 n1 b) l).
 simpl (Sumx
     (fun (i : nat) (H : (i < S n1)%nat) =>
      Bernstein (MultivariatePolynomial Q_as_CRing n)
        (lt_n_Sm_le i m (lt_le_trans i (S n1) (S m) H l)))).
 do 2 rewrite MVP_plus_apply.
 rewrite (Qplus_comm (@MVP_apply Q_as_CRing (S n)
  (Sumx
     (fun (i : nat) (l0 : (i < n1)%nat) =>
      Bernstein (MultivariatePolynomial Q_as_CRing n)
        (lt_n_Sm_le i m (lt_le_trans i (S n1) (S m) (lt_S i n1 l0) l))))
  (Vcons Q a n v0))).
 rewrite Qmult_comm.
 rewrite Qmult_plus_distr_l.
 apply Qplus_le_compat; rewrite Qmult_comm; rewrite Qmin_mult_pos_distr_l.
    replace RHS with (MVP_apply Q_as_CRing a0 v0 *
  @MVP_apply Q_as_CRing (S n)
    (Bernstein (MultivariatePolynomial Q_as_CRing n)
       (lt_n_Sm_le n1 m (lt_le_trans n1 (S n1) (S m) (lt_n_Sn n1) l)))
    (Vcons Q a n v0)).
     apply Qmin_lb_l.
    simpl.
    rewrite <- (MVP_mult_apply Q_as_CRing).
    rapply MVP_apply_wd; try reflexivity.
    replace (lt_n_Sm_le n1 m (lt_le_trans n1 (S n1) (S m) (lt_n_Sn n1) l))
     with (le_S_n n1 m l) by apply le_irrelevent.
    apply _c_mult_apply.
   apply MVP_BernsteinNonNeg; auto.
  eapply Qle_trans;[apply Qmin_lb_r|].
  set (R:=vector_rec (MultivariatePolynomial Q_as_CRing n)
 (fun (n2 : nat) (_ : vector (MultivariatePolynomial Q_as_CRing n) n2) => Q)
 0
 (fun (c : MultivariatePolynomial Q_as_CRing n) (n2 : nat)
    (_ : vector (MultivariatePolynomial Q_as_CRing n) n2) (rec : Q) =>
  Qmin (MVP_apply Q_as_CRing c v0) rec) n1 b) in *.
  replace LHS with (R*@MVP_apply Q_as_CRing (S n)
   (Sumx
       (fun (i : nat) (l0 : (i < n1)%nat) =>
        Bernstein (MultivariatePolynomial Q_as_CRing n)
         (lt_n_Sm_le i m (lt_le_trans i n1 (S m) l0 (le_Sn_le _ _ l)))))
     (Vcons Q a n v0)).
   apply IHb.
  rapply mult_wdr.
  apply MVP_apply_wd; try reflexivity.
  apply Sumx_wd.
  intros i H.
  replace (lt_n_Sm_le i m (lt_le_trans i (S n1) (S m) (lt_S i n1 H) l))
   with (lt_n_Sm_le i m (lt_le_trans i n1 (S m) H (le_Sn_le n1 (S m) l))) by apply le_irrelevent.
  reflexivity.
 clear - Ha0 Ha1.
 induction n1.
  rewrite zero_MVP_apply.
  auto with *.
 simpl (Sumx
    (fun (i : nat) (l0 : (i < S n1)%nat) =>
     Bernstein (MultivariatePolynomial Q_as_CRing n)
       (lt_n_Sm_le i m (lt_le_trans i (S (S n1)) (S m) (lt_S i (S n1) l0) l)))).
 rewrite MVP_plus_apply.
 rapply plus_resp_nonneg.
  stepr (@MVP_apply Q_as_CRing (S n)
        (Sumx
           (fun (i : nat) (l0 : (i < n1)%nat) =>
            Bernstein (MultivariatePolynomial Q_as_CRing n)
              (lt_n_Sm_le i m (lt_le_trans i (S n1) (S m) (lt_S i n1 l0) (le_Sn_le _ _ l))))) (Vcons Q a n v0)).
   apply IHn1.
  apply MVP_apply_wd; try reflexivity.
  apply Sumx_wd.
  intros i H.
  replace (lt_n_Sm_le i m
    (lt_le_trans i (S n1) (S m) (lt_S i n1 H) (le_Sn_le (S n1) (S m) l)))
   with (lt_n_Sm_le i m
    (lt_le_trans i (S (S n1)) (S m) (lt_S i (S n1) (lt_S i n1 H)) l))
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
