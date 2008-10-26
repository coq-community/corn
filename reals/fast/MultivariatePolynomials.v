Require Import Bernstein.
Require Import CRing_Homomorphisms.
Require Import COrdFields2.
Require Export Qordfield.
Require Import QMinMax.
Require Import CornTac.
Require Import Qauto.
Require Import Qmetric.
Require Import Qabs.
Require Import ModulusDerivative.

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

End MultivariatePolynomial.

Add Parametric Morphism F n : (@MVP_apply F n) with signature (@st_eq (MultivariatePolynomial F n)) ==> (@eq _) ==> (@st_eq _) as MVP_apply_wd.
Proof.
induction n;
 intros x y Hxy z.
 assumption.
simpl.
apply IHn.
rewrite Hxy.
reflexivity.
Qed.

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
rewrite one_apply.
reflexivity.
Qed.

Lemma C_MVP_apply : forall F n q v, MVP_apply F (MVP_C_ F n q) v[=]q.
Proof.
induction v.
 reflexivity.
simpl.
rewrite _c_apply.
assumption.
Qed.

Lemma MVP_plus_apply: forall F n (p q : MultivariatePolynomial F n) v,
  MVP_apply F (p[+]q) v [=] MVP_apply F p v[+]MVP_apply F q v.
Proof.
induction v.
 reflexivity.
simpl.
rewrite plus_apply.
apply IHv.
Qed.

Lemma MVP_mult_apply: forall F n (p q : MultivariatePolynomial F n) v,
  MVP_apply F (p[*]q) v [=] MVP_apply F p v[*]MVP_apply F q v.
Proof.
induction v.
 reflexivity.
simpl.
rewrite mult_apply.
apply IHv.
Qed.

Lemma MVP_c_mult_apply: forall F n (p : MultivariatePolynomial F n) c v,
  MVP_apply F (MVP_C_ _ _ c[*]p) v[=]c[*]MVP_apply F p v.
Proof.
induction v.
 reflexivity.
simpl.
rewrite <- IHv.
rewrite _c_mult_apply.
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
intros F n v.
exists (MVP_apply_hom_csf F v).
  intros x y; rapply MVP_plus_apply.
 intros x y; rapply MVP_mult_apply.
rapply one_MVP_apply.
Defined.

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
Open Local Scope Q_scope.

Definition MVP_apply_modulus n (p:MultivariatePolynomial Q_as_CRing (S n)) :=
let p' := (_D_ p) in
Qscale_modulus (Qmax (MVP_upperBound (S n) p') (-(MVP_lowerBound (S n) p'))).

Lemma MVP_apply_modulus_correct : forall n (p:MultivariatePolynomial Q_as_CRing (S n)) x y e, 
 (0 <= x) -> (x <= 1) -> (0 <= y) -> (y <= 1) ->
 ball_ex (MVP_apply_modulus p e) x y -> 
 forall (v:vector Q n), UnitHyperInterval v -> ball e (MVP_apply _ p (Vcons _ x _ v):Q) (MVP_apply _ p (Vcons _ y _ v)).
intros n p x y e Hx0 Hx1 Hy0 Hy1 Hxy v Hv.
assert (Hx : (Qmax 0 (Qmin 1 x))==x).
 rewrite Qle_min_r in Hx1.
 rewrite Hx1.
 rewrite Qle_max_r in Hx0.
 rewrite Hx0.
 reflexivity.
assert (Hy : (Qmax 0 (Qmin 1 y))==y).
 rewrite Qle_min_r in Hy1.
 rewrite Hy1.
 rewrite Qle_max_r in Hy0.
 rewrite Hy0.
 reflexivity.
simpl.
rewrite <- Hx.
rewrite <- Hy.
unfold MVP_apply_modulus in Hxy.
set (c:=(Qmax (MVP_upperBound (S n) (_D_ p))
              (- MVP_lowerBound (S n) (_D_ p)))) in *.
set (fp:=cpoly_map (RHcompose _ _ _ (inj_Q_hom IR) (MVP_apply_hom _ v)) p).
apply (fun A B e => is_UniformlyContinuousD_Q (Some 0) (Some 1) (refl_equal _) (FPoly _ fp) (FPoly _ (_D_ fp)) (Derivative_poly _ _ _)
 (fun x => (MVP_apply _ p (Vcons _ x _ v))) A c B e x y);
 try assumption.
 unfold fp.
 simpl.
 intros q _ _.
 clear - p.
 change (inj_Q_hom IR (MVP_apply_hom Q_as_CRing v p ! (MVP_C_ Q_as_CRing n q))[=]
   (cpoly_map (RHcompose (MultivariatePolynomial Q_as_CRing n) Q_as_CRing IR
      (inj_Q_hom IR) (MVP_apply_hom Q_as_CRing v)) p) ! (inj_Q_hom IR q)).
 rewrite cpoly_map_compose.
 rewrite <- cpoly_map_apply.
 rapply inj_Q_wd.
 rewrite cpoly_map_apply.
 apply csbf_wd; try reflexivity.
 rapply C_MVP_apply.
simpl.
clear - c Hv.
intros x _ [H0x Hx1].
change (AbsIR
  (_D_
     (cpoly_map
        (RHcompose (MultivariatePolynomial Q_as_CRing n) Q_as_CRing IR
           (inj_Q_hom IR) (MVP_apply_hom Q_as_CRing v)) p)) ! (inj_Q_hom IR x)[<=]
   inj_Q IR c).
rewrite <- cpoly_map_diff.
rewrite cpoly_map_compose.
rewrite <- cpoly_map_apply.
change (AbsIR (inj_Q IR (cpoly_map (MVP_apply_hom Q_as_CRing v) (_D_ p)) ! x)[<=]inj_Q IR c).
rewrite AbsIR_Qabs.
apply inj_Q_leEq.
assert (Hx: 0 <= x <= 1).
 split;
  apply (leEq_inj_Q IR).
  rewrite inj_Q_Zero.
  rstepl (Zero[/]Zero[+]One[//]den_is_nonzero IR 0); auto.
 rewrite inj_Q_One.
 rstepr (One[/]Zero[+]One[//]den_is_nonzero IR 1); auto.
setoid_replace ((cpoly_map (MVP_apply_hom Q_as_CRing v) (_D_ p)) ! x)
 with (@MVP_apply Q_as_CRing (S n) (_D_ p) (Vcons _ x _ v)).
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
rewrite cpoly_map_apply.
simpl.
rewrite C_MVP_apply.
reflexivity.
Qed.

Open Scope uc_scope.

Definition Qclamp01 := QboundBelow_uc (0) ∘ QboundAbove_uc 1.

Lemma Qclamp01_clamped : forall x, 0 <= Qclamp01 x <= 1.
Proof.
intros x.
unfold Qclamp01.
split; simpl.
 apply Qmax_ub_l.
rewrite Qmax_min_distr_r.
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
  rewrite Qabs_neg.
   intros He.
   rewrite Qabs_neg.
    replace LHS with (Qclamp01 y - Qclamp01 x) by ring.
    apply H; auto.
    replace LHS with (- (x-y)) by ring.
    auto.
   apply (shift_minus_leEq Q_as_COrdField).
   stepr (Qclamp01 y) by (simpl; ring).
   apply Qclamp01_le.
   auto.
  apply (shift_minus_leEq Q_as_COrdField).
  stepr y by (simpl; ring).
  auto. 
 rewrite Qabs_pos.
  intros He.
  rewrite Qabs_pos.
   apply H; auto.
  rapply shift_zero_leEq_minus.
  apply Qclamp01_le.
  auto.
 rapply shift_zero_leEq_minus.
 auto.
intros x y Hxy He.
simpl.
apply (Qmin_case 1 y).
 intros Hy.
 assert (Hx:=Qle_trans _ _ _ Hy Hxy).
 rewrite Qle_min_l in Hx.
 rewrite Hx.
 replace LHS with  0 by ring.
 eapply Qle_trans;[|apply He].
 rapply shift_zero_leEq_minus; auto.
apply (Qmin_case 1 x).
 intros Hx Hy.
 eapply Qle_trans;[|apply He].
 apply Qplus_le_compat; auto.
 apply Qopp_le_compat.
 apply Qmax_ub_r.
intros _ _.
apply (Qmax_case 0 x); intros Hx.
 assert (Hy:=Qle_trans _ _ _ Hxy Hx).
 rewrite Qle_max_l in Hy.
 rewrite Hy.
 eapply Qle_trans;[|apply He].
 rapply shift_zero_leEq_minus; auto.
apply (Qmax_case 0 y); intros Hy.
 eapply Qle_trans;[|apply He].
 apply Qplus_le_compat; auto with *.
auto.
Qed.

Fixpoint n_UniformlyContinuousFunction (X Y:MetricSpace) (n:nat) :=
match n with
|O => Y
|S n' => X --> (n_UniformlyContinuousFunction X Y n')
end.

Fixpoint MVP_uc_sig (n:nat) :MultivariatePolynomial Q_as_CRing n -> n_UniformlyContinuousFunction Q_as_MetricSpace Q_as_MetricSpace n -> Type :=
match n return MultivariatePolynomial Q_as_CRing n -> n_UniformlyContinuousFunction Q_as_MetricSpace Q_as_MetricSpace n -> Type with
| O => fun p x => p==x
| (S n') => fun p f => forall v, MVP_uc_sig n' (p ! (MVP_C_ Q_as_CRing _ (Qclamp01 v))) (f v)
end.

Definition MVP_uc : forall n (p:MultivariatePolynomial Q_as_CRing n),
 {f:n_UniformlyContinuousFunction Q_as_MetricSpace Q_as_MetricSpace n
 |MVP_uc_sig _ p f}.
induction n.
 intros x.
 exists x.
 simpl.
 reflexivity.
intros p.
assert (is_UniformlyContinuousFunction (fun (x:Q_as_CRing) => ProjT1 (IHn (p ! (MVP_C_ Q_as_CRing _ (Qclamp01 x))))) (MVP_apply_modulus p)).
 intros e x y Hxy.
 assert (Hxy' : ball_ex (MVP_apply_modulus p e) (Qclamp01 x) (Qclamp01 y)).
  destruct (MVP_apply_modulus p e); auto.
  simpl.
  rewrite Qball_Qabs.
  rapply Qclamp01_close.
  rewrite <- Qball_Qabs.
  auto.
 destruct (Qclamp01_clamped x) as [Hx0 Hx1].
 destruct (Qclamp01_clamped y) as [Hy0 Hy1].
 assert (X:=@MVP_apply_modulus_correct _ p (Qclamp01 x) (Qclamp01 y) e Hx0 Hx1 Hy0 Hy1 Hxy').
 clear Hxy Hxy'.
 generalize
        (proj2_sigT _  _ (IHn p ! (MVP_C_ Q_as_CRing n (Qclamp01 x))))
        (proj2_sigT _  _ (IHn p ! (MVP_C_ Q_as_CRing n (Qclamp01 y)))).
 set (x':=Qclamp01 x) in *.
 set (y':=Qclamp01 y) in *.
 simpl in X.
 revert X.
 generalize (ProjT1 (IHn p ! (MVP_C_ Q_as_CRing n x')))
            (ProjT1 (IHn p ! (MVP_C_ Q_as_CRing n y'))).
 change (Q_as_CSetoid) with (csg_crr Q_as_CRing).
 generalize (p ! (MVP_C_ Q_as_CRing n x'))
            (p ! (MVP_C_ Q_as_CRing n y')).
 clear - e.
 induction n.
  simpl.
  intros p q s t H Hs Ht.
  rewrite <- Hs, <- Ht.
  apply (H (Vnil _)).
  constructor.
 simpl.
 intros p q s t H Hs Ht v.
 apply (fun H => IHn _ _ _ _ H (Hs v) (Ht v)).
 intros v0 Hv0.
 apply (H (Vcons _ (Qclamp01 v) _ v0)).
 split; auto.
 apply Qclamp01_clamped.
exists (Build_UniformlyContinuousFunction H).
simpl.
intros v.
exact (ProjT2 (IHn p ! (MVP_C_ Q_as_CRing n (Qclamp01 v)))).
Defined.

Definition MVP_uc_Q := (fun n p => ProjT1 (MVP_uc n p)).

Fixpoint n_Cap X Y (plX : PrelengthSpace X) n : Complete (n_UniformlyContinuousFunction X Y n) -->
 n_UniformlyContinuousFunction (Complete X) (Complete Y) n :=
match n return Complete (n_UniformlyContinuousFunction X Y n) -->
 n_UniformlyContinuousFunction (Complete X) (Complete Y) n with
| O => uc_id _
| (S n') => (uc_compose_uc _ _ _ (@n_Cap X Y plX n')) ∘ (@Cap X _ plX)
end.

Definition n_Cmap X Y (plX : PrelengthSpace X) n : n_UniformlyContinuousFunction X Y n -->
 n_UniformlyContinuousFunction (Complete X) (Complete Y) n :=
(@n_Cap X Y plX n) ∘ (@Cunit _).

Definition MVP_uc_fun n (p:MultivariatePolynomial _ n) :
 n_UniformlyContinuousFunction CR CR n := 
n_Cmap _ QPrelengthSpace n (MVP_uc_Q n p).

