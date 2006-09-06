
Require Export IR_CPMSpace.

Section equivalent.
(** **Equivalent Pseudo Metric Spaces
*)
(**
We say that two pseudo metric spaces are equivalent, when there exists a 
bijective, structure-preserving function between them.
*)

Definition equivalent_psmetric (X : CSetoid) (d0 d1 : CSetoid_bin_fun X X IR)
  : CProp :=
  (is_CPsMetricSpace X d0 and is_CPsMetricSpace X d1)
  and {n : nat | forall x y : X, d0 x y[<=]nring (S n)[*]d1 x y}
      and {n : nat | forall x y : X, d1 x y[<=]nring (S n)[*]d0 x y}.

Definition isopsmetry (X Y : CPsMetricSpace) (f : CSetoid_fun X Y) :=
  bijective f
  and equivalent_psmetric X (cms_d (c:=X))
        (compose_CSetoid_bin_un_fun X Y IR (cms_d (c:=Y)) f).

Implicit Arguments isopsmetry [X Y].

Lemma isopsmetry_imp_bij :
 forall (X Y : CPsMetricSpace) (f : CSetoid_fun X Y),
 isopsmetry f -> bijective f.
intros X Y f H.
unfold isopsmetry in H.
elim H.
intuition.
Qed.

Lemma isopsmetry_imp_lipschitz :
 forall (X Y : CPsMetricSpace) (f : CSetoid_fun X Y),
 isopsmetry f -> lipschitz' f.
intros X Y f.
unfold isopsmetry in |- *.
unfold equivalent_psmetric in |- *.
intro H.
elim H. clear H.
intros H0 H1.
elim H1. clear H1.
intros H10 H11.
elim H11. clear H11.
intros H110 H111.
unfold lipschitz' in |- *.
elim H111. clear H111.
simpl in |- *.
intros n H111'.
exists (S n).
simpl in |- *.
exact H111'.
Qed.

Lemma id_is_isopsmetry : forall X : CPsMetricSpace, isopsmetry (id_un_op X).
intro X.
unfold isopsmetry in |- *.
split.
apply id_is_bij.
unfold equivalent_psmetric in |- *.
simpl in |- *.
unfold id_un_op in |- *.
split.
split.
apply CPsMetricSpace_is_CPsMetricSpace.
apply Build_is_CPsMetricSpace.
unfold com in |- *.
intros x y.
simpl in |- *.
apply ax_d_com.
apply CPsMetricSpace_is_CPsMetricSpace.
unfold nneg in |- *.
simpl in |- *.
apply ax_d_nneg.
apply CPsMetricSpace_is_CPsMetricSpace.
unfold pos_imp_ap in |- *.
simpl in |- *.
apply ax_d_pos_imp_ap.
apply CPsMetricSpace_is_CPsMetricSpace.
unfold tri_ineq in |- *.
simpl in |- *.
apply ax_d_tri_ineq.
apply CPsMetricSpace_is_CPsMetricSpace.
split.
exists 0.
intros x y.
simpl in |- *.
astepr (OneR[*](x[-d]y)).
astepr (x[-d]y).
apply leEq_reflexive.
exists 0.
intros x y.
simpl in |- *.
astepr (OneR[*](x[-d]y)).
astepr (x[-d]y).
apply leEq_reflexive.
Qed.

Lemma comp_resp_isopsmetry :
 forall (X Y Z : CPsMetricSpace) (f : CSetoid_fun X Y) (g : CSetoid_fun Y Z),
 isopsmetry f -> isopsmetry g -> isopsmetry (compose_CSetoid_fun X Y Z f g).
intros X Y Z f g.
unfold isopsmetry in |- *.
intros H0 H1.
elim H0.
intros H00 H01.
elim H1.
intros H10 H11.
split.
apply comp_resp_bij.
exact H00.
exact H10.
unfold equivalent_psmetric in |- *.
split.
split.
apply CPsMetricSpace_is_CPsMetricSpace.
unfold equivalent_psmetric in H01.
elim H01.
intros H010 H011.
elim H010.
intros H0100 H0101.
elim H11.
intros H110 H111.
elim H110.
intros H1100 H1101.
apply Build_is_CPsMetricSpace.
unfold com in |- *.
simpl in |- *.
intros x y.
elim H1101.
intros.
generalize ax_d_com.
unfold com in |- *.
simpl in |- *.
intro H2.
apply H2.
unfold nneg in |- *.
intros x y.
simpl in |- *.
elim H1101.
intros.
generalize ax_d_nneg.
unfold nneg in |- *.
simpl in |- *.
intro H2.
apply H2.

elim H1101.
intros.
generalize ax_d_pos_imp_ap.
unfold pos_imp_ap in |- *.
simpl in |- *.
intros H2 x y H3.
set (H5 := csf_strext X Y f) in *.
generalize H5.
unfold fun_strext in |- *.
intro H6.
apply H6.
auto.

unfold tri_ineq in |- *.
simpl in |- *.
intros x y z.
elim H1101.
intros.
generalize ax_d_tri_ineq.
unfold tri_ineq in |- *.
simpl in |- *.
intro H2.
apply H2.

split.
unfold equivalent_psmetric in H01.
elim H01.
intros H010 H011.
elim H011.
intros H0110 H0111.
unfold equivalent_psmetric in H11.
elim H11.
intros H110 H111.
elim H111.
intros H1110 H1111.
elim H0110.
simpl in |- *.
intros n H0110'.
elim H1110.
simpl in |- *.
intros m H1110'.
exists (S m * S n).
intros x y.
apply leEq_transitive with ((nring n[+]One)[*](f x[-d]f y)).
apply H0110'.
apply
 leEq_transitive
  with ((nring n[+]One)[*](nring m[+]One)[*](g (f x)[-d]g (f y))).
astepr ((nring n[+]One)[*]((nring m[+]One)[*](g (f x)[-d]g (f y)))).
apply mult_resp_leEq_lft.
apply H1110'.
apply less_leEq.
astepr (nring (R:=IR) (S n)).
apply pos_nring_S.
apply mult_resp_leEq_rht.
apply leEq_transitive with (nring (R:=IR) (S m * S n)).
apply eq_imp_leEq.
astepl (nring (R:=IR) (S n)[*](nring m[+]One)).
astepl (nring (R:=IR) (S n)[*]nring (S m)).
astepl (nring (R:=IR) (S m)[*]nring (S n)).
astepl (nring (R:=IR) (S m * S n)).
apply eq_reflexive.
astepr (nring (R:=IR) (S (S m * S n))).
apply less_leEq.
apply nring_less_succ.

apply ax_d_nneg.
apply CPsMetricSpace_is_CPsMetricSpace.


unfold equivalent_psmetric in H01.
elim H01.
intros H010 H011.
elim H011.
intros H0110 H0111.
unfold equivalent_psmetric in H11.
elim H11.
intros H110 H111.
elim H111.
intros H1110 H1111.
elim H0111.
simpl in |- *.
intros n H0111'.
elim H1111.
simpl in |- *.
intros m H1111'.
exists (S m * S n).
intros x y.
apply leEq_transitive with (nring (R:=IR) (S m)[*](f x[-d]f y)).
apply H1111'.
apply leEq_transitive with (nring (S m)[*]nring (S n)[*](x[-d]y)).
astepr (nring (S m)[*](nring (S n)[*](x[-d]y))).
apply mult_resp_leEq_lft.
apply H0111'.
apply less_leEq.
apply pos_nring_S.
apply mult_resp_leEq_rht.
apply leEq_transitive with (nring (R:=IR) (S m * S n)).
apply eq_imp_leEq.
astepl (nring (R:=IR) (S m * S n)).
apply eq_reflexive.
astepr (nring (R:=IR) (S (S m * S n))).
apply less_leEq.
apply nring_less_succ.

apply ax_d_nneg.
apply CPsMetricSpace_is_CPsMetricSpace.
Qed.

Lemma inv_isopsmetry :
 forall (X Y : CPsMetricSpace) (f : CSetoid_fun X Y) (H : isopsmetry f),
 isopsmetry (Inv f (isopsmetry_imp_bij X Y f H)).
intros X Y f H.
unfold isopsmetry in |- *.
split.
apply Inv_bij.
unfold isopsmetry in H.
unfold equivalent_psmetric in H.
elim H.
intros.
elim b.
intros.
elim a0.
intros.
elim b0.
intros.
unfold equivalent_psmetric in |- *.
split.
split.
apply CPsMetricSpace_is_CPsMetricSpace.
apply Build_is_CPsMetricSpace.
unfold com in |- *.
intros x y.
unfold Inv in |- *.
simpl in |- *.
apply ax_d_com.
exact a1.

unfold nneg in |- *.
intros x y.
unfold Inv in |- *.
simpl in |- *.
apply ax_d_nneg.
exact a1.

unfold pos_imp_ap in |- *.
intros x y.
unfold Inv in |- *.
simpl in |- *.
intro H7.
set (H6 := inv_strext) in *.
set
 (H5 :=
  H6 X Y f
    (isopsmetry_imp_bij X Y f
       (CAnd_intro _ _ a
          (CAnd_intro _ _ (CAnd_intro _ _ a1 b1) (CAnd_intro _ _ a2 b2)))))
 in *.
generalize H5.
unfold fun_strext in |- *.
intros H4.
apply H4.
set (H8 := ax_d_pos_imp_ap) in *.
set (H9 := H8 X (cms_d (c:=X)) a1) in *.
generalize H9.
unfold pos_imp_ap in |- *.
intro H10.
apply H10.
apply H7.

unfold tri_ineq in |- *.
unfold Inv in |- *.
simpl in |- *.
set (H3 := ax_d_tri_ineq) in *.
set (H4 := H3 X (cms_d (c:=X)) a1) in *.
generalize H4.
unfold tri_ineq in |- *.
intro H5.
intros x y z.
apply H5.

split.
elim b2.
simpl in |- *.
intros m P.
exists m.
intros y0 y1.
elim a.
intros. 
unfold surjective in b3.
elim (b3 y0).
intros x0 b4.
elim (b3 y1).
intros x1 b5.
astepl (f x0[-d]y1).
astepl (f x0[-d]f x1).
apply leEq_transitive with (nring (S m)[*](x0[-d]x1)).
simpl in |- *.
apply P.
simpl in |- *.
apply eq_imp_leEq.
apply mult_wdr.
set (H4 := csbf_wd) in *.
set (H5 := H4 X X IR (cms_d (c:=X))) in *.
generalize H5.
unfold bin_fun_wd in |- *.
intro H6.
apply H6.
cut
 (invfun f
    (isopsmetry_imp_bij X Y f
       (CAnd_intro _ _ (CAnd_intro _ _ a3 b3)
          (CAnd_intro _ _ (CAnd_intro _ _ a1 b1)
             (CAnd_intro _ _ a2
                (existT
                   (fun n : nat =>
                    forall x y : X, f x[-d]f y[<=](nring n[+]One)[*](x[-d]y))
                   m P))))) (f x0)[=]
  invfun f
    (isopsmetry_imp_bij X Y f
       (CAnd_intro _ _ (CAnd_intro _ _ a3 b3)
          (CAnd_intro _ _ (CAnd_intro _ _ a1 b1)
             (CAnd_intro _ _ a2
                (existT
                   (fun n : nat =>
                    forall x y : X, f x[-d]f y[<=](nring n[+]One)[*](x[-d]y))
                   m P))))) y0).
intros.
astepr
 (invfun f
    (isopsmetry_imp_bij X Y f
       (CAnd_intro _ _ (CAnd_intro _ _ a3 b3)
          (CAnd_intro _ _ (CAnd_intro _ _ a1 b1)
             (CAnd_intro _ _ a2
                (existT
                   (fun n : nat =>
                    forall x y : X, f x[-d]f y[<=](nring n[+]One)[*](x[-d]y))
                   m P))))) (f x0)).
apply eq_symmetric.
apply inv2.
set (H10 := csf_wd) in *.
set
 (H7 :=
  H10 Y X
    (Inv f
       (isopsmetry_imp_bij X Y f
          (CAnd_intro _ _ (CAnd_intro _ _ a3 b3)
             (CAnd_intro _ _ (CAnd_intro _ _ a1 b1)
                (CAnd_intro _ _ a2
                   (existT
                      (fun n : nat =>
                       forall x y : X,
                       f x[-d]f y[<=](nring n[+]One)[*](x[-d]y)) m P)))))))
 in *.
generalize H7.
unfold fun_wd in |- *.
unfold Inv in |- *.
simpl in |- *.
intro H8.
apply H8.
exact b4.

cut
 (invfun f
    (isopsmetry_imp_bij X Y f
       (CAnd_intro _ _ (CAnd_intro _ _ a3 b3)
          (CAnd_intro _ _ (CAnd_intro _ _ a1 b1)
             (CAnd_intro _ _ a2
                (existT
                   (fun n : nat =>
                    forall x y : X, f x[-d]f y[<=](nring n[+]One)[*](x[-d]y))
                   m P))))) (f x1)[=]
  invfun f
    (isopsmetry_imp_bij X Y f
       (CAnd_intro _ _ (CAnd_intro _ _ a3 b3)
          (CAnd_intro _ _ (CAnd_intro _ _ a1 b1)
             (CAnd_intro _ _ a2
                (existT
                   (fun n : nat =>
                    forall x y : X, f x[-d]f y[<=](nring n[+]One)[*](x[-d]y))
                   m P))))) y1).
intros.
astepr
 (invfun f
    (isopsmetry_imp_bij X Y f
       (CAnd_intro _ _ (CAnd_intro _ _ a3 b3)
          (CAnd_intro _ _ (CAnd_intro _ _ a1 b1)
             (CAnd_intro _ _ a2
                (existT
                   (fun n : nat =>
                    forall x y : X, f x[-d]f y[<=](nring n[+]One)[*](x[-d]y))
                   m P))))) (f x1)).
apply eq_symmetric.
apply inv2.
set (H10 := csf_wd) in *.
set
 (H7 :=
  H10 Y X
    (Inv f
       (isopsmetry_imp_bij X Y f
          (CAnd_intro _ _ (CAnd_intro _ _ a3 b3)
             (CAnd_intro _ _ (CAnd_intro _ _ a1 b1)
                (CAnd_intro _ _ a2
                   (existT
                      (fun n : nat =>
                       forall x y : X,
                       f x[-d]f y[<=](nring n[+]One)[*](x[-d]y)) m P)))))))
 in *.
generalize H7.
unfold fun_wd in |- *.
unfold Inv in |- *.
simpl in |- *.
intro H8.
apply H8.
exact b5.

elim a2.
simpl in |- *.
intros m P.
exists m.
intros y0 y1.
elim a.
intros. 
unfold surjective in b3.
elim (b3 y0).
intros x0 b4.
elim (b3 y1).
intros x1 b5.
astepr ((nring m[+]One)[*](f x0[-d]f x1)).
apply leEq_transitive with (x0[-d]x1).
2: apply P.
apply eq_imp_leEq.
set (H4 := csbf_wd) in *.
set (H5 := H4 X X IR (cms_d (c:=X))) in *.
generalize H5.
unfold bin_fun_wd in |- *.
intro H6.
apply H6.
cut
 (invfun f
    (isopsmetry_imp_bij X Y f
       (CAnd_intro _ _ (CAnd_intro _ _ a3 b3)
          (CAnd_intro _ _ (CAnd_intro _ _ a1 b1)
             (CAnd_intro _ _
                (existT
                   (fun n : nat =>
                    forall x y : X, x[-d]y[<=](nring n[+]One)[*](f x[-d]f y))
                   m P) b2)))) y0[=]
  invfun f
    (isopsmetry_imp_bij X Y f
       (CAnd_intro _ _ (CAnd_intro _ _ a3 b3)
          (CAnd_intro _ _ (CAnd_intro _ _ a1 b1)
             (CAnd_intro _ _
                (existT
                   (fun n : nat =>
                    forall x y : X, x[-d]y[<=](nring n[+]One)[*](f x[-d]f y))
                   m P) b2)))) (f x0)).
intros.
astepl
 (invfun f
    (isopsmetry_imp_bij X Y f
       (CAnd_intro _ _ (CAnd_intro _ _ a3 b3)
          (CAnd_intro _ _ (CAnd_intro _ _ a1 b1)
             (CAnd_intro _ _
                (existT
                   (fun n : nat =>
                    forall x y : X, x[-d]y[<=](nring n[+]One)[*](f x[-d]f y))
                   m P) b2)))) (f x0)).
apply inv2.
set (H10 := csf_wd) in *.
set
 (H7 :=
  H10 Y X
    (Inv f
       (isopsmetry_imp_bij X Y f
          (CAnd_intro _ _ (CAnd_intro _ _ a3 b3)
             (CAnd_intro _ _ (CAnd_intro _ _ a1 b1)
                (CAnd_intro _ _
                   (existT
                      (fun n : nat =>
                       forall x y : X,
                       x[-d]y[<=](nring n[+]One)[*](f x[-d]f y)) m P) b2))))))
 in *.
generalize H7.
unfold fun_wd in |- *.
unfold Inv in |- *.
simpl in |- *.
intro H8.
apply H8.
apply eq_symmetric.
exact b4.

cut
 (invfun f
    (isopsmetry_imp_bij X Y f
       (CAnd_intro _ _ (CAnd_intro _ _ a3 b3)
          (CAnd_intro _ _ (CAnd_intro _ _ a1 b1)
             (CAnd_intro _ _
                (existT
                   (fun n : nat =>
                    forall x y : X, x[-d]y[<=](nring n[+]One)[*](f x[-d]f y))
                   m P) b2)))) y1[=]
  invfun f
    (isopsmetry_imp_bij X Y f
       (CAnd_intro _ _ (CAnd_intro _ _ a3 b3)
          (CAnd_intro _ _ (CAnd_intro _ _ a1 b1)
             (CAnd_intro _ _
                (existT
                   (fun n : nat =>
                    forall x y : X, x[-d]y[<=](nring n[+]One)[*](f x[-d]f y))
                   m P) b2)))) (f x1)).
intros.
astepl
 (invfun f
    (isopsmetry_imp_bij X Y f
       (CAnd_intro _ _ (CAnd_intro _ _ a3 b3)
          (CAnd_intro _ _ (CAnd_intro _ _ a1 b1)
             (CAnd_intro _ _
                (existT
                   (fun n : nat =>
                    forall x y : X, x[-d]y[<=](nring n[+]One)[*](f x[-d]f y))
                   m P) b2)))) (f x1)).
apply inv2.
set (H10 := csf_wd) in *.
set
 (H7 :=
  H10 Y X
    (Inv f
       (isopsmetry_imp_bij X Y f
          (CAnd_intro _ _ (CAnd_intro _ _ a3 b3)
             (CAnd_intro _ _ (CAnd_intro _ _ a1 b1)
                (CAnd_intro _ _
                   (existT
                      (fun n : nat =>
                       forall x y : X,
                       x[-d]y[<=](nring n[+]One)[*](f x[-d]f y)) m P) b2))))))
 in *.
generalize H7.
unfold fun_wd in |- *.
unfold Inv in |- *.
simpl in |- *.
intro H8.
apply H8.
apply eq_symmetric.
exact b5.
Qed.

Definition MSequivalent (X Y : CPsMetricSpace) :=
  {f : CSetoid_fun X Y | isopsmetry f}.

(**
Not all pseudo metric spaces are equivalent:
*)

Lemma MSequivalent_discr :
 Not (MSequivalent IR_as_CPsMetricSpace (zf_as_CPsMetricSpace IR)).
red in |- *.
unfold MSequivalent in |- *.
unfold isopsmetry in |- *.
unfold equivalent_psmetric in |- *.
intros H0.
elim H0.
intros f H0'.
elim H0'.
intros H1 H2.
elim H2.
intros H3 H4.
elim H4.
intros H5 H6.
elim H5.
intros n.
simpl in |- *.
unfold zero_fun in |- *.
unfold dIR in |- *.
intro H7.
cut (OneR[<=]Zero).
unfold leEq in |- *.
intro H8.
set (H9 := H8 (pos_one IR)) in *.
exact H9.

astepr ((nring (R:=IR) n[+]One)[*]Zero).
astepl (ABSIR (One[-]Zero)).
apply H7.

unfold ABSIR in |- *.
astepl (Max [--](One[-]Zero) (One[-]Zero)).
astepl (Max [--](One[-]Zero) One).
apply leEq_imp_Max_is_rht.
astepl ([--]OneR).
astepl (ZeroR[-]One).
apply shift_minus_leEq.
astepr (Two:IR).
apply less_leEq.
apply pos_two.

apply Max_comm.
Qed.


End equivalent.