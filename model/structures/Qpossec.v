(* $Id$ *)


Require Export Qsec.
Require Import CLogic.

(** *About $\mathbb{Q}^{+}$ #Q<SUP>+</SUP>#
*)


(** We will prove some lemmas concerning rationals bigger than 0.
*)

(** **Constants
*)

(** One, two and four are all bigger than zero.
*)

Lemma pos_QONE : Q.ZERO{<Q}Q.ONE.
unfold Q.lt in |- *.
unfold Q.ZERO in |- *.
unfold Q.ONE in |- *.
simpl in |- *.
unfold Zlts in |- *.
constructor.
Qed.

Lemma pos_QTWO : Q.ZERO{<Q}QTWO.
unfold Q.lt in |- *.
unfold Q.ZERO in |- *.
unfold QTWO in |- *.
simpl in |- *.
unfold Zlts in |- *.
constructor.
Qed.

Lemma pos_QFOUR : Q.ZERO{<Q}QFOUR.
unfold Q.lt in |- *.
unfold Q.ZERO in |- *.
unfold QTWO in |- *.
simpl in |- *.
unfold Zlts in |- *.
constructor.
Qed.

(** A positive rational is not zero.
*)

Definition pos_imp_nonzero :
  forall q : Q.Q, (Q.ZERO{<Q}q) -> CNot (q{=Q}Q.ZERO).
intros q X.                                                            
unfold CNot in |- *.
set (i := Qlt_gives_apartness) in *.
generalize i.
unfold Iff in |- *.
intros i0.
clear i.
elim (i0 Q.ZERO q).
intros H0 H1 H2.
set (i1 := Cinleft (Q.ZERO{<Q}q) (q{<Q}Q.ZERO) X) in *.
set (i2 := H1 i1) in *.
set (i := ap_Q_tight0) in *.
generalize i.
intros i3.
elim (i3 q Q.ZERO).
intros H3 H4.
set (H5 := H4 H2) in *.
generalize H5.
unfold Not in |- *.
intro H6.
generalize ap_Q_symmetric0.
intros H7.
elim H6.
set (i8 := H7 Q.ZERO q i2) in *.
exact i8.
Qed.

(** **Multiplication
*)

(** The product of two positive rationals is again positive.
*)

Lemma Qmult_pres_pos0 :
 forall x y : Q.Q, (Q.ZERO{<Q}x) -> (Q.ZERO{<Q}y) -> Q.ZERO{<Q}x{*Q}y.
intros x y H H0.
apply Qmult_resp_pos_Qlt.
exact H.
exact H0.
Qed.

(** **Inverse
*)

(** The inverse of a positive rational is again positive.
*)

Lemma inv_pres_pos0 :
 forall (x : Q.Q) (H : Q.ZERO{<Q}x), Q.ZERO{<Q}Q.inv x (pos_imp_nonzero x H).
intros x H.
unfold Q.ZERO in |- *.
unfold Q.lt in |- *.
simpl in |- *.
apply toCProp_Zlt.
rewrite Zmult_1_r.
unfold Q.lt in H.
unfold Q.ZERO in H.
generalize H.
simpl in |- *.
intro i.
set (i0 := CZlt_to 0 (Q.num x * 1%positive) i) in *.
rewrite Zmult_1_r in i0.
generalize i0.
case (Q.num x).
intuition.

unfold Zsgn in |- *.
rewrite Zmult_1_l.
intuition.

unfold Zsgn in |- *.
intros p H0.
intuition.
Qed.

(** **Special multiplication
*)

(** Now we will investigate the function $(x,y) \mapsto xy/2$ #(x,y) &#x21A6; xy/2#. We will see that its unit is 2. Its inverse map is $x \mapsto 4/x$ #x &#x21A6; 4/x#.
*)

Lemma QTWOpos_is_rht_unit0 :
 forall x : Q.Q,
 (Q.ZERO{<Q}x) ->
 Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}(x{*Q}QTWO){=Q}x.
intros x h.
apply
 trans_Qeq with ((Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}QTWO){*Q}x).
apply
 trans_Qeq with (Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}(QTWO{*Q}x)).
apply Qmult_simpl.
apply refl_Qeq.
set (i := Qmult_sym) in *.
generalize i.
intuition.
apply Qmult_assoc.
set (i1 := Qinv_is_inv) in *.
set (i2 := i1 QTWO (pos_imp_nonzero QTWO pos_QTWO)) in *.
elim i2.
intros H1 H2.
apply trans_Qeq with (Q.ONE{*Q}x).
apply Qmult_simpl.
exact H1.
apply refl_Qeq.
cut (Q.ONE{*Q}x{=Q}x{*Q}Q.ONE).
intro H3.
apply trans_Qeq with (x{*Q}Q.ONE).
exact H3.
apply Qmult_n_1.
apply Qmult_sym.
Qed.

Lemma QTWOpos_is_left_unit0 :
 forall x : Q.Q,
 (Q.ZERO{<Q}x) ->
 Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}(QTWO{*Q}x){=Q}x.
intro x.
intro h.
apply
 trans_Qeq with ((Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}QTWO){*Q}x). 
apply Qmult_assoc.
set (i1 := Qinv_is_inv) in *.
set (i2 := i1 QTWO (pos_imp_nonzero QTWO pos_QTWO)) in *.
elim i2.
intros H1 H2.
apply trans_Qeq with (Q.ONE{*Q}x).
apply Qmult_simpl.
exact H1.
apply refl_Qeq.
apply trans_Qeq with (x{*Q}Q.ONE).
apply Qmult_sym.
apply Qmult_n_1.
Qed.




Lemma multdiv2_is_inv :
 forall (x : Q.Q) (H : Q.ZERO{<Q}x),
 (Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}
  (x{*Q}(QFOUR{*Q}Q.inv x (pos_imp_nonzero x H))){=Q}QTWO) /\
 (Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}
  ((QFOUR{*Q}Q.inv x (pos_imp_nonzero x H)){*Q}x){=Q}QTWO).
intros x scs_prf.
split.
apply
 trans_Qeq
  with
    (Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}
     (x{*Q}(Q.inv x (pos_imp_nonzero x scs_prf){*Q}QFOUR))).
apply Qmult_simpl.
apply refl_Qeq.
apply Qmult_simpl.
apply refl_Qeq.
apply Qmult_sym.
apply
 trans_Qeq
  with
    (Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}
     ((x{*Q}Q.inv x (pos_imp_nonzero x scs_prf)){*Q}QFOUR)).
apply Qmult_simpl.
apply refl_Qeq.
apply Qmult_assoc.
apply
 trans_Qeq
  with (Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}(Q.ONE{*Q}QFOUR)).
apply Qmult_simpl.
apply refl_Qeq.
apply Qmult_simpl.
set (i0 := Qinv_is_inv) in *.
elim (i0 x (pos_imp_nonzero x scs_prf)).
intuition.
apply refl_Qeq.
unfold Q.mult in |- *.
unfold QTWO in |- *. 
unfold Q.ONE in |- *.
unfold QFOUR in |- *.
unfold Q.eq in |- *.
simpl in |- *.
intuition.
apply
 trans_Qeq
  with
    (Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}
     (QFOUR{*Q}(Q.inv x (pos_imp_nonzero x scs_prf){*Q}x))).
apply Qmult_simpl.
apply refl_Qeq.
apply sym_Qeq.
apply Qmult_assoc.
apply
 trans_Qeq
  with (Q.inv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}(QFOUR{*Q}Q.ONE)). 
apply Qmult_simpl.
apply refl_Qeq.
apply Qmult_simpl.
apply refl_Qeq.
set (i0 := Qinv_is_inv) in *. 
elim (i0 x (pos_imp_nonzero x scs_prf)).
intuition.
unfold Q.mult in |- *.
unfold QTWO in |- *. 
unfold Q.ONE in |- *.
unfold QFOUR in |- *.
unfold Q.eq in |- *.
simpl in |- *.
intuition.
Qed.
