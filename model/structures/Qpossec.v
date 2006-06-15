(* $Id$ *)

(** printing Qpos $\mathbb{Q}^{+}$ #Q<SUP>+</SUP># *)

Require Export Qsec.
Require Import CLogic.

(** **About [Qpos]
We will prove some lemmas concerning rationals bigger than 0.

***Constants
One, two and four are all bigger than zero.
*)

Lemma pos_QONE : QZERO{<Q}QONE.
constructor.
Qed.

Lemma pos_QTWO : QZERO{<Q}QTWO.
constructor.
Qed.

Lemma pos_QFOUR : QZERO{<Q}QFOUR.
constructor.
Qed.

(** A positive rational is not zero.
*)

Definition pos_imp_nonzero : forall q : Q, (QZERO{<Q}q) -> ~(q{=Q}QZERO).
intros q X.
elim (Qlt_gives_apartness QZERO q).
intros H0 H1 H2.
set (i1 := Cinleft (QZERO{<Q}q) (q{<Q}QZERO) X) in *.
set (i2 := H1 i1) in *.
elim (ap_Q_tight0 q QZERO).
intros H3 H4.
elim (H4 H2).
generalize ap_Q_symmetric0.
intros H7.
exact (H7 QZERO q i2).
Qed.

(** ***Multiplication
The product of two positive rationals is again positive.
*)

Lemma Qmult_pres_pos0 : forall x y : Q, (QZERO{<Q}x) -> (QZERO{<Q}y) -> QZERO{<Q}x{*Q}y.
intros x y H H0.
apply Qmult_resp_pos_Qlt.
exact H.
exact H0.
Qed.

(** ***Inverse
The inverse of a positive rational is again positive.
*)

Lemma inv_pres_pos0 : forall x (H:QZERO{<Q}x), QZERO{<Q}Qinv x (pos_imp_nonzero x H).
intros x H.
unfold QZERO in |- *.
unfold Qlt in |- *.
simpl in |- *.
apply toCProp_Zlt.
rewrite Zmult_1_r.
unfold Qlt in H.
unfold QZERO in H.
generalize H.
simpl in |- *.
intro i.
set (i0 := CZlt_to 0 (num x * 1%positive) i) in *.
rewrite Zmult_1_r in i0.
generalize i0.
case (num x).
intuition.

unfold Zsgn in |- *.
rewrite Zmult_1_l.
intuition.

unfold Zsgn in |- *.
intros p H0.
intuition.
Qed.

(** ***Special multiplication
Now we will investigate the function $(x,y) \mapsto xy/2$#(x,y)
&#x21A6; xy/2#. We will see that its unit is 2. Its inverse map is $x
\mapsto 4/x$ #x &#x21A6; 4/x#.
*)

Lemma QTWOpos_is_rht_unit0 : forall x : Q, (QZERO{<Q}x) ->
 Qinv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}(x{*Q}QTWO){=Q}x.
intros x h.
apply
 trans_Qeq with ((Qinv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}QTWO){*Q}x).
apply
 trans_Qeq with (Qinv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}(QTWO{*Q}x)).
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
apply trans_Qeq with (QONE{*Q}x).
apply Qmult_simpl.
exact H1.
apply refl_Qeq.
cut (QONE{*Q}x{=Q}x{*Q}QONE).
intro H3.
apply trans_Qeq with (x{*Q}QONE).
exact H3.
apply Qmult_n_1.
apply Qmult_sym.
Qed.

Lemma QTWOpos_is_left_unit0 : forall x : Q, (QZERO{<Q}x) ->
 Qinv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}(QTWO{*Q}x){=Q}x.
intro x.
intro h.
apply
 trans_Qeq with ((Qinv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}QTWO){*Q}x). 
apply Qmult_assoc.
set (i1 := Qinv_is_inv) in *.
set (i2 := i1 QTWO (pos_imp_nonzero QTWO pos_QTWO)) in *.
elim i2.
intros H1 H2.
apply trans_Qeq with (QONE{*Q}x).
apply Qmult_simpl.
exact H1.
apply refl_Qeq.
apply trans_Qeq with (x{*Q}QONE).
apply Qmult_sym.
apply Qmult_n_1.
Qed.

Lemma multdiv2_is_inv : forall x (H : QZERO{<Q}x),
 (Qinv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}
  (x{*Q}(QFOUR{*Q}Qinv x (pos_imp_nonzero x H))){=Q}QTWO) /\
 (Qinv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}
  ((QFOUR{*Q}Qinv x (pos_imp_nonzero x H)){*Q}x){=Q}QTWO).
intros x scs_prf.
split.
apply
 trans_Qeq
  with
    (Qinv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}
     (x{*Q}(Qinv x (pos_imp_nonzero x scs_prf){*Q}QFOUR))).
apply Qmult_simpl.
apply refl_Qeq.
apply Qmult_simpl.
apply refl_Qeq.
apply Qmult_sym.
apply
 trans_Qeq
  with
    (Qinv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}
     ((x{*Q}Qinv x (pos_imp_nonzero x scs_prf)){*Q}QFOUR)).
apply Qmult_simpl.
apply refl_Qeq.
apply Qmult_assoc.
apply
 trans_Qeq
  with (Qinv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}(QONE{*Q}QFOUR)).
apply Qmult_simpl.
apply refl_Qeq.
apply Qmult_simpl.
set (i0 := Qinv_is_inv) in *.
elim (i0 x (pos_imp_nonzero x scs_prf)).
intuition.
apply refl_Qeq.
unfold Qmult in |- *.
unfold QTWO in |- *. 
unfold QONE in |- *.
unfold QFOUR in |- *.
unfold Qeq in |- *.
simpl in |- *.
intuition.
apply
 trans_Qeq
  with
    (Qinv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}
     (QFOUR{*Q}(Qinv x (pos_imp_nonzero x scs_prf){*Q}x))).
apply Qmult_simpl.
apply refl_Qeq.
apply sym_Qeq.
apply Qmult_assoc.
apply
 trans_Qeq
  with (Qinv QTWO (pos_imp_nonzero QTWO pos_QTWO){*Q}(QFOUR{*Q}QONE)). 
apply Qmult_simpl.
apply refl_Qeq.
apply Qmult_simpl.
apply refl_Qeq.
set (i0 := Qinv_is_inv) in *. 
elim (i0 x (pos_imp_nonzero x scs_prf)).
intuition.
unfold Qmult in |- *.
unfold QTWO in |- *. 
unfold QONE in |- *.
unfold QFOUR in |- *.
unfold Qeq in |- *.
simpl in |- *.
intuition.
Qed.

