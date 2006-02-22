(* $Id: Zfinsetoid.v,v 1.1 2004/09/22 11:06:14 loeb Exp $ *)
Require Export ZArith.
Require Import CSetoids.

(** ** Setoids of the integers between 0 and [z]
*)

Record ZF (n:Z):Set:=
{ZF_crr:> Z ;
ZF_prf0: (Zlt  ZF_crr n);
ZF_prf1: (Zle 0 ZF_crr)
}.

Definition ZFeq (n : Z) : ZF n -> ZF n -> Prop.
intros n a b.
case a.
case b.
intros x H H' x0 H0 H0'.
exact (x = x0).
Defined.

Definition ZFap (n : Z) : ZF n -> ZF n -> CProp.
intros n a b.
case a.
case b.
intros x H H' x0 H0 H0'.
exact (x <> x0).
Defined.

Lemma ZFap_irreflexive : forall n : Z, irreflexive (ZFap n).
unfold irreflexive in |- *.
unfold ZFap in |- *.
intros n x.
case x.
intuition.
red in |- *.
intuition.
Qed.

Lemma ZFap_symmetric : forall n : Z, Csymmetric (ZFap n).
intro n.
unfold Csymmetric in |- *.
unfold ZFap in |- *.
intros x y.
case x.
case y.
intuition.
Qed.

Lemma ZFap_cotransitive : forall n : Z, cotransitive (ZFap n).
intro n.
unfold cotransitive in |- *.
unfold ZFap in |- *.
intros x y.
case x.
case y.
intros x0 H0 H0' x1 H1 H1' H2 z.
case z.
intros x2 H H'.
set (H5 := Z_eq_dec x2 x1) in *.
elim H5.
clear H5.
intro H5.
right.
rewrite H5.
exact H2.

clear H5.
intro H5.
left. 
exact H5.
Qed.

Lemma ZFap_tight : forall n : Z, tight_apart (ZFeq n) (ZFap n).
unfold tight_apart in |- *.
unfold ZFap in |- *.
unfold ZFeq in |- *.
intros n x y.
case x.
case y.
intros x0 H0 H0'x1 H1 H1'.
red in |- *.
unfold not in |- *.
unfold Not in |- *.
intuition.
Qed.

Definition Zless (n : Z) :=
  Build_is_CSetoid (ZF n) (ZFeq n) (ZFap n) (ZFap_irreflexive n)
    (ZFap_symmetric n) (ZFap_cotransitive n) (ZFap_tight n).

Definition ZCSetoid_of_less (n : Z) : CSetoid :=
  Build_CSetoid (ZF n) (ZFeq n) (ZFap n) (Zless n).
