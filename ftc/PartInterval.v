(* $Id: PartInterval.v,v 1.6 2004/04/23 10:01:00 lcf Exp $ *)

Require Export IntervalFunct.

Section Conversion.

(** *Correspondence

In this file we prove that there are mappings going in both ways
between the set of partial functions whose domain contains
[[a,b]] and the set of real-valued functions with domain on
that interval.  These mappings form an adjunction, and thus they have
all the good properties for preservation results.

**Mappings

We begin by defining the map from partial functions to setoid
functions as simply being the restriction of the partial function to
the interval [[a,b]].

%\begin{convention}% Let [F] be a partial function and [a,b:IR] such
that [I [=] [a,b]] is included in the domain of [F].
%\end{convention}%
*)

Variable F : PartIR.
Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := compact a b Hab.
(* end hide *)

Hypothesis Hf : included I (Dom F).

Lemma IntPartIR_strext : fun_strext
 (fun x : subset I => F (scs_elem _ _ x) (Hf _ (scs_prf _ _ x))).
red in |- *; intros x y H.
generalize (pfstrx _ _ _ _ _ _ H).
case x; case y; auto.
Qed.

Definition IntPartIR : CSetoid_fun (subset I) IR.
apply
 Build_CSetoid_fun
  with
    (fun x : subset I =>
     Part F (scs_elem _ _ x) (Hf (scs_elem _ _ x) (scs_prf _ _ x))).
exact IntPartIR_strext.
Defined.

End Conversion.

Implicit Arguments IntPartIR [F a b Hab].

Section AntiConversion.

(**
To go the other way around, we simply take a setoid function [f] with
domain [[a,b]] and build the corresponding partial function.
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := compact a b Hab.
(* end hide *)

Variable f : CSetoid_fun (subset I) IR.

Lemma PartInt_strext : forall x y Hx Hy,
 f (Build_subcsetoid_crr IR _ x Hx) [#] f (Build_subcsetoid_crr IR _ y Hy) -> x [#] y.
intros x y Hx Hy H.
exact (csf_strext_unfolded _ _ _ _ _ H).
Qed.

Definition PartInt : PartIR.
apply
 Build_PartFunct
  with (pfpfun := fun (x : IR) Hx => f (Build_subcsetoid_crr IR _ x Hx)).
exact (compact_wd _ _ _).
exact PartInt_strext.
Defined.

End AntiConversion.

Implicit Arguments PartInt [a b Hab].

Section Inverses.

(**
In one direction these operators are inverses.
*)

Lemma int_part_int : forall a b Hab F (Hf : included (compact a b Hab) (Dom F)),
 Feq (compact a b Hab) F (PartInt (IntPartIR Hf)).
intros; FEQ.
Qed.

End Inverses.

Section Equivalences.

(** **Mappings Preserve Operations

We now prove that all the operations we have defined on both sets are
preserved by [PartInt].

%\begin{convention}% Let [F,G] be partial functions and [a,b:IR] and
denote by [I] the interval [[a,b]].  Let [f,g] be setoid functions of
type [I->IR] equal respectively to [F] and [G] in [I].
%\end{convention}%
*)

Variables F G : PartIR.
Variables a b c : IR.
Hypothesis Hab : a [<=] b.
(* begin hide *)
Let I := compact a b Hab.
(* end hide *)

Variables f g : CSetoid_fun (subset (compact a b Hab)) IR.

Hypothesis Ff : Feq I F (PartInt f).
Hypothesis Gg : Feq I G (PartInt g).

Lemma part_int_const : Feq I [-C-]c (PartInt (IConst (Hab:=Hab) c)).
apply eq_imp_Feq.
red in |- *; simpl in |- *; intros; auto.
unfold I in |- *; apply included_refl.
intros; simpl in |- *; algebra.
Qed.

Lemma part_int_id : Feq I FId (PartInt (IId (Hab:=Hab))).
apply eq_imp_Feq.
red in |- *; simpl in |- *; intros; auto.
unfold I in |- *; apply included_refl.
intros; simpl in |- *; algebra.
Qed.

Lemma part_int_plus : Feq I (F{+}G) (PartInt (IPlus f g)).
elim Ff; intros incF Hf.
elim Hf; clear Ff Hf; intros incF' Hf.
elim Gg; intros incG Hg.
elim Hg; clear Gg Hg; intros incG' Hg.
apply eq_imp_Feq.
Included.
Included.
intros; simpl in |- *; simpl in Hf, Hg.
simpl in |- *; algebra.
Qed.

Lemma part_int_inv : Feq I {--}F (PartInt (IInv f)).
elim Ff; intros incF Hf.
elim Hf; clear Ff Hf; intros incF' Hf.
apply eq_imp_Feq.
Included.
Included.
intros; simpl in |- *; simpl in Hf.
simpl in |- *; algebra.
Qed.

Lemma part_int_minus : Feq I (F{-}G) (PartInt (IMinus f g)).
elim Ff; intros incF Hf.
elim Hf; clear Ff Hf; intros incF' Hf.
elim Gg; intros incG Hg.
elim Hg; clear Gg Hg; intros incG' Hg.
apply eq_imp_Feq.
Included.
Included.
intros; simpl in |- *; simpl in Hf, Hg.
simpl in |- *; algebra.
Qed.

Lemma part_int_mult : Feq I (F{*}G) (PartInt (IMult f g)).
elim Ff; intros incF Hf.
elim Hf; clear Ff Hf; intros incF' Hf.
elim Gg; intros incG Hg.
elim Hg; clear Gg Hg; intros incG' Hg.
apply eq_imp_Feq.
Included.
Included.
intros; simpl in |- *; simpl in Hf, Hg.
simpl in |- *; algebra.
Qed.

Lemma part_int_nth : forall n : nat, Feq I (F{^}n) (PartInt (INth f n)).
intro.
elim Ff; intros incF Hf.
elim Hf; clear Ff Hf; intros incF' Hf.
apply eq_imp_Feq.
Included.
Included.
intros; simpl in |- *; simpl in Hf.
astepl (Part F x Hx[^]n); astepr (f (Build_subcsetoid_crr IR _ x Hx')[^]n).
apply nexp_wd; algebra.
Qed.

(* begin show *)
Hypothesis HG : bnd_away_zero I G.
Hypothesis Hg : forall x : subset I, g x [#] Zero.
(* end show *)

Lemma part_int_recip : Feq I {1/}G (PartInt (IRecip g Hg)).
elim Gg; intros incG Hg'.
elim Hg'; clear Gg Hg'; intros incG' Hg'.
apply eq_imp_Feq.
Included.
Included.
intros; simpl in Hg'; simpl in |- *; algebra.
Qed.

Lemma part_int_div : Feq I (F{/}G) (PartInt (IDiv f g Hg)).
elim Ff; intros incF Hf.
elim Hf; clear Ff Hf; intros incF' Hf.
elim Gg; intros incG Hg'.
elim Hg'; clear Gg Hg'; intros incG' Hg'.
apply eq_imp_Feq.
Included.
Included.
intros; simpl in Hf, Hg'; simpl in |- *.
algebra.
Qed.

End Equivalences.
