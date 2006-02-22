(* $Id: CMetricFields.v,v 1.6 2004/04/23 10:01:03 lcf Exp $ *)

Require Export CReals1.

Section CMetric_Fields.

(** *Metric Fields *)

Record is_CMetricField (F : CField) (abs : CSetoid_fun F IR) : Prop := 
  {ax_abs_gt_zero   : forall x : F, Zero [<=] abs x;
   ax_abs_resp_mult : forall x y : F, abs (x[*]y) [=] abs x[*]abs y;
   ax_abs_triangle  : forall x y : F, abs (x[+]y) [<=] abs x[+]abs y}.

Record CMetricField : Type := 
  {cmf_crr   :> CField;
   cmf_abs   :  CSetoid_fun cmf_crr IR;
   cmf_proof :  is_CMetricField cmf_crr cmf_abs}.

End CMetric_Fields.

Notation MAbs := (cmf_abs _).
Section basics.

Lemma MAbs_one : forall F : CMetricField,
 {MAbs (One:F) [=] Zero} + {MAbs (One:F) [=] One}.
intro F.
apply square_id.
astepl (cmf_abs F One[*]cmf_abs F One).
astepl (cmf_abs F (One[*]One)).
astepl (cmf_abs F One).
apply eq_reflexive.
apply ax_abs_resp_mult.
apply cmf_proof.
Qed.

Lemma MAbs_one_recip_one : forall F : CMetricField,
 MAbs (One:F) [=] MAbs ( [--]One:F).
intro F.
cut ({cmf_abs F (One:F) [=] Zero} + {cmf_abs F (One:F) [=] One}).
intro H.
elim H.
intro H2.
astepl ZeroR.
astepr (cmf_abs F ( [--]One[*]One)).
astepr (cmf_abs F [--]One[*]cmf_abs F One).
astepr (cmf_abs F [--]One[*]Zero).
astepr ZeroR.
apply eq_reflexive_unfolded.

apply eq_symmetric_unfolded.
apply ax_abs_resp_mult.

apply cmf_proof.

intro H1.
cut
 (cmf_abs F [--]One [=] cmf_abs F One
  or cmf_abs F [--]One [=] [--] (cmf_abs F One)).
intro H2.
elim H2.
intro H3.
apply eq_symmetric_unfolded.
exact H3.

intro H3.

(* begin hide *)
Lemma Hulp :
 forall F : CMetricField,
 cmf_abs F One [=] One -> cmf_abs F [--]One [=] [--] (cmf_abs F One) -> False.
intros F G H.
set (H0 := ax_abs_gt_zero) in *.
generalize H0.
unfold leEq in |- *.
intro H1.
set (H2 := H1 F (cmf_abs F) (cmf_proof F) [--] (One:F)) in *.
apply H2.
astepl ( [--] (cmf_abs F One)).
astepl ( [--]OneR).
apply plus_cancel_less with OneR.
astepl ZeroR.
astepr OneR.
apply pos_one.
Qed.
(* begin hide *)
simpl in |- *.
set (H4 := Hulp F H1 H3) in *.
intuition.

apply cond_square_eq.
apply ap_symmetric_unfolded.
apply less_imp_ap.
apply pos_two.

astepl OneR.
Algebra.

astepl (cmf_abs F [--]One[*]cmf_abs F [--]One).
astepl (cmf_abs F ( [--]One[*][--]One)).
2: apply ax_abs_resp_mult.
2: apply cmf_proof.

astepl (cmf_abs F One).
2: apply csf_wd.
2: astepl ( [--] ((One:F) [*][--]One)).
2: astepl ( [--] ( [--] (One:F) [*]One)).
2: astepl ( [--][--] ((One:F) [*]One)).
2: astepl ((One:F) [*]One).
2: Algebra.

astepl (cmf_abs F (One[*]One)).
astepl (cmf_abs F One[*]cmf_abs F One).
2: apply eq_symmetric_unfolded.
2: apply ax_abs_resp_mult.
2: apply cmf_proof.

astepr (cmf_abs F One[*]cmf_abs F One).
apply eq_reflexive_unfolded.

rational.

apply MAbs_one.
Qed.
(* end hide *)

End basics.
Section CMetric_Field_Cauchy.
Variable F : CMetricField.

(**
%\begin{convention}% Let [F:CMetricField].
%\end{convention}%
*)

Definition MCauchy_prop (g : nat -> F) : CProp := forall e : IR,
  Zero [<] e -> {N : nat | forall m, N <= m -> MAbs (g m[-]g N) [<=] e}.

Record MCauchySeq : Type := 
 {MCS_seq   :> nat -> F;
  MCS_proof :  MCauchy_prop MCS_seq}.

Definition MseqLimit (seq : nat -> F) (lim : F) : CProp := forall e : IR,
  Zero [<] e -> {N : nat | forall m, N <= m -> MAbs (seq m[-]lim) [<=] e}.

Definition is_MCauchyCompl (lim : MCauchySeq -> F) : CProp :=
  forall (s : MCauchySeq), MseqLimit s (lim s).

End CMetric_Field_Cauchy.

Implicit Arguments MseqLimit [F].
