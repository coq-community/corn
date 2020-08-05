(*
Copyright © 2020 Vincent Semeria

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*)


(** Proof that CoRN's faster reals implement the standard library's
    interface ConstructiveReals. *)

Require Import Coq.Reals.Abstract.ConstructiveReals.
Require Import CoRN.reals.faster.ARArith.
Require Import CoRN.metric2.Metric.
Require Import CoRN.metric2.Complete.
Require Import CoRN.metric2.MetricMorphisms.
Require Import CoRN.model.metric2.Qmetric.
Require Import CoRN.reals.fast.CRArith.
Require Import ConstructiveFastReals.


Context {AQ : Set} `{AppRationals AQ}.

Lemma ARlt_linear : @isLinearOrder (RegularFunction (Eball (cast AQ Q))) ARlt.
Proof.
  destruct ARfpsro, full_pseudo_srorder_pso.
  destruct pseudo_srorder_strict.
  split. split.
  - intros x y H H0.
    exact (pseudo_order_antisym x y (conj H H0)).
  - intros.
    apply AR_lt_ltT, (ARtoCR_preserves_ltT x z).
    apply AR_lt_ltT, (ARtoCR_preserves_ltT x y) in H5.
    apply AR_lt_ltT, (ARtoCR_preserves_ltT y z) in H6.
    apply (CRlt_trans _ _ _ H5 H6). 
  - intros x y z H.
    destruct (CRlt_linear (cast AR CR x) (cast AR CR y) (cast AR CR z)).
    apply (ARtoCR_preserves_ltT x z), AR_lt_ltT, H.
    left. apply AR_lt_ltT, (ARtoCR_preserves_ltT x y), c.
    right. apply AR_lt_ltT, (ARtoCR_preserves_ltT y z), c.
Qed.

Lemma ARlt_or_epsilon : forall a b c d : RegularFunction (Eball (cast AQ Q)),
       ARlt a b \/ ARlt c d -> ARlt a b + ARlt c d.
Proof.
  intros. destruct (CRlt_or_epsilon (cast AR CR a) (cast AR CR b)
                                    (cast AR CR c) (cast AR CR d)).
  - destruct H5. left.
    apply CR_lt_ltT, (ARtoCR_preserves_ltT a b), AR_lt_ltT. exact H5.
    right.
    apply CR_lt_ltT, (ARtoCR_preserves_ltT c d), AR_lt_ltT. exact H5.
  - left.
    apply AR_lt_ltT, (ARtoCR_preserves_ltT a b). exact c0.
  - right.
    apply AR_lt_ltT, (ARtoCR_preserves_ltT c d). exact c0. 
Qed.

Definition FasterRealsConstructive : ConstructiveReals.
Proof.
  pose proof (Build_ConstructiveReals
                (RegularFunction (Eball (cast AQ Q)))
                ARlt ARlt_linear ARlt
                (fun x y H => H) (fun x y H => H)
                ARlt_or_epsilon). 
Admitted.
