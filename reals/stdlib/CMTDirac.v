(*
Copyright © 2020 Vincent Semeria

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*)


(** Dirac measure at zero. *)

Require Import QArith.
Require Import ConstructiveReals.
Require Import ConstructiveLimits.
Require Import ConstructiveAbs.
Require Import ConstructiveMinMax.
Require Import ConstructivePartialFunctions.
Require Import CMTbase.

Local Open Scope ConstructiveReals.

(* The elementary functions for the Dirac measure
   are the functions defined at 0. *)
Definition DiracElemFunc {R : ConstructiveReals}
  : FunctionRieszSpace.
Proof.
  apply (Build_FunctionRieszSpace
           (CRcarrier R) R (fun f => Domain f 0)).
  - intros. destruct H, p. exact (d _ H0).
  - intros. split; assumption.
  - intros. exact H.
  - intros. exact H.
  - intros. exact H.
Defined.

Definition DiracOneFunc {R : ConstructiveReals}
  : @PartialFunction R (CRcarrier R)
  := Build_PartialFunctionXY
       (CRcarrier R) (CRcarrier R) (CReq R)
       (fun x => x == 0)
       (fun x xD => 1)
       (fun x p q => CReq_refl _).

Definition DiracIntegrationSpace {R : ConstructiveReals}
  : IntegrationSpace.
Proof.
  apply (Build_IntegrationSpace
           DiracElemFunc
           (fun f fL => partialApply f 0 fL) (* Dirac elementary integral *)
           (fun f g fL gL => CReq_refl _)
           (fun a f fL => CReq_refl _)
           DiracOneFunc
           (@CReq_refl R _)).
  - reflexivity.
  - intros f fn fL fnL fnNonNeg H.
    exists (Build_CommonPointFunSeq
         R _ f fn 0 fL fnL).
    simpl. exact H.
  - split.
    + intros p.
      destruct (CRup_nat (partialApply f 0 fL)) as [n H].
      exists n. intros. unfold XminConst, Xop, partialApply.
      rewrite (DomainProp _ _ _ fL), CRmin_left.
      rewrite CRabs_right. unfold CRminus. rewrite CRplus_opp_r.
      apply CR_of_Q_le. discriminate.
      unfold CRminus. rewrite CRplus_opp_r. apply CRle_refl.
      apply (CRle_trans _ (CR_of_Q R (Z.of_nat n # 1))).
      apply CRlt_asym, H. apply CR_of_Q_le.
      unfold Qle. simpl. do 2 rewrite Z.mul_1_r.
      apply Nat2Z.inj_le, H0.
    + intros p. exists (Pos.to_nat p). intros.
      unfold CRminus. rewrite CRopp_0, CRplus_0_r.
      rewrite CRabs_right.
      apply (CRle_trans _ (CR_of_Q R (1 # Pos.of_nat (S i)))).
      apply CRmin_r. apply CR_of_Q_le.
      unfold Qle, Qnum, Qden.
      do 2 rewrite Z.mul_1_l. apply Pos2Z.pos_le_pos, Pos2Nat.inj_le.
      rewrite Nat2Pos.id. apply (Nat.le_trans _ _ _ H).
      apply le_S, Nat.le_refl. discriminate.
      apply CRmin_glb. apply CRabs_pos.
      apply CR_of_Q_le. discriminate.
Defined.
