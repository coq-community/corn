(*
Copyright © 2006 Russell O’Connor

Permission is hereby granted, free of charge, to any person obtaining a copy of
this proof and associated documentation files (the "Proof"), to deal in
the Proof without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Proof, and to permit persons to whom the Proof is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Proof.

THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
*)

Require Export CRIR.
Require Import QMinMax.

Definition CR_epsilon_sign_dec (e:Qpos) (x:CR) : comparison :=
let z := (approximate x e) in
 match (Qle_total z (2*e)) with
 | right p => Gt
 | left _ => 
  match (Qle_total (-(2)*e) z) with
  | right p => Lt
  | left _ => Eq
  end
 end.

Lemma CR_epsilon_sign_dec_pos : forall x, 
{e:Qpos | CR_epsilon_sign_dec e x = Gt } -> CRpos x.
Proof.
intros x [e H].
apply (@CRpos_char e).
abstract (
unfold CR_epsilon_sign_dec in H;
destruct (Qle_total (approximate x e) (2 * e)) as [A|A];
 [destruct (Qle_total (- (2) * e) (approximate x e)) as [B|B]; discriminate H|];
assumption).
Defined.

Ltac IR_dec_precompute := 
 try apply less_leEq;
 apply CR_less_as_IR;
 unfold CRlt;
 match goal with 
 | |- CRpos ?X => let X0 := fresh "IR_dec" in
                  set (X0:=X);
                  let XH := fresh "IR_dec" in
                  assert (XH:(X==X0)%CR) by reflexivity;
                  autorewrite with IRtoCR in XH;
                  unfold ms_id;
                  autorewrite with CRfast_compute in XH;
                  apply (CRpos_wd XH);
                  clear X0 XH
 end.

Ltac CR_solve_pos_loop e :=
 (exists e;
  vm_compute;
  match goal with 
  | |- Gt = Gt => reflexivity
  | |- Lt = Gt => fail 2 "CR number is negative"
  end)
 || CR_solve_pos_loop ((1#2)*e)%Qpos.

Ltac CR_solve_pos e :=
 repeat (match goal with 
 | H:_ |-_  => clear H
 end);
 match goal with 
 | H:_ |-_  => fail 1 "Context cannot be cleared"
 | |-_ => idtac
 end;
 apply CR_epsilon_sign_dec_pos;
 CR_solve_pos_loop e.

Ltac IR_solve_ineq e :=
 IR_dec_precompute; CR_solve_pos e.
