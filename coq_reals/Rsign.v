Require Import CoRN.coq_reals.Rreals_iso.
Require Import CoRN.reals.fast.CRsign.

Ltac R_dec_precompute :=
 try apply Rlt_le;
 apply R_lt_as_IR;
 match goal with
 | |- (Ccsr_rel ?A ?B ?X ?Y) =>
                  let X0 := fresh "R_dec" in
                  pose (X0:=X);
                  let Y0 := fresh "R_dec" in
                  pose (Y0:=Y);
                  change (Ccsr_rel A B X0 Y0);
                  let XH := fresh "R_dec" in
                  assert (XH:(X[=]X0)) by apply eq_reflexive;
                  let YH := fresh "R_dec" in
                  assert (YH:(Y[=]Y0)) by apply eq_reflexive;
                  autorewrite with RtoIR in XH, YH;
                  apply (fun z z0 => @Ccsr_wdl A B _ z _ z0 XH);
                  apply (fun z z0 => @Ccsr_wdr A B z _ _ z0 YH);
                  clear X0 Y0 XH YH
   end.

Ltac R_solve_ineq P :=
  R_dec_precompute; IR_solve_ineq P.
