(* $Id: Tese_pfun.v,v 1.3 2004/03/31 09:13:40 lcf Exp $ *)

(** Alternative definitions of partial functions *)

Require Export CSetoidFun.

Record PartFunct' (S : CSetoid) : Type := 
  {dom : S -> CProp;
   dom_wd : pred_wd _ dom;
   fun_ :> CSetoid_fun (Build_SubCSetoid S dom) S}.

Definition map1 (S : CSetoid) : PartFunct S -> PartFunct' S.
intros S F.
inversion F.
apply Build_PartFunct' with pfdom.
auto.
apply
 Build_CSetoid_fun
  with
    (fun x : Build_SubCSetoid S pfdom =>
     pfpfun (scs_elem _ _ x) (scs_prf _ _ x)).
red in |- *; intros x y.
case x; case y; simpl in |- *; intros.
eauto.
Defined.

Definition map2 (S : CSetoid) : PartFunct' S -> PartFunct S.
intros S F.
inversion F.
inversion fun_0.
apply
 Build_PartFunct
  with
    dom0
    (fun (x : S) (Hx : dom0 x) => csf_fun (Build_subcsetoid_crr _ _ x Hx)).
auto.
intros.
apply (csf_strext _ _ X).
Qed.
