(* $Id: Tese_tact.v,v 1.2 2004/02/11 13:20:40 lcf Exp $ *)

Require Export InvTrigonom.

Ltac Lazy_Included' :=
  repeat
   match goal with
   |  |- (included _ (Dom [-C-]_)) => apply included_IR
   |  |- (included _ (Dom FId)) => apply included_IR
   |  |- (included _ (Dom (_{+}_))) =>
       apply
        included_FPlus
         (*  | [{--}?3] -> Let t1=(pfunct_to_cont a b ?3) In '(cinv a b t1)
           | [?3{-}?4] -> Let t1=(pfunct_to_cont a b ?3) And t2=(pfunct_to_cont a b ?4) In '(cminus a b t1 t2)
           | [?3{*}?4] -> Let t1=(pfunct_to_cont a b ?3) And t2=(pfunct_to_cont a b ?4) In '(cmult a b t1 t2)
           | [?3{**}?4] -> Let t=(pfunct_to_cont a b ?4) In '(cscalmult a b ?3 t)
           | [?3{^}?4] -> Let t1=(pfunct_to_cont a b ?3) In '(cnth a b t1 ?4)
           | [(FAbs ?3)] -> Let t1=(pfunct_to_cont a b ?3) In '(cabs a b t1)
           | [?3] -> (Let t=?3 In (Match Context With
             [Hab:?;H:(!Continuous_I a b ?1 t)|-?] -> '(hyp_c a b ?1 t H)
             | [H:(!Derivative_I a b ?1 t ?4)|-?] -> '(hyp_d a b ?1 t ?4 H)
             | [H:(!Derivative_I a b ?1 ?4 t)|-?] -> '(hyp_d' a b ?1 ?4 t H)
             | [H:(!Diffble_I a b ?1 t)|-?] -> '(hyp_diff a b ?1 t H))). *)
   |  |- (included _ (Dom (_{/}_))) => apply included_FDiv
   |  |- (included _ (Dom (_[o]_))) => apply included_FComp
   end.

Section test.

Variables F G H : PartIR.

Goal included (fun _ : IR => True) (Dom (F{+}G)).
Lazy_Included'.
Abort.

Goal included (fun _ : IR => True) (Dom ((F{+}G)[o](F{/}FId{+}FId{/}F))).
Lazy_Included'.
Abort.

End test.

Ltac New_Contin' :=
  match goal with
  |  |- (Continuous_I (a:=?X1) (b:=?X2) ?X4 ?X3) =>
      let r := pfunct_to_cont X1 X2 X3 in
      (change (Continuous_I X4 (cont_to_pfunct X1 X2 r)) in |- *;
        apply continuous_cont)
  end.

Ltac New_Deriv' :=
  match goal with
  |  |- (Derivative_I (a:=?X1) (b:=?X2) ?X4 ?X3 ?X5) =>
      let r := pfunct_to_restr X1 X2 X3 in
      (change (Derivative_I X4 (deriv_to_pfunct X1 X2 r) X5) in |- *;
        apply Derivative_I_wdr with (deriv_deriv X1 X2 r);
        [ unfold deriv_deriv, deriv_to_pfunct in |- * | apply deriv_restr ])
  end.

Section testes.

Variables a b : IR.
Hypothesis Hab : a[<=]b.

Notation I := (compact a b Hab).

Variable F : PartIR.
Hypothesis contF : Continuous_I Hab F.

Goal Continuous_I Hab ((F{+}FId){*}[-C-]Two{^}3{-}Four{**}F).
New_Contin.
Abort.

Goal Continuous_I Hab ((F{+}FId){*}[-C-]Two{^}3{-}Four{**}F).
New_Contin'.
Abort.

Hypothesis H : ZeroR[<]One.

Hint Resolve included_imp_Derivative: derivate.

Goal Derivative_I H (Sine{^}2) (Two{**}Sine{*}Cosine).
assert (Derivative_I H Sine Cosine).
Deriv.
New_Deriv'.
Abort.

End testes.
