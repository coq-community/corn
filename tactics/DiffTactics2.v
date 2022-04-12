(* Copyright © 1998-2006
 * Henk Barendregt
 * Luís Cruz-Filipe
 * Herman Geuvers
 * Mariusz Giero
 * Rik van Ginneken
 * Dimitri Hendriks
 * Sébastien Hinderer
 * Bart Kirkels
 * Pierre Letouzey
 * Iris Loeb
 * Lionel Mamane
 * Milad Niqui
 * Russell O’Connor
 * Randy Pollack
 * Nickolay V. Shmyrev
 * Bas Spitters
 * Dan Synek
 * Freek Wiedijk
 * Jan Zwanenburg
 *
 * This work is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *)

(* begin hide *)
Require Export CoRN.ftc.Differentiability.

Section Automatizing_Continuity.

Variables a b : IR.

Inductive cont_function : Type :=
  | hyp_c : forall Hab (F : PartIR),
      Continuous_I (a:=a) (b:=b) Hab F -> cont_function
  | hyp_d : forall Hab' (F F' : PartIR),
      Derivative_I (a:=a) (b:=b) Hab' F F' -> cont_function
  | hyp_d' : forall Hab' (F F' : PartIR),
      Derivative_I (a:=a) (b:=b) Hab' F F' -> cont_function
  | hyp_diff : forall Hab' (F : PartIR),
      Diffble_I (a:=a) (b:=b) Hab' F -> cont_function
  | cconst : forall c : IR, cont_function
  | cid : cont_function
  | cplus : cont_function -> cont_function -> cont_function
  | cinv : cont_function -> cont_function
  | cminus : cont_function -> cont_function -> cont_function
  | cmult : cont_function -> cont_function -> cont_function
  | cscalmult : IR -> cont_function -> cont_function
  | cnth : cont_function -> nat -> cont_function
  | cabs : cont_function -> cont_function.

Fixpoint cont_to_pfunct (r : cont_function) : PartIR :=
  match r with
  | hyp_c Hab F H => F
  | hyp_d Hab F F' H => F
  | hyp_d' Hab F F' H => F'
  | hyp_diff Hab F H => F
  | cconst c => [-C-]c
  | cid => FId
  | cplus f g => cont_to_pfunct f{+}cont_to_pfunct g
  | cinv f => {--}(cont_to_pfunct f)
  | cminus f g => cont_to_pfunct f{-}cont_to_pfunct g
  | cmult f g => cont_to_pfunct f{*}cont_to_pfunct g
  | cscalmult c f => c{**}cont_to_pfunct f
  | cnth f n => cont_to_pfunct f{^}n
  | cabs f => FAbs (cont_to_pfunct f)
  end.

Lemma continuous_cont :
 forall Hab (f : cont_function),
 Continuous_I (a:=a) (b:=b) Hab (cont_to_pfunct f).
Proof.
 intros.
 induction  f as [Hab0 F c| Hab' F F' d| Hab' F F' d| Hab' F d| c| | f1 Hrecf1 f0 Hrecf0| f Hrecf| f1
   Hrecf1 f0 Hrecf0| f1 Hrecf1 f0 Hrecf0| c f Hrecf| f Hrecf n| f Hrecf]; simpl in |- *; intros.
             assumption.
            exact (deriv_imp_contin_I _ _ _ _ _ _ d).
           exact (deriv_imp_contin'_I _ _ _ _ _ _ d).
          exact (diffble_imp_contin_I _ _ _ _ _ d).
         exact (Continuous_I_const _ _ _ c).
        exact (Continuous_I_id _ _ _).
       exact (Continuous_I_plus _ _ _ _ _ Hrecf1 Hrecf0).
      exact (Continuous_I_inv _ _ _ _ Hrecf).
     exact (Continuous_I_minus _ _ _ _ _ Hrecf1 Hrecf0).
    exact (Continuous_I_mult _ _ _ _ _ Hrecf1 Hrecf0).
   exact (Continuous_I_scal _ _ _ _ Hrecf _).
  exact (Continuous_I_nth _ _ _ _ Hrecf _).
 exact (Continuous_I_abs _ _ _ _ Hrecf).
Qed.

End Automatizing_Continuity.

Ltac pfunct_to_cont a b f :=
  match constr:(f) with
  | ([-C-]?X3) => constr:(cconst a b X3)
  | FId => constr:(cid a b)
  | (?X3{+}?X4) =>
      let t1 := pfunct_to_cont a b X3 with t2 := pfunct_to_cont a b X4 in
      constr:(cplus a b t1 t2)
  | ({--}?X3) =>
      let t1 := pfunct_to_cont a b X3 in
      constr:(cinv a b t1)
  | (?X3{-}?X4) =>
      let t1 := pfunct_to_cont a b X3 with t2 := pfunct_to_cont a b X4 in
      constr:(cminus a b t1 t2)
  | (?X3{*}?X4) =>
      let t1 := pfunct_to_cont a b X3 with t2 := pfunct_to_cont a b X4 in
      constr:(cmult a b t1 t2)
  | (?X3{**}?X4) =>
      let t := pfunct_to_cont a b X4 in
      constr:(cscalmult a b X3 t)
  | (?X3{^}?X4) =>
      let t1 := pfunct_to_cont a b X3 in
      constr:(cnth a b t1 X4)
  | (FAbs ?X3) => let t1 := pfunct_to_cont a b X3 in
                  constr:(cabs a b t1)
  | ?X3 =>
      let t := constr:(X3) in
      match goal with
      | Hab:_,H:(Continuous_I (a:=a) (b:=b) ?X1 t) |- _ =>
          constr:(hyp_c a b X1 t H)
      | H:(Derivative_I (a:=a) (b:=b) ?X1 t ?X4) |- _ =>
          constr:(hyp_d a b X1 t X4 H)
      | H:(Derivative_I (a:=a) (b:=b) ?X1 ?X4 t) |- _ =>
          constr:(hyp_d' a b X1 X4 t H)
      | H:(Diffble_I (a:=a) (b:=b) ?X1 t) |- _ =>
          constr:(hyp_diff a b X1 t H)
      end
  end.

Ltac New_Contin :=
  match goal with
  |  |- (Continuous_I (a:=?X1) (b:=?X2) ?X4 ?X3) =>
      let r := pfunct_to_cont X1 X2 X3 in
      let a := constr:(X1) in
      let b := constr:(X2) in
      (apply Continuous_I_wd with (cont_to_pfunct a b r);
        [ unfold cont_to_pfunct in |- * | apply continuous_cont ])
  end.

Section Automatizing_Derivatives.

Variables a b : IR.

Inductive deriv_function : Type :=
  | hyp :
      forall Hab' (f f' : PartIR),
      Derivative_I (a:=a) (b:=b) Hab' f f' -> deriv_function
  | hyp' :
      forall Hab' (f : PartIR),
      Diffble_I (a:=a) (b:=b) Hab' f -> deriv_function
  | const : forall c : IR, deriv_function
  | id : deriv_function
  | rplus : deriv_function -> deriv_function -> deriv_function
  | rinv : deriv_function -> deriv_function
  | rminus : deriv_function -> deriv_function -> deriv_function
  | rmult : deriv_function -> deriv_function -> deriv_function
  | rscalmult : IR -> deriv_function -> deriv_function
  | rnth : deriv_function -> nat -> deriv_function.

Fixpoint deriv_to_pfunct (r : deriv_function) : PartIR :=
  match r with
  | hyp Hab' f f' H => f
  | hyp' Hab' f H => f
  | const c => [-C-]c
  | id => FId
  | rplus f g => deriv_to_pfunct f{+}deriv_to_pfunct g
  | rinv f => {--}(deriv_to_pfunct f)
  | rminus f g => deriv_to_pfunct f{-}deriv_to_pfunct g
  | rmult f g => deriv_to_pfunct f{*}deriv_to_pfunct g
  | rscalmult c f => c{**}deriv_to_pfunct f
  | rnth f n => deriv_to_pfunct f{^}n
  end.

Fixpoint deriv_deriv (r : deriv_function) : PartIR :=
  match r with
  | hyp Hab' f f' H => f'
  | hyp' Hab' f H => PartInt (ProjT1 H)
  | const c => [-C-][0]
  | id => [-C-][1]
  | rplus f g => deriv_deriv f{+}deriv_deriv g
  | rinv f => {--}(deriv_deriv f)
  | rminus f g => deriv_deriv f{-}deriv_deriv g
  | rmult f g =>
      deriv_to_pfunct f{*}deriv_deriv g{+}deriv_deriv f{*}deriv_to_pfunct g
  | rscalmult c f => c{**}deriv_deriv f
  | rnth f n =>
      match n with
      | O => [-C-][0]
      | S p =>
          [-C-](nring (S p)){*}(deriv_deriv f{*}deriv_to_pfunct (rnth f p))
      end
  end.

Lemma deriv_restr :
 forall Hab' (f : deriv_function),
 Derivative_I (a:=a) (b:=b) Hab' (deriv_to_pfunct f) (deriv_deriv f).
Proof.
 intros.
 induction  f as [Hab'0 f f' d| Hab'0 f d| c| | f1 Hrecf1 f0 Hrecf0| f Hrecf| f1 Hrecf1 f0 Hrecf0| f1
   Hrecf1 f0 Hrecf0| c f Hrecf| f Hrecf n]; simpl in |- *.
          assumption.
         apply projT2.
        exact (Derivative_I_const _ _ Hab' c).
       exact (Derivative_I_id _ _ Hab').
      exact (Derivative_I_plus _ _ _ _ _ _ _ Hrecf1 Hrecf0).
     exact (Derivative_I_inv _ _ _ _ _ Hrecf).
    exact (Derivative_I_minus _ _ _ _ _ _ _ Hrecf1 Hrecf0).
   exact (Derivative_I_mult _ _ _ _ _ _ _ Hrecf1 Hrecf0).
  exact (Derivative_I_scal _ _ _ _ _ Hrecf _).
 case n.
  apply Derivative_I_wdl with (Fconst (S:=IR) [1]).
   apply FNth_zero'.
   exact (derivative_imp_inc _ _ _ _ _ Hrecf).
  exact (Derivative_I_const _ _ Hab' _).
 clear n; intro.
 exact (Derivative_I_nth _ _ _ _ _ Hrecf n).
Qed.

Lemma diffble_restr :
 forall Hab' (f : deriv_function),
 Diffble_I (a:=a) (b:=b) Hab' (deriv_to_pfunct f).
Proof.
 intros.
 induction  f as [Hab'0 f f' d| Hab'0 f d| c| | f1 Hrecf1 f0 Hrecf0| f Hrecf| f1 Hrecf1 f0 Hrecf0| f1
   Hrecf1 f0 Hrecf0| c f Hrecf| f Hrecf n]; simpl in |- *.
          apply deriv_imp_Diffble_I with f'; assumption.
         assumption.
        exact (Diffble_I_const _ _ Hab' c).
       exact (Diffble_I_id _ _ Hab').
      exact (Diffble_I_plus _ _ _ _ _ Hrecf1 Hrecf0).
     exact (Diffble_I_inv _ _ _ _ Hrecf).
    exact (Diffble_I_minus _ _ _ _ _ Hrecf1 Hrecf0).
   exact (Diffble_I_mult _ _ _ _ _ Hrecf1 Hrecf0).
  exact (Diffble_I_scal _ _ _ _ Hrecf _).
 exact (Diffble_I_nth _ _ _ _ Hrecf n).
Qed.

End Automatizing_Derivatives.

Ltac pfunct_to_restr a b f :=
  match constr:(f) with
  | ([-C-]?X3) => constr:(const a b X3)
  | FId => constr:(id a b)
  | (?X3{+}?X4) =>
      let t1 := pfunct_to_restr a b X3 with t2 := pfunct_to_restr a b X4 in
      constr:(rplus a b t1 t2)
  | ({--}?X3) =>
      let t1 := pfunct_to_restr a b X3 in
      constr:(rinv a b t1)
  | (?X3{-}?X4) =>
      let t1 := pfunct_to_restr a b X3 with t2 := pfunct_to_restr a b X4 in
      constr:(rminus a b t1 t2)
  | (?X3{*}?X4) =>
      let t1 := pfunct_to_restr a b X3 with t2 := pfunct_to_restr a b X4 in
      constr:(rmult a b t1 t2)
  | (?X3{**}?X4) =>
      let t := pfunct_to_restr a b X4 in
      constr:(rscalmult a b X3 t)
  | (?X3{^}?X4) =>
      let t1 := pfunct_to_restr a b X3 in
      constr:(rnth a b t1 X4)
  | ?X3 =>
      let t := constr:(X3) in
      match goal with
      | H:(Derivative_I (a:=a) (b:=b) ?X1 t ?X4) |- _ =>
          constr:(hyp a b X1 t X4 H)
      | H:(Diffble_I (a:=a) (b:=b) ?X1 t) |- _ => constr:(
      hyp' a b X1 t H)
      end
  end.

Ltac New_Deriv :=
  match goal with
  |  |- (Derivative_I (a:=?X1) (b:=?X2) _ ?X3 ?X4) =>
      let r := pfunct_to_restr X1 X2 X3 in
      (apply Derivative_I_wdl with (deriv_to_pfunct X1 X2 r);
        [ unfold deriv_to_pfunct in |- *
        | apply Derivative_I_wdr with (deriv_deriv X1 X2 r);
           [ unfold deriv_deriv, deriv_to_pfunct in |- *
           | apply deriv_restr ] ])
  end.

Ltac Differentiate :=
  match goal with
  |  |- (Diffble_I (a:=?X1) (b:=?X2) _ ?X3) =>
      let r := pfunct_to_restr X1 X2 X3 in
      (apply Diffble_I_wd with (deriv_to_pfunct X1 X2 r);
        [ apply diffble_restr | unfold deriv_deriv, deriv_to_pfunct in |- * ])
  end.

Ltac derivative_of f :=
  match constr:(f) with
  | ([-C-]?X3) => constr:([-C-]ZeroR)
  | FId => constr:([-C-]OneR)
  | (?X3{+}?X4) =>
      let t1 := derivative_of X3 with t2 := derivative_of X4 in
      constr:(t1{+}t2)
  | ({--}?X3) => let t1 := derivative_of X3 in
                 constr:({--}t1)
  | (?X3{-}?X4) =>
      let t1 := derivative_of X3 with t2 := derivative_of X4 in
      constr:(t1{-}t2)
  | (?X3{*}?X4) =>
      let t1 := derivative_of X3
      with t2 := derivative_of X4
      with t3 := constr:(X3)
      with t4 := constr:(X4) in
      constr:(t3{*}t2{+}t1{*}t4)
  | (?X3{**}?X4) =>
      let t1 := derivative_of X4 with t2 := constr:(X3) in
      constr:(t2{**}t1)
  | (?X3{^}0) => constr:([-C-]ZeroR)
  | (?X3{^}S ?X4) =>
      let t1 := derivative_of X3 with t2 := constr:(X3) with t3 := constr:(X4) in
      constr:(nring _ (S t3){**}(t1{*}t2{^}t3))
  | ({1/}?X3) =>
      let t1 := derivative_of X3 with t2 := constr:(X3) in
      constr:({--}(t1{/}t2{*}t2))
  | (?X3{/}?X4) =>
      let t1 := derivative_of X3
      with t2 := derivative_of X4
      with t3 := constr:(X3)
      with t4 := constr:(X4) in
      constr:((t1{*}t4{-}t3{*}t2){/}t4{*}t4)
  | (?X3[o]?X4) =>
      let t1 := derivative_of X3
      with t2 := derivative_of X4
      with t3 := constr:(X3) in
      constr:((t3[o]t2){*}t1)
  | ?X3 =>
      let t := constr:(X3) in
      match goal with
      | H:(Derivative_I (b:=t) ?X4) |- _ =>
          let t1 := constr:(X4) in
          constr:(t1)
      end
  end.

Ltac Deriv_I_substR :=
  match goal with
  |  |- (Derivative_I _ ?X1 _) =>
      let t := derivative_of X1 in
      apply Derivative_I_wdr with t
  end.
(* end hide *)
