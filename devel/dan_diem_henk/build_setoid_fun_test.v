Require Export build_setoid_fun.

Section samples.

Variables A B C D E : Setoid.

Definition setoid_id : Setoid_fun A A.
build_setoid_fun (fun x : A => x).
Defined.

Variable f : Setoid_fun A A.
Let f16 x := 
  f (f (f (f (f (f (f (f (f (f (f (f (f (f (f (f x))))))))))))))).

Definition setoid_f16 : Setoid_fun A A.
build_setoid_fun f16.
Defined.

Print setoid_f16.

Variable f1 : Setoid_fun C E.
Variable f2 : Setoid_bin_fun C D E.
Variable g1 : Setoid_fun A C.
Variable g2 : Setoid_bin_fun A B C.
Variable h1 : Setoid_fun B D.
Variable h2 : Setoid_bin_fun A B D.

Let uu x := f1 (g1 x).

Definition compose_uu : Setoid_fun A E.
build_setoid_fun uu.
(* [build_setoid_fun (fun x => (f1 (g1 x))).] also works *)
Defined.

Let ub x y := f1 (g2 x y).

Definition compose_ub : Setoid_bin_fun A B E.
build_setoid_fun ub.
Defined.

Let bu x y := f2 (g1 x) (h1 y).

Definition compose_bu : Setoid_bin_fun A B E.
build_setoid_fun bu.
Defined.

Let bb x y := f2 (g2 x y) (h2 x y).

Definition compose_bb : Setoid_bin_fun A B E.
build_setoid_fun bb.
Defined.

Definition id := id_un_op.

Variables S1 S2 : Setoid.

Let K (x:S1) (y:S2) := x.

Definition first : (Setoid_bin_fun S1 S2 S1).
build_setoid_fun (fun (x : S1) (_ : S2) => x).
Defined.

Let K' (x:S1) (y:S2) := y.

Definition second : (Setoid_bin_fun S1 S2 S2).
build_setoid_fun K'.
Defined.

Variable c : S2.
Let const_fun := fun _ : S1 => c.

Definition setoid_const_fun : (Setoid_fun S1 S2).
build_setoid_fun const_fun.
Defined.

Print setoid_const_fun.

End samples.
