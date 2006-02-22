Require Export build_csetoid_fun.
Require Export CGroups.

Section samples.

Variable G : CGroup.

Definition cg_minus : (CSetoid_bin_op G).
build_csetoid_fun (fun x y : G => x [+] [--]y).
Defined.

Variables A B C D E : CSetoid.

Variable f : CSetoid_fun C C.
Variable f1 : CSetoid_fun C E.
Variable f2 : CSetoid_bin_fun C D E.
Variable g1 : CSetoid_fun A C.
Variable g2 : CSetoid_bin_fun A B C.
Variable h1 : CSetoid_fun B D.
Variable h2 : CSetoid_bin_fun A B D.

Let uu x := f1 (g1 x).

Definition compose_uu : CSetoid_fun A E.
build_csetoid_fun uu.
Defined.

Let ub x y := f1 (g2 x y).

Definition compose_ub : CSetoid_bin_fun A B E.
build_csetoid_fun ub.
Defined.

Let bu x y := f2 (g1 x) (h1 y).

Definition compose_bu : CSetoid_bin_fun A B E.
build_csetoid_fun bu.
Defined.

Let bb x y := f2 (g2 x y) (h2 x y).

Definition compose_bb : CSetoid_bin_fun A B E.
build_csetoid_fun bb.
Defined.

Definition id := id_un_op.

Variables S1 S2 : CSetoid.

Let K (x:S1) (y:S2) := x.

Definition first : (CSetoid_bin_fun S1 S2 S1).
build_csetoid_fun K.
Defined.

Let K' (x:S1) (y:S2) := y.

Definition second : (CSetoid_bin_fun S1 S2 S2).
build_csetoid_fun K'.
Defined.

End samples.
