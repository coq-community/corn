
Require Export GroupReflection.
Require Export CFields.

Section Rtest.
Variable G : CAbGroup.
Variable f : CSetoid_un_op G.
Variable g : CSetoid_bin_op G.
Variables a b c : G.

Goal f (a[+]b)[=]f (b[+]a).
rational.
Abort.

Goal
f (a[+]b)[+]g c (a[-]b)[=][--][--](g (Zero[+]c) ([--]b[+]a))[+]f (b[+]a).
rational.
Abort.

End Rtest.

Require Export RingReflection.

Section Rtest2.
Variable R : CRing.
Variable f : CSetoid_un_op R.
Variable g : CSetoid_bin_op R.
Variables a b c : R.

Goal f (a[*]b)[=]f (b[*]a).
rational.
Abort.

Goal
f (a[+]b)[*]g (c[^]1) (a[-]b)[=]
[--][--](g (Zero[+]c) ([--]b[+]a))[*]f (b[+]a)[*]One.
rational.
Abort.

End Rtest2.

Require Export COrdFields.

Section Rtest3.
Variable F : COrdField.
Variable f : CSetoid_un_op F.
Variable g : CSetoid_bin_op F.
Variables a b c : F.

Goal f (a[*]b [/]OneNZ)[=]f (b[*]a).
rational.
Abort.

Goal Two [/]TwoNZ[=](One:F).
rational.
Abort.

Goal Two [/]TwoNZ[+]Zero[*]a[=]One.
rational.
Abort.


Goal
f (a[+]b)[*]g (c[^]1) (a[-]b)[=]
[--][--](g (Zero[+]c) ([--]b[+]a))[*]f (b[+]a) [/]OneNZ.
rational.
Abort.

End Rtest3.

Section Rtest4.
Variable R : CRing.
Variable F : CField.
Variable f : CSetoid_fun R F.
Variables x y : R.
Variable z : F.

Goal f (x[+]y)[+]z[=]z[+]f (x[+]y).
rational.
Abort.

End Rtest4.

Section Rtest5.
Variable F : CField.
Variable f : CSetoid_un_op F.
Variables x y : F.
Variable z : F.

Goal f (x[*]y)[*]z[=]z[*]f (y[*]x).
rational.
Abort.

End Rtest5.
