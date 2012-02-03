Require Import CRtrans.

Extraction Language Haskell.

Extract Inductive bool => Bool [ True False ].
Extract Inductive option => Maybe [ Just Nothing ].

Extract Inductive list => "([])" [ "[]" "( : )" ].
Extract Inlined Constant tl => "tail".
Extract Inlined Constant hd => "head".
Extract Inlined Constant map => "map".

Extract Inductive Streams.Stream => "([])" ["( : )"].
Extract Inlined Constant Streams.tl => "tail".
Extract Inlined Constant Streams.hd => "head".
Extract Inlined Constant Streams.map => "map".
Extract Inlined Constant Streams.zipWith => "zipWith".

Extract Inductive sum => "( :+: )" [ "Inl" "Inr" ].

Extract Inductive prod => "( , )" [ "( , )" ].
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".

Extract Inductive sumbool => Bool [ True False ].
Extraction Inline sumbool_rec.

Extract Inductive comparison => Ordering [ EQ LT GT ].

(* Misc *)
Extraction Inline eq_rect.
Extraction Inline eq_rec.
Extraction Inline eq_rec_r.
Extraction Inline proj1_sig.

(* nat *)
Extract Inductive nat => Integer [ "0" "succ" ]
 "(\ fO fS n -> if n == 0 then fO () else fS (n - 1))".

Extract Inlined Constant plus => "(+)".
Extract Inlined Constant pred => "fun n -> max 0 (pred n)".
Extract Inlined Constant minus => "fun n m -> max 0 (n - m)".
Extract Inlined Constant mult => "(*)".
Extract Inlined Constant max => max.
Extract Inlined Constant min => min.
Extract Inlined Constant EqNat.beq_nat => "(==)".
Extract Inlined Constant EqNat.eq_nat_decide => "(==)".
Extract Inlined Constant Peano_dec.eq_nat_dec => "(==)".

(* ZArith *)
Extract Inductive positive => Integer [ "(\p -> 1+2*p)" "(\p -> 2*p)" "1" ]
 "(\f2p1 f2p f1 p -> if p <= 1 then f1 () else if p`mod` 2 == 0 then f2p (p `div` 2) else f2p1 (p `div` 2))".

Extract Inductive Z => Integer [ "0" "" "negate" ]
"(\f0 fp fn z -> if z == 0 then f0 () else if z > 0 then fp z else fn (negate z))".

Extract Inlined Constant Pplus => "(+)".
Extract Inlined Constant Psucc => "succ".
Extract Inlined Constant Ppred => "pred".
Extract Inlined Constant Pminus => "\n m -> max 1 (n - m)".
Extract Inlined Constant Pmult => "(*)".
Extract Inlined Constant Pmin => "min".
Extract Inlined Constant Pmax => "max".
Extract Inlined Constant Pcompare => "compare".
Extract Inlined Constant positive_eq_dec => "(==)".
Extraction Inline positive_rec.

Extract Inlined Constant Zplus => "(+)".
Extract Inlined Constant Zsucc => "succ".
Extract Inlined Constant Zpred => "pred".
Extract Inlined Constant Zminus => "(-)".
Extract Inlined Constant Zmult => "(*)".
Extract Inlined Constant Zopp => "negate".
Extract Inlined Constant Zabs => "abs".
Extract Inlined Constant Zmin => "min".
Extract Inlined Constant Zmax => "max".
Extract Inlined Constant Zcompare => "compare".
Extract Inlined Constant Z_eq_dec => "(==)".
Extraction Inline Z_rec.
Extract Inlined Constant Z_of_nat => "id".

(* QArith *)
Extract Inductive Q => Rational [ "( :% )" ].
Extract Inlined Constant Qnum => "numerator".
Extract Inlined Constant Qden => "denominator".

Extract Inlined Constant Qplus => "(+)".
Extract Inlined Constant Qplus' => "(+)".
Extract Inlined Constant Qopp => "negate".
Extract Inlined Constant QMinMax.Qmin => "min".
Extract Inlined Constant Qminus' => "min".
Extract Inlined Constant QMinMax.Qmax => "max".
Extract Inlined Constant Qmult => "(*)".
Extract Inlined Constant Qmult' => "(*)".
Extract Inlined Constant Qinv => "recip".
Extract Inlined Constant Qcompare => "compare".
Extract Inlined Constant inject_Z => "fromInteger".
Extract Inlined Constant Qeq_dec => "(==)".

(*
Definition answer (n:positive) (r:CR) : Z :=
 let m := (iter_pos n _ (Pmult 10) 1%positive) in
 let (a,b) := (approximate r (1#m)%Qpos)*m in
 Zdiv a b.

Definition test := answer 10 (exp ('1))%CR.

Recursive Extraction test.
*)