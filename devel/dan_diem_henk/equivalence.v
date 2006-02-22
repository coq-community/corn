Require Export CLogic.

Definition subset (carrier:Type) : Type := carrier->CProp.

Section Equivalence.

Variable carrier:Type.
Variable domain:subset carrier.


Variable R: Crelation carrier.

Definition SReflexive:= forall (x:carrier), domain x -> R x x.
Definition SSymmetric:= forall (x y:carrier), domain x -> domain y -> R x y -> R y x.
Definition STransitive:= forall (x y z:carrier),domain x -> domain y -> domain z -> R x y -> R y z -> R x z.

Record equivalence :CProp := 
 {refl : SReflexive;
  symm : SSymmetric;
  trans: STransitive
 }.
End Equivalence.

Section Quotient.
Variable carrier:Type.

Record Quotient : Type :=
 {qdomain :> subset carrier;
  rel :> Crelation carrier; 
  isequiv : equivalence carrier qdomain rel
 }.
  

End Quotient.

Implicit Arguments qdomain [carrier].
Implicit Arguments rel [carrier].
Implicit Arguments isequiv [carrier].


Section Equivalence1.
Variable carrier:Type.
Variable R:Crelation carrier.


Record perRel :CProp := 
 {symme : Csymmetric _ R;
  transi: Ctransitive _ R
 }.
End Equivalence1.

Section PER.
Variable carrier:Type.

Record PER : Type :=
 {rela :> Crelation carrier; 
  isper : perRel carrier rela
 }.
  

End PER.
Implicit Arguments rel [carrier].
Implicit Arguments isper [carrier].



Section DRelation.

Variable carrier:Type.

Variable domain:subset carrier.

Definition DRelation :=
   forall (c1 c2: carrier)(p1: domain c1)(p2: domain c2),CProp.

Definition proofIrrel (rel:DRelation) :=
        forall (c1 c2: carrier)(p1 p1': domain c1)(p2 p2': domain c2), rel c1 c2 p1 p2 -> rel c1 c2 p1' p2'.


End DRelation.

Implicit Arguments DRelation [carrier].
Implicit Arguments proofIrrel [carrier domain].

Section DEquivalence.

Variable carrier:Type.
Variable domain:subset carrier.


Record Dequivalence (R:DRelation domain) :CProp := 
 {drefl :    forall (c: carrier)(p1 p2: domain c), R c c p1 p2;
  dsymm: forall (c1 c2:carrier)(p1 : domain c1)(p2: domain c2), R c1 c2 p1 p2 -> R c2 c1 p2 p1;
  dtrans:    forall (c1 c2 c3: carrier)
                   (p1: domain c1) (p2: domain c2) (p3: domain c3),
                    R c1 c2 p1 p2 -> R c2 c3 p2 p3  -> R c1 c3 p1 p3}.


End DEquivalence.

Implicit Arguments Dequivalence [carrier domain].


Section DQuotient.

Variable carrier:Type.
Unset Implicit Arguments.

Record DQuotient : Type :=
 {
  ddomain :> subset carrier;(* domain seems to be overloaded *)
  drel :> DRelation ddomain; (* These two could have been packaged, but seems too much? *)
  dirrel: proofIrrel drel;
  disequiv : Dequivalence drel
 }.
  
End DQuotient.

Implicit Arguments ddomain [carrier].
Implicit Arguments drel [carrier].
Implicit Arguments dirrel [carrier].
Implicit Arguments disequiv [carrier].

Variable carrier:Type.

Definition trans1:(Quotient carrier) -> PER carrier.
intros Q.
destruct Q.
apply (Build_PER _ (fun x y => qdomain0 x and qdomain0 y and rel0 x y )).
destruct isequiv0.
apply Build_perRel.
intros x y [p1 [p2 p3]].
repeat split; try assumption.
apply symm0; assumption.
intros x y z [p1 [p2 p3]] [p1a [p2a p3a]].
repeat split; try assumption.
apply (trans0 x y z p1 p2 p2a p3 p3a).
Defined.

Definition trans2: (PER carrier) -> Quotient carrier.
intros P.
destruct P.
apply (Build_Quotient _ (fun x => rela0 x x) rela0).
destruct isper0.
apply Build_equivalence.
intros x H.
exact H.

intros x y H1 H2 H3.
apply symme0.
exact H3.
intros x y z H1 H2 H3 H4 H5.
apply (transi0 x y z H4 H5).
Defined.


Definition trans3:(Quotient carrier) -> (DQuotient carrier).
intros.
destruct X.
apply (Build_DQuotient carrier qdomain0 (fun c1 c2 p1 p2 => rel0 c1 c2)).
intro; intros; assumption.
destruct isequiv0.
apply Build_Dequivalence.
intros.
apply refl0.
assumption.
intros.
apply symm0; assumption.
intros.
apply (trans0 c1 c2 c3 p1 p2 p3 X X0).
Defined.

Definition trans4:(DQuotient carrier) -> (Quotient carrier).
intros.
elim X.
intros.
apply (Build_Quotient carrier ddomain0 (fun c1 c2 => sigT (A := ddomain0 c1) (fun p1 => (sigT (A := ddomain0 c2) (fun p2 => drel0 c1 c2 p1 p2))))).
destruct disequiv0.
apply Build_equivalence.
intro; intros.
exists X0.
exists X0.
apply drefl0.
intro; intros.
elim X2. intros.
elim p.
intros.
exists x1.
exists x0.
apply dsymm0.
assumption.
intro; intros.
elim X3; intros.
elim p; intros.
elim X4; intros.
elim p1.
intros.
exists  x0.
exists x3.
unfold proofIrrel in dirrel0.
assert (H1 := dirrel0 x y x0 x0 x1 x2 p0).
apply (dtrans0 x y z x0 x2 x3).
assumption.
assumption.
Defined.
