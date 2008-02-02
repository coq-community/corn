Require Export Bvector.
Require Export List.

Set Implicit Arguments.
 
Definition raster n m := vector (Bvector n) m.

Notation "'⎥' a b" := (Vcons (vector bool _) a _ b) 
  (format "'[v' '⎥' a '/' b ']'", at level 0, a, b at level 0) : raster.
Notation "'⎥' a" := (Vcons (vector bool _) a _ (Vnil _)) 
  (format "'⎥' a", at level 0, a, b at level 0) : raster.
(*
Notation "☙" := (Vnil (vector bool _)) (at level 0, right associativity) : raster.
*)
Notation "█ a" := (Vcons bool true _ a) (at level 0, right associativity) : raster.
Notation "⎢" := (@Vnil bool) (at level 0, right associativity) : raster.
Notation "' ' a" := (Vcons bool false _ a) (at level 0, right associativity) : raster.
Notation "░ a" := (Vcons bool false _ a) (at level 0, right associativity, only parsing) : raster_parsing.

Definition vectorAsList A n (v:vector A n) : list A :=
vector_rect A (fun (n0 : nat) (_ : vector A n0) => list A) nil
  (fun (a : A) (n0 : nat) (_ : vector A n0) (IHv : list A) => a :: IHv) n v.

Coercion vectorAsList : vector>->list.

Definition RasterIndex n m (r:raster n m) i j :=
 nth j (nth i (map (@vectorAsList _ _) r) nil) false.
