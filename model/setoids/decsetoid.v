(* Standard Coq Setoids with decidable equality yield CSetoids with
 apartness defined as negation of equivalence. Also, morphisms on these
 setoids yield fun_strext/bin_fun_strext/Crel_strext. *)

Require Import
 CSetoids
 SetoidClass
 SetoidDec
 Morphisms.

Section contents.

  Context {T: Type} {S: Setoid T} {eq_dec: EqDec S}.

  Definition ap (a b: T): Prop := ~ (a == b).

  Lemma ap_irreflexive: irreflexive ap.
  Proof. do 2 intro. intuition. Qed.

  Lemma ap_symmetric: Csymmetric ap.
  Proof. do 4 intro. intuition. Qed.

  Lemma ap_cotransitive: cotransitive ap.
  Proof with intuition.
   intros x y H z.
   destruct (eq_dec x z)...
   destruct (eq_dec z y)...
   elimtype False.
   apply H.
   transitivity z...
  Qed.

  Lemma ap_tight: tight_apart (@equiv _ S) ap.
  Proof with intuition.
   red. unfold ap, Not. split...
   destruct (eq_dec x y)...
  Qed.

  Definition is_CSetoid: is_CSetoid T equiv ap
    := Build_is_CSetoid T equiv ap ap_irreflexive ap_symmetric ap_cotransitive ap_tight.

  Definition CSetoid: CSetoid := Build_CSetoid _ _ _ is_CSetoid.

  Lemma fun_strext (S': CSetoids.CSetoid) (f: T -> S'):
    Morphism (equiv ==> @st_eq _) f -> @fun_strext CSetoid S' f.
  Proof with auto.
   red. simpl.
   repeat intro.
   apply <- (ax_ap_tight _ _ _ (cs_proof S') (f x) (f y))...
  Qed.

  Lemma Crel_strext (R: relation T): Morphism (equiv ==> equiv ==> iff) R -> Crel_strext CSetoid R.
  Proof with auto.
   red. simpl. intros.
   destruct (eq_dec x1 x2)...
   destruct (eq_dec y1 y2)...
   left.
   rewrite <- e, <- e0...
  Qed.

End contents.

Section binary.

  Context {T T': Type} {S: Setoid T} {S': Setoid T'} {eq_dec: EqDec S} {eq_dec': EqDec S'}.

  Lemma bin_fun_strext (S'': CSetoids.CSetoid) (f: T -> T' -> S''):
    Morphism (equiv ==> equiv ==> @st_eq _) f -> bin_fun_strext CSetoid CSetoid S'' f.
  Proof with auto.
   red. simpl.
   intros.
   destruct (eq_dec x1 x2)...
   destruct (eq_dec' y1 y2)...
   elimtype False.
   apply <- (ax_ap_tight _ _ _ (cs_proof S'') (f x1 y1) (f x2 y2))...
   rewrite e e0.
   reflexivity.
  Qed.

End binary.
