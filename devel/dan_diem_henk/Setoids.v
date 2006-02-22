Require Export dh_tactics.
Require Export CLogic.
Require Export Step.

Record Setoid : Type := 
  {std_crr :> Type;
   std_rel :  Crelation std_crr;
   std_prf :  Cequivalence std_crr std_rel}.

Notation "x '[=]' y" := 
  (std_rel _ x y) (at level 70, no associativity).

Notation "x '[~=]' y" := 
  (Not (std_rel _ x y)) (at level 70, no associativity).

(** [Type2Setoid T] builds a setoid out of an arbitrary type [T],
where the equivalence is taken to be Coq's Leibniz equality ([(eq (A:=T))]).
*)

Definition Type2Setoid (T : Type) : Setoid :=
  Build_Setoid T (eq (A:=T)) 
    (Build_Cequivalence T (eq (A:=T))  
      (refl_equal (A:=T)) 
      (sym_equal (A:=T))
      (trans_equal (A:=T))).

(**
%\begin{nameconvention}%
In the names of lemmas, we refer to [ [=] ] by [eq].
%\end{nameconvention}%

** Setoid axioms
We want concrete lemmas that state the axiomatic properties of a setoid.
*)

Section setoid_basics.

Variable S : Setoid.

Section setoid_axioms.

Lemma eq_equivalence : Cequivalence S (std_rel S).
Proof.
exact (std_prf S).
Qed.

Lemma eq_reflexive : Creflexive S (std_rel S).
Proof.
exact (Cequiv_refl S (std_rel S) (std_prf S)).
Qed.

Lemma eq_symmetric : Csymmetric S (std_rel S).
Proof.
exact (Cequiv_symm S (std_rel S) (std_prf S)).
Qed.

Lemma eq_transitive : Ctransitive S (std_rel S).
Proof.
exact (Cequiv_trans S (std_rel S) (std_prf S)).
Qed.

End setoid_axioms.

Lemma lift_eq : forall x y : S, x = y -> x [=] y.
Proof.
intros x y H.
rewrite H.
apply eq_reflexive.
Qed. 

(**
In `there exists a unique [a:S] such that %\ldots%#...#', 
we now mean unique with respect to the setoid equality. 
We use [ex_unq] to denote unique existence.
*)

Definition ex_unq (P : S -> CProp) := 
  {x : S | forall y : S, P y -> x [=] y | P x}.

Notation "{ ! x : S  |  P }" := (ex_unq (fun x : S => P))
  (at level 0, x at level 99) : type_scope.

Lemma eq_wdl : forall x y z : S, x [=] y -> x [=] z -> z [=] y.
Proof.
intros x y z H H0.
apply eq_transitive with (2:=H).
apply eq_symmetric with (1:=H0).
Qed.

Lemma eq_wdr : forall x y z : S, x [=] y -> y [=] z -> x [=] z.
Proof.
exact eq_transitive.
Qed.

Lemma eq_imp_not_neq : forall x y : S, x [=] y -> Not (x [~=] y).
Proof.
intros x y H H0.
exact (H0 H).
Qed.

End setoid_basics.

(* begin hide *)

Ltac refl := apply eq_reflexive.

Ltac symm := apply eq_symmetric; trivial.

Ltac trans m := apply eq_transitive with (y:=m); trivial.

Ltac etrans := 
  match goal with 
  | H : (std_rel _ ?a1 ?a2) |- (std_rel _ ?a1 ?a3) => trans a2
end.

(* dh's naive tac *)
 Ltac triv :=
  (intros; 
    ( assumption || ex_falso || refl || (symm; assumption) 
      || (etrans; assumption) 
    ) 
  ) || trivial.

(* end hide *)

Section operations_on_setoids.

Variables A B : Setoid.

Section product_setoid.

(** **The product of setoids *)

Definition prod_eq : (Crelation (prodT A B)) :=
  fun p q => (fstT p [=] fstT q) and (sndT p [=] sndT q).

Lemma prod_eq_equiv : Cequivalence (prodT A B) prod_eq.
Proof.
split; red.
destruct x as [ a b ]; simpl.
split; refl.
destruct x as [ a1 b1 ].
destruct y as [ a2 b2 ].
intros [ Ha Hb ].
split; simpl_all; symm.
destruct x as [ a1 b1 ].
destruct y as [ a2 b2 ].
destruct z as [ a3 b3 ].
intros [ Ha1 Hb1 ] [ Ha2 Hb2 ].
split; simpl_all; etrans.
Qed.

Definition prod_setoid : Setoid := 
  Build_Setoid (prodT A B) prod_eq prod_eq_equiv.

End product_setoid.

Section union_setoid.

(** The union of setoids *)

Definition union_eq : Crelation (sumT A B) :=
  fun x y => 
  match x, y with 
  | inlT a, inlT b => a [=] b
  | inrT a, inrT b => a [=] b
  | _     , _      => False
  end.

Lemma union_eq_equiv : 
  Cequivalence (sumT A B) union_eq.
Proof.
split; red.
intros [ a | b ]; simpl; refl.
intros [ a1 | b1 ] [ a2 | b2 ]; simpl; triv.
intros [ a1 | b1 ] [ a2 | b2 ] [ a3 | b3 ]; simpl; triv.
Qed.

Definition union_setoid : Setoid :=
  Build_Setoid (sumT A B) union_eq  union_eq_equiv.

End union_setoid.

End operations_on_setoids.

Infix "[*]" := prod_setoid (at level 60, left associativity).

Infix "[+]" := union_setoid (at level 60, left associativity).

Implicit Arguments ex_unq [S].

Hint Resolve eq_reflexive: algebra_r.
Hint Resolve eq_symmetric : algebra_s.

Declare Left  Step eq_wdl.
Declare Right Step eq_wdr.

(** **Relations and predicates
Here we define the notions of well-definedness 
on predicates and relations.

%\begin{convention}% Let [S] be a setoid.
%\end{convention}%

%\begin{nameconvention}%
- ``well-defined'' is abbreviated to [well_def] (or [wd]).
%\end{nameconvention}%
*)

Section Setoid_relations_and_predicates.

Variable S : Setoid.

(** ***Predicates

At this stage, we consider [CProp]- and [Prop]-valued predicates on setoids.

%\begin{convention}% Let [P] be a predicate on (the carrier of) [S].
%\end{convention}%
*)

Section SetoidPredicates.

Variable P : S -> Prop.

Definition pred_wd (P : S -> CProp) : CProp := 
  forall x y : S, P x -> x [=] y -> P y.

End SetoidPredicates.

Record Setoid_predicate : Type := 
 {sp_pred :> S -> CProp;
  sp_wd   :  pred_wd sp_pred}.

(** ***Relations
%\begin{convention}%
Let [R] be a relation on (the carrier of) [S].
%\end{convention}% *)

Section SetoidRelations.

Variable R : S -> S -> CProp.

Definition rel_wdl : CProp := 
  forall x y z : S, R x y -> x [=] z -> R z y.

Definition rel_wdr : CProp := 
  forall x y z : S, R x y -> y [=] z -> R x z.

End SetoidRelations.

(** ***Definition of a setoid relation
The type of relations over a setoid.  *)

Record Setoid_relation : Type := 
  {sr_rel    :> S -> S -> CProp;
   sr_wdr    :  rel_wdr sr_rel;
   sr_wdl    :  rel_wdl sr_rel}.

End Setoid_relations_and_predicates.

(** **Functions between setoids
Such functions must preserve the setoid equality, 
i.e.%\% be well-defined.
For every arity this has to be defined separately.
%\begin{convention}%
Let [S1], [S2] and [S3] be setoids.
%\end{convention}%

First we consider unary functions.  *)

Section Setoid_functions.

Variables S1 S2 S3 : Setoid.

Section unary_functions.

(**
In the following two definitions,
[f] is a function from (the carrier of) [S1] to
(the carrier of) [S2].  *)

Variable f : S1 -> S2.

Definition fun_wd : CProp := 
  forall x y : S1, x [=] y -> f x [=] f y.

End unary_functions.

Record Setoid_fun : Type := 
  {sf_fun :> S1 -> S2;
   sf_wd  :  fun_wd sf_fun}.

Definition Const_Setoid_fun : S2 -> Setoid_fun.
intro c.
apply (Build_Setoid_fun (fun _ => c)).
intros x y H.
apply eq_reflexive.
Defined.

Section binary_functions.

(**
Now we consider binary functions.
In the following two definitions,
[f] is a function from [S1] and [S2] to [S3].
*)

Variable f : S1 -> S2 -> S3.

Definition bin_fun_wd : CProp := 
  forall x1 x2 y1 y2,
  x1 [=] x2 -> y1 [=] y2 -> f x1 y1 [=] f x2 y2.

End binary_functions.

Record Setoid_bin_fun : Type := 
 {sbf_fun :> S1 -> S2 -> S3;
  sbf_wd  : bin_fun_wd sbf_fun}.

End Setoid_functions.

Hint Resolve sf_wd : algebra_c.

(* beware, [Si] can't always be inferred from (std_crr Si) *)
Implicit Arguments fun_wd [S1 S2].
Implicit Arguments bin_fun_wd [S1 S2 S3].

(** **The unary and binary (inner) operations on a setoid
An operation is a function with domain(s) and co-domain equal.

%\begin{nameconvention}%
The word ``unary operation'' is abbreviated to [un_op];
``binary operation'' is abbreviated to [bin_op].
%\end{nameconvention}%

%\begin{convention}%
Let [S] be a setoid.
%\end{convention}%
*)

Section setoid_inner_ops.

Variable S : Setoid.

(** Properties of binary operations *)

Definition commutes (f : S -> S -> S) : CProp := 
  forall x y : S, f x y [=] f y x.

Definition associative (f : S -> S -> S) : CProp := 
  forall x y z : S, f x (f y z) [=] f (f x y) z.

(** Well-defined unary operations on a setoid.  *)

Definition un_op_wd := fun_wd (S1:=S) (S2:=S).

Definition Setoid_un_op : Type := Setoid_fun S S.

Definition Build_Setoid_un_op := Build_Setoid_fun S S.

Definition s_un_op_wd := sf_wd S S.

Lemma id_wd : un_op_wd (fun x : S => x).
Proof.
exact (fun x y H => H).
Qed.

Definition id_un_op := 
  Build_Setoid_un_op (fun x : S => x) id_wd.

(* begin hide *)
Identity Coercion un_op_fun : Setoid_un_op >-> Setoid_fun.
(* end hide *)

(** Well-defined binary operations on a setoid.  *)

Definition bin_op_wd := bin_fun_wd (S1:=S) (S2:=S) (S3:=S).

Definition Setoid_bin_op : Type := Setoid_bin_fun S S S.

Definition Build_Setoid_bin_op := Build_Setoid_bin_fun S S S.

Definition s_bin_op_wd := sbf_wd S S S.

(* begin hide *)
Identity Coercion bin_op_bin_fun : Setoid_bin_op >-> Setoid_bin_fun.
(* end hide *)

Variable op : Setoid_bin_op.
Variable c : S.

Lemma bin_op_is_wd_un_op_lft : un_op_wd (fun x => op x c).
Proof.
intros x y H.
apply s_bin_op_wd.
exact H.
apply eq_reflexive.
Qed.

Lemma bin_op_is_wd_un_op_rht : un_op_wd (fun x => op c x).
Proof.
intros x y H. 
apply s_bin_op_wd. 
apply eq_reflexive. 
exact H.
Qed.

Definition bin_op2un_op_rht : Setoid_un_op :=
  Build_Setoid_un_op (fun x => op c x) bin_op_is_wd_un_op_rht.

Definition bin_op2un_op_lft : Setoid_un_op :=
  Build_Setoid_un_op (fun x => op x c) bin_op_is_wd_un_op_lft.

End setoid_inner_ops.

Implicit Arguments commutes [S].
Implicit Arguments associative [S].

Hint Resolve s_bin_op_wd s_un_op_wd : algebra_c.

(** **The binary outer operations on a setoid
%\begin{convention}%
Let [S1] and [S2] be setoids.
%\end{convention}%
*)

Section setoid_outer_ops.

Variables S1 S2 : Setoid.

(**
Well-defined outer operations on a setoid.
*)

Definition outer_op_well_def := bin_fun_wd.

Definition Setoid_outer_op : Type := Setoid_bin_fun S1 S2 S2.
Definition Build_Setoid_outer_op := Build_Setoid_bin_fun S1 S2 S2.
Definition soo_wd := sbf_wd S1 S2 S2.

(* begin hide *)
Identity Coercion outer_op_bin_fun : Setoid_outer_op >-> Setoid_bin_fun.
(* end hide *)

End setoid_outer_ops.

Hint Resolve soo_wd : algebra_c.

(** **Subsetoids
%\begin{convention}%
Let [S] be a setoid, and [P] a predicate on the carrier of [S].
%\end{convention}%
*)

Section SubSetoids.

Variable S : Setoid.
Variable P : S -> CProp.

Record subsetoid_crr : Type := 
 {ss_elt :> S;
  ss_prf  :  P ss_elt}.

(** Though [ss_elt] is declared as a coercion, it does not satisfy the
uniform inheritance condition and will not be inserted.  However it will
also not be printed, which is handy.
*)

Definition restrict_relation (R : Crelation S) : Crelation subsetoid_crr :=
  fun a b =>
  match a, b with
  | Build_subsetoid_crr x _, Build_subsetoid_crr y _ => R x y
  end.

Definition subsetoid_eq : Crelation subsetoid_crr :=
  restrict_relation (std_rel S).

Lemma subsetoid_eq_equiv : 
  Cequivalence subsetoid_crr subsetoid_eq.
Proof.
split; red.
intros [ a p ]; simpl; refl.
intros [ a p ] [ b q ]; simpl; triv.
intros [ a p ] [ b q ] [ c r ]; simpl.
intros; trans b.
Qed.

Definition Build_SubSetoid : Setoid := 
  Build_Setoid subsetoid_crr subsetoid_eq subsetoid_eq_equiv.

Lemma ss_elt_wd :
  forall (e1 e2 : subsetoid_crr),
  (std_rel Build_SubSetoid e1 e2) -> 
  ss_elt e1 [=] ss_elt e2.
Proof.
intros [ a p ] [ b q ] H; simpl_all.
exact H.
Qed.

Lemma ss_elt_inj :
  forall (e1 e2 : subsetoid_crr),
  ss_elt e1 [=] ss_elt e2 ->
  std_rel Build_SubSetoid e1 e2. 
Proof.
intros [ a p ] [ b q ] H; simpl_all.
exact H.
Qed.

(** ***Subsetoid unary operations
%\begin{convention}%
Let [f] be a unary setoid operation on [S].
%\end{convention}%
*)

Section SubSetoid_unary_operations.

Variable f : Setoid_un_op S.

Definition un_op_pres_pred : CProp := 
  forall x : S, P x -> P (f x).

(**
%\begin{convention}%
Assume [pr:un_op_pres_pred].
%\end{convention}% *)

Variable pr : un_op_pres_pred.

Definition restr_un_op (a : subsetoid_crr) : subsetoid_crr :=
  match a with
  | Build_subsetoid_crr x p => Build_subsetoid_crr (f x) (pr x p)
  end.

Lemma restr_un_op_wd : un_op_wd Build_SubSetoid restr_un_op.
Proof.
red.
red.
destruct x; destruct y; simpl; intro H.
apply s_un_op_wd with (1:=H).
Qed.

Definition Build_SubSetoid_un_op : Setoid_un_op Build_SubSetoid :=
  Build_Setoid_un_op Build_SubSetoid restr_un_op restr_un_op_wd.

End SubSetoid_unary_operations.

(** ***Subsetoid binary operations
%\begin{convention}%
Let [f] be a binary setoid operation on [S].
%\end{convention}%
*)

Section SubSetoid_binary_operations.

Variable f : Setoid_bin_op S.

Definition bin_op_pres_pred : CProp := 
  forall x y : S, P x -> P y -> P (f x y).

(**
%\begin{convention}%
Assume [bin_op_pres_pred].
%\end{convention}%
*)

Variable pr : bin_op_pres_pred.

Definition restr_bin_op (a b : subsetoid_crr) : subsetoid_crr :=
  match a, b with
  | Build_subsetoid_crr x p, Build_subsetoid_crr y q =>
      Build_subsetoid_crr (f x y) (pr x y p q)
  end.

Lemma restr_bin_op_wd : bin_op_wd Build_SubSetoid restr_bin_op.
Proof.
red.
red.
destruct x1; destruct x2; destruct y1; destruct y2; simpl; intros H H0.
apply s_bin_op_wd with (1:=H) (2:=H0).
Qed.

Definition Build_SubSetoid_bin_op : Setoid_bin_op Build_SubSetoid :=
  Build_Setoid_bin_op Build_SubSetoid restr_bin_op restr_bin_op_wd.

Lemma restr_f_assoc : 
  associative f -> associative Build_SubSetoid_bin_op.
Proof.
intro H.
red.
intros.
simpl.
destruct x; destruct y; destruct z; simpl.
apply H.
Qed.

End SubSetoid_binary_operations.

End SubSetoids.

Implicit Arguments ss_elt [S P].
Implicit Arguments ss_prf [S P].

Notation "A '[|]' P " := 
  (Build_SubSetoid A P) (at level 60, left associativity).

(** [mk_ss_elt] is just a synonym for [Build_subsetoid_crr] 
but its type is forced to be [A[|]P] instead of [subsetoid_crr A P].
*)

Definition mk_ss_elt 
  (A : Setoid) (P : A -> CProp) (a : A) (p : P a) : A[|]P :=
  Build_subsetoid_crr A P a p.

Implicit Arguments mk_ss_elt [A].

(* 
my_simpl only unfolds the toplevel setoid equality and then simplifies;
simpl simplifies too much in concrete cases;
check out the next example *)

Ltac my_simpl := (* rename *)
  cbv delta [std_rel]; cbv delta-[std_rel]; cbv beta iota.

Ltac my_simpl_all :=
  cbv delta [std_rel] in *|-*; 
  cbv delta-[std_rel] in *|-*; 
  cbv beta iota in *|-*.
  
(*
Goal
  forall (P : Setoid_predicate IN) (x : (IN[|]P)),
  x [=] x and x [=] x.
intros P [ x p ]; split.
simpl.
reflexivity.
my_simpl.
refl.
Abort.
*)

(* adhoc adhoc adhoc *)
Ltac change_to_std_rel :=
  match goal with 
  | |- subsetoid_eq ?A ?P ?x ?y => 
      change (x[=]y); change_to_std_rel
  | H : subsetoid_eq ?A ?P ?x ?y |- _ => 
      change (x[=]y) in H; change_to_std_rel
  | _ : _ |- _ => idtac
  end.

Definition pred_eq (A : Setoid) (P Q : Setoid_predicate A) :=
  forall x : A, Iff (P x) (Q x).

(* universe inconsistency ! *)
(*

Section setoid_of_setoid_predicates.

Variable A : Setoid.

Lemma reflexive_pred_eq : 
  Creflexive (Setoid_predicate A) (pred_eq A).
Proof.
intro P; split; trivial.
Qed.

Lemma symmetric_pred_eq : 
  Csymmetric _ (pred_eq A).
Proof.
intros P Q H x.
destruct (H x) as [ H1 H2 ].
split; assumption.
Qed.

Lemma transitive_pred_eq : 
  Ctransitive _ (pred_eq A).
Proof.
intros P Q T H H0 x.
destruct (H x) as [ H1 H2 ].
destruct (H0 x) as [ H3 H4 ].
split; intro H5.
exact (H3 (H1 H5)).
exact (H2 (H4 H5)).
Qed.

Definition setoid_of_setoid_predicates :=
  Build_Setoid (Setoid_predicate A) (pred_eq A) 
    (Build_equivalence (Setoid_predicate A) (pred_eq A)
      reflexive_(pred_eq A)
      symmetric_(pred_eq A)
      transitive_(pred_eq A)).

Definition IP := setoid_of_setoid_predicates.

End setoid_of_setoid_predicates.

*)

Notation "P '=e' Q" := (pred_eq _ P Q) (at level 70, no associativity).

(* begin hide *)
Ltac Step_final x := trans x; Algebra.
(* end hide *)

Tactic Notation "Step_final" constr(c) :=  Step_final c.
