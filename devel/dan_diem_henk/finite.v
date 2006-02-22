Require Export IN_.

Implicit Types A B : Setoid.

Definition isomorphic A B :=
  {f : Setoid_fun A B | {f' : Setoid_fun B A | inverse f f'}}.

Infix "[~]" := isomorphic (at level 70).

Lemma isomorphic_reflexive :
  forall A, A[~]A.
Proof.
intro A.
exists (id A); exists (id A).
split; intro x; simpl; triv.
Qed.

Lemma isomorphic_symmetric :
  forall A B, A[~]B -> B[~]A.
Proof.
intros A B [ f [ f' H ] ].
exists f'; exists f.
apply inverse_symmetric with (1:=H).
Qed.

Lemma isomorphic_transitive :
  forall A B C, A[~]B -> B[~]C -> A[~]C.
Proof.
intros A B C [ f [ f' H1 ] ] [ g [ g' H2 ]].
exists (f[o]g).
exists (g'[o]f').
apply composition_preserves_inverse with (1:=H1) (2:=H2).
Qed.

(*
Definition decidable p := {p} + {~p}.
*)

Definition decidable_pred A (P : A -> CProp) := 
  forall x, Cdecidable (P x).

Definition decidable_rel A (R : A -> A -> CProp) :=
  forall x y, Cdecidable (R x y).

Implicit Arguments decidable_pred [A].
Implicit Arguments decidable_rel [A].

Definition Finite A : CProp :=
  {k : nat | A[~](IN_ k)}.

Lemma complement_of_predicate_wd :
  forall A (P : Setoid_predicate A),
  let C_P := fun x => Not (P x) in
  pred_wd A C_P.
Proof.
intros A P C_P x1 x2 H H0 H1.
apply H.
apply sp_wd with (1:=H1).
symm.
Qed.

Definition complement_of_predicate A P :=
  Build_Setoid_predicate A _  (complement_of_predicate_wd A P).

Notation "P ^c" := (complement_of_predicate _ P) (at level 60).

Lemma intersection_of_predicates_wd :
  forall A (P Q : Setoid_predicate A),
  let P_and_Q := fun a => (P a) and (Q a) in
  pred_wd A P_and_Q.
Proof.
intros A P Q P_and_Q a1 a2 [ H1 H2 ] H; split;
  apply sp_wd with (2:=H); assumption.
Qed.

Definition intersection_of_predicates A P Q :=
  Build_Setoid_predicate A _ (intersection_of_predicates_wd A P Q).

Notation "P [/\] Q" := 
  (intersection_of_predicates _ P Q) (at level 60).

Lemma union_of_predicates_wd :
  forall A (P Q : Setoid_predicate A),
  let P_or_Q := fun a => (P a) or (Q a) in
  pred_wd A P_or_Q.
Proof.
intros A P Q P_or_Q a1 a2 [H | H] H0; [ left | right ];
  apply sp_wd with (1:=H) (2:=H0).
Qed.

Definition union_of_predicates A P Q :=
  Build_Setoid_predicate A _ (union_of_predicates_wd A P Q).

Notation "P [\/] Q" := (union_of_predicates _ P Q) (at level 60).

Lemma equal_to_wd : 
  forall A (a : A),
  pred_wd A (fun x => x [=] a).
Proof.
intros A a x1 x2.
exact (eq_wdl A x1 a x2).
Qed.

Definition equal_to A (a : A) :=
  Build_Setoid_predicate A _ (equal_to_wd A a).

Definition unequal_to A  (a : A) :=
  (equal_to A a)^c.

Lemma ss_pair_of_projections :
  forall A P (x : (A[|]P)),
  Build_subsetoid_crr A P (ss_elt x) (ss_prf x) = x.
Proof.
intros A P [ x p ].
reflexivity.
Qed.

Lemma add_wd : 
  forall A P a, 
  pred_wd A (P [\/] (equal_to A a)).
Proof.
intros A P a x1 x2; simpl; intros [ H | H ] H0; [ left | right ].
apply sp_wd with (1:=H) (2:=H0).
trans x1.
symm.
Qed.

Definition add A P a := (* rename *)
  Build_Setoid_predicate A _ (add_wd A P a).

Lemma add_preserves_finiteness :
  forall A (P : Setoid_predicate A), 
  decidable_pred P ->
  Finite (A[|]P) -> 
  forall a : A, 
  Finite (A[|](add A P a)).
Proof.
intros A P Pdec. 
intros [ k [ f [ g [ lifg rifg ] ] ] ] a.
destruct (Pdec a) as [ H | H ].
(* P a *)
exists k.
set 
  (_h := 
    fun x : (A[|](add A P a)) =>
    let x_e := ss_elt x in
    let x_p := ss_prf x in
    match x_p with
    | Cinleft p  => f (mk_ss_elt _ x_e p)
    | Cinright p => f (mk_ss_elt _ x_e (sp_wd _ P a x_e H (eq_symmetric _ x_e a p)))
    end
  ).
assert (h_wd : fun_wd _h).
unfold _h.
intros [ x [ p | p ] ] [ y [ q | q ] ] H0; simpl; change_to_std_rel; 
  apply sf_wd; simpl; exact H0.
set (h := Build_Setoid_fun _ _ _h h_wd).
set 
  (_i := 
    fun m : IN_ k =>
    mk_ss_elt (add A P a) (ss_elt (g m)) 
      (Cinleft _ _ (ss_prf (g m)))
  ).
assert (i_wd : fun_wd _i).
unfold _i.
intros [ x p ] [ y q ] H0; simpl_all.
apply ss_elt_wd.
apply sf_wd.
simpl.
exact H0.
set (i := Build_Setoid_fun _ _ _i i_wd).
exists h; exists i.
unfold h, i, _h, _i.
split.
intros [ x [ p | p ] ]; simpl.
trans (ss_elt (mk_ss_elt P x p)).
apply ss_elt_wd.
apply lifg.
refl.
trans (ss_elt (mk_ss_elt P x (sp_wd A P a x H (eq_symmetric A x a p)))).
apply ss_elt_wd.
apply lifg.
refl.
intro x.
simpl; change_to_std_rel.
(*
trans (f (g x)).
*)
apply 
  (eq_transitive (IN_ k) 
    (f (mk_ss_elt P (ss_elt (g x)) (ss_prf (g x)))) 
    (f (g x)) 
    x
  ).
apply sf_wd.
destruct (g x); refl.
apply rifg.
(* Not (P a) *)
exists (S k).
set 
  (_h := 
    fun x : (A[|](add A P a)) =>
    let x_e := ss_elt x in
    let x_p := ss_prf x in
    match x_p with
    | Cinleft p  => lift_IN_ k (f (mk_ss_elt _ x_e p))
    | Cinright p => k_in_IN_Sk k
    end
  ).
assert (h_wd : fun_wd _h).
unfold _h.
intros [ x [ p | p ] ] [ y [ q | q ] ]; simpl; intro H0.
change 
  ((lift_IN_ k (f (mk_ss_elt _ x p)))
    [=](lift_IN_ k (f (mk_ss_elt _ y q)))).
apply sf_wd.
apply sf_wd.
exact H0.
destruct H.
apply sp_wd with (2:=q).
apply sp_wd with (2:=H0).
exact p.
destruct H.
apply sp_wd with (2:=p).
apply sp_wd with (2:=(eq_symmetric _ x y H0)).
exact q.
reflexivity.
set (h := Build_Setoid_fun _ _ _ h_wd).
set 
  (_i := 
    fun m : IN_ (S k) =>
    match (IN_S_dec k m) with
    | left p => 
        mk_ss_elt (add A P a) (ss_elt (g (proj_N_ k m p)))
          (Cinleft _ _ (ss_prf (g (proj_N_ k m p))))
    | right p => 
        mk_ss_elt (add A P a) a 
          (Cinright _ _ (eq_reflexive _ a))
    end
  ).
assert (i_wd : fun_wd _i).
unfold _i.
intros x y H0.
destruct (IN_S_dec k x) as [ p | p ];
  destruct (IN_S_dec k y) as [ q | q ]; simpl.
apply ss_elt_wd.
apply sf_wd.
apply proj_N__wd with (1:=H0).
destruct x as [ x x_ ]; destruct y as [ y y_ ]; simpl in H0, p, q.
destruct (lt_irrefl y).
pattern y at 1; rewrite <- H0.
rewrite q.
exact p.
destruct x as [ x x_ ]; destruct y as [ y y_ ]; simpl in H0, p, q.
destruct (lt_irrefl y).
pattern y at 2; (rewrite <- H0; rewrite p).
exact q.
refl.
set (i := Build_Setoid_fun _ _ _i i_wd).
exists h; exists i.
split; red.
unfold h, i, _h, _i.
intros [ x [ p | p ] ]; simpl in p |- *.
destruct (IN_S_dec k (lift_N_ k (f (mk_ss_elt (A:=A) P x p)))) 
  as [ q | q ]; simpl in q |- *.
trans (ss_elt (g (f (mk_ss_elt P x p)))).
apply ss_elt_wd.
apply sf_wd.
apply (left_inverse_proj_lift2 k (f (mk_ss_elt P x p))).
(* typical *)
trans (ss_elt (mk_ss_elt P x p)).
apply ss_elt_wd.
apply lifg.
refl.
simpl in q.
destruct (lift_N_neq_top k (f (mk_ss_elt P x p)) q).
destruct (IN_S_dec k (k_in_IN_Sk k)) as [ q | q ]; simpl in q |- *.
destruct (lt_irrefl k q).
symm.
unfold h, i, _h, _i.
intro m.
simpl.
destruct (IN_S_dec k m) as [ q | q ].
simpl.
destruct m as [ m p ].
simpl.
(* awful *)
set (m' := (mk_ss_elt (N_ (S k)) m p)).
transitivity (ss_elt (f (g (proj_N_ k m' q)))).
apply (f_equal (ss_elt (S:=IN) (P:=(N_ k)))).
apply (f_equal f).
unfold m'.
unfold mk_ss_elt.
apply (ss_pair_of_projections A P).
transitivity (ss_elt (proj_N_ k m' q)).
assert (HH := (rifg (proj_N_ k m' q))).
simpl in HH.
destruct (f(g(proj_N_ k m' q))) as [ what ever ].
simpl in HH.
destruct (proj_N_ k m' q) as [ hor rible ].
simpl.
exact HH.
simpl in q.

simpl in p.
unfold proj_N_.
destruct (IN_S_dec k m') as [ r | r ].
simpl.
reflexivity.
ex_falso.
simpl.
destruct m as [ m p ].
simpl in q.
symmetry.
exact q.
(* SIGHHHHHHH *)
Qed.

Lemma isomorphic_preserves_finiteness :
  forall A B, A[~]B -> Finite A -> Finite B.
Proof.
intros A B H [n H0].
exists n.
apply isomorphic_transitive with (2:=H0).
apply isomorphic_symmetric with (1:=H).
Qed.

Definition empty A (* : IP A *) :=
  Build_Setoid_predicate A (fun _ => False) (fun _ _ H _ => H).

Lemma empty_finite : 
  forall A, Finite (A[|](empty A)).
Proof.
intro A.
exists 0.
set 
  (_f := 
    fun x : (A[|](empty A)) => 
    False_rect (IN_ 0) (ss_prf x)
  ).
assert (f_wd : fun_wd _f).
red.
unfold _f.
intros.
ex_falso.
set (f := Build_Setoid_fun _ _ _f f_wd).
set 
  (_g := 
    fun x : IN_ 0 =>
    False_rect (A[|](empty A)) (lt_n_O _ (ss_prf x))
  ).
assert (g_wd : fun_wd _g).
red.
unfold _g.
intros.
ex_falso.
set (g := Build_Setoid_fun _ _ _g g_wd).
exists f; exists g.
split; intros [ x p ].
simpl in p.
ex_falso.
simpl in p.
destruct (lt_n_O x p).
Qed.

Lemma complement_preserves_decidability :
  forall A (P : Setoid_predicate A),
  decidable_pred P  ->
  decidable_pred (P^c).
Proof.
intros A P decP a.
destruct (decP a) as [ p | p ]; [ right | left ]; intro q.
exact (q p).
exact (p q).
Qed.

Lemma subsetoid_preserves_decidable_eq :
  forall A,
  decidable_rel (std_rel A) ->
  forall P : Setoid_predicate A,
  decidable_rel (std_rel (A[|]P)).
Proof.
intros A H P [ x Hx ] [ y Hy ]; simpl.
apply H.
Qed.

Lemma equal_pred_imp_iso_restr : (* nice name *)
  forall A (P Q : Setoid_predicate A), (* (P Q : IP A) *)
  P =e Q ->
  (A[|]P)[~](A[|]Q).
Proof.
intros A P Q H.
unfold isomorphic.
simpl in H.
red in H.
assert (H0 : forall x : A, P x -> Q x).
intro x.
destruct (H x) as [ H0 _ ].
exact H0.
set
 (f :=
   fun x : (A[|]P) =>
   let x_e := ss_elt x in
   let x_p := ss_prf x in
   mk_ss_elt Q x_e (H0 x_e x_p)
 ).
assert (f_wd : fun_wd f).
intros x y H1.
destruct x as [x_e x_p]. 
destruct y as [y_e y_p].
simpl_all.
exact H1.
exists (Build_Setoid_fun (A[|]P) (A[|]Q) f f_wd). 
assert (H2 : forall x : A, Q x -> P x).
intro x.
destruct (H x) as [ _ H3 ].
exact H3.
set
 (g :=
   fun x : (A[|]Q) =>
   let x_e := ss_elt x in
   let x_p := ss_prf x in
   mk_ss_elt P x_e (H2 x_e x_p)
 ).
assert (g_wd : fun_wd g).
intros x y H3.
destruct x as [x_e x_p]. 
destruct y as [y_e y_p].
simpl_all.
exact H3.
exists (Build_Setoid_fun (A[|]Q) (A[|]P) g g_wd). 
split; intros [x_e x_p]; simpl_all; refl.
Qed.

Lemma isomorphic_preserves_decidable_eq :
  forall A B,
  A[~]B ->
  decidable_rel (std_rel A) ->
  decidable_rel (std_rel B).
Proof.
intros A B [ f [ f' [ ff' f'f ] ] ] dec_eq_A x y.
destruct (dec_eq_A (f' x) (f' y)) as [ H | H ]; [ left | right ].
trans (f (f' x)).
symm.
trans (f (f' y)).
apply sf_wd with (1:=H).
intro H0.
apply H.
apply sf_wd with (1:=H0).
Qed.

Lemma pred_ext_eq_implies_isomorphic_subsetoids (* rename *) :
  forall A (P Q : Setoid_predicate A), (* (P Q : IP A) *)
  P =e Q -> (* P[=]Q *)
  A[|]P [~] A[|]Q.
Proof.
intros A P Q e.
set 
  (_f := 
    fun x : (A[|]P) => 
    let x_e := ss_elt x in
    let x_p := ss_prf x in
    mk_ss_elt Q x_e (CAnd_proj1 _ _ (e x_e) x_p)
  ).
assert (f_wd : fun_wd _f).
intros [ x_e x_p ] [ y_e y_p ]; simpl.
exact (fun H => H).
set (f := Build_Setoid_fun _ _ _ f_wd).
set 
  (_g := 
    fun x : (A[|]Q) => 
    let x_e := ss_elt x in
    let x_p := ss_prf x in
    mk_ss_elt P x_e (CAnd_proj2 _ _ (e x_e) x_p)
  ).
assert (g_wd : fun_wd _g).
intros [ x_e x_p ] [ y_e y_p ]; simpl.
exact (fun H => H).
set (g := Build_Setoid_fun _ _ _ g_wd).
exists f; exists g; split; intros [ x_e x_p ]; simpl; refl.
Qed.

Lemma map_pred_wd :
  forall A B (f' : Setoid_fun B A) (P : Setoid_predicate A),
  let map_pred := fun b => (P (f' b)) in
  pred_wd B map_pred.
Proof.
intros A B f' P map_pred b1 b2 H H0.
red.
apply sp_wd with (1:=H).
apply sf_wd with (1:=H0).
Qed.

Definition map_pred (* rename *) 
  A B (f' : Setoid_fun B A) (P : Setoid_predicate A) :
  Setoid_predicate B :=
  Build_Setoid_predicate B _ (map_pred_wd A B f' P).

Lemma map_pred_preserves_decidability :
  forall A B (f' : Setoid_fun B A) (P : Setoid_predicate A),
  decidable_pred P ->
  decidable_pred (map_pred A B f' P).
Proof.
intros A B f' P decP.
intro b.
exact (decP (f' b)).
Qed.

Lemma subsetoid_preserves_isomorphic :
  forall A B (f : Setoid_fun A B) (f' : Setoid_fun B A),
  inverse f f' ->
  forall (P : Setoid_predicate A),
  let Q := map_pred A B f' P in
  (A[|]P) [~] (B[|]Q).
Proof.
intros A B f f' [ liff' riff' ] P Q.
assert (p2q : forall a : A, P a -> (Q (f a))).
intros a p.
unfold Q.
simpl.
apply sp_wd with (1:=p).
symm.
set 
  (_g := 
    fun x : (A[|]P) =>
    let x_e := ss_elt x in
    let x_p := ss_prf x in
    mk_ss_elt Q (f x_e) (p2q x_e x_p)
  ).
assert (_g_wd : fun_wd _g).
intros [ x_e x_p ] [ y_e y_p ] H.
simpl_all.
apply sf_wd with (1:=H).
set (g := Build_Setoid_fun _ _ _g _g_wd).
set 
  (_g' := 
    fun x : (B[|]Q) =>
    let x_e := ss_elt x in
    let x_p := ss_prf x in
    mk_ss_elt P (f' x_e) x_p
  ).
assert (_g'_wd : fun_wd _g').
intros [ x_e x_p ] [ y_e y_p ] H.
simpl_all.
apply sf_wd with (1:=H).
set (g' := Build_Setoid_fun _ _ _g' _g'_wd).
exists g; exists g'; split; red; intros [ x_e x_p ]; simpl_all.
apply liff'.
apply riff'.
Qed.

(* Q restricted to A[|]P *)

Lemma restrict_predicate_wd :
  forall A (P Q : Setoid_predicate A),
  pred_wd (A[|]P) (fun x  => Q (ss_elt x)).
Proof.
intros A P Q [ x_e x_p ] [ y_e y_p ]; simpl; intros H H0.
apply sp_wd with (1:=H) (2:=H0).
Qed.

Definition restrict_predicate A (P Q : Setoid_predicate A) :=
  Build_Setoid_predicate _ _ (restrict_predicate_wd A P Q).

Notation "Q [||] P" := (restrict_predicate _ P Q) (at level 60).

Lemma restrict_predicate_preserves_decidability :
  forall A (P Q : Setoid_predicate A),
  decidable_pred Q ->
  decidable_pred (Q[||]P).
Proof.
intros A P Q Qdec.
intro x.
exact (Qdec (ss_elt x)).
Qed.

(*
Lemma ... :
  forall A (P Q : A -> Prop),
  A[|]P[|](Q[||]P) [~] A[|]Q[|](P[||]Q).
Proof.
*)

Lemma nn :
  forall A (P Q : Setoid_predicate A),
  (A[|]P[|](Q[||]P)) [~] (A[|](P[/\]Q)).
Proof.
intros A P Q.
set 
  (_f := 
    fun x : (A[|]P[|](Q[||]P)) => 
    mk_ss_elt (P[/\]Q) (ss_elt (ss_elt x)) 
      (CAnd_intro _ _ (ss_prf (ss_elt x)) (ss_prf x))
  ).
assert (_f_wd : fun_wd _f).
intros [[x_e_e x_e_p] x_p] [[y_e_e y_e_p] y_p] H.
simpl_all.
exact H.
set (f := Build_Setoid_fun _ _ _ _f_wd).
set 
  (_g := 
    fun x : (A[|](P[/\]Q)) => 
    mk_ss_elt (Q[||]P) 
      (mk_ss_elt P (ss_elt x) 
        (CAnd_proj1 _ _ (ss_prf x))) (CAnd_proj2 _ _ (ss_prf x))
  ).
assert (_g_wd : fun_wd _g).
intros [x_e [x_p x_q]] [y_e [y_p y_q]] H1.
simpl_all.
exact H1.
set (g := Build_Setoid_fun _ _ _ _g_wd).
exists f; exists g; split.
intros [[x_e_e x_e_p] x_p].
simpl_all.
refl.
intros [x_e [x_p x_q]].
simpl_all.
refl.
Qed.

Lemma inv_swap_eq : (* rename *)
  forall A B (f : Setoid_fun A B) (f' : Setoid_fun B A),
  inverse f f' ->
  forall a b,
  f a [=] b IFF a [=] f' b.
Proof.
intros A B f f' [ l r ] a b.
split; intro H.
trans (f' (f a)).
symm.
apply sf_wd.
exact H.
trans (f ( f' b)).
apply sf_wd.
exact H.
Qed.

Lemma my_if_wd :
  forall A (P : Setoid_predicate A)(Pdec : decidable_pred P)
  (Q : Setoid_predicate (A[|]P)),
  let F := 
    (fun a =>
      match (Pdec a) return CProp with
      | Cinleft  p  => Q (mk_ss_elt P a p)
      | Cinright _  => False
      end
    ) in
  pred_wd A F.
Proof.
cbv zeta.
intros A P Pdec Q x y H H0.
destruct (Pdec x) as [ px | px ].
destruct (Pdec y) as [ py | py ].
apply (sp_wd (A[|]P) Q (mk_ss_elt P x px) (mk_ss_elt P y py) H).
simpl.
exact H0.
apply py.
apply sp_wd with (1:=px) (2:=H0).
destruct H.
Qed.

Definition my_if A (P : Setoid_predicate A)(Pdec : decidable_pred P)
  (Q : Setoid_predicate (A[|]P)) : Setoid_predicate A :=
  Build_Setoid_predicate A _ (my_if_wd A P Pdec Q).

Lemma my_if_dec : 
  forall A (P : Setoid_predicate A) (Pdec : decidable_pred P) 
         (Q : Setoid_predicate (A[|]P)),
  decidable_pred Q ->
  decidable_pred (my_if A P Pdec Q).
Proof.
intros A P Pdec Q Qdec.
intro a.
simpl.
destruct (Pdec a) as [ p | p ].
apply Qdec.
right; id.
Qed.

Lemma dec_raa : forall p : CProp, Cdecidable p -> (Not (Not p)) -> p.
Proof.
intros p d H.
destruct d as [ H0 | H0 ].
exact H0.
destruct (H H0).
Qed.

Lemma sumbool2or : forall A B : Prop, {A} + {B} -> A or B.
intros A B [ H | H ]; [ left | right ]; exact H.
Qed.

Lemma Finite_ind :
  forall A : Setoid,
  Finite A ->
  forall M : (Setoid_predicate A) -> CProp, 
  (forall P Q, M P -> P =e Q -> M Q) ->
  M (empty A) ->
  ( forall (P : Setoid_predicate A), 
    decidable_pred P -> 
    M P -> forall a, M (add A P a)
  ) ->
  forall P : Setoid_predicate A, 
  decidable_pred P ->
  M P.
Proof.
intros A [ k H ].
generalize A H; clear H A.
induction k as [ | k IH ]; intros A H M Mext Mbase Mstep P Pdec.
(* 0 *)
destruct H as [ f _ ].
assert (H : (empty A) =e P).
red.
intro x; split; intro H.
destruct H.
destruct (lt_n_O (ss_elt (f x)) (ss_prf (f x))).
exact (Mext (empty A) P Mbase H).
(* S k *)
assert 
  (N_Sn_eq_dec := 
    subsetoid_preserves_decidable_eq IN (fun n m => sumbool2or _ _ (nat_eq_dec n m)) (N_ (S k))).
set (H' := isomorphic_symmetric _ _ H).
assert 
  (A_eq_dec := 
    isomorphic_preserves_decidable_eq  _ _ H' N_Sn_eq_dec).
clear H'.
destruct H as [ f [ f' H ] ].
assert (H' := inverse_symmetric H).
set (k' := k_in_IN_Sk k).
set (Uk := unequal_to _ (k:IN)).
set (Uk' := Uk[||]N_ (S k)).
(*
set (Uk' := unequal_to _ k').
*)
set (U := map_pred _ _ f Uk').
assert (H0 : IN_ (S k)[|]Uk' [~] IN_ k).
unfold Uk'.
unfold IN_.
apply isomorphic_transitive with (IN[|](N_ (S k)[/\]Uk)).
apply nn.
apply pred_ext_eq_implies_isomorphic_subsetoids.
intro n.
unfold N_; simpl.
split.
intros [ H0 H1 ].
assert (H2 : n <= k).
auto with arith.
destruct (le_lt_or_eq n k H2) as [ H3 | H3 ].
exact H3.
elim (H1 H3).
intro H0.
split.
apply lt_S with (1:=H0).
intro H1.
apply (lt_irrefl k).
rewrite H1 in H0.
exact H0.
assert (H1 :  A[|]U [~] IN_ k).
apply isomorphic_transitive with (2:=H0).
apply isomorphic_symmetric.
exact (subsetoid_preserves_isomorphic _ _ _ _ H' Uk').
clear H0; rename H1 into H0.
assert (Udec : decidable_pred U).
unfold U.
apply map_pred_preserves_decidability.
unfold Uk'.
unfold IN_.
apply restrict_predicate_preserves_decidability.
unfold Uk, unequal_to.
apply complement_preserves_decidability.
intro n.
exact (sumbool2or _ _ (nat_eq_dec n k)).
set (F := fun Q => (my_if A U Udec Q)).
set (M' := fun Q => M (F Q)).
assert (M'ext : forall P Q, M' P -> P =e Q -> M' Q).
intros P1 P2 H1 H2.
unfold M' in H1 |- * .
apply Mext with (1:=H1).
intro a.
unfold M'.
simpl.
destruct (Udec a) as [ p | p ].
apply H2.
split; id.
assert (M'base : M' (empty (A[|]U))).
unfold M'.
simpl.
apply Mext with (1:=Mbase).
intro a.
simpl.
destruct (Udec a); split; id.
assert 
  (M'step : 
    forall P : Setoid_predicate (A[|]U),
    decidable_pred P ->
    M' P -> 
    forall a : (A[|]U), M' (add (A[|]U) P a)
  ).
intros Q decQ H1 x.
change (M (my_if A U Udec (add (A[|]U) Q x))).
assert 
  (H2 :
    (add A (my_if A U Udec Q) (ss_elt x))
    =e (my_if A U Udec (add (A[|]U) Q x))
  ).
intro a.
simpl.
destruct (Udec a) as [ p | p ].
set (a_p := mk_ss_elt U a p).
change 
  (((Q a_p) or a [=] (ss_elt x))
  IFF
  ((Q a_p) or a_p [=] x)).
destruct x as [ x_e x_p ]; simpl; split; id.
split; intro H2.
destruct H2 as [ H2 | H2 ].
destruct H2.
apply p.
intro q.
destruct x as [ x_e x_p ].
simpl in H2.
apply x_p.
simpl.
transitivity (ss_elt (f a)).
apply (ss_elt_wd _ _ (f x_e) (f a)).
apply sf_wd.
symm.
exact q.
left.
exact H2.
apply Mext with (2:=H2).
apply Mstep with (2:=H1).
intro a.
simpl.
destruct (Udec a) as [ p | p ].
set (a_p := mk_ss_elt U a p).
change (Cdecidable (Q a_p)).
exact (decQ a_p).
right; id.
set (P' := P[||]U).
assert (P'dec : decidable_pred P').
unfold P'.
apply restrict_predicate_preserves_decidability with (1:=Pdec).
assert (Fdec := my_if_dec A U Udec P' P'dec).
rename H0 into H1.
assert (H0 := IH (A[|]U) H1 M' M'ext M'base M'step P' P'dec).
unfold M' in H0.
clear IH N_Sn_eq_dec H' H1 M' M'ext M'base M'step.
destruct (Pdec (f' k')) as [ H1 | H1 ].
(* P (f' k') *)
assert (H2 := Mstep (F P') Fdec H0 (f' k')).
unfold add in H2.
apply Mext with (1:=H2).
intro a.
simpl.
destruct (Udec a) as [ H3 | H3 ]; split; intro H4.
destruct H4 as [ H4 | H4 ].
exact H4.
destruct H3.
simpl.
assert (H5 := (CAnd_proj2 _ _ (inv_swap_eq _ _ f f' H a k') H4)).
destruct (f a); exact H5.
left; exact H4.
destruct H4 as [ H4 | H4 ].
destruct H4.
apply sp_wd with (1:=H1).
symm.
right.
apply dec_raa.
apply A_eq_dec.
intro H5.
apply H3.
intro H6.
apply H5.
simpl_all.
apply (CAnd_proj1 _ _ (inv_swap_eq _ _ f f' H a k')).
destruct (f a); exact H6.
(* ~ P (f' k') *)
apply Mext with (1:=H0).
intro a.
simpl.
destruct (Udec a) as [ H2 | H2 ]; split.
id.
id.
destruct 1.
intro H3.
apply H2.
intro H4.
apply H1.
apply sp_wd with (1:=H3).
apply (CAnd_proj1 _ _ (inv_swap_eq _ _ f f' H a k')).
destruct (f a); exact H4.
Qed.

Theorem subset_is_finite :
  forall (A : Setoid),
  Finite A -> 
  forall (P : Setoid_predicate A),
  decidable_pred P ->
  Finite (A[|]P).
Proof.
intros A finA P.
apply (Finite_ind A finA (fun P => Finite (A[|]P))).
intros P1 P2 [ k H ] H0.
exists k.
apply isomorphic_transitive with (A[|]P1).
apply pred_ext_eq_implies_isomorphic_subsetoids.
(*
apply symmetric_pred_eq with (1:=H0).
*)
intro x; apply Iff_sym; apply H0.
exact H.
apply empty_finite. 
intros Q Qdec H a.
apply add_preserves_finiteness.
exact Qdec.
exact H.
Qed.
