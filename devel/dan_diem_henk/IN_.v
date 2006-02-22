Require Export SetoidFun.

Implicit Types k : nat.

Lemma le_lt_or_eq_dec : 
  forall n m : nat, n <= m -> {n < m} + {n = m}.
Proof.
induction n; destruct m; intro H.
right; reflexivity.
left.
auto with arith.
assert False. (* *)
inversion H.
elim H0.
assert (n <= m).
auto with arith.
elim (IHn m H0); auto with arith.
Qed.

Lemma nat_eq_dec : 
  forall n m : nat, {n = m} + {n <> m}.
Proof.
induction n.
simple destruct m.
left; reflexivity.
right; red in |- *; intro h; discriminate h.
simple destruct m.
right; red in |- *; intro h; discriminate h.
intro m'.
elim (IHn m'); intro h.
left; rewrite h; reflexivity.
right; red in |- *; intro h0; injection h0; intro h1; exact (h h1).
Qed.

Definition IN : Setoid := 
  Type2Setoid nat.

Lemma N__wd :
  forall k (n m : IN),
  let N_k := (fun i => i < k) in 
  (N_k n) -> n [=] m -> (N_k m).
Proof.
intros k n m N_k H H0.
rewrite <- H0.
exact H.
Qed.

Definition N_ k : Setoid_predicate IN :=
  Build_Setoid_predicate _ _ (N__wd k).

Definition IN_ k : Setoid :=
  IN[|](N_ k).

Lemma IN_S_dec (* rename *) : 
  forall k (m : (IN_ (S k))),
  let m_e := ss_elt m in
  {m_e < k} + {m_e = k}.
Proof.
intros k m m_e.
assert (H := le_S_n _ _ (ss_prf m)).
exact (le_lt_or_eq_dec m_e k H).
Qed.

Definition lift_N_ k : (IN_ k) -> (IN_ (S k)) :=
  fun m =>
  mk_ss_elt (N_ (S k)) (ss_elt m) (le_S _ _ (ss_prf m)).

Lemma lift_N__wd : forall k, fun_wd (lift_N_ k).
Proof.
intros k [ x p ] [ y q ] H; my_simpl_all.
exact H.
Qed.

Definition lift_IN_ k :=
  Build_Setoid_fun (IN_ k) (IN_ (S k)) (lift_N_ k) (lift_N__wd k).

Definition k_in_IN_Sk k :=
  mk_ss_elt (N_ (S k)) k (lt_n_Sn k).

Definition proj_N_ k (m : (IN_ (S k))) :
  (ss_elt m) < k -> (IN_ k) :=
  fun p =>
  match (IN_S_dec k m) with
  | left q  => mk_ss_elt (N_ k) (ss_elt m) q
  | right q => 
      False_rect (IN_ k) 
        (lt_irrefl k  
          (eq_rect (ss_elt m) (N_ k) p k q))
  end.

Lemma proj_N__wd : 
  forall k (m1 m2 : IN_ (S k)), 
  m1[=]m2 ->
  forall (p1 : (ss_elt m1) < k) (p2 : (ss_elt m2) < k),
  proj_N_ k m1 p1 [=] proj_N_ k m2 p2.
Proof.
intros k m1 m2 H p1 p2.
unfold proj_N_.
destruct (IN_S_dec k m1) as [ q1 | q ].
destruct (IN_S_dec k m2) as [ q2 | q ].
destruct m1 as [ m1_e m1_p ]; destruct m2 as [ m2_e m2_p ]; my_simpl_all.
exact H.
ex_falso.
ex_falso.
Qed.

Lemma left_inverse_proj_lift :
  forall k (m : IN_ k),
  proj_N_ k (lift_IN_ k m) (ss_prf m) [=] m.
Proof.
intros k m.
unfold proj_N_.
destruct (IN_S_dec k (lift_IN_ k m)) as [ q | q ].
destruct m as [ m_e m_p ]; my_simpl.
refl.
ex_falso.
Qed.

Lemma left_inverse_proj_lift2 :
  forall k (m : IN_ k) (p : (ss_elt m) < k),
  proj_N_ k (lift_IN_ k m) p [=] m.
Proof.
intros k m p.
unfold proj_N_.
destruct (IN_S_dec k (lift_IN_ k m)) as [ q | q ].
destruct m as [ m_e m_p ]; my_simpl.
refl.
ex_falso.
Qed.

Lemma lift_N_neq_top :
  forall k (m : (IN_ k)),
  (lift_N_ k m) [~=] (k_in_IN_Sk k).
Proof.
intros k m.
red.
simpl.
destruct m as [ m_e m_p ].
simpl.
intro H.
rewrite H in m_p.
destruct (lt_irrefl k).
exact m_p.
Qed.
