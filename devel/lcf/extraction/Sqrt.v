
Require Export WeakIVT_Extr.
Require Export Cauchy_IR.

Section Square_Root_Revisited.

Variable x:IR.
Hypothesis Hx:Zero[<=]x.

Let F := FId{*}FId{-}[-C-]x.

Axiom grows : forall (w z:IR), (Zero [<=] w)->(Zero [<=] z)->(w[<]z)->
  forall Hw Hz, (F w Hw)[<](F z Hz).

Let a := (Zero:IR).
Let b := (x[+]One).

Let Hab' : (a[<]b).
unfold a, b.
apply leEq_less_trans with x.
 auto.
apply less_plusOne.
Qed.

Let Hab : (a[<=]b).
apply less_leEq.
auto.
Qed.

Let contF : (Continuous_I Hab F).
unfold F.
Contin.
Qed.

Let Finc : forall (w z:IR), (Compact Hab w)->(Compact Hab z)->(w[<]z)->
  forall Hw Hz, (F w Hw)[<](F z Hz).
intros w z H H0 H1 Hw Hz.
apply grows; auto; [elim H | elim H0]; auto.
Qed.

Lemma sqrt_via_IVT : {y:IR | (Compact Hab y) | forall Hy, (F y Hy)[=]Zero}.
apply IVT_I with contF; auto.
 unfold a; simpl.
 rstepl [--]x; astepr [--](Zero:IR).
 apply inv_resp_leEq; auto.
unfold b; simpl.
rstepr (x[^](2)[+]x[+]One); rstepl (Zero[+]Zero[+](Zero:IR)).
repeat apply plus_resp_leEq_both.
  apply sqr_nonneg.
 auto.
apply less_leEq; apply pos_one.
Qed.

End Square_Root_Revisited.

Definition sqrt' (x:IR) (Hx:(Zero[<=]x)) : IR.
intros.
elim sqrt_via_IVT with x Hx.
intro y; intros.
apply y.
Defined.

Lemma grows_opt : let RR := Cauchy_IR in
  forall (x:RR), (Zero [<=] x)-> forall (w z:RR) (w' z':Q_as_COrdField),
  (w = (inject_Q _ w'))->(z = (inject_Q _ z'))->
  (Zero [<=] w)->(Zero [<=] z)->(w[<]z)->
    forall Hw Hz, (FId{*}FId{-}[-C-]x) w Hw [<] (FId{*}FId{-}[-C-]x) z Hz.
intros RR x pos_x w z w' z' Hww' Hzz' pos_w pos_z w_lt_z Hw Hz.
rewrite Hww'. rewrite Hzz'.
rewrite Hww' in w_lt_z. rewrite Hzz' in w_lt_z.
elim w_lt_z. intros N HN.
elim HN; clear HN; intros e He HN.
simpl in HN.
exists N. exists (e[*](z'[+]w')).
 apply mult_resp_pos; auto. apply plus_resp_pos_nonneg.
 apply leEq_less_trans with w'. apply ing_cancel_leEq. rewrite <- Hww'. auto.
 apply ing_cancel_less. auto.
 apply ing_cancel_leEq. rewrite <- Hww'. auto.
intros n Hn.
Opaque Q_as_COrdField.
simpl.
Transparent Q_as_COrdField.
rstepr ((z'[-]w')[*](z'[+]w')).
apply mult_resp_leEq_rht. eauto.
astepl ((Zero:Q_as_COrdField)[+]Zero); apply plus_resp_leEq_both.
apply ing_cancel_leEq; rewrite <- Hzz'; auto.
apply ing_cancel_leEq; rewrite <- Hww'; auto.
Qed.

Axiom blah : False.

Lemma lft_rht_extract : let RR := Cauchy_IR in
  forall (a b : RR) (a' b': Q_as_COrdField),
  (a = (inject_Q _ a'))->(b = (inject_Q _ b'))->
  a [<] b -> (Two[*]a[+]b)[/]ThreeNZ [<] (a[+]Two[*]b)[/]ThreeNZ.
intros RR a b a' b' Haa' Hbb' H.
rewrite Haa'. rewrite Hbb'.
elim H. intros N HN. elim HN; clear HN. intros e He Hen.
exists N. exists (e[/]ThreeNZ).
clear Hen N H Hbb' Haa' b' a' b a.
2: elim blah.
simpl in He.
red in He; simpl in He.
simpl; red; simpl.
rewrite <- Zmult_assoc. simpl. auto.
Qed.
