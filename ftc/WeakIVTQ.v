(** Author : Abhishek Anand ( http://www.cs.cornell.edu/~aa755/ ) 
*)

Require Export CoRN.ftc.FTC.

Definition Q2R  (q: Q) : IR := (inj_Q IR q).
Coercion  Q2R : Q >-> st_car.


Require Import Ring. 
Require Import CoRN.tactics.CornTac.
Require Import CoRN.algebra.CRing_as_Ring.

Add Ring IRisaRing: (CRing_Ring IR).

Require Export CoRN.ftc.Derivative.   
Require Export CoRN.ftc.Integral.
Lemma shift_zeroR_leEq_minus :
  forall ft fq : IR, ft[<=]fq -> ft[-]fq[<=][0].
Proof.
  intros ? ? Hle.
  apply shift_minus_leEq.
  ring_simplify.
  trivial.
Qed.

Hint Resolve less_leEq_trans leEq_less_trans plus_resp_less_leEq
plus_resp_leEq_less minus_resp_less_leEq plus_resp_pos_nonneg
leEq_inj_Q leEq_wdr leEq_wdr leEq_reflexive eq_imp_leEq
leEq_imp_eq leEq_imp_eq leEq_transitive (leEq_inj_Q IR) less_leEq
Min_leEq_rht Min_leEq_lft
shift_zero_leEq_minus shift_minus_leEq shift_zeroR_leEq_minus
pos_two rht_leEq_Max 
lft_leEq_Max: CoRN.

Hint Immediate eq_reflexive_unfolded : CoRN.

Lemma ltAddRhs :
forall (a b : IR), 
    [0][<]b -> a[<]a[+]b.
  intros ? ? Hlt.
  pose proof (leEq_reflexive _ a) as Hr.
  apply (plus_resp_less_leEq _ _ _ _ _ Hlt) in Hr.
  eapply less_wdl in Hr;[|apply cm_lft_unit_unfolded].
  eapply less_wdr;[| apply cag_commutes_unfolded].
  trivial.
Qed.

Lemma closeRationalR : forall (a b t d : IR) (Hab : a [<=] b),
  Compact Hab t
  -> t[<]b
  -> [0][<]d
  -> {q : Q | Compact Hab q /\
                      AbsIR (t[-]q)[<=]d}.
Proof.
  intros ? ? ? ? ? p Hcc Hdp.
  pose proof (less_Min _ _ _ (ltAddRhs t d Hdp) Hcc) as Hmlt.
  pose proof (Q_dense_in_CReals' _ _ _ Hmlt) as Hqr.
  destruct Hqr as [q Hqr Hql].
  exists q.
  simpl in p. unfold Q2R in p. destruct p as [pl pr].
  assert ( a[<=]inj_Q IR q) as Haq by (eauto using
        less_leEq, leEq_less_trans).
  assert (inj_Q IR q[<=] b) as Hqb by (eauto using
      less_leEq,
      less_leEq_trans,
      Min_leEq_rht).
  split;[exact (Haq,Hqb)|].
  rewrite AbsIR_minus. unfold Q2R.
  rewrite AbsIR_eq_x;[|eauto 4 using 
        shift_zero_leEq_minus, less_leEq].
  apply shift_minus_leEq.
  rewrite cag_commutes_unfolded.
  eauto using
        less_leEq,leEq_less_trans,leEq_reflexive,
        less_leEq_trans,Min_leEq_lft.
Defined.

Lemma ltMinusRhs: 
  forall (x y: IR), 
    [0] [<]y -> x[-]y[<]x.
Proof.
  intros.
  apply shift_minus_less.
  apply ltAddRhs; auto.
Qed.



Lemma closeRationalL : forall (a b t d : IR) (Hab : a [<=] b),
  Compact Hab t
  -> a[<]t
  -> [0][<]d
  -> {q : Q | Compact Hab q /\
                      AbsIR (t[-]q)[<=]d}.
Proof.
  intros ? ? ? ? ? p Hcc Hdp.
  pose proof (Max_less _ _ _ (ltMinusRhs _ d Hdp) Hcc) as Hmlt.
  pose proof (Q_dense_in_CReals' _ _ _ Hmlt) as Hqr.
  destruct Hqr as [q Hqr Hql].
  exists q.
  simpl in p. unfold Q2R in p. destruct p as [pl pr].
  assert (inj_Q IR q[<=] b) as Hqb by (eauto using
        less_leEq, less_leEq_trans).
  assert (a[<=] inj_Q IR q) as Haq by (eauto using
      less_leEq,
      less_leEq_trans,
      leEq_less_trans,
      rht_leEq_Max).
  split;[exact (Haq,Hqb)|].
  rewrite AbsIR_eq_x;[|eauto 4 using 
        shift_zero_leEq_minus, less_leEq].
  apply shift_minus_leEq.
  apply shift_leEq_plus'.
  unfold Q2R.
  pose proof (lft_leEq_Max (t[-]d) a).
  apply less_leEq.
  eapply leEq_less_trans; eauto.
Qed.


Require Export CoRN.ftc.StrongIVT.

Lemma closeRationalLR : forall (a b x d : IR) (Hab : a [<] b),
  (Compact (less_leEq _ _ _ Hab)) x
  -> [0][<]d
  -> {q : Q | (Compact (less_leEq _ _ _ Hab)) q /\
                      AbsIR (x[-]q)[<=]d}.
Proof.
  intros ? ? ? ? ? Hcc Hdp.
  pose proof Hab as Hap.
  apply less_cotransitive_unfolded with (z:=x)in Hap.
  destruct Hap as [Hlt | Hgt].
- apply closeRationalL; auto.
- apply closeRationalR; auto.
Qed.

(** this lemma is stronger than Weak_IVT. the only change
    is that the type of [x] (in the concluion)
    is Q, instead of IR *)
Lemma Weak_IVTQ
     : forall (I : interval) (F : PartFunct IR),
       Continuous I F ->
       forall (a b : IR) (Ha : Dom F a) (Hb : Dom F b)
         (HFab : F a Ha[<]F b Hb),
       I a ->
       I b ->
       forall e : IR,
       [0][<]e ->
       forall y : IR,
       Compact (less_leEq IR (F a Ha) (F b Hb) HFab) y ->
       {x : Q | Compact (Min_leEq_Max a b) x /\
       forall Hx : Dom F x, AbsIR (F x Hx[-]y)[<=]e}.
Proof.
  intros ? ? Hc ? ? ? ? ? Hia Hib ? He ? Hcp.
  apply pos_div_two in He.
  pose proof He as Hivt.
  eapply Weak_IVT with (y:=y) (F:=F) (HFab := HFab) in Hivt;
    eauto.
  unfold compact in He.
  unfold Continuous in Hc.
  destruct Hc as [Hcl Hcr].
  specialize (Hcr _ _  (Min_leEq_Max a b)).
  unfold Continuous_I in Hcr.
  match type of Hcr with
  ?A -> _ => assert A as H99 by (apply included_interval; auto);
            pose proof (included_trans _ _ _ _ H99 Hcl) as Hdom;
             specialize (Hcr H99); clear H99
  end.

  apply snd in Hcr.
  specialize (Hcr _ He).
  destruct Hcr as [d Hdp Hcc].
  destruct Hivt as [x Hmm Hfx].
  pose proof HFab as Hap.
  specialize (fun xp => Hcc x xp Hmm).
    (* y already names a point in the co-domain *)
  apply less_imp_ap in Hap.
  apply pfstrx in Hap.
  apply ap_imp_Min_less_Max in Hap.
  pose proof (closeRationalLR _ _ _ _ Hap Hmm Hdp) as Hqq.
  destruct Hqq as [q H99].
  exists q.
  destruct H99 as [Hcomp Hab].
  split;[exact Hcomp|].
  specialize (Hcc q Hcomp (Hdom _ Hmm) (Hdom _ Hcomp) Hab).
  specialize (Hfx (Hdom _ Hmm)).
  rewrite AbsIR_minus in Hcc.
  apply AbsIR_imp_AbsSmall in Hcc.
  apply AbsIR_imp_AbsSmall in Hfx.
  pose proof (AbsSmall_eps_div_two  _ _ _ _ Hcc Hfx) as Hsum.
  clear Hfx Hcc.
  unfold cg_minus in Hsum.
  ring_simplify in Hsum.
  intros Hx.
  apply AbsSmall_imp_AbsIR.
  rewrite pfwdef with (Hy := Hx) in Hsum; trivial.
  apply eq_reflexive.
Qed.
