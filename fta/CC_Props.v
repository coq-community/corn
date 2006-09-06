
Require Export AbsCC.

(** * More properties of complex numbers
** Sequences and limits *)

Hint Resolve AbsIR_sqrt_sqr: algebra.

Lemma absCC_absIR_re : forall x : CC, AbsIR (Re x) [<=] AbsCC x.
intros.
astepl (sqrt (Re x[^]2) (sqr_nonneg _ (Re x))).
unfold AbsCC in |- *.
apply power_cancel_leEq with 2. auto. apply sqrt_nonneg.
astepl (Re x[^]2).
astepr (Re x[^]2[+]Im x[^]2).
astepl (Re x[^]2[+]Zero).
apply plus_resp_leEq_lft.
apply sqr_nonneg.
Qed.

Lemma absCC_absIR_im : forall x : CC, AbsIR (Im x) [<=] AbsCC x.
intros.
astepl (sqrt (Im x[^]2) (sqr_nonneg _ (Im x))).
unfold AbsCC in |- *.
apply power_cancel_leEq with 2. auto. apply sqrt_nonneg.
astepl (Im x[^]2).
astepr (Re x[^]2[+]Im x[^]2).
astepl (Zero[+]Im x[^]2).
apply plus_resp_leEq.
apply sqr_nonneg.
Qed.

Definition seq_re (s : nat -> CC) (n : nat) := Re (s n).
Definition seq_im (s : nat -> CC) (n : nat) := Im (s n).

Definition CC_Cauchy_prop (s : nat -> CC) : CProp :=
  Cauchy_prop (seq_re s) and Cauchy_prop (seq_im s).

Record CC_CauchySeq : Type := 
 {CC_seq   :> nat -> CC;
  CC_proof :  CC_Cauchy_prop CC_seq}.

Lemma re_is_Cauchy : forall s : CC_CauchySeq, Cauchy_prop (seq_re s).
Proof.
intro s; elim (CC_proof s); auto.
Qed.

Lemma im_is_Cauchy : forall s : CC_CauchySeq, Cauchy_prop (seq_im s).
Proof.
intro s; elim (CC_proof s); auto.
Qed.

Definition CC_Cauchy2re s := Build_CauchySeq _ _ (re_is_Cauchy s).

Definition CC_Cauchy2im s := Build_CauchySeq _ _ (im_is_Cauchy s).

Definition LimCC s : CC := (Lim (CC_Cauchy2re s)) [+I*] (Lim (CC_Cauchy2im s)).

Definition CC_SeqLimit (seq : nat -> CC) (lim : CC) : CProp := forall e,
  Zero [<] e -> {N : nat | forall m, N <= m -> AbsCC (seq m[-]lim) [<=] e}.

Lemma AbsSmall_sqr : forall x e : IR, AbsSmall e x -> x[^]2 [<=] e[^]2.
unfold AbsSmall in |- *. intros. elim H. clear H. intros.
astepl (Zero[+]x[^]2).
apply shift_plus_leEq.
astepr ((e[-]x) [*] (e[+]x)).
apply mult_resp_nonneg.
apply shift_leEq_minus. astepl x. auto.
rstepr (x[-][--]e).
apply shift_leEq_minus. astepl ( [--]e). auto.
Qed.

Lemma AbsSmall_AbsCC : forall (z : CC) (e : IR), Zero [<] e ->
 AbsSmall (e [/]TwoNZ) (Re z) -> AbsSmall (e [/]TwoNZ) (Im z) -> AbsCC z [<=] e.
intros. unfold AbsCC in |- *.
apply power_cancel_leEq with 2. auto.
apply less_leEq. auto.
astepl (Re z[^]2[+]Im z[^]2).
rstepr ((e [/]TwoNZ) [^]2[+] (e [/]TwoNZ) [^]2[+] (e[^]2) [/]TwoNZ).
astepl (Re z[^]2[+]Im z[^]2[+]Zero).
apply plus_resp_leEq_both.
apply plus_resp_leEq_both.
apply AbsSmall_sqr. auto.
apply AbsSmall_sqr. auto.
apply less_leEq.
apply div_resp_pos. apply pos_two.
apply nexp_resp_pos. auto.
Qed.

Lemma LimCC_is_lim : forall s : CC_CauchySeq, CC_SeqLimit s (LimCC s).
unfold CC_SeqLimit in |- *. unfold LimCC in |- *. intros s e H.
cut (SeqLimit (seq_re s) (Lim (CC_Cauchy2re s))).
unfold SeqLimit in |- *. intro H0.
cut (SeqLimit (seq_im s) (Lim (CC_Cauchy2im s))).
unfold SeqLimit in |- *. intro H1.
cut (Zero [<] e [/]TwoNZ). intro H2.
elim (H0 (e [/]TwoNZ) H2). unfold seq_re in |- *. intro N. intros H3.
elim (H1 (e [/]TwoNZ) H2). unfold seq_im in |- *. intro N'. intros H4.
cut {M : nat | N <= M | N' <= M}. intros H5.
elim H5. clear H5. intro M. intros.
exists M. intros.
apply AbsSmall_AbsCC. auto.
astepr (Re (CC_seq s m) [-]Lim (CC_Cauchy2re s)).
apply H3. omega.
astepr (Im (CC_seq s m) [-]Lim (CC_Cauchy2im s)).
apply H4. omega.
elim (le_lt_dec N N'); intros.
exists N'; auto.
exists N; auto with arith.
apply div_resp_pos. apply pos_two. auto.
apply
 Lim_Cauchy
  with
    (s := Build_CauchySeq IR (fun n : nat => Im (CC_seq s n))
            (im_is_Cauchy s)).
apply
 Lim_Cauchy
  with
    (s := Build_CauchySeq IR (fun n : nat => Re (CC_seq s n))
            (re_is_Cauchy s)).
Qed.

Lemma CC_SeqLimit_uniq : forall (s : nat -> CC) (l l' : CC),
 CC_SeqLimit s l -> CC_SeqLimit s l' -> l [=] l'.
unfold CC_SeqLimit in |- *. do 3 intro. intros H H0.
apply cg_inv_unique_2.
apply AbsCC_small_imp_eq. intros e H1.
cut (Zero [<] e [/]ThreeNZ). intro H2.
elim (H (e [/]ThreeNZ)). intro N. intros H3.
elim (H0 (e [/]ThreeNZ)). intro N'. intros H4.
cut {M : nat | N <= M | N' <= M}. intros H5.
elim H5. clear H5. intro M. intros.
apply leEq_less_trans with (AbsCC (s M[-]l) [+]AbsCC (s M[-]l')).
apply leEq_wdl with (AbsCC ( [--] (s M[-]l) [+] (s M[-]l'))).
apply leEq_wdr with (AbsCC [--] (s M[-]l) [+]AbsCC (s M[-]l')).
apply triangle.
algebra.
apply AbsCC_wd. rational.
rstepr (e [/]ThreeNZ[+]e [/]ThreeNZ[+]e [/]ThreeNZ). astepl (Zero[+]AbsCC (s M[-]l) [+]AbsCC (s M[-]l')).
apply plus_resp_less_leEq.
apply plus_resp_less_leEq.
auto.
apply H3. auto.
apply H4. auto.
exists (max N N'); auto with arith.
auto. auto.
apply pos_div_three. auto.
Qed.

Lemma CC_SeqLimit_unq : forall (s : CC_CauchySeq) l, CC_SeqLimit s l -> l [=] LimCC s.
intros.
apply CC_SeqLimit_uniq with (CC_seq s). auto.
apply LimCC_is_lim.
Qed.

(** ** Continuity for [CC]
*)

Section Continuity_for_CC.

(**
%\begin{convention}% Let [f : CC->CC].
%\end{convention}%
*)

Variable f : CC -> CC. (* (CSetoid_un_op CC). *)

Definition CCfunLim (p l : CC) : CProp := forall e : IR, Zero [<] e ->
  {d : IR | Zero [<] d | forall x, AbsCC (p[-]x) [<=] d -> AbsCC (l[-]f x) [<=] e}.

Definition CCcontinAt p : CProp := CCfunLim p (f p).

Definition CCcontin : CProp := forall x : CC, CCcontinAt x.

Lemma CCfunLim_SeqLimit : forall p l pn,
 CCfunLim p l -> CC_SeqLimit pn p -> CC_SeqLimit (fun n => f (pn n)) l.
Proof.
intros p l pn fl sl; unfold CC_SeqLimit in |- *.
intros eps epos.
elim (fl _ epos); intros del H H0.
elim (sl _ H); intros N Nh.
exists N. intros m leNm.
apply leEq_wdl with (AbsCC (l[-]f (pn m))).
apply H0.
apply leEq_wdl with (AbsCC (pn m[-]p)).
apply (Nh _ leNm).
apply cc_minus_abs.
apply cc_minus_abs.
Qed.

Definition f_seq (s : nat -> CC) (n : nat) : CC := f (s n).

Lemma poly_pres_lim : CCcontin ->
 forall s : CC_CauchySeq, CC_SeqLimit (fun n => f (s n)) (f (LimCC s)).
Proof.
intros cp s.
apply (CCfunLim_SeqLimit (LimCC s) (f (LimCC s))).
unfold CCfunLim in |- *.
intros e zlte.
elim (cp (LimCC s) e zlte).
intros d; exists d; auto.
exact (LimCC_is_lim s).
Qed.

End Continuity_for_CC.

Lemma seq_yields_zero : forall q : IR, Zero [<=] q -> q [<] One -> forall c : IR, Zero [<] c ->
 forall s, (forall i, AbsCC (s i) [<=] q[^]i[*]c) -> CC_SeqLimit s Zero.
Proof.
intros q zltq qlt1 c zltc s H.
unfold CC_SeqLimit in |- *.
intros e zlte.
generalize (qi_lim_zero q zltq qlt1).
intro Hqi.
unfold SeqLimit in Hqi.
elim (Hqi (e[/] c[//]pos_ap_zero _ c zltc)).
intros N HN.
exists N.
intros m leNm.
apply leEq_transitive with (q[^]m[*]c).
astepl (AbsCC (s m)).
apply H.
generalize (HN m leNm).
intro H0.
unfold AbsSmall in H0.
inversion_clear H0.
rstepr ((e[/] c[//]pos_ap_zero IR c zltc) [*]c).
apply mult_resp_leEq_rht.
rstepl (q[^]m[-]Zero).
assumption.
apply less_leEq. assumption.
apply shift_less_div.
assumption.
rstepl ZeroR; assumption.
Qed.
