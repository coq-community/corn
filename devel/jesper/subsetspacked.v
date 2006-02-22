(** This file provides packed versions of subsets with equivalence
relations. It demonstrates how the subsets module can be used. It is
often better to use the subsets module directly rather than this file.

Written by Jesper Carlstrom, Spring 2004, University of
Nijmegen. Financed by Calculemus.

*)

Require Export subsets.

Set Implicit Arguments.
Unset Strict Implicit.

(** Let's define an extension of auto, because auto doesn't understand
that an equivalence relation is reflexive, etc. *)

Ltac sauto := auto with subsets.

(** Putting the following definition in CProp gives a universe
inconsistency, hence we put it in Type *)

Record eq_rel (A:Type)(R:bin A):Type :=
{  eq_rel_refl:refl R;
   eq_rel_sym:sym R ;
   eq_rel_trans:trans R }.


Lemma extequal_eq: forall (A:Type), eq_rel (extequal (carrier:=A)).
Proof.
split.
    apply extequal_refl.
  apply extequal_sym.
apply extequal_trans.
Qed.


Record eq_part (A:Type)(U:subset A)(R:bin_on U): CProp :=
{
   eq_part_pirr:   proofirr R ;
   eq_part_refl:   refl_part R;
   eq_part_sym:    sym_part R;
   eq_part_tr:     trans_part R
}.

(** Teach sauto that equivalence relations are reflexive, etc *)

Hint Immediate eq_part_pirr : subsets.
Hint Immediate eq_part_refl : subsets.
Hint Immediate eq_part_sym : subsets.
Hint Immediate eq_part_tr : subsets.


Lemma reflexive_closure_of_eq_eq: forall (A:Type)(U:subset A)(R:bin_on U),
   eq_part R -> eq_rel (reflexive_closure R).
Proof.
intros A U R [Href Hsym Htr Hext].
split.
    apply reflexive_closure_refl.
  apply reflexive_closure_of_sym_sym; assumption.
apply reflexive_closure_of_pirr_trans_trans; assumption.
Qed.

Lemma same_eq: forall (A:Type)(U:subset A), eq_part (same U).
Proof.
intros A U.
split; compute; auto.
intros x _ y _ z _ p q.
transitivity y; assumption.
Qed.


Record surjective (A B:Type) (U:subset A) (V:subset B) (RV:bin_on V) (f:U~>B)
: CProp := {
   fun_i: into V f ;
   inv : V ~> A ;
   inv_i: into U inv ;
   isinv_pf : isinv RV f inv }.

Record quotient : Type :=
{
   q_carrier: Type ;
   q_subset:  subset q_carrier ;
   q_rel:     bin_on q_subset ;
   q_eq:      eq_part q_rel
}.

(** Teach sauto that the relation of a quotient is an equivalence. In
practice, this is used as a first step towards proving that it is
reflexive and proof-irrelevant. *)

Hint Resolve q_eq : subsets.

(** The automatic implicit arguments mechanism makes a bit too much
implicit, so we tell it not to make things implicit in the following
cases. *)

Implicit Arguments q_subset [].
Implicit Arguments q_rel [].

Record quotientfunction (Q1 Q2:quotient) : Type :=
{
   qf_function: (q_subset Q1) ~> (q_carrier Q2) ;
   qf_into:     into (q_subset Q2) qf_function ;
   qf_ext:      extensional (q_rel Q1) (q_rel Q2) qf_function 
}.

Definition identityfun (Q1:quotient) : quotientfunction Q1 Q1.
intros [A U R eqp].
exists (underlying (domain:=U)).
  exact (fun _ x => x).
compute; intros x' x1 y' y1 x2 y2 eq.
apply (eq_part_pirr eqp) with x1 y1; assumption.
Defined.

Definition q_extequal (Q1 Q2:quotient) (f g:quotientfunction Q1 Q2) : CProp
:=
for x in (q_subset Q1), q_rel Q2 _ (qf_into f x) _ (qf_into g x).

Lemma q_extequal_refl: forall Q1 Q2:quotient,
   refl (q_extequal (Q1:=Q1) (Q2:=Q2)).
Proof.
intros Q1 Q2 f x' x.
apply (eq_part_refl (q_eq Q2)).
Qed.

Lemma q_extequal_sym: forall Q1 Q2:quotient,
   sym (q_extequal (Q1:=Q1) (Q2:=Q2)).
Proof.
intros Q1 Q2 f g eq x' x.
apply (eq_part_sym (q_eq Q2)).
apply eq.
Qed.

Lemma q_extequal_tr: forall Q1 Q2:quotient,
   trans (q_extequal (Q1:=Q1) (Q2:=Q2)).
Proof.
intros Q1 Q2 f g h fg gh x' x.
apply (eq_part_tr (q_eq Q2)) with (qf_function g x) (qf_into g x).
  apply fg.
apply gh.
Qed.

Lemma q_extequal_eq: forall Q1 Q2:quotient,
  eq_rel (q_extequal (Q1:=Q1) (Q2:=Q2)).
Proof.
intros Q1 Q2.
split. 
    apply q_extequal_refl.
  apply q_extequal_sym.
apply q_extequal_tr.
Qed.

Definition q_composition (Q1 Q2 Q3:quotient) 
                         (f:quotientfunction Q1 Q2) 
			 (g:quotientfunction Q2 Q3) 
			  : (quotientfunction Q1 Q3).
intros Q1 Q2 Q3 f g.
exists (composition (qf_function g) (qf_into f)).
  intros x' x.
  unfold composition.
  apply (qf_into g).
unfold composition.
intros x' x y' y z w eq.
apply (qf_ext (q:=g)).
apply (qf_ext (q:=f)).
assumption.
Defined.

Lemma q_composition_associative: forall (Q1 Q2 Q3 Q4:quotient) 
                                        (f:quotientfunction Q1 Q2)
		        		(g:quotientfunction Q2 Q3)
					(h:quotientfunction Q3 Q4),
   (q_composition f (q_composition g h)) 
    = 
   (q_composition (q_composition f g) h).
Proof.
reflexivity.
Qed.

Lemma q_composition_identity: forall (Q1 Q2:quotient)
                                     (f:quotientfunction Q1 Q2),
                        q_extequal (q_composition f (identityfun Q2))
                                   f.
Proof.
intros Q1 [B V RV RVeq] f x' x.
apply (eq_part_refl RVeq).
Qed.

Lemma q_composition_ext:  forall (Q1 Q2 Q3:quotient) 
                                        (f:quotientfunction Q1 Q2)
		        		(g:quotientfunction Q2 Q3)
                                        (f':quotientfunction Q1 Q2)
		        		(g':quotientfunction Q2 Q3),
  q_extequal f f' ->
  q_extequal g g' ->
  q_extequal (q_composition f g) (q_composition f' g').
Proof.
intros Q1 Q2 Q3 f g f' g' feq geq.
apply q_extequal_tr with (q_composition f g'); intros x' x; 
                              simpl; unfold composition.
  apply geq.
apply (qf_ext (q:=g')).
apply feq.
Qed.

Definition q_injective (Q1 Q2:quotient) (f:quotientfunction Q1 Q2): CProp:=
  injective (q_rel Q1) (q_rel Q2) (qf_function f).


(** *** Split surjective

We define what Bishop called 'onto': a function has an extensional
right inverse. Because onto is used in other ways by others, we prefer
to adopt the category-theoretical terminology 'split'.

A few lines below we define also the weaker notion of surjectivity. *)

Record q_split_surjective (Q1 Q2:quotient) (f:quotientfunction Q1 Q2) : CProp :=
{
   q_inv : quotientfunction Q2 Q1 ;
   q_isinv_pf : q_extequal (q_composition q_inv f) (identityfun Q2)
}.

(** *** Surjective = having (not necessarily extensional) right inverse *)


Record q_surjective (Q1 Q2:quotient) (f:quotientfunction Q1 Q2) : CProp :=
{
   q_surj_inv : (q_subset Q2) ~> (q_carrier Q1) ;
   q_surj_inv_i : into (q_subset Q1) q_surj_inv ;
   q_isid : isinv (q_rel Q2) (qf_function f) q_surj_inv
}.

(** Split surjectivity is a stronger notion than surjectivity: *)

Remark split_surjective_surjective: forall (Q1 Q2:quotient)
                                           (f:quotientfunction Q1 Q2),
                                           q_split_surjective f ->
                                           q_surjective f.
intros [A U RU RUeq]
       [B V RV RVeq]
       [f f_i f_ext] 
       [[f_inv f_inv_i f_inv_ext] isid]; compute in isid.
exists f_inv; simpl; trivial.
intros y' y1 x y2.
apply (eq_part_tr RVeq) with (f _ (f_inv_i _ y1)) 
                           (f_i _ (f_inv_i _ y1)); trivial.
apply f_ext.
apply strongrefl; sauto.
Qed.


Record q_bijective (Q1 Q2:quotient) (f:quotientfunction Q1 Q2): CProp := 
{
  bij_inv : quotientfunction Q2 Q1 ;
  bij_right_inv : q_extequal (q_composition f bij_inv) (identityfun Q1) ;
  bij_left_inv  : q_extequal (q_composition bij_inv f) (identityfun Q2) 
}.

Let theinv (Q1 Q2:quotient) (f:quotientfunction Q1 Q2) (inj:q_injective f)(surj:q_surjective f) : quotientfunction Q2 Q1.
intros [A U RU [RUpirr RUrefl RUsym RUtr]] 
       [B V RV [RVpirr RVrefl RVsym RVtr]] 
       [f f_i f_ext] 
	inj 
       [f_inv f_inv_i isid]; compute in isid|-*.
exists f_inv; simpl.
  apply f_inv_i.
apply inv_ext with f; trivial.
Defined.


Theorem bijective: forall (Q1 Q2:quotient) (f:quotientfunction Q1 Q2),
      q_injective f ->
      q_surjective f ->
      q_bijective f.
Proof.
intros [A U RU [RUpirr RUrefl RUsym RUtr]] 
       [B V RV [RVpirr RVrefl RVsym RVtr]] 
       [f f_i f_ext]
	inj 
       [f_inv f_inv_i isid].
exists (theinv inj (Build_q_surjective f_inv_i isid)); simpl in *|-;
                      compute; intros.
  cut (isinv RU f_inv f); trivial.
  apply inv_leftinv with RV; trivial.
apply isid.
Qed.

(** The following lemma can be seen as a choice principle, since it
says that if a function is surjective in the sense that the image is
equal to the codomain, it is surjective also in our sense, that is,
there is a (not necessarily extensional) right inverse. *)
 
Lemma issurj: forall (Q1 Q2:quotient) (f:quotientfunction Q1 Q2),
   (for y in (q_subset Q2),
   exists x in (q_subset Q1),
   (q_rel Q2) _ ((qf_into f) _ x) _ y) ->
   q_surjective f.
Proof.
intros Q1 Q2
       [f f_i f_ext] 
       H; simpl in *|-.
exists  (fun y' y => (proj1_sigT _ _ (H y' y))); simpl.
  intros y' y.
  compute; elim (H y' y); intro; destruct 1; trivial.
intros y' y1 x y2;
destruct (H y' y1) as [x' [x2 eq]]; clear H; simpl in *|-*.
apply (eq_part_tr (q_eq Q2)) with (f _ x2) (f_i _ x2); trivial.
apply f_ext.
apply strongrefl; sauto.
Qed.

                 
Lemma q_composition_surjective: forall Q1 Q2 Q3:quotient,
                                forall f:quotientfunction Q1 Q2,
                                forall g:quotientfunction Q2 Q3,
                                q_surjective f ->
                                q_surjective g ->
                                q_surjective (q_composition f g).
Proof.
intros Q1 Q2 Q3 f g [f_inv f_inv_i fisid] [g_inv g_inv_i gisid].
exists (gfinv f_inv g_inv_i); unfold q_composition; simpl.
  apply gfinv_i; assumption.
destruct g; apply gfisid with (q_rel Q2); sauto.
Qed.



Definition q_fineq (n:nat) :eq_part (fineq (n:=n)).
intros n.
unfold fineq.
apply same_eq.
Defined.

Definition q_fin (n:nat) : quotient :=
   Build_quotient (q_fineq n).

Record finite (F:quotient) : CProp := 
{
   cardinality: nat ;
   enum:quotientfunction (q_fin cardinality) F ;
   enum_inj:q_injective enum ;
   enum_surj:q_surjective enum
}.

Lemma q_finite_discrete: forall F:quotient,
        finite F -> discrete (q_rel F).
Proof.
intros [A U RU [RUpirr RUrefl RUsym RUtr]] 
  [n [en en_i en_ext] inj [label label_i isid]];simpl in *|-*.
eapply (finite_discrete RUpirr RUrefl RUsym RUtr en_i); trivial.
  apply label_i.
assumption.
Qed.


Definition q_choice_function (F Q:quotient)
                             (f:quotientfunction Q F)
                             (fsurj:q_surjective f)
                             (Hfin:finite F):
quotientfunction F Q.  
intros F Q f fsurj [n [en en_i en_ext] inj [label label_i isid]]; simpl in *|-.
destruct fsurj as [f_inv f_inv_i fisid].
exists (finite_choice_function en_i label_i f_inv).
  apply finite_choice_function_i.
  apply f_inv_i.
apply finite_choice_ext; sauto.
Defined.

Lemma q_finite_choice: forall (F Q:quotient)
                              (f:quotientfunction Q F),
                              finite F ->
                              q_surjective f ->
                              q_split_surjective f.
Proof.
intros [A U RU [RUpirr RUrefl RUsym RUtr]] Q [f f_i f_ext] Hfin fsurj;
simpl in *|-*.
exists (q_choice_function fsurj Hfin).
intros x' x; simpl in *|-*.
destruct fsurj as [g g_i fgisid];
destruct Hfin as [n [en en_i en_ext] inj [label label_i isid]];
simpl in *|-*.
unfold composition.
apply finite_choice; assumption.
Qed.




