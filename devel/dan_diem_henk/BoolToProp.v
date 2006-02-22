Require Export Arith.
Require Export Bool.
Require Export Le.
Require Export bp.

Implicit Types n m : nat.

Fixpoint beq n m {struct n} : bool :=
match n, m with
   | O, O => true
   | S n', O => false
   | O, S m' => false
   | S n', S m' => (beq n' m')
   end.

Infix "=b" := beq (at level 4).

Fixpoint bleq n m {struct n} : bool :=
   match n, m with
   | O, _ => true
   | S n', O => false
   | S n', S m' => (bleq n' m')
   end.

Definition blt n m := bleq (S n) m.

Infix "<<=" := bleq (at level 4).
Infix "<<" := blt (at level 4).

Ltac btriv := 
        try (intro H);
        try (inversion H);
        unfold bp;
        try reflexivity.

Ltac aa := try assumption.

Ltac ap x:= apply x; aa; aa.

Lemma blte_imp_lte : forall n m, n<<=m -> n<=m.
Proof.
induction n.
intros m _.
apply (le_O_n m).
destruct m; simpl.
btriv.
intro P.
assert (n<=m).
ap (IHn m P).
ap le_n_S.
Qed.

Lemma lte_imp_blte : forall n m, n<=m -> n<<=m.
Proof.
induction n; intros m P.
btriv.
destruct m.
elim (le_Sn_O n P).
simpl.
apply IHn.
apply le_S_n with (1:=P).
Qed.

Lemma lt_imp_blt : forall n m,  n < m ->((n<<m) = true).
Proof.
intros n.
induction n.
destruct m.
intros.
inversion H.
unfold blt.
simpl.
reflexivity.
destruct m; simpl; intros.
inversion H.
unfold blt.
simpl.
unfold blt in IHn.
simpl in IHn.
apply IHn.
auto with arith.
Qed.


Lemma blt_imp_lt : forall n m,((n<<m) = true)->  n < m.
Proof.
intros n.
induction n.
destruct m.
intros.
inversion H.
intros.
auto with arith.
destruct m.
simpl.
intros.
inversion H.
unfold blt.
simpl.
intro.
assert (n < m).
apply IHn.
unfold blt.
assumption.
auto with arith.
Qed.

Lemma beq_imp_eq: forall n m,((n =b m) = true)->  n = m.
Proof.
induction n.
destruct m.
reflexivity.
intros.
inversion H.
destruct m.
intros.
inversion H.
simpl.
intros.
generalize (IHn m H); intro; auto with arith.
Qed.

Lemma eq_imp_beq : forall n m, n = m -> ((n =b m) = true).
Proof.
induction n.
destruct m.
reflexivity.
intros.
inversion H.
destruct m.
intros.
inversion H.
simpl.
intros.
apply IHn.
auto with arith.
Qed.

Hint Resolve lte_imp_blte lt_imp_blt eq_imp_beq:pbdb.
Hint Resolve blte_imp_lte blt_imp_lt beq_imp_eq:bpdb.

Lemma disjlemmabp :
  forall a b: bool,   
  ((orb a b) = true)-> 
  forall A B  : Prop, 
  (a = true -> A) -> (b = true -> B ) 
  -> (A \/ B).
Proof.
intros a b.
elim a.
intros H A B H1 H2.
left.
apply H1.
trivial.
elim b.
intros H A B H1 H2.
right.
apply H2.
trivial.
intros H A B H1 H2.
simpl in H.
inversion H.
Qed.

Implicit Arguments disjlemmabp [a b].

Lemma disjlemmapb : 
  forall A B : Prop, 
  (A \/ B) -> 
  forall a b : bool, 
  (A-> a = true) -> 
  (B -> b = true) ->
  (orb a b) = true.
Proof.
intros A B H a b.
elim H.
intros.
rewrite (H1 H0).
elim b.
simpl; trivial.
simpl; trivial.
intros.
rewrite (H2 H0).
elim a.
simpl; trivial.
simpl; trivial.
Qed.

Implicit Arguments disjlemmapb [A B].

Lemma conjlemmabp : 
  forall a b: bool,
  ((andb a b) = true) -> 
  forall A B  : Prop, 
  (a = true -> A) ->
  (b = true -> B ) -> 
  (A /\ B).
Proof.
intros a b.
elim b; elim a.
intros H A B H1 H2.
split.
apply H1; trivial.
apply H2; trivial.
intro H.
simpl in H; inversion H.
intro H.
simpl in H; inversion H.
intro H.
simpl in H;  inversion H.
Qed.

Implicit Arguments conjlemmabp [a b ].

Lemma conjlemmapb :
  forall A B : Prop, 
  (A /\ B) -> 
  forall a b : bool, 
  (A-> a = true) ->
  (B -> b = true) ->  
  (andb a b) = true.
Proof.
intros A B H a b.
elim H.
intros.
rewrite (H2 H0).
rewrite (H3 H1).
simpl; trivial.
Qed.

Implicit Arguments conjlemmapb [A B ].

Lemma implemmabp : 
  forall a b: bool,
  ((implb a b) = true) -> 
  forall A B  : Prop, 
  (A -> a = true) ->
  (b = true -> B) -> 
  (A -> B).
Proof.
intros a b.
elim b; elim a.
intros _ A B _  H2 _.
apply H2; trivial.
intros _ A B H1 _ pa.
generalize (H1 pa); intro H2; inversion H2.
intro H; inversion H.
intros _ A B H1 _ pa.
generalize (H1 pa); intro H2; inversion H2.
Qed.
Implicit Arguments implemmabp [a b ].

Lemma implemmapb :
  forall A B : Prop, 
  (A ->  B) -> 
  forall a b : bool, 
  (a = true -> A) ->
  (B -> b= true) ->
  (implb a b) = true.
Proof.
intros A B H a b.
elim a; elim b.
intros.
simpl; trivial.
intros.
assert (true = true).
reflexivity.
generalize (H1 (H (H0 H2))).
intro.
inversion H3.
intros.
simpl; trivial.
intros; simpl; trivial.
Qed.

Implicit Arguments implemmapb [A B ].

Lemma implemma :
  forall A B A' B': Prop, 
  (A ->  B) -> 
  (A' -> A) ->
  (B -> B') ->
  (A' -> B').
Proof.
intros.
apply H1.
apply H.
apply H0.
apply H2.
Qed.

Implicit Arguments implemma [A B].

Lemma notlemmabp :
  forall a : bool, 
  negb a = true -> 
  forall A : Prop, 
  (A -> a = true)-> ~A.
Proof.
intro a.
elim a.
intro H; inversion H.
intros _ A H pa.
generalize (H pa); intro H1; inversion H1.
Qed.

Implicit Arguments notlemmabp [a].

Lemma notlemmabp_false :
  forall a : bool, 
  a = false -> 
  forall A : Prop, 
  (A -> a = true)-> ~A.
Proof.
intro a.
elim a.
intro H; inversion H.
intros _ A H pa.
assert (H0 := H pa); inversion H0.
Qed.

Implicit Arguments notlemmabp_false [a].

Lemma notlemmapb :
  forall A : Prop, 
  ~A -> 
  forall a : bool, 
  (a = true -> A) -> 
  (negb a ) = true.
Proof.
intros A H a.
elim a.
intros.
assert (true = true); trivial.
elim (H ( H0 H1)).
intros.
simpl; trivial.
Qed.

Implicit Arguments notlemmapb [A].

Lemma notlemma : 
  forall A A' : Prop, 
  ~A -> (A' -> A)-> (~ A' ).
Proof.
intros.
intro.
apply H.
apply H0.
apply H1.
Qed.

Implicit Arguments notlemma [A].

Lemma falsetonegb:
   forall a:bool, negb a = true -> a = false.
destruct a.
simpl.
intro H; inversion H.
reflexivity.
Qed.

Ltac boolToPropFormula F :=
 match F with
    true => True
 |  false => False
 |  (andb ?f1 ?f2) => let c1 := boolToPropFormula f1 with c2 := boolToPropFormula f2 in constr:(and c1 c2)
 |  (orb ?f1 ?f2) => let c1 := boolToPropFormula f1 with c2 := boolToPropFormula f2 in constr:(or c1 c2)
 |  (implb ?f1 ?f2) => let c1 := boolToPropFormula f1 with c2 := boolToPropFormula f2 in constr:(c1 -> c2)
 |  (negb ?f1) => let c1 := boolToPropFormula f1 in constr:(~ c1)
 |  (?n1 <<= ?n2) => constr:(n1 <= n2)
 |  (?n1 << ?n2) => constr:(n1 < n2)
 |  (?n1 =b ?n2) => constr:(n1 = n2)
 |  ?p => constr:(eq p true)
 end.

Ltac preBoolToPropFormula F :=
 match F with
 |  True => True
 |  False => False
 |  (?f1 /\ ?f2) => let c1 := preBoolToPropFormula f1 with c2 := preBoolToPropFormula f2 in constr:(c1 /\ c2)
 |  (?f1 \/ ?f2) => let c1 := preBoolToPropFormula f1 with c2 := preBoolToPropFormula f2 in constr:(c1 \/ c2)
 |  (?f1 -> ?f2) => let c1 := preBoolToPropFormula f1 with c2 := preBoolToPropFormula f2 in constr:(c1 -> c2)
 |  (~ ?f1) => let c1 := preBoolToPropFormula f1 in constr:(~ c1)
 |  (eq ?b true) => boolToPropFormula b
 |  (eq ?b false) => boolToPropFormula (negb b)
 |  ?p => p
 end.

Ltac propToBoolFormula F :=
 match F with
    True => true
 |  False => false
 |  (and ?f1 ?f2) => let c1 := propToBoolFormula f1 with c2 := propToBoolFormula f2 in constr:(andb c1 c2)
 |  (or ?f1 ?f2) => let c1 := propToBoolFormula f1 with c2 := propToBoolFormula f2 in constr:(orb c1 c2)
 |  (?f1 -> ?f2) => let c1 := propToBoolFormula f1 with c2 := propToBoolFormula f2 in constr:(implb c1 c2)
 |  (~ ?f1) => let c1 := propToBoolFormula f1 in constr:(negb c1)
 |  (?n1 <= ?n2) => constr:(n1 <<= n2)
 |  (?n1 < ?n2) => constr:(n1 << n2)
 |  (?n1 = ?n2) => constr:(n1 =b n2)
 |  (eq ?b true) => b
 |  (eq ?b false) => constr:(negb b)
 |  ?f1 => fail "I cannot make a bool out of that!" (* f1 should be printed *)
 end.

Ltac boolToPropSolve H := 
   match goal with 
     | |- (eq (andb ?b1 ?b2) true) => 
            (apply (conjlemmapb H); 
              [(let H := fresh "H" 
                in (intro H; boolToPropSolve H))
              |(let H := fresh "H" 
                in (intro H; boolToPropSolve H))])
     | |- (eq (orb ?b1 ?b2) true) => 
            (apply (disjlemmapb H); 
              [(let H := fresh "H" 
                in (intro H; boolToPropSolve H))
              |(let H := fresh "H" 
                in (intro H; boolToPropSolve H))])
     | |- (eq (implb ?b1 ?b2) true) => 
            (apply (implemmapb H); 
              [(let H := fresh "H" 
                in (intro H; propToBoolSolve H))
              |(let H := fresh "H" 
                in (intro H; boolToPropSolve H))])
     | |- (eq (negb ?b1) true) => 
            (apply (notlemmapb H); 
              (let H := fresh "H" 
               in (intro H; propToBoolSolve H)))
     | |- (eq true true) => trivial
     | |- (eq false true) => inversion H  
     | |- (eq ?b false) => apply falsetonegb; boolToPropSolve H
     | |- _ => auto with pbdb
   end

with propToBoolSolve H := 
   match goal with 
     | |- (and ?b1 ?b2)  => 
            (apply (conjlemmabp H); 
              [(let H := fresh "H" 
                in (intro H; propToBoolSolve H))
              |(let H := fresh "H" 
                in (intro H; propToBoolSolve H))])
     | |- (or ?b1 ?b2) => 
            (apply (disjlemmabp H); 
              [(let H := fresh "H" 
                in (intro H; left; propToBoolSolve H))
              |(let H := fresh "H" 
                in (intro H; left; propToBoolSolve H))])
     | |-  (?b1 -> ?b2) => 
            (apply (implemmabp H b1 b2); 
              [(let H := fresh "H" 
                in (intro H; boolToPropSolve H))
              |(let H := fresh "H" 
                in (intro H; propToBoolSolve H))])
     | |- (~ ?b1) => 
            match type of H with
              (eq ?b false) =>
               (apply (notlemmabp_false H); 
                (let H := fresh "H" 
                 in (intro H; boolToPropSolve H)))
            | _ =>
               (apply (notlemmabp H); 
                (let H := fresh "H" 
                 in (intro H; boolToPropSolve H)))
            end
     | |- True => trivial
     | |- False => inversion H(* ???  *)
     | |- _ => auto with bpdb
   end.

Ltac preBoolToPropSolve H := 
   match goal with 
     | |- (?b1 /\?b2)  => 
            (elim H; 
             let H1 := fresh "H" in let H2 := fresh "H" in 
              (intros H1 H2; split; [preBoolToPropSolve H1; preBoolToPropSolve H2]))
     | |- (?b1 \/ ?b2) => 
            (elim H; 
              [let H1 := fresh "H" in (intro H1; left; preBoolToPropSolve H1) 
              |let H2 := fresh "H" in (intro H2; right; preBoolToPropSolve H2)])
     | |-  (?b1 -> ?b2) => 
            (apply (implemma b1 b2 H); 
              [(let H := fresh "H" in (intro H; prePropToBoolSolve H))
              |(let H := fresh "H" in (intro H; preBoolToPropSolve H))])
     | |- (~ ?b1) => 
            (apply (notlemma b1 H); 
              (let H := fresh "H" in (intro H; prePropToBoolSolve H)))
     | |- True => trivial
     | |- False => elim H(* ???  *)
     | |- _ => boolToPropSolve H
    end

with prePropToBoolSolve H := 
   let dummy := type of H in 
   match constr:dummy  with 
     (?b1 /\ ?b2)  => 
      (elim H; let H1 := fresh "H" in let H2 := fresh "H" in 
                 (intros H1 H2; split; [prePropToBoolSolve H1; prePropToBoolSolve H2]))
   | (?b1 \/ ?b2) => 
      (elim H; [let H1 := fresh "H" in (intro H1; prePropToBoolSolve H1) 
               |let H2 := fresh "H" in (intro H2; prePropToBoolSolve H2)])
   | (?b1 -> ?b2) => 
      (apply (implemma b1 b2 H); 
        [(let H := fresh "H" in (intro H; preBoolToPropSolve H))
        | (let H := fresh "H" in (intro H; prePropToBoolSolve H))])
   | (~ ?b1) => 
      (apply (notlemma b1 H); (let H := fresh "H" in (intro H; preBoolToPropSolve H)))
   | True => trivial
   | False => inversion H(* ???  *)
   | _ => propToBoolSolve H
  end.

Ltac boolToProp :=
   unfold bp; 
   match goal with 
    | |- ?b  => 
      let dummy := preBoolToPropFormula b with v := fresh "H" 
      in (cut dummy; [intro v; preBoolToPropSolve v | idtac])
(*    | |- _ => fail "Your goal is not of the form ?b = true"*)
   end.

Ltac propToBool :=
   unfold bp;
   match goal with 
    | |- ?b => 
      let dummy := propToBoolFormula b with v := fresh "H" 
      in (cut (bp dummy ); [intro v; prePropToBoolSolve v | idtac])
   end.

Ltac boolToProp_in H :=
  unfold bp in H;
  match type of H with
    ?b => let dummy := preBoolToPropFormula b 
          in (assert dummy; [propToBoolSolve H | idtac])
  end.

Ltac propToBool_in H :=
  unfold bp in H;
  let b := type of H in 
  let dummy := propToBoolFormula b 
  in (assert (dummy = true); [boolToPropSolve H | idtac]).

