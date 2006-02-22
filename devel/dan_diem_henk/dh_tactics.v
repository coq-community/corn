Ltac id := exact (fun H => H).

Ltac simpl_all := simpl in *|-* .

Ltac ex_falso :=
  match goal with
  |  H : False |- _ => destruct H
  |  |- context[False_rect _ ?H] => destruct H
  |  _ : context[False_rect _ ?H] |- _ => destruct H
  end.

Ltac cut_case t :=
  cut (t = t); 
  [ pattern t at -1; case t | reflexivity ].

Ltac expl_case t :=
  cut_case t; intros until 1.

(* tbd : load [ list of assumptions ] *)
Ltac load x := 
  generalize x; clear x.

Ltac rewrite_in_cxt H :=
  let T := type of H in
  match T with
  | ?t1 = ?t2 =>
      repeat
      (
      generalize H; clear H; 
      match goal with
      | id : context[t1] |- _ =>
          intro H; rewrite H in id
      end
      )
  end.

Ltac rewrite_all H :=
  rewrite_in_cxt H; rewrite H.

Ltac replace_in_cxt t1 t2 :=
  let H := fresh "H" in
  (cut (t1 = t2); [ intro H; rewrite_in_cxt H; clear H | idtac ]).

Ltac replace_all t1 t2 :=
  let H := fresh "H" in
  (cut (t1 = t2); [ intro H; rewrite_all H; clear H | idtac ]).

(*
Ltac rewrite_at n H :=
  match H with 
  ?t = ?u => pattern t at n; rewrite H.
*)

Lemma p_iff_p : 
  forall p : Prop,
  p <-> p.
Proof.
intro p.
split; id.
Qed.

Hint Resolve p_iff_p.
