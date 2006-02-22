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
