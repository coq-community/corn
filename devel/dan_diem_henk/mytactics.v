Ltac aa := 
  try assumption.

Ltac rr x :=
  rewrite -> x; aa.

Ltac rl x :=
  rewrite <- x; aa.

Ltac spl :=
  split; intros; aa.

Ltac get x y z :=
  elim x; try intro y; try intro z; aa; clear x.

Ltac getc x y z :=
  elim x; intros y z.

Ltac ap x:= apply x; aa.

Ltac el x y :=
  elim x; try intro y; aa.

Ltac simpl_all := simpl in * |- * .
