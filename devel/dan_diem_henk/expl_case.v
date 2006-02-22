Ltac cut_case t :=
  cut (t = t); 
  [ pattern t at -1; case t | reflexivity ].

Ltac expl_case t :=
  cut_case t; intros until 1.

Ltac load x := 
  generalize x; clear x.

