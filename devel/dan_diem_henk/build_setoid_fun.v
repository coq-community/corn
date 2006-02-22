Require Export Setoids.

Ltac prove_well_def :=
  match goal with
  | |- (std_rel ?B (sf_fun ?A ?B ?f _) (sf_fun ?A ?B ?f _)) =>
      apply (sf_wd A B f); ( assumption || prove_well_def )
  | |- (std_rel ?C (sbf_fun ?A ?B ?C ?f _ _) (sbf_fun ?A ?B ?C ?f _ _)) =>
      apply (sbf_wd A B C f); ( triv || prove_well_def )
  | _ => fail 1 "can't prove well-definedness"
  end.

Ltac build_setoid_un_fun f :=
  let x := fresh "x" in
  let y := fresh "y" in
  let H := fresh "H" in
  (
  apply Build_Setoid_fun with (sf_fun:=f);
  intros x y H;
  ( triv || prove_well_def )
  ).

Ltac build_setoid_bin_fun f :=
  let x1 := fresh "x" in
  let x2 := fresh "x" in
  let y1 := fresh "y" in
  let y2 := fresh "y" in
  let Hx  := fresh "H" in
  let Hy  := fresh "H" in
  (
  apply Build_Setoid_bin_fun with (sbf_fun:=f);
  intros x1 x2 y1 y2 Hx Hy;
  try ( destruct x1; destruct x2; destruct y1; destruct y2 );
  ( triv || prove_well_def )
  ).

Ltac build_setoid_fun' f :=
  let F := type of f in
  match F with
  | ?S1 -> ?S2 -> ?S3 => build_setoid_bin_fun f
  | ?S1 -> ?S2        => build_setoid_un_fun f
  | _                 => fail "your appropriate error message"
  end.

(* try to unfold f *)
Ltac build_setoid_fun f :=
  ( 
  let f' := ( eval unfold f in f ) in
  build_setoid_fun' f'
  )
  ||
  build_setoid_fun' f.
