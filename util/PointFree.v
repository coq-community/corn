Require Import Coq.Program.Program Coq.Unicode.Utf8 CoRN.stdlib_omissions.Pair.
Generalizable All Variables.

(** In the following type class, r is an "output parameter" in the sense
 that we will have unification infer it. We cannot turn r into a field instead,
 because that would hide it behind a projection, which hinders further
 scrutiny. *)

Class PointFree {T} (f r: T): Prop := pointfree_eq: f = r.

(** If no other instances match, give up and declare the thing point-free: *)

Instance proper_pf {T} (x: T): PointFree x x | 9.
Proof. firstorder. Qed.

(** Instances for various forms of lambdas: *)

Instance eta_pf {A B} (f: A → B) `{!PointFree f f'}: PointFree (λ x, f x) (f' ∘ id)  | 10.
Proof. firstorder. Qed.

Instance const_pf {A B} (b: B): PointFree (λ _: A, b) (const b).
Proof. firstorder. Qed.

Instance id_pf {A}: PointFree (λ x: A, x) id.
Proof. firstorder. Qed.

Instance pair_pf {A B C} (f: A → B) (g: A → C) `{!PointFree f f'} `{!PointFree g g'}:
   PointFree (λ x: A, (f x, g x)) (map_pair f' g' ∘ diagonal).
Proof. compute. rewrite PointFree0, PointFree1. reflexivity. Qed.
  (* This one may not be strictly needed in the presence of binapp_pf below. *)

Instance compose_pf {A B C} (f: B → C) (g: A → B)
  `{!PointFree f f'} `{!PointFree g g'}: PointFree (λ x, f (g x)) (f' ∘ g').
Proof. compute. rewrite PointFree0, PointFree1. reflexivity. Qed.

Instance binapp_pf {A B C D} (f: A → B → C) (g: D → A) (h: D → B)
  `{!PointFree f f'} `{!PointFree g g'} `{!PointFree h h'}:
     PointFree (λ x: D, f (g x) (h x)) (uncurry f' ∘ map_pair g' h' ∘ diagonal).
Proof. compute. rewrite PointFree0, PointFree1, PointFree2. reflexivity. Qed.

Instance uncur_pf {A B C} (f: A → B → C) `{!PointFree (λ p, f (fst p) (snd p)) f'}: PointFree (uncurry (λ x: A, f x)) f'.
Proof. compute. rewrite <- PointFree0. reflexivity. Qed.

(*
  (* In the following tests, the Print's should show that the second argument inferred for PointFree is actually point-free. *)
Definition test0: PointFree (@fst (unit*unit) unit) _ := _.
Check test0.
Definition test1: PointFree (λ x: unit * unit * unit, fst x) _ := _.
Check test1.
Definition test2: PointFree (λ x: unit * unit * unit, fst (fst x)) _ := _.
Check test2.
Definition test3: PointFree (λ x: unit, (x, x)) _ := _.
Check test3.
Definition test4: PointFree (λ x: unit, const x (const x x)) _ := _.
Check test4.
Definition test5: PointFree (uncurry (λ x y: unit, const x (const y x))) _ := _.
Check test5.
Definition test6: PointFree (uncurry (λ x y: unit, id y)) _ := _.
Check test6.
Definition test7: PointFree (uncurry (λ x y: unit, x)) _ := _.
Check test7.

(* Todo: The set of instances currently generates "uncurry const" (which is equivalent to "fst") sometimes (e.g. for test4 above).
 If this turns out to be annoying, we can probably get rid of it by adding more specialized and prioritized instances. *)
*)
