
Require Import
 Unicode.Utf8 Setoid Arith List Program
 CSetoids Qmetric Qring ProductMetric QposInf
 UniformContinuity
 stdlib_omissions.Pair stdlib_omissions.Q PointFree
 interfaces.canonical_names
 interfaces.abstract_algebra
 MathClasses.theory.setoids.

Section make_RSetoid.

  Context A `{@Setoid A e}.

  Definition mcSetoid_as_Setoid_Theory: Setoid_Theory A e.
   constructor; apply _.
  Qed.

  Definition mcSetoid_as_RSetoid: RSetoid.Setoid
    := @Build_Setoid A e mcSetoid_as_Setoid_Theory.

End make_RSetoid. (* Todo: Move. *)

Instance: ∀ S: RSetoid.Setoid, Equiv S := @st_eq.
Instance: ∀ S: RSetoid.Setoid, Setoid S.

(** MathClasses-style operational & structural classes for a Russell-style metric space (i.e. MetricSpace).
 We don't put this in MathClasses because for reasons of interoperability with the existing MetricSpace
 it is still bound to Qpos rather than an abstract Rationals model. *)

Section MetricSpaceClass.

  Variable X: Type.

  Class MetricSpaceBall: Type := mspc_ball: Qpos → relation X.

  Context `{!Equiv X} `{!MetricSpaceBall}.

  Class MetricSpaceClass: Prop :=
    { mspc_setoid: Setoid X
    ; mspc_ball_proper:> Proper (QposEq ==> (=) ==> (=) ==> iff) (mspc_ball: Qpos → relation X)
    ; mspc_refl:> ∀ e, Reflexive (mspc_ball e)
    ; mspc_sym:> ∀ e, Symmetric (mspc_ball e)
    ; mspc_triangle: ∀ (e1 e2: Qpos) (a b c: X),
         mspc_ball e1 a b → mspc_ball e2 b c → mspc_ball (e1 + e2)%Qpos a c
    ; mspc_closed: ∀ (e: Qpos) (a b: X),
         (∀ d: Qpos, mspc_ball (e + d)%Qpos a b) → mspc_ball e a b
    ; mspc_eq: ∀ a b, (∀ e, mspc_ball e a b) → a = b }.

  Context `{MetricSpaceClass}.

  Let hint := mspc_setoid.

  (** Instances can be bundled to yield MetricSpaces: *)

  Program Definition bundle_MetricSpace: MetricSpace :=
   @Build_MetricSpace (mcSetoid_as_RSetoid X) mspc_ball _ _.

  Next Obligation. apply mspc_ball_proper; assumption. Qed.

  Next Obligation.
   constructor; try apply _.
     apply mspc_triangle.
    apply mspc_closed.
   apply mspc_eq.
  Qed.

  (** .. which obviously have the same carrier: *)

  Goal X ≡ bundle_MetricSpace.
  Proof. reflexivity. Qed.

End MetricSpaceClass.

(** MetricSpaces immediately yield instances of the classes: *)

Instance: ∀ X: MetricSpace, MetricSpaceBall X := @ball.

Instance class_from_MetricSpace (X: MetricSpace): MetricSpaceClass X.
Proof.
 constructor; try apply _.
     apply msp_refl. apply X.
    apply msp_sym. apply X.
   apply msp_triangle. apply X.
  apply msp_closed. apply X.
 apply msp_eq. apply X.
Qed.

Section products.

  Context `{MetricSpaceClass X} `{MetricSpaceClass Y}.

  Global Instance: MetricSpaceBall (X * Y)
    := λ e a b, mspc_ball _ e (fst a) (fst b) ∧ mspc_ball _ e (snd a) (snd b).

  Global Instance: MetricSpaceClass (X * Y).
  Proof class_from_MetricSpace (ProductMS (bundle_MetricSpace X) (bundle_MetricSpace Y)).

End products.

(** I decided to experiment with a class used strictly to declare a metric space's
 components in a section using [Context] without also declaring the metric space structure
 itself, and risking accidental parameterization of the section context on the proof of that
 metric space structure if such parametrization is unneeded (for instance because there is
 already a UniformContinuous constraint which incorporates the metric space proof. *)

Class MetricSpaceComponents X `{Equiv X} `{MetricSpaceBall X}: Prop.

(** Next, we introduce classes for uniform continuity (which is what we're really after, since
 we will use these to automatically derive uniform continuity for various forms of function
 composition).

 For this, we first define mspc_ball_ex, analogous to ball_ex: *)

Definition mspc_ball_ex `{MetricSpaceBall X} (e: QposInf) (a b: X): Prop :=
  match e with
  | QposInfinity => True
  | Qpos2QposInf e' => mspc_ball X e' a b
  end.

Section uniform_continuity.

  Context `{MetricSpaceComponents X} `{MetricSpaceComponents Y}.

  Class UniformlyContinuous_mu (f: X → Y): Type := { uc_mu: Qpos → QposInf }.
    (* Note: If we omit the {} around the uc_mu field and let the class become a definitional class,
     instance resolution will often find the wrong instance because the type of uc_mu is the same for
     different instantiations of X and Y. This solution is not ideal. *)

  Context (f: X → Y) `{!UniformlyContinuous_mu f}.

  Class UniformlyContinuous: Prop :=
    { uc_from: MetricSpaceClass X
    ; uc_to: MetricSpaceClass Y
    ; uniformlyContinuous: 
      ∀ (e: Qpos) (a b: X), mspc_ball_ex (uc_mu e) a b → mspc_ball _ e (f a) (f b) }.

  Context `{uc: UniformlyContinuous}.

  Instance UniformlyContinuousFunction_Proper: Proper (=) f.
    (* Deliberately not Global because uniform continuity is not a "structurally smaller" constraint than propriety. *)
  Proof with auto.
   intros ?? E.
   pose proof uc_to.
   apply (mspc_eq Y).
   intro.
   apply uniformlyContinuous.
   destruct (@uc_mu f UniformlyContinuous_mu0 e).
    simpl.
    pose proof uc_from.
    pose proof (mspc_setoid X).
    pose proof (mspc_ball_proper X).
    rewrite E.
    reflexivity.
   exact I.
  Qed.

  (** If we have a function with this constraint, then we can bundle it into a UniformlyContinuousFunction: *)

  Let hint := uc_from.
  Let hint' := uc_to.

  Program Definition wrap_uc_fun
    : UniformlyContinuousFunction (bundle_MetricSpace X) (bundle_MetricSpace Y)
    := @Build_UniformlyContinuousFunction (bundle_MetricSpace X) (bundle_MetricSpace Y) f uc_mu _.

  Next Obligation.
   repeat intro.
   apply uniformlyContinuous.
   destruct (uc_mu e); auto.
  Qed.

  (** Note that wrap_uc_fun _also_ bundles the source and target metric spaces, because
   UniformlyContinuousFunction is expressed in terms of the bundled data type for metric spaces. *)

End uniform_continuity.

Implicit Arguments uc_mu [[X] [Y] [UniformlyContinuous_mu]].

(** Normally, we would like to use the type class constraints whenever we need uniform continuity of
 functions, including in the types for higher order functions. For instance, we would like to assign
 an integration function for uniformly continuous functions a type along the lines of:
   ∀ (f: Q → CR) `{!UniformlyContinuous f}, CR
 However, dependent types like these get in the way when we subsequently want to express continuity
 of this higher order function itself. Hence, a modicum of bundling is hard to avoid. However, we
 only need to bundle the components of the uniformly continuous function itself---there is no need to
 also start bundling source and target metric spaces the way UniformlyContinuousFunction and
 wrap_uc_fun do. Hence, we now introduce a record for uniformly continuous functions that does not
 needlessly bundle the source and target metric spaces. *)

Section shallowly_wrapped_ucfuns.

  Context `{@MetricSpaceComponents X Xe Xb} `{@MetricSpaceComponents Y Ye Yb}.
    (* We must name Xe/Xb/Ye/Yb here so that we can repeat them in the implicit argument
     specification later on. This could have been avoided if Coq offered more flexible
     commands for implicit argument specification that would let one reset implicit-ness for
     individual parameters without restating the whole list. *)

  Record UCFunction: Type := ucFunction
    { ucFun_itself:> X → Y
    ; ucFun_mu: UniformlyContinuous_mu ucFun_itself
    ; ucFun_uc: UniformlyContinuous ucFun_itself }.

  Global Instance: ∀ (f: UCFunction), Proper (=) (f: X → Y).
  Proof. intros. destruct f. apply (UniformlyContinuousFunction_Proper _). Qed.
    (* This is just the existing unregistered (local) instance for uniformly continuous functions,
     turned into a global instance, which is now justified because (1) the goal for this instance
     includes the coercion, making it far more specialized, and (2) this instance does not yield
     new constraints, and so can never blow up the search space. *)

End shallowly_wrapped_ucfuns.

Existing Instance ucFun_mu.
Existing Instance ucFun_uc.

Implicit Arguments UCFunction [[Xe] [Xb] [Yb] [Ye]].
Implicit Arguments ucFunction [[X] [Xe] [Xb] [Y] [Yb] [Ye] [ucFun_mu] [ucFun_uc]].


Section functions.

  Context `{MetricSpaceClass A} `{MetricSpaceClass B}.

  Global Instance: Equiv (UCFunction A B) := equiv: relation (A→B).

  Let hint := mspc_setoid A.
  Let hint' := mspc_setoid B.

  Global Instance: Setoid (UCFunction A B).
  Proof with intuition.
   constructor.
     intros ????.
     set (_: Proper (=) (ucFun_itself x)).
     destruct x...
    repeat intro. symmetry...
   intros ? y ??? x. transitivity (y x)...
  Qed.

  Global Instance: MetricSpaceBall (UCFunction A B) := λ e f g, ∀ a, mspc_ball B e (f a) (g a).

  Definition UCFunction_MetricSpace: MetricSpaceClass (UCFunction A B).
   destruct (uc_is_MetricSpace (bundle_MetricSpace A) (bundle_MetricSpace B)).
  Admitted. (* Todo. *)

End functions.

Existing Instance UCFunction_MetricSpace.
  (* For some reason Coq hangs when we just declare UCFunction_MetricSpace as an
   instance right away. This workaround seems to work... Todo: Investigate. *)


(** If source and target are /already/ bundled, then we don't need to rebundle them when bundling
 a uniformly continuous function: *)

Program Definition wrap_uc_fun' {X Y: MetricSpace} (f: X → Y)
  `{!UniformlyContinuous_mu f}
  `{@UniformlyContinuous X _ _ Y _ _ f _}:
    UniformlyContinuousFunction X Y :=
  @Build_UniformlyContinuousFunction X Y f (uc_mu f) _.

Next Obligation.
 repeat intro.
 apply (uniformlyContinuous f).
 destruct (uc_mu f e); auto.
Qed.

(** Conversely, if we have a UniformlyContinuousFunction (between bundled metric spaces) and project
 the real function out of it, instances of the classes can easily be derived. *)

Open Scope uc_scope.

Section unwrap_uc.

  Context {X Y: MetricSpace} (f: X --> Y).

  Global Instance unwrap_mu: UniformlyContinuous_mu f := { uc_mu := mu f }.

  Global Instance unwrap_uc_fun: UniformlyContinuous f.
  Proof.
   constructor; try apply _.
   unfold uc_mu, unwrap_mu.
   apply f.
  Qed.

End unwrap_uc.

(** Extentionally equal functions are obviously equally uniformly continuous (with extensionally equal mu's): *)

Lemma UniformlyContinuous_proper `{MetricSpaceClass X} `{MetricSpaceClass Y} (f g: X → Y)
  `{!UniformlyContinuous_mu f} `{!UniformlyContinuous_mu g}:
  (∀ x, f x = g x) → (∀ e, uc_mu f e ≡ uc_mu g e) →
    UniformlyContinuous f → UniformlyContinuous g.
      (* Todo: Stronger versions of this statement can be proved with a little effort. *)
Proof.
 constructor; try apply _.
 intros ????.
 pose proof (mspc_ball_proper Y).
 assert (QposEq e e) by reflexivity.
 apply (H7 e e H8 (f a) (g a) (H3 a) (f b) (g b) (H3 b)).
 apply (uniformlyContinuous f).
 rewrite H4. auto.
Qed. (* Todo: Clean up! (by making [rewrite] work)*)


(** We now show that a couple of basic functions are continuous: *)

(** The identity function is uniformly continuous: *)

Section id_uc. Context `{MetricSpaceClass X}.
  Global Instance: UniformlyContinuous_mu (@Datatypes.id X) := { uc_mu := Qpos2QposInf }.
  Global Instance: UniformlyContinuous (@Datatypes.id X).
  Proof. constructor; try apply _. intros. assumption. Qed.
End id_uc.
  (* Note: We don't need a separate instance for the [id] constant. If such an instance
   is needed, we can use [Hint Unfold id: typeclass_instances.] *)

(** Constant functions are uniformly continuous: *)

Section const_uc. Context `{MetricSpaceClass X} `{MetricSpaceClass Y} (y: Y).
  Global Instance: UniformlyContinuous_mu (@Basics.const Y X y) := { uc_mu := λ _, QposInfinity }.
  Global Instance: UniformlyContinuous (@Basics.const Y X y).
  Proof. repeat intro. constructor; try apply _. intros. apply (mspc_refl Y). Qed.
End const_uc.

(** Mapping both of a pair's components by uniformly continuous functions
 is uniformly continuous: *)

Section map_pair_uc.
  Context `{MetricSpaceComponents X} `{MetricSpaceComponents Y}
    `{MetricSpaceComponents A} `{MetricSpaceComponents B}
    (f: X → Y) `{!UniformlyContinuous_mu f} `{!UniformlyContinuous f}
    (g: A → B) `{!UniformlyContinuous_mu g} `{!UniformlyContinuous g}.

  Global Instance: UniformlyContinuous_mu (map_pair f g) :=
    { uc_mu := λ x, QposInf_min (uc_mu f x) (uc_mu g x) }.

  Let hint := uc_from g.
  Let hint' := uc_to g.
  Let hint'' := uc_from f.
  Let hint''' := uc_to f.

  Global Instance: UniformlyContinuous (map_pair f g).
  Proof.
   constructor; try apply _.
   exact (together_uc (wrap_uc_fun f) (wrap_uc_fun g)).
  Qed.
End map_pair_uc.

(** The diagonal function is uniformly continuous: *)

Section diagonal_uc.
  Context `{MetricSpaceClass X}.

  Global Instance: UniformlyContinuous_mu (@diagonal X) := { uc_mu := Qpos2QposInf }.

  Global Instance: UniformlyContinuous (@diagonal X).
  Proof. constructor; try apply _. split; auto. Qed.
End diagonal_uc.

(** fst/snd/pair are uniformly continuous: *)

Section pairops_uc.
  Context `{MetricSpaceClass A} `{MetricSpaceClass B}.

  Global Instance: UniformlyContinuous_mu (@fst A B) := { uc_mu := Qpos2QposInf }.
  Global Instance: UniformlyContinuous_mu (@snd A B) := { uc_mu := Qpos2QposInf }.
  Global Instance: UniformlyContinuous_mu (uncurry (@pair A B)) := { uc_mu := Qpos2QposInf }.
  Global Instance: ∀ a, UniformlyContinuous_mu (@pair A B a) := { uc_mu := Qpos2QposInf }.

  Global Instance: UniformlyContinuous (@fst A B).
  Proof. constructor; try apply _. intros ??? P. apply P. Qed. 
  Global Instance: UniformlyContinuous (@snd A B).
  Proof. constructor; try apply _. intros ??? P. apply P. Qed. 
  Global Instance: UniformlyContinuous (uncurry (@pair A B)).
  Proof. constructor; try apply _. intros ??? P. apply P. Qed.
  Global Instance: ∀ a, UniformlyContinuous (@pair A B a).
  Proof. constructor; try apply _. intros ??? P. split. reflexivity. apply P. Qed.
End pairops_uc.

Section compose_uc.
  Context `{MetricSpaceComponents X}  `{MetricSpaceComponents Y} `{MetricSpaceComponents Z'}
   (f: Y → Z') `{!UniformlyContinuous_mu f} `{!UniformlyContinuous f}
   (g: X → Y) `{!UniformlyContinuous_mu g} `{!UniformlyContinuous g}.

  Global Instance compose_mu: UniformlyContinuous_mu (f ∘ g)%prg :=
    { uc_mu := λ e, QposInf_bind (uc_mu g) (uc_mu f e) }.

  Let hint := uc_from g.
  Let hint' := uc_to g.
  Let hint'' := uc_to f.

  Global Instance compose_uc: UniformlyContinuous (f ∘ g)%prg.
  Proof with auto.
   constructor; try apply _.
   intros ??? P.
   apply (uniformlyContinuous f).
   revert P. simpl.
   generalize (uc_mu f e).
   destruct q...
   apply (uniformlyContinuous g).
  Qed.
End compose_uc.

Section curried_uc.

  Context `{MetricSpaceClass X} `{MetricSpaceClass Y} `{MetricSpaceClass Z'} (f: X → Y → Z')
   `{fmu1: ∀ x: X, UniformlyContinuous_mu (f x)}
   `{fuc1: ∀ x: X, UniformlyContinuous (f x)}
   `{fmu: !UniformlyContinuous_mu (λ p, f (fst p) (snd p))}
   `{fuc: !UniformlyContinuous (λ p, f (fst p) (snd p))}.

  Local Notation F := (λ x: X, {| ucFun_itself := λ y: Y, f x y; ucFun_mu := fmu1 x; ucFun_uc := fuc1 x |}).

  Global Instance curried_mu: UniformlyContinuous_mu F := { uc_mu := uc_mu (λ p, f (fst p) (snd p)) }.

  Global Instance curried_uc: UniformlyContinuous F.
  Proof with trivial.
   constructor; try apply _.
   repeat intro.
   simpl in *.
   destruct fuc.
   apply (@uniformlyContinuous0 e (a, a0) (b, a0)).
   simpl.
   set (q := uc_mu (λ p, f (fst p) (snd p)) e) in *.
   destruct q...
   split...
   reflexivity.
  Qed.

End curried_uc.


Class HasLambda `{X: Type} (x: X): Prop.

Instance lambda_has_lambda `(f: A → B): HasLambda (λ x, f x).
Instance application_has_lambda_left: ∀ `(f: A → B) (x: A), HasLambda f → HasLambda (f x).
Instance application_has_lambda_right: ∀ `(f: A → B) (x: A), HasLambda x → HasLambda (f x).


Section lambda_uc.

  Context `{MetricSpaceComponents A} `{MetricSpaceComponents B}  (f: A → B).

  Global Instance lambda_mu `{!HasLambda f} {free_f: A → B} `{!PointFree f free_f} `{!UniformlyContinuous_mu free_f}: UniformlyContinuous_mu f.
    (* Note: The HasLambda and PointFree constraints cannot be added to the Context declaration
     above because the definition of this mu needs to depend on them /despite/ not using them.
     Without the dependency, lambda_mu would be allowed to find a random free_f of the right signature
     for which it happens to have a mu already, and use that one.
     We do not factor out the mu constraint either, because for (dubious) efficiency reasons it is critical
     that it appear /after/ the PointFree constraint.*)
  Proof. constructor. apply UniformlyContinuous_mu0. Defined.

  Context `{!HasLambda f} {free_f: A → B} `{!PointFree f free_f} `{!UniformlyContinuous_mu free_f} `{!UniformlyContinuous free_f}.

  Global Instance lambda_uc: UniformlyContinuous f.
  Proof.
   destruct UniformlyContinuous0.
   constructor.
     apply _.
    apply _.
   destruct uc_from0.
   destruct uc_to0.
   intros.
   unfold PointFree in PointFree0.
   rewrite PointFree0.
   apply uniformlyContinuous0.
   unfold uc_mu in H5.
   simpl in H5.
   assumption.
  Qed. (* Todo: Clean up. *)

End lambda_uc.

Module test.
Section test.

  Context
    `{MetricSpaceClass A}
    (f: A → A → A)
    `{!UniformlyContinuous_mu (uncurry f)} `{!UniformlyContinuous (uncurry f)} `{!Proper (=) f}.

  Definition t0: UniformlyContinuous_mu (λ (x: A), f (f x x) (f x (f x x))) := _.

End test.
End test.
