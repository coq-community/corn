
Require Import
 Unicode.Utf8 Setoid Arith List
 CSetoids Qmetric Qring ProductMetric QposInf
 UniformContinuity
 stdlib_omissions.Pair stdlib_omissions.Q
 interfaces.canonical_names
 interfaces.abstract_algebra
 MathClasses.theory.setoids.

Generalizable All Variables.


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

  (** If we have a function with this constraint, then we can bundle it into a UniformlyContinuousFunction: *)

  Context `{uc: UniformlyContinuous}.

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

  (** Note that wrap_uc_fun _also_ bundles the metric spaces. This is because the bundled data type
   for uniform continuous functions is expressed in terms of the bundled data for metric spaces. *)

End uniform_continuity.

Implicit Arguments uc_mu [[X] [Y] [UniformlyContinuous_mu]].

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
  Global Instance: UniformlyContinuous_mu (λ x: X, x) := { uc_mu := Qpos2QposInf }.
  Global Instance: UniformlyContinuous (λ x: X, x).
  Proof. constructor; try apply _. intros. assumption. Qed.
End id_uc.
  (* Note: We don't need a separate instance for the [id] constant. If such an instance
   is needed, we can use [Hint Unfold id: typeclass_instances.] *)

(** Constant functions are uniformly continuous: *)

Section const_uc. Context `{MetricSpaceClass X} `{MetricSpaceClass Y} (y: Y).
  Global Instance: UniformlyContinuous_mu (λ _: X, y) := { uc_mu := λ _, QposInfinity }.
  Global Instance: UniformlyContinuous (λ _: X, y).
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

  Global Instance: UniformlyContinuous (@fst A B).
  Proof. constructor; try apply _. intros ??? P. apply P. Qed. 
  Global Instance: UniformlyContinuous (@snd A B).
  Proof. constructor; try apply _. intros ??? P. apply P. Qed. 
  Global Instance: UniformlyContinuous (uncurry (@pair A B)).
  Proof. constructor; try apply _. intros ??? P. apply P. Qed.
End pairops_uc.


(** We now move on to compositions of functions, starting with the simplest case: *)

Section uc_comp_uc.

  Context `{MetricSpaceComponents X}  `{MetricSpaceComponents Y} `{MetricSpaceComponents Z'}
   (f: Y → Z') `{!UniformlyContinuous_mu f} `{!UniformlyContinuous f}
   (g: X → Y) `{!UniformlyContinuous_mu g} `{!UniformlyContinuous g}.

  Global Instance uc_comp_mu: UniformlyContinuous_mu (λ x, f (g x)) :=
    { uc_mu := λ e, QposInf_bind (uc_mu g) (uc_mu f e) }.

  Let hint := uc_from g.
  Let hint' := uc_to g.
  Let hint'' := uc_to f.

  Global Instance uc_comp_uc: UniformlyContinuous (λ x, f (g x)).
  Proof with auto.
   constructor; try apply _.
   intros ??? P.
   apply (uniformlyContinuous f).
   revert P. simpl.
   generalize (uc_mu f e).
   destruct q...
   apply (uniformlyContinuous g).
  Qed.

End uc_comp_uc.

(** Now a slightly more interesting case: application of the "binary" function obtained
 by currying a function on products. Note that we need the g and h parameterization
 here because f is not the head function in the lambda. The class instances are
 elegantly obtained simply by observing that [curry f (g x) (h x) ≡ f (map_pair f g (diagonal x))],
 for which the instances can be derived automatically from those we've already defined. *)

Section cur_appl_inst.

  Context
    `{MetricSpaceComponents X} `{MetricSpaceComponents Y}
    `{MetricSpaceComponents A} `{MetricSpaceComponents B}
    (f: A * B → Y) `{!UniformlyContinuous_mu f}
    (g: X → A) `{!UniformlyContinuous_mu g} 
    (h: X → B) `{!UniformlyContinuous_mu h}.

  Global Instance appl_mu: UniformlyContinuous_mu (λ x, curry f (g x) (h x)).
   change (UniformlyContinuous_mu (λ x, f (map_pair g h (diagonal x)))).
   apply _.
  Defined.

  Context `{!UniformlyContinuous f} `{!UniformlyContinuous g} `{!UniformlyContinuous h}.

  Let hint := uc_to g.
  Let hint' := uc_to h.
  Let hint''' := uc_to f.
  Let hint'''' := uc_from g.

  Global Instance uc_appl_inst: UniformlyContinuous (λ x, curry f (g x) (h x)).
  Proof.
   change (UniformlyContinuous (λ x, f (map_pair g h (diagonal x)))).
   apply _.
  Qed.

End cur_appl_inst.


Hint Unfold Datatypes.id: typeclass_instances.

(** A lambda (λ x, f (g x) (h x)) applying a binary function f is uniformly continuous if f is uniformly
 continuous when uncurried and the argument x is piped through uniformly continuous functions g and h: *)

Section binary_uc_function_application.

  Context `{MetricSpaceComponents X} `{MetricSpaceComponents Y} `{MetricSpaceComponents A} `{MetricSpaceComponents B}
    (f: A → B → Y) `{!UniformlyContinuous_mu (uncurry f)} `{!UniformlyContinuous (uncurry f)}
    (g: X → A) `{!UniformlyContinuous_mu g} `{!UniformlyContinuous g}
    (h: X → B) `{!UniformlyContinuous_mu h} `{!UniformlyContinuous h}.

  Global Instance binary_uc_function_application_mu: UniformlyContinuous_mu (λ x, f (g x) (h x)).
   change (UniformlyContinuous_mu (λ x, uncurry f (map_pair g h (diagonal x)))).
   apply _.
  Defined.

  Let hint := uc_to g.
  Let hint' := uc_to h.
  Let hint'' := uc_to (uncurry f).
  Let hint''' := uc_from g.

  Global Instance binary_uc_function_application: UniformlyContinuous (λ x, f (g x) (h x)).
  Proof.
   change (UniformlyContinuous (λ x, uncurry f (map_pair g h (diagonal x)))).
   apply _.
  Qed.

End binary_uc_function_application.

(** This last instance is a bit awkward. Intuitively you'd expect that an instance
 for lambdas of the form (λ x, (f x) (g x)) should suffice. However, higher order unification
 is not clever enough to make the tests work if the above instance is replaced with
 the following two instances: *)

(**
Section application_under_lambda.

  Context `{MetricSpaceComponents X} `{MetricSpaceComponents Y} `{MetricSpaceComponents A}
    (f: X → A → Y) `{!UniformlyContinuous_mu (uncurry f)} `{!UniformlyContinuous (uncurry f)}
    (g: X → A) `{!UniformlyContinuous_mu g} `{!UniformlyContinuous g}.

  Global Instance uc_application_mu: UniformlyContinuous_mu (λ x, (f x) (g x)).
   change (UniformlyContinuous_mu (λ x, uncurry f (map_pair Datatypes.id g (diagonal x)))).
   apply _.
  Defined.

  Let hint := uc_from g.
  Let hint' := uc_to g.
  Let hint'' := uc_to (uncurry f).

  Global Instance uc_application: UniformlyContinuous (λ x, (f x) (g x)).
  Proof.
   change (UniformlyContinuous (λ x, uncurry f (map_pair Datatypes.id g (diagonal x)))).
   apply _.
  Qed.

End application_under_lambda.

Section composition_under_uncurry.

  Context
    `{MetricSpaceComponents X} `{MetricSpaceComponents Y}
    `{MetricSpaceComponents A} `{MetricSpaceComponents B}
    (f: A → B → Y) `{!UniformlyContinuous_mu (uncurry f)}
    (g: X → A) `{!UniformlyContinuous_mu g} .

  Global Instance comp_under_uncurry_mu: UniformlyContinuous_mu (uncurry (fun x => f (g x))).
   change (UniformlyContinuous_mu (λ p, uncurry f (g (fst p), snd p))).
   change (UniformlyContinuous_mu (λ x, uncurry f (map_pair g Datatypes.id x))).
   apply uc_comp_mu.
    apply _.
   apply _.
  Defined.

End composition_under_uncurry.
*)


Module test.
Section test.

  Context
    `{MetricSpaceClass A}
    (f: A → A → A)
    `{!UniformlyContinuous_mu (uncurry f)} `{!UniformlyContinuous (uncurry f)}.

  Definition composition (x: A): A := f (f x x) (f x (f x x)).

  Definition t0: UniformlyContinuous_mu composition := _.

End test.
End test.
