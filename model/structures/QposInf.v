Require Export Qpossec.
Require Import QposMinMax.

Set Implicit Arguments.

Open Local Scope Q_scope.
Open Local Scope Qpos_scope.

Inductive QposInf : Set :=
| Qpos2QposInf : Qpos -> QposInf
| QposInfinity : QposInf.

Bind Scope QposInf_scope with QposInf.
Delimit Scope QposInf_scope with QposInf.

Coercion Qpos2QposInf : Qpos >-> QposInf.

Definition QposInf_bind (f : Qpos -> QposInf) (x:QposInf) :=
 match x with
 | Qpos2QposInf x' => f x'
 | QposInfinity => QposInfinity
 end.

Lemma QposInf_bind_id : forall x, QposInf_bind (fun e => e) x = x.
intros [x|]; reflexivity.
Qed.

Definition QposInf_plus (x y : QposInf) : QposInf := 
QposInf_bind (fun x' => QposInf_bind (fun y' => x'+y') y) x.

Definition QposInf_mult (x y : QposInf) : QposInf := 
QposInf_bind (fun x' => QposInf_bind (fun y' => x'*y') y) x.

Definition QposInf_le (x y: QposInf) : Prop :=
match y with
| QposInfinity => True
| Qpos2QposInf y' =>
 match x with 
 | QposInfinity => False
 | Qpos2QposInf x' => x' <= y'
 end
end.

Definition QposInf_min (x y : QposInf) : QposInf :=
match x with
| QposInfinity => y
| Qpos2QposInf x' => 
 match y with
 | QposInfinity => x'
 | Qpos2QposInf y' => Qpos2QposInf (Qpos_min x' y')
 end
end.

Lemma QposInf_min_lb_l : forall x y, QposInf_le (QposInf_min x y) x.
Proof.
intros [x|] [y|]; simpl; try auto.
apply Qpos_min_lb_l.
apply Qle_refl.
Qed.

Lemma QposInf_min_lb_r : forall x y, QposInf_le (QposInf_min x y) y.
Proof.
intros [x|] [y|]; simpl; try auto.
apply Qpos_min_lb_r.
apply Qle_refl.
Qed.

Infix "+" := QposInf_plus : QposInf_scope.
Infix "*" := QposInf_mult : QposInf_scope.
