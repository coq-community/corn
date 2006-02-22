Require Export FieldReflection.
Require Export RingReflection.
Require Export GroupReflection.

Inductive AlgebraName : Type :=
|cfield : CField -> AlgebraName
|cring : CRing -> AlgebraName
|cabgroup : CAbGroup -> AlgebraName.

Ltac GetStructureName t :=
match t with 
| (csg_crr (cm_crr (cg_crr (cag_crr ?s)))) =>
 match s with
 | (cr_crr ?r) =>
  match r with
  | (cf_crr ?q) => constr:(cfield q)
  | _ => constr:(cring r)
  end
 | _ => constr:(cabgroup s)
 end
end.

Ltac rational := 
match goal with
[|-@cs_eq ?T ?x ?y] => 
 match GetStructureName T with 
 |(cfield ?F) => rationalF F x y
 |(cring ?R) => rationalR R x y
 |(cabgroup ?G) => rationalG G x y
 end
end.

Tactic Notation "rstepl" constr(c) :=  stepl c;[idtac | rational].

Tactic Notation "rstepr" constr(c) :=  stepr c;[idtac | rational].
