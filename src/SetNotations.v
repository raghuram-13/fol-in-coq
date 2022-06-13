Require Import Coq.Classes.RelationClasses.

(* Subsets *)

Export Coq.Classes.RelationClasses (unary_predicate).

Notation "x ∈ S" := ((S : unary_predicate _) x) (at level 70).
Notation "x ∉ S" := (~(S : unary_predicate _) x) (at level 70).

Declare Scope subset_scope. Bind Scope subset_scope with unary_predicate.
Delimit Scope subset_scope with subset.

(*
Local Notation "{ x : U ∣ P }" := (fun x : U => P)
    (x binder, x at level 99) : subset_scope.
Local Notation "{ x | P }"     := (fun x => P)
    (x binder, x at level 99) : subset_scope.
*)

Notation "∅"     := (false_predicate : unary_predicate _) : subset_scope.
Notation "A ∪ B" :=
  (predicate_union _        (A : unary_predicate _) (B : unary_predicate _))
    (at level 65, right associativity)                    : subset_scope.
Notation "A ∩ B" :=
  (predicate_intersection _ (A : unary_predicate _) (B : unary_predicate _))
    (at level 65, right associativity)                    : subset_scope.
Notation "A ⊆ B" :=
  (predicate_implication    (A : unary_predicate _) (B : unary_predicate _))
    (at level 70)                                         : subset_scope.

Open Scope subset_scope.


(* Type-valued predicates *)

Module MyExtensions. Module Classes. Module RelationClasses.
Section ForVariables.
Context [T : Type] (op : T -> T -> Type).

Fixpoint arrows_all (l : Tlist) : arrows l Type -> Type := match l with
| Tnil      => id (A := Type)
| Tcons _ l => fun R => forall x, arrows_all l (R x)
end.

Fixpoint arrows_some (l : Tlist) : arrows l Type -> Type := match l with
| Tnil      => id (A := Type)
| Tcons _ l => fun R => {x & arrows_some l (R x)}
end.

Fixpoint pointwise_lifting' {l : Tlist} :=
match l as l return arrows l T -> arrows l T -> Type with
| Tnil      => fun R R' : arrows Tnil T => op R R'
| Tcons _ l => fun R R' => forall x, pointwise_lifting' (R x) (R' x)
end.

End ForVariables.
End RelationClasses. End Classes. End MyExtensions.
Import MyExtensions.Classes.RelationClasses.

Notation "A ⊔ B" := (pointwise_extension sum (Tcons _ Tnil) A B)
    (at level 67, left associativity) : function_scope.
Notation "A ⊑ B" :=
  (pointwise_lifting' Coq.Program.Basics.arrow (l := Tcons _ Tnil) A B)
    (at level 70) : function_scope.
