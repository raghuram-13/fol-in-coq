Require Import Coq.Classes.RelationClasses.

Export Coq.Classes.RelationClasses (unary_predicate).

Notation "x ∈ S" := ((S : unary_predicate _) x) (at level 70).
Notation "x ∉ S" := (~(S : unary_predicate _) x) (at level 70).

(*
Local Notation "{ x : U ∣ P }" := (fun x : U => P) (x binder, x at level 99) : subset_scope.
Local Notation "{ x | P }"     := (fun x => P)     (x binder, x at level 99) : subset_scope.
*)

Declare Scope subset_scope. Bind Scope subset_scope with unary_predicate.
Delimit Scope subset_scope with subset_scope.

Notation "∅"     := (false_predicate : unary_predicate _) : subset_scope.
Notation "A ∪ B" := (predicate_union _ (A : unary_predicate _) (B : unary_predicate _))
                      (at level 65, right associativity)  : subset_scope.
Notation "A ∩ B" := (predicate_intersection _ (A : unary_predicate _) (B : unary_predicate _))
                      (at level 65, right associativity)  : subset_scope.
Notation "A ⊆ B" := (predicate_implication (A : unary_predicate _) (B : unary_predicate _))
                      (at level 70)                       : subset_scope.

Open Scope subset_scope.

(* Some other notations. *)
Notation "A ⊔ B" := (pointwise_extension sum (Tcons _ Tnil) A B) (at level 67, left associativity) : function_scope.
Notation "A ⊆' B" := (pointwise_extension Coq.Program.Basics.arrow (Tcons _ Tnil) A B) (at level 70) : function_scope.
