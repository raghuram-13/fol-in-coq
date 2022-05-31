Require Import Coq.Classes.RelationClasses.

Notation "x ∈ S" := ((S : unary_predicate _) x) (at level 70).
Notation "x ∉ S" := (~(S : unary_predicate _) x) (at level 70).

(*
Local Notation "{ x : U ∣ P }" := (fun x : U => P) (x binder, x at level 99) : subset_scope.
Local Notation "{ x | P }"     := (fun x => P)     (x binder, x at level 99) : subset_scope.
*)

Notation "∅"     := (false_predicate : unary_predicate _) : predicate_scope.
Notation "A ∪ B" := (predicate_union (A : unary_predicate _) (B : unary_predicate _))        (at level 65, right associativity) : subset_scope.
Notation "A ∩ B" := (intersection A B) (at level 65, right associativity) : subset_scope.
Notation "A ⊆ B" := (included A B)     (at level 70)                      : subset_scope.



