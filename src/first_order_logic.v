Set Implicit Arguments. Unset Strict Implicit. Set Maximal Implicit Insertion.

From Coq Require Lists.List.
Require Import Util. Import (notations) Util.HeterolistNotations.

Section Syntax.

(* The signature of a particular FOL. *)

(* We are building many-sorted FOL. This hopefully shouldn't add much
   complexity to the proofs of the fundamental theorems. *)
Variable types : Type.
Variable functions : list types -> types -> Type.
Variable predicates : list types -> Type.

Inductive Term (type_context : list types) | (type : types) :=
| var (_ : occ type type_context)
| app {arg_types} (function : functions arg_types type)
                  (args : heterolist Term arg_types).

Definition ClosedTerm := Term nil.

(* Note: this has unnecessary repetition in that it repeats the
    operations of propositional logic and this might force us to redo
    things we did for propositional logic.
   Possible fix: rewrite propositional_logic to not assume free
    propositional language on a set of variables, and have the free
    case as an instance? *)
Inductive Formula | (type_context : list types) :=
| predApp {arg_types} (predicate : predicates arg_types)
                      (args : heterolist (Term type_context) arg_types)
| false
| impl : Formula type_context -> Formula type_context -> Formula type_context
| univ {type} : Formula (type :: type_context) -> Formula type_context.
#[global] Arguments false {type_context}.

Definition Sentence := Formula nil.

(* Derived operations. *)
(* Mainly defined to use for the notations. *)
Definition neg {type_context} (φ : Formula type_context)
  : Formula type_context :=
impl φ false.

Definition exist {type_context type} (φ : Formula (type::type_context))
  : Formula type_context :=
neg (univ (neg φ)).

Section Substitution.
Context {type_context : list types} {type : types}
        (variable : occ type type_context) (value : Term type_context type).

Fixpoint term_subst [type'] (term : Term type_context type')
  : Term (remove_occ variable) type' := match term with
| var o      => _
| app f args => app f (heteromap term_subst args)
end.

End Syntax.
#[global] Arguments var {types functions type_context type}.
#[global] Arguments false {types functions predicates type_context}.

Module FOLFormulaNotations.
  Declare Scope first_order_formula.
  Bind Scope first_order_formula with Formula.
  Delimit Scope first_order_formula with fol_formula.
  Open Scope first_order_formula.

  Notation "⊥" := false : first_order_formula.
  Infix "'->" := impl (at level 60, right associativity) : first_order_formula.

  Notation "¬ φ" := (neg φ) (at level 35, right associativity) : first_order_formula.

  Notation "∀. φ" := (univ φ) (at level 95, right associativity).
  Notation "∃. φ" := (exist φ) (at level 95, right associativity).

  (* Example: given a predicate symbol φ with one argument of type t,
     the formula `∃ x, ¬(φ x)`. *)
  (* Check fun t φ => ∃.¬(predApp φ [var (occ_head t nil)]). *)
End FOLFormulaNotations.


Section Semantics.
Variables (types : Type) (functions : list types -> types -> Type)
                         (predicates : list types -> Type).

Structure Model := {
  modelType : types -> Type;
  modelFun {arg_types : list types} {res_type : types}
    : functions arg_types res_type
      -> vararg_function modelType arg_types (modelType res_type);
  modelPred {arg_types : list types}
    : predicates arg_types -> vararg_predicate modelType arg_types
}.

Section Interpretation.
Set Strict Implicit. Context (m : Model).

Section value.
Context [type_context] (context : heterolist m.(modelType) type_context).
Fixpoint value [type] (term : Term functions type_context type)
  : m.(modelType) type := match term with
| var occ    => ref_by_occ occ context
| app f args =>
  vararg_apply (m.(modelFun) f)
    (* This runs into the problem that `value` is passed
       to `heteromap` unapplied to two arguments, rather
       than just the decreasing argument `term`.

       Ideally we want the Fixpoint declaration to be
       interpreted as
       "term decreases and type changes arbitrarily", but
       it seems it is perhaps interpreted as
       "term decreases and type remains the same"
       instead. `type` is literally just an index for the
       type of term; this shouldn't be a problem at all. *)
    (* (heteromap value args) *)
    ((fix map_value [is] (l : heterolist (Term functions type_context) is)
      : heterolist m.(modelType) is := match l with
    | []           => []
    | term :: rest => value term :: map_value rest
    end) _ args)
end.
End value.

(* Can't use type_context, context section variables because context has to
   vary in the recursive calls. *)
Fixpoint interpret
    [type_context] (context : heterolist m.(modelType) type_context)
  (φ : Formula functions predicates type_context) : Prop := match φ with
| predApp r args       => vararg_apply (m.(modelPred) r)
                            (heteromap (value context) args)
| false                => False
| impl p q             => interpret context p -> interpret context q
| @univ _ _ _ _ type φ =>
  forall x : m.(modelType) type, interpret (x :: context) φ
end.

End Interpretation.
End Semantics.

Section Proofs.
Context {types : Type} {functions : list types -> types -> Type}
                       {predicates : list types -> Type}.

Section defs.

#[local] Notation "'Assumptions'" :=
(forall type_context, Formula functions predicates type_context -> Type)
    (only parsing).

Implicit Types assumptions Γ : Assumptions.

Inductive Proof .

End defs.

End Proofs.

(* Test example *)

Section Example.

(* We could let these be automatically inferred (as Prop), but we might
   as well specify Set. *)
Inductive types : Set := | Nat. Check types.
Inductive functions : list types -> types -> Set :=
| zero : functions nil  Nat
| succ : functions (Nat::nil) Nat.
Inductive relations : list types -> Set :=
| int_eq : relations (Nat :: Nat :: nil).

Let mysentence := univ (type := Nat)
                    (impl (predApp int_eq [var (occ_head _ _); app zero []])
                      (impl (predApp int_eq [var (occ_head _ _); app succ [app zero []]])
                        false)) : Sentence functions relations.

Definition standard_model : Model functions relations := {|
  modelType x    := nat (* match x with | Nat => nat end *);
  modelFun _ _ f := match f in functions l _ return vararg_function _ l nat with
    | zero => 0
    | succ => S
    end;
  modelPred _ r := match r in relations l return vararg_function _ l Prop with
    | int_eq => @eq nat
    end
|}.

Eval compute in interpret standard_model [] mysentence.

End Example.
