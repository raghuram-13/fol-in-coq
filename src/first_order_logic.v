Set Implicit Arguments. Unset Strict Implicit. Set Maximal Implicit Insertion.

From Coq Require Program.Basics.
Import (notations) Coq.Program.Basics. Open Scope program_scope.
Require Import Util. Import (notations) Util.Heterolist.Notation.

Section ForVariables.
(* The signature of a particular FOL.
  (We are building many-sorted FOL.) *)
Variable (types : Type) (functions : list types -> types -> Type)
                        (predicates : list types -> Type).

Implicit Types (type : types) (context arity : list types).

Section Syntax.

Inductive Term context | type :=
| var' (_ : Occ type context)
| app' {arity} (function : functions arity type) (args : Heterolist Term arity).

Section var. Context {context} (ind : BNat (List.length context)).
Definition varType : types := projT1 (Occ.fromBNat ind).
Definition var : Term context varType := var' (projT2 (Occ.fromBNat ind)).
End var.

Definition app {context type arity}
  : functions arity type
  -> vararg_function (Term context) arity (Term context type) :=
vararg_curry ∘ app'.

Definition ClosedTerm := Term nil.

(* This comes with motive not depending on the `Term` itself because it
   gets into heterogenous lists depending on two parameters (using
   things like homogenize) and that gets overly complicated quickly. *)
Fixpoint Term_rect' {context} {P : types -> Type}
  (var' : forall [type], Occ type context -> P type)
  (app' : forall [type arity]
                (f : functions arity type) (args : Heterolist (Term context) arity),
                Heterolist P arity -> P type)
  {type} (term : Term context type) : P type := match term with
| var' occ    => var' occ
| app' f args => app' f args
                  ((fix ListTerm_rect' {l} args :=
                   match args in Heterolist _ l return Heterolist P l with
                   | []          => []
                   | arg :: rest => Term_rect' var' app' arg :: ListTerm_rect' rest
                   end) _ args)
end.

(* Note: this has unnecessary repetition in that it repeats the
    operations of propositional logic and this might force us to redo
    things we did for propositional logic.
   Possible fix: rewrite propositional_logic to not assume free
    propositional language on a set of variables, and have the free
    case as an instance? *)
Inductive Formula | context :=
| predApp {arity} (predicate : predicates arity)
                  (args : Heterolist (Term context) arity)
| false
| impl : Formula context -> Formula context -> Formula context
| univ {type} : Formula (type :: context) -> Formula context.
#[global] Arguments false {context}.

Definition Sentence := Formula nil.

(* Derived operations. *)
(* Mainly defined to use for the notations. *)
Definition neg {context} (φ : Formula context)
  : Formula context :=
impl φ false.

Definition exist {type context} (φ : Formula (type :: context))
  : Formula context :=
neg (univ (neg φ)).

Section Substitution.

Definition addContext extraContext {context}
  [type] : Term context type -> Term (extraContext ++ context) type :=
Term_rect' (fun _ occ => var' (Occ.addBefore extraContext occ))
           (fun _ _ f _ args' => app' f args').

(* A list of values for the `context'` which must be valid in `context`. *)
Definition Substitutions context context' := Heterolist (Term context') context.

Section TermSubst.
Context {context context'} (values : Substitutions context context').

Definition term_subst [type] : Term context type -> Term context' type :=
(* match term with
| var o      => Array.ref o values
| app' f args => app' f (Array.map term_subst args)
end. *)
Term_rect' (fun _ occ => Heterolist.ref occ values)
           (fun _ _ f _ args' => app' f args').
End TermSubst.

(* This now works pretty much exactly like
   (* _Completeness theorems for first-order logic, analysed in constructive type theory_ *)
   _Formalized First-Order Logic_ by Andreas Halkjær (Section 5.1.2)
   and other sources.
   Recursion except through quantifiers (or anything that changes the
    context) is straightforward, and for moving under a quantifier we
    increment the de Bruijn indexes (achieved by `Heterolist.map (addContext _)`) and
    add an identity substitution at the front (achieved by
    `var' Occ_head ::`). *)
Fixpoint formula_subst {context context'} (values : Substitutions context context')
                       (formula : Formula context) : Formula context' :=
match formula with
| predApp r args => predApp r (Heterolist.map (term_subst values) args)
| false          => false
| impl p q       => impl (formula_subst values p) (formula_subst values q)
| @univ _ type formula   => univ (formula_subst (context := type :: context)
                                     (var' Occ_head ::
                                        Heterolist.map (addContext (type :: nil))
                                          values)
                                     formula)
end.

(* Constructing `Value`s to use in substitutions. *)
Definition value_id {context} : Substitutions context context :=
Heterolist.mapList context (fun _ o => var' o).

(* We perhaps don't need this: it's just heterocons, after all. *)
(* Definition subst_head {type context context'} (values : Substitutions context context')
                      (new_value : Term context' type)
  : Substitutions (type :: context) context' := new_value :: values. *)

End Substitution.

End Syntax.

Section Semantics.

Structure Model := {
  modelType : types -> Type;
  modelFun {type arity}
    : functions arity type
    -> vararg_function modelType arity (modelType type);
  modelPred {arity}
    : predicates arity -> vararg_predicate modelType arity
}.

Section Interpretation.
Set Strict Implicit. Context (m : Model).

Definition value {context} (values : Heterolist m.(modelType) context)
  [type] : Term context type -> m.(modelType) type :=
Term_rect' (fun _ occ => Heterolist.ref occ values)
           (fun _ _ f _ args' => vararg_apply (m.(modelFun) f) args').

(* Can't use context, values section variables because values has to
   vary in the recursive calls. *)
Fixpoint interpret {context} (values : Heterolist m.(modelType) context)
  (formula : Formula context) : Prop := match formula with
| predApp r args       => vararg_apply (m.(modelPred) r)
                            (Heterolist.map (value values) args)
| false                => False
| impl p q             => interpret values p -> interpret values q
| @univ _ type formula => forall x : m.(modelType) type,
                            interpret (x :: values) formula
end.

End Interpretation.
End Semantics.

Section Proofs.

Section defs.

#[local] Notation "'Assumptions'" :=
(forall context, Formula context -> Type)
    (only parsing).

Implicit Types assumptions Γ : Assumptions.

Inductive Proof.

End defs.

End Proofs.

End ForVariables.
#[global] Arguments var' {types functions context type}.
#[global] Arguments var {types functions context}.
#[global] Arguments false {types functions predicates context}.


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
  (* Check fun t φ => ∃.¬(predApp φ [var (* (occ_head t nil) *) BNat_zero]). *)
End FOLFormulaNotations.


(* Test example *)

Section Example.

(* We could let these be automatically inferred (as Prop), but we might
   as well specify Set. *)
Inductive types : Set := | Nat.
Inductive functions : list types -> types -> Set :=
| zero : functions nil  Nat
| succ : functions (Nat::nil) Nat.
Inductive relations : list types -> Set :=
| int_eq : relations (Nat :: Nat :: nil).

Let mysentence := univ (type := Nat)
                    (impl (predApp int_eq [var' Occ_head; app zero : Term functions _ Nat])
                      (impl (predApp int_eq [var' Occ_head; app succ (app zero)])
                        false)) : Sentence functions relations.

Definition standard_model : Model functions relations := {|
  modelType _    := nat (* match x with | Nat => nat end *);
  modelFun _ _ f := match f in functions arity _
                            return vararg_function _ arity nat with
    | zero => 0
    | succ => S
    end;
  modelPred _ r := match r in relations arity return vararg_predicate _ arity with
    | int_eq => @eq nat
    end
|}.

Eval compute in interpret standard_model [] mysentence.

End Example.
