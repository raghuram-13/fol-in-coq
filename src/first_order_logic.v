Set Implicit Arguments. Unset Strict Implicit. Set Maximal Implicit Insertion.

From Coq Require Lists.List.
Require Import Util. Import (notations) Util.Array.Notation.

Section Syntax.

(* The signature of a particular FOL. *)

(* We are building single-sorted FOL. *)
Variable functions : nat -> Type.
Variable predicates : nat -> Type.

Inductive Term (context : nat) :=
| var (_ : BNat context)
| app {arity} (function : functions arity) (args : Array (Term context) arity).

Definition ClosedTerm := Term 0.

(* This comes with no motives because I've abandoned heterogenous lists and arrays. *)
Definition Term_rect' {context} {P : Type}
  (var : BNat context -> P)
  (app : forall {arity}, functions arity -> Array (Term context) arity -> Array P arity -> P)
  : Term context -> P :=
fix Term_rect' (term : Term context) := match term with
| var a => var a
| app f args => app f args
                  ((fix ArrayTerm_rect' {n} args := match args with
                   | []          => []
                   | arg :: rest => Term_rect' arg :: ArrayTerm_rect' rest
                   end) _ args)
end.

(* Note: this has unnecessary repetition in that it repeats the
    operations of propositional logic and this might force us to redo
    things we did for propositional logic.
   Possible fix: rewrite propositional_logic to not assume free
    propositional language on a set of variables, and have the free
    case as an instance? *)
Inductive Formula | (context : nat) :=
| predApp {arity} (predicate : predicates arity)
                  (args : Array (Term context) arity)
| false
| impl : Formula context -> Formula context -> Formula context
| univ : Formula (S context) -> Formula context.
#[global] Arguments false {context}.

Definition Sentence := Formula 0.

(* Derived operations. *)
(* Mainly defined to use for the notations. *)
Definition neg {context} (φ : Formula context)
  : Formula context :=
impl φ false.

Definition exist {context} (φ : Formula (S context))
  : Formula context :=
neg (univ (neg φ)).

Section Substitution.

Fixpoint addContext extraContext {context} (term : Term context) {struct term}
  : Term (extraContext + context) := match term with
| var o      => var (BNat.toSum_a extraContext o)
| app f args => app f (* Array.map (addContext extraContext) args *)
                      ((fix Array_map {n} (args : Array (Term context) n) := match args with
                       | []          => []
                       | arg :: rest => addContext extraContext arg :: Array_map rest
                       end) _ args)
end.

Section TermSubst.
Context {context context' : nat} (values : Array (Term context) context').

Definition term_subst : Term context' -> Term context :=
(* match term with
| var o      => Array.ref o values
| app f args => app f (Array.map term_subst args)
end. *)
Term_rect' (fun a : BNat context' => Array.ref a values)
           (fun _ f _ args' => app f args').
End TermSubst.

(* This now works pretty much exactly like
   _Completeness theorems for first-order logic, analysed in constructive type theory_
   and other sources.
   Recursion except through quantifiers (or anything that changes the
    context) is straightforward, and for moving under a quantifier we
    increment the de Bruijn indexes (achieved by `Array.map (addContext 1)`) and
    add an identity substitution at the front (achieved by
    `var BNat_zero ::`). *)
Fixpoint formula_subst {context context' : nat} (values : Array (Term context) context')
                       (formula : Formula context') : Formula context :=
match formula with
| predApp r args => predApp r (Array.map (term_subst values) args)
| false          => false
| impl p q       => impl (formula_subst values p) (formula_subst values q)
| univ formula   => univ (formula_subst (context := S context)
                                          (var BNat_zero :: Array.map (addContext 1)
                                                                      values)
                                        formula)
end.

End Substitution.

End Syntax.
#[global] Arguments var {functions context}.
#[global] Arguments false {functions predicates context}.

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


Section Semantics.
Variables (functions : nat -> Type) (predicates : nat -> Type).

Structure Model := {
  modelType : Type;
  modelFun {arity : nat}
    : functions arity -> vararg_function arity modelType modelType;
  modelPred {arity : nat}
    : predicates arity -> vararg_predicate arity modelType
}.

Section Interpretation.
Set Strict Implicit. Context (m : Model).

Section value.
Context [context] (values : Array m.(modelType) context).
Fixpoint value (term : Term functions context)
  : m.(modelType) := match term with
| var occ    => Array.ref occ values
| app f args =>
  vararg_apply (m.(modelFun) f)
    (* (Array.map value args) *)
    ((fix map_value [is] (l : Array (Term functions context) is)
      : Array m.(modelType) is := match l with
    | []           => []
    | term :: rest => value term :: map_value rest
    end) _ args)
end.
End value.

(* Can't use context, values section variables because values has to
   vary in the recursive calls. *)
Fixpoint interpret
    [context] (values : Array m.(modelType) context)
  (formula : Formula functions predicates context) : Prop := match formula with
| predApp r args       => vararg_apply (m.(modelPred) r)
                            (Array.map (value values) args)
| false                => False
| impl p q             => interpret values p -> interpret values q
| univ formula => forall x : m.(modelType), interpret (x :: values) formula
end.

End Interpretation.
End Semantics.

Section Proofs.
Context {types : Type} {functions : nat -> Type} {predicates : nat -> Type}.

Section defs.

#[local] Notation "'Assumptions'" :=
(forall context, Formula functions predicates context -> Type)
    (only parsing).

Implicit Types assumptions Γ : Assumptions.

Inductive Proof.

End defs.

End Proofs.

(* Test example *)

Section Example.

(* We could let these be automatically inferred (as Prop), but we might
   as well specify Set. *)
(* Inductive types : Set := | Nat. Check types. *)
Inductive functions : (* list types -> types *) nat -> Set :=
| zero : functions (* nil  Nat *) 0
| succ : functions (* (Nat::nil) Nat *) 1.
Inductive relations : (* list types *) nat -> Set :=
| int_eq : relations (* (Nat :: Nat :: nil) *) 2.

Let mysentence := univ (* (type := Nat) *)
                    (impl (predApp int_eq [var (* (occ_head _ _) *) BNat_zero; app zero []])
                      (impl (predApp int_eq [var (* (occ_head _ _) *) BNat_zero; app succ [app zero []]])
                        false)) : Sentence functions relations.

Definition standard_model : Model functions relations := {|
  modelType (* x *)    := nat (* match x with | Nat => nat end *);
  modelFun _ (* _ *) f := match f in functions l (* _ *)
                            return vararg_function (* _ *) l nat nat with
    | zero => 0
    | succ => S
    end;
  modelPred _ r := match r in relations l return vararg_predicate l nat with
    | int_eq => @eq nat
    end
|}.

Eval compute in interpret standard_model [] mysentence.

End Example.
