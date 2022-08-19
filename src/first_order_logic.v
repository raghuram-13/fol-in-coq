Set Implicit Arguments. Unset Strict Implicit. Set Maximal Implicit Insertion.

From Coq Require Program.Basics Lists.List.
Import (notations) Coq.Program.Basics. #[local] Open Scope program_scope.
Import (notations) Coq.Lists.List.ListNotations.
Require Import Util. Import (notations) Util.Heterolist.Notation.
#[local] Open Scope heterolist. (* for `match` patterns *)

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
Definition varType : types := List_bnatRef context ind.
Definition var : Term context varType := var' (Occ.fromBNat context ind).
End var.

Definition app {context type arity} : forall function : functions arity type,
  vararg_function (Term context) arity (Term context type) :=
vararg_curry ∘ app'.

Definition ClosedTerm := Term nil.

(* This comes with motive not depending on the `Term` itself because it
   gets into heterogenous lists depending on two parameters (using
   things like homogenize) and that gets overly complicated quickly. *)
Fixpoint Term_rect' {context} {P : types -> Type}
    (var' : forall [type] (occ: Occ type context), P type)
    (app' : forall [type arity] (f : functions arity type)
                                (args : Heterolist (Term context) arity),
                                Heterolist P arity -> P type)
  {type} (term : Term context type) : P type := match term with
| var' occ    => var' occ
| app' f args =>
  app' f args ((fix ListTerm_rect' {l} args :=
               match args in Heterolist _ l return Heterolist P l with
               | []          => []
               | arg :: rest => Term_rect' var' app' arg :: ListTerm_rect' rest
               end) _ args)
end.

(* Consider "doubly heterogenous" lists worth it for inductive proofs. *)
(* We could have gone through this for `rect` too, but chose to not
   define an analogue of `Forall` for types.  (Note that this would have
   to be a separate inductive definition.) *)
Fixpoint Term_ind' {context} {P : forall [type], Term context type -> Prop}
    (var' : forall [type] (occ : Occ type context), P (var' occ))
    (app' : forall [type arity] (f : functions arity type)
                                (args : Heterolist (Term context) arity),
                                Heterolist.Forall P args -> P (app' f args))
  {type} (term : Term context type) : P term := match term with
| var' occ    => var' occ
| app' f args =>
  app' f args ((fix mapForall {l} args :=
               match args return Heterolist.Forall P args with
               | []          => Heterolist.Forall_nil
               | arg :: rest => Heterolist.Forall_cons (Term_ind' var' app' arg)
                                                       (mapForall rest)
               end) _ args)
end.

(* Note: this has unnecessary repetition in that it repeats the
   operations of propositional logic and this might force us to redo
   things we did for propositional logic.
   Possible fix: rewrite propositional_logic to not assume free
   propositional language on a set of variables, and have the free
   case as an instance? *)
Inductive Formula | context :=
| predApp' {arity} (predicate : predicates arity)
                   (args : Heterolist (Term context) arity)
| contradiction
| impl : Formula context -> Formula context -> Formula context
| univ {type} : Formula (type :: context) -> Formula context.
#[global] Arguments contradiction {context}.

Definition predApp {context arity} : forall predicate : predicates arity,
  vararg_function (Term context) arity (Formula context) :=
vararg_curry ∘ predApp'.

Definition Sentence := Formula nil.

(* Derived operations. *)
(* Mainly defined to use for the notations. *)
Definition neg {context} (formula : Formula context)
  : Formula context :=
impl formula contradiction.

Definition exist {type context} (formula : Formula (type :: context))
  : Formula context :=
neg (univ (neg formula)).

Section Substitution.

(* A list of values for the `context'` which must be valid in `context`. *)
Definition Substitutions context context' := Heterolist (Term context') context.

Definition addContext extraContext {context}
  [type] : Term context type -> Term (extraContext ++ context) type :=
Term_rect' (fun _ occ => var' (Occ.addBefore extraContext occ))
           (fun _ _ f _ args' => app' f args').

(* Constructing `Value`s to use in substitutions. *)
Definition value_id {context} : Substitutions context context :=
Heterolist.mapList context (fun _ o => var' o).

(* TODO generalise this to adding multiple types like addContext? *)
(* Transforms a substitution to an equivalent one in a context with one
   more variable of type `type`.
   This is achieved by incrementing the de Bruijn indexes of the terms
   to substitute (achieved by `Heterolist.map (addContext _)`) and
   adding an identity substitution at the front (achieved by
   `var' Occ_head ::`). *)
Definition add1ContextToSubst {type context context'}
  (values : Substitutions context context')
  : Substitutions (type :: context) (type :: context') :=
var' Occ_head :: Heterolist.map (addContext [type]) values.


Section TermSubst.
Context {context context'} (values : Substitutions context context').

Definition term_subst [type] : Term context type -> Term context' type :=
(* match term with
| var o      => Array.ref o values
| app' f args => app' f (Array.map term_subst args)
end. *)
Term_rect' (fun _ occ => Heterolist.ref' occ values)
           (fun _ _ f _ args' => app' f args').
End TermSubst.

(* This now works pretty much exactly like
   (* _Completeness theorems for first-order logic, analysed in constructive type theory_ *)
   _Formalized First-Order Logic_ by Andreas Halkjær (Section 5.1.2)
   and other sources.
   Recursion except through quantifiers (or anything that changes the
   context) is straightforward, and for moving under a quantifier we
   use add1ContextToSubst. *)
Fixpoint formula_subst {context context'}
    (values : Substitutions context context')
    (formula : Formula context) : Formula context' :=
match formula with
| predApp' r args => predApp' r (Heterolist.map (term_subst values) args)
| contradiction   => contradiction
| impl p q        => impl (formula_subst values p) (formula_subst values q)
| univ formula    => univ (formula_subst (add1ContextToSubst values) formula)
end.

End Substitution.

End Syntax.

Section Semantics.

Structure Model := {
  modelType : types -> Type;
  modelFun {type arity}
    : functions arity type -> vararg_function modelType arity (modelType type);
  modelPred {arity}
    : predicates arity -> vararg_predicate modelType arity
}.

Section Interpretation.
Set Strict Implicit. Context (m : Model).

Definition value {context} (values : Heterolist m.(modelType) context)
  [type] : Term context type -> m.(modelType) type :=
Term_rect' (fun _ occ => Heterolist.ref' occ values)
           (fun _ _ f _ args' => vararg_apply (m.(modelFun) f) args').

(* Can't use context, values section variables because values has to
   vary in the recursive calls. *)
Fixpoint interpret {context} (values : Heterolist m.(modelType) context)
  (formula : Formula context) : Prop := match formula with
| predApp' r args      => vararg_apply (m.(modelPred) r)
                            (Heterolist.map (value values) args)
| contradiction        => False
| impl p q             => interpret values p -> interpret values q
| @univ _ type formula => forall x : m.(modelType) type,
                            interpret (x :: values) formula
end.

End Interpretation.
End Semantics.

Section Proofs.

Section defs.

(* #[local] Notation "'Assumptions'" := (forall context, Formula context -> Type)
    (only parsing). *)
(* Note: experimental. *)
(* Level motivations:
   - Standalone notations like [], 'Assumptions' above, etc. are at level 0.
   - Since (Assumptions c) is a term, there's no reason to exclude it from
     being parsed anywhere, so it should have level 0.
   - `context` should at least bind tighter than ⊔, +, * so we can use such
     type operations etc. *)
#[local] Notation "'Assumptions' context" := (Formula context -> Type)
    (at level 0, context at level 30, only parsing).

(* Implicit Types assumptions Γ : Assumptions context. *)

(* We define proofs in a context of free variables, with a set of
   assumptions that is allowed to refer to the variables. So proofs of
   statements with free variables are not to be interpreted as
   implicitly generalised (although if the set of assumptions does not
   refer to that variable, we should be able to generalise them.) *)
Inductive Proof.

End defs.

End Proofs.

End ForVariables.
#[global] Arguments var' {types functions context type}.
#[global] Arguments var {types functions context}.
#[global] Arguments contradiction {types functions predicates context}.
(* TODO reconsider this. functions actually can't be implicitly inferred
   except from the expected type, which may not be very reliable. *)
#[global] Arguments predApp {types functions predicates context arity}.


Module FOLFormulaNotations.
  Declare Scope first_order_formula.
  Bind Scope first_order_formula with Formula.
  Delimit Scope first_order_formula with fol_formula.
  Open Scope first_order_formula.

  Notation "⊥" := contradiction : first_order_formula.
  Infix "'->" := impl (at level 60, right associativity) : first_order_formula.

  Notation "¬ φ" := (neg φ) (at level 35, right associativity)
    : first_order_formula.

  Notation "∀. φ" := (univ φ) (at level 95, right associativity).
  Notation "∃. φ" := (exist φ) (at level 95, right associativity).

  (* Example: given a predicate symbol `formula` with one argument, the
     formula `∃ x, ¬(formula x)`. *)
  Check fun formula => ∃.¬predApp' formula [var' Occ_head].
  (* or more generally, given a formula with one free variable, applying
     it by substitution instead. *)
  Check fun formula => ∃.¬formula_subst [var' Occ_head] formula.
End FOLFormulaNotations.


(* Test example *)

Section Example.

(* We could let these be automatically inferred (as Prop), but we might
   as well specify Set. *)
Inductive types : Set := | _nat | _bool.
Inductive functions : list types -> types -> Set :=
| zero' : functions nil  _nat
| succ' : functions (_nat::nil) _nat
| leq' : functions (_nat::_nat::nil) _bool.
Inductive relations : list types -> Set :=
| eq_n' : relations (_nat :: _nat :: nil)
| eq_b' : relations (_bool :: _bool :: nil).

(* Ugly, but Coq doesn't unfold vararg_* properly otherwise. *)
Let zero {context} := app (context := context) zero'.
Let succ {context} := app (context := context) succ'.
Let leq {context} := app (context := context) leq'.
Let eq_n {context} := predApp (functions := functions) (context := context) eq_n'.
Let eq_b {context} := predApp (functions := functions) (context := context) eq_b'.

Let mysentence := univ
                    (impl (predApp' eq_n' [var' Occ_head; app zero' : Term functions _ _])
                      (impl (predApp' eq_n' [var' Occ_head; app succ' (app zero')])
                        contradiction)) : Sentence functions relations.

(* The `(rest := nil)` specifies that `x` is the outermost variable*)
Let sampleFormula (* {rest} *) :=
let x := var' (Occ_tail (Occ_tail (Occ_head (rest := nil)))) in
let y := var' (Occ_tail Occ_head) in
let b := var' Occ_head in
(impl (eq_b (leq x y) b)
(impl (eq_b (leq y x) b)
  (eq_n x y))).

(* TODO: find and put implementation of actual Nat.leqb here *)
Parameter leqb : nat -> nat -> bool.
Definition standard_model : Model functions relations := {|
  modelType type := match type with | _nat => nat | _bool => bool end;
  modelFun _ _ f := match f in functions arity type
                            return vararg_function _ arity (_ type) with
    | zero' => 0
    | succ' => S
    | leq'  => leqb
    end;
  modelPred _ r := match r in relations arity return vararg_predicate _ arity with
    | eq_n' => @eq nat
    | eq_b' => @eq bool
    end
|}.

Eval compute in interpret standard_model [] mysentence.
Eval compute in interpret standard_model
                          [false : standard_model.(modelType) _bool;
                           0 : standard_model.(modelType) _nat;
                           1 : standard_model.(modelType) _nat] sampleFormula.
Eval compute in interpret standard_model []
            (univ (univ (formula_subst
                            (add1ContextToSubst [succ (var' Occ_head);
                                                 var' Occ_head])
                            sampleFormula))).
Check (let subst_y_with_Sx := [succ (var' Occ_head); var' Occ_head] in
      eq_refl : formula_subst subst_y_with_Sx (univ sampleFormula)
              = univ (formula_subst (add1ContextToSubst subst_y_with_Sx) sampleFormula)).

End Example.
