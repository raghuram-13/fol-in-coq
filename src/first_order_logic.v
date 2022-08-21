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

Inductive Term context | : types -> Type :=
| var (ind : ListIndex context) : Term (ListIndex.ref context ind)
| app' {type arity} (function : functions arity type)
                    (args : Heterolist Term arity) : Term type.

Section var'. Context {context type} (occ : Occ type context).
Import (notations) EqNotations.
Definition var' : Term context type :=
rew [Term context] Occ.ref_toIndex occ in var (Occ.toIndex occ).
End var'.

Definition app {context type arity} : forall function : functions arity type,
  vararg_function (Term context) arity (Term context type) :=
vararg_curry ∘ app'.

Definition ClosedTerm := Term nil.

Section Term_rect'. #[local] Unset Implicit Arguments.
(* This comes with motive not depending on the `Term` itself because it
   gets into heterogenous lists depending on two parameters (using
   things like homogenize) and that gets overly complicated quickly. *)
Context {context} {P : types -> Type}
    (var_case : forall (ind : ListIndex context), P (ListIndex.ref context ind))
    (app'_case : forall [type arity] (f : functions arity type)
                                     (args : Heterolist (Term context) arity),
                   Heterolist P arity -> P type).
Arguments app'_case [type arity].

Fixpoint Term_rect' [type] (term : Term context type) := match term with
| var ind     => var_case ind
| app' f args => app'_case f args (Heterolist.map Term_rect' args)
end.
End Term_rect'.

Section Term_ind'. #[local] Unset Implicit Arguments.
(* Consider "doubly heterogenous" lists worth it for inductive proofs. *)
(* We could have gone through this for `rect` too, but chose to not
   define an analogue of `Forall` for types.  (Note that this would have
   to be a separate inductive definition.) *)
Context {context} {P : forall [type], Term context type -> Prop}
    (var_case : forall (ind : ListIndex context), P (var ind))
    (app'_case : forall [type arity] (f : functions arity type)
                                     (args : Heterolist (Term context) arity),
                   Heterolist.Forall P args -> P (app' f args)).
Arguments P [type]. Arguments app'_case [type arity].

Fixpoint Term_ind' [type] (term : Term context type) := match term with
| var ind     => var_case ind
| app' f args => app'_case f args (Heterolist.Forall.of_univ Term_ind' args)
end.

End Term_ind'.

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

Import (notations) EqNotations.
Definition addContext extraContext {context}
  : forall [type], Term context type -> Term (extraContext ++ context) type :=
Term_rect' (P := fun type => Term (extraContext ++ context) type)
           (fun ind => rew ListIndex.ref_addBefore _ _ in
                       var (ListIndex.addBefore extraContext ind))
           (fun _ _ f _ args' => app' f args').

(* Constructing `Value`s to use in substitutions. *)
Definition id_values {context} : Substitutions context context :=
Heterolist.mapList context var.

(* TODO generalise this to adding multiple types like addContext? *)
(* Transforms a substitution to an equivalent one in a context with one
   more variable of type `type`.
   This is achieved by incrementing the de Bruijn indexes of the terms
   to substitute (achieved by `Heterolist.map (addContext [type])`) and
   adding an identity substitution at the front (achieved by
   `var' Occ_head ::`). *)
Definition add1ContextToSubst {type context context'}
  (values : Substitutions context context')
  : Substitutions (type :: context) (type :: context') :=
var ListIndex.head :: Heterolist.map (addContext [type]) values.


Lemma addContext_to_id_subst {type context}
  : add1ContextToSubst id_values = @id_values (type :: context).
unfold add1ContextToSubst, id_values at 2; simpl; f_equal.
apply Heterolist.map_mapList.
Qed.

Section TermSubst.
Context {context context'} (values : Substitutions context context').

Definition term_subst : forall [type], Term context type -> Term context' type :=
(* match term with
| var o      => Array.ref o values
| app' f args => app' f (Array.map term_subst args)
end. *)
Term_rect' (fun ind => Heterolist.ref ind values)
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

Definition evaluate {context} (values : Heterolist m.(modelType) context)
  : forall [type], Term context type -> m.(modelType) type :=
Term_rect' (fun ind => Heterolist.ref ind values)
           (fun _ _ f _ args' => vararg_apply (m.(modelFun) f) args').
(* Evaluate term to a function from variable values to value. *)
Definition evaluate' {context} {type} (term : Term context type) :=
vararg_curry (fun values => evaluate values term).

(* Can't use context, values section variables because values has to
   vary in the recursive calls. *)
Fixpoint interpret {context} (values : Heterolist m.(modelType) context)
  (formula : Formula context) : Prop := match formula with
| predApp' r args      => vararg_apply (m.(modelPred) r)
                            (Heterolist.map (evaluate values) args)
| contradiction        => False
| impl p q             => interpret values p -> interpret values q
| @univ _ type formula => forall x : m.(modelType) type,
                            interpret (x :: values) formula
end.
(* Interpret formula as a predicate on possible variable values. *)
Definition interpret' {context} :=
vararg_curry ∘ Coq.Program.Basics.flip (@interpret context).

Example evaluate_subst {context context'}
                       (subst_values : Substitutions context context')
                       (values : Heterolist m.(modelType) context')
  [type] (term : Term context type)
  : evaluate values (term_subst subst_values term)
    = evaluate (Heterolist.map (evaluate values) subst_values) term.
induction term as [ind|? ? f args h_i] using @Term_ind'.
+ (* unfold term_subst; simpl. unfold evaluate at 2; simpl. *)
  symmetry; apply Heterolist.ref_map_eq_app_ref.
+ unfold term_subst, evaluate at 1 2; repeat simpl;
  fold (term_subst subst_values) (evaluate values)
       (evaluate (Heterolist.map (evaluate values) subst_values)).
  rewrite Heterolist.map_map. f_equal. apply (Heterolist.map_equals h_i).
Qed.

End Interpretation.
End Semantics.

Section Proofs.

Section defs.

(* #[local] Notation "'Assumptions'" := (forall context, Formula context -> Type)
    (only parsing). *)
(* Note: experimental. *)
Notation Assumptions context := (Formula context -> Type) (only parsing).

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
(* #[global] Arguments predApp {types functions predicates context arity}. *)


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
| zero  : functions []           _nat
| succ  : functions [_nat]       _nat
| leq   : functions [_nat; _nat] _bool.
Inductive relations : list types -> Set :=
| eq_n : relations [_nat; _nat]
| eq_b : relations [_bool; _bool].

Notation app := (app (functions := functions)).
Notation predApp := (@predApp _ functions relations).

Check app zero.
Check app leq (* : Term _ _ _nat -> Term _ _ _nat -> Term _ _ _bool *).
Check predApp eq_n (* : ClosedTerm _ _nat -> ClosedTerm _ _nat -> Sentence _ _ *).

Let mysentence := univ (type := _nat)
                    (impl (predApp' eq_n [var' Occ_head; app zero])
                      (impl (predApp' eq_n [var' Occ_head; app succ (app zero)])
                        contradiction)) : Sentence functions relations.
(* Check eq_refl : mysentence
                = univ (impl (predApp eq_n (var' Occ_head) (app zero))
                        (impl (predApp eq_n (var' Occ_head) (app succ (app zero)))
                        contradiction)). *)

Import ListIndex (head, fromTail).
(* The `(rest := nil)` specifies that `x` is the outermost variable*)
Let sampleFormula (* {rest} *) :=
let context := [_bool; _nat; _nat]%list in
let x : Term _ context _nat := var (fromTail (fromTail head)) in
let y : Term _ context _nat := var (fromTail head) in
let b : Term _ context _bool := var head in
(impl (predApp eq_b (app leq x y) b)
(impl (predApp eq_b (app leq y x) b)
  (predApp eq_n x y))).
Print sampleFormula.

(* TODO: find and put implementation of actual Nat.leqb here *)
Fixpoint leqb (m n : nat) : bool := match m, n with
| 0, _ => true | S _, 0 => false | S m, S n => leqb m n
end. Arguments leqb : simpl nomatch.

Definition standard_model : Model functions relations := {|
  modelType type := match type with | _nat => nat | _bool => bool end;
  modelFun _ _ f := match f in functions arity type
                            return vararg_function _ arity (_ type) with
    | zero => 0
    | succ => S
    | leq  => leqb
    end;
  modelPred _ r := match r in relations arity return vararg_predicate _ arity with
    | eq_n => @eq nat
    | eq_b => @eq bool
    end
|}.

Compute interpret standard_model [] mysentence.
Compute interpret standard_model
            [false : standard_model.(modelType) _bool;
             0 : standard_model.(modelType) _nat;
             1 : standard_model.(modelType) _nat]
            sampleFormula.
Eval compute -[leqb] in interpret' standard_model sampleFormula.
Compute interpret standard_model []
            (univ (univ (formula_subst
                            (add1ContextToSubst [app succ (var head);
                                                 var head])
                            sampleFormula))).
Check (let subst_y_with_Sx := [app succ (var head); var head] in
      eq_refl : formula_subst subst_y_with_Sx (univ sampleFormula)
              = univ (formula_subst (add1ContextToSubst subst_y_with_Sx) sampleFormula)).

End Example.
