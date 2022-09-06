Set Implicit Arguments. Unset Strict Implicit. Set Maximal Implicit Insertion.

From Coq Require Program.Basics Lists.List.
Import (notations) Coq.Program.Basics. #[local] Open Scope program_scope.
Import (notations) Coq.Lists.List.ListNotations.
Require Import Util. Import (notations) Util.Heterolist.Notation.
#[local] Open Scope heterolist. (* for `match` patterns *)

(* The signature of a particular FOL.
   (We are building many-sorted FOL.) *)
Module Type Signature.
  Parameter (types : Type) (functions : list types -> types -> Type)
                           (predicates : list types -> Type).
End Signature.

(* Implicit Types (type : types) (context arity : list types). *)

Module Syntax (sig : Signature). Import sig.

Implicit Types (type : types) (context arity : list types).

(* Coq does not generate useful schemes for this nested inductive type.
   We mostly just use fix and match instead. *)
Section TermDef. #[local] Unset Elimination Schemes.
Inductive Term context | : types -> Type :=
| var (ind : ListIndex context) : Term (ListIndex.ref context ind)
| app' {type arity} (function : functions arity type)
                    (args : Heterolist Term arity) : Term type.
End TermDef.

Section var'. Import (notations) EqNotations.
Context {context type} (occ : Occ type context).
Definition var' : Term context type :=
rew [Term context] Occ.ref_toIndex occ in var (Occ.toIndex occ).
End var'.

Definition app {context type arity} : forall function : functions arity type,
  vararg_function (Term context) arity (Term context type) :=
vararg_curry ∘ app'.

Definition ClosedTerm := Term nil.

Section Term_ind. #[local] Unset Implicit Arguments.
(* Consider "doubly heterogenous" lists worth it for inductive *proofs*. *)
(* We could have gone through this for `rect` too, but chose to not
   define an analogue of `Forall` for types.  (Note that this would have
   had to be to be a separate inductive definition.) *)
Context {context} {P : forall [type], Term context type -> Prop}
    (var_case : forall (ind : ListIndex context), P (var ind))
    (app'_case : forall [type arity] (f : functions arity type)
                                     (args : Heterolist (Term context) arity),
                   Heterolist.Forall P args -> P (app' f args)).
Arguments P [type]. Arguments app'_case [type arity].

Fixpoint Term_ind [type] (term : Term context type) := match term with
| var ind     => var_case ind
| app' f args => app'_case f args (Heterolist.Forall.of_univ Term_ind args)
end.

End Term_ind.

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
(* This is necessary because of certain type inference issues:
   the `functions` argument can only be inferred from the `vararg_curry`
   arguments, which could be difficult (although I don't understand
   exactly why this causes a problem).
   In particular, this is not necessary so far for `app`.
   But consider using it anyway. *)
#[global] Arguments predApp _ _ predicate &.

Definition Sentence := Formula nil.

(* Derived operations. *)
(* Mainly defined to use for the notations. *)
Definition neg {context} (formula : Formula context)
  : Formula context :=
impl formula contradiction.

Definition exist {context type} (formula : Formula (type :: context))
  : Formula context :=
neg (univ (neg formula)).

(* Notation *)

Declare Scope first_order_formula.
Bind Scope first_order_formula with Formula.
Delimit Scope first_order_formula with fol_formula.
Open Scope first_order_formula.

Notation "⊥" := contradiction : first_order_formula.
Infix "→" := impl (at level 60, right associativity) : first_order_formula.
Notation "¬ φ" := (neg φ) (at level 35, right associativity)
    : first_order_formula.
Notation "∀'[ type ] ϕ" := (@univ _ type ϕ) (at level 70, right associativity)
    : first_order_formula.
Notation "∀' φ" := (univ φ) (at level 70, right associativity)
    : first_order_formula.
Notation "∃'[ type ] φ" := (@exist _ type φ) (at level 70, right associativity)
    : first_order_formula.
Notation "∃' φ" := (exist φ) (at level 70, right associativity)
    : first_order_formula.

Section Substitution.

(* A list of values for the `context'` which must be valid in `context`. *)
Definition Substitutions context context' := Heterolist (Term context') context.

Section addContext. Import (notations) EqNotations.
Context (extraContext : list types) {context}.
Fixpoint addContext [type] (term : Term context type)
  : Term (extraContext ++ context) type := match term with
| var ind => rew ListIndex.ref_addBefore _ _ in
             var (ListIndex.addBefore extraContext ind)
| app' f args => app' f (Heterolist.map addContext args)
end.
End addContext.

(* Constructing substitutions. *)

(* Identity subsitution.  Does nothing. *)
Definition id_subst {context} : Substitutions context context :=
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
  : add1ContextToSubst id_subst = @id_subst (type :: context).
unfold add1ContextToSubst, id_subst at 2; simpl; f_equal.
apply Heterolist.map_mapList.
Qed.


Section TermSubst.
Context {context context'} (values : Substitutions context context').

Fixpoint term_subst [type] (term : Term context type) : Term context' type :=
match term with
| var ind      => Heterolist.ref ind values
| app' f args => app' f (Heterolist.map term_subst args)
end.

End TermSubst.

(* This now works pretty much exactly like
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

(* Test notation *)

(* Example: given a predicate symbol `formula` with one argument, the
   formula `∃ x, ¬(formula x)`. *)
Check fun formula => ∃' ¬predApp' formula [var ListIndex.head].
(* or more generally, given a formula with one free variable, applying
   it by substitution instead. *)
Check fun formula => ∃' ¬formula_subst [var ListIndex.head] formula.

End Syntax.

Module Model (sig : Signature).
  Module _syntax := Syntax sig. Import sig _syntax.

Structure Model := {
  modelType : types -> Type;
  modelFun {type arity}
    : functions arity type -> vararg_function modelType arity (modelType type);
  modelPred {arity}
    : predicates arity -> vararg_predicate modelType arity
}.

Section Interpretation.
Set Strict Implicit. Context (m : Model).

Section evaluate.
Context {context} (values : Heterolist m.(modelType) context).
Fixpoint evaluate'' [type] (term : Term context type) : m.(modelType) type :=
match term with
| var ind     => Heterolist.ref ind values
| app' f args => vararg_apply (m.(modelFun) f) (Heterolist.map evaluate'' args)
end.
End evaluate.

(* Can't use context, values section variables because values has to
   vary in the recursive calls. *)
Fixpoint interpret'' {context} (values : Heterolist m.(modelType) context)
  (formula : Formula context) : Prop := match formula with
| predApp' r args      => vararg_apply (m.(modelPred) r)
                            (Heterolist.map (evaluate'' values) args)
| contradiction        => False
| impl p q             => interpret'' values p -> interpret'' values q
| @univ _ type formula => forall x : m.(modelType) type,
                            interpret'' (x :: values) formula
end.

Section Variations. Context {context : list types} {type : types}.

Definition evaluate (term : Term context type) values := evaluate'' values term.
(* Evaluate term to a function from variable values to value. *)
Definition evaluate' := vararg_curry ∘ evaluate.

Definition interpret := Coq.Program.Basics.flip (@interpret'' context).
(* Interpret formula as a predicate on possible variable values. *)
Definition interpret' := vararg_curry ∘ interpret.

End Variations.

Example evaluate_subst {context context'}
                       (subst_values : Substitutions context context')
                       (values : Heterolist m.(modelType) context')
  [type] (term : Term context type)
  : evaluate'' values (term_subst subst_values term)
    = evaluate'' (Heterolist.map (evaluate'' values) subst_values) term.
induction term as [ind|? ? f args h_i].
+ (* unfold term_subst; simpl. unfold evaluate at 2; simpl. *)
  symmetry; apply Heterolist.ref_map_eq_app_ref.
+ unfold term_subst, evaluate'' at 1 2; repeat simpl;
  fold (term_subst subst_values) (evaluate'' values)
       (evaluate'' (Heterolist.map (evaluate'' values) subst_values)).
  rewrite Heterolist.map_map. f_equal. apply (Heterolist.map_equals h_i).
Qed.

End Interpretation.

End Model.

Module ProofSystem (sig : Signature).
Module _syntax := Syntax sig. Import sig _syntax.

Section defs.

(* Note: experimental. *)
Notation Assumptions context := (list (Formula context)) (only parsing).
Notation "↑[ type ] assumptions" :=
  (List.map (formula_subst (Heterolist.map (addContext [type]) id_subst))
     assumptions)
  (at level 8, right associativity).
Notation "↑ assumptions" := (↑[_] assumptions)
  (at level 8, right associativity).

(* We define proofs in a context of free variables, with a set of
   assumptions that is allowed to refer to the variables. So proofs of
   statements with free variables are not to be interpreted as
   implicitly generalised (although if the set of assumptions does not
   refer to that variable, we should be able to generalise them.) *)
(* The approach to universal quantifier elimination here is also found in
   _A Constructive Analysis of First-Order Completeness Theorems in Coq_
   by Dominik Wehr et al. in section 2.4. *)
Inductive Proof | {context} (assumptions : Assumptions context)
  : Formula context -> Type :=
(* Propositional logic *)
| by_assumption {p} : Occ p assumptions -> Proof _ p
| rule_1 p q : Proof _ (p → q → p)
| rule_2 p q r : Proof _ ((p → q → r) → (p → q) → p → r)
| by_contradiction p : Proof _ (¬¬p → p)
| modus_ponens hyp concl : Proof _ (hyp → concl) -> Proof _ hyp -> Proof _ concl
(* univ *)
| univ_intro {type p} : Proof ↑[type]assumptions p
                        -> Proof assumptions (∀'[type] p)
| univ_elim {type} (term : Term context type) formula
  : Proof _ (univ (type := type) formula)
    -> Proof _ (formula_subst (term :: id_subst) formula).

End defs.

End ProofSystem.

Declare Module sig : Signature.
Module syntax := Syntax sig.


(* Test example *)

Module ExampleSignature <: Signature.

  (* Because the module system is a pain, we have to define the exported
     names as definitions and not inductives. *)
  (* We could let these be automatically inferred (as Prop), but we might
     as well specify Set. *)
  Inductive types' : Set := nat' | bool'. Definition types := types'.
  Inductive functions' : list types -> types -> Set :=
  | zero  : functions' []           nat'
  | succ  : functions' [nat']       nat'
  | leq   : functions' [nat'; nat'] bool'. Definition functions := functions'.
  Inductive relations : list types -> Set :=
  | eq_n : relations [nat'; nat']
  | eq_b : relations [bool'; bool']. Definition predicates := relations.

End ExampleSignature.

Module _syntax := Syntax ExampleSignature. Import ExampleSignature _syntax.

Check app zero.
Check app leq.
Check predApp eq_n.

Let mysentence := univ (type := nat')
                    (impl (predApp' eq_n [var' Occ_head; app zero])
                      (impl (predApp' eq_n [var' Occ_head; app succ (app zero)])
                        contradiction)) : Sentence.

Import ListIndex (head, fromTail).

Succeed Check eq_refl :
mysentence = ∀' predApp eq_n (var head) (app zero)
                → ¬predApp eq_n (var head) (app succ (app zero)).

(* The expression could be in any context starting with
   `[bool'; nat'; nat'; ...]`. We need to specify the type only so that
   Coq knows the context to use (and even there, only the length of the
   context is needed).
   Alternatively, it's enough to specify it in the types of any one of
   `x`, `y`, `b` OR fix the implicit argument anywhere; or
   `sampleFormula` can be parametrised on a `rest` argument. *)
Let sampleFormula : Formula [_; _; _]%list :=
let x := var (fromTail (fromTail head)) in
let y := var (fromTail head) in
let b := var head in
(predApp eq_b (app leq x y) b) → (predApp eq_b (app leq y x) b)
                               → (predApp eq_n x y).

(* TODO: find and put implementation of actual Nat.leqb here *)
Fixpoint leqb (m n : nat) : bool := match m, n with
| 0, _ => true | S _, 0 => false | S m, S n => leqb m n
end. Arguments leqb : simpl nomatch.

Module ModelofExample := Model ExampleSignature.
Import ModelofExample (Model, modelType, modelFun, modelPred,
    evaluate'', interpret'', evaluate, interpret, evaluate', interpret').
Definition standard_model : Model := {|
  modelType type := match type with | nat' => nat | bool' => bool end;
  modelFun _ _ f := match f in functions' arity type
                            return vararg_function _ arity (_ type) with
    | zero => 0
    | succ => S
    | leq  => leqb
    end;
  modelPred _ r := match r in relations arity
                           return vararg_predicate _ arity with
    | eq_n => @eq nat
    | eq_b => @eq bool
    end
|}.


(* Note: some of these return huge answers without using the `vm_compute`
   reduction strategy or the equivalent `Compute` command, and I don't
   know why. *)

Compute interpret'' standard_model [] mysentence.

(* Hint Extern 1 => (match goal with
  | |- _ = modelType types _ _ _ ?t => destruct t
end) : core. *)
(* The essential problem here is that Coq cannot solve
   `bool = standard_model.(modelType) ?a` backwards (there's no
   mechanism I know of to hint to it to destruct `?a : types`),
   and it tries to type-check it before looking at the next argument,
   `sampleFormula`, which would give it the answer too.
   Notice how just supplying the `?a :types` is enough, it knows the
   rest. *)
Compute interpret'' standard_model [false : _ bool'; 0 : _ nat'; 1 : _ nat']
                                   sampleFormula.
(* Simply interchanging the arguments can solve this problem. *)
Compute interpret standard_model sampleFormula [false; 0; 1].
(* Curried version of the same as the last two checks. *)
Eval compute -[leqb] in interpret' standard_model sampleFormula.

Compute interpret standard_model
            (∀' ∀' (formula_subst (add1ContextToSubst [app succ (var head);
                                                       var head])
                                  sampleFormula)) [].

Succeed Check let subst_y_with_Sx := [app succ (var head); var head] in eq_refl:
formula_subst subst_y_with_Sx (∀' sampleFormula)
=  ∀' formula_subst (add1ContextToSubst subst_y_with_Sx)
                    sampleFormula.

End Example.
