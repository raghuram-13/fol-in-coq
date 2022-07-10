Set Implicit Arguments. Unset Strict Implicit. Set Maximal Implicit Insertion.
From Coq Require Lists.List.

Section Util.

Definition dep_uncurry {A : Type} {motive : A -> Type}
                       {motive' : forall a, motive a -> Type}
    (f : forall a (b : motive a), motive' a b)
  : let motive' : sigT motive -> Type :=
      fun '(existT _ a b : sigT motive) => motive' a b in
    forall x : sigT motive, motive' x :=
fun '(existT _ a b) => f a b.

Definition dep_curry {A : Type} {motive : A -> Type}
                     {motive' : sigT motive -> Type}
    (f : forall x : sigT motive, motive' x)
  a (b : motive a) : motive' (existT _ a b) := f (existT _ a b).

Section occurrence.
Import (notations) List.ListNotations. Open Scope list.

Inductive occ {A : Type} | (a : A) : list A -> Type :=
| head rest : occ a (a :: rest)
| tail rest b : occ a rest -> occ a (b :: rest).
#[global] Arguments tail {_ _ _} [b].

Definition no_occ_nil {A : Type} (a : A) (h : occ a []) : False :=
(* `in` enables match to eliminate constructors whose type doesn't match
   the index. I think. *)
match h in occ _ [] with end.

End occurrence.

Section heterolist.

Variables (Ind : Type) (motive : Ind -> Type).

(* This caused a universe inconsistency error in the definition of Term (after
   enabling universe polymorphism).
   Using an indexed family was recommended at
   https://coq.discourse.group/t/constructing-heterogeneous-lists/1467/4
   and fixed the error. *)
(* Inductive heterolist@{u} : list Type@{u} -> Type :=
| heteronil : heterolist nil
| heterocons {T : Type@{u}} {Ts} : T -> heterolist Ts -> heterolist (T :: Ts). *)
Inductive heterolist : list Ind -> Type :=
| heteronil : heterolist nil
| heterocons {i is} : motive i -> heterolist is -> heterolist (i :: is).

(* Fixpoint ref_by_occ {i is} (h : occ i is) (l : heterolist is) :=
match h in occ _ is, l in heterolist is return motive i with
| head _ _, @heterocons _ _ x _  => _
| tail h  , @heterocons _ _ _ xs => _
| head _ _, heteronil | tail _, heteronil => ID
end. *)

(* It is easier to do this than to write these matches inline due to
   the spurious new copies of bindings for i and is Coq introduces and
   then complains about. *)
Definition heterofirst {i is} : heterolist (i::is) -> motive i :=
fun '(heterocons x _) => x.
Definition heterorest {i is} : heterolist (i::is) -> heterolist is :=
fun '(heterocons _ rest) => rest.

Fixpoint ref_by_occ {i is} (h : occ i is) : heterolist is -> motive i :=
match h with
| head _ _ => heterofirst
| tail h   => fun l => ref_by_occ h (heterorest l)
end.

Fixpoint homogenize {is} (l : heterolist is)
  : list (sigT motive) := match l with
| heteronil       => nil
| heterocons x xs => cons (existT _ _ x) (homogenize xs)
end.

Section vararg.

Fixpoint vararg_function (arg_types : list Ind) (B : Type) : Type :=
match arg_types with
| nil         => B
| cons i rest => motive i -> vararg_function rest B
end.

Definition vararg_predicate (arg_types : list Ind) :=
vararg_function arg_types Prop.

Fixpoint vararg_apply {arg_types : list Ind} {B : Type}
                      (f : vararg_function arg_types B)
                      (args : heterolist arg_types) : B :=
(* We need f effectively unapplied so its type changes with `args`. *)
(match args in heterolist arg_types return vararg_function arg_types B -> B with
| heteronil           => id
| heterocons arg rest => fun f => vararg_apply (f arg) rest
end) f.

End vararg.

Fixpoint map_hetero (f : forall i, motive i) is : heterolist is := match is with
| nil       => heteronil
| cons i is => heterocons (f i) (map_hetero f is)
end.

End heterolist.
#[global] Arguments heteronil {_ motive}.

Fixpoint heteromap {Ind : Type} {motive1 motive2 : Ind -> Type}
                   (f : forall [i : Ind], motive1 i -> motive2 i)
  {is : list Ind} (l : heterolist motive1 is) : heterolist motive2 is :=
match l with
| heteronil         => heteronil
| heterocons a rest => heterocons (f a) (heteromap f rest)
end.

End Util.
(* Has to be done outside any sections *)
Declare Scope heterolist.
Bind Scope heterolist with heterolist. Delimit Scope heterolist with heterolist.
#[local] Open Scope heterolist.
Notation "[ ]" := heteronil : heterolist.
Infix "::" := heterocons : heterolist.
Notation "[ x ; .. ; y ]" := (x :: .. (y :: heteronil)..) : heterolist.


Section Main.

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
#[global] Arguments var {type_context type}.
#[global] Arguments app {type_context type arg_types}.

Definition ClosedTerm := Term nil.

(* This definition would account for everything except quantification. *)
(* Require propositional_logic.
Definition Formula (context : list types) :=
propositional_logic.Proposition {arg_types & predicates arg_types
                                           & heterolist (Term context) arg_types}. *)

(* Note: this has unnecessary repetition in that it repeats the
    operations of propositional logic and this might force us to redo
    things we did for propositional logic.
   Possible fix: rewrite propositional_logic to not assume free
    propositional language on a set of variables, and have the free
    case as an instance? *)
Inductive Formula | (context : list types) :=
| predApp {arg_types} (predicate : predicates arg_types)
                      (args : heterolist (Term context) arg_types)
| false | impl : Formula context -> Formula context -> Formula context
| univ {type : types} : Formula (type :: context) -> Formula context.
#[global] Arguments false {context}.

Declare Scope first_order_formula.
Bind Scope first_order_formula with Formula.
Delimit Scope first_order_formula with fol_formula.

#[local] Notation "⊥" := false : first_order_formula.
#[local] Infix "'->" := impl (at level 60, right associativity) : first_order_formula.

Definition neg {context} (φ : Formula context) : Formula context :=
impl φ false.
#[local] Notation "¬ φ" := (neg φ) (at level 35, right associativity) : first_order_formula.

Definition exist {context type} (φ : Formula (type::context)) : Formula context :=
neg (univ (neg φ)).
#[local] Notation "∀. φ" := (univ φ) (at level 95, right associativity).
#[local] Notation "∃. φ" := (exist φ) (at level 95, right associativity).

(* Example: given a predicate symbol φ with one argument of type t,
   the formula `∃ x, ¬(φ x)`. *)
(* Check fun t φ => ∃.¬(predApp φ [var (head t nil)]). *)

Definition Sentence := Formula nil.



(* Semantics *)
Structure Model := {
  modelType : types -> Type;
  modelFun {arg_types : list types} {res_type : types}
    : functions arg_types res_type
      -> vararg_function modelType arg_types (modelType res_type);
  modelPred {arg_types : list types}
    : predicates arg_types -> vararg_predicate modelType arg_types
}.

Section local. #[local] Unset Implicit Arguments.
Context (m : Model).

Fixpoint value [type_context] (context : heterolist m.(modelType) type_context)
               [type] (term : Term type_context type)
  : m.(modelType) type := match term with
| var occ    => ref_by_occ occ context
| app f args => vararg_apply (m.(modelFun) f)
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
                  ((fix map_value [is] (l : heterolist (Term type_context) is)
                    : heterolist m.(modelType) is := match l with
                  | []           => []
                  | term :: rest => value context term :: map_value rest
                  end) _ args)
end.
(* This runs into the problem of having a heterolist with elements of the right
   types and with the right elements, but with the wrong indices for the types of
   the elements. *)
(* Fixpoint value_ (t : sigT (Term type_context)) {struct t}
  : m.(modelType) (projT1 t) := match t as t return m.(modelType) (projT1 t) with
| existT _ type (var occ)    => ref_by_occ occ context
| existT _ type (app f args) => vararg_apply (m.(modelFun) f)
                  (map_hetero value_ (homogenize args))
end. *)

Fixpoint interpret [type_context] (context : heterolist m.(modelType) type_context)
                   (φ : Formula type_context) : Prop := match φ with
| predApp r args => vararg_apply (m.(modelPred) r) (heteromap (value context) args)
| false          => False
| impl p q       => interpret context p -> interpret context q
| @univ _ type φ => forall x : m.(modelType) type, interpret (x :: context) φ
end.

End local.


End Main.
#[global] Arguments var {_ _ _ _}.
#[global] Arguments false {_ _ _ _}.

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

(* Check neg (atomic (existT2 relations (heterolist (Term functions nil)) _
                      int_eq
                      [ app succ [app succ [app zero []]]
                      ; app succ [app zero []]]))
    : Sentence functions relations. *)
Check univ (type := Nat) (impl (predApp int_eq [var (head _ _); app zero []])
                         (impl (predApp int_eq [var (head _ _); app succ [app zero []]])
                             false)) : Sentence functions relations.

End Example.