From Coq Require Program.Basics Bool.Bool Lists.List.

Section Logic. Implicit Types p q r : Prop.
Import Coq.Program.Basics. Local Open Scope program_scope.

Definition not_elim {p q} : ~p -> p -> q := compose (False_ind q).
Definition absurd {p q} : p -> ~p -> q := flip not_elim.

Definition or_elim_left {p q} : p \/ q -> ~p -> q := or_ind absurd const.
Definition or_elim_right {p q} : p \/ q -> ~q -> p := or_ind const absurd.

End Logic.

Section Is_true.
Import Coq.Bool.Bool. Export Coq.Bool.Bool (Is_true).
Variables b b1 b2 : bool.

Lemma Is_true_iff_eq_true : Is_true b <-> b = true. split
;[ apply Is_true_eq_true | apply Is_true_eq_left ].
Qed.

Lemma Is_true_em : Is_true b \/ ~Is_true b.
destruct b; intuition. Qed.

Lemma Is_true_and : Is_true (b1 && b2) <-> Is_true b1 /\ Is_true b2. split
;[ exact (andb_prop_elim b1 b2) | exact (andb_prop_intro b1 b2) ]. Qed.

Lemma Is_true_or : Is_true (b1 || b2) <-> Is_true b1 \/ Is_true b2. split
;[ exact (orb_prop_elim b1 b2) | exact (orb_prop_intro b1 b2) ]. Qed.

Lemma Is_true_impl : Is_true (implb b1 b2) <-> (Is_true b1 -> Is_true b2).
destruct b1, b2; intuition. Qed.

End Is_true.

Section occurrence.
Import (notations) List.ListNotations. Open Scope list.

Inductive occ {A : Type} : A -> list A -> Type :=
| occ_head a rest : occ a (a :: rest)
| occ_tail a rest b : occ a rest -> occ a (b :: rest).
#[global] Arguments occ_tail {_ _ _} [b].
(* #[global] Arguments occ_rect {_ _} _ _ {_ _} _. *)

Definition no_occ_nil {A : Type} (a : A) (h : occ a []) : False :=
(* `in` enables match to eliminate constructors whose type doesn't match
   the index. I think. *)
match h in occ _ [] with end.

Context {A : Type} {motive : A -> Type}. Implicit Types (a : A) (l : list A).

Fixpoint remove_occ [l a] (occ : occ a l) : list A :=
match occ with
| occ_head _ rest       => rest
| @occ_tail _ _ _ b occ => b :: remove_occ occ
end.
Print occ_rect.

(* Definition my_subst
  : forall a l, occ a l
  -> (forall a, occ a l -> motive a) -> forall b, occ b l -> motive a -> motive b.
induction 1; intros f(* ; induction 1 *).
(* apply (occ_rect A (fun a l _ => motive a -> (forall a, occ a l -> motive a) -> forall b, occ b l -> motive b)). *)
+ destruct 1 eqn:h.
  - exact X.


Fixpoint subst_occ {l a}
  : occ a l -> motive a -> (forall a, occ a l -> motive a)
  -> forall {b}, occ b l -> motive b :=
occ_rect A (fun a l _ => motive a -> (forall a, occ a l -> motive a) -> forall b, occ b l -> motive b)
         (fun a rest val f => (fun f => (fun b occ => f b (a::rest) occ))
           (occ_rect A (fun b _ _ => motive b) _ _)) _
  a l

(* match occ1 with
| occ_head _ _ => fun val f => fix rec {b} occ := match occ in occ b l return motive b with
  | occ_head _ _ => val
  | occ_tail _   => f b
  end
| occ_tail _ => _
end *).
 *)
End occurrence.

Section heterolist.
Set Implicit Arguments. Unset Strict Implicit. Set Maximal Implicit Insertion.

Variable Ind : Type. Implicit Types motive : Ind -> Type.

Section defs. Variable motive : Ind -> Type.

(* Using a list of types caused a universe inconsistency error in the
   definition of Term (_after_ enabling universe polymorphism).
   Using an indexed family was recommended at
   https://coq.discourse.group/t/constructing-heterogeneous-lists/1467/4
   and fixed the error. *)
Inductive heterolist : list Ind -> Type :=
| heteronil : heterolist nil
| heterocons {i is} : motive i -> heterolist is -> heterolist (i :: is).

(* It is easier to do this than to write these matches inline due to
   the spurious new copies of bindings for i and is Coq introduces and
   then complains about. *)
Definition heterofirst {i is} : heterolist (i::is) -> motive i :=
fun '(heterocons x _) => x.
Definition heterorest {i is} : heterolist (i::is) -> heterolist is :=
fun '(heterocons _ rest) => rest.

Fixpoint homogenize {is} (l : heterolist is)
  : list (sigT motive) := match l with
| heteronil       => nil
| heterocons x xs => cons (existT _ _ x) (homogenize xs)
end.

Fixpoint map_hetero (f : forall i, motive i) is : heterolist is := match is with
| nil       => heteronil
| cons i is => heterocons (f i) (map_hetero f is)
end.

End defs.
#[global] Arguments heteronil {motive}.

Fixpoint heteromap {motive1 motive2}
                   (f : forall [i : Ind], motive1 i -> motive2 i)
  {is} (l : heterolist motive1 is) : heterolist motive2 is := match l with
| heteronil         => heteronil
| heterocons a rest => heterocons (f a) (heteromap f rest)
end.

End heterolist.

Module HeterolistNotations.
  Declare Scope heterolist. Bind Scope heterolist with heterolist.
  Delimit Scope heterolist with heterolist. Open Scope heterolist.

  Notation "[ ]" := heteronil : heterolist.
  Infix "::" := heterocons : heterolist.
  Notation "[ x ; .. ; y ]" := (x :: .. (y :: heteronil)..) : heterolist.
End HeterolistNotations.

Fixpoint ref_by_occ {Ind} {motive : Ind -> Type} {i is} (h : occ i is)
  : heterolist motive is -> motive i := match h with
| occ_head _ _ => heterofirst
| occ_tail h   => fun l => ref_by_occ h (heterorest l)
end.

Section Functions.

(* Definition dep_uncurry {A : Type} {motive : A -> Type}
                       {motive' : forall a, motive a -> Type}
    (f : forall a (b : motive a), motive' a b)
  : let motive' : sigT motive -> Type :=
      fun '(existT _ a b : sigT motive) => motive' a b in
    forall x : sigT motive, motive' x :=
fun '(existT _ a b) => f a b.

Definition dep_curry {A : Type} {motive : A -> Type}
                     {motive' : sigT motive -> Type}
    (f : forall x : sigT motive, motive' x)
  a (b : motive a) : motive' (existT _ a b) := f (existT _ a b). *)

Section Vararg.
Variables (Ind : Type) (motive : Ind -> Type).

Fixpoint vararg_function (arg_types : list Ind) (B : Type) : Type :=
match arg_types with
| nil         => B
| cons i rest => motive i -> vararg_function rest B
end.

Definition vararg_predicate (arg_types : list Ind) :=
vararg_function arg_types Prop.

Fixpoint vararg_apply {arg_types : list Ind} {B : Type}
                      (f : vararg_function arg_types B)
                      (args : heterolist motive arg_types) : B :=
(* We need f effectively unapplied so its type changes with `args`. *)
(match args in heterolist _ arg_types return vararg_function arg_types B -> B with
| heteronil           => id
| heterocons arg rest => fun f => vararg_apply (f arg) rest
end) f.

End Vararg.

End Functions.
