From Coq Require Program.Basics Bool.Bool Lists.List.

Import Coq.Program.Basics. Local Open Scope program_scope.
Section Logic. Implicit Types p q r : Prop.

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



(* Bounded natural numbers. *)
Inductive BNat : nat -> Set :=
| BNat_zero {n} : BNat (S n)
| BNat_succ {n} : BNat n -> BNat (S n).

Lemma no_bnat_zero : BNat 0 -> False. exact (fun a => match a with end). Qed.

(* Occurrences of an element in a list. *)
Inductive Occ {A : Type} : A -> list A -> Type :=
| Occ_head {a rest} : Occ a (cons a rest)
| Occ_tail {a rest b} : Occ a rest -> Occ a (cons b rest).

Module Occ.
Section ForVariables. Context {A : Type}. Implicit Types (a : A) (l : list A).
Import (notations) List.ListNotations. #[local] Open Scope list.

Fixpoint addBefore l1 {a l2} : Occ a l2 -> Occ a (l1 ++ l2) := match l1 with
| []        => id
| a :: rest => Occ_tail ∘ addBefore rest
end.

Fixpoint addAfter l1 {a l2} (occ : Occ a l2) : Occ a (l2 ++ l1) :=
match occ with
| Occ_head     => Occ_head
| Occ_tail occ => Occ_tail (addAfter l1 occ)
end.

Fixpoint toBNat {a l} (occ : Occ a l) : BNat (List.length l) := match occ with
| Occ_head     => BNat_zero
| Occ_tail occ => BNat_succ (toBNat occ)
end.

Definition fromBNat {l} : BNat (List.length l) -> {a & Occ a l}.
refine (let _fromBNat := _ : forall n (a : BNat n) l,
                               List.length l = n -> {a & Occ a l}
        in fun b => _fromBNat _ b _ eq_refl).
induction 1 as [|? b h_i]
; (intros [|a rest] h;
  simpl in h; [ discriminate h | injection h as h ]); [
  econstructor; exact Occ_head
| refine (let (a, h) := h_i rest h in _); econstructor; exact (Occ_tail h)
].
Defined.

End ForVariables.
End Occ.



(* Heterogenous lists. *)
Inductive Heterolist {A : Type} {motive : A -> Type} : list A -> Type :=
| heteronil : Heterolist nil
| heterocons {a rest} : motive a -> Heterolist rest -> Heterolist (cons a rest).
#[global] Arguments Heterolist {A} motive _.

Module Heterolist.

Module Notation.
  Declare Scope heterolist. Bind Scope heterolist with Heterolist.
  Delimit Scope heterolist with heterolist. #[local] Open Scope heterolist.

  Notation "[ ]" := heteronil : heterolist.
  Infix "::" := heterocons : heterolist.
  (* This is redundant, but introducing the mere syntax [ x ; .. ; y ]
     interferes with `Coq.Lists.List.ListNotations`'s redundant way of doing
     this. *)
  Notation "[ x ]" := (x :: heteronil) : heterolist.
  Notation "[ x ; y ; .. ; z ]" := (x :: (y :: .. (z :: heteronil)..))
    : heterolist.
End Notation.
Import (notations) Notation. #[local] Open Scope heterolist.

Section ForVariables.
Context {A : Type}. Implicit Type motive : A -> Type.

Section Temp. Context {motive}.
Definition first {a l} : Heterolist motive (a :: l) -> motive a :=
fun '(a :: _) => a.
Definition rest {a l} : Heterolist motive (a :: l) -> Heterolist motive l :=
fun '(_ :: l) => l.

Fixpoint ref {a l} (occ : Occ a l) : Heterolist motive l -> motive a :=
match occ with
| Occ_head     => first
| Occ_tail occ => ref occ ∘ rest
end.
End Temp.

(* Let's see how well this works. *)
(* Problem: `List.map id l` and `l` are not definitionally equal.
   Hence we define a `map` below for when `B` is `A` and `f` is `id`. *)
Fixpoint map' {A : Type} {motive1 : A -> Type} {B : Type} {motive2 : B -> Type}
             [f : A -> B] (f' : forall [a], motive1 a -> motive2 (f a))
  {l'} (l : Heterolist motive1 l') : Heterolist motive2 (List.map f l') :=
match l with
| []        => []
| a :: rest => f' a :: map' f' rest
end.

Fixpoint map {motive1 motive2} (f : forall [a], motive1 a -> motive2 a)
  {l'} (l : Heterolist motive1 l') : Heterolist motive2 l' := match l with
(* `List.map id` is not _definitionally_ `id`, and don't want to rewrite. *)
(* map' f l' *)
| []        => []
| a :: rest => f a :: map f rest
end.

Check map' (*motive1 := fun _ => nat*) (motive2 := id)
            (fun _ (b : nat) => b).

Fixpoint mapList {motive} l
  : (forall {a}, Occ a l -> motive a) -> Heterolist motive l := match l with
| nil         => fun f => []
| cons a rest => fun f => f a Occ_head :: mapList rest (fun {a} o => f a (Occ_tail o))
end.

End ForVariables.
End Heterolist.



Section Functions.

Section Vararg. Context {A : Type} (motive : A -> Type).

Fixpoint vararg_function (l : list A) (B : Type) : Type :=
match l with
| nil         => B
| cons a rest => motive a -> vararg_function rest B
end.

Definition vararg_predicate (l : list A) :=
vararg_function l Prop.

Fixpoint vararg_apply {l B} (f : vararg_function l B)
                            (args : Heterolist motive l) : B :=
(* We need f effectively unapplied so its type changes with `args`. *)
match args in Heterolist _ l return vararg_function l B -> B with
| heteronil           => id
| heterocons arg rest => fun f => vararg_apply (f arg) rest
end f.

Fixpoint vararg_curry {l B} : (Heterolist motive l -> B) -> vararg_function l B :=
match l with
| nil         => fun f => f heteronil
| cons a rest => fun f arg => vararg_curry (fun rest => f (heterocons arg rest))
end.

End Vararg.
#[global] Arguments vararg_apply {_ motive _ _}.
#[global] Arguments vararg_curry {_ motive _ _}.

End Functions.
