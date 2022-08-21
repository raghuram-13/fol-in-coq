From Coq Require Program.Basics Bool.Bool Lists.List.

Import Coq.Program.Basics. Local Open Scope program_scope.

Section Transparency.
#[global] Arguments id {_} _ /.
#[global] Arguments compose {_ _ _} _ _ _ /.
End Transparency.

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

Section Equality.
Import (notations) EqNotations.

Theorem rew_app {A : Type} {P Q : A -> Type} (f : forall {a}, P a -> Q a)
                {a1 a2} (h : a1 = a2) (x : P a1)
  : rew h in f x = f (rew h in x). exact
(match h with eq_refl => eq_refl end). Qed.

End Equality.



(* Bounded natural numbers. *)
Inductive BNat : nat -> Set :=
| BNat_zero {n} : BNat (S n)
| BNat_succ {n} : BNat n -> BNat (S n).

Module BNat.

Definition elim_bnat_zero {P : BNat 0 -> Type} (n : BNat 0) : P n :=
match n with end.
Lemma no_bnat_zero : BNat 0 -> False. exact elim_bnat_zero. Qed.

(* Better to define functions when Coq's pattern-matching is so difficult. *)
Section Pred. Context {n} (a : BNat (S n)).
Definition pred_spec : { b : BNat n | BNat_succ b = a } + {BNat_zero = a} :=
match a with
| BNat_zero   => inright eq_refl
| BNat_succ a => inleft (exist _ a eq_refl)
end.
Definition pred : BNat n + {BNat_zero = a} := match pred_spec with
| inright h => inright h
| inleft (exist _ a _) => inleft a
end.
End Pred.

Section Cases. Import (notations) EqNotations.
Definition cases {n} {P : BNat (S n) -> Type}
  (zero : P BNat_zero) (succ : forall a : BNat n, P (BNat_succ a))
  (a : BNat (S n)) : P a := match BNat.pred_spec a with
| inright h            => rew h in zero
| inleft (exist _ n h) => rew h in succ n
end.
End Cases.

End BNat.

Definition ListIndex {A} := BNat ∘ List.length (A := A).

Fixpoint ListIndex_rect {A} {P : forall l : list A, ListIndex l -> Type}
    (zero : forall {a rest}, P (cons a rest) BNat_zero)
    (succ : forall {a rest ind}, P rest ind -> P (cons a rest) (BNat_succ ind))
  [l] : forall ind, P l ind := match l with
| nil         => BNat.elim_bnat_zero
| cons a rest => BNat.cases zero (fun ind =>
                                   succ (ListIndex_rect (@zero) (@succ) ind))
end.
Arguments ListIndex_rect _ _ &.

Module ListIndex.

(* Better type inference *)
Section PseudoConstructors. Context {A} {a : A} {l : list A}.
Definition head : ListIndex (a::l) := BNat_zero.
Definition fromTail : ListIndex l -> ListIndex (a::l) := BNat_succ.
End PseudoConstructors.

Definition ref {A} : forall (l : list A), ListIndex l -> A :=
(* match l with
| nil      => BNat.elim_bnat_zero
| cons a l => BNat.cases a (ref l)
end *)
ListIndex_rect (fun a _ => a) (fun _ _ _ rec => rec).

Section Add. Context {A : Type}. Implicit Type l : list A.
Fixpoint addBefore l1 {l2} : ListIndex l2 -> ListIndex (l1 ++ l2) :=
match l1 with
| nil         => id
| cons a rest => fromTail ∘ addBefore rest
end.
(* Import (notations) EqNotations.
Definition addBefore' l1 {l2} : ListIndex l2 -> ListIndex (l1 ++ l2) :=
rew <- [fun length => ListIndex l2 -> BNat length] (List.app_length l1 l2) in
BNat.addBefore (List.length l1) (n := List.length l2). *)

Definition addAfter l1 : forall {l2}, ListIndex l2 -> ListIndex (l2 ++ l1) :=
(* match l2 with
| nil         => False_rect _ ∘ BNat.no_bnat_zero
| cons a rest => BNat.cases BNat_zero (BNat_succ ∘ addAfter l1)
end *)
ListIndex_rect (fun _ _ => head) (fun _ _ _ rec => fromTail rec).

Section AddRefLemmas. Import (notations) EqNotations.

(* Lesson: ALWAYS define an equality you might rewrite using with `Defined`
   so it is transparent to at least the type-checker for definitional
   equality-checking of terms rewriting using it,
   unless assuming proof irrelevance/working in `SProp`.

   Although this may not be enough if a theorem you want to prove is
   not provable without proof irrelevance.  *)
Lemma ref_addBefore l1 {l2} (ind : ListIndex l2)
  : ref (l1 ++ l2) (addBefore l1 ind) = ref l2 ind.
induction l1 as [|a rest h_i]; [ reflexivity | exact h_i ].
Defined.

Lemma ref_addAfter l1 {l2} (ind : ListIndex l2)
  : ref (l2 ++ l1) (addAfter l1 ind) = ref l2 ind.
induction ind as [|??? rec] using @ListIndex_rect; [ reflexivity | exact rec ].
Defined.

#[global] Opaque ref_addBefore ref_addAfter.
End AddRefLemmas.

End Add.

End ListIndex.

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

Fixpoint toIndex {a l} (occ : Occ a l) : ListIndex l := match occ with
| Occ_head     => ListIndex.head
| Occ_tail occ => ListIndex.fromTail (toIndex occ)
end.

Definition fromIndex : forall l (ind : ListIndex l),
  Occ (ListIndex.ref l ind) l :=
(* match l with
| nil      => BNat.elim_bnat_zero
| cons a l => BNat.cases Occ_head (fun n => Occ_tail (fromIndex l n))
end *)
ListIndex_rect (fun _ _ => Occ_head) (fun _ _ _ rec => Occ_tail rec).

Section OccBNatLemmas. Import (notations) EqNotations.

Lemma ref_toIndex {a l} (occ : Occ a l) : ListIndex.ref l (toIndex occ) = a.
(* `h_i` takes an argument unnecessarily and I don't know why.
     induction occ as [|? ? ? occ' h_i]
   So I'm doing the induction manually. *)
revert a l occ; apply Occ_ind; [intros ? ?|intros ? ? ? occ h_i];
[ reflexivity | exact h_i ].
Defined. (* Transparent because we need it to prove things about it in Coq. *)

Lemma from_toIndex {a l} (occ : Occ a l)
  : rew [fun a => Occ a l] ref_toIndex occ in fromIndex l (toIndex occ) = occ.
induction occ.
+ reflexivity.
+ simpl.
  unfold fromIndex; simpl; unfold BNat.cases; simpl;
  fold (fromIndex rest (toIndex occ)).
  rewrite rew_app with (f := fun a => Occ_tail (a := a)).
  f_equal; assumption.
Qed.

#[global] Opaque ref_toIndex.
End OccBNatLemmas.

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

Inductive Forall {A motive} {P : forall {a : A}, motive a -> Prop}
  : forall {l}, Heterolist motive l -> Prop :=
| Forall_nil : Forall []
| Forall_cons {a l} {x : motive a} {l' : Heterolist motive l}
  : P x -> Forall l' -> Forall (x :: l').
#[global] Arguments Forall {A motive} P {_} _.

(* Inductive Forall' {A motive}
  : forall {l} (P : Heterolist (fun a : A => motive a -> Prop) l),
      Heterolist motive l -> Prop :=
| Forall'_nil : Forall' [] []
| Forall'_cons {a l} {x : motive a} {l' : Heterolist motive l}
                     {Pa : motive a -> Prop} {P}
  : Pa x -> Forall' P l' -> Forall' (Pa :: P) (x :: l'). *)

Section ForVariables.
Context {A : Type}. Implicit Type motive : A -> Type.

Section Temp. Context {motive}.
Definition first {a l} : Heterolist motive (a :: l) -> motive a :=
fun '(a :: _) => a.
Definition rest {a l} : Heterolist motive (a :: l) -> Heterolist motive l :=
fun '(_ :: l) => l.

Section Ref.

(* Keep only the list as a parameter to ensure the `BNat` type gets rewritten
   when matching against it. *)
Definition ref : forall {l} (ind : ListIndex l), Heterolist motive l
  -> motive (ListIndex.ref l ind) :=
(* match l with
| nil      => (* dependent comp *) fun n => False_rect _ (BNat.no_bnat_zero n)
| cons a l => BNat.cases (P := fun n => Heterolist motive (a::l) -> motive (ListIndex.ref (a::l) n))
                first
                (fun n => fun l => ref n (rest l))
end *)
ListIndex_rect (fun _ _ => first) (fun _ _ _ rec => rec ∘ rest).
End Ref.

Fixpoint ref' {a l} (occ : Occ a l) : Heterolist motive l -> motive a :=
match occ with
| Occ_head     => first
| Occ_tail occ => ref' occ ∘ rest
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
Fixpoint mapList {motive} l : (forall ind, motive (ListIndex.ref l ind))
  -> Heterolist motive l := match l with
| nil         => fun f => []
| cons a rest => fun f => f BNat_zero :: mapList rest (fun n => f (BNat_succ n))
end.

Fixpoint mapList_occ {motive} l
  : (forall {a}, Occ a l -> motive a) -> Heterolist motive l := match l with
| nil         => fun f => []
| cons a rest => fun f => f a Occ_head :: mapList rest (fun {a} o => f a (Occ_tail o))
end.
End mapList.

Section MapLemmas. Context {motive1 motive2 motive3}.

Lemma map_mapList {l}
    (f : forall n, motive1 (ListIndex.ref l n))
    (g : forall [a], motive1 a -> motive2 a)
  : map g (mapList l f) = mapList l (fun n => g (f n)).
induction l as [|?? h_i]; [ reflexivity | simpl; f_equal; apply h_i ].
Qed.

Lemma map_map (f : forall [a], motive1 a -> motive2 a)
              (g : forall [a], motive2 a -> motive3 a)
  : forall {l'} (l : Heterolist motive1 l'),
    map g (map f l) = map (fun a => @g a ∘ @f a) l.
induction l as [|???? h_i]; [ reflexivity | simpl; f_equal; exact h_i ].
Qed.

Lemma ref_map_eq_app_ref (f : forall [a], motive1 a -> motive2 a)
                         {l'} (l : Heterolist motive1 l') (ind : ListIndex l')
  : ref ind (map f l) = f (ref ind l).
induction ind as [|?? ind h_i] using @ListIndex_rect; [
  exact (match l with | _ :: _ => eq_refl end)
| replace l with (first l :: rest l) by
    exact (match l with | _ :: _ => eq_refl end);
  f_equal; exact (h_i (rest l))
].
Qed.

Lemma map_equals {f g : forall [a], motive1 a -> motive2 a}
                 {l'} {l : Heterolist motive1 l'}
  (h : Forall (fun _ x => f x = g x) l) : map f l = map g l.
induction h as [|???? h _ h_i]; [
  reflexivity
| simpl; f_equal; [ exact h | exact h_i ]
]. Qed.

End MapLemmas. End Map.

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
