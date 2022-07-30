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



(* Bounded natural numbers, for contexts, array indices, etc. *)
Inductive BNat : nat -> Set :=
| BNat_zero {n} : BNat (S n)
| BNat_succ {n} : BNat n -> BNat (S n).

Module BNat.
Implicit Types (m n : nat).

(* Map from `BNat n` to `BNat (S n)` preserving number of `BNat`s after. *)
Definition toSucc_a {n} := BNat_succ (n := n).
(* Map from `BNat n` to `BNat (S n)` preserving number of `BNat`s before. *)
Fixpoint toSucc_b {n} (a : BNat n) : BNat (S n) := match a with
| BNat_zero => BNat_zero
| BNat_succ a => BNat_succ (toSucc_b a)
end.


(* Map from `BNat n` to `BNat (m + n)` preserving number of `BNat`s after. *)
(* This adds `m` applications of `BNat_succ` without changing the type of
   the `BNat_zero`. *)
Fixpoint toSum_a m {n} : BNat n -> BNat (m + n) := match m with
| 0   => id
| S m => toSucc_a ∘ toSum_a m
end.

(* Map from `BNat n` to `BNat (m + n)` preserving number of `BNat`s before. *)
Fixpoint toSum_b m {n} : BNat n -> BNat (m + n) :=
(* eq_subst (P := BNat) (add_comm n m) ∘ toSum_b' m *)
match m return BNat n -> BNat (m + n) with
| 0   => id
| S m => toSucc_b ∘ toSum_b m
end.

(* Map from `BNat n` to `BNat (n + m)` preserving number of `BNat`s before. *)
(* This effectively just adds `m` to the type of the BNat_zero inside. *)
Fixpoint toSum_b' m {n} (a : BNat n) : BNat (n + m) :=
match a in BNat n return BNat (n + m) with
| BNat_zero => BNat_zero
| BNat_succ a => BNat_succ (toSum_b' m a)
end.

End BNat.



(* Arrays - lists of given length *)
Inductive Array {A : Type} : nat -> Type :=
| Array_nil : Array 0
| Array_cons {n} : A -> Array n -> Array (S n).
#[global] Arguments Array (A) : clear implicits.

Module Array.
Section ForVariables. Context {A : Type}.

#[local] Notation "[ ]" := Array_nil.
#[local] Infix "::" := Array_cons (at level 60, right associativity).

(* As usual, Coq's pathetic pattern matching has forced me to define
   this unnecessarily. *)
Definition first {n} : Array A (S n) -> A := fun '(a :: _) => a.
Definition rest {n} : Array A (S n) -> Array A n := fun '(_ :: arr) => arr.

Fixpoint ref {n} (a : BNat n) : Array A n -> A :=
match a with
| BNat_zero   => first
| BNat_succ a => ref a ∘ rest
end.

Fixpoint map {A B} (f : A -> B) {n} (arr : Array A n) : Array B n := match arr with
| [] => Array_nil
| a :: rest => f a :: map f rest
end.

End ForVariables.

Module Notation.
  Declare Scope array. Bind Scope array with Array.
  Delimit Scope array with array. Open Scope array.

  Notation "[ ]" := Array_nil : array.
  Infix "::" := Array_cons : array.
  Notation "[ x ; .. ; y ]" := (x :: .. (y :: Array_nil)..) : array.
End Notation.

End Array.



Section Functions.

Section Vararg.

Fixpoint vararg_function (n : nat) (A B : Type) : Type :=
match n with
| 0   => B
| S n => A -> vararg_function n A B
end.

Definition vararg_predicate (n : nat) (A : Type) :=
vararg_function n A Prop.

Fixpoint vararg_apply {n A B} (f : vararg_function n A B) (args : Array A n) : B :=
(* We need f effectively unapplied so its type changes with `args`. *)
match args in Array _ n return vararg_function n A B -> B with
| Array_nil           => id
| Array_cons arg rest => fun f => vararg_apply (f arg) rest
end f.

End Vararg.

End Functions.
