Set Implicit Arguments. Unset Strict Implicit.

Require Import Coq.Program.Basics.
Require Import SetNotations.
Require Import Coq.Classes.RelationClasses.

(* "Setoid handling" *)
Require Coq.Classes.Morphisms. Import (notations) Coq.Classes.Morphisms.
Import Coq.Classes.Morphisms (Proper).
From Coq Require Setoid.

(* Why is this missing? *)
(* It caused an endless loop when searching for an instance of `Reflexive`
   at least once. *)
(* #[local] Existing Instance Build_Equivalence. *)

Structure Preordered :=
{ carrier :> Type; le : carrier -> carrier -> Prop; pre : PreOrder le }.

(* In the context `X : Preordered`, we can use `le : X -> X -> Prop` without
   specifying the implicit argument as `X`. *)
Arguments le {X} : rename.

Definition ge {X : Preordered} : X -> X -> Prop := flip le.

#[export] Instance preorder_bundle (X : Preordered) : PreOrder X.(le) := X.(pre).

Notation "x ≤[ X ] y" := (le (X := X) x y) (at level 70).
Notation "x ≤ y"      := (le x y)          (at level 70).
Notation "x ≥[ X ] y" := (ge (X := X) x y) (at level 70).
Notation "x ≥ y"      := (ge x y)          (at level 70).

Section PreorderedProperties. Context {X : Preordered}.

Definition le_refl : Reflexive X.(le) := reflexivity.
Definition le_rfl {x : X} : x ≤ x := le_refl x.

Definition le_trans : Transitive X.(le) := transitivity.

Definition equiv (x y : X) : Prop := x ≤ y /\ y ≤ x.

Section ProjectedIneqs. Context [x y : X] (h : equiv x y).
Definition equiv_le     : x ≤ y := proj1 h.
Definition equiv_le_rev : y ≤ x := proj2 h.
Definition equiv_ge     : x ≥ y := proj2 h.
Definition equiv_ge_rev : y ≥ x := proj1 h.
End ProjectedIneqs.

Definition equiv_refl : Reflexive equiv := fun _ => conj le_rfl le_rfl.
Definition equiv_rfl {x : X} : equiv x x := equiv_refl x.

Definition equiv_sym : Symmetric equiv :=
fun _ _ h => conj (equiv_le_rev h) (equiv_le h).

Definition equiv_trans : Transitive equiv := fun _ _ _ h1 h2 =>
conj (le_trans (equiv_le h1) (equiv_le h2))
     (le_trans (equiv_le_rev h2) (equiv_le_rev h1)).

Instance equiv_equivalence : Equivalence equiv :=
Build_Equivalence equiv equiv_refl equiv_sym equiv_trans.

Instance le_respects_equiv : Proper (equiv ==> equiv ==> iff) X.(le) :=
fun _ _ h_x _ _ h_y => conj
(fun h_le_1 => le_trans (le_trans (equiv_ge h_x) h_le_1) (equiv_le h_y))
(fun h_le_2 => le_trans (le_trans (equiv_le h_x) h_le_2) (equiv_ge h_y)).

End PreorderedProperties.

Notation "x ∼ y" := (equiv x y) (at level 70).
Notation "x ∼[ X ] y" := (equiv (X := X) x y) (at level 70).

Definition Preordered_dual (X : Preordered) : Preordered := {|
  carrier := X.(carrier);
  le := flip X.(le);
  pre := flip_PreOrder X.(pre)
|}.

Section SpecialElements.

(* Definition is_sup (A : Subset *)

End SpecialElements.

Structure BooleanAlgebra := {
  preCarrier :> Preordered;

  and : preCarrier -> preCarrier -> preCarrier;
  or : preCarrier -> preCarrier -> preCarrier;
  true : preCarrier; false : preCarrier;
  not : preCarrier -> preCarrier;

  and_spec p q r : le r (and p q) <-> le r p /\ le r q;
  or_spec p q r : le (or p q) r <-> le p r /\ le q r;
  and_distrib_or p q r : equiv (and p (or q r)) (or (and p q) (and p r));
  false_spec p : le false p; true_spec p : le p true;
  and_not' p : and p (not p) ≤ false;
  or_not' p : true ≤ or p (not p)
}.

Local Notation "⊥[ B ]" := (B.(false)).
Local Notation "⊥"      := (_.(false)).
Local Notation "⊤[ B ]" := (B.(true)).
Local Notation "⊤"      := (_.(true)).
(* I can redefine /\, \/, but I can't change their levels.  So use \./, /.\. *)
Local Notation "x /.\[ B ] y" := (B.(and) x y) (at level 65, right associativity).
Local Notation "x /.\ y"      := (_.(and) x y) (at level 65, right associativity).
Local Notation "x \./[ B ] y" := (B.(or) x y)  (at level 65, right associativity).
Local Notation "x \./ y"      := (_.(or) x y)  (at level 65, right associativity).
Local Notation "¬ x"         := (_.(not) x)   (at level 35).

Section BasicResults. Context {B : BooleanAlgebra}.

Definition false_of_le_false p (h : p ≤ ⊥) : p ∼ ⊥ := conj h (B.(false_spec) p).
Definition true_of_true_le p (h : ⊤ ≤ p) : p ∼ ⊤ := conj (B.(true_spec) p) h.

Definition and_not_equiv_false p : p /.\ ¬p ∼ ⊥ := false_of_le_false (and_not' p).
Definition or_not_equiv_true p : p \./ ¬p ∼ ⊤ := true_of_true_le (or_not' p).

Definition binop_respects_equiv_of_mono (bin_op : B -> B -> B)
        (h : Proper (le ==> le ==> le) bin_op)
    : Proper (equiv ==> equiv ==> equiv) bin_op :=
fun _ _ h_x _ _ h_y => conj (h _ _ (equiv_le h_x)     _ _ (equiv_le h_y))
                            (h _ _ (equiv_le_rev h_x) _ _ (equiv_le_rev h_y)).

Section and.

Definition and_le_left p q : p /.\ q ≤ p :=
proj1 (proj1 (B.(and_spec) p q (p /.\ q)) le_rfl).
Definition and_le_right p q : p /.\ q ≤ q :=
proj2 (proj1 (B.(and_spec) p q (p /.\ q)) le_rfl).
Definition le_and_of_le_both p q r : r ≤ p -> r ≤ q -> r ≤ p /.\ q :=
fun h1 h2 => proj2 (B.(and_spec) p q r) (conj h1 h2).

Definition and_mono : Proper (le ++> le ++> le) B.(and) := fun x1 x2 h_x y1 y2 h_y =>
le_and_of_le_both (le_trans (and_le_left x1 y1) h_x)
                  (le_trans (and_le_right x1 y1) h_y).

Instance and_respects_equiv : Proper (equiv ==> equiv ==> equiv) B.(and) :=
binop_respects_equiv_of_mono and_mono.

Definition and_true p : p /.\ ⊤ ∼ p :=
conj (and_le_left p ⊤) (le_and_of_le_both (le_refl p) (B.(true_spec) p)).

Definition and_false p : p /.\ ⊥ ∼ ⊥ :=
conj (and_le_right p ⊥) (B.(false_spec) _).

Definition and_comm p q : p /.\ q ∼ q /.\ p := conj
(le_and_of_le_both (and_le_right p q) (and_le_left p q))
(le_and_of_le_both (and_le_right q p) (and_le_left q p)).

Definition and_assoc p q r : (p /.\ q) /.\ r ∼ p /.\ (q /.\ r) := conj
(le_and_of_le_both   (le_trans (and_le_left _ r) (and_le_left p q)  : _ ≤ p)
  (le_and_of_le_both (le_trans (and_le_left _ r) (and_le_right p q) : _ ≤ q)
                     (and_le_right _ r                              : _ ≤ r)))
(le_and_of_le_both (le_and_of_le_both
  (and_le_left p _                                : _ ≤ p)
  (le_trans (and_le_right p _) (and_le_left q r)  : _ ≤ q))
  (le_trans (and_le_right p _) (and_le_right q r) : _ ≤ r)).

End and.

Section or.

Definition left_le_or p q : p ≤ p \./ q :=
proj1 (proj1 (B.(or_spec) p q (p \./ q)) le_rfl).
Definition right_le_or p q : q ≤ p \./ q :=
proj2 (proj1 (B.(or_spec) p q (p \./ q)) le_rfl).
Definition or_le_of_both_le p q r : p ≤ r -> q ≤ r -> p \./ q ≤ r :=
fun h1 h2 => proj2 (B.(or_spec) p q r) (conj h1 h2).

Definition or_mono : Proper (le ++> le ++> le) B.(or) := fun x1 x2 h_x y1 y2 h_y =>
or_le_of_both_le (le_trans h_x (left_le_or x2 y2))
                 (le_trans h_y (right_le_or x2 y2)).

Instance or_respects_equiv : Proper (equiv ==> equiv ==> equiv) B.(or) :=
binop_respects_equiv_of_mono or_mono.

Definition or_false p : p \./ ⊥ ∼ p :=
conj (or_le_of_both_le (le_refl p) (B.(false_spec) p)) (left_le_or p ⊥).

Definition or_true p : p \./ ⊤ ∼ ⊤ :=
conj (B.(true_spec) _) (right_le_or p ⊤).

Definition or_comm p q : p \./ q ∼ q \./ p := conj
(or_le_of_both_le (right_le_or q p) (left_le_or q p))
(or_le_of_both_le (right_le_or p q) (left_le_or p q)).

Definition or_assoc p q r : (p \./ q) \./ r ∼ p \./ (q \./ r) := conj
(or_le_of_both_le (or_le_of_both_le
  (left_le_or p _                               : p ≤ _)
  (le_trans (left_le_or q r) (right_le_or p _)  : q ≤ _))
  (le_trans (right_le_or q r) (right_le_or p _) : r ≤ _))
(or_le_of_both_le   (le_trans (left_le_or p q) (left_le_or _ r)  : p ≤ _)
  (or_le_of_both_le (le_trans (right_le_or p q) (left_le_or _ r) : q ≤ _)
                     (right_le_or _ r                            : r ≤ _))).

End or.

Definition or_distrib_and p q r : p \./[B] (q /.\ r) ∼ (p \./ q) /.\ (p \./ r).
Admitted.

(* Can't get setoid rewriting/etc. to work *)
Definition le_of_and_false_of_or_true p q r (h1 : p /.\ q ∼ ⊥) (h2 : p \./ r ∼ ⊤)
    : q ≤[ B ] r.
apply (and_respects_equiv (equiv_refl q)) in h2.
apply (equiv_trans (equiv_sym (and_distrib_or q p r))) in h2.
apply (fun h => equiv_trans h (and_true q)) in h2.
apply (equiv_trans (equiv_sym (or_respects_equiv (equiv_trans (and_comm q p) h1) (equiv_refl (q /.\ r))))) in h2.
apply (equiv_trans (equiv_sym (equiv_trans (or_comm ⊥ _) (or_false _)))) in h2.
apply (le_respects_equiv h2 equiv_rfl).
exact (and_le_right q r).
Defined.

Definition le_not_of_and_false p q (h : p /.\ q ∼ ⊥) : q ≤ ¬p :=
le_of_and_false_of_or_true h (or_not_equiv_true p).

Definition not_le_of_or_true p q (h : p \./ q ∼ ⊤) : ¬p ≤ q :=
le_of_and_false_of_or_true (and_not_equiv_false p) (h).

End BasicResults.

Section Filters.
Context (B : BooleanAlgebra).

Structure filter := {
  filterSet :> unary_predicate B;

  filter_true_spec : ⊤ ∈ filterSet;
  filter_false_spec : ⊥ ∉ filterSet;
  filter_mono p q : p ≤ q -> p ∈ filterSet -> q ∈ filterSet;
  filter_and_spec p q : p ∈ filterSet -> q ∈ filterSet -> p /.\ q ∈ filterSet;
}.

#[local] Arguments ex_intro2 [A P Q].
Definition filter_adjoin (f : filter) [p] (h : ¬p ∉ f) : filter := {|
  filterSet := fun q => exists2 r, r ∈ f & p /.\ r ≤ q;

  (* No idea why it guesses Q wrong when the expected type LITERALLY
     specifies it. *)
  filter_true_spec := ex_intro2 (Q := fun r => p /.\ r ≤ ⊤)
                        ⊤ f.(filter_true_spec) (B.(true_spec) _);
  filter_false_spec h' := let (r, h_in, h_le) := h' in
    h (f.(filter_mono) (le_not_of_and_false (false_of_le_false h_le)) h_in);

  filter_mono q q' h_le h' := let (r, h_in, h_le') := h' in
    ex_intro2 r h_in (le_trans h_le' h_le);

  filter_and_spec q1 q2 h1 h2 :=
    let (r1, h_in1, h_le1) := h1 in let (r2, h_in2, h_le2) := h2 in
    ex_intro2 (r1 /.\ r2) (f.(filter_and_spec) h_in1 h_in2)
      (let r := p /.\ (r1 /.\ r2) in
       let h1 : r ≤ p /.\ r1 := and_mono le_rfl (and_le_left r1 r2) in
       let h2 : r ≤ p /.\ r2 := and_mono le_rfl (and_le_right r1 r2) in
       le_and_of_le_both (le_trans h1 h_le1) (le_trans h2 h_le2))
|}.

Definition filter_sub_adjoin (f : filter) p (h : ¬p ∉ f) : f ⊆ filter_adjoin h := fun q h' =>
ex_intro2 (Q := fun r => p /.\ r ≤ q) q h' (and_le_right p q).

Definition in_filter_adjoin (f : filter) p (h : ¬p ∉ f) : p ∈ filter_adjoin h :=
ex_intro2 ⊤ f.(filter_true_spec) (and_le_left p ⊤).

Section Ultrafilters.
Context (f : filter).

Definition filter_maximal := forall f' : filter, f ⊆ f' -> f' ⊆ f.

(* We use here lem in the form `forall p, p ∈ f \/ ¬p ∈ f`. *)
Theorem filter_maximal_iff_mem_or_not_mem {h_em : forall p, p ∈ f \/ p ∉ f}
    : filter_maximal <-> forall p, p ∈ f \/ ¬p ∈ f.
split.
- intros h_max p.
  destruct (h_em (¬p)) as [h_n_in|h_n_notin].
  + exact (or_intror h_n_in).
  + apply or_introl.
    apply (h_max (filter_adjoin h_n_notin) (filter_sub_adjoin h_n_notin)).
    exact (in_filter_adjoin h_n_notin).
  (* destruct (h_em p) as [|h_notin], (h_em (¬p)) as [|h_nnotin]
  ; try ((apply or_introl + apply or_intror); assumption).
  (* remaining case: p ∉ f and ¬p ∉ f *)
  exfalso.
  exact (h_notin (h_max _ (filter_sub_adjoin h_nnotin)
                          p (in_filter_adjoin h_nnotin))). *)
- intros h f' h_incl p h_in_f'.
  assert (h_n_notin' : ¬p ∉ f').
  { intro. apply f'.(filter_false_spec).
    apply (f'.(filter_mono) (equiv_le (and_not_equiv_false p))).
    apply (f'.(filter_and_spec) h_in_f').
    assumption. }
  destruct (h p) as [h_p|h_np]. + exact h_p.
  + contradiction (h_n_notin' (h_incl _ h_np)).
Qed.

End Ultrafilters.

Definition Ultrafilter := {f : filter | filter_maximal f}.

End Filters.


Definition BPIT (B : BooleanAlgebra) :=
forall f : filter B, exists2 f' : filter B, filter_maximal f' & f ⊆ f'.

Axiom boolean_prime_ideal_theorem : forall B : BooleanAlgebra, BPIT B.
