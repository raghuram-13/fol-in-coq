Set Implicit Arguments. Unset Strict Implicit.

Require Import Coq.Program.Basics.
Require Import Coq.Classes.RelationClasses.
(* Import Coq.Classes.RelationClasses (PreOrder, Equivalence). *)
Require Coq.Classes.Morphisms. Import (notations) Coq.Classes.Morphisms.
Import Coq.Classes.Morphisms (Proper).

(* Why is this missing? *)
(* It caused an endless loop when searching for an instance of `Reflexive`
   at least once. *)
(* #[local] Existing Instance Build_Equivalence. *)

Structure Preordered :=
{ carrier :> Type; le : carrier -> carrier -> Prop; pre : PreOrder le }.

Arguments le {X} : rename.

Definition ge {X : Preordered} : X -> X -> Prop := flip le.

#[export] Instance preorder_bundle (X : Preordered) : PreOrder X.(le) := X.(pre).

Notation "x ≤[ X ] y" := (le (X := X) x y) (at level 70).
Notation "x ≤ y"      := (le x y)          (at level 70).
Notation "x ≥[ X ] y" := (ge (X := X) x y) (at level 70).
Notation "x ≥ y"      := (ge x y)          (at level 70).

Section PreorderedProperties. Variables (X : Preordered).

Definition le_refl : Reflexive X.(le) := reflexivity.
Definition le_rfl {x : X} : x ≤ x := le_refl x.

Definition le_trans : Transitive X.(le) := transitivity.

Definition equiv (x y : X) : Prop := x ≤ y /\ y ≤ x.

Notation "x ∼ y" := (equiv x y) (at level 70).

Section ProjectedIneqs. Variables (x y : X) (h : x ∼ y).
Definition equiv_le     : x ≤ y := proj1 h.
Definition equiv_le_rev : y ≤ x := proj2 h.
Definition equiv_ge     : x ≥ y := proj2 h.
Definition equiv_ge_rev : y ≥ x := proj1 h.
End ProjectedIneqs.

Instance equiv_refl : Reflexive equiv := fun _ => conj le_rfl le_rfl.
Definition equiv_rfl {x : X} : x ∼ x := equiv_refl x.

Definition equiv_sym : Symmetric equiv :=
fun _ _ h => conj (equiv_le_rev h) (equiv_le h).

Definition equiv_trans : Transitive equiv := fun _ _ _ h1 h2 =>
conj (le_trans (equiv_le h1) (equiv_le h2))
     (le_trans (equiv_le_rev h2) (equiv_le_rev h1)).

Definition equiv_equivalence : Equivalence equiv :=
Build_Equivalence equiv equiv_refl equiv_sym equiv_trans.

Definition le_respects_equiv : Proper (equiv ==> equiv ==> iff) X.(le) :=
fun x1 x2 h_x y1 y2 h_y => conj
(fun h_le_1 => le_trans (le_trans (equiv_ge h_x) h_le_1) (equiv_le h_y))
(fun h_le_2 => le_trans (le_trans (equiv_le h_x) h_le_2) (equiv_ge h_y)).

End PreorderedProperties.
Arguments equiv {X}.
(* Print le. Print le_refl. Print le_rfl. Print le_trans. Print equiv. *)

Notation "x ∼[ X ] y" := (equiv (X := X) x y) (at level 70).

Definition Preordered_dual (X : Preordered) : Preordered := {|
  carrier := X.(carrier);
  le := flip X.(le);
  pre := flip_PreOrder X.(pre)
|}.

Section SpecialElements.

Definition is_sup (A : Subset

End SpecialElements.

Structure BooleanAlgebra := {
  carrier :> Preordered;

  and : carrier -> carrier -> carrier;
  or : carrier -> carrier -> carrier;
  true : carrier; false : carrier;
  not : carrier -> carrier;

  and_spec {p q r} : le r (and p q) <-> le r p /\ le r q;
  or_spec {p q r} : le (or p q) r <-> le p r /\ le q r;
  false_spec {p} : le false p; true_spec {p} : le p true;
  and_not_spec {p} : eq (and p (not p)) false;
  or_not_spec {p} : eq (or p (not p)) true;
}.

Structure filter (B : BooleanAlgebra) := {
  set :> Subset B.(carrier);

  filter_true_spec : B.(true) ∈ set;
  filter_false_spec : B.(false) ∉ set;
  filter_mono p q : B.(le) p q -> p ∈ set -> q ∈ set;
  filter_and_spec p q : p ∈ set -> q ∈ set -> B.(and) p q ∈ set;
}.

Section BasicResults.
Variable (B : BooleanAlgebra).

Definition le_refl : forall {p}, B.(le) p p := B.(is_preorder).(preord_refl _ _).
Definition le_trans : forall p q r, B.(le) p q -> B.(le) q r -> B.(le) p r :=
B.(is_preorder).(preord_trans _ _).

Definition and_le_left p q : B.(le) (B.(and) p q) p :=
  proj1 (proj1 B.(and_spec) le_refl).
Definition and_le_right p q : B.(le) (B.(and) p q) q :=
  proj2 (proj1 B.(and_spec) le_refl).

End BasicResults.
Arguments and_le_left {B p q}. Arguments and_le_right {B p q}.

Section Ultrafilters.
Variable (B : BooleanAlgebra) (f : filter B).

Definition filter_adjoin (p : B) (h : B.(not) p ∉ f) : filter B := {|
  set := fun q => exists2 r, r ∈ f & B.(le) (B.(and) p r) q;

  filter_true_spec := ex_intro2 _ (fun r => B.(le) (B.(and) p r) B.(true))
                          B.(true) f.(filter_true_spec) B.(true_spec);
  filter_false_spec h' := let (r, h_in, h_le) := h' in
                          let h' : B.(le) r (B.(not) p) :=
                            _ in
    h (f.(filter_mono) h' h_in);

  filter_mono q q' h_le h' := let (r, h_in, h_le') := h' in
    ex_intro2 _ _ r h_in (le_trans h_le' h_le);

  filter_and_spec q q' h h' := let (r, h_in, h_le) := h in let (r', h_in', h_le') := h' in
    ex_intro2 _ _ (B.(and) r r') (f.(filter_and_spec) h_in h_in')
                  (let r_ := B.(and) p (B.(and) r r') in
                   let h' : B.(le) r_ p := and_le_left in
                   let h'' : B.(le) r_ r := le_trans and_le_right and_le_left in
                   let h''' : B.(le) r_ r' := le_trans and_le_right and_le_right in
                   let h : B.(le) r_ q := le_trans (proj2 B.(and_spec) (conj h' h'')) h_le in
                   let h' : B.(le) r_ q' := le_trans (proj2 B.(and_spec) (conj h' h''')) h_le' in
                   proj2 B.(and_spec) (conj h h'))
|}.

Definition maximal (B : BooleanAlgebra) (f : filter B) :=
forall f' : filter B, f ⊆ f' -> f' ⊆ f.

Definition adjoin (B : Bool

Theorem maximal_iff_mem_or_mem_not B f : maximal f <-> forall p, (* p ∈ f \/ B.(not) p ∈ f *) B.(not) p ∉ f -> p ∈ f.
split.
- intros h_max p. 
- intros h f' h_incl p h_in_f'.
  assert (h_nn_in_f' : B.(not) p ∉ f').
  { intro. apply f'.(filter_false_spec).
    apply (f'.(filter_mono) (proj1 (B.(and_not_spec) p))).
    apply (f'.(filter_and_spec) h_in_f').
    assumption. }
  (* destruct (h p) as [h_p|h_np].
  + exact h_p.
  + contradiction (h_nn_in_f' (h_incl _ h_np)). *)
Qed.

End Ultrafilters.

