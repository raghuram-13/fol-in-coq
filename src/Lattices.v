Set Implicit Arguments. Unset Strict Implicit.

Require Coq.Program.Basics. Import Coq.Program.Basics (flip, impl).
Require Import Coq.Classes.RelationClasses.
Require Import SetNotations Util.
Import (notations) EqNotations.

(* "Setoid handling" *)
Require Coq.Classes.Morphisms. Import (notations) Coq.Classes.Morphisms.
Import Coq.Classes.Morphisms (Proper).
From Coq Require Setoid.

Structure Preordered :=
{ carrier :> Type; le : carrier -> carrier -> Prop; pre : PreOrder le }.

(* In the context `X : Preordered`, we can use `le : X -> X -> Prop` without
   specifying the implicit argument as `X`. *)
Arguments le {X} : rename.

Definition ge {X : Preordered} : X -> X -> Prop := flip le.

#[export] Existing Instance pre.

Notation "x ≤[ X ] y" := (le (X := X) x y) (at level 70).
Notation "x ≤ y"      := (le x y)          (at level 70).
Notation "x ≥[ X ] y" := (ge (X := X) x y) (at level 70).
Notation "x ≥ y"      := (ge x y)          (at level 70).

Section PreorderedProperties. Context {X : Preordered}.

Definition le_refl : Reflexive X.(le) := reflexivity.
#[global] Arguments le_refl {x}, x.

Definition le_trans : Transitive X.(le) := transitivity.

Definition equiv (x y : X) : Prop := x ≤ y /\ y ≤ x.

Section ProjectedIneqs. Context [x y : X] (h : equiv x y).
Definition equiv_le     : x ≤ y := proj1 h.
Definition equiv_le_rev : y ≤ x := proj2 h.
Definition equiv_ge     : x ≥ y := proj2 h.
Definition equiv_ge_rev : y ≥ x := proj1 h.
End ProjectedIneqs.

Definition equiv_refl : Reflexive equiv := fun _ => conj le_refl le_refl.
#[global] Arguments equiv_refl {x}, x.

Definition equiv_sym : Symmetric equiv :=
fun _ _ h => conj (equiv_le_rev h) (equiv_le h).

Definition equiv_trans : Transitive equiv := fun _ _ _ h1 h2 =>
conj (le_trans (equiv_le h1) (equiv_le h2))
     (le_trans (equiv_le_rev h2) (equiv_le_rev h1)).

#[export] Instance equiv_equivalence : Equivalence equiv :=
Build_Equivalence equiv (@equiv_refl) equiv_sym equiv_trans.

#[export] Instance : subrelation equiv le := equiv_le.
#[export] Instance : subrelation equiv (flip le) := equiv_ge.

#[export] Instance le_respects_equiv : Proper (equiv ==> equiv ==> iff) X.(le) :=
fun _ _ h_x _ _ h_y => conj
(fun h_le_1 => le_trans (le_trans (equiv_ge h_x) h_le_1) (equiv_le h_y))
(fun h_le_2 => le_trans (le_trans (equiv_le h_x) h_le_2) (equiv_ge h_y)).

Definition binop_respects_equiv_of_mono (bin_op : X -> X -> X)
        (h : Proper (le ==> le ==> le) bin_op)
    : Proper (equiv ==> equiv ==> equiv) bin_op :=
fun _ _ h_x _ _ h_y => conj (h _ _ (equiv_le h_x)     _ _ (equiv_le h_y))
                            (h _ _ (equiv_le_rev h_x) _ _ (equiv_le_rev h_y)).

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

Module BooleanAlgebra.

Class isBooleanAlgebra B le `(@PreOrder B le) := {
  isBooleanAlgebra_PreOrder :> PreOrder le := _;
  (* This is purely to allow us to use the ≤ and ∼ notations *)
  _BA_pre : Preordered := {| carrier := B; le := le; pre := _ |};

  meet : _BA_pre -> _BA_pre -> _BA_pre;
  join : _BA_pre -> _BA_pre -> _BA_pre;
  top : _BA_pre; bot : _BA_pre;
  complement : _BA_pre -> _BA_pre;

  meet_le_left p q : meet p q ≤ p; meet_le_right p q : meet p q ≤ q;
  le_meet_of_le_both {p q r} : r ≤ p -> r ≤ q -> r ≤ meet p q;

  meet_spec p q r : r ≤ meet p q <-> r ≤ p /\ r ≤ q := ltac:(split; [
      intro h_meet; split; apply (le_trans h_meet)
      ; [ apply meet_le_left | apply meet_le_right ]
    | intros [h1 h2]; exact (le_meet_of_le_both p q r h1 h2) ]);

  left_le_join p q : p ≤ join p q; right_le_join p q : q ≤ join p q;
  join_le_of_both_le {p q r} : p ≤ r -> q ≤ r -> join p q ≤ r;

  join_spec p q r : join p q ≤ r <-> p ≤ r /\ q ≤ r := ltac:(split; [
      intro h_join; split; refine (le_trans _ h_join)
      ; [ apply left_le_join | apply right_le_join ]
    | intros [h1 h2]; exact (join_le_of_both_le p q r h1 h2) ]);

  bot_le p : bot ≤ p; le_top p : p ≤ top;

  equiv_bot_of_le_bot {p} : p ≤ bot -> p ∼ bot := fun h => conj h (bot_le p);
  equiv_top_of_top_le {p} : top ≤ p -> p ∼ top := fun h => conj (le_top p) h;

  meet_compl_le_bot p : meet p (complement p) ≤ bot;
  top_le_join_compl p : top ≤ join p (complement p);

  meet_compl_equiv_bot p : meet p (complement p) ∼ bot :=
    equiv_bot_of_le_bot (meet_compl_le_bot p);
  join_compl_equiv_top p : join p (complement p) ∼ top :=
    equiv_top_of_top_le (top_le_join_compl p);

  meet_distrib_join' p q r : meet p (join q r) ≤ join (meet p q) (meet p r);
  meet_distrib_join p q r  : meet p (join q r) ∼ join (meet p q) (meet p r) :=
  conj (meet_distrib_join' p q r)
       ltac:(apply le_meet_of_le_both; [
           apply join_le_of_both_le; apply meet_le_left
         | apply join_le_of_both_le; apply (le_trans (meet_le_right p _))
           ;[apply left_le_join | apply right_le_join] ]);

  (* join_distrib_meet' p q r : join p (meet q r) ≥ meet (join p q) (join p r) :=
    _;
  join_distrib_meet p q r : join p (meet q r) ∼ meet (join p q) (join p r) :=
  conj ltac:(apply join_le_of_both_le; [
           apply le_meet_of_le_both; apply left_le_join
         | apply le_meet_of_le_both; refine (le_trans _ (right_le_join p _))
           ;[apply meet_le_left | apply meet_le_right] ])
       (join_distrib_meet' p q r) *)
}.
Arguments isBooleanAlgebra [B] le {_}, [B] le _.
Arguments Build_isBooleanAlgebra B le H &.

(* Specifying multiple argument sequences like this should allow us
   to either omit or specify all the `carrier` arguments, which is
   convenient. *)
(* Specifying multiple implicit arguments not working only when
   the conclusion type is a ≤ instead of an ∼. Why? *)
(* Arguments meet_le_left {_ _ _ _} p q, {_ _ _ _ p q}.
Arguments meet_le_right {_ _ _ _} p q, {_ _ _ _ p q}.
Arguments left_le_join {_ _ _ _} p q, {_ _ _ _ p q}.
Arguments right_le_join {_ _ _ _} p q, {_ _ _ _ p q}.
Arguments bot_le {_ _ _ _} p, {_ _ _ _ p}.
Arguments le_top {_ _ _ _} p, {_ _ _ _ p}.
Arguments meet_compl_le_bot {_ _ _ _} p, {_ _ _ _ p}.
Arguments top_le_join_compl {_ _ _ _} p, {_ _ _ _ p}. *)
Arguments meet_compl_equiv_bot {_ _ _ _} p, {_ _ _ _ p}.
Arguments join_compl_equiv_top {_ _ _ _} p, {_ _ _ _ p}.
(* Argument meet_distrib_join' {_ _ _ _} p q r, {_ _ _ _ p q r}. *)
Arguments meet_distrib_join {_ _ _ _} p q r, {_ _ _ _ p q r}.
(* (* Arguments join_distrib_meet' {_ _ _ _} p q r, {_ _ _ _ p q r}. *)
Arguments join_distrib_meet {_ _ _ _} p q r, {_ _ _ _ p q r}. *)

Structure BooleanAlgebra := {
  preCarrier :> Preordered;
  _is_boolean_algebra : isBooleanAlgebra preCarrier.(le)
}.
#[export] Existing Instance _is_boolean_algebra.

Notation "⊥[ B ]" := (bot : B). Notation "⊤[ B ]" := (top : B).
Notation "x ∧[ B ] y" := (meet (x:B) (y:B)) (at level 65, right associativity).
Notation "x ∨[ B ] y" := (join (x:B) (y:B)) (at level 65, right associativity).
Notation "⊥"   := (bot). Notation "⊤"   := (top).
Infix    "∧"   := meet           (at level 65, right associativity).
Infix    "∨"   := join           (at level 65, right associativity).
Notation "¬ x" := (complement x) (at level 35, right associativity).

Section Stuff. Context {B : BooleanAlgebra}.

Section BasicResults. Implicit Types p q r : B.

Section meet.

Definition meet_mono : Proper (le ++> le ++> le) (meet : B -> B -> B) :=
fun x1 x2 h_x y1 y2 h_y => le_meet_of_le_both
  (le_trans (meet_le_left x1 y1) h_x)
  (le_trans (meet_le_right x1 y1) h_y).

#[export] Instance meet_respects_equiv : Proper (equiv ==> equiv ==> equiv) meet :=
binop_respects_equiv_of_mono meet_mono.

Definition meet_top p : p ∧ ⊤ ∼ p :=
conj (meet_le_left p ⊤) (le_meet_of_le_both (le_refl p) (le_top p)).
Definition top_meet p : ⊤ ∧ p ∼ p :=
conj (meet_le_right ⊤ p) (le_meet_of_le_both (le_top p) (le_refl p)).

Definition meet_bot p : p ∧ ⊥ ∼ ⊥ := equiv_bot_of_le_bot (meet_le_right p ⊥).
Definition bot_meet p : ⊥ ∧ p ∼ ⊥ := equiv_bot_of_le_bot (meet_le_left ⊥ p).

Definition meet_comm p q : p ∧ q ∼ q ∧ p := conj
(le_meet_of_le_both (meet_le_right p q) (meet_le_left p q))
(le_meet_of_le_both (meet_le_right q p) (meet_le_left q p)).

Definition meet_assoc p q r : (p ∧ q) ∧ r ∼ p ∧ (q ∧ r) := conj
(le_meet_of_le_both   (le_trans (meet_le_left _ r) (meet_le_left p q)  : _ ≤ p)
  (le_meet_of_le_both (le_trans (meet_le_left _ r) (meet_le_right p q) : _ ≤ q)
                     (meet_le_right _ r                              : _ ≤ r)))
(le_meet_of_le_both (le_meet_of_le_both
  (meet_le_left p _                                : _ ≤ p)
  (le_trans (meet_le_right p _) (meet_le_left q r)  : _ ≤ q))
  (le_trans (meet_le_right p _) (meet_le_right q r) : _ ≤ r)).

End meet.

Section join.

Definition join_mono : Proper (le ++> le ++> le) (join : B -> B -> B) :=
fun x1 x2 h_x y1 y2 h_y => join_le_of_both_le
  (le_trans h_x (left_le_join x2 y2))
  (le_trans h_y (right_le_join x2 y2)).

#[export] Instance join_respects_equiv : Proper (equiv ==> equiv ==> equiv) join :=
binop_respects_equiv_of_mono join_mono.

Definition join_bot p : p ∨ ⊥ ∼ p :=
conj (join_le_of_both_le (le_refl p) (bot_le p)) (left_le_join p ⊥).
Definition bot_join p : ⊥ ∨ p ∼ p :=
conj (join_le_of_both_le (bot_le p) (le_refl p)) (right_le_join ⊥ p).

Definition join_top p : p ∨ ⊤ ∼ ⊤ := equiv_top_of_top_le (right_le_join p ⊤).
Definition top_join p : ⊤ ∨ p ∼ ⊤ := equiv_top_of_top_le (left_le_join ⊤ p).

Definition join_comm p q : p ∨ q ∼ q ∨ p := conj
(join_le_of_both_le (right_le_join q p) (left_le_join q p))
(join_le_of_both_le (right_le_join p q) (left_le_join p q)).

Definition join_assoc p q r : (p ∨ q) ∨ r ∼ p ∨ (q ∨ r) := conj
(join_le_of_both_le (join_le_of_both_le
  (left_le_join p _                               : p ≤ _)
  (le_trans (left_le_join q r) (right_le_join p _)  : q ≤ _))
  (le_trans (right_le_join q r) (right_le_join p _) : r ≤ _))
(join_le_of_both_le   (le_trans (left_le_join p q) (left_le_join _ r)  : p ≤ _)
  (join_le_of_both_le (le_trans (right_le_join p q) (left_le_join _ r) : q ≤ _)
                     (right_le_join _ r                            : r ≤ _))).

End join.

(* Definition join_distrib_meet' p q r : p ∨ (q ∧ r) ≥ (p ∨ q) ∧ (p ∨ r).
Admitted. *)

Definition le_of_meet_bot_of_join_top p q r
    : p ∧ q ∼ ⊥ -> p ∨ r ∼ ⊤ -> q ≤ r.
intros h1 h2. rewrite meet_comm in h1.
apply (meet_respects_equiv (equiv_refl q)) in h2.
rewrite meet_distrib_join, meet_top, h1, bot_join in h2.
rewrite <-h2; exact (meet_le_right q r).
Defined.

Definition le_compl_of_meet_bot p q (h : p ∧ q ∼ ⊥) : q ≤ ¬p :=
le_of_meet_bot_of_join_top h (join_compl_equiv_top p).

Definition compl_le_of_join_top p q (h : p ∨ q ∼ ⊤) : ¬p ≤ q :=
le_of_meet_bot_of_join_top (meet_compl_equiv_bot p) h.

Definition compl_compl p : ¬¬p ∼ p := conj
  (compl_le_of_join_top (equiv_trans (join_comm _ _) (join_compl_equiv_top p)))
  (le_compl_of_meet_bot (equiv_trans (meet_comm _ _) (meet_compl_equiv_bot p))).

End BasicResults.

Section Homomorphisms.
Context {B1 B2 : BooleanAlgebra}.
Implicit Types p q r : B1.

Class isBooleanAlgebraHom (f : B1 -> B2) := {
  hom_mono : Proper (le ==> le) f;

  hom_preserves_meet' p q : f (p ∧ q) ≥ f p ∧ f q;
  hom_preserves_meet  p q : f (p ∧ q) ∼ f p ∧ f q := conj
    (le_meet_of_le_both (hom_mono (meet_le_left p q))
                        (hom_mono (meet_le_right p q)))
    (hom_preserves_meet' p q);

  hom_preserves_join' p q : f (p ∨ q) ≤ f p ∨ f q;
  hom_preserves_join  p q : f (p ∨ q) ∼ f p ∨ f q := conj
    (hom_preserves_join' p q)
    (join_le_of_both_le (hom_mono (left_le_join p q))
                        (hom_mono (right_le_join p q)));

  hom_preserves_bot' : f ⊥ ≤ ⊥; hom_preserves_top' : f ⊤ ≥ ⊤;
  hom_preserves_bot : f ⊥ ∼ ⊥ := equiv_bot_of_le_bot hom_preserves_bot';
  hom_preserves_top : f ⊤ ∼ ⊤ := equiv_top_of_top_le hom_preserves_top';

  hom_preserves_compl p : f (¬p) ∼ ¬f p;
}.
#[global] Arguments hom_mono [f] {_}.

Structure BooleanAlgebraHom := {
  hom_function :> B1 -> B2;
  _is_boolean_algebra_hom : isBooleanAlgebraHom hom_function
}.
#[export] Existing Instance _is_boolean_algebra_hom.

End Homomorphisms.
Arguments BooleanAlgebraHom B1 B2 : clear implicits.

Section bool.

#[export] Instance : PreOrder Bool.le := ltac:(
split; unfold Reflexive, Transitive
; Bool.destr_bool).

#[export, refine] Instance : isBooleanAlgebra Coq.Bool.Bool.le := {|
  meet := andb; join := orb; bot := false; top := true; complement := negb
|}. all:(intros; simpl in *; Bool.destr_bool). Defined.

#[global] Canonical Structure boolBooleanAlgebra : BooleanAlgebra := {|
  preCarrier := {| le := Bool.le |}
|}.

Lemma eq_of_equiv_bool (p q : boolBooleanAlgebra) : p ∼ q -> p = q.
simpl in p, q. intro h; unfold equiv in h; simpl in h; destruct h.
Bool.destr_bool. Qed.
(* Hint Resolve eq_of_equiv_bool : core. *)

End bool.

Section Filters.

Structure Filter := {
  filterSet :> unary_predicate B;

  filter_top_spec : ⊤ ∈ filterSet;
  filter_mono p q : p ≤ q -> p ∈ filterSet -> q ∈ filterSet;
  filter_meet_spec p q : p ∈ filterSet -> q ∈ filterSet -> p ∧ q ∈ filterSet;
}.

#[export] Instance : forall F : Filter,
    Proper (A := unary_predicate B) (le ==> impl) F :=
filter_mono.

#[export] Instance filter_respects_equiv (F : Filter)
    : Proper (A := unary_predicate B) (equiv ==> iff) F := fun p q h =>
conj (F.(filter_mono) (equiv_le h)) (F.(filter_mono) (equiv_ge h)).

Definition filter_proper (F : Filter) : Prop := ⊥ ∉ F.

Structure ProperFilter := {
  _ProperFilter_as_Filter :> Filter;
  ProperFilter_spec : filter_proper _ProperFilter_as_Filter
}.

Definition trivial_filter : Filter := {|
  filterSet := flip equiv ⊤;

  filter_top_spec := equiv_refl ⊤;
  filter_mono p q h_le h := equiv_top_of_top_le (le_trans (equiv_ge h) h_le);
  filter_meet_spec p q h_p h_q := ltac:(rewrite <-(meet_top ⊤), <-h_p, <-h_q;
                                        reflexivity)
                                  : p ∧ q ∼ ⊤
|}.

Section AdjoinElement.
Variables (F : Filter) (p : B).

Arguments ex_intro2 [_ _ _].

Definition filter_adjoin : Filter := {|
  filterSet := fun q => exists2 r : B, r ∈ F & p ∧ r ≤ q;

  (* No idea why Q isn't inferred correctly just because ⊤ occurs twice
     when it should be LITERALLY available from the expected type. *)
  filter_top_spec := ex_intro2 (Q := fun r => p ∧ r ≤ ⊤)
                               ⊤ F.(filter_top_spec) (le_top (p ∧ ⊤));
  filter_mono q q' h_le '(ex_intro2 r h_in h_le') :=
    ex_intro2 r h_in (le_trans h_le' h_le);
  filter_meet_spec q1 q2
      '(ex_intro2 r1 h_in1 h_le1) '(ex_intro2 r2 h_in2 h_le2) :=
    ex_intro2 (r1 ∧ r2) (F.(filter_meet_spec) h_in1 h_in2)
      (let r := p ∧ (r1 ∧ r2) in
       let h1 : r ≤ p ∧ r1 := meet_mono le_refl (meet_le_left r1 r2) in
       let h2 : r ≤ p ∧ r2 := meet_mono le_refl (meet_le_right r1 r2) in
       le_meet_of_le_both (le_trans h1 h_le1) (le_trans h2 h_le2))
|}.

Section Inclusions.
Definition filter_sub_adjoin : F ⊆ filter_adjoin := fun q h =>
ex_intro2 (Q := fun r => p ∧ r ≤ q) q h (meet_le_right p q).

Definition adjoined_in_filter_adjoin : p ∈ filter_adjoin :=
(ex_intro2 ⊤ F.(filter_top_spec) (meet_le_left p ⊤)).
End Inclusions.

Definition filter_adjoin_proper (h : filter_proper F) (h' : ¬p ∉ F)
    : filter_proper filter_adjoin := fun '(ex_intro2 r h_in h_le) =>
h' (F.(filter_mono) (le_compl_of_meet_bot (equiv_bot_of_le_bot h_le)) h_in).

End AdjoinElement.
Arguments filter_sub_adjoin F p : clear implicits.

Section Ultrafilters. Variable (F : Filter).

Definition filter_maximal_proper :=
filter_proper F /\ forall F', filter_proper F' -> F ⊆ F' -> F' ⊆ F.

Theorem filter_maximal_iff_mem_or_compl_mem (h_em : forall p, p ∈ F \/ p ∉ F)
    : filter_maximal_proper <-> filter_proper F /\ forall p, p ∈ F \/ ¬p ∈ F.
(* Turns out (¬p ∈ F \/ p ∈ F) comes up naturally in the proof.
   `setoid_rewrite` is needed to rewrite under the `forall` to avoid funext. *)
setoid_rewrite or_comm.
(* Making use of `h_em`. *)
assert (em__or_iff : forall p B, (p ∈ F \/ B) <-> (p ∉ F -> B)).
{ split. + intros [h_p | h_B] h_np; [ contradiction (h_np h_p) | exact h_B ].
         + intro h; destruct (h_em p); [ left | right; apply h ]; assumption. }
(* Since `filter_proper F` is common on both sides, we can assume it's there
   and prove the other halves are equivalent. *)
assert (iff_under : forall (a b c : Prop) (h : a -> (b <-> c)),
                      a /\ b <-> a /\ c).
{ split; (intros [h_a ?]; split; [ | apply (h h_a) ]; assumption). }
apply iff_under; intro h_proper.
split.
- intros h_max p. apply em__or_iff; intro h_c_notin.
  apply (h_max (filter_adjoin F p) (filter_adjoin_proper h_proper h_c_notin)
               (filter_sub_adjoin F p)).
  exact (adjoined_in_filter_adjoin F p).
- intros h F' h_proper' h_incl p h_in'.
  apply em__or_iff with (p := ¬p); [ apply h | ].
  intro h'.
  apply h_incl, (F'.(filter_meet_spec) h_in') in h'.
  pose (h_bot_in' := F'.(filter_mono) (meet_compl_le_bot p) h').
  contradiction (h_proper' h_bot_in').
Qed.

Section Ultrafilter'. Import Coq.Bool.Bool (Is_true).
Definition Ultrafilter' := BooleanAlgebraHom B boolBooleanAlgebra.

Variable uf : Ultrafilter'. Unset Implicit Arguments.

Definition Ultrafilter'_as_Filter : Filter := {|
  filterSet p := Is_true (uf p);
  filter_top_spec := rew <-(eq_of_equiv_bool hom_preserves_top) in
                     (I : Is_true true);
  filter_mono p q h_le h_p := ltac:(
      apply hom_mono with (f := uf) in h_le; only 2: typeclasses eauto;
      simpl in h_p; rewrite Is_true_iff_eq_true in h_p; rewrite h_p in h_le;
      destruct (uf q); [ exact I | simpl in h_le; discriminate h_le ])
    : Is_true (uf q);
  filter_meet_spec p q h_p h_q := ltac:(
    rewrite (eq_of_equiv_bool (hom_preserves_meet p q)), Is_true_and; exact
    (conj h_p h_q)) : Is_true (uf (p ∧ q))
|}.

Definition Ultrafilter'_is_proper : filter_proper Ultrafilter'_as_Filter :=
fun (h : Is_true (uf ⊥)) =>
rew (eq_of_equiv_bool hom_preserves_bot : uf ⊥ = false) in h.

Definition Ultrafilter'_int_em p
    : p ∈ Ultrafilter'_as_Filter \/ ¬p ∈ Ultrafilter'_as_Filter.
simpl; rewrite (eq_of_equiv_bool (hom_preserves_compl p) : uf(¬p)=negb(uf p)).
destruct (uf p); [ left | right ]; exact (I : Is_true true).
Defined.

Set Implicit Arguments. End Ultrafilter'.

Section OpMembership.

Definition elem_meet_and p q : p ∧ q ∈ F <-> p ∈ F /\ q ∈ F. split.
+ intro; split; (apply F.(filter_mono) with (p := p ∧ q)
                 ; [ apply meet_le_left + apply meet_le_right | assumption ]).
+ intros []; apply F.(filter_meet_spec); assumption.
Qed.

Definition not_elem_and_elem_compl (h : filter_proper F) p : ~(p ∈ F /\ ¬p ∈ F).
intros []. apply h.
apply (F.(filter_mono) (meet_compl_le_bot p)).
apply F.(filter_meet_spec) with (p := p) (q := ¬p); assumption.
Defined.

Definition elem_compl_not (h_em : forall p, p ∈ F \/ p ∉ F)
                          (h : filter_maximal_proper)
    p : ¬p ∈ F <-> p ∉ F.
rewrite (filter_maximal_iff_mem_or_compl_mem h_em) in h; destruct h as [? h].
split.
+ intros ? ?; refine (not_elem_and_elem_compl _ (conj _ _)); eassumption.
+ exact (or_elim_left (h p)).
Defined.

Definition elem_join_of_or_elem {p q} : p ∈ F \/ q ∈ F -> p ∨ q ∈ F.
intro h; destruct h as [h|h]; refine (F.(filter_mono) _ h)
; [ apply left_le_join | apply right_le_join ].
Defined.

Definition elem_join_or (h_em : forall p, p ∈ F \/ p ∉ F)
                        (h : filter_maximal_proper)
    p q : p ∨ q ∈ F <-> p ∈ F \/ q ∈ F.
split.
+ rewrite (filter_maximal_iff_mem_or_compl_mem h_em) in h;
    destruct h as [h_proper h].
  destruct (h p), (h q); intro h_join; [
    solve [ left + right; assumption ] ..
  | exfalso ].
  assert (h_meet : ¬p ∧ ¬q ∈ F) by (eapply F.(filter_meet_spec); assumption).
  apply (F.(filter_meet_spec) h_join) in h_meet.
  assert (h_le : (p ∨ q) ∧ ¬p ∧ ¬q ≤ ⊥) by (
    rewrite meet_comm, meet_distrib_join;
    apply join_le_of_both_le; [
      rewrite meet_comm, <-meet_assoc
    | rewrite meet_assoc, meet_comm with (q:=q)
    ]; rewrite meet_compl_equiv_bot; [apply meet_le_left|apply meet_le_right]).
  eapply h_proper; exact (F.(filter_mono) h_le h_meet).
+ exact elem_join_of_or_elem.
Defined.

Definition elem_impl_impl (h_em : forall p, p ∈ F \/ p ∉ F)
                          (h : filter_maximal_proper)
    p q : ¬p ∨ q ∈ F <-> (p ∈ F -> q ∈ F).
split.
+ intros h_int h_p.
  destruct (h_em q); apply (elem_join_or h_em h), or_comm in h_int as []; [
    assumption ..
  | exfalso; eapply not_elem_and_elem_compl; [ exact (proj1 h) |
      split; eassumption ]].
+ intro h_impl. apply elem_join_of_or_elem.
  rewrite (filter_maximal_iff_mem_or_compl_mem h_em) in h; destruct h as [? h].
  destruct (h p); [ right; apply h_impl | left ]; assumption.
Defined.

End OpMembership.

End Ultrafilters.
Structure Ultrafilter := {
  _Ultrafilter_as_Filter : Filter;
  Ultrafilter_spec : filter_maximal_proper _Ultrafilter_as_Filter
}.
Coercion _Ultrafilter_as_ProperFilter (F : Ultrafilter) : ProperFilter :=
Build_ProperFilter (proj1 (Ultrafilter_spec F)).

Coercion Ultrafilter'_as_Ultrafilter (F : Ultrafilter') : Ultrafilter := {|
  _Ultrafilter_as_Filter := Ultrafilter'_as_Filter F;
  Ultrafilter_spec := proj2 (filter_maximal_iff_mem_or_compl_mem
                              (fun p => ltac:(simpl; destruct (F p)
                                              ; simpl Is_true; intuition)
                                        : p ∈ Ultrafilter'_as_Filter F
                                          \/ p ∉ Ultrafilter'_as_Filter F))
                        (conj (Ultrafilter'_is_proper F)
                              (Ultrafilter'_int_em F))
|}.

End Filters.

End Stuff.
Arguments Filter B : clear implicits.
Arguments ProperFilter B : clear implicits.
Arguments Ultrafilter B : clear implicits.
Arguments Ultrafilter' B : clear implicits.

Arguments trivial_filter B : clear implicits.

Definition UltrafilterLemma (B : BooleanAlgebra) : Prop :=
forall F : ProperFilter B, exists F' : Ultrafilter B, F ⊆ F'.

Definition UltrafilterLemmaEm (B : BooleanAlgebra) :=
forall F : ProperFilter B, exists F' : Ultrafilter' B, F ⊆ F'.

Axiom ultrafilter_lemma : forall B : BooleanAlgebra, UltrafilterLemma B.
Axiom ultrafilter_lemma_em : forall B : BooleanAlgebra, UltrafilterLemmaEm B.

End BooleanAlgebra.
